module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.E64

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

@[expose] def inducedGroup (ι : Elem2 6 →* G) : Subgroup (Equiv.Perm V6) where
  carrier := {g | ∃ n ∈ normalizer (ι.range : Set G),
    ∀ v : V6, n * coordElt ι v * n⁻¹ = coordElt ι (g v)}
  mul_mem' := by
    rintro g g' ⟨n, hn, hg⟩ ⟨n', hn', hg'⟩
    refine ⟨n * n', mul_mem hn hn', fun v => ?_⟩
    have h1 : n * n' * coordElt ι v * (n * n')⁻¹ = n * (n' * coordElt ι v * n'⁻¹) * n⁻¹ := by
      group
    rw [h1, hg' v, hg (g' v)]
    rfl
  one_mem' := ⟨1, one_mem _, fun v => by simp⟩
  inv_mem' := by
    rintro g ⟨n, hn, hg⟩
    refine ⟨n⁻¹, inv_mem hn, fun v => ?_⟩
    have h := hg (g⁻¹ v)
    have h2 : g (g⁻¹ v) = v := by simp
    rw [h2] at h
    calc n⁻¹ * coordElt ι v * n⁻¹⁻¹ = n⁻¹ * (n * coordElt ι (g⁻¹ v) * n⁻¹) * n := by
          rw [h]; simp
      _ = coordElt ι (g⁻¹ v) := by group

theorem isAddPerm_of_mem_inducedGroup (hι : Function.Injective ι) {g : Equiv.Perm V6}
    (hg : g ∈ inducedGroup ι) : IsAddPerm g := by
  obtain ⟨n, -, hn⟩ := hg
  intro x y
  have h1 : coordElt ι (g (x + y)) = coordElt ι (g x + g y) := by
    rw [← hn (x + y), coordElt_add, coordElt_add, ← hn x, ← hn y]
    group
  exact Multiplicative.ofAdd.injective (hι h1)

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private noncomputable def normalizerInducedPerm (hι : Function.Injective ι)
    (n : normalizer (ι.range : Set G)) : Equiv.Perm V6 :=
  (exists_perm_of_mem_normalizer hι n.2).choose

private lemma normalizerInducedPerm_spec (hι : Function.Injective ι)
    (n : normalizer (ι.range : Set G)) :
    ∀ v : V6, n.1 * coordElt ι v * n.1⁻¹ = coordElt ι (normalizerInducedPerm hι n v) :=
  (exists_perm_of_mem_normalizer hι n.2).choose_spec.2

private lemma normalizerInducedPerm_unique (hι : Function.Injective ι) {n : G}
    {g g' : Equiv.Perm V6}
    (hg : ∀ v : V6, n * coordElt ι v * n⁻¹ = coordElt ι (g v))
    (hg' : ∀ v : V6, n * coordElt ι v * n⁻¹ = coordElt ι (g' v)) : g = g' := by
  apply Equiv.ext
  intro v
  have h2 : coordElt ι (g v) = coordElt ι (g' v) := by rw [← hg v, ← hg' v]
  exact coordElt_injective hι h2

private noncomputable def normalizerInducedHom (hι : Function.Injective ι) :
    normalizer (ι.range : Set G) →* Equiv.Perm V6 where
  toFun := normalizerInducedPerm hι
  map_one' := by
    apply normalizerInducedPerm_unique hι (n := 1)
    · intro v; simpa using normalizerInducedPerm_spec hι 1 v
    · intro v; simp
  map_mul' n m := by
    apply normalizerInducedPerm_unique hι (n := (n * m).1)
    · intro v; simpa using normalizerInducedPerm_spec hι (n * m) v
    · intro v
      rw [Subgroup.coe_mul]
      calc n.1 * m.1 * coordElt ι v * (n.1 * m.1)⁻¹
          = n.1 * (m.1 * coordElt ι v * m.1⁻¹) * n.1⁻¹ := by group
        _ = n.1 * coordElt ι (normalizerInducedPerm hι m v) * n.1⁻¹ := by
              rw [normalizerInducedPerm_spec hι m v]
        _ = coordElt ι (normalizerInducedPerm hι n (normalizerInducedPerm hι m v)) :=
              normalizerInducedPerm_spec hι n _
        _ = coordElt ι ((normalizerInducedPerm hι n * normalizerInducedPerm hι m) v) := by
              rw [Equiv.Perm.mul_apply]

theorem card_inducedGroup_mul [Finite G] (hι : Function.Injective ι)
    (hC : centralizer (ι.range : Set G) ≤ ι.range) :
    Nat.card (inducedGroup ι) * 64 = Nat.card (normalizer (ι.range : Set G)) := by
  let φ : normalizer (ι.range : Set G) →* Equiv.Perm V6 := normalizerInducedHom hι
  have hrange : φ.range = inducedGroup ι := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.1, n.2, normalizerInducedPerm_spec hι n⟩
    · rintro ⟨n, hn, hg⟩
      exact ⟨⟨n, hn⟩,
        normalizerInducedPerm_unique hι (normalizerInducedPerm_spec hι ⟨n, hn⟩) hg⟩
  have hker : φ.ker =
      (centralizer (ι.range : Set G)).subgroupOf (normalizer (ι.range : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hh
      have hn1 : normalizerInducedPerm hι n = 1 := hn
      have hspec := normalizerInducedPerm_spec hι n (Multiplicative.toAdd a)
      rw [hn1] at hspec
      simp only [Equiv.Perm.coe_one, id_eq] at hspec
      have hc : n.1 * ι a = ι a * n.1 := by
        simpa [coordElt] using (mul_inv_eq_iff_eq_mul.mp hspec)
      exact hc.symm
    · intro hn
      rw [mem_centralizer_iff] at hn
      apply normalizerInducedPerm_unique hι (n := n.1)
      · intro v; exact normalizerInducedPerm_spec hι n v
      · intro v
        have hcomm : coordElt ι v * n.1 = n.1 * coordElt ι v :=
          hn (coordElt ι v) ⟨Multiplicative.ofAdd v, rfl⟩
        simpa using (mul_inv_eq_iff_eq_mul.mpr hcomm.symm)
  have hcent_eq : centralizer (ι.range : Set G) = ι.range := by
    apply le_antisymm hC
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hcard_range : Nat.card (ι.range) = 64 := by
    calc Nat.card (ι.range) = Nat.card (Elem2 6) :=
          (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
      _ = 64 := by
          rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin 6 → ZMod 2) ≃ Elem2 6)]
          simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
          norm_num
  have hcard_ker : Nat.card φ.ker = 64 := by
    rw [hker]
    have hcard_cent : Nat.card (centralizer (ι.range : Set G)) = 64 := by
      rw [hcent_eq]; exact hcard_range
    rw [← hcard_cent]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (ι.range : Set G))).toEquiv
  have hiso := Subgroup.card_ker_mul_card_range φ
  rw [hcard_ker, hrange] at hiso
  rw [Nat.mul_comm] at hiso
  exact hiso

theorem HData.card_normalizer_eq [Finite G] (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    Nat.card (normalizer (ι.range : Set G)) =
      Nat.card {v : V6 // IsConj t (coordElt ι v)} * 46080 := by
  let N : Subgroup G := normalizer (ι.range : Set G)
  letI : MulAction ↥N G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have smul_eq : ∀ (n : ↥N) (x : G), n • x = n.1 * x * n.1⁻¹ := by
    intro n x
    change (ConjAct.toConjAct n.1) • x = n.1 * x * n.1⁻¹
    rw [ConjAct.toConjAct_smul]
  have hstab : Nat.card (MulAction.stabilizer ↥N t) = 46080 := by
    have e : MulAction.stabilizer ↥N t ≃ ↥(N ⊓ centralizer ({t} : Set G)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s
        refine ⟨s.1.1, s.1.2, ?_⟩
        have hs : s.1.1 * t * s.1.1⁻¹ = t := by
          have h : s.1 • t = t := s.2
          rwa [smul_eq] at h
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hs)
      · intro m
        refine ⟨⟨m.1, m.2.1⟩, ?_⟩
        show (⟨m.1, m.2.1⟩ : ↥N) • t = t
        rw [smul_eq]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp m.2.2)
      · intro s; apply Subtype.ext; rfl
      · intro m; apply Subtype.ext; rfl
    rw [Nat.card_congr e]
    dsimp only [N]
    exact hD.card_NH
  let X : Type := {v : V6 // IsConj t (coordElt ι v)}
  have horbit : Nat.card (MulAction.orbit ↥N t) = Nat.card X := by
    let f : X → MulAction.orbit ↥N t := fun v =>
      ⟨coordElt ι v, MulAction.mem_orbit_iff.mpr (by
        obtain ⟨n, hn, hnt⟩ :=
          hD.exists_normalizer_conj_t ⟨Multiplicative.ofAdd v.1, rfl⟩ v.2
        exact ⟨⟨n, hn⟩, by rw [smul_eq]; exact hnt⟩)⟩
    refine (Nat.card_congr (Equiv.ofBijective f ?_)).symm
    constructor
    · intro v w h
      apply Subtype.ext
      have hv : coordElt ι v = coordElt ι w := congrArg Subtype.val h
      exact coordElt_injective hD.injective_ι hv
    · intro x
      obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp x.2
      have hnt : n.1 * t * n.1⁻¹ = (x : G) := by rw [← smul_eq]; exact hn
      have hmem : (x : G) ∈ ι.range := by
        rw [← hnt, ← hD.ι_tv]
        exact (Subgroup.mem_normalizer_iff.mp n.2 (coordElt ι tv)).mp
          ⟨Multiplicative.ofAdd tv, rfl⟩
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
      refine ⟨⟨Multiplicative.toAdd a, ?_⟩, ?_⟩
      · rw [show coordElt ι (Multiplicative.toAdd a) = ι a from rfl, ha]
        exact isConj_iff.mpr ⟨n.1, hnt⟩
      · apply Subtype.ext
        change coordElt ι (Multiplicative.toAdd a) = (x : G)
        rw [show coordElt ι (Multiplicative.toAdd a) = ι a from rfl, ha]
  have hOS : Nat.card ↥N = 46080 * Nat.card X := by
    rw [← Subgroup.card_mul_index (MulAction.stabilizer ↥N t), MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq, hstab, horbit]
  rw [hOS]
  dsimp only [X]
  ring

theorem HData.card_inducedGroup [Finite G] (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    Nat.card (inducedGroup ι) * 64 = Nat.card {v : V6 // IsConj t (coordElt ι v)} * 46080 := by
  rw [card_inducedGroup_mul hD.injective_ι hD.centralizer_le, hD.card_normalizer_eq]

end CFSG.EvenSporadicStandard.HNRecog.Harada
