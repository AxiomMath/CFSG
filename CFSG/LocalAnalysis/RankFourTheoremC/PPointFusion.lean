module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointStructure
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_zpowers' (y h : G) :
    (zpowers y).map (MulAut.conj h).toMonoidHom = zpowers (h * y * h⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]))

theorem exists_mem_mul_mem_normalizer_zpowers {P : Sylow 3 G} {x : G} {C : Subgroup G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hx3 : x ^ 3 = 1) (hxC : x ∈ C) {m : G} (hx'C : m * x * m⁻¹ ∈ C) :
    ∃ c ∈ C, c * m ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : ∀ y : G, y ∈ C → y ^ 3 = 1 → ∃ S : Subgroup G, IsSylowOf 3 S C ∧ y ∈ S := by
    intro y hy hy3
    have hyp : IsPGroup 3 ((zpowers y).subgroupOf C) := by
      have : IsPGroup 3 (zpowers y) := by
        have hyo : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
        rcases (Nat.dvd_prime Nat.prime_three).mp hyo with h | h
        · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
        · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
      exact this.comap_subtype
    obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
    exact ⟨(Q : Subgroup C).map C.subtype, ⟨Q, rfl⟩,
      ⟨⟨y, hy⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers y)), rfl⟩⟩
  obtain ⟨S₁, hS₁, hxS₁⟩ := hp3 x hxC hx3
  have hx'3 : (m * x * m⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
  obtain ⟨S₂, hS₂, hx'S₂⟩ := hp3 _ hx'C hx'3
  obtain ⟨k, hkC, hk⟩ := hS₁.exists_mem_conj hS₂
  have hyS₁ : k⁻¹ * (m * x * m⁻¹) * k ∈ S₁ := (hk _).mp hx'S₂
  obtain ⟨P', hP'⟩ := hS₁.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hS₁P : ∀ y ∈ S₁, g⁻¹ * y * g ∈ (P : Subgroup G) := by
    intro y hy
    have hyP' : y ∈ ((g • P : Sylow 3 G) : Subgroup G) := by rw [hg]; exact hP' hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hyP'
    exact hyP'
  have hconjP : ∀ y ∈ S₁, (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    intro y hy
    rw [map_conj_zpowers', zpowers_le]
    have := hS₁P y hy
    simpa [mul_assoc] using this
  set c : G := k⁻¹ with hc
  set y : G := k⁻¹ * (m * x * m⁻¹) * k with hy
  have hcC : c ∈ C := C.inv_mem hkC
  have h1 : (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x :=
    hwc g⁻¹ (hconjP x hxS₁)
  have h1' : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
    rw [Subgroup.map_map] at this
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hid, Subgroup.map_id] at this
    exact this.symm
  have hyx : zpowers y = (zpowers x).map (MulAut.conj (c * m)).toMonoidHom := by
    rw [map_conj_zpowers', hy, hc]
    congr 1
    group
  have hcomp : (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom =
      (zpowers x).map (MulAut.conj (g⁻¹ * (c * m))).toMonoidHom := by
    rw [hyx, Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  have h2 : (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x := by
    rw [hcomp]
    exact hwc _ (hcomp ▸ hconjP y hyS₁)
  have h3 : zpowers y = zpowers x := by
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h2
    rw [Subgroup.map_map] at this
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hid, Subgroup.map_id, h1'] at this
    exact this
  refine ⟨c, hcC, mem_normalizer_of_map_conj_le ?_⟩
  rw [← hyx, h3]

theorem exists_centralizer_mul_mem_normalizer_zpowers {P : Sylow 3 G} {x : G} {E : Subgroup G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hx3 : x ^ 3 = 1) (hxE : ∀ e ∈ E, x * e = e * x) {m : G} (hmE : m ∈ normalizer (E : Set G)) :
    ∃ c ∈ centralizer (E : Set G), c * m ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  set C : Subgroup G := centralizer (E : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_iff.mpr fun e he => (hxE e he).symm
  have hx'C : m * x * m⁻¹ ∈ C := by
    rw [mem_centralizer_iff]
    intro e he
    have h1 : m⁻¹ * e * m ∈ E := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hmE) e).mp he
      simpa using this
    have h2 := hxE _ h1
    calc e * (m * x * m⁻¹) = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by rw [h2]
      _ = m * x * m⁻¹ * e := by group
  exact exists_mem_mul_mem_normalizer_zpowers hwc hx3 hxC hx'C



omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer_zpowers {x n : G}
    (hn : n ∈ normalizer ((zpowers x : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) : n * c * n⁻¹ ∈ centralizer ({x} : Set G) := by
  have h : n⁻¹ * x * n ∈ zpowers x := by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp (mem_zpowers x)
    simpa using this
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  have hck : (n⁻¹ * x * n) * c = c * (n⁻¹ * x * n) := by
    rw [← hk]
    exact ((Commute.zpow_left (show Commute x c from (mem_centralizer_singleton_iff.mp hc).symm)
      k)).eq
  rw [mem_centralizer_singleton_iff]
  calc n * c * n⁻¹ * x = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by rw [hck]
    _ = x * (n * c * n⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem_normalizer_zpowers {x n : G}
    (hn : n ∈ normalizer ((zpowers x : Subgroup G) : Set G)) :
    n ∈ normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer_zpowers hn, fun hc => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer_zpowers (Subgroup.inv_mem _ hn) hc
  have e : n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c := by group
  rwa [e] at this

omit [Finite G] in
theorem exists_redCent_mulEquiv (p : ℕ) {x n : G}
    (hn : n ∈ normalizer ((zpowers x : Subgroup G) : Set G)) :
    ∃ e : RedCent p x ≃* RedCent p x, ∀ (c : G) (hc : c ∈ centralizer ({x} : Set G))
      (hnc : n * c * n⁻¹ ∈ centralizer ({x} : Set G)),
      e (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p) ⟨c, hc⟩) =
        QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          ⟨n * c * n⁻¹, hnc⟩ := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hnC : n ∈ normalizer (C : Set G) := mem_normalizer_centralizer_of_mem_normalizer_zpowers hn
  set σ : MulAut C := C.normalizerMonoidHom ⟨n, hnC⟩ with hσ
  have hσc : ∀ c : C, ((σ c : C) : G) = n * c * n⁻¹ := fun c =>
    Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨n, hnC⟩ c
  have hO : (primeComplementCore (G := C) p).map σ.toMonoidHom = primeComplementCore (G := C) p :=
    Subgroup.characteristic_iff_map_eq.mp (primeComplementCore_characteristic p) σ
  refine ⟨QuotientGroup.congr _ _ σ hO, fun c hc hnc => ?_⟩
  refine (QuotientGroup.congr_mk' _ _ σ hO ⟨c, hc⟩).trans ?_
  congr 1

end CFSG.LocalAnalysis.RankFourTheoremC
