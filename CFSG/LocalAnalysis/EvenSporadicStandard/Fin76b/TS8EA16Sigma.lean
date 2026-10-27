module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8EA16

open CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.Monster.B.Co2 Subgroup

theorem checkEA16_checkD8 {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)}
    (h : checkEA16 n A B U ws = true) : checkD8 n A B U ws = true := by
  simp only [checkEA16, Bool.and_eq_true] at h
  exact h.1

theorem checkEA16_chain {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)}
    (h : checkEA16 n A B U ws = true) :
    hasChainIx (mulTabT n (bfsT n (gensT n A B U ws)).1 (idxT (bfsT n (gensT n A B U ws)).1)) 5 [0]
      (invsIx (mulTabT n (bfsT n (gensT n A B U ws)).1 (idxT (bfsT n (gensT n A B U ws)).1))) =
      false := by
  simp only [checkEA16, chainFreeCheck, Bool.and_eq_true] at h
  simpa using h.2

section Generic

variable {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)} {E M : Array (Array ℕ)} {I : Array ℕ}
  {gens : Array (Array ℕ)} {par gen : Array ℕ}

theorem card_le_sigma (h : TabOK n A B U ws E M I gens par gen)
    (hch : hasChainIx M 5 [0] (invsIx M) = false) {K : Subgroup (Equiv.Perm (Fin n))}
    (hK : K ≤ sigmaT h) (hsq : ∀ b ∈ K, b * b = 1) : Nat.card ↥K ≤ 16 :=
  chain_bound (EpT n E) M (EpT_zero h)
    (fun a ha b hb => ⟨mulIx_lt h ha hb, EpT_mul h ha hb⟩)
    (fun a ha b hb hab => EpT_inj h ha hb hab) hch
    (fun b hb => hK hb) hsq

end Generic

theorem elAb16_of_sylow {G : Type} [Group G] [Finite G] {m : ℕ} (hG : Nat.card G = 256 * m)
    (hm : ¬ 2 ∣ m) (S0 : Subgroup G) (hS0card : Nat.card S0 = 256)
    (hq : ∀ K : Subgroup G, K ≤ S0 → (∀ b ∈ K, b * b = 1) → Nat.card ↥K ≤ 16)
    (A : Subgroup G) (hA : ∀ a ∈ A, a * a = 1) : Nat.card ↥A ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS0p : IsPGroup 2 S0 := IsPGroup.of_card (n := 8) (by rw [hS0card]; norm_num)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (ea16_isPGroup_two hA)
  have hPmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ ⊤ → S0 ≤ R → R ≤ S0 :=
    fun R hR _ hle => max_of_card_odd hG hm hS0card hR hle
  have hQmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ ⊤ → (Q : Subgroup G) ≤ R →
      R ≤ (Q : Subgroup G) :=
    fun R hR _ hle => (Q.is_maximal' hR hle).le
  obtain ⟨g, -, hg⟩ := sylow_conj le_top le_top hS0p Q.isPGroup' hPmax hQmax
  have hconj : ∀ x : G, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := fun x => by
    simp [MulAut.conj_apply]
  have hB : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ S0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    exact (hg x).1 (hQ hx)
  have hBsq : ∀ b ∈ A.map (MulAut.conj g⁻¹).toMonoidHom, b * b = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hA x hx]; group
  have hc : Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hc]
  exact hq _ hB hBsq

theorem elAb16_of_table {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)} {m : ℕ}
    {R : Subgroup (Equiv.Perm (Fin n))} (hG : Nat.card R = 256 * m) (hm : ¬ 2 ∣ m)
    (hC : checkEA16 n A B U ws = true) (hRA : permOfArr n A ∈ R) (hRB : permOfArr n B ∈ R)
    (hRU : permOfArr n U ∈ R) : ElAb16 ↥R := by
  have h := checkD8_tabOK (checkEA16_checkD8 hC)
  have hch := checkEA16_chain hC
  have hsub : Nat.card ((sigmaT h : Subgroup (Equiv.Perm (Fin n))).subgroupOf R) = 256 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sigmaT_le h hRA hRB hRU)).toEquiv).trans
      (card_sigmaT h)
  intro A' hA'
  refine elAb16_of_sylow hG hm _ hsub ?_ A' hA'
  intro K hK hKsq
  have hmap : K.map R.subtype ≤ sigmaT h := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hK hb)
  have hcard : Nat.card ↥(K.map R.subtype) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective R)
  rw [← hcard]
  refine card_le_sigma h hch hmap ?_
  rintro _ ⟨b, hb, rfl⟩
  have hbb := congrArg Subtype.val (hKsq b hb)
  simpa using hbb

end CFSG.EvenSporadicStandard.Fin76b.TS8EA16
