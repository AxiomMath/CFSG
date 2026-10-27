module

public import CFSG.LieType.SeitzGeneration.SpF2.Core
public import CFSG.LieType.SeitzGeneration.SpF2.Config
public import CFSG.LieType.SeitzGeneration.RootPairSpOdd

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.RootPair
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

theorem charP_two_of_subfield_card_two {K : Type} [Field K] {k : Subfield K}
    (hk : Nat.card k = 2) : CharP K 2 := by
  rcases SpF2.eq_zero_or_eq_one_of_card_two hk (k.add_mem k.one_mem k.one_mem) with h | h
  · exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by push_cast; linear_combination h)
  · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero

theorem subfieldPairSpF2_holds : SubfieldPairSpF2 := by
  intro K _ _ k p hp hp2 hK hk r hr A hne
  classical
  have : CharP K 2 := charP_two_of_subfield_card_two hk
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set X : Subgroup (StatedSp r K) := Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
    ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) with hXdef
  have hsp : spSub r k ≤ X := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hmap : (spSub r k).map (conjSp r K A).toMonoidHom ≤ X :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hrat1 : ∀ v₀ : Fin r ⊕ Fin r → k, spTransvection (ratVec v₀) 1 ∈ X := by
    intro v₀
    have h := CFSG.RankThree.PartOne.KCSpComm.subfieldSpHom_spTransvection k v₀ 1
    exact hsp ⟨_, h⟩
  obtain ⟨a₀, a₀'', b, haa, hab, hlam, hbX⟩ := SpF2.exists_config hp hp2 hK hr A hne
  obtain ⟨μ, hμk⟩ : ∃ μ : K, μ ∉ k := by
    by_contra hall
    push Not at hall
    have hcard : Nat.card k = Nat.card K := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hK, hk] at hcard
    have h1 : 2 ^ 1 = 2 ^ p := by rw [pow_one]; exact hcard
    have := Nat.pow_right_injective (le_refl 2) h1
    exact hp.one_lt.ne this
  have hμ0 : μ ≠ 0 := fun h => hμk (h ▸ k.zero_mem)
  obtain ⟨y, hyX, hy⟩ := SpF2.exists_eigen hk hp hp2 hK haa hab hlam (hrat1 a₀) (hrat1 a₀'')
    (hmap hbX) μ hμ0
  set v₀ : Fin r ⊕ Fin r → k := a₀ + a₀'' with hv₀def
  have hv : ratVec v₀ = ratVec a₀ + ratVec a₀'' := by
    funext i
    simp [hv₀def, ratVec]
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    apply hlam
    have ha'' : ratVec a₀'' = ratVec a₀ := by
      have : ratVec a₀ + ratVec a₀'' = 0 := by rw [← hv, h0]; funext i; simp [ratVec]
      have h' := eq_neg_of_add_eq_zero_right this
      rw [h']
      funext i
      simp [CharTwo.neg_eq]
    rw [ha'', div_self hab]
    exact k.one_mem
  have hTμ : spTransvection (ratVec v₀) (μ * μ) ∈ X := by
    have h1 := X.mul_mem (X.mul_mem hyX (hrat1 v₀)) (X.inv_mem hyX)
    rw [spTransvection_conj, hv, hy, spTransvection_smul, mul_one] at h1
    rwa [← hv] at h1
  obtain ⟨i, hi⟩ : ∃ i, v₀ i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv₀ (funext hall)
  have hi1 : (v₀ i : K) = 1 := by
    rcases SpF2.eq_zero_or_eq_one_of_card_two hk (v₀ i).2 with h | h
    · exact absurd (Subtype.ext h) hi
    · exact h
  set w₀ : Fin r ⊕ Fin r → k := -(dualVec i : Fin r ⊕ Fin r → k) with hw₀def
  have hw : ratVec w₀ = -(dualVec i : Fin r ⊕ Fin r → K) := by
    rw [hw₀def, dualVec_rat (k := k) i]
    funext a
    simp [ratVec]
  have hvw : spForm r K (ratVec v₀) (ratVec w₀) = 1 := by
    rw [hw, map_neg, SpF2.spForm_swap_two, spForm_dualVec]
    simp only [ratVec]
    rw [hi1, CharTwo.neg_eq]
  set M : Subgroup (SpecialLinearGroup (Fin 2) K) := X.comap (RootPair.spSL2Hom hvw) with hMdef
  have hmemM : ∀ x : K, spTransvection (ratVec v₀) x ∈ X → u2 x ∈ M := by
    intro x hx
    show RootPair.spSL2Hom hvw (u2 x) ∈ X
    rw [RootPair.spSL2Hom_u2, CharTwo.neg_eq]
    exact hx
  have hμ2 : μ * μ / 1 ∉ k := by
    rw [div_one, ← sq]
    intro h
    exact hμk (mem_subfield_of_sq_mem k h)
  have hM : M = ⊤ := by
    refine sl2_eq_top_of_root_groups hp hp2 hK one_ne_zero hμ2 one_ne_zero ?_ ?_
    · intro c₁ hc₁ c₂ hc₂
      rcases SpF2.eq_zero_or_eq_one_of_card_two hk hc₁ with rfl | rfl <;>
        rcases SpF2.eq_zero_or_eq_one_of_card_two hk hc₂ with rfl | rfl
      · rw [show (0 : K) * 1 + 0 * (μ * μ) = 0 by ring, u2_zero]; exact M.one_mem
      · rw [show (0 : K) * 1 + 1 * (μ * μ) = μ * μ by ring]; exact hmemM _ hTμ
      · rw [show (1 : K) * 1 + 0 * (μ * μ) = 1 by ring]; exact hmemM _ (hrat1 v₀)
      · rw [show (1 : K) * 1 + 1 * (μ * μ) = 1 + μ * μ by ring, u2_add]
        exact M.mul_mem (hmemM _ (hrat1 v₀)) (hmemM _ hTμ)
    · show RootPair.spSL2Hom hvw (l2 1) ∈ X
      rw [RootPair.spSL2Hom_l2]
      exact hrat1 w₀
  have hcen : TransCenter X (ratVec v₀) := by
    intro t
    have h1 : u2 (-t) ∈ M := by rw [hM]; trivial
    have h3 : RootPair.spSL2Hom hvw (u2 (-t)) ∈ X := h1
    rwa [RootPair.spSL2Hom_u2, neg_neg] at h3
  exact eq_top_of_rat_centers fun u₀ hu₀ => transCenter_rat hsp hv₀ hcen hu₀

end CFSG.LieType.SeitzGeneration
