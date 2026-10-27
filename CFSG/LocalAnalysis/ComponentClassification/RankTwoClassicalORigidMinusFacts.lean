module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusSyl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem ne_zero_of_irr (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  apply hirr r
  rw [hr]
  linear_combination r ^ 2 * CharTwo.two_eq_zero (R := K)

omit [Finite K] [CharP K 2] in
theorem ne_zero_of_irr' (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : c ≠ 0 := by
  intro h
  apply hirr 0
  rw [h]
  ring

theorem isSimpleGroup_statedOmega_quadMinus_of_two_le {m : ℕ} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (StatedOmega (StatedQuadMinus m K b c)) := by
  rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | h4
  · exact (isSimpleGroup_statedOmega_quadMinus_small (Or.inl rfl) hirr).1
  · exact (isSimpleGroup_statedOmega_quadMinus_small (Or.inr rfl) hirr).1
  · have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus h4 hirr
    exact (MulEquiv.ofBijective (oProj (StatedQuadMinus m K b c))
      ⟨oProj_injective_minus m b c, oProj_surjective _⟩).isSimpleGroup

theorem commutator_statedOmega_quadMinus_eq_top {m : ℕ} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    commutator (StatedOmega (StatedQuadMinus m K b c)) = ⊤ := by
  rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | h4
  · exact (isSimpleGroup_statedOmega_quadMinus_small (Or.inl rfl) hirr).2.1
  · exact (isSimpleGroup_statedOmega_quadMinus_small (Or.inr rfl) hirr).2.1
  · exact (isPerfect_statedOmega_quadMinus h4 hirr).commutator_eq_top

theorem noNormalTwo_of_isSimpleGroup {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hs : IsSimpleGroup H) (hna : ¬ ∀ x y : H, x * y = y * x) : NoNormalTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q hQ hQ2 hN
  have hnorm : (Q.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp (hN g.2) x).mp hx
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf H) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hQ hx⟩ : H) ∈ Q.subgroupOf H := by rwa [mem_subgroupOf]
    rw [h, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  · exfalso
    have hH2 : IsPGroup 2 H := by
      intro x
      have hxQ : (x : G) ∈ Q := by
        have : x ∈ Q.subgroupOf H := by rw [h]; trivial
        rwa [mem_subgroupOf] at this
      obtain ⟨k, hk⟩ := hQ2 ⟨x, hxQ⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hnt : Nontrivial H := hs.toNontrivial
    have hZ := hH2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with hc | hc
    · rw [hc] at hZ
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hZ
      rw [Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · apply hna
      intro x y
      have hx : x ∈ center H := by rw [hc]; trivial
      exact (Subgroup.mem_center_iff.mp hx y).symm

theorem noNormalTwo_statedOmega_quadMinus {m : ℕ} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NoNormalTwo (StatedOmega (StatedQuadMinus m K b c)) := by
  have hs := isSimpleGroup_statedOmega_quadMinus_of_two_le hm hirr
  refine noNormalTwo_of_isSimpleGroup hs fun hc => ?_
  have hperf := commutator_statedOmega_quadMinus_eq_top hm hirr
  have hbot : commutator (StatedOmega (StatedQuadMinus m K b c)) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  rw [hperf] at hbot
  have := hs.toNontrivial
  exact top_ne_bot hbot

omit [CharP K 2] in
theorem polar_eq_zero_of_eichler_fix {m : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {e w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} (he2 : ∀ t, e (.inr (.inr t)) = 0) (t : Fin 2)
    (hw : (quadMinusForm m K b c hirr).eichler e (maniso (Pi.single t 1)) w = w) :
    quadMinusPolar m K b c e w = 0 := by
  have h := congrFun hw (.inr (.inr t))
  rw [QuadForm.eichler_apply] at h
  change (w + quadMinusPolar m K b c e w • (maniso (Pi.single t 1) -
    StatedQuadMinus m K b c (maniso (Pi.single t 1)) • e) -
      quadMinusPolar m K b c (maniso (Pi.single t 1)) w • e :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) (.inr (.inr t)) = w (.inr (.inr t)) at h
  simpa [he2, maniso] using h

omit [CharP K 2] in
theorem polar_maniso_eq_zero_of_eichler_fix {m : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {e w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {j : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2}
    (hej : e j = 1) (z : Fin 2 → K)
    (hew : quadMinusPolar m K b c e w = 0)
    (hw : (quadMinusForm m K b c hirr).eichler e (maniso z) w = w) :
    quadMinusPolar m K b c (maniso z) w = 0 := by
  have h := congrFun hw j
  rw [QuadForm.eichler_apply] at h
  change (w + quadMinusPolar m K b c e w • (maniso z - StatedQuadMinus m K b c (maniso z) • e) -
      quadMinusPolar m K b c (maniso z) w • e :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) j = w j at h
  simpa [hew, hej] using h

theorem eq_zero_of_forall_statedOmega_quadMinus_mulVec_eq {m : ℕ} (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K}
    (hw : ∀ Y ∈ StatedOmega (StatedQuadMinus m K b c), (Y : Matrix _ _ K) *ᵥ w = w) : w = 0 := by
  have hfix : ∀ {e : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K}, StatedQuadMinus m K b c e = 0 →
      ∀ z, quadMinusPolar m K b c e (maniso z) = 0 →
        (quadMinusForm m K b c hirr).eichler e (maniso z) w = w := fun he z hez => by
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler_maniso hirr he z hez
    rw [← hAv]
    exact hw A hA
  have hx : ∀ (i : Fin (m - 1)) z,
      quadMinusPolar m K b c (Pi.single (.inl i) 1) (maniso z) = 0 := fun i z => by
    rw [quadMinusPolar_single_inl, maniso_inr_inl]
  have hy : ∀ (i : Fin (m - 1)) z,
      quadMinusPolar m K b c (Pi.single (.inr (.inl i)) 1) (maniso z) = 0 := fun i z => by
    rw [quadMinusPolar_single_inr_inl, maniso_inl]
  have hwy : ∀ i, w (.inr (.inl i)) = 0 := fun i => by
    have h := polar_eq_zero_of_eichler_fix hirr (e := Pi.single (.inl i) 1)
      (fun t => by simp) 0
      (hfix (statedQuadMinus_single_inl i) _ (hx i _))
    rwa [quadMinusPolar_single_inl] at h
  have hwx : ∀ i, w (.inl i) = 0 := fun i => by
    have h := polar_eq_zero_of_eichler_fix hirr (e := Pi.single (.inr (.inl i)) 1)
      (fun t => by simp) 0
      (hfix (statedQuadMinus_single_inr_inl i) _ (hy i _))
    rwa [quadMinusPolar_single_inr_inl] at h
  have i₀ : Fin (m - 1) := ⟨0, by omega⟩
  have hb := ne_zero_of_irr hirr
  have ha : ∀ z, quadMinusPolar m K b c (maniso z) w = 0 := fun z =>
    polar_maniso_eq_zero_of_eichler_fix hirr (e := Pi.single (.inl i₀) 1) (j := .inl i₀)
      (by simp) z (by rw [quadMinusPolar_single_inl, hwy])
      (hfix (statedQuadMinus_single_inl i₀) z (hx i₀ z))
  have h0 := ha (Pi.single 0 1)
  have h1 := ha (Pi.single 1 1)
  rw [quadMinusPolar_maniso] at h0 h1
  have hu1 : w (.inr (.inr 1)) = 0 := by simpa [hb] using h0
  have hu0 : w (.inr (.inr 0)) = 0 := by simpa [hb] using h1
  funext j
  rcases j with i | i | t
  · exact hwx i
  · exact hwy i
  · fin_cases t
    · exact hu0
    · exact hu1

theorem card_statedOmega_quadMinus_ne_card_sl (j : ℕ) (hSL : commutator SL(2, K) = ⊤) :
    Nat.card (StatedOmega (StatedQuadMinus (j + 3) K b c)) ≠ Nat.card SL(2, K) := by
  intro h
  have hinj : Function.Injective
      (oRhoTwo (minusOe j) (statedQuadMinus_minusOe j b c) hSL) := oRhoTwo_injective
  obtain ⟨A, hA⟩ := (hinj.bijective_of_nat_card_le h.le).2
    (oRhoOne (minusOe j) (statedQuadMinus_minusOe j b c) hSL (slTr 1))
  have h1 := congrArg (fun g : StatedOmega (StatedQuadMinus (j + 3) K b c) => g.1.1) hA
  simp only [coe_oRhoTwo, coe_oRhoOne] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoTwoMat_apply, rhoOneMat_apply, fromBlocks_inj] at h2
  have h3 := congrFun (congrFun h2.2.1 0) 1
  simp [slTr, swapM] at h3

end CFSG.ComponentClassification.RankTwoClassical.ORigid
