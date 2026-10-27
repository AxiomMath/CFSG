module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G7
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.EvenSmallLie.Sp6

namespace Four

theorem card_centralizer_sp62
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSp 3 2 1) (v : Y) (hv : orderOf v = 2) :
    Nat.card (Subgroup.centralizer ({v} : Set Y)) = 23040 ∨
      Nat.card (Subgroup.centralizer ({v} : Set Y)) = 4608 ∨
      Nat.card (Subgroup.centralizer ({v} : Set Y)) = 1536 ∨
      Nat.card (Subgroup.centralizer ({v} : Set Y)) = 384 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hY
  obtain ⟨hcov, h1, h2, h3, h4, -⟩ := co3X36_involution_centralizers
  have hord : orderOf (e v : Equiv.Perm (Fin 36)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv]
  obtain ⟨r, hr, c, hc, hcr⟩ := hcov _ (e v).2 hord
  have hcard : Nat.card (Subgroup.centralizer ({v} : Set Y)) =
      Nat.card (centralizerIn co3X36 r) := by
    rw [Nat.card_congr ((centralizerEquiv e v).trans
      (centralizerSubgroupEquiv co3X36 (e v))).toEquiv, hcr,
      ← Nat.card_congr (centralizerInConjEquiv co3X36 hc r).toEquiv]
  rw [hcard]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

theorem not_isPGroup_centralizer_sp62
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSp 3 2 1) (v : Y) (hv : orderOf v = 2) :
    ¬ IsPGroup 2 (Subgroup.centralizer ({v} : Set Y)) := by
  intro hP
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set Y)) := by
    rcases card_centralizer_sp62 hY v hv with h | h | h | h <;> rw [h] <;> norm_num
  rw [hn] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem not_isPGroup_centralizer_omega8 {Y : Type} [Group Y]
    [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1) (v : Y) (hv : orderOf v = 2) :
    ¬ IsPGroup 2 (Subgroup.centralizer ({v} : Set Y)) := by
  intro hP
  have hodd := CFSG.EvenSmallLie.OmegaEight.involutionsInOddPart_of_lieModel hY v hv
  have hsub : {g : Y | g * v = v * g ∧ Odd (orderOf g)} ⊆ ({1} : Set Y) := by
    rintro g ⟨hg, hgo⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP)
      ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg⟩
    have hk' : orderOf g = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have : Even (orderOf g) := by
        rw [hk']
        exact Nat.even_pow.mpr ⟨even_two, hk0⟩
      exact (Nat.not_even_iff_odd.mpr hgo) this
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  have h1 : Subgroup.closure {g : Y | g * v = v * g ∧ Odd (orderOf g)} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    exact hsub hg
  have hv1 : v = 1 := Subgroup.mem_bot.mp (h1 hodd)
  rw [hv1, orderOf_one] at hv
  omega

theorem e4TwinFactsQ8_of_certs :
    E4TwinFactsQ8 := by
  intro Q _ _ hQ w hw
  rcases hQ with hQ | hQ
  · exact not_isPGroup_centralizer_sp62 hQ w hw
  · exact not_isPGroup_centralizer_omega8 hQ w hw

end Four

section Final


theorem twinCentral4_holds
    (n : ℕ) : TwinCentral4 n :=
  twinCentral4_of_facts Four.e4TwinFactsQ8_of_certs n

end Final

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
