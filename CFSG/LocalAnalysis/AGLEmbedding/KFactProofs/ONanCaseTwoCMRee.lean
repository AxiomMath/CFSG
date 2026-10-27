module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeMaximal
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding

theorem three_pow_odd_mod (m : ℕ) :
    (3 ^ (2 * m + 1) % 16 = 3 ∨ 3 ^ (2 * m + 1) % 16 = 11) ∧
    (3 ^ (2 * m + 1) % 5 = 2 ∨ 3 ^ (2 * m + 1) % 5 = 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have : 3 ^ (2 * (m + 1) + 1) = 3 ^ (2 * m + 1) * 9 := by ring
    rw [this]
    omega

theorem ree_order_mod_sixteen {q : ℕ} (hq : q % 16 = 3 ∨ q % 16 = 11) :
    (q ^ 3 * (q ^ 3 + 1) * (q - 1)) % 16 = 8 := by
  rcases hq with h | h
  · have e1 : q ^ 3 % 16 = 11 := by rw [Nat.pow_mod, h]
    have e2 : (q - 1) % 16 = 2 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), Nat.add_mod, e1, e2]
  · have e1 : q ^ 3 % 16 = 3 := by rw [Nat.pow_mod, h]
    have e2 : (q - 1) % 16 = 10 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), Nat.add_mod, e1, e2]

theorem ree_order_mod_five {q : ℕ} (hq : q % 5 = 2 ∨ q % 5 = 3) :
    (q ^ 3 * (q ^ 3 + 1) * (q - 1)) % 5 = 2 := by
  rcases hq with h | h
  · have e1 : q ^ 3 % 5 = 3 := by rw [Nat.pow_mod, h]
    have e2 : (q - 1) % 5 = 1 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), Nat.add_mod, e1, e2]
  · have e1 : q ^ 3 % 5 = 2 := by rw [Nat.pow_mod, h]
    have e2 : (q - 1) % 5 = 2 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), Nat.add_mod, e1, e2]


theorem ree_card_facts
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (e : K ≃* CatGroup d) : ¬ 5 ∣ Nat.card K ∧ ¬ 16 ∣ Nat.card K := by
  have hcard := kFactReeOrder K d hd ⟨e⟩
  obtain ⟨m, hm⟩ := hd.odd_fieldExponent
  rw [hm] at hcard
  obtain ⟨h16, h5⟩ := three_pow_odd_mod m
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := ree_order_mod_five h5
    rw [← hcard] at this
    omega
  · have := ree_order_mod_sixteen h16
    rw [← hcard] at this
    omega

theorem ree_no_orderOf_four
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (e : K ≃* CatGroup d) (x : K) : orderOf x ≠ 4 := by
  intro hx
  obtain ⟨a, ha, -, ⟨eT⟩⟩ := ReeModel.exists_equiv_reeGamma hd ⟨e⟩
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element CFSG.LieType.Ree.ReeTag.G2.tag
  have hord : orderOf (eT x) = 4 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hP : IsPGroup 2 (Subgroup.zpowers (eT x)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num)
  have h2 := CFSG.ComponentClassification.LiteratureLocal.SmallRee.sq_eq_one_of_isPGroup_two hK
    hw₀ hP (Subgroup.mem_zpowers _)
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at this
  omega

theorem ree_section_facts
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (e : K ≃* CatGroup d) (B : Subgroup K) {Y : Type} [Group Y] (g : B →* Y)
    (hg : Function.Surjective g) :
    ¬ 5 ∣ Nat.card Y ∧ ¬ 16 ∣ Nat.card Y ∧ ∀ y : Y, orderOf y ≠ 4 := by
  obtain ⟨h5, h16⟩ := ree_card_facts hd e
  have hdvd : Nat.card Y ∣ Nat.card K :=
    (Subgroup.card_dvd_of_surjective hg).trans (Subgroup.card_subgroup_dvd_card B)
  refine ⟨fun h => h5 (h.trans hdvd), fun h => h16 (h.trans hdvd), fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_orderOf_eq_of_surjective B g hg hy
  exact ree_no_orderOf_four hd e x hx

theorem ree_sections
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (e : K ≃* CatGroup d) (B : Subgroup K) (Y : Type) [Group Y] (g : B →* Y)
    (hg : Function.Surjective g) (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : IsClassicalTwoOrG2 Y ∨ IsOrthogonalTwo Y ∨
      ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n))) :
    IsCaseTwoGroup 3 Y ∧ ¬ IsOrthogonalTwo Y ∧
      ¬ ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  obtain ⟨h5, h16, h4⟩ := ree_section_facts hd e B g hg
  have hnorth : ¬ IsOrthogonalTwo Y := fun ho => false_of_orthogonalTwo_of_not_dvd hs hna h5 h16 ho
  have hnalt : ¬ ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n)) := fun ⟨n, ⟨ea⟩⟩ =>
    false_of_alternating_of_not_five_dvd hs hna h5 ea
  refine ⟨?_, hnorth, hnalt⟩
  rcases h with hc | ho | ha
  · exact isCaseTwoGroup_three_of_classical hs hna h5 h16 h4 hc
  · exact (hnorth ho).elim
  · exact (hnalt ha).elim

end CFSG.AGLEmbedding
