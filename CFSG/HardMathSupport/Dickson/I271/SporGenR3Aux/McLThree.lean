module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PairCover
public import CFSG.Sporadic.Recognition.LyonsLocalThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.McLAS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section McL


theorem mcl_card_centralizer_eq_or {y : NativeSporadic.McL} (hy : orderOf y = 3) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.McL)) = 29160 ∨
      Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.McL)) = 972 := by
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  rcases hall y hy with h | h
  · left; rw [card_centralizer_eq_of_isConj h]; exact c₁
  · right; rw [card_centralizer_eq_of_isConj h]; exact c₂

theorem mcl_exists_threeCore {y : NativeSporadic.McL} (hy : orderOf y = 3)
    (hc : Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.McL)) = 29160) :
    ∃ R : Subgroup NativeSporadic.McL, ThreeCore y R := by
  obtain ⟨x, R, T, A, hL⟩ := mcl_threeLocal_of_certificate
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  have hxy : IsConj x y := isConj_of_card_eq_aux c₂ hall hL.order_x hy hL.card_centralizer hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  have h1 := (ThreeCore.of_threeLocal hL.toThreeLocal).map (MulAut.conj g)
  rw [MulAut.conj_apply, hg] at h1
  exact ⟨_, h1⟩

theorem mcl_card_dvd_of_centralizes {N R : Subgroup NativeSporadic.McL}
    (hNR : N ≤ Subgroup.centralizer (R : Set NativeSporadic.McL)) (hR : Nat.card R = 243)
    (hN : Nat.card N ∣ 29160) : Nat.card N ∣ 2 ^ 3 * 3 ^ 6 := by
  have h5 : ¬ 5 ∣ Nat.card N := by
    intro h5
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 5 h5
    have hg5 : orderOf (g : NativeSporadic.McL) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
    obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ := mcl_two_classes_order_five_of_certificate
    have hRle : R ≤ Subgroup.centralizer ({(g : NativeSporadic.McL)} : Set NativeSporadic.McL) := by
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (hNR g.2) r hr)
    have hdvd : Nat.card R ∣ Nat.card (Subgroup.centralizer
        ({(g : NativeSporadic.McL)} : Set NativeSporadic.McL)) := Subgroup.card_dvd_of_le hRle
    rw [hR] at hdvd
    rcases hall _ hg5 with h | h
    · rw [card_centralizer_eq_of_isConj h, c₁] at hdvd
      omega
    · rw [card_centralizer_eq_of_isConj h, c₂] at hdvd
      omega
  have hcop : Nat.Coprime (Nat.card N) 5 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5))
  have h1 : Nat.card N ∣ 5832 * 5 := by simpa using hN
  have h2 : Nat.card N ∣ 5832 := hcop.dvd_of_dvd_mul_right h1
  simpa using h2

theorem mcl_pConstrained_three (hO : OPrimeCoreTrivialAt 3 NativeSporadic.McL)
    (k : NativeSporadic.McL) (hord : orderOf k = 3) :
    PConstrainedShape 3 (Subgroup.centralizer ({k} : Set NativeSporadic.McL)) := by
  have hOk : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({k} : Set NativeSporadic.McL)) = ⊥ :=
    hO k hord
  rcases mcl_card_centralizer_eq_or hord with h | h
  · obtain ⟨R, hR⟩ := mcl_exists_threeCore hord h
    refine pConstrainedShape_of_centralizer_solvable Nat.prime_three hR.le_cent hR.normal
      hR.isPGroup hR.max hOk ?_
    have hN : Nat.card ↥(Subgroup.centralizer ({k} : Set NativeSporadic.McL) ⊓
        Subgroup.centralizer (R : Set NativeSporadic.McL)) ∣ 2 ^ 3 * 3 ^ 6 := by
      refine mcl_card_dvd_of_centralizes (R := R) inf_le_right hR.card ?_
      rw [← h]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact isSolvable_of_card_dvd_two_three hN
  · exact pConstrainedShape_of_solvable Nat.prime_three
      (isSolvable_of_card_two_pow_mul_three_pow (a := 2) (b := 5) (by rw [h]; norm_num)) hOk

theorem mcl_constrainedShape_three (hO : OPrimeCoreTrivialAt 3 NativeSporadic.McL) :
    ConstrainedShape .McL 3 :=
  fun k hk1 hk3 => mcl_pConstrained_three hO k (orderOf_eq_prime hk3 hk1)

end McL

end CFSG.HardMathSupport.Dickson.I271
