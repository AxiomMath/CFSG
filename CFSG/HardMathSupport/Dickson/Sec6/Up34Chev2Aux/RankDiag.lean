module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Rank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance

theorem Up34Pumpup.exists_elemAbelian_aut_gt_nine {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {α : MulAut S} (h : Up34Pumpup S α) :
    ∃ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B ∧ 9 < Nat.card B ∧
      B ≤ Subgroup.zpowers α ⊔ (MulAut.conj : S →* MulAut S).range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := h
  have hαI : ∀ i ∈ I, α i = i := fun i hi => hI.1 hi
  have hcinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun φ : MulAut S => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      exact (mul_inv_eq_iff_eq_mul.1 hx).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨Eb, hEb, hEb9⟩ := exists_elemAbelian_nine_of_isLThreeFour hI34
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥I)
  obtain ⟨P, -, hP, hPcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift (p := 3)
    (GLAPPrimeCore 3 ↥I) hN3 hEb
  rw [hEb9] at hPcard
  have hinj : Function.Injective I.subtype := Subtype.val_injective
  set P' : Subgroup S := P.map I.subtype with hP'def
  have hP' : CFSG.Assembly.IsElemAbelian 3 P' := isElemAbelian_map_up34 I.subtype hinj hP
  have hP'card : Nat.card P' = 9 := by
    rw [hP'def, Subgroup.card_map_of_injective hinj]
    exact hPcard
  set P'' : Subgroup (MulAut S) := P'.map (MulAut.conj : S →* MulAut S) with hP''def
  have hP'' : CFSG.Assembly.IsElemAbelian 3 P'' := isElemAbelian_map_up34 _ hcinj hP'
  have hP''card : Nat.card P'' = 9 := by
    rw [hP''def, Subgroup.card_map_of_injective hcinj]
    exact hP'card
  have hαP'' : ∀ a ∈ P'', a * α = α * a := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := Subgroup.mem_map.1 hy
    refine MulEquiv.ext fun z => ?_
    have hi : α (I.subtype i) = I.subtype i := hαI i.1 i.2
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_subtype] at hi ⊢
    rw [hi]
  have hαnot : α ∉ P'' := by
    intro hαP
    obtain ⟨y, hy, hyα⟩ := Subgroup.mem_map.1 hαP
    obtain ⟨i, hi, hiy⟩ := Subgroup.mem_map.1 hy
    have hic : ∀ j : ↥I, i * j = j * i := by
      intro j
      apply Subtype.ext
      have h1 := congrArg (fun φ : MulAut S => φ (j : S)) hyα
      have h2 := hαI j.1 j.2
      simp only [MulAut.conj_apply] at h1
      rw [h2, ← hiy] at h1
      change (i : S) * j * (i : S)⁻¹ = j at h1
      calc (i : S) * j = (i : S) * j * (i : S)⁻¹ * i := by group
        _ = j * i := by rw [h1]
    have hcen : (QuotientGroup.mk i : ↥I ⧸ GLAPPrimeCore 3 ↥I) ∈
        Subgroup.center (↥I ⧸ GLAPPrimeCore 3 ↥I) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H j =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hic j]
    obtain ⟨hsimp, hnab⟩ := isSimpleGroup_of_isLThreeFour hI34
    haveI := hsimp
    rw [up34_center_eq_bot_of_simple hnab, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    have hi3 : i ^ 3 = 1 := hP.2 i hi
    have hi1 : i ≠ 1 := by
      intro h1
      apply hα1
      rw [← hyα, ← hiy, h1]
      simp
    have hdvd : orderOf (⟨i, hcen⟩ : ↥(GLAPPrimeCore 3 ↥I)) ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
      orderOf_dvd_natCard _
    have hord : orderOf (⟨i, hcen⟩ : ↥(GLAPPrimeCore 3 ↥I)) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hi3 hi1
    rw [hord] at hdvd
    exact hN3 hdvd
  refine ⟨P'' ⊔ Subgroup.zpowers α, ?_, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec8.Item82OneProof.isElemAbelian_sup_zpowers hP'' hα3 hαP''
  · have hle : P'' ≤ P'' ⊔ Subgroup.zpowers α := le_sup_left
    have hαE : α ∈ P'' ⊔ Subgroup.zpowers α := Subgroup.mem_sup_right (Subgroup.mem_zpowers α)
    by_contra hcon
    push Not at hcon
    have heq : P'' = P'' ⊔ Subgroup.zpowers α := Subgroup.eq_of_le_of_card_ge hle (by omega)
    exact hαnot (heq ▸ hαE)
  · refine sup_le ?_ le_sup_left
    intro a ha
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 ha
    exact Subgroup.mem_sup_right ⟨y, rfl⟩

end CFSG.HardMathSupport.Dickson.Sec6
