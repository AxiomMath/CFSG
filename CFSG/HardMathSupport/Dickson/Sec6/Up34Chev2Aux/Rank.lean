module

public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_projectiveSL_equiv_of_isLThreeFour' {X : Type} [Group X] (h : IsLThreeFour X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hcard,
    ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F)⟩⟩

theorem exists_elemAbelian_nine_of_isLThreeFour {X : Type} [Group X] [Finite X]
    (h : IsLThreeFour X) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := exists_projectiveSL_equiv_of_isLThreeFour' h
  refine ⟨(CFSG.RankThree.PartTwo.KFacts.L34.eZero F).map e.symm.toMonoidHom, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    refine Subtype.ext ?_
    show _ * _ = _ * _
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, CFSG.RankThree.PartTwo.KFacts.L34.commute_of_mem_eZero hF4 ha' hb']
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, CFSG.RankThree.PartTwo.KFacts.L34.pow_three_of_mem_eZero hF4 ha', map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hF4

theorem isElemAbelian_map_up34 {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian p B) :
    CFSG.Assembly.IsElemAbelian p (B.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    have h := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    rw [← hxa, ← hzb, ← map_mul, ← map_mul, h]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hB.2 x hx, map_one]

theorem Up34Pumpup.exists_elemAbelian_gt_nine {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {x : S} (h : Up34Pumpup S (MulAut.conj x)) :
    ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E ∧ 9 < Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx3', hx1', I, hI, hI34⟩ := h
  have hx3 : x ^ 3 = 1 := by
    have h1 : (MulAut.conj (x ^ 3) : MulAut S) = 1 := by rw [map_pow]; exact hx3'
    have h2 : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h1 g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
        _ = x ^ 3 * g := by group
    rwa [hZ, Subgroup.mem_bot] at h2
  have hxne : x ≠ 1 := fun h' => hx1' (by rw [h', map_one])
  have hxI : ∀ i ∈ I, x * i = i * x := by
    intro i hi
    have h' : MulAut.conj x i = i := hI.1 hi
    rw [MulAut.conj_apply] at h'
    calc x * i = x * i * x⁻¹ * x := by group
      _ = i * x := by rw [h']
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
  have hxP' : ∀ a ∈ P', a * x = x * a := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Subgroup.mem_map.1 ha
    exact (hxI i.1 i.2).symm
  have hxnot : x ∉ P' := by
    intro hxP
    obtain ⟨i, hi, hix⟩ := Subgroup.mem_map.1 hxP
    have hic : ∀ j : ↥I, i * j = j * i := by
      intro j
      apply Subtype.ext
      have := hxI j.1 j.2
      simpa [← hix] using this
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
    have hi3 : i ^ 3 = 1 := Subtype.ext (by simpa [← hix] using hx3)
    have hi1 : i ≠ 1 := fun h1 => hxne (by rw [← hix, h1]; rfl)
    have hdvd : orderOf (⟨i, hcen⟩ : ↥(GLAPPrimeCore 3 ↥I)) ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
      orderOf_dvd_natCard _
    have hord : orderOf (⟨i, hcen⟩ : ↥(GLAPPrimeCore 3 ↥I)) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hi3 hi1
    rw [hord] at hdvd
    exact hN3 hdvd
  refine ⟨P' ⊔ Subgroup.zpowers x, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec8.Item82OneProof.isElemAbelian_sup_zpowers hP' hx3 hxP'
  · have hle : P' ≤ P' ⊔ Subgroup.zpowers x := le_sup_left
    have hxE : x ∈ P' ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    by_contra hcon
    push Not at hcon
    have heq : P' = P' ⊔ Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge hle (by omega)
    exact hxnot (heq ▸ hxE)

end CFSG.HardMathSupport.Dickson.Sec6
