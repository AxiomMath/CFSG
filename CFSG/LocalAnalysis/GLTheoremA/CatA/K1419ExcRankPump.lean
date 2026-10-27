module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem L3U3Pumpup.exists_elemAbelian_gt_nine {S : Type} [Group S] [Finite S] (hF : L3U3Facts)
    (hctr : ∀ (X : Type) [Group X] [Finite X], L3U3 X → Subgroup.center X = ⊥)
    (hZ : Subgroup.center S = ⊥) {x : S} (h : L3U3Pumpup S (MulAut.conj x)) :
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
  obtain ⟨Eb, hEb, hEb9⟩ := hF.elem9 _ hI34
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥I)
  obtain ⟨P, -, hP, hPcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift (p := 3)
    (GLAPPrimeCore 3 ↥I) hN3 hEb
  rw [hEb9] at hPcard
  have hinj : Function.Injective I.subtype := Subtype.val_injective
  set P' : Subgroup S := P.map I.subtype with hP'def
  have hP' : CFSG.Assembly.IsElemAbelian 3 P' := CFSG.Open.IsElemAbelian.map hP _
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
    rw [hctr _ hI34, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
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

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
