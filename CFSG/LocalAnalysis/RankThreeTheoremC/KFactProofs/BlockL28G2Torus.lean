module

public import CFSG.LieType.Steinberg.Adjoint.Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def gtwoNode0 : Fin (Tag.rank .G2) := ⟨0, by decide⟩

@[expose] def gtwoNode1 : Fin (Tag.rank .G2) := ⟨1, by decide⟩

@[expose] noncomputable def gtwoTorusHom
    (F : Type) [Field F] : (Fin 2 → Fˣ) →* adjointGroup .G2 F where
  toFun a := torusHom F gtwoNode0 (a 0) * torusHom F gtwoNode1 (a 1)
  map_one' := by simp
  map_mul' a b := by
    have hc : Commute (torusHom F gtwoNode1 (a 1)) (torusHom F gtwoNode0 (b 0)) :=
      Subtype.ext (torusElt_mul_comm gtwoNode1 gtwoNode0 (a 1) (b 0))
    simp only [Pi.mul_apply, map_mul]
    set x0 := torusHom F gtwoNode0 (a 0)
    set x1 := torusHom F gtwoNode1 (a 1)
    set y0 := torusHom F gtwoNode0 (b 0)
    set y1 := torusHom F gtwoNode1 (b 1)
    calc x0 * y0 * (x1 * y1) = x0 * (y0 * x1) * y1 := by simp only [mul_assoc]
      _ = x0 * (x1 * y0) * y1 := by rw [hc.eq]
      _ = x0 * x1 * (y0 * y1) := by simp only [mul_assoc]

theorem gtwoTorusHom_apply
    {F : Type} [Field F] (a : Fin 2 → Fˣ) :
    gtwoTorusHom F a = torusHom F gtwoNode0 (a 0) * torusHom F gtwoNode1 (a 1) :=
  rfl

theorem gtwo_sq_eq_one_of_torusHom_eq_one
    {F : Type} [Field F] (i : Fin (Tag.rank .G2)) {t : Fˣ}
    (ht : torusHom F i t = 1) : t ^ 2 = 1 := by
  have h1 := torusElt_single (R := F) i t (Sum.inr ⟨Pi.single i 1, isRoot_single .G2 i⟩)
  have hsum : ∑ j, Tag.cartan .G2 i j *
      labelWt .G2 (Sum.inr ⟨Pi.single i 1, isRoot_single .G2 i⟩ : Label .G2) j = 2 := by
    simp only [labelWt, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    fin_cases i <;> rfl
  rw [hsum] at h1
  have h2 : (torusElt .G2 F i t : Module.End F (RootModule .G2 F)) = 1 :=
    congrArg (fun g : adjointGroup .G2 F => ((g : ModGL .G2 F) : Module.End F (RootModule .G2 F)))
      ht
  rw [h2, Module.End.one_apply] at h1
  have h4 := congrArg (fun x : RootModule .G2 F =>
    x (Sum.inr ⟨Pi.single i 1, isRoot_single .G2 i⟩)) h1
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h4
  exact Units.ext (by simpa using h4.symm)

theorem gtwo_eq_one_of_torusHom_eq_one
    {F : Type} [Field F] (hF : Nat.card Fˣ = 7)
    (i : Fin (Tag.rank .G2)) {t : Fˣ} (ht : torusHom F i t = 1) : t = 1 := by
  have h2 := gtwo_sq_eq_one_of_torusHom_eq_one i ht
  have h7 : t ^ 7 = 1 := by rw [← hF]; exact pow_card_eq_one'
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 7)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h7))

theorem gtwo_exists_cartan_inverse :
    ∃ B : Matrix (Fin (Tag.rank .G2)) (Fin (Tag.rank .G2)) ℤ, Tag.cartan .G2 * B = 1 :=
  ⟨!![2, 1; 3, 2], by decide⟩

theorem gtwoTorusHom_injective
    {F : Type} [Field F] (hF : Nat.card Fˣ = 7) :
    Function.Injective (gtwoTorusHom F) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨B, hB⟩ := gtwo_exists_cartan_inverse
  have hdis : Disjoint (torus F gtwoNode0) (torus F gtwoNode1) :=
    (torus_iSupIndep (K := F) hB).pairwiseDisjoint (by decide : gtwoNode0 ≠ gtwoNode1)
  rw [gtwoTorusHom_apply] at ha
  have h0 : torusHom F gtwoNode0 (a 0) = 1 := by
    refine Subgroup.disjoint_def.1 hdis ⟨a 0, rfl⟩ ?_
    have h : torusHom F gtwoNode0 (a 0) = torusHom F gtwoNode1 (a 1)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left ha
    rw [h]
    exact ⟨(a 1)⁻¹, rfl⟩
  have h1 : torusHom F gtwoNode1 (a 1) = 1 := by
    rw [h0, one_mul] at ha
    exact ha
  funext i
  fin_cases i
  · exact gtwo_eq_one_of_torusHom_eq_one hF _ h0
  · exact gtwo_eq_one_of_torusHom_eq_one hF _ h1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
