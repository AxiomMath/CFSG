module

public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpLayer
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpArith

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Module
open CFSG.ClassicalInvolution.Models.SymplecticPairs (form form_antisymm form_zero_left
  form_single_inl_inr IsHyperbolicPlane isHyperbolicPlane_iff finrank_span_pair planeGroup
  stdPlane isHyperbolicPlane_stdPlane isAlt_toBilin'_J nondegenerate_toBilin'_J toBilin'_J_apply
  longInv planeGroup_stdPlane longInv_mem_longRootSp2)

section Pairs

variable {F : Type} [Field F] [Finite F] {n : ℕ}

abbrev SympPairs (U : Submodule F (Fin n ⊕ Fin n → F)) : Type :=
  {x : (Fin n ⊕ Fin n → F) × (Fin n ⊕ Fin n → F) // x.1 ∈ U ∧ x.2 ∈ U ∧ form x.1 x.2 = 1}

abbrev SympPlanes (U : Submodule F (Fin n ⊕ Fin n → F)) : Type :=
  {P : Submodule F (Fin n ⊕ Fin n → F) // IsHyperbolicPlane P ∧ P ≤ U}

instance finite_sympPlanes (U : Submodule F (Fin n ⊕ Fin n → F)) : Finite (SympPlanes U) :=
  Finite.of_injective (fun P : SympPlanes U => (P.1 : Set (Fin n ⊕ Fin n → F)))
    fun _ _ h => Subtype.ext (SetLike.coe_injective h)

theorem card_sympPairs {U : Submodule F (Fin n ⊕ Fin n → F)}
    (hU : ∀ v ∈ U, (∀ u ∈ U, form v u = 0) → v = 0) {d : ℕ} (hd : finrank F U = d) :
    Nat.card (SympPairs U) = (Nat.card F ^ d - 1) * Nat.card F ^ (d - 1) := by
  set B : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) := Matrix.toBilin' (Matrix.J (Fin n) F)
    with hB
  have hAlt : B.IsAlt := isAlt_toBilin'_J
  have hBform : ∀ u v, B u v = -form u v := fun u v => toBilin'_J_apply u v
  have hres : ∀ x y : U, (B.restrict U) x y = B x y := fun x y => rfl
  have hrefl : (B.restrict U).IsRefl := fun x y h => by
    rw [hres] at h ⊢
    exact hAlt.isRefl x y h
  have hnd : (B.restrict U).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun z hz => ?_
    refine Subtype.ext (hU z z.2 fun u hu => ?_)
    have := hz ⟨u, hu⟩
    rw [hres, hBform, neg_eq_zero] at this
    exact this
  have e : {x : U × U // (B.restrict U) x.2 x.1 = 1} ≃ SympPairs U :=
    { toFun := fun x => ⟨((x.1.1 : Fin n ⊕ Fin n → F), (x.1.2 : Fin n ⊕ Fin n → F)),
        x.1.1.2, x.1.2.2, by
          have h := x.2
          rw [hres, hBform, form_antisymm, neg_neg] at h
          exact h⟩
      invFun := fun x => ⟨(⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2.1⟩), by
          rw [hres, hBform, form_antisymm x.1.1 x.1.2, neg_neg]
          exact x.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e, card_hyperbolicPairs hnd, Module.natCard_eq_pow_finrank (K := F), hd]

@[expose] def sympSpan {U : Submodule F (Fin n ⊕ Fin n → F)} (x : SympPairs U) : SympPlanes U :=
  ⟨Submodule.span F {x.1.1, x.1.2}, ⟨x.1.1, x.1.2, x.2.2.2, rfl⟩,
    Submodule.span_le.mpr
      (Set.insert_subset_iff.mpr ⟨x.2.1, Set.singleton_subset_iff.mpr x.2.2.1⟩)⟩

@[expose] def sympFiber {U : Submodule F (Fin n ⊕ Fin n → F)} (P : SympPlanes U) :
    {x : SympPairs U // sympSpan x = P} ≃ SympPairs P.1 where
  toFun x := ⟨x.1.1, by
      have hsp : Submodule.span F {x.1.1.1, x.1.1.2} = P.1 := congrArg Subtype.val x.2
      exact ⟨by rw [← hsp]; exact Submodule.subset_span (by simp),
        by rw [← hsp]; exact Submodule.subset_span (by simp), x.1.2.2.2⟩⟩
  invFun w := ⟨⟨w.1, P.2.2 w.2.1, P.2.2 w.2.2.1, w.2.2.2⟩, Subtype.ext
    (show Submodule.span F {w.1.1, w.1.2} = P.1 from Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr
        (Set.insert_subset_iff.mpr ⟨w.2.1, Set.singleton_subset_iff.mpr w.2.2.1⟩))
      (by rw [finrank_span_pair w.2.2.2, (isHyperbolicPlane_iff.mp P.2.1).1]))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_sympPairs_eq_planes (U : Submodule F (Fin n ⊕ Fin n → F)) :
    Nat.card (SympPairs U) =
      Nat.card (SympPlanes U) * ((Nat.card F ^ 2 - 1) * Nat.card F ^ (2 - 1)) := by
  classical
  let _ : Fintype (SympPlanes U) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (sympSpan (U := U))), Nat.card_sigma]
  rw [Finset.sum_congr rfl fun P _ => by
      rw [Nat.card_congr (sympFiber P), card_sympPairs (isHyperbolicPlane_iff.mp P.2.1).2
        (isHyperbolicPlane_iff.mp P.2.1).1],
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]

theorem card_sympPlanes_mul {U : Submodule F (Fin n ⊕ Fin n → F)}
    (hU : ∀ v ∈ U, (∀ u ∈ U, form v u = 0) → v = 0) (h4 : finrank F U = 4) :
    Nat.card (SympPlanes U) * ((Nat.card F ^ 2 - 1) * Nat.card F) =
      (Nat.card F ^ 4 - 1) * Nat.card F ^ 3 := by
  have h := card_sympPairs_eq_planes U
  rw [card_sympPairs hU h4] at h
  simpa using h.symm

theorem card_sympPlanes {U : Submodule F (Fin n ⊕ Fin n → F)}
    (hU : ∀ v ∈ U, (∀ u ∈ U, form v u = 0) → v = 0) (h4 : finrank F U = 4)
    (hq : 2 ≤ Nat.card F) : Nat.card (SympPlanes U) = f4Core (Nat.card F) := by
  have h := card_sympPlanes_mul hU h4
  set q := Nat.card F with hqdef
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hne : (q ^ 2 - 1) * q ≠ 0 := by
    have : 1 < q ^ 2 := by nlinarith
    exact mul_ne_zero (by omega) (by omega)
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) ?_
  rw [h]
  unfold f4Core
  zify [hq1, hq2]
  ring

end Pairs

section Layer

variable {p f : ℕ} [Fact p.Prime]

@[expose] noncomputable def f4Compl (p f : ℕ) [Fact p.Prime] :
    Submodule (GaloisField p f) (Fin 3 ⊕ Fin 3 → GaloisField p f) :=
  (Matrix.toBilin' (Matrix.J (Fin 3) (GaloisField p f))).orthogonal
    (stdPlane (GaloisField p f) 3 (Fin.last 2))

theorem mem_f4Compl_iff {v : Fin 3 ⊕ Fin 3 → GaloisField p f} :
    v ∈ f4Compl p f ↔ ∀ u ∈ stdPlane (GaloisField p f) 3 (Fin.last 2), form u v = 0 := by
  unfold f4Compl
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun u _ => ?_
  rw [toBilin'_J_apply, neg_eq_zero]

private theorem f4_hfe :
    Matrix.toBilin' (Matrix.J (Fin 3) (GaloisField p f))
      (Pi.single (Sum.inr (Fin.last 2)) 1 : Fin 3 ⊕ Fin 3 → GaloisField p f)
      (Pi.single (Sum.inl (Fin.last 2)) 1 : Fin 3 ⊕ Fin 3 → GaloisField p f) = 1 := by
  rw [toBilin'_J_apply, form_antisymm, neg_neg]
  exact form_single_inl_inr _

theorem f4Compl_nondeg :
    ∀ v ∈ f4Compl p f, (∀ u ∈ f4Compl p f, form v u = 0) → v = 0 := by
  intro v hv hvu
  have hnd := isAlt_toBilin'_J.restrict_nondegenerate_orthogonal_span_pair
    (f4_hfe (p := p) (f := f)) nondegenerate_toBilin'_J
  have h0 := hnd.1 ⟨v, hv⟩ fun u => by
    have := hvu u u.2
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, toBilin'_J_apply, this,
      neg_zero]
  exact congrArg Subtype.val h0

theorem finrank_f4Compl : finrank (GaloisField p f) (f4Compl p f) = 4 := by
  have h := isAlt_toBilin'_J.finrank_orthogonal_span_pair_add_two nondegenerate_toBilin'_J
    (f4_hfe (p := p) (f := f))
  have hV : finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 → GaloisField p f) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have h' : finrank (GaloisField p f) (f4Compl p f) + 2 = 6 := hV ▸ h
  omega

theorem sympPlane_ne_stdPlane (P : SympPlanes (f4Compl p f)) :
    P.1 ≠ stdPlane (GaloisField p f) 3 (Fin.last 2) := by
  intro h
  obtain ⟨u, hu, v, hv, huv⟩ := exists_form_ne_zero_self
    (isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := 3) (Fin.last 2))
  have hv' : v ∈ f4Compl p f := P.2.2 (by rw [h]; exact hv)
  exact huv (mem_f4Compl_iff.mp hv' u hu)

theorem sympPlane_le_centralizer (hp2 : p ≠ 2) (P : SympPlanes (f4Compl p f)) :
    planeGroup P.1 ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _) := by
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hc : Commutes (planeGroup P.1) (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))) :=
    (commutes_planeGroup_iff h2 P.2.1 (isHyperbolicPlane_stdPlane _)
      (sympPlane_ne_stdPlane P)).mpr fun u hu v hv => by
        have := mem_f4Compl_iff.mp (P.2.2 hu) v hv
        rw [form_antisymm v u, this, neg_zero]
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hc x hx _ (by rw [planeGroup_stdPlane]; exact longInv_mem_longRootSp2 _)

@[expose] noncomputable def f4LayerOfPlane (hp2 : p ≠ 2) :
    Option (SympPlanes (f4Compl p f)) → {x : F4Layer p f // x ≠ none}
  | none => ⟨f4NodePoint hp2, f4NodePoint_ne_none hp2⟩
  | some P => ⟨some ⟨planeGroup P.1, ⟨P.1, P.2.1, rfl⟩, sympPlane_le_centralizer hp2 P⟩,
      Option.some_ne_none _⟩

theorem f4LayerOfPlane_bijective (hp2 : p ≠ 2) :
    Function.Bijective (f4LayerOfPlane (p := p) (f := f) hp2) := by
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hstd := isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := 3) (Fin.last 2)
  refine ⟨?_, ?_⟩
  · rintro (_ | P) (_ | P') h
    · rfl
    · exfalso
      have h1 : f4Node p f = planeGroup P'.1 := by
        simp only [f4LayerOfPlane, f4NodePoint, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact sympPlane_ne_stdPlane P' (planeGroup_injective h2 hstd P'.2.1 h1).symm
    · exfalso
      have h1 : planeGroup P.1 = f4Node p f := by
        simp only [f4LayerOfPlane, f4NodePoint, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact sympPlane_ne_stdPlane P (planeGroup_injective h2 P.2.1 hstd h1)
    · have h1 : planeGroup P.1 = planeGroup P'.1 := by
        simp only [f4LayerOfPlane, Subtype.mk.injEq, Option.some.injEq] at h
        exact h
      exact congrArg some (Subtype.ext (planeGroup_injective h2 P.2.1 P'.2.1 h1))
  · rintro ⟨_ | ⟨R, ⟨P, hP, rfl⟩, hRc⟩, hx⟩
    · exact absurd rfl hx
    · by_cases hRn : planeGroup P = f4Node p f
      · exact ⟨none, Subtype.ext (congrArg some (Subtype.ext hRn.symm))⟩
      · have hne : P ≠ stdPlane (GaloisField p f) 3 (Fin.last 2) := fun e => hRn (by rw [e]; rfl)
        have hcomm := commutes_planeGroup_stdPlane_of_le_centralizer h2 (Fin.last 2) hP hRc hRn
        have horth := (commutes_planeGroup_iff h2 hP hstd hne).mp hcomm
        refine ⟨some ⟨P, hP, fun u hu => mem_f4Compl_iff.mpr fun v hv => ?_⟩, Subtype.ext rfl⟩
        rw [form_antisymm u v, horth u hu v hv, neg_zero]

theorem card_f4Layer (hp2 : p ≠ 2) :
    Nat.card (F4Layer p f) = Nat.card (SympPlanes (f4Compl p f)) + 2 := by
  rw [← card_ne_none_add_one, ← Nat.card_eq_of_bijective _ (f4LayerOfPlane_bijective hp2)]
  have := Fintype.ofFinite (SympPlanes (f4Compl p f))
  simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem card_f4Layer_eq (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 2 ≤ p ^ f) :
    Nat.card (F4Layer p f) = f4Core (p ^ f) + 2 := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  rw [card_f4Layer hp2, card_sympPlanes f4Compl_nondeg finrank_f4Compl (by rw [hcard]; exact hq),
    hcard]

end Layer

end CFSG.ClassicalInvolution.RouteD.NonClassical
