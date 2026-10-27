module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedInnerAction
import CFSG.Quasithin.H13.GoldschmidtC137S6Aut
import CFSG.GroupTheory.ConjTransport
import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.H13.U3.GC137

private lemma hat_lt_hat_iff {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) {R R' : Subgroup Γ} (hR : R ≤ A) (hR' : R' ≤ A) :
    (R.subgroupOf A).map e.toMonoidHom < (R'.subgroupOf A).map e.toMonoidHom ↔ R < R' := by
  rw [Subgroup.map_lt_map_iff_of_injective e.injective]
  exact (Subgroup.map_subtype_lt_map_subtype (G' := A)).symm.trans (by
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hR, inf_of_le_left hR'])

private lemma hat_top {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) :
    (A.subgroupOf A).map e.toMonoidHom = ⊤ := by
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ e.surjective]

private noncomputable def hatAlpha {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) {a : Γ} (ha : a ∈ normalizer (A : Set Γ)) :
    MulAut (Equiv.Perm (Fin 6)) :=
  e.symm.trans ((A.normalizerMonoidHom ⟨a, ha⟩).trans e)

private lemma hatAlpha_apply {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) {a : Γ} (ha : a ∈ normalizer (A : Set Γ))
    (x : Equiv.Perm (Fin 6)) :
    hatAlpha e ha x = e (A.normalizerMonoidHom ⟨a, ha⟩ (e.symm x)) :=
  rfl

private lemma map_hat_hatAlpha {Γ : Type*} [Group Γ] {A R : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) {a : Γ} (ha : a ∈ normalizer (A : Set Γ))
    (haR : a ∈ normalizer (R : Set Γ)) :
    ((R.subgroupOf A).map e.toMonoidHom).map (hatAlpha e ha).toMonoidHom =
      (R.subgroupOf A).map e.toMonoidHom := by
  have hmem : ∀ y : ↥A, y ∈ R.subgroupOf A →
      A.normalizerMonoidHom ⟨a, ha⟩ y ∈ R.subgroupOf A := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp haR (y : Γ)).mp hy
  have hle : ((R.subgroupOf A).map e.toMonoidHom).map (hatAlpha e ha).toMonoidHom ≤
      (R.subgroupOf A).map e.toMonoidHom := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_map_equiv] at hy
    rw [Subgroup.mem_map]
    refine ⟨A.normalizerMonoidHom ⟨a, ha⟩ (e.symm y), hmem (e.symm y) hy, ?_⟩
    exact (hatAlpha_apply e ha y).symm
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Subgroup.card_map_of_injective
    (hatAlpha e ha).injective).symm)

private lemma exists_conj_hat_T6 {Γ : Type*} [Group Γ] [Finite Γ] {A T : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) (hT : IsSylowOf 2 T A) :
    ∃ π : Equiv.Perm (Fin 6),
      (T.subgroupOf A).map (e.trans (MulAut.conj π)).toMonoidHom = T6 := by
  have hT6 : IsPGroup 2 T6 := IsPGroup.of_card (n := 4) (by
    rw [CFSG.Quasithin.H13.U3.GC137.card_T6]; norm_num)
  have hidxT6 : T6.index = 45 := by
    have h1 := Subgroup.index_mul_card (H := T6)
    rw [CFSG.Quasithin.H13.U3.GC137.card_T6, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    norm_num at h1
    omega
  have hiT6 : ¬ 2 ∣ T6.index := by rw [hidxT6]; norm_num
  have hThat : IsPGroup 2 ((T.subgroupOf A).map e.toMonoidHom) :=
    (hT.isPGroup.comap_subtype (K := A)).map e.toMonoidHom
  have hiThat : ¬ 2 ∣ ((T.subgroupOf A).map e.toMonoidHom).index := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv (H := T.subgroupOf A) e]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hT).2.2
  obtain ⟨π, hπ⟩ := CFSG.GroupTheory.exists_conj_of_isPGroup 2 hT6 hThat hiT6 hiThat
  refine ⟨π, ?_⟩
  have he' : (e.trans (MulAut.conj π)).toMonoidHom =
      (MulAut.conj π).toMonoidHom.comp e.toMonoidHom :=
    MulEquiv.toMonoidHom_trans e (MulAut.conj π)
  rw [he', ← Subgroup.map_map]
  exact hπ

private lemma exists_inner_of_normalizes {Γ : Type*} [Group Γ]
    {A V T Q : Subgroup Γ} (e : ↥A ≃* Equiv.Perm (Fin 6))
    (hVA : V ≤ normalizer (A : Set Γ)) (hVT : V ≤ normalizer (T : Set Γ))
    (hVQ : V ≤ normalizer (Q : Set Γ))
    (hT_hat : (T.subgroupOf A).map e.toMonoidHom = T6)
    (hTQ : T6 < (Q.subgroupOf A).map e.toMonoidHom)
    (hQtop : (Q.subgroupOf A).map e.toMonoidHom < ⊤) :
    ∀ a ∈ V, ∃ w ∈ A, ∀ x ∈ A, a * x * a⁻¹ = w * x * w⁻¹ := by
  intro a ha
  have haN : a ∈ normalizer (A : Set Γ) := hVA ha
  have hαT : T6.map (hatAlpha e haN).toMonoidHom = T6 := by
    have h := map_hat_hatAlpha e haN (hVT ha)
    rwa [hT_hat] at h
  have hαQ : ((Q.subgroupOf A).map e.toMonoidHom).map (hatAlpha e haN).toMonoidHom =
      (Q.subgroupOf A).map e.toMonoidHom :=
    map_hat_hatAlpha e haN (hVQ ha)
  obtain ⟨π, hπ⟩ := CFSG.Quasithin.H13.U3.GC137.exists_conj_of_map_T6_eq
    (hatAlpha e haN) hαT hTQ hQtop hαQ
  refine ⟨(e.symm π : ↥A), (e.symm π).2, fun x hx => ?_⟩
  have h1 : A.normalizerMonoidHom ⟨a, haN⟩ ⟨x, hx⟩ =
      e.symm π * ⟨x, hx⟩ * (e.symm π)⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hπ (e ⟨x, hx⟩)]
    rw [hatAlpha_apply, MulEquiv.symm_apply_apply]
  have h2 := congrArg (fun z : ↥A => (z : Γ)) h1
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  simpa using h2

private lemma hat_inf_centralizer_eq_bot {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) :
    A ⊓ centralizer (A : Set Γ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : (⟨z, hz.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    ext
    exact Subgroup.mem_centralizer_iff.mp hz.2 g.1 g.2
  have hmap : e ⟨z, hz.1⟩ ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hzc
  rw [CFSG.ClassicalInvolution.Sp62Rec.I1.center_perm_fin_six_eq_bot, Subgroup.mem_bot] at hmap
  have h1 : (⟨z, hz.1⟩ : ↥A) = 1 := e.injective (by rw [hmap, map_one])
  exact Subtype.ext_iff.mp h1

private lemma isPIsolatedOver_top_of_mulEquiv {Γ : Type*} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 6)) (h : IsPIsolatedOver 2 A ⊥) :
    IsPIsolatedOver 2 (⊤ : Subgroup (Equiv.Perm (Fin 6))) ⊥ := by
  have h1 : IsPIsolatedOver 2 (⊤ : Subgroup ↥A) ⊥ := by
    have := (isPIsolatedOver_subgroupOf_iff (p := 2) (H := ⊥) (K := A) (K' := A)
      bot_le le_rfl).2 h
    simpa using this
  have hker : e.toMonoidHom.ker = ⊥ := MonoidHom.ker_eq_bot e.toMonoidHom e.injective
  have hk : IsPGroup 2 e.toMonoidHom.ker := by rw [hker]; exact IsPGroup.of_bot
  have h2 := (isPIsolatedOver_map_iff (p := 2) (f := e.toMonoidHom) e.surjective hk
    (le_of_eq hker) le_top).2 h1
  rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, Subgroup.map_bot] at h2

theorem not_isPIsolatedOver_perm_six :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup (Equiv.Perm (Fin 6))) ⊥ := by
  intro h
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hev : Even (Nat.card (alternatingGroup (Fin 6))) := by
    rw [hcard]
    exact ⟨180, by norm_num⟩
  have ht : orderOf (Equiv.swap (0 : Fin 6) 1) = 2 :=
    Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
  have hmem : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) :=
    h.mem_of_isSubnormal
      (Subgroup.Normal.isSubnormal (inferInstance : (alternatingGroup (Fin 6)).Normal)) hev ht
  rw [Equiv.Perm.mem_alternatingGroup] at hmem
  rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1)] at hmem
  exact (by decide : (-1 : ℤˣ) ≠ 1) hmem

theorem exists_not_mem_normalizer_of_mulEquiv_perm_six {Γ : Type*} [Group Γ] [Finite Γ]
    {A V T Q : Subgroup Γ} (e : ↥A ≃* Equiv.Perm (Fin 6)) (hV : IsPGroup 2 V)
    (hVA : V ≤ normalizer (A : Set Γ)) (hT : IsSylowOf 2 T A)
    (hVT : V ≤ normalizer (T : Set Γ)) (hiso : IsPIsolatedOver 2 (A ⊓ centralizer (V : Set Γ)) ⊥)
    (hTQ : A ⊓ normalizer (T : Set Γ) < Q) (hQA : Q < A) :
    ∃ a ∈ V, a ∉ normalizer (Q : Set Γ) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨π, hT_hat⟩ := exists_conj_hat_T6 e hT
  let e' : ↥A ≃* Equiv.Perm (Fin 6) := e.trans (MulAut.conj π)
  have hTQ' : T < Q := lt_of_le_of_lt (le_inf hT.le Subgroup.le_normalizer) hTQ
  have hT6_lt_Qhat : T6 < (Q.subgroupOf A).map e'.toMonoidHom := by
    rw [← hT_hat]
    exact (hat_lt_hat_iff e' hT.le hQA.le).mpr hTQ'
  have hQhat_lt_top : (Q.subgroupOf A).map e'.toMonoidHom < ⊤ := by
    have h := (hat_lt_hat_iff e' hQA.le le_rfl).mpr hQA
    rwa [hat_top e'] at h
  have hinner := exists_inner_of_normalizes e' hVA hVT hcon hT_hat hT6_lt_Qhat hQhat_lt_top
  have hZ : A ⊓ centralizer (A : Set Γ) = ⊥ := hat_inf_centralizer_eq_bot e'
  have hcent : V ≤ centralizer (A : Set Γ) :=
    IsPIsolatedOver.le_centralizer_of_inner hZ hV hinner hiso
  have hA_le : A ≤ centralizer (V : Set Γ) := Subgroup.le_centralizer_iff.mp hcent
  have hisoA : IsPIsolatedOver 2 A ⊥ := by
    rwa [inf_eq_left.mpr hA_le] at hiso
  exact not_isPIsolatedOver_perm_six (isPIsolatedOver_top_of_mulEquiv e' hisoA)

end CFSG.GroupTheory
