module

public import CFSG.LargeExtraspecial.S11MbKeyD
public import CFSG.LargeExtraspecial.S11MbKeyC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G} {kb σ u₁ : G}

variable (hy : Hyp S g) (K : Conf S g t τ u) (hm : finrank (ZMod 2) (Vt S g t) = 2)
  (Y : YData S g t τ u kb σ u₁)
  (hcase : ∀ w ∈ Wt S g t, (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
    (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
  (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u)
  (hbs : S.cl (kb * S.z * kb⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
  (hCE : CentralExtInput.{u_G}) (hn : 7 ≤ S.width)
include hy K hm hcase hb hbs hCE hn

theorem YData.false_of_case : False := by
  set s := S.ρ ⟨σ, Y.mem_M⟩ with hs
  set c := S.cl (g * S.z * g⁻¹) with hc
  have hdC := Y.finrank_clSub_centralizer hy K hm hcase
  obtain ⟨hFU, hF2⟩ := Y.clSub_le_commSpace hy K hm hcase hb hCE
  have hQt := S.finrank_Qt_eq_two_mul_width
  have hdP := S.finrank_clSub_QG_inf_Qa hy.hyp4.conj_mem hy.hyp4.conj_ne hy.cons.card_QG_inf_Qa
  have hc0 : c ≠ 0 := cl_conj_z_ne_zero S hy.hyp4.conj_mem hy.hyp4.conj_ne
  have hdH := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate ((ZMod 2) ∙ c)
  rw [finrank_span_singleton hc0] at hdH
  have hdF := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate
    (S.clSub (S.QG ⊓ S.Qa u₁))
  rw [hF2] at hdF
  have hdt := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
  rw [K.timmesfeld_11_7 hy hCE, hm] at hdt
  have hdt' := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hcA := Y.two_pow_le_card hy K hm hcase
  set C := S.clSub (S.QG ⊓ centralizer ({σ} : Set G)) with hC
  set F := S.clSub (S.QG ⊓ S.Qa u₁) with hF
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set H := LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ c) with hH
  set Ft := fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hFt
  have hmemH : ∀ x, x ∈ H ↔ polar S.q c x = 0 := fun x => mem_orthogonal_span_singleton_iff
  have hcF : c ∈ F := S.cl_mem_clSub (mem_inf.mpr ⟨hy.hyp4.conj_mem, Y.a_mem⟩)
    hy.hyp4.conj_mem
  have hCF : C ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin F := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun f hf => by
      change S.q.polarBilin f x = 0
      rw [polarBilin_apply_apply]
      exact Y.polar_eq_zero hf hx
  have hFtF : Ft ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin F := by
    rw [hFt, fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate t.2]
    exact LinearMap.BilinForm.orthogonal_le hFU
  have hS1 := Submodule.finrank_sup_add_finrank_inf_eq C Ft
  have hS2 := Submodule.finrank_mono (sup_le hCF hFtF)
  have hCfix : C ≤ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have := S.clSub_centralizer_le_fixQt Y.mem_M
    rwa [S.fixQt_of_mem Y.mem_M] at this
  have hsL := Y.rho_mem_Lbar hy
  have hd7 := finrank_inf_fixSpace_inf_le hy.hyp4 hy.cons hsL K.mem_Lbar Y.rho_ne_one K.ne_one
    (Y.rho_ne K)
  rw [← hs, ← hP, ← hFt] at hd7
  have hle7 : (C ⊓ Ft) ⊓ P ≤ (P ⊓ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓ (P ⊓ Ft) :=
    fun x hx => ⟨⟨hx.2, hCfix hx.1.1⟩, ⟨hx.2, hx.1.2⟩⟩
  have hT1 := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ Ft) P
  have hT2 := Submodule.finrank_mono hle7
  have hTH : (C ⊓ Ft) ⊔ P ≤ H := by
    refine sup_le (fun x hx => (hmemH x).mpr (Y.polar_eq_zero hcF hx.1)) fun x hx =>
      (hmemH x).mpr (polar_eq_zero_of_mem_clSub hy.hyp4.conj_ne (cl_mem_clSub_self
        hy.hyp4.conj_mem) hx)
  set X := S.Qa u₁ ⊓ S.Qa g ⊓ S.M with hX
  set A := ((X.subgroupOf S.M).map S.ρ ⊓ (S.Lbar g ⊓ Nbar S g t) : Subgroup S.O) with hA
  have hcq : S.q c = 0 := (S.q_cl_eq_zero_iff hy.hyp4.conj_mem).mpr (by
    rw [pow_two]; exact conj_z_mul_self S g)
  have hn6 : 6 ≤ S.width := by omega
  have hAO : A.map S.O.subtype ≤ orthogonalGroup S.q := by
    rintro _ ⟨l, -, rfl⟩
    exact l.2
  have hAinv : ∀ l ∈ A.map S.O.subtype, l * l = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg Subtype.val (mul_self_of_mem_Lbar S hy.hyp4.conj_mem hl.2.1)
  have hAc : ∀ l ∈ A.map S.O.subtype, l c = c := by
    rintro _ ⟨l, hl, rfl⟩
    exact Lbar_apply_cl hy.hyp4 hl.2.1
  have hAP : ∀ l ∈ A.map S.O.subtype, ∀ x, polar S.q c x = 0 → l x - x ∈ P := by
    rintro _ ⟨l, hl, rfl⟩ x hx
    exact Lbar_sub_mem_clSub hy.hyp4 hy.cons hl.2.1 hx
  have hAT : ∀ l ∈ A.map S.O.subtype, ∀ x ∈ (C ⊓ Ft) ⊔ P, l x - x ∈ (ZMod 2) ∙ c := by
    rintro _ ⟨l, hl, rfl⟩ x hx
    obtain ⟨y, hy', p, hp, rfl⟩ := Submodule.mem_sup.mp hx
    have e : (S.O.subtype l) (y + p) - (y + p) =
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) := by
      change (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (y + p) - (y + p) = _
      rw [map_add]
      abel
    rw [e]
    refine add_mem ?_ (Lbar_apply_sub_mem_span' hy.hyp4.conj_mem hp hl.2.1)
    obtain ⟨x₀, hx₀, hx₀l⟩ := Subgroup.mem_map.mp hl.1
    have hx₀X : (x₀ : G) ∈ X := mem_subgroupOf.mp hx₀
    have hF' : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ F := by
      rw [← hx₀l]
      exact Y.apply_sub_mem_clSub (mem_inf.mp (mem_inf.mp hx₀X).1).1 x₀.2 hy'.1
    have hV' : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t :=
      K.apply_sub_mem_Vt_of_mem_fixSpace hy hCE hn6 hl.2.2 hy'.2
    exact Y.inf_Vt_le hy K hm hcase hb hbs ⟨hF', hV'⟩
  have hA2 : ∀ l ∈ A.map S.O.subtype, l ≠ 1 → ¬ IsTypeA S.q l 2 := by
    rintro _ ⟨l, hl, rfl⟩ hl1
    exact hy.not_isTypeA_of_mem_Lbar hl.2.1 fun h => hl1 (by rw [h]; rfl)
  have h8 := card_le_eight S.q_nondegenerate hc0 hcq (P := P) (T := (C ⊓ Ft) ⊔ P)
    (fun x hx => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hy.hyp4.conj_ne hx) le_sup_right hTH
    (by rw [← hH]; omega) hAO hAinv hAc hAP hAT hA2
  rw [Subgroup.card_map_of_injective S.O.subtype_injective] at h8
  have h9 : 128 ≤ 2 ^ S.width := by
    calc 128 = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hn
  omega

end CFSG.LargeExtraspecial.S11
