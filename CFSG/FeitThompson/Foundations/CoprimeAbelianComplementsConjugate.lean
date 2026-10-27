module

public import CFSG.FeitThompson.Foundations.AveragingCrossedHomomorphism
public import CFSG.FeitThompson.Foundations.ComplementsDifferByCrossedHom

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open IsMulCommutative Pointwise

variable {G : Type*} [Group G] {A H K : Subgroup G} [A.Normal]

theorem isComplement'_of_sup_eq_top_of_inf_eq_bot (hsup : A ⊔ H = ⊤) (hinf : A ⊓ H = ⊥) :
    H.IsComplement' A := by
  refine (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) ?_).symm
  rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]

variable [IsMulCommutative ↥A]

theorem exists_mem_conj_smul_eq_of_isComplement' [Finite G]
    (hcop : (Nat.card ↥A).Coprime A.index) (hH : H.IsComplement' A) (hK : K.IsComplement' A) :
    ∃ a ∈ A, MulAut.conj a • H = K := by
  have hcop' : (Nat.card (G ⧸ A)).Coprime (Nat.card (Additive ↥A)) := by
    rw [← Subgroup.index_eq_card]; exact hcop.symm
  obtain ⟨v, hv⟩ := exists_forall_crossedHom_eq_sub_smul hcop'
    (fun x => Additive.ofMul (complementDiff hH hK x)) (ofMul_complementDiff_mul hH hK)
  set w : ↥A := v.toMul with hw
  have key : ∀ x : G ⧸ A, (w : G) * (hH.QuotientMulEquiv x : G) * (w : G)⁻¹
      = (complementDiff hH hK x : G) * (hH.QuotientMulEquiv x : G) := by
    intro x
    have h1 : complementDiff hH hK x = w / (x • w) := by
      have h := congrArg Additive.toMul (hv x)
      simpa [toMul_sub, hw] using h
    rw [h1, Subgroup.coe_div, coe_smul_quotientMulEquiv hH, div_eq_mul_inv, mul_inv_rev,
      mul_inv_rev]
    group
  refine ⟨w, w.2, ?_⟩
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hg
    have hs := quotientMulEquiv_mk_coe hH ⟨_, hg⟩
    have hgeq : g
        = (w : G) * (hH.QuotientMulEquiv ((((w : G)⁻¹ * g * w : G)) : G ⧸ A) : G) * (w : G)⁻¹ := by
      rw [hs]; group
    rw [hgeq, key]
    exact complementDiff_mul_section_mem hH hK _
  · intro hg
    rw [← SetLike.mem_coe, coe_eq_range_complementDiff hH hK] at hg
    obtain ⟨x, hx⟩ := hg
    dsimp only at hx
    rw [← hx, ← key]
    have h2 : (w : G)⁻¹ * ((w : G) * (hH.QuotientMulEquiv x : G) * (w : G)⁻¹) * (w : G)
        = (hH.QuotientMulEquiv x : G) := by group
    rw [h2]
    exact (hH.QuotientMulEquiv x).2

theorem exists_mem_conj_smul_eq [Finite G] (hcop : (Nat.card ↥A).Coprime (Nat.card (G ⧸ A)))
    (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥) (hKsup : A ⊔ K = ⊤) (hKinf : A ⊓ K = ⊥) :
    ∃ a ∈ A, MulAut.conj a • H = K :=
  exists_mem_conj_smul_eq_of_isComplement' (by rwa [Subgroup.index_eq_card])
    (isComplement'_of_sup_eq_top_of_inf_eq_bot hHsup hHinf)
    (isComplement'_of_sup_eq_top_of_inf_eq_bot hKsup hKinf)

theorem exists_mem_forall_mem_iff_conj_mem [Finite G]
    (hcop : (Nat.card ↥A).Coprime (Nat.card (G ⧸ A)))
    (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥) (hKsup : A ⊔ K = ⊤) (hKinf : A ⊓ K = ⊥) :
    ∃ a ∈ A, ∀ g : G, g ∈ K ↔ a⁻¹ * g * a ∈ H := by
  obtain ⟨a, ha, hconj⟩ := exists_mem_conj_smul_eq hcop hHsup hHinf hKsup hKinf
  refine ⟨a, ha, fun g => ?_⟩
  rw [← hconj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]

theorem exists_mem_map_conj_eq [Finite G] (hcop : (Nat.card ↥A).Coprime (Nat.card (G ⧸ A)))
    (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥) (hKsup : A ⊔ K = ⊤) (hKinf : A ⊓ K = ⊥) :
    ∃ a ∈ A, H.map (MulAut.conj a).toMonoidHom = K := by
  obtain ⟨a, ha, hconj⟩ := exists_mem_conj_smul_eq hcop hHsup hHinf hKsup hKinf
  refine ⟨a, ha, ?_⟩
  rw [← hconj]
  ext g
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨by rintro ⟨h, hh, rfl⟩; simpa [mul_assoc] using hh,
    fun hg => ⟨a⁻¹ * g * a, hg, by group⟩⟩

theorem exists_mulEquiv_of_isComplement' [Finite G] (hcop : (Nat.card ↥A).Coprime A.index)
    (hH : H.IsComplement' A) (hK : K.IsComplement' A) : Nonempty (↥H ≃* ↥K) := by
  obtain ⟨a, _, hconj⟩ := exists_mem_conj_smul_eq_of_isComplement' hcop hH hK
  exact ⟨(Subgroup.equivSMul (MulAut.conj a) H).trans (MulEquiv.subgroupCongr hconj)⟩

end CFSG.FeitThompson
