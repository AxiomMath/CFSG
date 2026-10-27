module

public import CFSG.LargeExtraspecial.DW3Main

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
open Matrix
open scoped MatrixGroups

@[expose] def HeldTypeRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), orderOf z = 2 →
    Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (centralizer ({z} : Set G)) ∧ g⁻¹ * z * g ≠ z) →
      Nonempty (G ≃* PSL(5, ZMod 2)) ∨ IsSporadic G .M24 ∨ IsSporadic G .He

theorem pCoreOf_two_eq_QG {G : Type*} [Group G] (S : Setting G) :
    pCoreOf 2 (centralizer ({S.z} : Set G)) = S.QG := by
  have h : CFSG.Open.pCore 2 S.M = CFSG.pCore 2 S.M := rfl
  rw [pCoreOf, ← S.Q_eq_pCore]
  try rfl

variable {G : Type} [Group G] [Finite G]

theorem nonempty_centralizer_mulEquiv_sl5 (S : Setting G) (hw : S.width = 3) {V₁ V₂ : Subgroup G}
    (hV₁Q : V₁ ≤ S.QG) (hV₂Q : V₂ ≤ S.QG) (hV₁ : IsElemAbelian 2 V₁) (hV₂ : IsElemAbelian 2 V₂)
    (hV12 : V₁ ⊓ V₂ = zpowers S.z) (hV12' : V₁ ⊔ V₂ = S.QG)
    (hMV₁ : S.M ≤ normalizer (V₁ : Set G)) (hMV₂ : S.M ≤ normalizer (V₂ : Set G))
    (hidx : Nat.card S.M = 168 * Nat.card S.Q) {E : Subgroup G} (hEM : E ≤ S.M)
    (hE : IsElemAbelian 2 E) (hEcard : Nat.card E = 64)
    (hEQ : Nat.card (S.QG ⊓ E : Subgroup G) = 16) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) := by
  have hzV₂ : S.z ∈ V₂ := (show S.z ∈ V₁ ⊓ V₂ by rw [hV12]; exact mem_zpowers _).2
  have hinv : ∀ {V : Subgroup G}, S.M ≤ normalizer (V : Set G) → ∀ m : S.M, ∀ w ∈ S.clSub V,
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub V := by
    intro V hMV m w hw'
    obtain ⟨x, hxV, hxQ, rfl⟩ := S.mem_clSub_iff.mp hw'
    rw [S.ρ_cl m hxQ]
    exact S.cl_mem_clSub ((mem_normalizer_iff.mp (hMV m.2) x).mp hxV) (S.conj_mem_QG m.2 hxQ)
  have hts : ∀ {V : Subgroup G}, IsElemAbelian 2 V → ∀ w ∈ S.clSub V, S.q w = 0 := by
    intro V hV w hw'
    obtain ⟨x, hxV, hxQ, rfl⟩ := S.mem_clSub_iff.mp hw'
    exact (S.q_cl_eq_zero_iff hxQ).mpr (hV.2 x hxV)
  have hcompl : IsCompl (S.clSub V₁) (S.clSub V₂) := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro v hv1 hv2
      obtain ⟨x, hxV, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv1
      obtain ⟨y, hyV, hyQ, hyx⟩ := S.mem_clSub_iff.mp hv2
      have hxV₂ : x ∈ V₂ := by
        rcases (S.cl_eq_cl_iff hyQ hxQ).mp hyx with rfl | rfl
        · exact hyV
        · exact V₂.mul_mem hyV hzV₂
      have hx : x ∈ zpowers S.z := hV12 ▸ ⟨hxV, hxV₂⟩
      rcases (Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp hx with rfl | rfl
      · exact S.cl_one
      · exact S.cl_z
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      obtain ⟨q, hq, rfl⟩ := S.exists_cl v
      have hle : V₁ ≤ normalizer (V₂ : Set G) := fun x hx => hMV₂ (S.QG_le_M (hV₁Q hx))
      rw [← hV12', ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hle]
        at hq
      obtain ⟨a, ha, b, hb, rfl⟩ := hq
      rw [S.cl_mul (hV₁Q ha) (hV₂Q hb)]
      exact Submodule.add_mem_sup (S.cl_mem_clSub ha (hV₁Q ha)) (S.cl_mem_clSub hb (hV₂Q hb))
  have H : DW.W3.Hyp S (S.clSub V₁) (S.clSub V₂) :=
    ⟨hcompl, hinv hMV₁, hinv hMV₂, hts hV₁, hts hV₂, hw⟩
  have hker : H.res.ker = S.Q := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      obtain ⟨hm, hmQ⟩ := S.mem_QG_iff.mp (H.mem_QG_of_res_eq_one h)
      exact hmQ
    · intro h
      exact H.res_eq_one_of_mem_QG ⟨m, h, rfl⟩
  have hrange : Nat.card H.res.range = 168 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H.res.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange H.res).toEquiv, hker, hidx] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have : Finite (S.clSub V₁ ≃ₗ[ZMod 2] S.clSub V₁) :=
    Finite.of_injective (fun f : S.clSub V₁ ≃ₗ[ZMod 2] S.clSub V₁ => (f : S.clSub V₁ → S.clSub V₁))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have hGL : Nat.card (S.clSub V₁ ≃ₗ[ZMod 2] S.clSub V₁) = 168 := by
    rw [GroupTheory.GLnTwoSplitting.card_linearEquiv_eq H.finrank₁, DW.W3.card_GL_three]
  have hsurj : Function.Surjective H.res := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (hrange.trans hGL.symm)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  set A : Subgroup G := S.QG ⊓ E with hA
  have : IsElementaryAbelian 2 A :=
    { is_comm := ⟨fun a b => Subtype.ext (hEc a a.2.2 b b.2.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hE.2 a a.2.2) }
  have hmax : DW.MaxEA S A := ⟨inf_le_left, by rw [hEQ, hw]; norm_num⟩
  obtain ⟨x, hxE, hxQ⟩ : ∃ x ∈ E, x ∉ S.QG := by
    by_contra h
    have hle : E ≤ S.QG := fun y hy => by_contra fun hq => h ⟨y, hy, hq⟩
    rw [hA, inf_eq_right.mpr hle, hEcard] at hEQ
    omega
  have hx : x * x = 1 := by
    rw [← pow_two]
    exact hE.2 x hxE
  exact H.nonempty_centralizer_mulEquiv hsurj (hEM hxE) hxQ hx hmax
    fun a ha => hEc x hxE a ha.2

end CFSG.ComponentClassification.AS81
