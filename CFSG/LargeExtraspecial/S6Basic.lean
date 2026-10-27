module

public import CFSG.LargeExtraspecial.S3bTenB
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4FiveConj
public import CFSG.LargeExtraspecial.S4FiveRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Wt_mul (h : S.M) (t : S.O) : Wt S ((h : G) * g) t = Wt S g t := by
  unfold Wt
  rw [Vt_mul]

theorem ρ_inv_mem_Rbar {t : S.O} {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    S.ρ k⁻¹ ∈ Rbar S ((k : G) * g) t := by
  rw [Rbar_mul, map_inv]
  exact inv_mem hk

omit [Finite G] in
theorem inv_mul_coe (k : S.M) : ((k⁻¹ : S.M) : G) * ((k : G) * g) = g := by
  rw [← mul_assoc, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, one_mul]

theorem not_V_le_Qa_mul (H : Hyp4 S g) {t : S.O} (hVQ : ¬ V S g t ≤ S.Qa g) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) : ¬ V S ((k : G) * g) t ≤ S.Qa ((k : G) * g) := by
  intro hle
  apply hVQ
  have h1 := V_le_Qa_mul (H.mul k) hle (ρ_inv_mem_Rbar hk)
  rwa [inv_mul_coe, V_mul] at h1

theorem mem_clSub_Qa_mul_iff (k : S.M) {v : S.Qt} :
    v ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ↔
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  rw [QG_inf_Qa_mul k, mem_clSub_map_conj_iff k inf_le_left]

theorem apply_mem_clSub_Qa_mul (k : S.M) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
  rw [mem_clSub_Qa_mul_iff, inv_apply_apply_O]
  exact hv

omit [Finite G] in
theorem cl_mem_clSub_self (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ

theorem apply_mem_clSub_of_fix {g' : G} (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hbz : g' * S.z * g'⁻¹ ≠ S.z) {x : S.O} (hx : x ∈ S.Mbar)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g' * S.z * g'⁻¹)) = S.cl (g' * S.z * g'⁻¹))
    {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g')) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g') := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := MonoidHom.mem_range.mp hx
  have h1 := hfix
  rw [S.ρ_cl _ hbQ] at h1
  have hyb := (S.cl_eq_cl_iff hbQ (S.conj_mem_QG hy hbQ)).mp h1.symm
  exact S.ρ_mem_clSub_of_fix hbQ hbz hy hyb hv

theorem Nbar_apply_mem_clSub {t : S.O} {g' : G} (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hbz : g' * S.z * g'⁻¹ ≠ S.z) (hbV : S.cl (g' * S.z * g'⁻¹) ∈ Vt S g t) {x : S.O}
    (hx : x ∈ Nbar S g t) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g')) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g') :=
  apply_mem_clSub_of_fix hbQ hbz (Rbar_le_Mbar (Nbar_le_Rbar hx)) (hx.2 _ hbV) hv

theorem Lbar_apply_sub_mem_span' (haQ : g * S.z * g⁻¹ ∈ S.QG) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨x, hx, -, rfl⟩ := S.mem_clSub_iff.mp hv
  exact Lbar_apply_sub_mem_span haQ hx hs

theorem polar_eq_zero_of_mem_clSub (hne : g * S.z * g⁻¹ ≠ S.z) {u v : S.Qt}
    (hu : u ∈ S.clSub (S.QG ⊓ S.Qa g)) (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    polar S.q u v = 0 := by
  rw [polar, S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne (add_mem hu hv),
    S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hu, S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hv]
  simp

theorem orthogonal_clSub_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1)) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) =
      S.clSub (S.QG ⊓ S.Qa g) := by
  have hle : S.clSub (S.QG ⊓ S.Qa g) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    simp only [polarBilin_apply_apply]
    exact polar_eq_zero_of_mem_clSub hne hu hv
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (S.clSub (S.QG ⊓ S.Qa g))
  have h2 := S.finrank_clSub_QG_inf_Qa haQ hne hcard
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

theorem clSub_not_le_Wt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (hVQ : ¬ V S g t ≤ S.Qa g) : ¬ S.clSub (S.QG ⊓ S.Qa g) ≤ Wt S g t := by
  intro hle
  apply hVQ
  rw [V_le_Qa_iff H.conj_mem H.conj_ne, ← orthogonal_clSub_eq H.conj_mem H.conj_ne
    C.card_QG_inf_Qa]
  intro u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  simp only [polarBilin_apply_apply]
  have := (mem_Wt.mp (hle hv)) u hu
  rwa [polar_comm] at this

theorem finrank_clSub_inf_Wt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) + 1 = S.width := by
  have hdim := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  have hfix := (commSpace_t_eq H C ht ht1 hVQ).2
  have h1 := S2.finrank_map_sub_one_add (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.clSub (S.QG ⊓ S.Qa g))
  have hmap : (S.clSub (S.QG ⊓ S.Qa g)).map ((t : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Lbar_apply_sub_mem_span' H.conj_mem hv ht
  have h2 := Submodule.finrank_mono hmap
  rw [finrank_span_singleton (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)] at h2
  have hlt : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t < S.clSub (S.QG ⊓ S.Qa g) :=
    lt_of_le_of_ne inf_le_left fun heq => clSub_not_le_Wt H C hVQ (heq ▸ inf_le_right)
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [← hfix] at h3 ⊢
  omega

section Beta

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

theorem finrank_clSub_inf_Vt :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) + 1 =
      finrank (ZMod 2) (Vt S g t) := by
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set B := beta H C ht ht1 hVQ (aV ht) with hB
  have hK : LinearMap.ker B = P.comap (Vt S g t).subtype := by
    ext y
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact beta_aV_eq_zero_iff H C ht ht1 hVQ y
  have hB0 : B ≠ 0 := by
    intro h0
    apply aV_ne_zero H ht
    exact (beta_nondegenerate H C ht ht1 hVQ).1 _ fun y => by
      change B y = 0
      rw [h0, LinearMap.zero_apply]
  have hrange : LinearMap.range B = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, B y ≠ 0 := by
      by_contra h
      push Not at h
      exact hB0 (LinearMap.ext h)
    have hy1 := OrthoF2.zmod2_eq_one_of_ne_zero hy
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker B
  rw [hrange, finrank_top, finrank_self, hK] at h1
  have h2 : P.comap (Vt S g t).subtype = (P ⊓ Vt S g t).comap (Vt S g t).subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [h2, (Submodule.comapSubtypeEquivOfLe (inf_le_right : P ⊓ Vt S g t ≤ Vt S g t)).finrank_eq]
    at h1
  omega

theorem beta_bV_eq_zero_iff {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hth : t ∈ S.Lbar ((h : G) * g)) (y : Vt S g t) :
    beta H C ht ht1 hVQ (bV hth) y = 0 ↔ (y : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
  set r : Rbar S g t := ⟨S.ρ h, hh⟩ with hr
  have hb : bV hth = resV H.conj_mem t r (aV ht) := Subtype.ext (by
    rw [coe_bV, coe_resV_apply]
    exact (ρ_cl_conj_z S h H.conj_mem).symm)
  have hy : resV H.conj_mem t r (resV H.conj_mem t r⁻¹ y) = y := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have e1 : beta H C ht ht1 hVQ (bV hth) y =
      beta H C ht ht1 hVQ (aV ht) (resV H.conj_mem t r⁻¹ y) := by
    conv_lhs => rw [hb, ← hy]
    exact beta_apply_resV H C ht ht1 hVQ r _ _
  rw [e1, beta_aV_eq_zero_iff H C ht ht1 hVQ, coe_resV_apply, mem_clSub_Qa_mul_iff]
  rfl

end Beta

end CFSG.LargeExtraspecial.S6
