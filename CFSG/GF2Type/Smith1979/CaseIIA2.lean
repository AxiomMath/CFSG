module

public import CFSG.GF2Type.Smith1979.CaseIIA1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g) in
@[expose] noncomputable def Ea : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa g)

variable (S g t) in
@[expose] noncomputable def Ha : Submodule (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  (Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).comap
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype

theorem mem_Ha {u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} :
    u ∈ Ha S g t ↔ (u : S.Qt) ∈ Ea S g := by
  change (u : S.Qt) ∈ Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ _
  exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩

namespace Data

@[expose] noncomputable def aW (D : Data S g t) : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  ⟨S.cl (g * S.z * g⁻¹), Vt_le_commSpace D.H D.ht1 (cl_a_mem_Vt D.ht)⟩

variable (D : Data S g t)
include D

theorem coe_aW : ((D.aW : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
    S.cl (g * S.z * g⁻¹) := rfl

theorem aW_ne_zero : D.aW ≠ 0 := fun h =>
  cl_conj_z_ne_zero S D.H.conj_mem D.H.conj_ne (congrArg Subtype.val h)

theorem aW_mem_Vsub : D.aW ∈ Vsub g t := cl_a_mem_Vt D.ht

theorem Lbar_apply_cl {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have h : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [D.H.fixSub_eq]
    exact Submodule.mem_span_singleton_self _
  exact (mem_fixSub S).mp h s hs

theorem finrank_Ea : finrank (ZMod 2) (Ea S g) = 6 := by
  have h := S.finrank_clSub_QG_inf_Qa D.H.conj_mem D.H.conj_ne D.C.card_QG_inf_Qa
  have := D.hw
  change finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = 6
  omega

theorem Vt_le_Ea : Vt S g t ≤ Ea S g := by
  rw [← D.Tt_eq_Vt]
  exact Tt_le_clSub D.H D.C D.hL (k := g) ⟨D.H.conj_mem, cl_a_mem_Vt D.ht⟩

theorem map_Ea_le : (Ea S g).map (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
    (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  rintro _ ⟨v, hv, rfl⟩
  exact Lbar_apply_sub_mem_span' D.H.conj_mem hv D.ht

theorem exists_Ea_not_fix : ∃ v ∈ Ea S g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact D.ht1 (D.C.faithful t D.ht hcon)

theorem finrank_Ea_inf :
    finrank (ZMod 2) ↥(Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 5 := by
  have h1 := S2.finrank_map_sub_one_add (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (Ea S g)
  rw [← D.commSpace_eq_fixSpace] at h1
  have h2 := Submodule.finrank_mono D.map_Ea_le
  rw [finrank_span_singleton (cl_conj_z_ne_zero S D.H.conj_mem D.H.conj_ne)] at h2
  have h3 : finrank (ZMod 2) ((Ea S g).map
      (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvt⟩ := D.exists_Ea_not_fix
    have hmem : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (Ea S g).map
        (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := ⟨v, hv, rfl⟩
    have hbot : (Ea S g).map (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) = ⊥ :=
      Submodule.finrank_eq_zero.mp h0
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hvt hmem
  have := D.finrank_Ea
  omega

theorem eq_one_or_eq_t {s : S.O} (hs : s ∈ S.Lbar g)
    (hfix : ∀ v ∈ Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : s = 1 ∨ s = t := by
  obtain ⟨x₀, hx₀E, hx₀t⟩ := D.exists_Ea_not_fix
  have hspan : ∀ v ∈ Ea S g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = 0 ∨
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = S.cl (g * S.z * g⁻¹) := fun v hv =>
    mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' D.H.conj_mem hv D.ht)
  have hx₀a : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ = S.cl (g * S.z * g⁻¹) := by
    rcases hspan x₀ hx₀E with h | h
    · exact absurd (sub_eq_zero.mp h) hx₀t
    · exact h
  have hdec : ∀ v ∈ Ea S g, v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∨
      v + x₀ ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro v hv
    rw [D.commSpace_eq_fixSpace, mem_fixSpace, mem_fixSpace]
    rcases hspan v hv with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      rw [map_add]
      have : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v + (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - (v + x₀) =
          ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) := by abel
      rw [h, hx₀a, Sp.vec_add_self] at this
      exact sub_eq_zero.mp this
  have caseA : ∀ s' ∈ S.Lbar g, (∀ v ∈ Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ = x₀ → s' = 1 := by
    intro s' hs' hf hx
    refine D.C.faithful s' hs' fun v hv => ?_
    rcases hdec v hv with h | h
    · exact hf v ⟨hv, h⟩
    · have h1 := hf (v + x₀) ⟨add_mem hv hx₀E, h⟩
      rw [map_add, hx] at h1
      exact add_right_cancel h1
  have hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ = 0 ∨
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ = S.cl (g * S.z * g⁻¹) :=
    mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' D.H.conj_mem hx₀E hs)
  rcases hsa with h | h
  · exact Or.inl (caseA s hs hfix (sub_eq_zero.mp h))
  · right
    have hst : s * t ∈ S.Lbar g := mul_mem hs D.ht
    have hs1 : s * t = 1 := by
      refine caseA (s * t) hst (fun v hv => ?_) ?_
      · have hvf : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
          mem_fixSpace.mp (by rw [← D.commSpace_eq_fixSpace]; exact hv.2)
        rw [coe_mul_apply, hvf, hfix v hv]
      · rw [coe_mul_apply]
        have e : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ = x₀ + S.cl (g * S.z * g⁻¹) := by
          rw [← hx₀a]; abel
        rw [e, map_add, D.Lbar_apply_cl hs]
        have e2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ = x₀ + S.cl (g * S.z * g⁻¹) := by
          rw [← h]; abel
        rw [e2, add_assoc, Sp.vec_add_self, add_zero]
    have htt := mul_self_of_mem_Lbar S D.H.conj_mem D.ht
    calc s = s * (t * t) := by rw [htt, mul_one]
      _ = (s * t) * t := by rw [mul_assoc]
      _ = t := by rw [hs1, one_mul]

theorem finrank_Ha : finrank (ZMod 2) (Ha S g t) = 5 :=
  (Submodule.comapSubtypeEquivOfLe (inf_le_right : Ea S g ⊓
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ _)).finrank_eq.trans D.finrank_Ea_inf

theorem Vsub_le_Ha : Vsub g t ≤ Ha S g t := fun v hv => mem_Ha.mpr (D.Vt_le_Ea hv)

theorem mem_Ha_iff (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    u ∈ Ha S g t ↔ omegaU t u D.aW = 0 := by
  refine Sp.eq_perp_of_stable D.spData D.isGamma D.aW_mem_Vsub D.aW_ne_zero D.Vsub_le_Ha
    D.finrank_Ha ?_ u
  rintro _ ⟨r, rfl⟩ hγa d hd
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := congrArg Subtype.val hγa
  rw [mem_Ha, coe_resR]
  exact apply_mem_clSub_of_fix D.H.conj_mem D.H.conj_ne (Rbar_le_Mbar r.2) hfix
    (mem_Ha.mp hd)

@[expose] noncomputable def Lam : Subgroup
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  ((S.Lbar g).subgroupOf (Rbar S g t)).map D.resR

theorem mem_Lam {x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} :
    x ∈ D.Lam ↔ ∃ s : S.O, ∃ hs : s ∈ S.Lbar g, x = D.resR ⟨s, Lbar_le_Rbar D.ht hs⟩ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, Lbar_le_Rbar D.ht hs⟩, mem_subgroupOf.mpr hs, rfl⟩

theorem Lam_le_Gam : D.Lam ≤ D.Gam := Subgroup.map_le_range _ _

theorem Lam_sub_mem_span {x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hx : x ∈ D.Lam)
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hu : omegaU t u D.aW = 0) :
    x u - u ∈ Submodule.span (ZMod 2) {D.aW} := by
  obtain ⟨s, hs, rfl⟩ := D.mem_Lam.mp hx
  have hE : (u : S.Qt) ∈ Ea S g := mem_Ha.mp ((D.mem_Ha_iff u).mpr hu)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
    (Lbar_apply_sub_mem_span' D.H.conj_mem hE hs)
  refine Submodule.mem_span_singleton.mpr ⟨r, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, Submodule.coe_sub, coe_resR, coe_aW]
  exact hr

theorem Lam_conj_mem {γ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hγ : γ ∈ D.Gam) (hγa : γ D.aW = D.aW)
    {x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hx : x ∈ D.Lam) : γ * x * γ⁻¹ ∈ D.Lam := by
  obtain ⟨r, rfl⟩ := hγ
  obtain ⟨s, hs, rfl⟩ := D.mem_Lam.mp hx
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := congrArg Subtype.val hγa
  have hr : (r : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
    have h1 : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) =
        S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) := by
      rw [Subgroup.coe_one, one_mul]
      exact hfix
    have := mem_normalizer_of_fix D.H.conj_mem D.H.conj_ne (h := 1) (x := (r : S.O))
      (Rbar_le_Mbar r.2) h1
    rwa [Subgroup.coe_one, one_mul] at this
  have hs' : (r : S.O) * s * (r : S.O)⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hr s).mp hs
  rw [D.mem_Lam]
  refine ⟨_, hs', ?_⟩
  have e : (⟨(r : S.O) * s * (r : S.O)⁻¹, Lbar_le_Rbar D.ht hs'⟩ : Rbar S g t) =
      r * ⟨s, Lbar_le_Rbar D.ht hs⟩ * r⁻¹ := Subtype.ext rfl
  have h3 : D.resR r⁻¹ = (D.resR r)⁻¹ := map_inv D.resR r
  have h4 : D.resR (r * ⟨s, Lbar_le_Rbar D.ht hs⟩ * r⁻¹) =
      D.resR r * D.resR ⟨s, Lbar_le_Rbar D.ht hs⟩ * D.resR r⁻¹ :=
    (map_mul D.resR _ _).trans (congrArg (fun y => y * D.resR r⁻¹) (map_mul D.resR _ _))
  have e5 : D.resR ⟨(r : S.O) * s * (r : S.O)⁻¹, Lbar_le_Rbar D.ht hs'⟩ =
      D.resR r * D.resR ⟨s, Lbar_le_Rbar D.ht hs⟩ * (D.resR r)⁻¹ :=
    (congrArg D.resR e).trans (h4.trans
      (congrArg (fun y => D.resR r * D.resR ⟨s, Lbar_le_Rbar D.ht hs⟩ * y) h3))
  exact e5.symm

theorem Lam_not_transvection {x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hx : x ∈ D.Lam) :
    ¬ ∀ u, x u = u + omegaU t u D.aW • D.aW := by
  intro h
  obtain ⟨s, hs, rfl⟩ := D.mem_Lam.mp hx
  have hfix : ∀ v ∈ Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have hvH : (⟨v, hv.2⟩ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∈ Ha S g t :=
      mem_Ha.mpr hv.1
    have h0 := (D.mem_Ha_iff _).mp hvH
    have := h ⟨v, hv.2⟩
    rw [h0, zero_smul, add_zero] at this
    exact congrArg Subtype.val this
  have hu : ∀ u, D.resR ⟨s, Lbar_le_Rbar D.ht hs⟩ u = u := by
    intro u
    apply Subtype.ext
    rw [coe_resR]
    rcases D.eq_one_or_eq_t hs hfix with rfl | rfl
    · rfl
    · exact mem_fixSpace.mp (by rw [← D.commSpace_eq_fixSpace]; exact u.2)
  have hω : ∀ u, omegaU t u D.aW = 0 := by
    intro u
    have h1 := h u
    rw [hu u] at h1
    have h2 : omegaU t u D.aW • D.aW = 0 := add_eq_left.mp h1.symm
    exact (smul_eq_zero.mp h2).resolve_right D.aW_ne_zero
  exact D.aW_ne_zero (D.omegaU_nondeg.2 D.aW hω)

end Data

end CFSG.GF2Type.Smith1979.Case2
