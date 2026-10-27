module

public import CFSG.LargeExtraspecial.S4FiveW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4ThmA

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

structure ThmAData (S : Setting G) (g : G) (t : S.O) : Prop where
  H : Hyp4 S g
  C : Cons311 S g
  ht : t ∈ S.Lbar g
  ht1 : t ≠ 1
  hVQ : ¬ V S g t ≤ S.Qa g
  hw : S.width = 4
  hdim : finrank (ZMod 2) (Vt S g t) = 4
  htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v

theorem exists_comm_iff {t : S.O} (φ : Vt S g t →ₗ[ZMod 2] ZMod 2) :
    ∃ q ∈ S.QG, ∀ (y : G) (hy : y ∈ V S g t), q * y = y * q ↔ φ ⟨S.cl y, hy.2⟩ = 0 := by
  obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend φ
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : S.Qt, ∀ y, S.q.polarBilin s₀ y = φ' y :=
    ⟨(LinearMap.BilinForm.toDual (S.q.polarBilin : LinearMap.BilinForm (ZMod 2) S.Qt)
      S.q_nondegenerate).symm φ', fun y => LinearMap.BilinForm.apply_toDual_symm_apply φ' y⟩
  obtain ⟨q, hqQ, hq⟩ := S.exists_cl s₀
  refine ⟨q, hqQ, fun y hy => ?_⟩
  rw [← S.polar_cl_eq_zero_iff hqQ hy.1, hq, ← polarBilin_apply_apply, hs₀]
  exact iff_of_eq (congrArg (· = (0 : ZMod 2)) (LinearMap.congr_fun hφ' ⟨S.cl y, hy.2⟩))

namespace ThmAData

variable {t : S.O} (D : ThmAData S g t)
include D

theorem haQ : g * S.z * g⁻¹ ∈ S.QG := D.H.conj_mem

theorem hne : g * S.z * g⁻¹ ≠ S.z := D.H.conj_ne

theorem V_comm {x y : G} (hx : x ∈ V S g t) (hy : y ∈ V S g t) : x * y = y * x :=
  (S.polar_cl_eq_zero_iff hx.1 hy.1).mp (polar_eq_zero_of_mem_Vt D.H D.ht1 hx.2 hy.2)

theorem V_mul_self {x : G} (hx : x ∈ V S g t) : x * x = 1 :=
  (sq x).symm.trans ((S.q_cl_eq_zero_iff hx.1).mp (q_eq_zero_of_mem_Vt D.H D.ht1 hx.2))

theorem a_mem_V : g * S.z * g⁻¹ ∈ V S g t := ⟨D.haQ, cl_a_mem_Vt D.ht⟩

theorem card_V : Nat.card (V S g t) = 32 := by
  change Nat.card (S.clPre (Vt S g t)) = 32
  rw [S.card_clPre, S.card_submodule, D.hdim]
  norm_num

theorem Vt_eq_Wt : Vt S g t = Wt S g t := by
  have h1 := finrank_Wt (S := S) (g := g) (t := t)
  have h2 := S.finrank_Qt_eq_two_mul_width
  have h3 := D.hw
  have h4 := D.hdim
  exact Submodule.eq_of_le_of_finrank_le (Vt_le_Wt D.H D.ht1) (by omega)

theorem commSpace_eq : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t :=
  (commSpace_t_eq D.H D.C D.ht D.ht1 D.hVQ).1

theorem fixSpace_eq : fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t := by
  rw [(commSpace_t_eq D.H D.C D.ht D.ht1 D.hVQ).2, D.Vt_eq_Wt]

theorem t_apply_of_mem {v : S.Qt} (hv : v ∈ Vt S g t) : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  mem_fixSpace.mp (D.fixSpace_eq ▸ hv)

theorem exists_t_sub_eq {v : S.Qt} (hv : v ∈ Vt S g t) :
    ∃ w, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v :=
  mem_commSpace.mp (D.commSpace_eq ▸ hv)

theorem mem_V_of_comm {q : G} (hq : q ∈ S.QG) (hc : ∀ v ∈ V S g t, q * v = v * q) :
    q ∈ V S g t := by
  have hW : q ∈ W S g t := ⟨hq, mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
  rw [W_eq_clPre] at hW
  exact ⟨hq, D.Vt_eq_Wt ▸ hW.2⟩

theorem t_mul_t : t * t = 1 := mul_self_of_mem_Lbar S D.H.conj_mem D.ht

theorem comm_of_ρ_eq_t {x : G} (hxM : x ∈ S.M) (hx : S.ρ ⟨x, hxM⟩ = t) (hxx : x * x = 1)
    {v : G} (hv : v ∈ V S g t) : x * v = v * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  obtain ⟨wt, hwt⟩ := D.exists_t_sub_eq hv.2
  obtain ⟨w, hwQ, hw⟩ := S.exists_cl wt
  have hxwQ : x * w * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM hwQ
  have hcQ : x * w * x⁻¹ * w⁻¹ ∈ S.QG := S.QG.mul_mem hxwQ (S.QG.inv_mem hwQ)
  have h1 : S.cl (x * w * x⁻¹) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) := by
    have h := S.ρ_cl ⟨x, hxM⟩ hwQ
    rw [hx] at h
    exact h.symm
  have hcl : S.cl (x * w * x⁻¹ * w⁻¹) = S.cl v := by
    rw [S.cl_mul hxwQ (S.QG.inv_mem hwQ), S.cl_inv hwQ, h1, hw, ← hwt, ZModModule.sub_eq_add]
  obtain ⟨c, hc⟩ : ∃ c, c = x * w * x⁻¹ * w⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hcQ hcl
  have hcV : c ∈ V S g t := ⟨hcQ, by rw [hcl]; exact hv.2⟩
  have hcc : c * c = 1 := D.V_mul_self hcV
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hc, hxi]
    calc x * (x * w * x * w⁻¹) * x = (x * x) * (w * x * w⁻¹ * x) := by group
      _ = w * x * w⁻¹ * x := by rw [hxx, one_mul]
      _ = (x * w * x * w⁻¹)⁻¹ := by
        rw [show (x * w * x * w⁻¹)⁻¹ = w * x⁻¹ * w⁻¹ * x⁻¹ by group, hxi]
  have hxc' : x * c = c * x := by
    have h2 : x * c * x⁻¹ = c := hxc.trans (inv_eq_of_mul_eq_one_right hcc)
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h2]
  rcases (S.cl_eq_cl_iff hcQ hv.1).mp hcl with h | h
  · rw [h]
    exact hxc'
  · rw [h, ← mul_assoc, hxc', mul_assoc, S.z_comm hxM, ← mul_assoc]

theorem exists_cl_comm_eq {x : G} (hxM : x ∈ S.M) (hx : S.ρ ⟨x, hxM⟩ = t) {v : G}
    (hv : v ∈ V S g t) : ∃ q ∈ S.QG, S.cl (q * x * q⁻¹ * x⁻¹) = S.cl v := by
  obtain ⟨wt, hwt⟩ := D.exists_t_sub_eq hv.2
  obtain ⟨q, hqQ, hq⟩ := S.exists_cl wt
  refine ⟨q, hqQ, ?_⟩
  have hxqQ : x * q⁻¹ * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM (S.QG.inv_mem hqQ)
  have h1 : S.cl (x * q⁻¹ * x⁻¹) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) := by
    have h := S.ρ_cl ⟨x, hxM⟩ (S.QG.inv_mem hqQ)
    rw [hx, S.cl_inv hqQ] at h
    exact h.symm
  have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
  rw [e, S.cl_mul hqQ hxqQ, h1, hq, ← hwt, ZModModule.sub_eq_add, add_comm]

theorem conj_mem_V_of_mem_Rbar {m : G} (hm : m ∈ S.M) (hr : S.ρ ⟨m, hm⟩ ∈ Rbar S g t) {y : G}
    (hy : y ∈ V S g t) : m * y * m⁻¹ ∈ V S g t :=
  conj_mem_V_of_commute D.H (k := ⟨m, hm⟩) (commute_of_mem_Rbar D.H.conj_mem hr) hy

theorem exists_conj_eq_of_mem_V {v w : G} (hv : v ∈ V S g t) (hw : w ∈ V S g t) (hv1 : v ≠ 1)
    (hvz : v ≠ S.z) (hw1 : w ≠ 1) (hwz : w ≠ S.z) :
    ∃ (m : G) (hm : m ∈ S.M), S.ρ ⟨m, hm⟩ ∈ Rbar S g t ∧ m * v * m⁻¹ = w := by
  have hcl0 : ∀ {y : G}, y ∈ V S g t → y ≠ 1 → y ≠ S.z → S.cl y ≠ 0 := fun hy hy1 hyz h => by
    rcases (S.cl_eq_zero_iff hy.1).mp h with h | h
    · exact hy1 h
    · exact hyz h
  obtain ⟨e₁, he₁, h₁⟩ := D.htr ⟨S.cl v, hv.2⟩
    fun h => hcl0 hv hv1 hvz (congrArg Subtype.val h)
  obtain ⟨e₂, he₂, h₂⟩ := D.htr ⟨S.cl w, hw.2⟩
    fun h => hcl0 hw hw1 hwz (congrArg Subtype.val h)
  have he : e₂ * e₁⁻¹ ∈ RmodN S g t := mul_mem he₂ (inv_mem he₁)
  have hevw : (e₂ * e₁⁻¹) ⟨S.cl v, hv.2⟩ = ⟨S.cl w, hw.2⟩ := by
    rw [LinearEquiv.mul_apply, ← h₁, show e₁⁻¹ (e₁ (aV D.ht)) = aV D.ht from
      e₁.symm_apply_apply _, h₂]
  obtain ⟨r, hr, her⟩ := mem_RmodN.mp he
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hcl : S.cl w = S.cl ((m : G) * v * (m : G)⁻¹) := by
    have h := her ⟨S.cl v, hv.2⟩
    rw [hevw] at h
    exact h.trans (S.ρ_cl m hv.1)
  have hbQ : (m : G) * v * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 hv.1
  have hb0 : S.cl ((m : G) * v * (m : G)⁻¹) ≠ 0 := by
    rw [← hcl]
    exact hcl0 hw hw1 hwz
  have hb1 : (m : G) * v * (m : G)⁻¹ ≠ 1 := fun h =>
    hb0 ((S.cl_eq_zero_iff hbQ).mpr (Or.inl h))
  have hbz : (m : G) * v * (m : G)⁻¹ ≠ S.z := fun h =>
    hb0 ((S.cl_eq_zero_iff hbQ).mpr (Or.inr h))
  rcases (S.cl_eq_cl_iff hbQ hw.1).mp hcl.symm with h | h
  · exact ⟨m, m.2, hr, h.symm⟩
  · obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hbQ hb1 hbz
    have huM : u ∈ S.M := S.QG_le_M huQ
    refine ⟨u * (m : G), S.M.mul_mem huM m.2, ?_, ?_⟩
    · have e : S.ρ ⟨u * (m : G), S.M.mul_mem huM m.2⟩ = S.ρ m := by
        have e' : (⟨u * (m : G), S.M.mul_mem huM m.2⟩ : S.M) = ⟨u, huM⟩ * m := rfl
        rw [e', map_mul, (S.ρ_eq_one_iff ⟨u, huM⟩).mpr huQ, one_mul]
      rw [e]
      exact hr
    · rw [h, ← hu]
      group

theorem axis {s : S.O} (hs : s ∈ S.Lbar g)
    (hfix : ∀ e ∈ V S g t ⊓ S.Qa g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e) :
    s = 1 ∨ s = t := by
  have haQ := D.haQ
  set E : Subgroup G := S.QG ⊓ S.Qa g with hE
  have faith : ∀ s' ∈ S.Lbar g,
      (∀ e ∈ E, (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e) → s' = 1 := by
    intro s' hs' hf
    refine D.C.faithful s' hs' fun v hv => ?_
    obtain ⟨e, he, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact hf e he
  have h4 : ∀ s' ∈ S.Lbar g, ∀ e ∈ E,
      (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) - S.cl e = 0 ∨
        (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) - S.cl e = S.cl (g * S.z * g⁻¹) :=
    fun s' hs' e he => OrthoF2.mem_span_singleton_iff.mp (Lbar_apply_sub_mem_span haQ he hs')
  have hA5 : ∀ e ∈ E, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e →
      e ∈ V S g t ⊓ S.Qa g := by
    intro e he hte
    refine ⟨⟨he.1, ?_⟩, he.2⟩
    rw [← D.fixSpace_eq]
    exact mem_fixSpace.mpr hte
  obtain ⟨e₁, he₁, hte₁⟩ : ∃ e₁ ∈ E, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) ≠ S.cl e₁ := by
    by_contra hcon
    push Not at hcon
    exact D.ht1 (faith t D.ht hcon)
  have ht₁ : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) - S.cl e₁ = S.cl (g * S.z * g⁻¹) :=
    (h4 t D.ht e₁ he₁).resolve_left fun h => hte₁ (sub_eq_zero.mp h)
  have claim : ∀ s' ∈ S.Lbar g, (∀ e ∈ V S g t ⊓ S.Qa g,
      (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e) →
      (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) = S.cl e₁ → s' = 1 := by
    intro s' hs' hf h1
    refine faith s' hs' fun e he => ?_
    rcases h4 t D.ht e he with h0 | h0
    · exact hf e (hA5 e he (sub_eq_zero.mp h0))
    · have heE : e * e₁ ∈ E := E.mul_mem he he₁
      have hcl : S.cl (e * e₁) = S.cl e + S.cl e₁ := S.cl_mul he.1 he₁.1
      have hfixe : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (e * e₁)) = S.cl (e * e₁) := by
        rw [hcl, map_add]
        have h2 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e + S.cl (g * S.z * g⁻¹) := by
          rw [← h0]; abel
        have h3 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) = S.cl e₁ + S.cl (g * S.z * g⁻¹) := by
          rw [← ht₁]; abel
        rw [h2, h3]
        calc S.cl e + S.cl (g * S.z * g⁻¹) + (S.cl e₁ + S.cl (g * S.z * g⁻¹)) =
            S.cl e + S.cl e₁ + (S.cl (g * S.z * g⁻¹) + S.cl (g * S.z * g⁻¹)) := by abel
          _ = S.cl e + S.cl e₁ := by rw [OrthoF2.vec_add_self, add_zero]
      have h5 := hf (e * e₁) (hA5 _ heE hfixe)
      rw [hcl] at h5
      rw [map_add, h1] at h5
      exact add_right_cancel h5
  by_cases h1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) = S.cl e₁
  · exact Or.inl (claim s hs hfix h1)
  · right
    have hs₁ : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) - S.cl e₁ = S.cl (g * S.z * g⁻¹) :=
      (h4 s hs e₁ he₁).resolve_left fun h => h1 (sub_eq_zero.mp h)
    have hst : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e₁) :=
      sub_left_injective (hs₁.trans ht₁.symm)
    have hts : t * s = 1 := by
      refine claim (t * s) (mul_mem D.ht hs) (fun e he => ?_) ?_
      · rw [coe_mul_apply, hfix e he]
        exact D.t_apply_of_mem he.1.2
      · rw [coe_mul_apply, hst, ← coe_mul_apply, D.t_mul_t]
        rfl
    rw [eq_inv_of_mul_eq_one_right hts]
    exact inv_eq_of_mul_eq_one_right D.t_mul_t

end ThmAData

end CFSG.GF2Type.Smith1979.W4ThmA
