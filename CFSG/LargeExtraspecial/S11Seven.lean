module

public import CFSG.LargeExtraspecial.S11SevenA
public import CFSG.LargeExtraspecial.S2FiveMod
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LargeExtraspecial.S2FiveT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  basisMatrixEquiv_mulVec)

universe u_G

section Basis

open Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
  (b : Module.Basis (Fin m) (ZMod 2) V)

@[expose] noncomputable def slAct :
    Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* (V ≃ₗ[ZMod 2] V) :=
  (basisMatrixEquiv b).symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

theorem slAct_apply (T : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) (v : V) :
    slAct b T v =
      b.equivFun.symm ((T : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ b.equivFun v) := by
  have h := basisMatrixEquiv_mulVec b (slAct b T) v
  have h2 : basisMatrixEquiv b (slAct b T) = Matrix.SpecialLinearGroup.toGL T := by
    simp [slAct]
  rw [h2] at h
  rw [← b.equivFun.symm_apply_apply (slAct b T v), ← h]
  rfl

theorem slAct_surjective : Function.Surjective (slAct b) := by
  intro e
  set U := basisMatrixEquiv b e with hU
  have hdet : (U : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1 := by
    have h1 : IsUnit (U : Matrix (Fin m) (Fin m) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit
    obtain ⟨w, hw⟩ := h1
    rw [← hw, Subsingleton.elim w 1, Units.val_one]
  refine ⟨⟨U, hdet⟩, ?_⟩
  have h1 : Matrix.SpecialLinearGroup.toGL
      (⟨U, hdet⟩ : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) = U := Units.ext rfl
  change (basisMatrixEquiv b).symm (Matrix.SpecialLinearGroup.toGL _) = e
  rw [h1, hU, MulEquiv.symm_apply_apply]

theorem slAct_tv {a φ : Fin m → ZMod 2} (h : φ ⬝ᵥ a = 0) (v : V) :
    slAct b (S2.tv a φ) v = v + (φ ⬝ᵥ b.equivFun v) • b.equivFun.symm a := by
  rw [slAct_apply, S2.tv_mulVec h, map_add, map_smul, LinearEquiv.symm_apply_apply]

end Basis

theorem finrank_le_finrank_fixAll_add {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N] {m : ℕ} (hm : 2 ≤ m)
    (ρ : Matrix.SpecialLinearGroup (Fin m) (ZMod 2) →* (N ≃ₗ[ZMod 2] N))
    (hT : ∀ t, S2.IsTransvection t →
      finrank (ZMod 2) (fixSpace (ρ t)) + 1 = finrank (ZMod 2) N) :
    finrank (ZMod 2) N ≤ finrank (ZMod 2) (S2.fixAll ρ) + m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have h1 := S2.finrank_le_finrank_iInf_add (fun i : Fin (n + 2) => ρ (S2.cycT i)) fun i => by
    have h := hT _ (S2.isTransvection_cycT i)
    have h2 := finrank_commSpace_add_finrank_fixSpace (ρ (S2.cycT i))
    omega
  rw [Fintype.card_fin] at h1
  have h2 : (⨅ i : Fin (n + 2), fixSpace (ρ (S2.cycT i))) ≤ S2.fixAll ρ := by
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hcl : ∀ g ∈ Subgroup.closure (Set.range (S2.cycT (n := n))), ρ g v = v := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact mem_fixSpace.mp (hv i)
      | one =>
        rw [map_one]
        rfl
      | mul g h _ _ hg hh => rw [map_mul, LinearEquiv.mul_apply, hh, hg]
      | inv g _ hg =>
        have : ρ g⁻¹ (ρ g v) = ρ g⁻¹ v := by rw [hg]
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
        exact this.symm
    exact S2.mem_fixAll.mpr fun g => hcl g (by rw [S2.closure_cycT_eq_top]; exact mem_top g)
  have h3 := Submodule.finrank_mono h2
  omega

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

section Conf

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.linCase_of {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) (htk : t ∈ S.Lbar k) :
    LinCase S k htk := by
  obtain ⟨hkz, -⟩ := K.base_of_mem hk
  have hy' := hy.of_conj hk.1 hkz
  refine (hy'.lin htk K.ne_one).resolve_left fun hR => ?_
  have h1 := K.lin.two_le_finrank
  rw [← hy.Vt_eq hk.1 hkz] at h1
  have h2 := Submodule.finrank_mono (Vt_le_span_of_Rbar_eq hy'.hyp4 hy'.cons hR)
  have h3 := finrank_span_singleton_le_one (S.cl (k * S.z * k⁻¹))
  omega

variable (hCE : CentralExtInput.{u_G})
include hCE

theorem Conf.finrank_fixSpace_TtHom (r : Rbar S g t) {c : Vt S g t} (hc : c ≠ 0)
    (hrc : ∀ v : Vt S g t, resV hy.hyp4.conj_mem t r v - v ∈ (ZMod 2) ∙ c)
    (hr1 : resV hy.hyp4.conj_mem t r ≠ 1) :
    finrank (ZMod 2) (fixSpace (TtHom S g hy.hyp4 t r)) + 1 = finrank (ZMod 2) (Tt S g t) := by
  obtain ⟨b', k, hbE, hk, hbcl⟩ := K.exists_coimage hy c.2 fun h => hc (Subtype.ext h)
  subst hk
  obtain ⟨hkz, htk⟩ := K.base_of_mem hbE
  have hL := K.linCase_of hy hbE htk
  have hV := hy.Vt_eq hbE.1 hkz t
  set e := resV hy.hyp4.conj_mem t r with he
  set e' : Vt S k t ≃ₗ[ZMod 2] Vt S k t :=
    (LinearEquiv.ofEq _ _ hV).trans (e.trans (LinearEquiv.ofEq _ _ hV.symm)) with he'
  have he'v : ∀ v : Vt S k t, ((e' v : Vt S k t) : S.Qt) =
      ((e ⟨v, hV ▸ v.2⟩ : Vt S g t) : S.Qt) := by
    intro v
    rw [he', LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    congr 2
  have hmem : e' ∈ LmodN S k t := by
    rw [hL.LmodN_eq, mem_centreGroup]
    intro v
    rw [mem_span_singleton_subtype]
    have h1 := hrc ⟨v, hV ▸ v.2⟩
    rw [mem_span_singleton_subtype] at h1
    rw [Submodule.coe_sub, he'v]
    change _ ∈ (ZMod 2) ∙ S.cl (k * S.z * k⁻¹)
    rw [hbcl]
    exact h1
  obtain ⟨ℓ, hℓ, hℓe⟩ := hmem
  have hℓR : ℓ ∈ Rbar S g t := by
    rw [← hy.Rbar_eq hbE.1 hkz]
    exact Lbar_le_Rbar htk hℓ
  have hagree : ∀ w ∈ Tt S g t, ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
    intro w hw
    have hN : (r : S.O)⁻¹ * ℓ ∈ Nbar S g t := by
      refine ⟨mul_mem (inv_mem r.2) hℓR, fun v hv => ?_⟩
      have h1 := hℓe ⟨v, hV ▸ hv⟩
      rw [he'v] at h1
      have h2 : ((e ⟨v, hv⟩ : Vt S g t) : S.Qt) = ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
        coe_resV_apply _ r _
      rw [coe_mul_apply, ← h1, h2, inv_apply_apply_O]
    have h3 := K.apply_eq_of_mem_Nbar hy hCE hN hw
    rw [coe_mul_apply] at h3
    have h4 := congrArg ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h3
    rwa [apply_inv_apply_O, eq_comm] at h4
  have hTP : Tt S g t ≤ S.clSub (S.QG ⊓ S.Qa k) :=
    Tt_le_clSub hy.hyp4 hy.cons K.lin (K.QG_inf_Qa_le_V hy hbE)
  have hVT : Vt S g t ≤ Tt S g t := Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin
  have hcbT : S.cl (k * S.z * k⁻¹) ∈ Tt S g t := by rw [hbcl]; exact hVT c.2
  have hle : commSpace (TtHom S g hy.hyp4 t r) ≤ (ZMod 2) ∙ (⟨_, hcbT⟩ : Tt S g t) := by
    intro x hx
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hx
    rw [mem_span_singleton_subtype, Submodule.coe_sub, coe_TtHom_apply, hagree w w.2]
    exact Lbar_apply_sub_mem_span' hbE.1 (hTP w.2) hℓ
  have hne : commSpace (TtHom S g hy.hyp4 t r) ≠ ⊥ := by
    intro h0
    apply hr1
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    have h1 : TtHom S g hy.hyp4 t r ⟨v, hVT v.2⟩ - ⟨v, hVT v.2⟩ ∈
        commSpace (TtHom S g hy.hyp4 t r) := sub_mem_commSpace _ _
    rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_TtHom_apply] at h2
    rw [coe_resV_apply]
    exact h2
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_singleton_le_one (⟨_, hcbT⟩ : Tt S g t)
  have h3 : finrank (ZMod 2) (commSpace (TtHom S g hy.hyp4 t r)) ≠ 0 :=
    fun h => hne (Submodule.finrank_eq_zero.mp h)
  have h4 := finrank_commSpace_add_finrank_fixSpace (TtHom S g hy.hyp4 t r)
  omega

theorem Conf.timmesfeld_11_7 : Tt S g t = Vt S g t := by
  set bas := Module.finBasis (ZMod 2) (Vt S g t) with hbas
  have haQ := hy.hyp4.conj_mem
  have hrange : (resV haQ t).range = ⊤ := (range_resV haQ t).trans K.lin.eq_top
  set σ' : (Vt S g t ≃ₗ[ZMod 2] Vt S g t) →* (Tt S g t ≃ₗ[ZMod 2] Tt S g t) :=
    (S6.descend (resV haQ t) (TtHom S g hy.hyp4 t) (K.ker_resV_le hy hCE)).comp
      ((MonoidHom.id _).codRestrict (resV haQ t).range fun e => by
        rw [hrange]
        exact mem_top e) with hσ'
  have hσ'r : ∀ r : Rbar S g t, σ' (resV haQ t r) = TtHom S g hy.hyp4 t r := fun r => by
    rw [hσ', MonoidHom.comp_apply]
    exact S6.descend_apply' (resV haQ t) (TtHom S g hy.hyp4 t) (K.ker_resV_le hy hCE) rfl
  have hsurj : ∀ e, ∃ r : Rbar S g t, resV haQ t r = e := fun e => by
    have : e ∈ (resV haQ t).range := by rw [hrange]; exact mem_top e
    exact this
  set ρ' := σ'.comp (slAct bas) with hρ'
  have hρ'T : ∀ T, ∃ r : Rbar S g t, resV haQ t r = slAct bas T ∧
      ρ' T = TtHom S g hy.hyp4 t r := fun T => by
    obtain ⟨r, hr⟩ := hsurj (slAct bas T)
    refine ⟨r, hr, ?_⟩
    rw [hρ', MonoidHom.comp_apply, ← hr, hσ'r]
  have hT : ∀ T, S2.IsTransvection T →
      finrank (ZMod 2) (fixSpace (ρ' T)) + 1 = finrank (ZMod 2) (Tt S g t) := by
    rintro _ ⟨a, φ, ha, hφ, hφa, rfl⟩
    obtain ⟨r, hr, hρr⟩ := hρ'T (S2.tv a φ)
    rw [hρr]
    have hc0 : bas.equivFun.symm a ≠ 0 := by
      intro h
      apply ha
      have := congrArg bas.equivFun h
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    refine K.finrank_fixSpace_TtHom hy hCE r hc0 (fun v => ?_) ?_
    · rw [hr, slAct_tv bas hφa v, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [hr]
      intro h1
      obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
        by_contra h
        push Not at h
        exact hφ (funext h)
      have h2 := congrArg (fun f => f (bas.equivFun.symm (Pi.single i 1))) h1
      simp only [slAct_tv bas hφa, LinearEquiv.apply_symm_apply] at h2
      rw [show (1 : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (bas.equivFun.symm (Pi.single i 1)) =
        bas.equivFun.symm (Pi.single i 1) from rfl, add_eq_left] at h2
      have hφi : φ ⬝ᵥ Pi.single i 1 = φ i := by
        rw [dotProduct_comm, single_dotProduct, one_mul]
      exact hc0 ((smul_eq_zero.mp h2).resolve_left (hφi ▸ hi))
  have hfix : S2.fixAll ρ' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwR : ∀ x ∈ Rbar S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      intro x hx
      obtain ⟨T, hT⟩ := slAct_surjective bas (resV haQ t ⟨x, hx⟩)
      have h2 : ρ' T = TtHom S g hy.hyp4 t ⟨x, hx⟩ := by
        rw [hρ', MonoidHom.comp_apply, hT, hσ'r]
      have h1 := congrArg Subtype.val ((S2.mem_fixAll.mp hw) T)
      rw [h2, coe_TtHom_apply] at h1
      exact h1
    have hwL : (w : S.Qt) ∈ fixSub S (S.Lbar g) :=
      fun x hx => hwR x (Lbar_le_Rbar K.mem_Lbar hx)
    rw [hy.hyp4.fixSub_eq] at hwL
    rcases mem_span_cl_iff.mp hwL with h0 | h0
    · exact Subtype.ext h0
    · exfalso
      obtain ⟨v, hv, hvs⟩ : ∃ v ∈ Vt S g t, v ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
        by_contra h
        push Not at h
        have h3 := Submodule.finrank_mono (show Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
          from fun v hv => h v hv)
        have h4 := finrank_span_singleton_le_one (S.cl (g * S.z * g⁻¹))
        have h5 := K.lin.two_le_finrank
        omega
      have hv0 : (⟨v, hv⟩ : Vt S g t) ≠ 0 := fun h =>
        hvs (by rw [show v = 0 from congrArg Subtype.val h]; exact zero_mem _)
      obtain ⟨x, hx, hxv⟩ := K.lin.mem_orbit ⟨v, hv⟩ hv0
      have h5 := hwR x hx
      rw [h0] at h5
      apply hvs
      change v = _ at hxv
      rw [hxv, h5]
      exact Submodule.mem_span_singleton_self _
  have hcod := finrank_le_finrank_fixAll_add K.lin.two_le_finrank ρ' hT
  rw [hfix, finrank_bot, zero_add] at hcod
  have hVT := Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin
  exact (Submodule.eq_of_le_of_finrank_eq hVT
    (le_antisymm (Submodule.finrank_mono hVT) hcod)).symm

end Conf

end CFSG.LargeExtraspecial.S11
