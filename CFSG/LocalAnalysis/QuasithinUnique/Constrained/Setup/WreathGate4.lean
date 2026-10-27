module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathHyp

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type} [Group H] [Finite H] {R M V : Subgroup H}
  {Wm : Type} [AddCommGroup Wm] [Module (ZMod 2) Wm] [Finite Wm] [V.Normal]

theorem GateHyp.exists_wreathHyp_model (g : GateHyp R M V) (θ : ↥V ≃* Multiplicative Wm) :
    ∃ (r : ℕ) (I : Fin r → Subgroup H) (W F : Subgroup H)
      (Pm : Subgroup (Equiv.Perm (Fin r))), (∃ k : ℕ, r = 2 ^ k) ∧ WreathHyp R M V W F I Pm := by
  classical
  obtain ⟨-, hex⟩ := g.S3Wreath_model θ
  obtain ⟨r, hr, L, S, Il, P, hd⟩ := hex
  set ρ := modelRho θ with hρ
  set Hl : Subgroup (Wm ≃ₗ[ZMod 2] Wm) := (⊤ : Subgroup H).map ρ with hHl
  set Nn : Subgroup (Wm ≃ₗ[ZMod 2] Wm) := (CFSG.fittingSubgroup ↥Hl).map Hl.subtype with hNn
  obtain ⟨hW, hrange⟩ := hd.image_eq
  have hmemHl : ∀ x : H, ρ x ∈ Hl := fun x => ⟨x, Subgroup.mem_top x, rfl⟩
  set Wl : Submodule (ZMod 2) Wm := Offender.commGL Nn ⊤ with hWl
  have hWeq : Wl = ⨆ i, Il i := hd.W_eq
  have hWl_inv : ∀ x : H, ∀ w ∈ Wl, ρ x w ∈ Wl := fun x w hw => hW (ρ x) (hmemHl x) w hw
  have hNnle : Nn ≤ Hl := Subgroup.map_subtype_le _
  have hNnorm : (Nn.subgroupOf Hl).Normal := by
    have : Nn.subgroupOf Hl = CFSG.fittingSubgroup ↥Hl :=
      Subgroup.comap_map_eq_self_of_injective Hl.subtype_injective _
    rw [this]
    exact CFSG.fittingSubgroup_normal
  have hF_inv : ∀ x : H, ∀ u ∈ Offender.fixGL Nn, ρ x u ∈ Offender.fixGL Nn := by
    intro x u hu n hn
    have hnHl : n ∈ Hl := hNnle hn
    have hconj : ρ x⁻¹ * n * (ρ x⁻¹)⁻¹ ∈ Nn :=
      Subgroup.mem_subgroupOf.1 (hNnorm.conj_mem ⟨n, hnHl⟩ (Subgroup.mem_subgroupOf.2 hn)
        ⟨ρ x⁻¹, hmemHl x⁻¹⟩)
    have hc : (ρ x)⁻¹ * n * ρ x ∈ Nn := by
      have e : ρ x⁻¹ * n * (ρ x⁻¹)⁻¹ = (ρ x)⁻¹ * n * ρ x := by
        rw [map_inv, inv_inv]
      rwa [e] at hconj
    have hcu := hu _ hc
    calc n (ρ x u) = (n * ρ x) u := rfl
      _ = (ρ x * ((ρ x)⁻¹ * n * ρ x)) u := by group
      _ = ρ x (((ρ x)⁻¹ * n * ρ x) u) := rfl
      _ = ρ x u := by
        have : (((ρ x)⁻¹ * n * ρ x) u) = u := hcu
        rw [this]
  have hdisj := hd.V_compl
  have hmemWl : ∀ i, Il i ≤ Wl := fun i => by
    rw [hWeq]
    exact le_iSup Il i
  have : Module.Finite (ZMod 2) Wm := Module.Finite.of_finite
  refine ⟨r, fun i => modelSub θ (Il i), modelSub θ Wl, modelSub θ (Offender.fixGL Nn), P,
    hd.r_pow, ?_⟩
  exact
    { sylow := g.sylow
      nonnormal := g.nonnormal
      le_M := g.le_M
      M_lt := g.M_lt
      M_max := g.M_max
      J_not_le_centralizer := g.J_not_le_centralizer
      reduced := g.reduced
      W_le := modelSub_le θ _
      F_le := modelSub_le θ _
      W_normal := modelSub_normal θ hWl_inv
      F_normal := modelSub_normal θ hF_inv
      W_sup_F := by rw [← modelSub_sup, hWeq, hdisj.sup_eq_top, modelSub_top]
      W_inf_F := by rw [← modelSub_inf, hWeq, hdisj.inf_eq_bot, modelSub_bot]
      r_pos := hr
      I_le := fun i => (modelSub_le_iff θ).2 (hmemWl i)
      I_card := fun i => by
        rw [card_modelSub]
        have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(Il i))
        rw [Nat.card_zmod, hd.finrank_I i] at h
        simpa using h
      I_indep := iSupIndep_modelSub θ hd.I_indep
      I_sup := by rw [← modelSub_iSup, hWeq]
      Pm_two := hd.P_two
      Pm_trans := hd.P_trans
      image_le := fun x => by
        have hmem : Layer.resSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) Hl Wl hW
            ⟨ρ x, hmemHl x⟩ ∈ linWreath Wl Il P := by
          rw [← hrange]
          exact ⟨_, rfl⟩
        obtain ⟨σ, hσ, hiff⟩ := hmem
        refine ⟨σ, hσ, fun i => ?_⟩
        refine map_conj_modelSub θ (hmemWl i) (hmemWl (σ i)) hWl_inv x ?_
        intro w hw
        have := hiff i ⟨w, hw⟩
        simpa [Layer.resSub_apply] using this
      image_ge := fun g' σ hσ hg' => by
        set κ := modelSubEquiv (H := H) θ Wl with hκ
        let gl : ↥Wl ≃ₗ[ZMod 2] ↥Wl := Layer.binPsi κ g'
        have hgl_apply : ∀ u : ↥Wl, gl u =
            Multiplicative.toAdd (κ (g' (κ.symm (Multiplicative.ofAdd u)))) := fun u =>
          Layer.binPsi_apply κ g' u
        have hmem : gl ∈ linWreath Wl Il P := by
          refine ⟨σ, hσ, fun i u => ?_⟩
          set w' : ↥(modelSub (H := H) θ Wl) := κ.symm (Multiplicative.ofAdd u) with hw'
          have hu : (u : Wm) = Multiplicative.toAdd (θ ⟨w'.1, (mem_modelSub.1 w'.2).1⟩) := by
            have h1 := coe_modelSubEquiv θ Wl w'
            rw [hw', MulEquiv.apply_symm_apply] at h1
            simpa using h1
          have hgu : ((gl u : ↥Wl) : Wm) =
              Multiplicative.toAdd (θ ⟨(g' w').1, (mem_modelSub.1 (g' w').2).1⟩) := by
            rw [hgl_apply]
            exact coe_modelSubEquiv θ Wl (g' w')
          rw [hgu, hu]
          have h1 := hg' i w'
          constructor
          · intro h
            obtain ⟨_, h2⟩ := mem_modelSub.1
              (h1.1 (mem_modelSub.2 ⟨(mem_modelSub.1 (g' w').2).1, h⟩))
            exact h2
          · intro h
            obtain ⟨_, h2⟩ := mem_modelSub.1
              (h1.2 (mem_modelSub.2 ⟨(mem_modelSub.1 w'.2).1, h⟩))
            exact h2
        have hmem' : gl ∈ (Layer.resSub (MonoidHom.id (Wm ≃ₗ[ZMod 2] Wm)) Hl Wl hW).range := by
          rw [hrange]
          exact hmem
        obtain ⟨b, hb⟩ := hmem'
        obtain ⟨x, -, hx⟩ := b.2
        refine ⟨x, fun w => ?_⟩
        set u : ↥Wl := Multiplicative.toAdd (κ w) with hu
        have h1 : ((gl u : ↥Wl) : Wm) = ρ x (u : Wm) := by
          rw [← hb, Layer.resSub_apply]
          simp [hx]
        have h2 : gl u = Multiplicative.toAdd (κ (g' w)) := by
          rw [hgl_apply, hu]
          simp
        have e1 := coe_modelSubEquiv θ Wl (g' w)
        have e2 := coe_modelSubEquiv θ Wl w
        have h3 : Multiplicative.toAdd (θ ⟨(g' w).1, (mem_modelSub.1 (g' w).2).1⟩) =
            Multiplicative.toAdd (θ ⟨x * (w : H) * x⁻¹,
              modelRho_conj_mem x (mem_modelSub.1 w.2).1⟩) := by
          rw [← e1, ← h2, h1]
          show ρ x ((Multiplicative.toAdd (κ w) : ↥Wl) : Wm) = _
          rw [e2]
          exact modelRho_apply' θ x (mem_modelSub.1 w.2).1
        have h4 := θ.injective (Multiplicative.toAdd.injective h3)
        exact congrArg Subtype.val h4
      centralizes := fun x hx f hf => by
        have hpres : ∀ i, ∀ u : Wm, ρ x u ∈ Il i ↔ u ∈ Il i := fun i u =>
          rho_mem_iff_of_map_conj θ (hx i) u
        have hy : ∀ i, ∀ u ∈ Il i, ρ x u ∈ Il i := fun i u hu => (hpres i u).2 hu
        have hs : ∀ i, ∃ s ∈ S i, ∀ u ∈ Il i, s u = ρ x u := by
          intro i
          obtain ⟨hWi, hbij⟩ := hd.S_action i
          obtain ⟨s, hs⟩ := hbij.2 (restrictLin (Il i) (ρ x) (hpres i))
          refine ⟨s.1, s.2, fun u hu => ?_⟩
          have := congrArg (fun c : ↥(Il i) ≃ₗ[ZMod 2] ↥(Il i) => ((c ⟨u, hu⟩ : ↥(Il i)) : Wm)) hs
          simpa [Layer.resSub_apply, restrictLin_apply] using this
        obtain ⟨b, hbB, hb⟩ := exists_mem_iSup_of_agree S Il (ρ x) hy
          (fun i j hij s hs u hu => (Offender.mem_fixGL.1 (hd.S_fix_I i j hij hu)) s hs) hs
        have hbW : ∀ w ∈ Wl, b w = ρ x w := by
          intro w hw
          rw [hWeq] at hw
          exact Submodule.iSup_induction Il (motive := fun w => b w = ρ x w) hw
            (fun j u hu => hb j u hu) (by simp) (fun u v hu hv => by simp [map_add, hu, hv])
        have hbHl : b ∈ Hl := by
          have : (⨆ i, S i) ≤ Hl := iSup_le fun i => hd.S_le i
          exact this hbB
        have hone : b⁻¹ * ρ x = 1 := hd.faithful (b⁻¹ * ρ x)
          (Hl.mul_mem (Hl.inv_mem hbHl) (hmemHl x)) (by
            intro w hw
            show (b⁻¹ * ρ x) w = w
            have h1 : ρ x w = b w := (hbW w hw).symm
            rw [LinearEquiv.mul_apply, h1]
            simp)
        have hxb : b = ρ x := inv_mul_eq_one.1 hone
        obtain ⟨hfV, hfu⟩ := mem_modelSub.1 hf
        set u := Multiplicative.toAdd (θ ⟨f, hfV⟩) with hu
        have hfixb : b u = u := Subgroup.iSup_induction S (C := fun b => b u = u) hbB
          (fun i s hs => (Offender.mem_fixGL.1 (hd.S_fix_C i hfu)) s hs) rfl
          (fun b1 b2 h1 h2 => by rw [LinearEquiv.mul_apply, h2, h1])
        rw [hxb] at hfixb
        have h5 : Multiplicative.toAdd (θ ⟨x * f * x⁻¹, modelRho_conj_mem x hfV⟩) = u := by
          rw [← modelRho_apply' θ x hfV]
          exact hfixb
        have h6 := θ.injective (Multiplicative.toAdd.injective (h5.trans hu))
        have h7 : x * f * x⁻¹ = f := congrArg Subtype.val h6
        calc x * f = (x * f * x⁻¹) * x := by group
          _ = f * x := by rw [h7] }

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
