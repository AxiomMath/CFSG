module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4B
public import CFSG.ClassicalInvolution.Asc77.AscT8V2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open scoped commutatorElement

@[expose] def TightSecNoRootR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ¬ T3.DStarConnected Φ →
        ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
          IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
            (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
              (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
            (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
              e * e = x * x' → ∀ P ∈ Φ, P ≠ A → P ≠ B → ∀ v : X, IsUniqueInvolution P v →
                ∀ g ∈ A, ∀ k ∈ B, e ≠ v * g⁻¹ * k⁻¹)

section Rel

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem centralizes_of_comm_r_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) {y : G}
    (hyW : y ∈ W) (hry : ρ.r * y = y * ρ.r) : ∀ x ∈ ρ.R, x * y = y * x := by
  intro x hx
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW y hyW
  · have hw : ρ.r⁻¹ * x ∈ W := Q3CL.Thompson.D_inv_mul_mem c.hΩ c.hW ρ.hR ρ.hr hx ρ.hrW hxW
    have hwy : (ρ.r⁻¹ * x) * y = y * (ρ.r⁻¹ * x) := c.comm_W _ hw y hyW
    calc x * y = ρ.r * ((ρ.r⁻¹ * x) * y) := by group
      _ = ρ.r * (y * (ρ.r⁻¹ * x)) := by rw [hwy]
      _ = (ρ.r * y) * (ρ.r⁻¹ * x) := by group
      _ = (y * ρ.r) * (ρ.r⁻¹ * x) := by rw [hry]
      _ = y * x := by group

theorem exists_sq_root_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) {z : G}
    (hz : IsUniqueInvolution ρ.K z) : ∃ g : G, g ∈ ρ.K ⊓ W ∧ g ∈ ρ.R ∧ g * g = z := by
  obtain ⟨h1, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hzKW : z ∈ ρ.K ⊓ W :=
    Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz
  have hzU : z ∈ ρ.R ⊓ W := h1 ▸ hzKW
  have hU2 : IsPGroup 2 ↥(ρ.R ⊓ W) := (Thompson.isPGroup_of_mem_WSet c.hW).to_inf_right
  obtain ⟨g, hg, hgg⟩ := T8V.exists_mul_self_eq_of_cyclic (ρ.R ⊓ W) hU2 h4 hzU hz.sq hz.ne_one
  exact ⟨g, h1 ▸ hg, hg.1, hgg⟩

theorem centralizes_vg_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z v g : G} (hz : IsUniqueInvolution ρ.K z)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ.K ⊓ W) (hgg : g * g = z) :
    v * g⁻¹ ∈ W ∧ (∀ x ∈ ρ.R, x * (v * g⁻¹) = (v * g⁻¹) * x) ∧
      (v * g⁻¹) * (v * g⁻¹) = z := by
  have hvW : v ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW σ.hK σ.hR σ.hRK hv).2
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz).2
  have hyW : v * g⁻¹ ∈ W := W.mul_mem hvW (W.inv_mem hg.2)
  have h1 : ρ.r * v * ρ.r⁻¹ = z * v := c.conj_involution ρ σ hne hnot hz hv
  have h2 : ρ.r * g * ρ.r⁻¹ = g⁻¹ := c.conj_inv ρ hg
  have hzz : z * z = 1 := hz.sq
  have hgi : g⁻¹ = g * z := by
    have : g * (g * z) = 1 := by rw [← mul_assoc, hgg, hzz]
    exact inv_eq_of_mul_eq_one_right this
  have hgz : g * z = z * g := c.comm_W g hg.2 z hzW
  have hvg : v * g = g * v := c.comm_W v hvW g hg.2
  have hvz : v * z = z * v := c.comm_W v hvW z hzW
  have hvv : v * v = 1 := hv.sq
  have hrg : ρ.r * g⁻¹ * ρ.r⁻¹ = g := by
    have : ρ.r * g⁻¹ * ρ.r⁻¹ = (ρ.r * g * ρ.r⁻¹)⁻¹ := by group
    rw [this, h2, inv_inv]
  have hcomm : ρ.r * (v * g⁻¹) = (v * g⁻¹) * ρ.r := by
    have : ρ.r * (v * g⁻¹) * ρ.r⁻¹ = v * g⁻¹ := by
      calc ρ.r * (v * g⁻¹) * ρ.r⁻¹ = (ρ.r * v * ρ.r⁻¹) * (ρ.r * g⁻¹ * ρ.r⁻¹) := by group
        _ = (z * v) * g := by rw [h1, hrg]
        _ = v * (z * g) := by rw [← hvz, mul_assoc]
        _ = v * g⁻¹ := by rw [hgi, hgz]
    calc ρ.r * (v * g⁻¹) = (ρ.r * (v * g⁻¹) * ρ.r⁻¹) * ρ.r := by group
      _ = (v * g⁻¹) * ρ.r := by rw [this]
  refine ⟨hyW, centralizes_of_comm_r_gen c ρ hyW hcomm, ?_⟩
  calc (v * g⁻¹) * (v * g⁻¹) = (v * v) * (g⁻¹ * g⁻¹) := by
        have : g⁻¹ * v = v * g⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hvg]; group
        calc (v * g⁻¹) * (v * g⁻¹) = v * (g⁻¹ * v) * g⁻¹ := by group
          _ = v * (v * g⁻¹) * g⁻¹ := by rw [this]
          _ = (v * v) * (g⁻¹ * g⁻¹) := by group
    _ = z := by
      rw [hvv, one_mul]
      have : g⁻¹ * g⁻¹ = (g * g)⁻¹ := by group
      rw [this, hgg]
      exact inv_eq_of_mul_eq_one_right hzz

theorem centralizes_mem_inf_W_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W)
    (hnbr : σ.K ∈ omegaNbr Ω ρ.K) {g : G} (hg : g ∈ σ.K ⊓ W) : ∀ x ∈ ρ.R, x * g = g * x :=
  centralizes_of_comm_r_gen c ρ hg.2 (c.centralizes ρ σ hnbr hg)

theorem centralizes_inv_of_nbr_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W)
    (hnbr : σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ∀ x ∈ ρ.R, x * v = v * x := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mp (rep_le_centralizer_gen c ρ σ (Or.inr hnbr) hv hx)

theorem exists_y_left_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ v g : G}
    (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne : ρ₁.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ₁.K)
    (hσ₂ : σ.K ∈ omegaNbr Ω ρ₂.K) (hz : IsUniqueInvolution ρ₁.K z₁)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁) :
    ∃ y ∈ W, y * y = z₁ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧ (∀ x ∈ ρ₂.R, x * y = y * x) := by
  obtain ⟨hyW, hy1, hyy⟩ := centralizes_vg_gen c ρ₁ σ hne hnot hz hv hg hgg
  refine ⟨v * g⁻¹, hyW, hyy, hy1, fun x hx => ?_⟩
  have h1 : Commute x v := centralizes_inv_of_nbr_gen c ρ₂ σ hσ₂ hv x hx
  have h2 : Commute x g := centralizes_mem_inf_W_gen c ρ₂ ρ₁ hn21 hg x hx
  exact h1.mul_right h2.inv_right

theorem exists_y_both_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ z₂ v g h : G}
    (hn12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne1 : ρ₁.K ≠ σ.K)
    (hne2 : ρ₂.K ≠ σ.K) (hnot1 : σ.K ∉ omegaNbr Ω ρ₁.K) (hnot2 : σ.K ∉ omegaNbr Ω ρ₂.K)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁)
    (hh : h ∈ ρ₂.K ⊓ W) (hhh : h * h = z₂) :
    ∃ y ∈ W, y = v * g⁻¹ * h⁻¹ ∧ y * y = z₁ * z₂ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧
      (∀ x ∈ ρ₂.R, x * y = y * x) := by
  obtain ⟨hyW1, hy1, -⟩ := centralizes_vg_gen c ρ₁ σ hne1 hnot1 hz₁ hv hg hgg
  obtain ⟨-, hy2, -⟩ := centralizes_vg_gen c ρ₂ σ hne2 hnot2 hz₂ hv hh hhh
  have hvW : v ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW σ.hK σ.hR σ.hRK hv).2
  have hgh : Commute g h := c.comm_W g hg.2 h hh.2
  have hvg : Commute v g := c.comm_W v hvW g hg.2
  have hvh : Commute v h := c.comm_W v hvW h hh.2
  have hyW : v * g⁻¹ * h⁻¹ ∈ W := W.mul_mem hyW1 (W.inv_mem hh.2)
  refine ⟨v * g⁻¹ * h⁻¹, hyW, rfl, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [T8V.mul_inv_inv_sq hvg hvh hgh, hv.sq, hgg, hhh, one_mul]
    have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
    have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂.sq
    rw [i1, i2]
  · have h1 : Commute x (v * g⁻¹) := hy1 x hx
    have h2 : Commute x h := centralizes_mem_inf_W_gen c ρ₁ ρ₂ hn12 hh x hx
    exact h1.mul_right h2.inv_right
  · have h1 : Commute x (v * h⁻¹) := hy2 x hx
    have h2 : Commute x g := centralizes_mem_inf_W_gen c ρ₂ ρ₁ hn21 hg x hx
    have e : v * g⁻¹ * h⁻¹ = (v * h⁻¹) * g⁻¹ := by
      rw [mul_assoc, mul_assoc, hgh.inv_inv.eq]
    rw [e]
    exact h1.mul_right h2.inv_right

end Rel

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem comm_mk_mem_secImg {M : Subgroup G} (hM : XMem Ω x M) (e : ↥(layerY Ω x))
    (hy : (e : G) ∈ Subgroup.centralizer ({x} : Set G))
    (hyN : (e : G) ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅(e : G), k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ secImg Ω x M,
      ⁅(QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) e : SecQuot Ω x), kb⁆ ∈
        oddCoreOf (secImg Ω x M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hkL : (k' : G) ∈ coreAt x M := Subgroup.mem_subgroupOf.mp hk'
  have h3 := mk_mem_oddCoreOf_secImg hM ⁅e, k'⁆ (by
    have : ((⁅e, k'⁆ : ↥(layerY Ω x)) : G) = ⁅(e : G), (k' : G)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact comm_mem_oddCoreOf_coreAt hy hyN hcomm hkL)
  rwa [map_commutatorElement] at h3

end Sec

theorem conj_eq_of_central_mul_gen {X : Type} [Group X] {x x' : X} (hx : x * x = 1)
    (hc : x * x' ∈ Subgroup.center X) : MulAut.conj x' = MulAut.conj x := by
  ext g
  rw [MulAut.conj_apply, MulAut.conj_apply]
  have hc' := Subgroup.mem_center_iff.mp hc g
  have hx' : x' = x * (x * x') := by rw [← mul_assoc, hx, one_mul]
  rw [hx']
  calc x * (x * x') * g * (x * (x * x'))⁻¹ = x * ((x * x') * g) * (x * x')⁻¹ * x⁻¹ := by group
    _ = x * (g * (x * x')) * (x * x')⁻¹ * x⁻¹ := by rw [← hc']
    _ = x * g * x⁻¹ := by group

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.z_mem_W (hs : TightStd8R r n Rd Sd z J S R T W t) : z ∈ W :=
  (Q3CL.Thompson.uniqueInvolution_mem_W hs.hyp hs.hW.1 hs.mem
    (Q3CL.T8R.Loc.mem_DSet_of_le_sylow hs.toStd8Core hs.hR.1 hs.hR.2.2)
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.mem hs.hR.1 hs.hR.2.1) hs.hz).2

theorem TightStd8R.t_mem_W (hs : TightStd8R r n Rd Sd z J S R T W t) : t ∈ W :=
  (Q3CL.Thompson.uniqueInvolution_mem_W hs.hyp hs.hW.1 hs.hJ.1
    (Q3CL.T8R.Loc.mem_DSet_of_le_sylow hs.toStd8Core hs.hT.1 hs.hT.2.2)
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1) hs.ht).2

theorem TightStd8R.y_data (hs : TightStd8R r n Rd Sd z J S R T W t) {y : Y} (hyW : y ∈ W)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) :
    y ∈ Subgroup.centralizer ({z * t} : Set Y) ∧
      y ∈ Subgroup.normalizer (tightCore Rd : Set Y) ∧ y ∈ Subgroup.normalizer (J : Set Y) ∧
      (∀ k ∈ tightCore Rd, ⁅y, k⁆ ∈ oddCoreOf (tightCore Rd)) ∧
      (∀ k ∈ J, ⁅y, k⁆ ∈ oddCoreOf J) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have c := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  have hyz : y * z = z * y := c.comm_W y hyW z hs.z_mem_W
  have hyt : y * t = t * y := c.comm_W y hyW t hs.t_mem_W
  have hyN1 : y ∈ Subgroup.normalizer (tightCore Rd : Set Y) :=
    hs.large.datum.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have hyN2 : y ∈ Subgroup.normalizer (J : Set Y) :=
    h.tight J hs.hJ.1 t hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
  refine ⟨?_, hyN1, hyN2, fun k hk => ?_, fun k hk => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (z * t) = (y * z) * t := by group
      _ = (z * y) * t := by rw [hyz]
      _ = z * (y * t) := by group
      _ = z * (t * y) := by rw [hyt]
      _ = (z * t) * y := by group
  · exact comm_mem_oddCoreOf_of_twoGroup (h.twoGroup _ hs.mem)
      (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hs.hR.1 hs.hR.2.1) hyN1
      (fun x hx => (hyR x hx).symm) hk
  · exact comm_mem_oddCoreOf_of_twoGroup (h.twoGroup J hs.hJ.1)
      (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1) hyN2
      (fun x hx => (hyT x hx).symm) hk

theorem TightStd8R.secImg_J_mem_omegaNbr (hs : TightStd8R r n Rd Sd z J S R T W t) :
    secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
        (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  have hne' := secImg_ne h hs.xMem_K hs.xMem_J hs.hz hs.ht hzt
    (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  exact secImg_mem_omegaNbr hs.xMem_K hs.xMem_J
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1)
    hs.T_le_centralizer_mul (hs.T_le_centralizer_z.trans hs.large.datum.le_normalizer_core) hne'

theorem TightStd8R.mk_mul_mk_mem_center (_hs : TightStd8R r n Rd Sd z J S R T W t)
    (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (htY : t ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) :
    (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨t, htY⟩ :
      SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ∈
      Subgroup.center (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) := by
  have := mk_mem_center_secQuot (Ω := CoreAssembly.conjClass (tightCore Rd)) (x := z * t)
    ((layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)).mul_mem hzY htY) rfl
  rw [← map_mul]
  exact this

theorem TightStd8R.no_root_sq (hNR : TightSecNoRootR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    {y u : Y} (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (hu : u ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) (hyW : y ∈ W)
    (hyy : y * y = u) (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x)
    (hconj : MulAut.conj (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨u, hu⟩ :
          SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) =
      MulAut.conj (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩)) : False := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hcl := hs.hyp.conjInvariant
  have hXK := hs.xMem_K
  have hXJ := hs.xMem_J
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ := hs.y_data hyW hyR hyT
  have htY : t ∈ layerY Ω (z * t) := mem_layerY_of_isUniqueInvolution h hXJ hs.ht
  have hNR' := hNR (SecQuot Ω (z * t)) hs.natCard_secQuot_lt (secFam Ω (z * t)) h.secFam
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h) hdisc _ (secImg_mem hXK) _
    hs.secImg_J_mem_omegaNbr _ _ (isUniqueInvolution_secImg h hXK hs.hz)
    (isUniqueInvolution_secImg h hXJ hs.ht) (hs.mk_mul_mk_mem_center hzY htY)
  refine hNR'.1 (secAct hcl hycen) (secAct_mul_inv_mem hcl hycen hXK hyK hcK)
    (secAct_mul_inv_mem hcl hycen hXJ hyJ hcJ) ?_
  show s26Act (layerY Ω (z * t)) ⟨y, mem_normalizer_layerY hcl hycen⟩ *
    s26Act (layerY Ω (z * t)) ⟨y, mem_normalizer_layerY hcl hycen⟩ = _
  rw [← map_mul]
  have e : (⟨y, mem_normalizer_layerY hcl hycen⟩ * ⟨y, mem_normalizer_layerY hcl hycen⟩ :
      ↥(Subgroup.normalizer ((layerY Ω (z * t) : Subgroup Y) : Set Y))) =
      ⟨u, Subgroup.le_normalizer hu⟩ := Subtype.ext hyy
  rw [e, s26Act_eq_conj (layerY Ω (z * t)) ⟨u, hu⟩]
  exact hconj

theorem TightStd8R.no_root_z (hNR : TightSecNoRootR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    {y : Y} (hyW : y ∈ W) (hyy : y * y = z) (hyR : ∀ x ∈ R, x * y = y * x)
    (hyT : ∀ x ∈ T, x * y = y * x) : False := by
  have hzY := mem_layerY_of_isUniqueInvolution (TightLargeHypR.typeRFam hs.large) hs.xMem_K hs.hz
  exact hs.no_root_sq hNR hdisc hzY hzY hyW hyy hyR hyT rfl

theorem TightStd8R.no_root_t (hNR : TightSecNoRootR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    {y : Y} (hyW : y ∈ W) (hyy : y * y = t) (hyR : ∀ x ∈ R, x * y = y * x)
    (hyT : ∀ x ∈ T, x * y = y * x) : False := by
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  refine hs.no_root_sq hNR hdisc hzY htY hyW hyy hyR hyT
    (conj_eq_of_central_mul_gen ?_ (hs.mk_mul_mk_mem_center hzY htY))
  rw [← map_mul]
  have : (⟨z, hzY⟩ * ⟨z, hzY⟩ :
      ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) = 1 := Subtype.ext hs.hz.sq
  rw [this, map_one]

theorem TightStd8R.no_root_zt (hNR : TightSecNoRootR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (ρ : Rep (CoreAssembly.conjClass (tightCore Rd)) W)
    (hX : XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) ρ.K) (hρK : ρ.K ≠ tightCore Rd)
    (hρJ : ρ.K ≠ J) {v g k y : Y} (hv : IsUniqueInvolution ρ.K v) (hgR : g ∈ R) (hkT : k ∈ T)
    (hyW : y ∈ W) (hy : y = v * g⁻¹ * k⁻¹) (hyy : y * y = z * t)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False := by
  revert ρ
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  intro ρ hX hρK hρJ hv
  have h := TightLargeHypR.typeRFam hs.large
  have c := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  have hXK := hs.xMem_K
  have hXJ := hs.xMem_J
  have hzY := mem_layerY_of_isUniqueInvolution h hXK hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hXJ hs.ht
  have hvY := mem_layerY_of_isUniqueInvolution h hX hv
  have hRc : R ≤ coreAt (z * t) (tightCore Rd) :=
    le_coreAt (z * t) (S.isPGroup'.to_le hs.hR.2.2) hs.hR.2.1
      (Q3CL.T8R.Loc.le_centralizer_mul hs.toStd8Core)
  have hTc : T ≤ coreAt (z * t) J :=
    le_coreAt (z * t) (S.isPGroup'.to_le hs.hT.2.2) hs.hT.2.1 hs.T_le_centralizer_mul
  have hgY : g ∈ layerY Ω (z * t) := coreAt_le_layerY hXK (hRc hgR)
  have hkY : k ∈ layerY Ω (z * t) := coreAt_le_layerY hXJ (hTc hkT)
  have hyY : y ∈ layerY Ω (z * t) := by
    rw [hy]
    exact (layerY Ω (z * t)).mul_mem ((layerY Ω (z * t)).mul_mem hvY
      ((layerY Ω (z * t)).inv_mem hgY)) ((layerY Ω (z * t)).inv_mem hkY)
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ := hs.y_data hyW hyR hyT
  have hvW : v ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hv).2
  have hPK : secImg Ω (z * t) ρ.K ≠ secImg Ω (z * t) (tightCore Rd) :=
    secImg_ne h hX hXK hv hs.hz (c.comm_W v hvW z hs.z_mem_W)
      fun he => hρK (h.noTwins _ hs.mem ρ.K ⟨ρ.hK, z, hs.hz, he ▸ hv⟩)
  have hPJ : secImg Ω (z * t) ρ.K ≠ secImg Ω (z * t) J :=
    secImg_ne h hX hXJ hv hs.ht (c.comm_W v hvW t hs.t_mem_W)
      fun he => hρJ (h.noTwins _ hs.hJ.1 ρ.K ⟨ρ.hK, t, hs.ht, he ▸ hv⟩)
  have hNR' := hNR (SecQuot Ω (z * t)) hs.natCard_secQuot_lt (secFam Ω (z * t)) h.secFam
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h) hdisc _ (secImg_mem hXK) _
    hs.secImg_J_mem_omegaNbr _ _ (isUniqueInvolution_secImg h hXK hs.hz)
    (isUniqueInvolution_secImg h hXJ hs.ht) (hs.mk_mul_mk_mem_center hzY htY)
  refine hNR'.2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨y, hyY⟩)
    (comm_mk_mem_secImg hXK ⟨y, hyY⟩ hycen hyK hcK)
    (comm_mk_mem_secImg hXJ ⟨y, hyY⟩ hycen hyJ hcJ) ?_ _ (secImg_mem hX) hPK hPJ
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨v, hvY⟩)
    (isUniqueInvolution_secImg h hX hv)
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨g, hgY⟩)
    (Subgroup.mem_map.mpr ⟨⟨g, hgY⟩, Subgroup.mem_subgroupOf.mpr (hRc hgR), rfl⟩)
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨k, hkY⟩)
    (Subgroup.mem_map.mpr ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr (hTc hkT), rfl⟩) ?_
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyy
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hy

theorem TightStd8R.xMem_rep (hs : TightStd8R r n Rd Sd z J S R T W t)
    (ρ : Rep (CoreAssembly.conjClass (tightCore Rd)) W) (hK : ρ.K ≠ tightCore Rd) (hJ : ρ.K ≠ J)
    (hnK : ρ.K ∉ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hnJ : ρ.K ∉ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J) {v : Y}
    (hv : IsUniqueInvolution ρ.K v) :
    XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) ρ.K ∧
      ρ.R ≤ Subgroup.centralizer ({z * t} : Set Y) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have c := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  have hnK' : tightCore Rd ∉ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) ρ.K := fun h' =>
    hnK (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ ρ.hK hs.mem h')
  have hnJ' : J ∉ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) ρ.K := fun h' =>
    hnJ (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ ρ.hK hs.hJ.1 h')
  have h1 : ρ.r * z * ρ.r⁻¹ = v * z :=
    c.conj_involution ρ (Q3CL.T8R.Loc.stdRepK hs.toStd8Core) hK hnK' hv hs.hz
  have h2 : ρ.r * t * ρ.r⁻¹ = v * t :=
    c.conj_involution ρ (Q3CL.T8R.Loc.stdRepJ hs.toStd8Core) hJ hnJ' hv hs.ht
  have hvW : v ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hv).2
  have hzW := hs.z_mem_W
  have htW := hs.t_mem_W
  have hvz : v * z = z * v := c.comm_W v hvW z hzW
  have hconj : ρ.r * (z * t) * ρ.r⁻¹ = z * t := by
    calc ρ.r * (z * t) * ρ.r⁻¹ = (ρ.r * z * ρ.r⁻¹) * (ρ.r * t * ρ.r⁻¹) := by group
      _ = (v * z) * (v * t) := by rw [h1, h2]
      _ = v * (z * v) * t := by group
      _ = v * (v * z) * t := by rw [hvz]
      _ = (v * v) * (z * t) := by group
      _ = z * t := by rw [hv.sq, one_mul]
  have hra : ρ.r * (z * t) = (z * t) * ρ.r := by
    calc ρ.r * (z * t) = (ρ.r * (z * t) * ρ.r⁻¹) * ρ.r := by group
      _ = (z * t) * ρ.r := by rw [hconj]
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcR : ∀ x ∈ ρ.R, x * (z * t) = (z * t) * x := centralizes_of_comm_r_gen c ρ haW hra
  have hav : (z * t) * v = v * (z * t) := c.comm_W _ haW v hvW
  refine ⟨⟨ρ.hK, ?_, ρ.R, ρ.hRK, fun x hx => hcR x hx⟩, fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcR x hx)⟩
  exact h.tight ρ.K ρ.hK v hv (Subgroup.mem_centralizer_singleton_iff.mpr hav)

theorem TightStd8R.dstarConnected_secFam_of_third (hTri : TightSecTriangleR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (τ : Rep (CoreAssembly.conjClass (tightCore Rd)) W) (hτK : τ.K ≠ tightCore Rd)
    (hτJ : τ.K ≠ J) (h1 : τ.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (h2 : τ.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J) :
    T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)) := by
  revert τ
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  intro τ hτK hτJ h1 h2
  classical
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hc := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  obtain ⟨z₂, hz₂⟩ := Sec6Gen.exists_uniqueInvolution hΩ τ.hK
  have hKJ : tightCore Rd ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.mem hs.hJ.1 hs.hJ
  have h1' : tightCore Rd ∈ omegaNbr Ω τ.K :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.mem τ.hK h1
  have h2' : J ∈ omegaNbr Ω τ.K := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.hJ.1 τ.hK h2
  let ρ : Fin 3 → Rep Ω W :=
    ![Q3CL.T8R.Loc.stdRepK hs.toStd8Core, Q3CL.T8R.Loc.stdRepJ hs.toStd8Core, τ]
  let zz : Fin 3 → Y := ![z, t, z₂]
  have hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i) := by
    intro i
    fin_cases i
    · exact hs.hz
    · exact hs.ht
    · exact hz₂
  have hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hs.hJ
    · exact h1
    · exact hKJ
    · exact absurd rfl hij
    · exact h2
    · exact h1'
    · exact h2'
    · exact absurd rfl hij
  have hrel : ∀ i j, (ρ j).K = (ρ i).K ∨ (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Or.inl rfl
    · exact Or.inr (hnbr i j hij)
  have hKE : ∀ i, (ρ i).K = ![tightCore Rd, J, τ.K] i := by
    intro i
    fin_cases i <;> rfl
  have hRE : ∀ i, (ρ i).R = ![R, T, τ.R] i := by
    intro i
    fin_cases i <;> rfl
  have hzE : ∀ i, zz i = ![z, t, z₂] i := by
    intro i
    fin_cases i <;> rfl
  have hF : TriFrame Ω ![tightCore Rd, J, τ.K] ![z, t, z₂] ![R, T, τ.R] :=
    { mem := fun i => by
        rw [← hKE i]
        exact (ρ i).hK
      inv := fun i => by
        rw [← hKE i, ← hzE i]
        exact hzz i
      nbr := fun i j hij => by
        rw [← hKE i, ← hKE j]
        exact hnbr i j hij
      syl := fun i => by
        rw [← hKE i, ← hRE i]
        exact (ρ i).hRK
      cent := fun i j => by
        rw [← hRE i, ← hzE j]
        exact rep_le_centralizer_gen hc (ρ i) (ρ j) (hrel i j) (hzz j) }
  have hX : ∀ i, XMem Ω (z * t) (![tightCore Rd, J, τ.K] i) :=
    xMem_of_triFrame hΩ h.noTwins hF
  have hne : ∀ i j, i ≠ j → secImg Ω (z * t) (![tightCore Rd, J, τ.K] i) ≠
      secImg Ω (z * t) (![tightCore Rd, J, τ.K] j) := fun i j hij =>
    secImg_ne h (hX i) (hX j) (hF.inv i) (hF.inv j) (triFrame_comm_gen hF hΩ i j)
      (hF.x_ne h.noTwins hij)
  have hadj : ∀ i j, i ≠ j → secImg Ω (z * t) (![tightCore Rd, J, τ.K] j) ∈
      omegaNbr (secFam Ω (z * t)) (secImg Ω (z * t) (![tightCore Rd, J, τ.K] i)) := by
    intro i j hij
    have hPN : (![R, T, τ.R] j) ≤ Subgroup.normalizer ((![tightCore Rd, J, τ.K] i :
        Subgroup Y) : Set Y) :=
      (hF.cent j i).trans (h.tight _ (hF.mem i) _ (hF.inv i))
    exact secImg_mem_omegaNbr (hX i) (hX j) (hF.syl j) (triFrame_le_centralizer_mul hF j) hPN
      (hne i j hij)
  refine hTri (SecQuot Ω (z * t)) hs.natCard_secQuot_lt (secFam Ω (z * t)) h.secFam
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h)
    (fun i => secImg Ω (z * t) (![tightCore Rd, J, τ.K] i)) (fun i => secImg_mem (hX i)) ?_ hadj
  intro i j hij
  by_contra hne'
  exact hne i j hne' hij

theorem TightStd8R.rep_K_eq (hNR : TightSecNoRootR r n) (hTri : TightSecTriangleR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (ρ : Rep (CoreAssembly.conjClass (tightCore Rd)) W) : ρ.K = tightCore Rd ∨ ρ.K = J := by
  revert ρ
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  intro ρ
  by_contra hcon
  push Not at hcon
  obtain ⟨hρK, hρJ⟩ := hcon
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have c := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρ.hK
  have hKJ : tightCore Rd ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.mem hs.hJ.1 hs.hJ
  set ρK := Q3CL.T8R.Loc.stdRepK hs.toStd8Core with hρKdef
  set ρJ := Q3CL.T8R.Loc.stdRepJ hs.toStd8Core with hρJdef
  by_cases h1 : ρ.K ∈ omegaNbr Ω (tightCore Rd) <;> by_cases h2 : ρ.K ∈ omegaNbr Ω J
  · exact hdisc (hs.dstarConnected_secFam_of_third hTri ρ hρK hρJ h1 h2)
  · obtain ⟨g, hg, -, hgg⟩ := exists_sq_root_gen c ρJ hs.ht
    obtain ⟨y, hyW, hyy, hyJ, hyK⟩ :=
      exists_y_left_gen c ρJ ρK ρ hs.hJ (Ne.symm hρJ) h2 h1 hs.ht hv hg hgg
    exact hs.no_root_t hNR hdisc hyW hyy hyK hyJ
  · obtain ⟨g, hg, -, hgg⟩ := exists_sq_root_gen c ρK hs.hz
    obtain ⟨y, hyW, hyy, hyK, hyJ⟩ :=
      exists_y_left_gen c ρK ρJ ρ hKJ (Ne.symm hρK) h1 h2 hs.hz hv hg hgg
    exact hs.no_root_z hNR hdisc hyW hyy hyK hyJ
  · obtain ⟨hX, -⟩ := hs.xMem_rep ρ hρK hρJ h1 h2 hv
    obtain ⟨g, hg, hgR, hgg⟩ := exists_sq_root_gen c ρK hs.hz
    obtain ⟨k, hk, hkT, hkk⟩ := exists_sq_root_gen c ρJ hs.ht
    obtain ⟨y, hyW, hy, hyy, hyK, hyJ⟩ := exists_y_both_gen c ρK ρJ ρ hs.hJ hKJ (Ne.symm hρK)
      (Ne.symm hρJ) h1 h2 hs.hz hs.ht hv hg hgg hk hkk
    exact hs.no_root_zt hNR hdisc ρ hX hρK hρJ hv hgR hkT hyW hy hyy hyK hyJ

theorem tightC27_YsmallR_of (hNR : TightSecNoRootR r n) (hTri : TightSecTriangleR r n) :
    TightC27_YsmallR r n := by
  intro Y _ _ Rd Sd z J S R T W t hs _hD _hE4 hnab hdisc
  exfalso
  obtain ⟨d, hd, e, he, hde⟩ := exists_noncomm_of_not_abelian hnab
  have c := Q3CL.T8.ctxOf hs.partIHypG hs.hW.1
  have hKJ : tightCore Rd ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.hyp hs.mem hs.hJ.1 hs.hJ
  have key : ∀ ρ σ : Rep (CoreAssembly.conjClass (tightCore Rd)) W,
      (ρ.K = tightCore Rd ∨ ρ.K = J) → (σ.K = tightCore Rd ∨ σ.K = J) →
        T8.repElt ρ * T8.repElt σ = T8.repElt σ * T8.repElt ρ := by
    intro ρ σ hρ hσ
    by_cases h : ρ.K = σ.K
    · rw [(repElt_eq_iff_gen c ρ σ).mpr h]
    · refine (repElt_commute_iff_gen c ρ σ h).mpr ?_
      rcases hρ with h1 | h1 <;> rcases hσ with h2 | h2
      · exact absurd (h1.trans h2.symm) h
      · rw [h1, h2]
        exact hs.hJ
      · rw [h1, h2]
        exact hKJ
      · exact absurd (h1.trans h2.symm) h
  obtain ⟨ρ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := T8.exists_rep_of_mem_muDelta he
  exact hde (key ρ σ (hs.rep_K_eq hNR hTri hdisc ρ) (hs.rep_K_eq hNR hTri hdisc σ))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
