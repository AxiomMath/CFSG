module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Num
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Facts

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G] [Finite G] {t : G} {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzDat t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_digits {x : ℕ} (hx : x < 512) :
    (fzEOf x).1 = fzElt (x % 64) ∧
    (fzEOf x).2.1.val = x / 64 % 2 ∧
    (fzEOf x).2.2.1.val = x / 128 % 2 ∧
    (fzEOf x).2.2.2.val = x / 256 % 2 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [fzEOf]
    rw [ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))]
  · simp only [fzEOf]
    rw [ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))]
  · simp only [fzEOf]
    rw [ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))]

private theorem fzrAux_mod64 (y : FzElt) : fzEIdx y % 64 = fzIdx y.1 := by
  unfold fzEIdx
  have h := fzIdx_lt y.1
  omega

private theorem fzrAux_div64 (y : FzElt) :
    fzEIdx y / 64 = y.2.1.val + 2 * y.2.2.1.val + 4 * y.2.2.2.val := by
  unfold fzEIdx
  have h0 := fzIdx_lt y.1
  have h1 := ZMod.val_lt y.2.1
  have h2 := ZMod.val_lt y.2.2.1
  have h3 := ZMod.val_lt y.2.2.2
  omega

private theorem fzrAux_idx_mod16 (x : FzUT) : fzIdx x % 16 = 0 ↔ FzInZ x := by
  revert x
  simp only [FzInZ]
  decide +kernel

private theorem fzrAux_base_le_wreath :
    (baseGrp x₁ x₂ : Subgroup G) ≤ wreathGrp x₁ x₂ lam := by
  unfold baseGrp wreathGrp
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  tauto

private theorem fzrAux_conj_triple {G : Type} [Group G] {rho t tau : G} (a : G) (i j : ℕ)
    (ht : rho * t ^ i * rho⁻¹ = t ^ i) (htau : rho * tau ^ j * rho⁻¹ = tau ^ j) :
    rho * (a * t ^ i * tau ^ j) * rho⁻¹ = (rho * a * rho⁻¹) * t ^ i * tau ^ j := by
  calc rho * (a * t ^ i * tau ^ j) * rho⁻¹
      = (rho * a * rho⁻¹) * (rho * t ^ i * rho⁻¹) * (rho * tau ^ j * rho⁻¹) := by group
    _ = (rho * a * rho⁻¹) * t ^ i * tau ^ j := by rw [ht, htau]

private theorem fzrAux_fzEOf_rho {x : ℕ} (hx : x < 256) :
    fzEOf ((fzrCPar D).rhoMap x) = (fzRho0 (fzEOf x).1, (fzEOf x).2) := by
  have hx512 : x < 512 := by omega
  obtain ⟨h0, h1, h2, h3⟩ := fzrAux_digits hx512
  have hidx : (fzrCPar D).rhoMap x = fzEIdx (fzRho0 (fzEOf x).1, (fzEOf x).2) := by
    have hx64 : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have hval : x / 64 = x / 64 % 2 + 2 * (x / 128 % 2) + 4 * (x / 256 % 2) := by omega
    have hL : rho0 (x % 64) = fzIdx (fzRho0 (fzElt (x % 64))) :=
      calc rho0 (x % 64) = rho0 (fzIdx (fzElt (x % 64))) := by rw [fzIdx_fzElt hx64]
        _ = fzIdx (fzRho0 (fzElt (x % 64))) := fzIdx_rho0 _
    simp only [fzrCPar, parOf]
    rw [h0, hL]
    simp only [fzEIdx]
    rw [h1, h2, h3, ← hval]
  calc fzEOf ((fzrCPar D).rhoMap x)
      = fzEOf (fzEIdx (fzRho0 (fzEOf x).1, (fzEOf x).2)) := by rw [hidx]
    _ = (fzRho0 (fzEOf x).1, (fzEOf x).2) := fzEOf_fzEIdx _

theorem fzrCMu_rho {x : ℕ} (hx : x < 256) :
    fzrCMu D ((fzrCPar D).rhoMap x) = rho * fzrCMu D x * rho⁻¹ := by
  have hx512 : x < 512 := by omega
  obtain ⟨-, -, -, h3⟩ := fzrAux_digits hx512
  have hlam : (fzEOf x).2.2.2.val = 0 := by rw [h3]; omega
  have hEOf := fzrAux_fzEOf_rho D hx
  have hcR : ((D.φ.symm (fzRho0 (fzEOf x).1) : ↥(fzP t x₁ x₂ rho)) : G) =
      rho * ((D.φ.symm (fzEOf x).1 : ↥(fzP t x₁ x₂ rho)) : G) * rho⁻¹ := by
    rw [← D.cR_apply]
    exact D.cR_coe _
  have ht : ∀ i, rho * t ^ i * rho⁻¹ = t ^ i := by
    intro i
    rw [← conj_pow, D.str.rho_t]
  have htau : ∀ i, rho * tau ^ i * rho⁻¹ = tau ^ i := by
    intro i
    have h1 : rho * tau * rho⁻¹ = tau := by
      calc rho * tau * rho⁻¹ = (tau * rho) * rho⁻¹ := by rw [← D.str.tau_rho]
        _ = tau := by group
    rw [← conj_pow, h1]
  rw [show fzrCMu D ((fzrCPar D).rhoMap x)
        = D.mu (fzEOf ((fzrCPar D).rhoMap x)) from rfl, hEOf]
  rw [show fzrCMu D x = D.mu (fzEOf x) from rfl]
  unfold Fz319Data.mu
  rw [hlam, hcR]
  simp only [pow_zero, mul_one]
  exact (fzrAux_conj_triple ((D.φ.symm (fzEOf x).1 : ↥(fzP t x₁ x₂ rho)) : G)
    (fzEOf x).2.1.val (fzEOf x).2.2.1.val (ht _) (htau _)).symm

theorem fzrCMu_inW {x : ℕ} (h : (fzrCPar D).inW x = true) : fzrCMu D x ∈ ctxW t x₁ x₂ := by
  simp only [fzrCPar, parOf, Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨hap, hlt⟩ := h
  have hx : x < 512 := by omega
  set y : FzElt := fzEOf x with hy
  have hIdx : fzEIdx y = x := by rw [hy, fzEIdx_fzEOf hx]
  have hW : fzInW D.cT y := by
    rw [← fzEIdx_W D.cT y, hIdx]
    simp [hap, hlt]
  obtain ⟨hfix, hv1, hv2⟩ := hW
  have hμ : D.mu y = ((D.φ.symm y.1 : ↥(fzP t x₁ x₂ rho)) : G) * t ^ y.2.1.val := by
    unfold Fz319Data.mu
    rw [hv1, hv2]
    simp
  have hbase : ((D.φ.symm y.1 : ↥(fzP t x₁ x₂ rho)) : G) ∈
      (baseGrp x₁ x₂ : Subgroup G) := by
    rw [D.E_iff]
    simpa using hfix
  rw [show fzrCMu D x = D.mu y from rfl, hμ]
  exact (ctxW t x₁ x₂).mul_mem (D.str.EW hbase) ((ctxW t x₁ x₂).pow_mem D.str.t_mem _)

theorem fzrCMu_inTL {x : ℕ} (hx : x < 512) (h : (fzrCPar D).inTL x = true) :
    fzrCMu D x ∈ wreathGrp x₁ x₂ lam := by
  simp only [fzrCPar, parOf, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨hap, hmod⟩ := h
  set y : FzElt := fzEOf x with hy
  have hIdx : fzEIdx y = x := by rw [hy, fzEIdx_fzEOf hx]
  have hfix : D.cT y.1 = y.1 := by
    have h0 : x % 64 = fzIdx y.1 := by rw [← hIdx, fzrAux_mod64]
    have h1 : (fzAutI D.cT).ap (fzIdx y.1) = fzIdx y.1 := by
      rw [← h0]
      exact hap
    rw [fzAutI_ap] at h1
    exact fzIdx_injective h1
  have hsum : (y.2.1.val + 2 * y.2.2.1.val + 4 * y.2.2.2.val) % 4 = 0 := by
    rw [← fzrAux_div64, hIdx]
    exact hmod
  have hv0 : y.2.1 = 0 := by
    rw [← ZMod.val_eq_zero]
    have h1 := ZMod.val_lt y.2.1
    have h2 := ZMod.val_lt y.2.2.1
    have h3 := ZMod.val_lt y.2.2.2
    omega
  have hv1 : y.2.2.1 = 0 := by
    rw [← ZMod.val_eq_zero]
    have h1 := ZMod.val_lt y.2.1
    have h2 := ZMod.val_lt y.2.2.1
    have h3 := ZMod.val_lt y.2.2.2
    omega
  have hbase : ((D.φ.symm y.1 : ↥(fzP t x₁ x₂ rho)) : G) ∈
      (baseGrp x₁ x₂ : Subgroup G) := by
    rw [D.E_iff]
    simpa using hfix
  have hbaseW : ((D.φ.symm y.1 : ↥(fzP t x₁ x₂ rho)) : G) ∈
      wreathGrp x₁ x₂ lam := fzrAux_base_le_wreath hbase
  have hlamW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hμ : D.mu y = ((D.φ.symm y.1 : ↥(fzP t x₁ x₂ rho)) : G) * lam ^ y.2.2.2.val := by
    unfold Fz319Data.mu
    rw [hv0, hv1]
    simp
  rw [show fzrCMu D x = D.mu y from rfl, hμ]
  exact (wreathGrp x₁ x₂ lam).mul_mem hbaseW ((wreathGrp x₁ x₂ lam).pow_mem hlamW _)

theorem fzrCMu_inTZ {z : G} (hz : z ∈ fourGrp x₁ x₂) {x : ℕ} (hx : x < 512)
    (h : fzrCMu D x = t * z) : (fzrCPar D).inTZ x = true := by
  have hzE : z ∈ (baseGrp x₁ x₂ : Subgroup G) := D.str.ZE hz
  have hzP : z ∈ (fzP t x₁ x₂ rho : Subgroup G) := D.pf.EP hzE
  let pz : ↥(fzP t x₁ x₂ rho) := ⟨z, hzP⟩
  have hZp : FzInZ (D.φ pz) := (D.Z_iff pz).mp hz
  have hZa : (D.φ pz).a = 0 ∧ (D.φ pz).b = 0 := hZp
  let y : FzElt := (D.φ pz, ((1 : ZMod 2), (0 : ZMod 2), (0 : ZMod 2)))
  have hy_symm : ((D.φ.symm (D.φ pz) : ↥(fzP t x₁ x₂ rho)) : G) = z := by
    rw [MulEquiv.symm_apply_apply]
  have hzt : z * t = t * z :=
    D.str.W_comm z (D.str.EW hzE) t D.str.t_mem
  have hmu : D.mu y = t * z := by
    unfold Fz319Data.mu
    dsimp only [y]
    simp only [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one]
    rw [hy_symm, hzt]
  have hmueq : D.mu (fzEOf x) = D.mu y := by
    change fzrCMu D x = D.mu y
    rw [h, hmu]
  have hy_eq : fzEOf x = y := D.mu_injective hmueq
  have hx_eq : x = fzEIdx y := by
    rw [← fzEIdx_fzEOf hx, hy_eq]
  have hxval : fzEIdx y = fzIdx (D.φ pz) + 64 := by
    unfold fzEIdx
    dsimp only [y]
    simp [ZMod.val_one, ZMod.val_zero]
  have hzidx16 : fzIdx (D.φ pz) % 16 = 0 := (fzrAux_idx_mod16 _).mpr hZp
  have hzidxlt : fzIdx (D.φ pz) < 64 := fzIdx_lt _
  have hx64 : x / 64 = 1 := by
    rw [hx_eq, hxval]
    omega
  have hxmod : x % 64 % 16 = 0 := by
    rw [hx_eq, hxval]
    omega
  simp only [fzrCPar, parOf]
  simp [hx64, hxmod]

@[expose] noncomputable def fzrCNum : FzRNum t x₁ x₂ lam rho tau T₂ where
  par := fzrCPar D
  mu := fzrCMu D
  mu_mem := fzrCMu_mem D
  mu_zero := fzrCMu_zero D
  mu_mul := fun _ _ hn hm => fzrCMu_mul D hn hm
  mu_inj := fun _ _ hn hm h => fzrCMu_inj D hn hm h
  mu_surj := fun _ hg => fzrCMu_surj D hg
  tI_eq := rfl
  sI_eq := rfl
  mu_tI := fzrCMu_tI D
  mu_sI := fzrCMu_sI D
  e_lt := fzrCPar_e_lt D
  gens_lt := (fzrCPar_lt D).2.2.1
  rho_lt := (fzrCPar_lt D).2.2.2
  mu_rho := fun _ hx => fzrCMu_rho D hx
  mu_inW := fun _ h => fzrCMu_inW D h
  mu_inTL := fun _ hx h => fzrCMu_inTL D hx h
  mu_inTZ := fun _ hz _ hx h => fzrCMu_inTZ D hz hx h
  t_mem := D.t_mem
  t_sq := D.str.t_sq
  tau_sq1 := D.pf.tau_sq1
  tau_t := D.str.tau_t

end CFSG.OddStandard.SmallF3.FritzII
