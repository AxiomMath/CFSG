module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NH

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem tG_not_mem_normal_eleven {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hRcard : 2 ^ 11 ≤ Nat.card R) (hAR : NormalIn A R) (hA16 : Nat.card A ≤ 16) (g : G) :
    g * t * g⁻¹ ∉ A := by
  intro hmem
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hz.toCtx10.hyp.ord_t
    rw [h, orderOf_one] at h2
    norm_num at h2
  have ha1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hb := S4B.card_le_mul_card_centralizer (R := R) (A := A) hAR.2 hmem ha1 hAR.1
  have hQp : IsPGroup 2 (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) :=
    hR.to_le inf_le_left
  have hQbound := S4A.card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t)
    hz.toCtx10.le_invCent hz.toCtx10.isPGroup hz.toCtx10.relIndex_odd
    (Ctx4.card_S_seven hz.toCtx10.toCtx4) g hQp inf_le_right
  have hA1 : Nat.card A - 1 ≤ 15 := by
    haveI : Nonempty A := ⟨⟨1, A.one_mem⟩⟩
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  have hRle : Nat.card R ≤ 15 * 2 ^ 7 := by
    calc Nat.card R
        ≤ (Nat.card A - 1) *
            Nat.card (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) := hb
      _ ≤ 15 * 2 ^ 7 := Nat.mul_le_mul hA1 hQbound
  have : (2 : ℕ) ^ 11 ≤ 15 * 2 ^ 7 := le_trans hRcard hRle
  norm_num at this

end Ctx4Z

namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem U_tG {R A : Subgroup G} (hR : IsPGroup 2 R) (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R)
    (hA : IsE16In R A) (hAN : NormalIn A R) (g : G) : g * t * g⁻¹ ∉ A := by
  obtain ⟨-, -, hAcard⟩ := hA
  have hRcard : 2 ^ 11 ≤ Nat.card R := hw.card_ctxVN ▸ Subgroup.card_le_of_le hVR
  exact hw.toCtx4Z.tG_not_mem_normal_eleven hR hRcard hAN (le_of_eq hAcard) g

theorem U_tQ {R A : Subgroup G} (hR : IsPGroup 2 R) (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R)
    (hA : IsE16In R A) (hAN : NormalIn A R) {q : G} (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    t * q ∉ A := by
  intro hmem
  have h2 : (t * q) * (t * q) = 1 := by
    have h := hA.2.1.2 (t * q) hmem
    rwa [pow_two] at h
  obtain ⟨p, hp, hp'⟩ := hw.fl_t q (hw.Q_le_ctxWN hq) h2
  exact hw.U_tG hR hVR hA hAN p (by rw [← hp']; exact hmem)

theorem U_ttauQ {R A : Subgroup G} (hR : IsPGroup 2 R) (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R)
    (hA : IsE16In R A) (hAN : NormalIn A R) {q : G} (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    (t * tau) * q ∉ A := by
  intro hmem
  obtain ⟨V', v₁, v₂, hV'e, _hV'card, hQeq, _hBinf, _hYeq, _hrho, hv₁, _hv₂, _hv₁ne, _hv₂nn,
    _hgen, _ht₁, _ht₂, _hsigma, hQm⟩ := hw.data_V
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hw.base_le_Q (Subgroup.subset_closure (by simp))
  have hv₁Q : v₁ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hQeq]; exact Subgroup.mem_sup_right hv₁
  have hx₁v₁Q : x₁ * v₁ ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).mul_mem hx₁Q hv₁Q
  have hcQm : x₁ * v₁ ∈ ctxQm t tau x₁ x₂ rho := by
    rw [ctxQm, hQm]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨w, hwW, hwc⟩ := hw.phi_surj (x₁ * v₁) hcQm
  have hwR : w ∈ R := hVR (hw.W_le_ctxVN hwW)
  have hconj : w * ((t * tau) * q) * w⁻¹ ∈ A := hAN.2 w hwR ((t * tau) * q) hmem
  have hwq : w * q = q * w := ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hwW) hq
  have hwqinv : q * w⁻¹ = w⁻¹ * q := by
    calc q * w⁻¹ = w⁻¹ * (w * q) * w⁻¹ := by group
      _ = w⁻¹ * (q * w) * w⁻¹ := by rw [hwq]
      _ = w⁻¹ * q := by group
  have hstep : w * ((t * tau) * q) * w⁻¹ = (w * (t * tau) * w⁻¹) * q := by
    calc w * ((t * tau) * q) * w⁻¹ = w * (t * tau) * (q * w⁻¹) := by group
      _ = w * (t * tau) * (w⁻¹ * q) := by rw [hwqinv]
      _ = (w * (t * tau) * w⁻¹) * q := by group
  have hconjA : w * (t * tau) * w⁻¹ * (t * tau)⁻¹ ∈ A := by
    have h2 := A.mul_mem (hstep ▸ hconj) (A.inv_mem hmem)
    convert h2 using 1
    group
  set d : G := w * tau * w⁻¹ * tau⁻¹ with hddef
  have hdY : d ∈ ctxYq t tau x₁ x₂ rho := by
    have h := hw.comm_tau_mem_Y w hwW
    have hd : d = (tau * w * tau⁻¹ * w⁻¹)⁻¹ := by rw [hddef]; group
    rw [hd]
    exact (ctxYq t tau x₁ x₂ rho).inv_mem h
  set y' : G := t * d * t⁻¹ with hy'def
  have hy'Y : y' ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hy'def]
    exact hw.normal_Y.2 t hw.t_mem_M d hdY
  have hy'Q : y' ∈ ctxQ t tau x₁ x₂ rho := hw.Y_le_Q hy'Y
  have hid : w * (t * tau) * w⁻¹ * (t * tau)⁻¹ = (x₁ * v₁) * y' := by
    rw [← hwc, hy'def, hddef]
    group
  have hcA : (x₁ * v₁) * y' ∈ A := hid ▸ hconjA
  have hv₁sq : v₁ ^ 2 = 1 := hV'e.2 v₁ hv₁
  have hy'sq : y' ^ 2 = 1 := hw.Y_isElemAbelian.2 y' hy'Y
  have hxv : (x₁ * v₁) ^ 2 = x₁ ^ 2 * v₁ ^ 2 :=
    Commute.mul_pow (show Commute x₁ v₁ from hw.Q_comm x₁ hx₁Q v₁ hv₁Q) 2
  have houter : ((x₁ * v₁) * y') ^ 2 = (x₁ * v₁) ^ 2 * y' ^ 2 :=
    Commute.mul_pow (show Commute (x₁ * v₁) y' from hw.Q_comm (x₁ * v₁) hx₁v₁Q y' hy'Q) 2
  have hsq : ((x₁ * v₁) * y') ^ 2 = x₁ ^ 2 := by
    rw [houter, hxv, hv₁sq, hy'sq]
    group
  have hsq1 : ((x₁ * v₁) * y') ^ 2 = 1 := hA.2.1.2 ((x₁ * v₁) * y') hcA
  exact hw.y_ne_one (by rw [← hsq]; exact hsq1)

theorem U_tauQ {R A : Subgroup G} (hR : IsPGroup 2 R) (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R)
    (hA : IsE16In R A) (hAN : NormalIn A R) {q : G} (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    tau * q ∉ A := by
  intro hmem
  obtain ⟨-, -, hAcard⟩ := hA
  have hYle : ctxYq t tau x₁ x₂ rho ≤ A := by
    intro c hcY
    obtain ⟨w, hwW, hwτ⟩ := hw.comm_tau_surj c⁻¹ ((ctxYq t tau x₁ x₂ rho).inv_mem hcY)
    have hwτ' : w * tau * w⁻¹ * tau⁻¹ = c := by
      calc w * tau * w⁻¹ * tau⁻¹ = (tau * w * tau⁻¹ * w⁻¹)⁻¹ := by group
        _ = (c⁻¹)⁻¹ := by rw [hwτ]
        _ = c := inv_inv c
    have hwq : w * q = q * w := ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hwW) hq
    have hwqinv : q * w⁻¹ = w⁻¹ * q := by
      calc q * w⁻¹ = w⁻¹ * (w * q) * w⁻¹ := by group
        _ = w⁻¹ * (q * w) * w⁻¹ := by rw [hwq]
        _ = w⁻¹ * q := by group
    have hconj : w * (tau * q) * w⁻¹ ∈ A :=
      hAN.2 w (hVR (hw.W_le_ctxVN hwW)) (tau * q) hmem
    have hstep1 : w * (tau * q) * w⁻¹ = (w * tau * w⁻¹) * q := by
      calc w * (tau * q) * w⁻¹ = w * tau * (q * w⁻¹) := by group
        _ = w * tau * (w⁻¹ * q) := by rw [hwqinv]
        _ = (w * tau * w⁻¹) * q := by group
    have hstep2 : w * tau * w⁻¹ = c * tau := by
      calc w * tau * w⁻¹ = (w * tau * w⁻¹ * tau⁻¹) * tau := by group
        _ = c * tau := by rw [hwτ']
    have heq : w * (tau * q) * w⁻¹ = c * (tau * q) := by rw [hstep1, hstep2]; group
    have hcA : c * (tau * q) ∈ A := heq ▸ hconj
    have hprod : (c * (tau * q)) * (tau * q)⁻¹ ∈ A := A.mul_mem hcA (A.inv_mem hmem)
    rwa [show (c * (tau * q)) * (tau * q)⁻¹ = c from by group] at hprod
  have hYeq : ctxYq t tau x₁ x₂ rho = A :=
    Subgroup.eq_of_le_of_card_ge hYle (by rw [hAcard, hw.card_Y])
  have htauY : tau * q ∈ ctxYq t tau x₁ x₂ rho := by rw [hYeq]; exact hmem
  have htauqQ : tau * q ∈ ctxQ t tau x₁ x₂ rho := hw.Y_le_Q htauY
  have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
    have hprod := (ctxQ t tau x₁ x₂ rho).mul_mem htauqQ
      ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
    rwa [show (tau * q) * q⁻¹ = tau from by group] at hprod
  exact hw.tau_not_mem_Q htauQ

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
