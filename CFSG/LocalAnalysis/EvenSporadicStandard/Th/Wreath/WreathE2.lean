module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathN1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.PhiMap
public import CFSG.LinearAlgebra.GLTwoCocycle
public import CFSG.LinearAlgebra.GL4OddGeneration

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q : Subgroup G} {z b : G}

private theorem w_apply_apply (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (x : VSub hD) : w (w x) = w x :=
  congrArg (fun e : AddMonoid.End (VSub hD) => e x) hww

private theorem one_add_w_apply (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD))
    (x : VSub hD) : (1 + w) x = x + w x := rfl

private theorem one_add_w_eq_zero_of_w_eq_self (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} {x : VSub hD} (hx : w x = x) : (1 + w) x = 0 := by
  change x + w x = 0
  rw [hx, VSub.add_self_apply hD]

private theorem one_add_w_eq_self_of_w_eq_zero (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} {x : VSub hD} (hx : w x = 0) : (1 + w) x = x := by
  change x + w x = x
  rw [hx, add_zero]

private theorem w_one_add_self (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (x : VSub hD) : w ((1 + w) x) = 0 := by
  change w (x + w x) = 0
  rw [map_add, w_apply_apply hD hww, VSub.add_self_apply]

private theorem w_vConj_apply (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} {n : G}
    (hn : n ∈ wComm hD w) (x : VSub hD) : w (vConj hD n x) = vConj hD n (w x) := by
  calc w (vConj hD n x) = (w * vConj hD n) x := by
        rw [AddMonoid.End.coe_mul]; rfl
    _ = (vConj hD n * w) x := by rw [← hn.2]
    _ = vConj hD n (w x) := by rw [AddMonoid.End.coe_mul]; rfl

private def dFun (f σ : G) : G := f⁻¹ * σ * f * σ⁻¹

private theorem dFun_eq (f σ : G) : dFun f σ = f⁻¹ * (σ * f * σ⁻¹) := by
  simp only [dFun]
  group

private theorem dFun_mul (f σ τ : G) :
    dFun f (σ * τ) = dFun f σ * (σ * dFun f τ * σ⁻¹) := by
  simp only [dFun]
  group

private theorem dFun_mem_omega1 (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w)
    {σ : G} (hσ : σ ∈ wreathN₁ hD Q w) : dFun f σ ∈ omega1 D hD.comm := by
  have hσQ : σ ∈ normalizer (Q : Set G) := hσ.1.1
  have hσf : σ * f * σ⁻¹ ∈ Q := (mem_normalizer_iff.1 hσQ f).1 hf
  have hdQ : dFun f σ ∈ Q := by
    rw [dFun_eq]
    exact Q.mul_mem (Q.inv_mem hf) hσf
  have hd2 : dFun f σ ^ 2 = 1 := by
    have hcomm : Commute f⁻¹ (σ * f * σ⁻¹) :=
      hQ.comm f⁻¹ (Q.inv_mem hf) (σ * f * σ⁻¹) hσf
    rw [dFun_eq, hcomm.mul_pow]
    have hb2 : (σ * f * σ⁻¹) ^ 2 = f ^ 2 := by
      rw [show (σ * f * σ⁻¹) ^ 2 = σ * f ^ 2 * σ⁻¹ by rw [sq, sq]; group]
      calc σ * f ^ 2 * σ⁻¹ = (f ^ 2 * σ) * σ⁻¹ := by rw [← hσ.2 (f ^ 2) hf2]
        _ = f ^ 2 := by group
    rw [hb2, inv_pow, inv_mul_cancel]
  exact CFSG.EvenSporadicStandard.ThStd.mem_omega1_iff.2
    ⟨hQ.mem_of_sq_eq_one _ hdQ hd2, hd2⟩

private def dSub (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q) {w : AddMonoid.End (VSub hD)}
    {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w) (σ : ↥(wreathN₁ hD Q w)) : VSub hD :=
  AbelianSub.mk (dFun f σ.1) (dFun_mem_omega1 hD hQ hf hf2 σ.2)

private theorem dSub_mul (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w)
    (σ τ : ↥(wreathN₁ hD Q w)) :
    dSub hD hQ hf hf2 (σ * τ) =
      dSub hD hQ hf hf2 σ + vConj hD (σ : G) (dSub hD hQ hf hf2 τ) := by
  apply AbelianSub.ext
  rw [AbelianSub.val_add,
    val_vConj_apply hD (QHyp.mem_normalizer_omega1 hD hQ σ.2.1.1) (dSub hD hQ hf hf2 τ)]
  show dFun f ((σ : G) * (τ : G)) =
    dFun f (σ : G) * ((σ : G) * dFun f (τ : G) * (σ : G)⁻¹)
  rw [dFun_mul]

private theorem one_add_w_vConj (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) {σ : G} (hσ : σ ∈ wreathN₁ hD Q w) (x : VSub hD) :
    (1 + w) (vConj hD σ x) = (1 + w) x := by
  have hσw : σ ∈ wComm hD w := hσ.1.2
  have hx : vConj hD σ x = vConj hD σ (w x) + vConj hD σ ((1 + w) x) := by
    rw [← map_add]
    show vConj hD σ x = vConj hD σ (w x + (1 + w) x)
    have hsplit : w x + (1 + w) x = x := by
      rw [one_add_w_apply hD w x]
      rw [add_comm (w x) (x + w x), add_assoc, VSub.add_self_apply, add_zero]
    rw [hsplit]
  rw [hx, map_add]
  have h1 : (1 + w) (vConj hD σ (w x)) = 0 := by
    apply one_add_w_eq_zero_of_w_eq_self hD
    rw [w_vConj_apply hD hσw, w_apply_apply hD hww]
  have h2 : (1 + w) (vConj hD σ ((1 + w) x)) = (1 + w) x := by
    have hfix : vConj hD σ ((1 + w) x) = (1 + w) x := by
      apply AbelianSub.ext
      rw [val_vConj_apply hD hσw.1]
      have hc := hσ.2 ((1 + w) x).val ⟨(1 + w) x, rfl, w_one_add_self hD hww x⟩
      calc σ * ((1 + w) x).val * σ⁻¹ = (((1 + w) x).val * σ) * σ⁻¹ := by rw [← hc]
        _ = ((1 + w) x).val := by group
    rw [hfix]
    exact one_add_w_eq_self_of_w_eq_zero hD (w_one_add_self hD hww x)
  rw [h1, h2, zero_add]

private theorem psi_mul (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) (σ τ : ↥(wreathN₁ hD Q w)) :
    (1 + w) (dSub hD hQ hf hf2 (σ * τ)) =
      (1 + w) (dSub hD hQ hf hf2 σ) + (1 + w) (dSub hD hQ hf hf2 τ) := by
  rw [dSub_mul, map_add, one_add_w_vConj hD hww σ.2]

private theorem psi_one (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) :
    (1 + w) (dSub hD hQ hf hf2 (1 : ↥(wreathN₁ hD Q w))) = 0 := by
  have h1 : dSub hD hQ hf hf2 (1 : ↥(wreathN₁ hD Q w)) = 0 := by
    apply AbelianSub.ext
    rw [AbelianSub.val_zero]
    show dFun f ((1 : ↥(wreathN₁ hD Q w)) : G) = 1
    simp [dFun]
  rw [h1, map_zero]

private theorem nsmul_eq_self_of_odd {M : Type*} [AddMonoid M] (h2 : ∀ x : M, x + x = 0)
    {m : ℕ} (hm : Odd m) (x : M) : m • x = x := by
  obtain ⟨k, rfl⟩ := hm
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, add_nsmul, ih,
      show (2 : ℕ) • x = 0 by rw [two_nsmul, h2], add_zero]

private theorem psi_odd (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) (x : ↥(wreathN₁ hD Q w)) (hodd : Odd (orderOf x)) :
    (1 + w) (dSub hD hQ hf hf2 x) = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hiter : ∀ n : ℕ,
      (1 + w) (dSub hD hQ hf hf2 (x ^ n)) =
        n • ((1 + w) (dSub hD hQ hf hf2 x)) := by
    intro n
    induction n with
    | zero => simpa using psi_one hD hQ hf hf2
    | succ n ih =>
      rw [pow_succ, psi_mul hD hQ hww hf hf2, ih, succ_nsmul]
  have h0 : (1 + w) (dSub hD hQ hf hf2 (x ^ (2 * k + 1))) = 0 := by
    rw [hpow, psi_one hD hQ hf hf2]
  rw [hiter] at h0
  have hy : (2 * k + 1) • ((1 + w) (dSub hD hQ hf hf2 x)) =
      (1 + w) (dSub hD hQ hf hf2 x) :=
    nsmul_eq_self_of_odd (fun y => VSub.add_self_apply hD y) ⟨k, rfl⟩ _
  rwa [hy] at h0

private def psiKer (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) : Subgroup ↥(wreathN₁ hD Q w) where
  carrier := {x | (1 + w) (dSub hD hQ hf hf2 x) = 0}
  one_mem' := psi_one hD hQ hf hf2
  mul_mem' := by
    intro σ τ hσ hτ
    show (1 + w) (dSub hD hQ hf hf2 (σ * τ)) = 0
    rw [psi_mul hD hQ hww hf hf2, hσ, hτ, add_zero]
  inv_mem' := by
    intro σ hσ
    show (1 + w) (dSub hD hQ hf hf2 σ⁻¹) = 0
    have h := psi_mul hD hQ hww hf hf2 σ σ⁻¹
    rw [mul_inv_cancel, psi_one hD hQ hf hf2, hσ, zero_add] at h
    exact h.symm

private theorem psi_eq_zero_of_mem_wreathP₁ (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) {σ : G} (hσ : σ ∈ wreathP₁ hD Q w) :
    ∃ h : σ ∈ wreathN₁ hD Q w, (1 + w) (dSub hD hQ hf hf2 ⟨σ, h⟩) = 0 := by
  have hle : wreathP₁ hD Q w ≤
      (psiKer hD hQ hww hf hf2).map (wreathN₁ hD Q w).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxN, hxodd⟩
    exact Subgroup.mem_map.2
      ⟨⟨x, hxN⟩, psi_odd hD hQ hww hf hf2 ⟨x, hxN⟩ (by simpa using hxodd), rfl⟩
  obtain ⟨y, hy, rfl⟩ := hle hσ
  exact ⟨y.2, hy⟩

theorem wKer_le_wreathE₂ (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hQ : QHyp L A D t Q) : wKer hD w ≤ wreathE₂ hD Q w := by
  intro v hv
  rw [mem_wreathE₂_iff]
  refine ⟨hQ.D_le (wKer_le_omega1 hD w hv).1, ?_⟩
  intro x hx
  exact (wreathP₁_le_wreathN₁ hD Q w hx).2 v hv |>.symm

theorem wreathP₁_comm_mem_wFix (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hQ : QHyp L A D t Q) {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w)
    {σ : G} (hσ : σ ∈ wreathP₁ hD Q w) : f⁻¹ * σ * f * σ⁻¹ ∈ wFix hD w := by
  obtain ⟨hσN, hψ⟩ := psi_eq_zero_of_mem_wreathP₁ hD hQ hww hf hf2 hσ
  have hwx : w (dSub hD hQ hf hf2 ⟨σ, hσN⟩) = dSub hD hQ hf hf2 ⟨σ, hσN⟩ := by
    have h1 : dSub hD hQ hf hf2 ⟨σ, hσN⟩ + dSub hD hQ hf hf2 ⟨σ, hσN⟩ = 0 :=
      VSub.add_self_apply hD _
    have h2 : (1 + w) (dSub hD hQ hf hf2 ⟨σ, hσN⟩) =
        dSub hD hQ hf hf2 ⟨σ, hσN⟩ + w (dSub hD hQ hf hf2 ⟨σ, hσN⟩) := rfl
    exact add_left_cancel (by rw [← h2, hψ, h1])
  refine (mem_wFix_iff_exists hD w).2 ⟨dSub hD hQ hf hf2 ⟨σ, hσN⟩, rfl, hwx⟩


private theorem c₁_one (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁) : c₁ 1 = 0 := by
  have h := hc₁.mul 1 (wFix hD w).one_mem 1 (wFix hD w).one_mem
  rw [one_mul] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

private def M5 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0,0,0,1; 1,0,0,1; 0,1,0,1; 0,0,1,1]

private lemma M5_pow : M5 ^ 5 = 1 := by
  decide

private lemma M5_fixed : ∀ u : Fin 4 → ZMod 2, M5 *ᵥ u = u → u = 0 := by
  decide

private def M5u : GL (Fin 4) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero M5 (by decide)

private lemma M5u_val : (M5u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M5 := rfl

private lemma M5u_pow : M5u ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, M5u_val, Units.val_one]
  exact M5_pow

private lemma M5u_odd : Odd (orderOf M5u) :=
  Odd.of_dvd_nat (show Odd 5 by norm_num) (orderOf_dvd_of_pow_eq_one M5u_pow)

theorem exists_fixedPointFree_mem_wreathP₁ (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} {c₁ : G → (Fin 4 → ZMod 2)}
    (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁) :
    ∃ σ ∈ wreathP₁ hD Q w, Odd (orderOf σ) ∧
      ∀ v ∈ wFix hD w, σ * v * σ⁻¹ = v → v = 1 := by
  obtain ⟨σ₀, hσ₀⟩ := hsurj M5u
  have hoddmap : Odd (orderOf (ρ₁ σ₀)) := by rw [hσ₀]; exact M5u_odd
  obtain ⟨γ, -, hγodd, hγρ⟩ :=
    CFSG.LinearAlgebra.exists_odd_orderOf_map_eq ρ₁ hoddmap
  have hγN : (γ : G) ∈ wreathN₁ hD Q w := γ.2
  have hγGodd : Odd (orderOf (γ : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hγodd
  have hc₁_one : c₁ 1 = 0 := c₁_one hD hc₁
  refine ⟨(γ : G), mem_wreathP₁_of_odd hD hγN hγGodd, hγGodd, ?_⟩
  intro v hv hfix
  have hrep := hρ₁ γ v hv
  rw [show (γ : G) * v * (γ : G)⁻¹ = v from hfix] at hrep
  have hM : (ρ₁ γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M5 := by
    rw [hγρ, hσ₀, M5u_val]
  rw [hM] at hrep
  have hzero : c₁ v = 0 := M5_fixed (c₁ v) hrep.symm
  exact hc₁.inj v hv 1 (wFix hD w).one_mem (by rw [hzero, hc₁_one])

theorem wreathE₂_inf_wFix_eq_bot (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁) :
    wreathE₂ hD Q w ⊓ wFix hD w = ⊥ := by
  obtain ⟨σ, hσP, -, hσfree⟩ :=
    exists_fixedPointFree_mem_wreathP₁ hD hc₁ ρ₁ hρ₁ hsurj
  refine le_antisymm ?_ bot_le
  rintro v ⟨⟨-, hvc⟩, hvFix⟩
  refine Subgroup.mem_bot.2 (hσfree v hvFix ?_)
  have hcomm : σ * v = v * σ := (mem_centralizer_iff.1 hvc) σ hσP
  calc σ * v * σ⁻¹ = (v * σ) * σ⁻¹ := by rw [hcomm]
    _ = v := by group

theorem sq_mem_wKer_of_mem_wreathE₂ (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁) {e : G} (he : e ∈ wreathE₂ hD Q w) :
    e ^ 2 ∈ wKer hD w := by
  have heQ : e ∈ Q := he.1
  have he2V : e ^ 2 ∈ omega1 D hD.comm := by
    refine (QHyp.mem_omega1_iff hD hQ (Q.pow_mem heQ 2)).2 ?_
    rw [show (e ^ 2) ^ 2 = e ^ 4 by rw [← pow_mul]]
    exact hq4 e heQ
  obtain ⟨v₁, hv₁, v₂, hv₂, heq⟩ := exists_mem_wFix_mul_mem_wKer hD w hww he2V
  have hv₂E : v₂ ∈ wreathE₂ hD Q w := wKer_le_wreathE₂ hD hQ hv₂
  have he2E : e ^ 2 ∈ wreathE₂ hD Q w := by
    have h := (wreathE₂ hD Q w).mul_mem he he
    rwa [pow_two]
  have hv₁E : v₁ ∈ wreathE₂ hD Q w := by
    have hval : v₁ = e ^ 2 * v₂⁻¹ := by rw [heq]; group
    rw [hval]
    exact (wreathE₂ hD Q w).mul_mem he2E ((wreathE₂ hD Q w).inv_mem hv₂E)
  have hv₁bot : v₁ ∈ (⊥ : Subgroup G) := by
    rw [← wreathE₂_inf_wFix_eq_bot hD hc₁ ρ₁ hρ₁ hsurj]
    exact ⟨hv₁E, hv₁⟩
  have hv₁one : v₁ = 1 := Subgroup.mem_bot.1 hv₁bot
  rw [heq, hv₁one, one_mul] at *
  exact hv₂

theorem wreathE₂_inf_omega1 (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hQ : QHyp L A D t Q)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁) :
    wreathE₂ hD Q w ⊓ omega1 D hD.comm = wKer hD w := by
  refine le_antisymm ?_ (le_inf (wKer_le_wreathE₂ hD hQ) (wKer_le_omega1 hD w))
  rintro v ⟨hvE, hvV⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, heq⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hvV
  have hv₂E : v₂ ∈ wreathE₂ hD Q w := wKer_le_wreathE₂ hD hQ hv₂
  have hv₁E : v₁ ∈ wreathE₂ hD Q w := by
    have hval : v₁ = v * v₂⁻¹ := by rw [heq]; group
    rw [hval]
    exact (wreathE₂ hD Q w).mul_mem hvE ((wreathE₂ hD Q w).inv_mem hv₂E)
  have hv₁bot : v₁ ∈ (⊥ : Subgroup G) := by
    rw [← wreathE₂_inf_wFix_eq_bot hD hc₁ ρ₁ hρ₁ hsurj]
    exact ⟨hv₁E, hv₁⟩
  have hv₁one : v₁ = 1 := Subgroup.mem_bot.1 hv₁bot
  rw [heq, hv₁one, one_mul]
  exact hv₂


private theorem inv_eq_self_of_mem_omega1 (hD : DHyp A Aa t D) {v : G}
    (hv : v ∈ omega1 D hD.comm) : v⁻¹ = v := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_two]
  exact hv.2

private theorem c₁_mul_mul (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁) {x y z : G}
    (hx : x ∈ wFix hD w) (hy : y ∈ wFix hD w) (hz : z ∈ wFix hD w) :
    c₁ (x * y * z) = c₁ x + c₁ y + c₁ z := by
  rw [hc₁.mul (x * y) ((wFix hD w).mul_mem hx hy) z hz, hc₁.mul x hx y hy]

private def kappa (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w)
    (c₁ : G → (Fin 4 → ZMod 2)) (σ : ↥(wreathN₁ hD Q w)) : Fin 4 → ZMod 2 :=
  c₁ ((w (dSub hD hQ hf hf2 σ)).val)

private theorem kappa_mul (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w) {c₁ : G → (Fin 4 → ZMod 2)}
    (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (σ τ : ↥(wreathN₁ hD Q w)) :
    kappa hD hQ hf hf2 c₁ (σ * τ) =
      kappa hD hQ hf hf2 c₁ σ +
        (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ kappa hD hQ hf hf2 c₁ τ := by
  have hFixσ : (w (dSub hD hQ hf hf2 σ)).val ∈ wFix hD w := ⟨_, rfl, w_apply_apply hD hww _⟩
  have hFixτ : (w (dSub hD hQ hf hf2 τ)).val ∈ wFix hD w := ⟨_, rfl, w_apply_apply hD hww _⟩
  have hFixc : (vConj hD (σ : G) (w (dSub hD hQ hf hf2 τ))).val ∈ wFix hD w := by
    rw [val_vConj_apply hD (QHyp.mem_normalizer_omega1 hD hQ σ.2.1.1)]
    exact conj_mem_wFix_of_mem_wComm hD σ.2.1.2 hFixτ
  have hz : w (dSub hD hQ hf hf2 (σ * τ)) =
      w (dSub hD hQ hf hf2 σ) + vConj hD (σ : G) (w (dSub hD hQ hf hf2 τ)) := by
    rw [dSub_mul, map_add, w_vConj_apply hD σ.2.1.2]
  unfold kappa
  rw [hz, AbelianSub.val_add, hc₁.mul _ hFixσ _ hFixc,
    val_vConj_apply hD (QHyp.mem_normalizer_omega1 hD hQ σ.2.1.1) (w (dSub hD hQ hf hf2 τ)),
    hρ₁ σ _ hFixτ]

private theorem kappa_ker (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w) {f : G} (hf : f ∈ Q)
    (hf2 : f ^ 2 ∈ wKer hD w)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hΦw : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c * w = w * phiQ hD Q c)
    (σ : ↥(wreathN₁ hD Q w)) (hσ : ρ₁ σ = 1) :
    kappa hD hQ hf hf2 c₁ σ = 0 := by
  have hσV₁ : ∀ v ∈ wFix hD w, (σ : G) * v * (σ : G)⁻¹ = v := by
    intro v hv
    refine hc₁.inj _ (conj_mem_wFix_of_mem_wComm hD σ.2.1.2 hv) v hv ?_
    have h := hρ₁ σ v hv
    rw [show (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 by rw [hσ]; rfl,
      Matrix.one_mulVec] at h
    exact h
  have hσV₂ : ∀ v ∈ wKer hD w, (σ : G) * v * (σ : G)⁻¹ = v := by
    intro v hv
    calc (σ : G) * v * (σ : G)⁻¹ = (v * (σ : G)) * (σ : G)⁻¹ := by rw [← σ.2.2 v hv]
      _ = v := by group
  have hσV : ∀ v ∈ omega1 D hD.comm, (σ : G) * v * (σ : G)⁻¹ = v := by
    intro v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
    rw [show (σ : G) * (v₁ * v₂) * (σ : G)⁻¹ =
        ((σ : G) * v₁ * (σ : G)⁻¹) * ((σ : G) * v₂ * (σ : G)⁻¹) by group,
      hσV₁ v₁ hv₁, hσV₂ v₂ hv₂]
  have hσNV : (σ : G) ∈
      normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
    refine ⟨σ.2.1.1, mem_centralizer_iff.2 fun v hv => ?_⟩
    calc v * (σ : G) = ((σ : G) * v * (σ : G)⁻¹) * (σ : G) := by rw [hσV v hv]
      _ = (σ : G) * v := by group
  have hf2V : f ^ 2 ∈ omega1 D hD.comm := wKer_le_omega1 hD w hf2
  have hd_eq : dFun f (σ : G) =
      (phiQ hD Q (σ : G) (AbelianSub.mk (f ^ 2) hf2V)).val :=
    (QHyp.val_phiQ_apply hD hQ hq4 hsq hσNV hf (AbelianSub.mk (f ^ 2) hf2V) rfl).symm
  have hwx : w (AbelianSub.mk (f ^ 2) hf2V) = 0 := (mem_wKer_iff hD w hf2V).1 hf2
  have hphiw : w (phiQ hD Q (σ : G) (AbelianSub.mk (f ^ 2) hf2V)) = 0 := by
    have h := congrArg
      (fun e : AddMonoid.End (VSub hD) => e (AbelianSub.mk (f ^ 2) hf2V))
      (hΦw (σ : G) hσNV)
    have hleft : (phiQ hD Q (σ : G) * w) (AbelianSub.mk (f ^ 2) hf2V) =
        phiQ hD Q (σ : G) (w (AbelianSub.mk (f ^ 2) hf2V)) := rfl
    have hright : (w * phiQ hD Q (σ : G)) (AbelianSub.mk (f ^ 2) hf2V) =
        w (phiQ hD Q (σ : G) (AbelianSub.mk (f ^ 2) hf2V)) := rfl
    rw [hleft, hright, hwx, map_zero] at h
    exact h.symm
  have hwzero : w (dSub hD hQ hf hf2 σ) = 0 := by
    have hsub : dSub hD hQ hf hf2 σ =
        (AbelianSub.mk (dFun f (σ : G))
          (dFun_mem_omega1 hD hQ hf hf2 σ.2) : VSub hD) := rfl
    have heq : (AbelianSub.mk (dFun f (σ : G))
          (dFun_mem_omega1 hD hQ hf hf2 σ.2) : VSub hD) =
        phiQ hD Q (σ : G) (AbelianSub.mk (f ^ 2) hf2V) := by
      apply AbelianSub.ext
      rw [AbelianSub.val_mk]
      exact hd_eq
    rw [hsub, heq, hphiw]
  unfold kappa
  rw [hwzero, AbelianSub.val_zero]
  exact c₁_one hD hc₁

theorem exists_mul_mem_wreathE₂ (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁)
    (hΦw : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c * w = w * phiQ hD Q c)
    {f : G} (hf : f ∈ Q) (hf2 : f ^ 2 ∈ wKer hD w) :
    ∃ a ∈ wFix hD w, f * a ∈ wreathE₂ hD Q w := by
  classical
  have htrans : ∀ i j : Fin 4, i ≠ j → ∃ γ : ↥(wreathN₁ hD Q w),
      (ρ₁ γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Matrix.transvection i j 1 := by
    intro i j hij
    obtain ⟨γ, hγ⟩ := hsurj (Matrix.GeneralLinearGroup.transvection i j hij 1)
    exact ⟨γ, by rw [hγ]; exact Matrix.GeneralLinearGroup.val_transvection i j hij 1⟩
  obtain ⟨u, hu⟩ := CFSG.LinearAlgebra.exists_eq_mulVec_sub_of_cocycle (n := 4)
    (le_rfl) ρ₁ htrans (kappa hD hQ hf hf2 c₁)
    (kappa_mul hD hQ hww hf hf2 hc₁ ρ₁ hρ₁)
    (kappa_ker hD hQ hq4 hsq hww hf hf2 hc₁ ρ₁ hρ₁ hΦw)
  obtain ⟨a, haV₁, ha⟩ := hc₁.onto u
  have haV : a ∈ omega1 D hD.comm := wFix_le_omega1 hD w haV₁
  have haQ : a ∈ Q := hQ.D_le haV.1
  have ha2 : a ^ 2 = 1 := haV.2
  have hf' : f * a ∈ Q := Q.mul_mem hf haQ
  have hf'2 : (f * a) ^ 2 ∈ wKer hD w := by
    have hcomm : Commute f a := hQ.comm f hf a haQ
    rw [hcomm.mul_pow, ha2, mul_one]
    exact hf2
  let A : VSub hD := AbelianSub.mk a haV
  have hAval : (A : VSub hD).val = a := AbelianSub.val_mk a haV
  have hwA : w A = A := (mem_wFix_iff hD w haV).1 haV₁
  have hd'_sub : ∀ σ : ↥(wreathN₁ hD Q w), dSub hD hQ hf' hf'2 σ =
      -A + dSub hD hQ hf hf2 σ + vConj hD (σ : G) A := by
    intro σ
    apply AbelianSub.ext
    rw [AbelianSub.val_add, AbelianSub.val_add, AbelianSub.val_neg,
      val_vConj_apply hD (QHyp.mem_normalizer_omega1 hD hQ σ.2.1.1), hAval]
    show dFun (f * a) (σ : G) = a⁻¹ * dFun f (σ : G) * ((σ : G) * a * (σ : G)⁻¹)
    simp only [dFun]
    group
  have hw' : ∀ σ : ↥(wreathN₁ hD Q w), w (dSub hD hQ hf' hf'2 σ) =
      -A + w (dSub hD hQ hf hf2 σ) + vConj hD (σ : G) A := by
    intro σ
    rw [hd'_sub, map_add, map_add, map_neg, w_vConj_apply hD σ.2.1.2, hwA]
  have hkappa_zero : ∀ σ : ↥(wreathN₁ hD Q w), kappa hD hQ hf' hf'2 c₁ σ = 0 := by
    intro σ
    have hFixAneg : a⁻¹ ∈ wFix hD w := (wFix hD w).inv_mem haV₁
    have hFixw : (w (dSub hD hQ hf hf2 σ)).val ∈ wFix hD w :=
      ⟨_, rfl, w_apply_apply hD hww _⟩
    have hFixc : (σ : G) * a * (σ : G)⁻¹ ∈ wFix hD w :=
      conj_mem_wFix_of_mem_wComm hD σ.2.1.2 haV₁
    have hval : (w (dSub hD hQ hf' hf'2 σ)).val =
        a⁻¹ * (w (dSub hD hQ hf hf2 σ)).val * ((σ : G) * a * (σ : G)⁻¹) := by
      rw [hw' σ, AbelianSub.val_add, AbelianSub.val_add, AbelianSub.val_neg,
        val_vConj_apply hD (QHyp.mem_normalizer_omega1 hD hQ σ.2.1.1), hAval]
    have hk := hu σ
    simp only [kappa] at hk
    calc kappa hD hQ hf' hf'2 c₁ σ
        = c₁ (a⁻¹ * (w (dSub hD hQ hf hf2 σ)).val * ((σ : G) * a * (σ : G)⁻¹)) := by
          unfold kappa
          rw [hval]
      _ = c₁ a⁻¹ + c₁ ((w (dSub hD hQ hf hf2 σ)).val) +
            c₁ ((σ : G) * a * (σ : G)⁻¹) :=
          c₁_mul_mul hD hc₁ hFixAneg hFixw hFixc
      _ = u + ((ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ u - u) +
            ((ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ u) := by
          rw [show c₁ a⁻¹ = u from by
            rw [show a⁻¹ = a from inv_eq_self_of_mem_omega1 hD haV, ha], hk,
            hρ₁ σ a haV₁, ha]
      _ = 0 := by
          have h1 : u + ((ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ u - u) =
              (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ u := by abel
          rw [h1]
          funext i
          simp only [Pi.add_apply, Pi.zero_apply]
          exact CharTwo.add_self_eq_zero _
  have hw0 : ∀ σ : ↥(wreathN₁ hD Q w), w (dSub hD hQ hf' hf'2 σ) = 0 := by
    intro σ
    apply AbelianSub.ext
    rw [AbelianSub.val_zero]
    exact hc₁.inj _ ⟨_, rfl, w_apply_apply hD hww _⟩ 1 (wFix hD w).one_mem
      (by
        have hk := hkappa_zero σ
        simp only [kappa] at hk
        rw [hk, c₁_one hD hc₁])
  have hdker : ∀ σ : ↥(wreathN₁ hD Q w), dFun (f * a) (σ : G) ∈ wKer hD w :=
    fun σ => ⟨dSub hD hQ hf' hf'2 σ, rfl, hw0 σ⟩
  refine ⟨a, haV₁, ?_⟩
  rw [mem_wreathE₂_iff]
  refine ⟨hf', fun x hx => ?_⟩
  have hxN : x ∈ wreathN₁ hD Q w := wreathP₁_le_wreathN₁ hD Q w hx
  have hFix : dFun (f * a) x ∈ wFix hD w :=
    wreathP₁_comm_mem_wFix hD hww hQ hf' hf'2 hx
  have hKer : dFun (f * a) x ∈ wKer hD w := hdker ⟨x, hxN⟩
  have hone : dFun (f * a) x = 1 := by
    have hmem : dFun (f * a) x ∈ wFix hD w ⊓ wKer hD w := ⟨hFix, hKer⟩
    rw [wFix_inf_wKer_eq_bot hD w] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hconj : x * (f * a) * x⁻¹ = f * a := by
    have h := hone
    simp only [dFun] at h
    calc x * (f * a) * x⁻¹ = (f * a) * ((f * a)⁻¹ * x * (f * a) * x⁻¹) := by group
      _ = (f * a) * 1 := by rw [h]
      _ = f * a := mul_one _
  calc x * (f * a) = (x * (f * a) * x⁻¹) * x := by group
    _ = (f * a) * x := by rw [hconj]


theorem exists_mem_wreathE₂_sq_eq (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁)
    (hΦw : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c * w = w * phiQ hD Q c)
    {v : G} (hv : v ∈ wKer hD w) : ∃ e ∈ wreathE₂ hD Q w, e ^ 2 = v := by
  have hvV : v ∈ omega1 D hD.comm := wKer_le_omega1 hD w hv
  obtain ⟨f, hfQ, hf2eq⟩ := hsq v hvV
  have hf2 : f ^ 2 ∈ wKer hD w := by rw [hf2eq]; exact hv
  obtain ⟨a, haV₁, hfaE⟩ :=
    exists_mul_mem_wreathE₂ hD hww hQ hq4 hsq hc₁ ρ₁ hρ₁ hsurj hΦw hfQ hf2
  refine ⟨f * a, hfaE, ?_⟩
  have haV : a ∈ omega1 D hD.comm := wFix_le_omega1 hD w haV₁
  have haQ : a ∈ Q := hQ.D_le haV.1
  have hcomm : Commute f a := hQ.comm f hfQ a haQ
  rw [hcomm.mul_pow, haV.2, mul_one]
  exact hf2eq

theorem card_wreathE₂ (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁)
    (hΦw : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c * w = w * phiQ hD Q c) :
    Nat.card (wreathE₂ hD Q w) = 2 ^ 8 := by
  let φ : ↥(wreathE₂ hD Q w) →* ↥(wKer hD w) :=
    { toFun := fun e =>
        ⟨(e : G) ^ 2, sq_mem_wKer_of_mem_wreathE₂ hD hww hQ hq4 hc₁ ρ₁ hρ₁ hsurj e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun e₁ e₂ => Subtype.ext (by
        have hcomm : Commute (e₁ : G) (e₂ : G) :=
          hQ.comm (e₁ : G) (wreathE₂_le hD Q w e₁.2) (e₂ : G)
            (wreathE₂_le hD Q w e₂.2)
        exact hcomm.mul_pow 2) }
  have hsurjφ : Function.Surjective φ := by
    intro v
    obtain ⟨e, he, he2⟩ :=
      exists_mem_wreathE₂_sq_eq hD hww hQ hq4 hsq hc₁ ρ₁ hρ₁ hsurj hΦw v.2
    exact ⟨⟨e, he⟩, Subtype.ext he2⟩
  have hker : φ.ker = (wKer hD w).subgroupOf (wreathE₂ hD Q w) := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_subgroupOf]
      have hsq1 : (x : G) ^ 2 = 1 := by
        have := congrArg (fun y : ↥(wKer hD w) => (y : G)) hx
        dsimp only [φ] at this
        simpa using this
      have hxD : (x : G) ∈ D :=
        hQ.mem_of_sq_eq_one _ (wreathE₂_le hD Q w x.2) hsq1
      have hxV : (x : G) ∈ omega1 D hD.comm :=
        mem_omega1_iff.2 ⟨hxD, hsq1⟩
      rw [← wreathE₂_inf_omega1 hD hww hQ hc₁ ρ₁ hρ₁ hsurj]
      exact ⟨x.2, hxV⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      dsimp only [φ]
      simpa using (wKer_le_omega1 hD w hx).2
  have hkerCard : Nat.card ↥φ.ker = 16 := by
    rw [hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (wKer_le_wreathE₂ hD hQ)).toEquiv]
    exact card_wKer H W W2 hD hww hτw
  have hrangeCard : Nat.card ↥φ.range = 16 := by
    rw [MonoidHom.range_eq_top_of_surjective φ hsurjφ, Subgroup.card_top]
    exact card_wKer H W W2 hD hww hτw
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hkerCard, hrangeCard] at hcard
  rw [← hcard]
  norm_num

end CFSG.EvenSporadicStandard.ThStd
