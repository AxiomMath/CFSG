module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmAltPerm
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallExc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open Equiv Equiv.Perm QuaternionGroup

set_option linter.unusedSectionVars false


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

namespace Alt

theorem odd_orderOf_of_fix (h : PerpHypS n Y R S t) {α : Type*} (ι : Y →* Perm α) {p : α}
    (hp : ι t p ≠ p) {w : Y} (hw : w ∈ R) (hfix : ι w p = p) : Odd (orderOf w) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hpos : 0 < orderOf w := orderOf_pos w
  have hk0 : k ≠ 0 := by omega
  have hu2 : orderOf (w ^ k) = 2 := by
    rw [orderOf_pow_of_dvd hk0 ⟨2, by omega⟩, hk, ← two_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hD := h.core.datum
  obtain ⟨e⟩ := h.core.q8
  have hut : w ^ k = t :=
    Nobq.eq_of_orderOf_eq_two_of_datum S e hD.mem hD.order hD.cent (R.pow_mem hw k) hu2
  apply hp
  rw [← hut, map_pow]
  exact Perm.pow_apply_eq_self_of_apply_eq_self hfix k

theorem mem_oddCore_of_odd (h : PerpHypS n Y R S t) {w : Y} (hw : w ∈ R)
    (hodd : Odd (orderOf w)) : (⟨w, hw⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R := by
  have h2 := h.core.datum.twoGroup
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp h2)
    (QuotientGroup.mk (⟨w, hw⟩ : ↥R) : ↥R ⧸ classicalInvolutionOddCore ↥R)
  have hdvd : orderOf (QuotientGroup.mk (⟨w, hw⟩ : ↥R) : ↥R ⧸ classicalInvolutionOddCore ↥R) ∣
      orderOf w := by
    rw [← Subgroup.orderOf_mk w hw]
    exact orderOf_map_dvd (QuotientGroup.mk' _) _
  rw [hj] at hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    have h2w : 2 ∣ orderOf w := (dvd_pow_self 2 hj0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2w)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact (QuotientGroup.eq_one_iff _).mp hj

theorem eq_one_of_mem_oddCore (h : PerpHypS n Y R S t) {φ : QuaternionGroup 2 →* Y}
    (hφK : ∀ x, φ x ∈ tightCore R) (hφt : φ (a 2) = t) {y : QuaternionGroup 2}
    (hy : (⟨φ y, tightCore_le R (hφK y)⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R) : y = 1 := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j : ℕ, φ (y ^ j) = t := by
    rcases q8_eq_or_sq y hne with h1 | h1
    · exact ⟨1, by rw [pow_one, h1, hφt]⟩
    · exact ⟨2, by rw [pow_two, h1, hφt]⟩
  have htR : t ∈ R := hj ▸ tightCore_le R (hφK _)
  have ht : (⟨t, htR⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R := by
    have hpow := pow_mem hy j
    have heq : (⟨φ y, tightCore_le R (hφK y)⟩ : ↥R) ^ j = ⟨t, htR⟩ :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hj])
    rwa [heq] at hpow
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥R)) :=
    CFSG.ComponentClassification.OddCore.odd_card R
  have hdvd := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore ↥R) ht
  rw [Subgroup.orderOf_mk, h.core.datum.order] at hdvd
  exact absurd (Odd.of_dvd_nat hodd hdvd) (by decide)

theorem moved_of_mem (h : PerpHypS n Y R S t) {α : Type*} (ι : Y →* Perm α) {p : α}
    (hp : ι t p ≠ p) {w : Y} (hw : w ∈ R) : ι t (ι w p) ≠ ι w p := by
  have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp (h.core.datum.cent hw)
  have h1 : ι w (ι t p) = ι t (ι w p) := by
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, ← map_mul, hwt]
  intro heq
  exact hp ((ι w).injective (h1.trans heq))

theorem exists_left (h : PerpHypS n Y R S t) {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 16) (ι : Y →* Perm α) {φ : QuaternionGroup 2 →* Y}
    (hφt : φ (a 2) = t) {p : α} (hp : ι t p ≠ p) {w : Y} (hw : w ∈ R) :
    ∃ y : QuaternionGroup 2, ι w p = ι (φ y) p := by
  have hq : (ι.comp φ) (a 2) p ≠ p := by rw [MonoidHom.comp_apply, hφt]; exact hp
  have hr : (ι.comp φ) (a 2) (ι w p) ≠ ι w p := by
    rw [MonoidHom.comp_apply, hφt]; exact moved_of_mem h ι hp hw
  obtain ⟨y, hy⟩ := exists_eq_of_moved hα (ι.comp φ) hq hr
  exact ⟨y, hy.symm⟩

theorem oddCore_fix (h : PerpHypS n Y R S t) {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 16) (ι : Y →* Perm α) {φ : QuaternionGroup 2 →* Y}
    (hφK : ∀ x, φ x ∈ tightCore R) (hφt : φ (a 2) = t) {p : α} (hp : ι t p ≠ p) {w : Y}
    (hw : w ∈ R) (hO : (⟨w, hw⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R) : ι w p = p := by
  obtain ⟨y, hy⟩ := exists_left h hα ι hφt hp hw
  have hyR : φ y ∈ R := tightCore_le R (hφK y)
  have hw'R : (φ y)⁻¹ * w ∈ R := R.mul_mem (R.inv_mem hyR) hw
  have hfix : ι ((φ y)⁻¹ * w) p = p := by
    rw [map_mul, map_inv, Perm.mul_apply, hy, perm_inv_apply_self]
  have hO' : (⟨(φ y)⁻¹ * w, hw'R⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R :=
    mem_oddCore_of_odd h hw'R (odd_orderOf_of_fix h ι hp hw'R hfix)
  have hyO : (⟨φ y, hyR⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R := by
    have heq : (⟨φ y, hyR⟩ : ↥R) = ⟨w, hw⟩ * (⟨(φ y)⁻¹ * w, hw'R⟩ : ↥R)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [heq]
    exact mul_mem hO (inv_mem hO')
  rw [hy, eq_one_of_mem_oddCore h hφK hφt hyO, map_one, map_one, Perm.one_apply]

theorem oddCore_fix_all (h : PerpHypS n Y R S t) {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 16) (ι : Y →* Perm α) {φ : QuaternionGroup 2 →* Y}
    (hφK : ∀ x, φ x ∈ tightCore R) (hφt : φ (a 2) = t) {p : α} (hp : ι t p ≠ p) {w : Y}
    (hw : w ∈ R) (hO : (⟨w, hw⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R)
    (x : QuaternionGroup 2) : ι w (ι (φ x) p) = ι (φ x) p := by
  have hxR : φ x ∈ R := tightCore_le R (hφK x)
  have hw''R : (φ x)⁻¹ * w * φ x ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hxR) hw) hxR
  have hO'' : (⟨(φ x)⁻¹ * w * φ x, hw''R⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R := by
    have heq : (⟨(φ x)⁻¹ * w * φ x, hw''R⟩ : ↥R) =
        (⟨φ x, hxR⟩ : ↥R)⁻¹ * ⟨w, hw⟩ * ((⟨φ x, hxR⟩ : ↥R)⁻¹)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv])
    rw [heq]
    exact (inferInstance : (classicalInvolutionOddCore ↥R).Normal).conj_mem _ hO _
  have hfix := oddCore_fix h hα ι hφK hφt hp hw''R hO''
  calc ι w (ι (φ x) p) = ι (φ x) (ι ((φ x)⁻¹ * w * φ x) p) := by
        rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, perm_apply_inv_self]
    _ = ι (φ x) p := by rw [hfix]

theorem acts_left (h : PerpHypS n Y R S t) {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 16) (ι : Y →* Perm α) {φ : QuaternionGroup 2 →* Y}
    (hφK : ∀ x, φ x ∈ tightCore R) (hφt : φ (a 2) = t) {p : α} (hp : ι t p ≠ p) {w : Y}
    (hw : w ∈ R) :
    ∃ y : QuaternionGroup 2, ∀ x : QuaternionGroup 2, ι w (ι (φ x) p) = ι (φ (y * x)) p := by
  obtain ⟨y, hy⟩ := exists_left h hα ι hφt hp hw
  have hyR : φ y ∈ R := tightCore_le R (hφK y)
  have hw'R : (φ y)⁻¹ * w ∈ R := R.mul_mem (R.inv_mem hyR) hw
  have hfix : ι ((φ y)⁻¹ * w) p = p := by
    rw [map_mul, map_inv, Perm.mul_apply, hy, perm_inv_apply_self]
  have hO' : (⟨(φ y)⁻¹ * w, hw'R⟩ : ↥R) ∈ classicalInvolutionOddCore ↥R :=
    mem_oddCore_of_odd h hw'R (odd_orderOf_of_fix h ι hp hw'R hfix)
  refine ⟨y, fun x => ?_⟩
  have hx := oddCore_fix_all h hα ι hφK hφt hp hw'R hO' x
  calc ι w (ι (φ x) p) = ι (φ y) (ι ((φ y)⁻¹ * w) (ι (φ x) p)) := by
        rw [map_mul, map_inv, Perm.mul_apply, perm_apply_inv_self]
    _ = ι (φ y) (ι (φ x) p) := by rw [hx]
    _ = ι (φ (y * x)) p := by rw [map_mul, map_mul, Perm.mul_apply]

theorem false_of_exAlt (h : PerpHypS n Y R S t) (hF : ExAlt ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  obtain ⟨m, hm7, hm11, ⟨e⟩⟩ := hF
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨ι, hι, hιN⟩ := exists_perm_embedding (by omega) (by omega) e hC
  obtain ⟨φ, hφ, hφK⟩ := exists_q8 h
  have hz := uniqueInv_core h
  have hφt : φ (a 2) = t := by
    have h1 : φ (a 2) * φ (a 2) = 1 := by
      rw [← map_mul, show (a 2 : QuaternionGroup 2) * a 2 = 1 by decide, map_one]
    have h2 : φ (a 2) ≠ 1 := fun h' =>
      absurd (hφ (h'.trans (map_one φ).symm)) (by decide)
    exact (hz.unique _ (hφK _) h1).resolve_left h2
  have hα : Fintype.card (Fin m) < 16 := by rw [Fintype.card_fin]; omega
  obtain ⟨p, hp⟩ : ∃ p, ι t p ≠ p := by
    by_contra hcon
    push Not at hcon
    have h1 : ι t = 1 := Equiv.ext hcon
    exact hz.ne_one (hι (h1.trans (map_one ι).symm))
  have hqp : (ι.comp φ) (a 2) p ≠ p := by rw [MonoidHom.comp_apply, hφt]; exact hp
  obtain ⟨σ, hσ, hcomm, hnl⟩ := exists_witness (ι.comp φ) hqp
  obtain ⟨g, hg⟩ : ∃ g : Y, ι g = σ := by
    refine ⟨(e.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩ : Y), ?_⟩
    rw [hιN, MulEquiv.apply_symm_apply]
  set k : Y := φ (xa 0) with hkdef
  have hιX : ι (g * k * g⁻¹) = σ * (ι.comp φ) (xa 0) * σ⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg, MonoidHom.comp_apply]
  refine false_of_omega5 h (g := g) (k := k) (hφK _) ?_ ?_ ?_ ?_
  · refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hkdef, orderOf_injective φ hφ, QuaternionGroup.orderOf_xa]
    norm_num
  · refine ⟨φ (a 1), hφK _, fun h' => ?_⟩
    have h'' : φ (xa 0 * a 1) = φ (a 1 * xa 0) := by rw [map_mul, map_mul]; exact h'
    exact absurd (hφ h'') (by decide)
  · apply hι
    rw [map_mul ι (g * k * g⁻¹) t, map_mul ι t (g * k * g⁻¹), hιX, ← hφt]
    exact hcomm
  · intro hN
    have hw : (g * k * g⁻¹) * φ (a 1) * (g * k * g⁻¹)⁻¹ ∈ tightCore R :=
      (Subgroup.mem_normalizer_iff.mp hN (φ (a 1))).mp (hφK _)
    obtain ⟨y, hy⟩ := acts_left h hα ι hφK hφt hp (tightCore_le R hw)
    refine hnl (ι ((g * k * g⁻¹) * φ (a 1) * (g * k * g⁻¹)⁻¹)) y ?_ (fun x => hy x)
    rw [map_mul ι ((g * k * g⁻¹) * φ (a 1)) (g * k * g⁻¹)⁻¹, map_mul ι (g * k * g⁻¹) (φ (a 1)),
      map_inv ι (g * k * g⁻¹), hιX, MonoidHom.comp_apply ι φ (a 1)]
    group

end Alt

theorem leaf_exAlt {n : ℕ} : TwinLeafS n ExAlt :=
  TwinLeafS.of_no fun _ _ _ _ _ _ h _ hF => Alt.false_of_exAlt h hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
