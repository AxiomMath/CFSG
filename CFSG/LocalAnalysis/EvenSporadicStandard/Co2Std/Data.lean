module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Co2
public import Certificates.Certificate24960

public section

namespace CFSG.EvenSporadicStandard.Co2Std

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSporadicStandard.HypOne.Co2

structure Co2Facts (Y : Type) [Group Y] : Prop where
  sq_of_invol : ∀ v : Y, v * v = 1 → v ≠ 1 → ∃ w : Y, w * w = v
  sylow : ∃ (S : Subgroup Y) (t : Y), IsPGroup 2 S ∧
    (∀ R : Subgroup Y, IsPGroup 2 R → S ≤ R → R = S) ∧ t ∈ S ∧ t ≠ 1 ∧ t * t = 1 ∧
    (∀ s ∈ S, s * t = t * s) ∧ ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c = 1 ∨ c = t

theorem Co2Facts.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : Co2Facts Y') :
    Co2Facts Y := by
  refine ⟨fun v hv2 hv1 => ?_, ?_⟩
  · obtain ⟨w', hw'⟩ := h.sq_of_invol (e v) (by rw [← map_mul, hv2, map_one])
      (fun h1 => hv1 (e.injective (h1.trans (map_one e).symm)))
    refine ⟨e.symm w', e.injective ?_⟩
    rw [map_mul, MulEquiv.apply_symm_apply, hw']
  · obtain ⟨S', t', hSp, hmax, ht, ht1, ht2, htc, hZ⟩ := h.sylow
    refine ⟨S'.comap e.toMonoidHom, e.symm t', hSp.comap_of_injective _ e.injective, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro R hR hSR
      have hR' : IsPGroup 2 (R.map e.toMonoidHom) := hR.map _
      have hle : S' ≤ R.map e.toMonoidHom := fun x hx =>
        ⟨e.symm x, hSR (by simpa using hx), by simp⟩
      have hRS := hmax _ hR' hle
      refine le_antisymm (fun y hy => ?_) hSR
      have : e y ∈ R.map e.toMonoidHom := ⟨y, hy, rfl⟩
      rw [hRS] at this
      exact this
    · simpa using ht
    · intro h1
      exact ht1 (by simpa using congrArg e h1)
    · apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, ht2, map_one]
    · intro s hs
      apply e.injective
      have hs' : e s ∈ S' := hs
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, htc _ hs']
    · intro c hc hcc
      have hc' : e c ∈ S' := hc
      have : e c = 1 ∨ e c = t' := by
        refine hZ _ hc' fun s' hs' => ?_
        have hs : e.symm s' ∈ S'.comap e.toMonoidHom := by simpa using hs'
        have := congrArg e (hcc _ hs)
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
        exact this
      rcases this with h1 | h1
      · left; exact e.injective (by rw [h1, map_one])
      · right; exact e.injective (by rw [h1, MulEquiv.apply_symm_apply])

theorem exists_sq_root_reps :
    (∃ w ∈ co2P, w * w = locZ) ∧ (∃ w ∈ co2P, w * w = locT) ∧ (∃ w ∈ co2P, w * w = locU) :=
  Certificates.certificate24960

theorem co2P_sq_of_invol
    (v : co2P) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ w : co2P, w * w = v := by
  have hord : orderOf (v : Equiv.Perm (Fin 2300)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  obtain ⟨r, hr, c, hc, hvc⟩ := involution_cover (v : Equiv.Perm (Fin 2300)) v.2 hord
  obtain ⟨hz, ht, hu⟩ := exists_sq_root_reps
  have hroot : ∃ w ∈ co2P, w * w = r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact hu
  obtain ⟨w, hw, hww⟩ := hroot
  refine ⟨⟨c * w * c⁻¹, mul_mem (mul_mem hc hw) (inv_mem hc)⟩, Subtype.ext ?_⟩
  change c * w * c⁻¹ * (c * w * c⁻¹) = (v : Equiv.Perm (Fin 2300))
  rw [hvc, ← hww]
  group

theorem co2Facts_co2P :
    Co2Facts co2P := by
  refine ⟨co2P_sq_of_invol, ?_⟩
  have hmem : ∀ x : co2P, x ∈ (locSylow : Subgroup co2P) ↔ (x : Equiv.Perm (Fin 2300)) ∈ locS :=
    fun x => by rw [coe_locSylow, Subgroup.mem_subgroupOf]
  have hzS : zP ∈ (locSylow : Subgroup co2P) := (hmem zP).2 locZ_mem_S
  have hzcent : ⟨locZ, locZ_mem_S⟩ ∈ Subgroup.center locS :=
    (mem_center_locS_iff _).2 (Or.inr rfl)
  refine ⟨(locSylow : Subgroup co2P), zP, locSylow.isPGroup', fun R hR hle =>
    locSylow.is_maximal' hR hle, hzS, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact locZ_ne_one (congrArg Subtype.val h1)
  · apply Subtype.ext
    change locZ * locZ = 1
    rw [← pow_two]
    exact locZ_sq
  · intro s hs
    have := Subgroup.mem_center_iff.1 hzcent ⟨(s : Equiv.Perm (Fin 2300)), (hmem s).1 hs⟩
    have h2 := congrArg (fun x : locS => (x : Equiv.Perm (Fin 2300))) this
    exact Subtype.ext h2
  · intro c hc hcc
    have hy : (⟨(c : Equiv.Perm (Fin 2300)), (hmem c).1 hc⟩ : locS) ∈ Subgroup.center locS := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (⟨(g : Equiv.Perm (Fin 2300)), locS_le_P g.2⟩ : co2P) ∈
          (locSylow : Subgroup co2P) := (hmem _).2 g.2
      have := hcc _ hg
      have h2 := congrArg (fun x : co2P => (x : Equiv.Perm (Fin 2300))) this
      exact Subtype.ext h2
    rcases (mem_center_locS_iff _).1 hy with h1 | h1
    · left; exact Subtype.ext h1
    · right; exact Subtype.ext h1

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic in
theorem co2Facts_of_isSporadic
    {Y : Type} [Group Y]
    (h : IsSporadic Y .Co2) : Co2Facts Y := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.Co2 := e₀
  exact Co2Facts.of_mulEquiv (e.trans co2PermEquiv) co2Facts_co2P

end CFSG.EvenSporadicStandard.Co2Std

