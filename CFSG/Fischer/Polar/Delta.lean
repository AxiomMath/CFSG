
module

public import CFSG.Fischer.Polar.DeltaBase
import all CFSG.Fischer.Polar.DeltaBase

public import CFSG.Fischer.Polar.Hyperoval
import CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native Matrix

local notation "DT" => deltaTab ()

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  deltaTab

theorem deltaFacts : DeltaFacts := by
  have h := delta_certificate
  unfold deltaCertificate deltaTabOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hinv, hperp⟩, hconj⟩, hr1⟩, hr2⟩, hr3⟩ := h
  refine ⟨hinv, fun a ha => ?_, fun p hp q hq => ?_, hr1, hr2, hr3⟩
  · have := (allIn_eq_true.1 hperp) a (Nat.zero_le _) ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    refine ⟨this.1, fun b hb => ?_⟩
    have := (allIn_eq_true.1 this.2) b (Nat.zero_le _) hb
    rwa [beq_iff_eq] at this
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hconj) p (Nat.zero_le _) hp)) q (Nat.zero_le _) hq
    rwa [beq_iff_eq] at this

theorem rep_deltaInv : Rep 693 (invT 693 DT) delta⁻¹ := rep_deltaTab.inv_of_invOK deltaFacts.inv

theorem perp_delta
    (p q : Fin 693) : perp (delta p) (delta q) ↔ perp p q := by
  rw [← perpTab_spec, ← perpTab_spec, delta_val, delta_val, (deltaFacts.perp p.val p.2).2 q.val q.2]

theorem delta_tvP (p q : Fin 693) : delta (tvP p q) = tvP (delta p) (delta q) := by
  apply Fin.ext
  have h1 : (tvP p q).val = ap tvTabs[p.val]! q.val := by
    rw [rep_tvP p q.val q.2, idx_of_lt _ q.2]; rfl
  have h2 : (tvP (delta p) (delta q)).val = ap tvTabs[(delta p).val]! (delta q).val := by
    rw [rep_tvP (delta p) (delta q).val (delta q).2, idx_of_lt _ (delta q).2]; rfl
  rw [delta_val, h1, h2, delta_val, delta_val, deltaFacts.conj p.val p.2 q.val q.2]

theorem isPolarAut_delta :
    IsPolarAut delta := ⟨perp_delta, delta_tvP⟩

theorem delta_mul_tvP
    (p : Fin 693) : delta * tvP p * delta⁻¹ = tvP (delta p) :=
  isPolarAut_delta.mul_tvP_mul_inv p

theorem image_delta_hypRoot (i : Fin 3) : ⇑delta '' hypRoot i = hypRoot (i + 1) := by
  fin_cases i
  · show ⇑delta '' hypRoot 0 = hypRoot 1
    rw [← flagSet_rootFlags 0, ← flagSet_rootFlags 1, ← flagSet_imgFlags rep_deltaInv]
    exact congrArg flagSet deltaFacts.root₁.symm
  · show ⇑delta '' hypRoot 1 = hypRoot 2
    rw [← flagSet_rootFlags 1, ← flagSet_rootFlags 2, ← flagSet_imgFlags rep_deltaInv]
    exact congrArg flagSet deltaFacts.root₂.symm
  · show ⇑delta '' hypRoot 2 = hypRoot 0
    rw [← flagSet_rootFlags 2, ← flagSet_rootFlags 0, ← flagSet_imgFlags rep_deltaInv]
    exact congrArg flagSet deltaFacts.root₃.symm

theorem image_delta_hypOrbit
    (i : Fin 3) :
    (fun O => ⇑delta '' O) '' hypOrbit i = hypOrbit (i + 1) := by
  ext Q
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨delta * g * delta⁻¹, conj_mem_T46 isPolarAut_delta hg, ?_⟩
    show ⇑delta '' (⇑g '' hypRoot i) = ⇑(delta * g * delta⁻¹) '' hypRoot (i + 1)
    rw [← image_delta_hypRoot, ← image_mul, ← image_mul,
      show delta * g * delta⁻¹ * delta = delta * g by group]
  · rintro ⟨g, hg, rfl⟩
    have hg' : delta⁻¹ * g * delta⁻¹⁻¹ ∈ T46 := conj_mem_T46 isPolarAut_delta.inv hg
    rw [inv_inv] at hg'
    refine ⟨⇑(delta⁻¹ * g * delta) '' hypRoot i, ⟨_, hg', rfl⟩, ?_⟩
    show ⇑delta '' (⇑(delta⁻¹ * g * delta) '' hypRoot i) = ⇑g '' hypRoot (i + 1)
    rw [← image_mul, show delta * (delta⁻¹ * g * delta) = g * delta by group, image_mul,
      image_delta_hypRoot]

end CFSG.Fischer
