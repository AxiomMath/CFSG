module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPfCore
public import CFSG.ClassicalInvolution.Asc77.AscFusionS4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem isPGroup_zpowers_of_pow_four {x : G} (h : x ^ 4 = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨2, ?_⟩
  apply Subtype.ext
  show (g : G) ^ (2 ^ 2) = 1
  rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  norm_num [h]

theorem exists_sylow_of_mem {K : Subgroup G} {x t : G} (hxK : x ∈ K) (hx4 : x ^ 4 = 1)
    (ht2 : t * t = 1) (hxt : x * t = t * x) (htK : t ∈ centralizerModOdd ⊤ K) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ x ∈ R ∧ ∀ r ∈ R, r * t = t * r := by
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_four hx4
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht2
  have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute t x from hxt.symm) k)).eq
  have hA2 : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers t : Subgroup G) :=
    hxp.to_sup_of_normal_right' htp hxn
  have hAK : Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hxK))
      (Subgroup.zpowers_le.mpr htK.2.1)
  obtain ⟨R, hR2, hAR, hRK⟩ := Asc77.AscFusion.exists_sylow_normalized hA2 hAK
  have hxR : x ∈ R := hAR (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have htR : t ∈ R := hAR (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  refine ⟨R ⊓ K, hRK, ⟨hxR, hxK⟩, fun r hr => ?_⟩
  have h1 : t * r * t⁻¹ * r⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem htR hr.1) (R.inv_mem htR)) (R.inv_mem hr.1)
  have h3 : t * r * t⁻¹ * r⁻¹ ∈ oddCoreOf K := by
    have := htK.2.2.2 r hr.2
    rwa [commutatorElement_def] at this
  have h4 : IsPGroup 2 (Subgroup.zpowers (t * r * t⁻¹ * r⁻¹)) :=
    hR2.to_le (Subgroup.zpowers_le.mpr h1)
  have h5 : t * r * t⁻¹ * r⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h3 h4
  have h6 : t * r * t⁻¹ = r := by
    have := congrArg (fun w => w * r) h5
    simpa using this
  calc r * t = t * r * t⁻¹ * t := by rw [h6]
    _ = t * r := by group

theorem mem_centralizerModOdd_of_sq (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (hf : TwinFrameData Ω K K' z u J t) (htK : t ∈ centralizerModOdd ⊤ K) {x : G} (hxK : x ∈ K)
    (hx2 : x * x = z) (hxt : x * t = t * x) : x ∈ centralizerModOdd ⊤ J := by
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hx2, hf.hz.sq]
  obtain ⟨R, hR, hxR, hRt⟩ := exists_sylow_of_mem hxK hx4 hf.ht.sq hxt htK
  have hRc : R ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRt r hr)
  have hcomm := TwinUActsPf.comm_of_sylow hΩ hf.hJ.1 hf.mem hf.ht hf.hz hf.t_ne_z hR hRc
  exact TwinUActsPf.le_centralizerModOdd_of_comm R J (fun v hv k hk => hcomm v hv k hk) hxR

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
