
module

public import Certificates.Data.Kernel.GammaUFrameK
public import CFSG.Certificates.Kernel.GammaUNormSound

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem spanOf_map_isP {T : GL} {t : Nat} (hT : IsP T t) (D0 : List Nat) :
    spanOf (D0.map (ap12 t)) = (spanOf D0).map (T : V12 →ₗ[ZMod 2] V12) := by
  unfold spanOf
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨vecOf v, ⟨v, hv, rfl⟩, by rw [LinearEquiv.coe_coe, hT.apply_code]⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ap12 t v, ⟨v, hv, rfl⟩, by rw [LinearEquiv.coe_coe, hT.apply_code]⟩

theorem into_spec {A : Nat} {ds vs : List Nat} (hvs : ∀ v ∈ vs, v < 4096)
    (h : intoOK A ds (spanList vs) = true) : ∀ y ∈ spanOf ds, linP A y ∈ spanOf vs := by
  have hle : spanOf ds ≤ (spanOf vs).comap (linP A) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    change linP A (vecOf d) ∈ spanOf vs
    rw [← vecOf_ap12]
    exact (mem_spanList_iff hvs (ap12_lt A d)).1
      ((memN_iff _ _).1 (List.all_eq_true.1 h d hd))
  exact fun y hy => hle hy

theorem map_lt (t : Nat) (D0 : List Nat) : ∀ v ∈ D0.map (ap12 t), v < 4096 := by
  intro v hv
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hv
  exact ap12_lt t d

theorem sjAt_spec {D0 : List Nat} {g gi t t' : Nat} (h : sjAt D0 g gi t t' = true) {U T T' : GL}
    (hU : IsP U g) (hUi : IsP U⁻¹ gi) (hT : IsP T t) (hT' : IsP T' t') :
    (spanOf D0).map ((U * T : GL) : V12 →ₗ[ZMod 2] V12) =
      (spanOf D0).map (T' : V12 →ₗ[ZMod 2] V12) := by
  unfold sjAt at h
  rw [Bool.and_eq_true] at h
  have h1 := into_spec (map_lt t' D0) h.1
  have h2 := into_spec (map_lt t D0) h.2
  rw [spanOf_map_isP hT'] at h1
  rw [spanOf_map_isP hT] at h2
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have := h1 y hy
    rwa [← (hU.mul hT)] at this
  · rintro _ ⟨y, hy, rfl⟩
    have := h2 y hy
    rw [← (hUi.mul hT')] at this
    obtain ⟨z, hz, hzy⟩ := this
    refine ⟨z, hz, ?_⟩
    change (U * T) z = T' y
    rw [LinearEquiv.mul_apply]
    change T z = (U⁻¹ * T') y at hzy
    rw [hzy, LinearEquiv.mul_apply, apply_inv_apply]

theorem dtOK_spec {TH t : Nat} (hTH : ∀ v, linP TH v = theta0 v) (h : dtOK TH t = true) {T : GL}
    (hT : IsP T t) : T ∈ gammaU ∧ T (vecOf 3072) = vecOf 3072 := by
  unfold dtOK at h
  rw [Bool.and_eq_true] at h
  exact ⟨guOK_spec hTH h.1 hT, by rw [hT.apply_code, Nat.eq_of_beq_eq_true h.2]⟩

end CFSG.KC.GUV

end
