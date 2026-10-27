module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltSetup

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.Blueprint Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S3SL2AltTw

variable {Y : Type} [Group Y] {H : Subgroup Y} {n : ℕ} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}

@[expose] def Nsub (H : Subgroup Y) : Subgroup Y := (center ↥H).map H.subtype

theorem mem_Nsub_iff (S : AltSetting H n hsN) (w : ↥H) : (w : Y) ∈ Nsub H ↔ S.π w = 1 := by
  rw [S.mem_ker_iff]
  constructor
  · rintro ⟨z, hz, hzw⟩
    have : z = w := Subtype.ext hzw
    exact this ▸ hz
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem Nsub_le (H : Subgroup Y) : Nsub H ≤ H := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

@[expose] def Tw (S : AltSetting H n hsN) (y : Y) (τ' : Perm (Fin n)) : Prop :=
  ∃ hy : y ∈ normalizer (H : Set Y), ∀ h : ↥H,
    ((S.π (S3SL2Basic.actH H hy h) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      τ' * (S.π h : Perm (Fin n)) * τ'⁻¹

variable {S : AltSetting H n hsN}

theorem tw_of_mem (w : ↥H) : Tw S (w : Y) (S.π w : Perm (Fin n)) := by
  have hy : (w : Y) ∈ normalizer (H : Set Y) := Subgroup.le_normalizer w.2
  refine ⟨hy, fun h => ?_⟩
  have : S3SL2Basic.actH H hy h = w * h * w⁻¹ := Subtype.ext rfl
  rw [this]
  simp [map_mul, map_inv, mul_assoc]

theorem tw_mul_s (w : ↥H) : Tw S ((w : Y) * s) ((S.π w : Perm (Fin n)) * S.σ) := by
  have hy : (w : Y) * s ∈ normalizer (H : Set Y) :=
    mul_mem (Subgroup.le_normalizer w.2) hsN
  refine ⟨hy, fun h => ?_⟩
  have : S3SL2Basic.actH H hy h = w * S3SL2Basic.actH H hsN h * w⁻¹ :=
    Subtype.ext (by simp [S3SL2Basic.actH_apply, mul_assoc])
  rw [this]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, S.act]
  group

theorem Tw.comm_mem {y : Y} {τ' : Perm (Fin n)} (T : Tw S y τ') (h : ↥H)
    (hc : τ' * (S.π h : Perm (Fin n)) = (S.π h : Perm (Fin n)) * τ') :
    ⁅y, (h : Y)⁆ ∈ Nsub H := by
  obtain ⟨hy, hT⟩ := T
  have h1 : y * (h : Y) * y⁻¹ * (h : Y)⁻¹ = ((S3SL2Basic.actH H hy h * h⁻¹ : ↥H) : Y) := rfl
  rw [commutatorElement_def, h1, mem_Nsub_iff S]
  have h2 := hT h
  apply Subtype.ext
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, h2, OneMemClass.coe_one]
  calc τ' * (S.π h : Perm (Fin n)) * τ'⁻¹ * (S.π h : Perm (Fin n))⁻¹
      = (τ' * (S.π h : Perm (Fin n))) * τ'⁻¹ * (S.π h : Perm (Fin n))⁻¹ := rfl
    _ = ((S.π h : Perm (Fin n)) * τ') * τ'⁻¹ * (S.π h : Perm (Fin n))⁻¹ := by rw [hc]
    _ = 1 := by group

theorem Tw.normalizer {y : Y} {τ' : Perm (Fin n)} (T : Tw S y τ') :
    y ∈ normalizer (Nsub H : Set Y) := by
  obtain ⟨hy, hT⟩ := T
  rw [mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    have hmH : m ∈ H := Nsub_le H hm
    have hm1 : S.π ⟨m, hmH⟩ = 1 := (mem_Nsub_iff S ⟨m, hmH⟩).1 hm
    have h2 := hT ⟨m, hmH⟩
    rw [hm1] at h2
    have : (y * m * y⁻¹ : Y) = ((S3SL2Basic.actH H hy ⟨m, hmH⟩ : ↥H) : Y) := rfl
    rw [this, mem_Nsub_iff S]
    apply Subtype.ext
    rw [h2]
    simp
  · intro hm
    have hyH : y * m * y⁻¹ ∈ H := Nsub_le H hm
    have hmH : m ∈ H := (mem_normalizer_iff.1 hy m).2 hyH
    have hm1 : S.π (S3SL2Basic.actH H hy ⟨m, hmH⟩) = 1 :=
      (mem_Nsub_iff S (S3SL2Basic.actH H hy ⟨m, hmH⟩)).1 hm
    have h2 := hT ⟨m, hmH⟩
    rw [hm1] at h2
    have h3 : τ' * (S.π ⟨m, hmH⟩ : Perm (Fin n)) * τ'⁻¹ = 1 := by
      rw [← h2]; rfl
    have hπ1 : S.π ⟨m, hmH⟩ = 1 := by
      apply Subtype.ext
      calc ((S.π ⟨m, hmH⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
          = τ'⁻¹ * (τ' * (S.π ⟨m, hmH⟩ : Perm (Fin n)) * τ'⁻¹) * τ' := by group
        _ = 1 := by rw [h3]; group
    exact (mem_Nsub_iff S ⟨m, hmH⟩).2 hπ1

end S3SL2AltTw

end CFSG.GH74.Generic.BProg.B3
