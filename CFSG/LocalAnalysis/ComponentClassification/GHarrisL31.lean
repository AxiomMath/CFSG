module

public import Certificates.Certificate22601
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSModel

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

namespace SCert.SE

theorem conj_gen0 : ∀ s : SE, s⁻¹ * gen 0 * s = gen 0 := by decide +kernel

theorem conj_invRep1 : ∀ s : SE, s⁻¹ * invRep 1 * s = invRep 1 ∨
    s⁻¹ * invRep 1 * s = invRep 1 * gen 0 := by decide +kernel

theorem conj_gen7_invRep1 : (gen 7)⁻¹ * invRep 1 * gen 7 = invRep 1 * gen 0 := by decide

theorem invRep1_mul_self : invRep 1 * invRep 1 = 1 := by decide

theorem gen0_mul_self : gen 0 * gen 0 = 1 := by decide

theorem gen0_comm_invRep1 : gen 0 * invRep 1 = invRep 1 * gen 0 := by decide

theorem gen0_ne_one : gen 0 ≠ 1 := by decide

theorem invRep1_ne_one : invRep 1 ≠ 1 := by decide

theorem gen0_ne_invRep1 : gen 0 ≠ invRep 1 := by decide

theorem center_centralizer_invRep1 (s : SE)
    (hs : s * invRep 1 = invRep 1 * s)
    (hc : ∀ g : SE, g * invRep 1 = invRep 1 * g → g * s = s * g) :
    s = 1 ∨ s = gen 0 ∨ s = invRep 1 ∨ s = invRep 1 * gen 0 :=
  Certificates.certificate22601 s hs hc

end SCert.SE

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj {T : Set G} {g : G} (h1 : ∀ w ∈ T, g * w * g⁻¹ ∈ T)
    (h2 : ∀ w ∈ T, g⁻¹ * w * g ∈ T) : g ∈ normalizer T := by
  refine fun w => ⟨h1 w, fun hw => ?_⟩
  have := h2 _ hw
  rwa [show g⁻¹ * (g * w * g⁻¹) * g = w by group] at this

theorem conj_mem_of_mem_normalizer {T : Set G} {g w : G} (hg : g ∈ normalizer T) (hw : w ∈ T) :
    g⁻¹ * w * g ∈ T := by
  have := ((inv_mem hg : g⁻¹ ∈ normalizer T) w).mp hw
  rwa [inv_inv] at this

theorem conj_mem_of_two_mul_card [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (h2 : 2 * Nat.card H = Nat.card K) {k h : G} (hk : k ∈ K) (hh : h ∈ H) : k⁻¹ * h * k ∈ H := by
  have hidx : (H.subgroupOf K).index = 2 := by
    have := relIndex_mul_card (H := H) (K := K)
    rw [inf_of_le_left hHK] at this
    change H.relIndex K = 2
    have hpos : 0 < Nat.card H := Nat.card_pos
    nlinarith
  have hn := normal_of_index_eq_two hidx
  have := hn.conj_mem ⟨h, hHK hh⟩ (mem_subgroupOf.mpr hh) ⟨k, hk⟩⁻¹
  simpa [mem_subgroupOf] using this

namespace GHSylow

variable (D : GHSylow G)

abbrev z : G := D.toG (SE.gen 0)

abbrev t : G := D.toG (SE.invRep 1)

abbrev Zset : Set G := {1, D.z, D.t, D.t * D.z}

theorem conj_z_S {c : G} (hc : c ∈ (D.S : Subgroup G)) : c⁻¹ * D.z * c = D.z := by
  obtain ⟨c', rfl⟩ := D.exists_toG hc
  rw [← map_inv, ← map_mul, ← map_mul, SE.conj_gen0]

theorem conj_t_S {c : G} (hc : c ∈ (D.S : Subgroup G)) :
    c⁻¹ * D.t * c = D.t ∨ c⁻¹ * D.t * c = D.t * D.z := by
  obtain ⟨c', rfl⟩ := D.exists_toG hc
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rcases SE.conj_invRep1 c' with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem t_mul_t : D.t * D.t = 1 := by rw [← map_mul, SE.invRep1_mul_self, map_one]

theorem z_mul_z : D.z * D.z = 1 := by rw [← map_mul, SE.gen0_mul_self, map_one]

theorem z_comm_t : D.z * D.t = D.t * D.z := by rw [← map_mul, ← map_mul, SE.gen0_comm_invRep1]

theorem z_mem_S : D.z ∈ (D.S : Subgroup G) := D.toG_mem _

theorem t_mem_S : D.t ∈ (D.S : Subgroup G) := D.toG_mem _

theorem conj_Zset_S {c : G} (hc : c ∈ (D.S : Subgroup G)) {w : G} (hw : w ∈ D.Zset) :
    c⁻¹ * w * c ∈ D.Zset := by
  have hz := D.conj_z_S hc
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · rw [hz]; simp
  · rcases D.conj_t_S hc with h | h <;> rw [h] <;> simp
  · rw [show c⁻¹ * (D.t * D.z) * c = (c⁻¹ * D.t * c) * (c⁻¹ * D.z * c) by group, hz]
    rcases D.conj_t_S hc with h | h <;> rw [h]
    · simp
    · rw [mul_assoc, D.z_mul_z, mul_one]; simp

theorem S_le_normalizer_Zset : (D.S : Subgroup G) ≤ normalizer D.Zset := fun c hc =>
  mem_normalizer_of_conj (fun w hw => by
    have := D.conj_Zset_S (inv_mem hc) hw
    rwa [inv_inv] at this) (fun w hw => D.conj_Zset_S hc hw)

end GHSylow

end CFSG.ComponentClassification.GHarris
