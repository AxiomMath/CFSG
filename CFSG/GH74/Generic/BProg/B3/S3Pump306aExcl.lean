module

public import CFSG.GH74.Generic.S3.LyVertCore
public import CFSG.GH74.GLS.Stage1.Main.Gen4NoL34Proof

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 Subgroup
open scoped MatrixGroups commutatorElement

theorem false_of_sl2 {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y) {H Lb : Subgroup Y}
    (hH : CFSG.IsComponent H) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (e : ↥H ≃* SL(2, F)) {s : Y} (hs2 : s * s = 1)
    (hsN : s ∈ normalizer (H : Set Y)) (hcomm : s ∈ _root_.commutator Y) (hLbH : Lb ≤ H)
    (hLbc : ∀ l ∈ Lb, s * l = l * s) (hLbna : ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a)
    (hns : ∃ h ∈ H, s * h ≠ h * s) : False := by
  refine vert_false hY hH hodd h3 e hs2 hsN ?_ hcomm
  intro hmem
  have hfix : ∀ (a : Y) (ha : a ∈ Lb), autOf e hsN (e ⟨a, hLbH ha⟩) = e ⟨a, hLbH ha⟩ := by
    intro a ha
    have h1 := autOf_coe e hsN (⟨a, hLbH ha⟩ : ↥H)
    have h2 : s * a * s⁻¹ = a := by
      rw [hLbc a ha]
      group
    rw [h2] at h1
    have h3' : e.symm (autOf e hsN (e ⟨a, hLbH ha⟩)) = ⟨a, hLbH ha⟩ := Subtype.ext h1
    have := congrArg e h3'
    simpa using this
  obtain ⟨a, ha, b, hb, hab⟩ := hLbna
  have hβ : autOf e hsN = 1 := by
    refine eq_one_of_mem_range_of_fix_nonabelian hmem ⟨e ⟨a, hLbH ha⟩, e ⟨b, hLbH hb⟩, hfix a ha,
      hfix b hb, fun hc => hab ?_⟩
    have h5 : (⟨a, hLbH ha⟩ * ⟨b, hLbH hb⟩ : ↥H) = ⟨b, hLbH hb⟩ * ⟨a, hLbH ha⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact hc
    exact congrArg Subtype.val h5
  obtain ⟨h0, hh0, hne0⟩ := hns
  apply hne0
  have h1 := autOf_coe e hsN (⟨h0, hh0⟩ : ↥H)
  rw [hβ] at h1
  have h2 : h0 = s * h0 * s⁻¹ := by simpa using h1
  calc s * h0 = (s * h0 * s⁻¹) * s := by group
    _ = h0 * s := by rw [← h2]

theorem false_of_l34 {Y : Type}
    [Group Y] [Finite Y] (hY : Gen4 Y) {H : Subgroup Y} (hH : CFSG.IsComponent H)
    (hZ2 : IsPGroup 2 ↥(center ↥H)) (hZ : center ↥H ≠ ⊥) (hL34 : IsL34Quotient ↥H) : False :=
  Stage1.Main.l34_cover_any ↥H hH.1 hZ2 hL34 hZ (Gen4.subgroup H hY)

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
