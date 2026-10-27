module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs10b

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]

theorem conjugate_conjugate (H : Subgroup G) (a b : G) : conjugate (conjugate H a) b = conjugate H (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  have : a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
  rw [this]

theorem conjugate_one (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff]
  simp

theorem conjugate_mono {H K : Subgroup G} (h : H ≤ K) (g : G) : conjugate H g ≤ conjugate K g :=
  Subgroup.map_mono h

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card ↥(conjugate H g) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isPGroup_conjugate {p : ℕ} {H : Subgroup G} (h : IsPGroup p ↥H) (g : G) : IsPGroup p ↥(conjugate H g) :=
  h.map _

theorem conjugate_inv_conjugate (H : Subgroup G) (g : G) : conjugate (conjugate H g) g⁻¹ = H := by
  rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem normalizer_le_normalizer_centralizer (U : Subgroup G) :
    normalizer (U : Set G) ≤ normalizer ((centralizer (U : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 : n⁻¹ * u * n ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) u).mp hu
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hx (n⁻¹ * u * n) h1
    calc u * (n * x * n⁻¹) = n * ((n⁻¹ * u * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * u * n)) * n⁻¹ := by rw [h2]
      _ = n * x * n⁻¹ * u := by group
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 : n * u * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn u).mp hu
    have h2 := Subgroup.mem_centralizer_iff.mp hx (n * u * n⁻¹) h1
    calc u * x = n⁻¹ * ((n * u * n⁻¹) * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * (n * u * n⁻¹)) * n := by rw [h2]
      _ = x * u := by group

theorem normalizer_conjugate_of_centralizer {S E : Subgroup G} {a : G} (ha : a ∈ centralizer (S : Set G))
    (hE : S ≤ normalizer (E : Set G)) : S ≤ normalizer ((conjugate E a : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hsa : s * a = a * s := Subgroup.mem_centralizer_iff.mp ha s hs
  have hcomm : a * (s * x * s⁻¹) * a⁻¹ = s * (a * x * a⁻¹) * s⁻¹ := by
    calc a * (s * x * s⁻¹) * a⁻¹ = (a * s) * x * (a * s)⁻¹ := by group
      _ = (s * a) * x * (s * a)⁻¹ := by rw [hsa]
      _ = s * (a * x * a⁻¹) * s⁻¹ := by group
  rw [mem_conjugate_iff, mem_conjugate_iff, hcomm]
  exact Subgroup.mem_normalizer_iff.mp (hE hs) (a * x * a⁻¹)

theorem exists_maxSInv_above {r : ℕ} [Finite G] {S H W : Subgroup G} (hW : W ≤ H) (hp : IsPGroup r ↥W)
    (hS : S ≤ normalizer (W : Set G)) : ∃ V, MaxSInv r S H V ∧ W ≤ V := by
  obtain ⟨V, hV, hWV⟩ := exists_maxIn_above
    (𝒮 := {W' : Subgroup G | W' ≤ H ∧ IsPGroup r ↥W' ∧ S ≤ normalizer (W' : Set G)}) (R₁ := W) ⟨hW, hp, hS⟩
  exact ⟨V, ⟨hV.1.1, hV.1.2.1, hV.1.2.2, fun W' h1 h2 h3 h4 => hV.2 W' ⟨h1, h2, h3⟩ h4⟩, hWV⟩

theorem maxSInv_top_conjugate {r : ℕ} {S V : Subgroup G} {a : G} (ha : a ∈ centralizer (S : Set G))
    (hV : MaxSInv r S ⊤ V) : MaxSInv r S ⊤ (conjugate V a) := by
  have ha' : a⁻¹ ∈ centralizer (S : Set G) := inv_mem ha
  refine ⟨le_top, isPGroup_conjugate hV.2.1 a, normalizer_conjugate_of_centralizer ha hV.2.2.1, ?_⟩
  intro W _ hWp hWS hle
  have h1 : conjugate W a⁻¹ = V := by
    refine hV.2.2.2 _ le_top (isPGroup_conjugate hWp a⁻¹) (normalizer_conjugate_of_centralizer ha' hWS) ?_
    have := conjugate_mono hle a⁻¹
    rwa [conjugate_conjugate, mul_inv_cancel, conjugate_one] at this
  have h2 : conjugate (conjugate W a⁻¹) a = W := by
    rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
  rw [← h2, h1]

end Conj

end CFSG.GH74.GLS.Stage2.Bender.Thm2
