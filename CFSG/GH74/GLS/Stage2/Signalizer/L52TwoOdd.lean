module

public import CFSG.GH74.GLS.Stage2.Local.P27.S45E
public import CFSG.Dihedral.DihedralFusionAutomorphisms
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem centralizes_of_isPGroup_mulAut {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]
    (hA : IsPGroup 2 (MulAut ↥D)) {g : Y} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    ∀ d ∈ D, g * d * g⁻¹ = d := by
  have hα : (MulAut.conjNormal (H := D) g) ^ m = 1 := by
    rw [← map_pow, hgm, map_one]
  obtain ⟨k, hk⟩ := hA (MulAut.conjNormal (H := D) g)
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h1 : MulAut.conjNormal (H := D) g = 1 := by
    have := (pow_gcd_eq_one (a := MulAut.conjNormal (H := D) g)).mpr ⟨hk, hα⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  intro d hd
  have := congrArg (fun f : MulAut ↥D => (f ⟨d, hd⟩ : Y)) h1
  simpa [MulAut.conjNormal_apply] using this

theorem klein_aut_fixes {K : Type*} [Group K] [IsKleinFour K] (α : MulAut K) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) {u : K} (hu1 : u ≠ 1) (hfix : α u = u) : α = 1 := by
  have huu : u * u = 1 := IsKleinFour.mul_self u
  classical
  open scoped IsKleinFour in
  have hfin : Finite K := inferInstance
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨b, hb1, hbu⟩ : ∃ b : K, b ≠ 1 ∧ b ≠ u := by
    by_contra h
    have h' : ∀ b : K, b ≠ 1 → b = u := fun b hb1 => by
      by_contra hbu
      exact h ⟨b, hb1, hbu⟩
    have hsub : (Finset.univ : Finset K) ⊆ {1, u} := fun x _ => by
      by_cases hx : x = 1
      · simp [hx]
      · simp [h' x hx]
    have h2 : Fintype.card K ≤ 2 :=
      (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have h4 : Fintype.card K = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact IsKleinFour.card_four
    omega
  have hall : ∀ z : K, z = 1 ∨ z = u ∨ z = b ∨ z = u * b := by
    intro z
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    by_cases hzu : z = u
    · exact Or.inr (Or.inl hzu)
    by_cases hzb : z = b
    · exact Or.inr (Or.inr (Or.inl hzb))
    exact Or.inr (Or.inr (Or.inr (IsKleinFour.eq_mul_of_ne_all hu1 hb1 hbu.symm hz1 hzu hzb)))
  have hαb1 : α b ≠ 1 := fun h => hb1 (α.injective (h.trans (map_one α).symm))
  have hαbu : α b ≠ u := fun h => hbu (α.injective (h.trans hfix.symm))
  by_cases hb : α b = b
  · ext z
    rcases hall z with rfl | rfl | rfl | rfl
    · simp
    · simpa using hfix
    · simpa using hb
    · simp [map_mul, hfix, hb]
  · have hαb' : α b = u * b := IsKleinFour.eq_mul_of_ne_all hu1 hb1 hbu.symm hαb1 hαbu hb
    have hsq : α * α = 1 := by
      ext z
      rcases hall z with rfl | rfl | rfl | rfl
      · simp
      · simp [MulAut.mul_apply, hfix]
      · simp [MulAut.mul_apply, hαb', map_mul, hfix, ← mul_assoc, huu]
      · simp [MulAut.mul_apply, hαb', map_mul, hfix, ← mul_assoc, huu]
    obtain ⟨k, hk⟩ := hm
    have : α = α ^ m := by
      rw [hk, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
    rw [this, hαm]

theorem centralizes_of_klein {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal] [IsKleinFour ↥D]
    {g : Y} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) {u : Y} (hu : u ∈ D) (hu1 : u ≠ 1)
    (hfix : g * u * g⁻¹ = u) : ∀ d ∈ D, g * d * g⁻¹ = d := by
  have hα : (MulAut.conjNormal (H := D) g) ^ m = 1 := by
    rw [← map_pow, hgm, map_one]
  have hf : MulAut.conjNormal (H := D) g ⟨u, hu⟩ = ⟨u, hu⟩ :=
    Subtype.ext (by simpa [MulAut.conjNormal_apply] using hfix)
  have h1 := klein_aut_fixes (MulAut.conjNormal (H := D) g) hm hα
    (fun h => hu1 (congrArg Subtype.val h)) hf
  intro d hd
  have := congrArg (fun f : MulAut ↥D => (f ⟨d, hd⟩ : Y)) h1
  simpa [MulAut.conjNormal_apply] using this

theorem isPGroup_mulAut_of_le {Y : Type} [Group Y] [Finite Y] {W D : Subgroup Y}
    (hW2 : IsPGroup 2 ↥W) (hW : IsCyclic ↥W ∨ IsDihedral ↥W) (hDW : D ≤ W)
    (hK : ¬ IsKleinFour ↥D) : IsPGroup 2 (MulAut ↥D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eD : ↥(D.subgroupOf W) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDW
  have hD2 : IsPGroup 2 ↥D := IsPGroup.to_le hW2 hDW |> fun h => by
    exact h
  rcases hW with hcyc | hdih
  · have : IsCyclic ↥D := by
      have hc : IsCyclic ↥(D.subgroupOf W) := inferInstance
      exact (eD.isCyclic).1 hc
    exact CFSG.FiveTransitive.CyclicTwoAutomorphismKernel.automorphism_two_group hD2
  · obtain ⟨m, hm, ⟨e⟩⟩ := (P27.S45.isDihedral_iff_two_group hW2).1 hdih
    obtain ⟨S, hS⟩ := (show IsPGroup 2 ↥(⊤ : Subgroup ↥W) from
      (IsPGroup.of_equiv hW2 (Subgroup.topEquiv (G := ↥W)).symm)).exists_le_sylow
    have hSt : (S : Subgroup ↥W) = ⊤ := top_le_iff.1 hS
    let eS : ↥(S : Subgroup ↥W) ≃* DihedralGroup (2 ^ m) :=
      (MulEquiv.subgroupCongr hSt).trans (Subgroup.topEquiv.trans e)
    have hKU : ¬ IsKleinFour ↥(D.subgroupOf W) := by
      intro h
      apply hK
      refine ⟨?_, ?_⟩
      · rw [← Nat.card_congr eD.toEquiv]; exact h.card_four
      · rw [← Monoid.exponent_eq_of_mulEquiv eD]; exact h.exponent_two
    have hA := CFSG.GorensteinWalter.dihedral_subgroup_automorphism_isTwoGroup S hm eS
      (D.subgroupOf W) (by rw [hSt]; exact le_top) hKU
    exact hA.of_equiv (MulAut.congr eD)

theorem odd_centralizes {Y : Type} [Group Y] [Finite Y] {W D : Subgroup Y} [D.Normal]
    (hW2 : IsPGroup 2 ↥W) (hW : IsCyclic ↥W ∨ IsDihedral ↥W) (hDW : D ≤ W)
    {g : Y} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hfix : IsKleinFour ↥D → ∃ u ∈ D, u ≠ 1 ∧ g * u * g⁻¹ = u) :
    ∀ d ∈ D, g * d * g⁻¹ = d := by
  by_cases hK : IsKleinFour ↥D
  · obtain ⟨u, hu, hu1, hfx⟩ := hfix hK
    exact centralizes_of_klein hm hgm hu hu1 hfx
  · exact centralizes_of_isPGroup_mulAut (isPGroup_mulAut_of_le hW2 hW hDW hK) hm hgm

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
