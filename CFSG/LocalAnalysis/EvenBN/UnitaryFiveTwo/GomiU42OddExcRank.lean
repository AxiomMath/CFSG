module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddRee
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddExc
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.GHInv
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)


variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem zpow_eq_one_or_self_of_sq {G : Type*} [Group G] {y : G} (hy : y * y = 1) (m : ℤ) :
    y ^ m = 1 ∨ y ^ m = y := by
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  have hm : y ^ m = y ^ (m % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    rw [hm, h0, zpow_zero]
  · right
    rw [hm, h1, zpow_one]

theorem outer_elementary_card_le_two_of_outPNice {L : Type} [Group L] [Finite L]
    (hN : OutPNice 2 L) (A : Subgroup (Outer L)) (hA : ∀ e ∈ A, e * e = 1) :
    Nat.card A ≤ 2 ^ 1 := by
  classical
  haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L
  obtain ⟨Dd, Ee, hInn, h2, h3, -, h5⟩ := hN
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hxy := hA _ (A.mul_mem hx hy)
    have hx2 := hA x hx
    have hy2 := hA y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]
  have key : ∀ x ∈ A, ∀ y ∈ A, x ≠ 1 → y ≠ 1 → x = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective y
    have hα2 : α ^ 2 ∈ Inn L := by
      have := hA _ hx
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this
      rw [pow_two]
      exact this
    have hβ2 : β ^ 2 ∈ Inn L := by
      have := hA _ hy
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this
      rw [pow_two]
      exact this
    have hαE : α ∈ Ee := h3 α ⟨1, by simpa using hInn hα2⟩
    have hβE : β ∈ Ee := h3 β ⟨1, by simpa using hInn hβ2⟩
    have hcmp := h5 α hαE β hβE ⟨1, by simpa using hInn hα2⟩ ⟨1, by simpa using hInn hβ2⟩
    have hyy : (QuotientGroup.mk β : Outer L) * QuotientGroup.mk β = 1 := hA _ hy
    have hxx : (QuotientGroup.mk α : Outer L) * QuotientGroup.mk α = 1 := hA _ hx
    rcases hcmp with ⟨m, hm⟩ | ⟨m, hm⟩
    ·
      have hδ2 : (α * β ^ m) ^ 2 ∈ Inn L := by
        have hsq : ((QuotientGroup.mk (α * β ^ m) : Outer L)) *
            (QuotientGroup.mk (α * β ^ m) : Outer L) = 1 := by
          have hβm : (QuotientGroup.mk β : Outer L) ^ m ∈ A := A.zpow_mem hy m
          have := hA _ (A.mul_mem hx hβm)
          rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul] at this
          exact this
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hsq
        rw [pow_two]
        exact hsq
      have hδ : α * β ^ m ∈ Inn L := h2 _ hm 1 (by simpa using hδ2)
      have hq : (QuotientGroup.mk α : Outer L) * (QuotientGroup.mk β : Outer L) ^ m = 1 := by
        rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        exact hδ
      rcases zpow_eq_one_or_self_of_sq hyy m with hm1 | hm1
      · rw [hm1, mul_one] at hq
        exact absurd hq hx1
      · rw [hm1] at hq
        have : (QuotientGroup.mk α : Outer L) = (QuotientGroup.mk β : Outer L)⁻¹ :=
          eq_inv_of_mul_eq_one_left hq
        rw [this]
        exact inv_eq_of_mul_eq_one_right hyy
    · have hδ2 : (β * α ^ m) ^ 2 ∈ Inn L := by
        have hsq : ((QuotientGroup.mk (β * α ^ m) : Outer L)) *
            (QuotientGroup.mk (β * α ^ m) : Outer L) = 1 := by
          have hαm : (QuotientGroup.mk α : Outer L) ^ m ∈ A := A.zpow_mem hx m
          have := hA _ (A.mul_mem hy hαm)
          rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul] at this
          exact this
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hsq
        rw [pow_two]
        exact hsq
      have hδ : β * α ^ m ∈ Inn L := h2 _ hm 1 (by simpa using hδ2)
      have hq : (QuotientGroup.mk β : Outer L) * (QuotientGroup.mk α : Outer L) ^ m = 1 := by
        rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        exact hδ
      rcases zpow_eq_one_or_self_of_sq hxx m with hm1 | hm1
      · rw [hm1, mul_one] at hq
        exact absurd hq hy1
      · rw [hm1] at hq
        have : (QuotientGroup.mk β : Outer L) = (QuotientGroup.mk α : Outer L)⁻¹ :=
          eq_inv_of_mul_eq_one_left hq
        rw [this]
        exact (inv_eq_of_mul_eq_one_right hxx).symm
  have hinj : Function.Injective (fun x : A => decide ((x : Outer L) = 1)) := by
    intro x y hxy
    by_cases hx1 : (x : Outer L) = 1
    · by_cases hy1 : (y : Outer L) = 1
      · exact Subtype.ext (hx1.trans hy1.symm)
      · simp [hx1, hy1] at hxy
    · by_cases hy1 : (y : Outer L) = 1
      · simp [hx1, hy1] at hxy
      · exact Subtype.ext (key _ x.2 _ y.2 hx1 hy1)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P (gomiOdd_false_of_g2 gomiOdd_false_of_d4)

open CFSG.RankThree.PartOne.OutStructure (outPNice_G2_odd outPNice_G2_three outPNice_trialityD4_odd)


theorem card_elementary_le_of_no_two_pow_six {M : Type} [Group M] [Finite M]
    (hno : ∀ E : Subgroup M, Nat.card E = 2 ^ 6 → (∀ x ∈ E, x * x = 1) → False)
    (E : Subgroup M) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 5 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one' E hE
  have hd6 : 6 ≤ d := by
    by_contra hd'
    have h5 : d ≤ 5 := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h5
    omega
  have hdvd : 2 ^ 6 ∣ Nat.card E := by
    rw [hd]
    exact pow_dvd_pow 2 hd6
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 hdvd
  refine hno (K.map E.subtype) ?_ ?_
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  · rintro _ ⟨x, -, rfl⟩
    exact hE x x.2

theorem GomiU42Data.false_of_oddLie_g2d4
    (h : GomiU42Data X J D E a) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .trialityD4) (hD : ChevalleyExceptionalModel ↥D t p f) : False := by
  have hlie : LieModel ↥D t 0 p f := Or.inr (Or.inl ⟨rfl, by rcases ht with rfl | rfl <;> decide, hD⟩)
  haveI := h.simple
  have hZ : center ↥D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).2
  have hOutP : OutPNice 2 ↥D := by
    rcases ht with rfl | rfl
    · by_cases hp3 : p = 3
      · subst hp3
        exact outPNice_G2_three Nat.prime_two hD
      · exact outPNice_G2_odd Nat.prime_two hp2 hp3 hD
    · exact outPNice_trialityD4_odd Nat.prime_two hp2 hD
  have hL : ∀ E₁ : Subgroup ↥D, (∀ x ∈ E₁, x * x = 1) → Nat.card E₁ ≤ 2 ^ 5 := by
    intro E₁ hE₁
    refine card_elementary_le_of_no_two_pow_six (fun K hKc hKsq => ?_) E₁ hE₁
    rcases ht with rfl | rfl
    · exact gomiOdd_false_of_g2 hp hp2 hlie K hKc hKsq
    · exact gomiOdd_false_of_d4 hp hp2 hlie K hKc hKsq
  obtain ⟨E', hE'sq, hE'card⟩ := h.exists_elementary_aut
  have hle := card_le_two_pow_add_of_aut (L := ↥D) hZ (r := 5) (s := 1) hL
    (fun A hA => outer_elementary_card_le_two_of_outPNice hOutP A hA) E' hE'sq
  rw [hE'card] at hle
  norm_num at hle

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
