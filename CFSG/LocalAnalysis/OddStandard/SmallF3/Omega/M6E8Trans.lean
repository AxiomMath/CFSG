module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem m6e8_three_le_card_of_pairwise {α : Type} [Finite α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card α := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hcard : ({a, b, c} : Finset α).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  calc 3 = ({a, b, c} : Finset α).card := hcard.symm
    _ ≤ (Finset.univ : Finset α).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Nat.card α := by rw [Finset.card_univ, Nat.card_eq_fintype_card]

private theorem m6e8_commHom_range_card_le_two {R : Subgroup G} {s : G}
    (hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z = z * x) (hexp : ∀ x ∈ R, x ^ 2 = 1)
    (hsN : s ∈ Subgroup.normalizer (R : Set G)) (hs2 : s ^ 2 ∈ R)
    (hR8 : Nat.card ↥R = 8) :
    ∃ φ : ↥R →* ↥R, (∀ x, (φ x : G) = s * (x : G) * s⁻¹ * (x : G)⁻¹) ∧
      Nat.card ↥φ.range ≤ 2 := by
  have hconj : ∀ x : ↥R, s * (x : G) * s⁻¹ ∈ R := fun x =>
    (Subgroup.mem_normalizer_iff.1 hsN (x : G)).1 x.2
  haveI hcommI : IsMulCommutative ↥R :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  let conjHom : ↥R →* ↥R :=
    MonoidHom.mk' (fun x => ⟨s * (x : G) * s⁻¹, hconj x⟩)
      (by
        intro x z
        apply Subtype.ext
        change s * ((x : G) * (z : G)) * s⁻¹
          = (s * (x : G) * s⁻¹) * (s * (z : G) * s⁻¹)
        group)
  let invHom : ↥R →* ↥R :=
    MonoidHom.mk' (fun x => x⁻¹)
      (by
        intro x z
        rw [mul_inv_rev, mul_comm])
  let φ : ↥R →* ↥R := conjHom * invHom
  have hφ : ∀ x : ↥R, (φ x : G) = s * (x : G) * s⁻¹ * (x : G)⁻¹ := by
    intro x
    rfl
  have hs2m : s * s ∈ R := by simpa [pow_two] using hs2
  have hφφ : ∀ x : ↥R, φ (φ x) = 1 := by
    intro x
    apply Subtype.ext
    rw [hφ (φ x)]
    have hσ2 : s * (s * (x : G) * s⁻¹) * s⁻¹ = (x : G) := by
      have h1 : s * (s * (x : G) * s⁻¹) * s⁻¹ = (s * s) * (x : G) * (s * s)⁻¹ := by
        group
      rw [h1]
      calc (s * s) * (x : G) * (s * s)⁻¹ = (x : G) * (s * s) * (s * s)⁻¹ := by
            rw [hcomm (s * s) hs2m (x : G) x.2]
        _ = (x : G) := by group
    have hconjδ : s * (φ x : G) * s⁻¹ = ((φ x : G))⁻¹ := by
      calc s * (φ x : G) * s⁻¹
          = (s * (s * (x : G) * s⁻¹) * s⁻¹) * (s * (x : G)⁻¹ * s⁻¹) := by
            rw [hφ x]; group
        _ = (x : G) * (s * (x : G) * s⁻¹)⁻¹ := by rw [hσ2]; group
        _ = ((s * (x : G) * s⁻¹ * (x : G)⁻¹))⁻¹ := by group
        _ = ((φ x : G))⁻¹ := by rw [hφ x]
    rw [hconjδ]
    calc (φ x : G)⁻¹ * (φ x : G)⁻¹ = ((φ x : G) ^ 2)⁻¹ := by group
      _ = 1 := by simp [hexp (φ x : G) (φ x).2]
  have hle : φ.range ≤ φ.ker := by
    rintro z ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (hφφ x)
  have hker : Nat.card ↥φ.range ≤ Nat.card ↥φ.ker := Subgroup.card_le_of_le hle
  have hprod : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥R :=
    Subgroup.card_ker_mul_card_range φ
  refine ⟨φ, hφ, ?_⟩
  have hsq : Nat.card ↥φ.range * Nat.card ↥φ.range ≤ 8 := by
    calc Nat.card ↥φ.range * Nat.card ↥φ.range
        ≤ Nat.card ↥φ.ker * Nat.card ↥φ.range := Nat.mul_le_mul_right _ hker
      _ = Nat.card ↥R := hprod
      _ = 8 := hR8
  by_contra hlt
  push Not at hlt
  have h3 : 3 ≤ Nat.card ↥φ.range := by omega
  have h9 : 9 ≤ Nat.card ↥φ.range * Nat.card ↥φ.range := by
    simpa using Nat.mul_le_mul h3 h3
  omega

private theorem m6e8_card_centralizer_gt {T R : Subgroup G} {s r' : G}
    (hRT : R ≤ T) (hRcomm : ∀ x ∈ R, ∀ z ∈ R, x * z = z * x)
    (hR8 : Nat.card ↥R = 8) (hr'R : r' ∈ R) (hsT : s ∈ T) (hsR : s ∉ R)
    (hsr' : s * r' = r' * s) :
    8 < Nat.card ↥(T ⊓ centralizer ({r'} : Set G)) := by
  have hle : R ≤ T ⊓ centralizer ({r'} : Set G) := by
    intro x hx
    refine ⟨hRT hx, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hRcomm x hx r' hr'R)
  have hsC : s ∈ T ⊓ centralizer ({r'} : Set G) := by
    refine ⟨hsT, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hsr'
  have hne : R ≠ T ⊓ centralizer ({r'} : Set G) := by
    intro hEq
    apply hsR
    rw [hEq]
    exact hsC
  have hlt : R < T ⊓ centralizer ({r'} : Set G) := lt_of_le_of_ne hle hne
  have hcard := Subgroup.card_lt_of_lt hlt
  rwa [hR8] at hcard

theorem m6e8_exists_centralizing {T : Subgroup G} {y r : G} (hT : IsPGroup 2 T) (hyT : y ∈ T)
    (hRab : CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)))
    (hR8 : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8)
    (hRT : T ⊓ centralizer ({y} : Set G) ≠ T)
    (hrR : r ∈ T ⊓ centralizer ({y} : Set G)) (hry : r ∉ Subgroup.zpowers y) :
    ∃ r' : G, (r' = r ∨ r' = r * y) ∧ r' ∈ T ⊓ centralizer ({y} : Set G) ∧
      r' ∉ Subgroup.zpowers y ∧ 8 < Nat.card ↥(T ⊓ centralizer ({r'} : Set G)) := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  have hyR : y ∈ R := ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hrR' : r ∈ R := hrR
  have hR8' : Nat.card ↥R = 8 := hR8
  have hRT' : R ≠ T := hRT
  have hRcomm : ∀ x ∈ R, ∀ z ∈ R, x * z = z * x := by
    haveI : IsMulCommutative ↥R := hRab.1
    intro x hx z hz
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥R) (⟨z, hz⟩ : ↥R))
  have hRexp : ∀ x ∈ R, x ^ 2 = 1 := fun x hx => hRab.2 x hx
  obtain ⟨s, hsT, hsR, hsN, hs2⟩ :=
    CFSG.ComponentClassification.AschbacherKnownGroup.Lemma37.exists_mem_normalizer_sq
      (G := G) hT (show R ≤ T from inf_le_left) hRT'
  have hsy : s * y ≠ y * s := by
    intro h
    exact hsR ⟨hsT, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
  obtain ⟨φ, hφ, hφcard⟩ := m6e8_commHom_range_card_le_two hRcomm hRexp hsN hs2 hR8'
  have hdy_ne_one : (φ ⟨y, hyR⟩ : G) ≠ 1 := by
    intro h1
    have h3 : s * y * s⁻¹ * y⁻¹ = 1 := by
      rw [← hφ ⟨y, hyR⟩]
      exact h1
    have h2 : s * y * s⁻¹ = y := by
      calc s * y * s⁻¹ = s * y * s⁻¹ * y⁻¹ * y := by group
        _ = 1 * y := by rw [h3]
        _ = y := by group
    exact hsy (by
      calc s * y = s * y * s⁻¹ * s := by group
        _ = y * s := by rw [h2])
  by_cases hdr : (φ ⟨r, hrR'⟩ : G) = 1
  · refine ⟨r, Or.inl rfl, hrR', hry, ?_⟩
    have hsr : s * r = r * s := by
      have h3 : s * r * s⁻¹ * r⁻¹ = 1 := by
        rw [← hφ ⟨r, hrR'⟩]
        exact hdr
      have h2 : s * r * s⁻¹ = r := by
        calc s * r * s⁻¹ = s * r * s⁻¹ * r⁻¹ * r := by group
          _ = 1 * r := by rw [h3]
          _ = r := by group
      calc s * r = s * r * s⁻¹ * s := by group
        _ = r * s := by rw [h2]
    exact m6e8_card_centralizer_gt (R := R) (T := T) (s := s) (r' := r)
      (show R ≤ T from inf_le_left) hRcomm hR8' hrR' hsT hsR hsr
  · have hdr_eq_dy : (φ ⟨r, hrR'⟩ : G) = (φ ⟨y, hyR⟩ : G) := by
      by_contra hne
      have h3 := m6e8_three_le_card_of_pairwise
        (a := (1 : ↥φ.range))
        (b := (⟨φ ⟨y, hyR⟩, ⟨⟨y, hyR⟩, rfl⟩⟩ : ↥φ.range))
        (c := (⟨φ ⟨r, hrR'⟩, ⟨⟨r, hrR'⟩, rfl⟩⟩ : ↥φ.range))
        (by
          intro h
          have h2 : (φ ⟨y, hyR⟩ : ↥R) = 1 := by
            have := congrArg (fun z : ↥φ.range => (z : ↥R)) h
            simpa using this.symm
          have h4 : (φ ⟨y, hyR⟩ : G) = 1 := by
            have := congrArg (fun z : ↥R => (z : G)) h2
            simpa using this
          exact hdy_ne_one h4)
        (by
          intro h
          have h2 : (φ ⟨r, hrR'⟩ : ↥R) = 1 := by
            have := congrArg (fun z : ↥φ.range => (z : ↥R)) h
            simpa using this.symm
          have h4 : (φ ⟨r, hrR'⟩ : G) = 1 := by
            have := congrArg (fun z : ↥R => (z : G)) h2
            simpa using this
          exact hdr h4)
        (by
          intro h
          have h2 : (φ ⟨y, hyR⟩ : ↥R) = φ ⟨r, hrR'⟩ := by
            have := congrArg (fun z : ↥φ.range => (z : ↥R)) h
            simpa using this
          have h4 : (φ ⟨y, hyR⟩ : G) = (φ ⟨r, hrR'⟩ : G) := by
            have := congrArg (fun z : ↥R => (z : G)) h2
            simpa using this
          exact hne h4.symm)
      omega
    refine ⟨r * y, Or.inr rfl, R.mul_mem hrR' hyR, ?_, ?_⟩
    · intro hmem
      apply hry
      have hr_eq : r = (r * y) * y⁻¹ := by group
      rw [hr_eq]
      exact (Subgroup.zpowers y).mul_mem hmem
        ((Subgroup.zpowers y).inv_mem (Subgroup.mem_zpowers y))
    · have hry1 : φ ⟨r * y, R.mul_mem hrR' hyR⟩ = 1 := by
        have hsub : (⟨r * y, R.mul_mem hrR' hyR⟩ : ↥R) = ⟨r, hrR'⟩ * ⟨y, hyR⟩ :=
          Subtype.ext rfl
        rw [hsub, map_mul]
        have hdy2 : (φ ⟨y, hyR⟩ : ↥R) * (φ ⟨y, hyR⟩ : ↥R) = 1 := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_one]
          rw [← pow_two]
          exact hRexp (φ ⟨y, hyR⟩ : G) (φ ⟨y, hyR⟩).2
        have hreq : φ ⟨r, hrR'⟩ = φ ⟨y, hyR⟩ :=
          Subtype.ext (show (φ ⟨r, hrR'⟩ : G) = (φ ⟨y, hyR⟩ : G) from hdr_eq_dy)
        rw [hreq, hdy2]
      have hsry : s * (r * y) = (r * y) * s := by
        have h3 : s * (r * y) * s⁻¹ * (r * y)⁻¹ = 1 := by
          rw [← hφ ⟨r * y, R.mul_mem hrR' hyR⟩]
          exact congrArg (fun z : ↥R => (z : G)) hry1
        have h2 : s * (r * y) * s⁻¹ = r * y := by
          calc s * (r * y) * s⁻¹ = s * (r * y) * s⁻¹ * (r * y)⁻¹ * (r * y) := by group
            _ = 1 * (r * y) := by rw [h3]
            _ = r * y := by group
        calc s * (r * y) = s * (r * y) * s⁻¹ * s := by group
          _ = (r * y) * s := by rw [h2]
      exact m6e8_card_centralizer_gt (R := R) (T := T) (s := s) (r' := r * y)
        (show R ≤ T from inf_le_left) hRcomm hR8' (R.mul_mem hrR' hyR) hsT hsR hsry

end CFSG.OddStandard.SmallF3.Omega
