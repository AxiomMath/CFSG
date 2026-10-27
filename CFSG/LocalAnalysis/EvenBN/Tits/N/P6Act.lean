module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Fix
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Seven
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FixedCount

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem ncard_orbit_eq_three [Finite G] {R Z : Subgroup G} (hZ4 : Nat.card Z = 4)
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hfix : ∀ z ∈ Z, (∀ r ∈ R, r * z = z * r) → z = 1) {a : G} (haZ : a ∈ Z) (ha1 : a ≠ 1) :
    {y | ∃ r ∈ R, r * a * r⁻¹ = y}.ncard = 3 := by
  set X : Set G := (Z : Set G) \ {1} with hXdef
  set O : Set G := {y | ∃ r ∈ R, r * a * r⁻¹ = y} with hOdef
  have hZcard : (Z : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ4
  have hX3 : X.ncard = 3 := by
    rw [hXdef, Set.ncard_diff_singleton_of_mem Z.one_mem, hZcard]
  have hconjX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X := by
    intro r hr x hx
    refine ⟨hRZ r hr x hx.1, fun h => hx.2 ?_⟩
    have h1 : r * x * r⁻¹ = 1 := h
    show x = 1
    calc x = r⁻¹ * (r * x * r⁻¹) * r := by group
      _ = 1 := by rw [h1]; group
  have hOX : O ⊆ X := by
    rintro _ ⟨r, hr, rfl⟩
    exact hconjX r hr a ⟨haZ, ha1⟩
  have haO : a ∈ O := ⟨1, R.one_mem, by simp⟩
  have hO3 : O.ncard ≤ 3 := hX3 ▸ Set.ncard_le_ncard hOX
  obtain ⟨r₀, hr₀, hr₀a⟩ : ∃ r ∈ R, r * a ≠ a * r := by
    by_contra h
    push Not at h
    exact ha1 (hfix a haZ h)
  have hb : r₀ * a * r₀⁻¹ ∈ O := ⟨r₀, hr₀, rfl⟩
  have hne : r₀ * a * r₀⁻¹ ≠ a := fun h => hr₀a (by
    calc r₀ * a = r₀ * a * r₀⁻¹ * r₀ := by group
      _ = a * r₀ := by rw [h])
  have hO2 : 2 ≤ O.ncard := by
    have := (Set.one_lt_ncard_iff (Set.toFinite O)).2 ⟨a, r₀ * a * r₀⁻¹, haO, hb, hne.symm⟩
    omega
  by_contra hO
  have hO2' : O.ncard = 2 := by omega
  have hdiff : (X \ O).ncard = 1 := by
    rw [Set.ncard_diff hOX, hX3, hO2']
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 hdiff
  have hcXO : c ∈ X \ O := by rw [hc]; exact Set.mem_singleton c
  have hcfix : ∀ r ∈ R, r * c * r⁻¹ = c := by
    intro r hr
    have h1 : r * c * r⁻¹ ∈ X := hconjX r hr c hcXO.1
    have h2 : r * c * r⁻¹ ∉ O := by
      rintro ⟨r', hr', hr'c⟩
      apply hcXO.2
      refine ⟨r⁻¹ * r', R.mul_mem (R.inv_mem hr) hr', ?_⟩
      calc r⁻¹ * r' * a * (r⁻¹ * r')⁻¹ = r⁻¹ * (r' * a * r'⁻¹) * r := by group
        _ = r⁻¹ * (r * c * r⁻¹) * r := by rw [hr'c]
        _ = c := by group
    have h3 : r * c * r⁻¹ ∈ X \ O := ⟨h1, h2⟩
    rw [hc] at h3
    exact h3
  have hc1 : c = 1 := hfix c hcXO.1.1 (fun r hr => by
    have := hcfix r hr
    calc r * c = r * c * r⁻¹ * r := by group
      _ = c * r := by rw [this])
  exact hcXO.1.2 hc1

theorem exists_isPGroup_three_not_comm [Finite G] {R Z : Subgroup G} (hZ4 : Nat.card Z = 4)
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hfix : ∀ z ∈ Z, (∀ r ∈ R, r * z = z * r) → z = 1) :
    ∃ y ∈ R, IsPGroup 3 (zpowers y) ∧ ∃ z ∈ Z, y * z ≠ z * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haZ, ha1⟩ : ∃ a ∈ Z, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).2 h
    rw [hbot, Subgroup.card_bot] at hZ4
    omega
  have h3 := ncard_orbit_eq_three hZ4 hRZ hfix haZ ha1
  have hcard := CFSG.LocalAnalysis.EvenBN.Tits.card_eq_ncard_conj_mul R a
  rw [h3] at hcard
  obtain ⟨P₃, hP₃⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 R
  have hP₃card := hP₃.card_eq
  have hnot : ¬ P₃ ≤ R ⊓ centralizer ({a} : Set G) := by
    intro hle
    have hdvd := Subgroup.card_dvd_of_le hle
    have hCpos : 0 < Nat.card ↥(R ⊓ centralizer ({a} : Set G)) := Nat.card_pos
    have hv : (Nat.card R).factorization 3 =
        (Nat.card ↥(R ⊓ centralizer ({a} : Set G))).factorization 3 + 1 := by
      rw [hcard, Nat.factorization_mul (by norm_num) hCpos.ne', Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_three, add_comm]
    rw [hP₃card, hv] at hdvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hCpos.ne').1 hdvd
    omega
  obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P₃, y ∉ R ⊓ centralizer ({a} : Set G) := by
    by_contra h
    push Not at h
    exact hnot h
  have hyR : y ∈ R := hP₃.le hyP
  refine ⟨y, hyR, IsPGroup.to_le hP₃.isPGroup (zpowers_le.2 hyP), a, haZ, ?_⟩
  intro hcomm
  exact hy ⟨hyR, mem_centralizer_singleton_iff.2 hcomm⟩

theorem comm_of_central_involution [Finite G] {R Z : Subgroup G} (hZ4 : Nat.card Z = 4)
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hfix : ∀ z ∈ Z, (∀ r ∈ R, r * z = z * r) → z = 1) {s : G} (hsR : s ∈ R)
    (hsc : ∀ r ∈ R, r * s = s * r) (hs2 : s * s = 1) : ∀ z ∈ Z, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Z ⊓ centralizer ((zpowers s : Subgroup G) : Set G) with hC
  have hcz : ∀ x : G, x ∈ centralizer ((zpowers s : Subgroup G) : Set G) ↔ s * x = x * s := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact h s (mem_zpowers s)
    · intro h g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      exact (Commute.zpow_left (show Commute s x from h) n).eq
  have hP : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hs2))
  have hsN : s ∈ normalizer (Z : Set G) := by
    refine mem_normalizer_iff.2 fun z => ⟨fun hz => hRZ s hsR z hz, fun h => ?_⟩
    have h1 := hRZ s hsR _ h
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have : s * (s * z * s⁻¹) * s⁻¹ = z := by
      rw [hsi]
      calc s * (s * z * s) * s = (s * s) * z * (s * s) := by group
        _ = z := by rw [hs2]; group
    rwa [this] at h1
  have hmod : Nat.card Z ≡ Nat.card C [MOD 2] :=
    CFSG.LocalAnalysis.EvenBN.Tits.card_modEq_card_inf_centralizer (p := 2) (A := Z)
      hP (fun x hx a ha => (mem_normalizer_iff.1 ((zpowers_le.2 hsN) hx) a).1 ha)
  have hCdvd : Nat.card C ∣ 4 := hZ4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hCle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hCdvd
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have heven : 2 ∣ Nat.card C := by
    have h := hmod
    unfold Nat.ModEq at h
    rw [hZ4] at h
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hC24 : Nat.card C = 2 ∨ Nat.card C = 4 := by omega
  have hCZ : C = Z := by
    rcases hC24 with h2 | h4
    · exfalso
      obtain ⟨w, hwC, hw1⟩ : ∃ w ∈ C, w ≠ 1 := by
        by_contra h
        push Not at h
        have hbot : C = ⊥ := (Subgroup.eq_bot_iff_forall C).2 h
        rw [hbot, Subgroup.card_bot] at h2
        omega
      have hwZ : w ∈ Z := (Subgroup.mem_inf.1 hwC).1
      refine hw1 (hfix w hwZ fun r hr => ?_)
      have hwcs : s * w = w * s := (hcz w).1 (Subgroup.mem_inf.1 hwC).2
      have hrs : r * s = s * r := hsc r hr
      have hsr : s * r⁻¹ = r⁻¹ * s := by
        calc s * r⁻¹ = r⁻¹ * (r * s) * r⁻¹ := by group
          _ = r⁻¹ * (s * r) * r⁻¹ := by rw [hrs]
          _ = r⁻¹ * s := by group
      have hrw : r * w * r⁻¹ ∈ C := by
        refine Subgroup.mem_inf.2 ⟨hRZ r hr w hwZ, (hcz _).2 ?_⟩
        calc s * (r * w * r⁻¹) = (s * r) * w * r⁻¹ := by group
          _ = (r * s) * w * r⁻¹ := by rw [← hrs]
          _ = r * (s * w) * r⁻¹ := by group
          _ = r * (w * s) * r⁻¹ := by rw [hwcs]
          _ = r * w * (s * r⁻¹) := by group
          _ = r * w * (r⁻¹ * s) := by rw [hsr]
          _ = r * w * r⁻¹ * s := by group
      exact comm_of_card_two h2 hwC hw1 hrw
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ4, h4])
  intro z hz
  have : z ∈ C := hCZ ▸ hz
  exact (hcz z).1 (Subgroup.mem_inf.1 this).2

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
