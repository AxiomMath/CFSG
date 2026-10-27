module

public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510A

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ABGLocalTools
  CFSG.GH74.GLS.IVK.Lifted

section DSD

variable {M : Type} [Group M]

theorem dsd_inv_mul_mem {A : Subgroup M} {u : M} (hu4 : orderOf u = 4)
    (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) {x y : M} (hx : x ∉ A) (hy : y ∉ A) :
    x⁻¹ * y ∈ A := by
  by_contra hxy
  have hx' : x⁻¹ ∉ A := fun h1 => hx (by simpa using inv_mem h1)
  have h1 := hinv _ hxy
  have h4 : x⁻¹ * y * u * (x⁻¹ * y)⁻¹ = u := by
    calc x⁻¹ * y * u * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * u * y⁻¹) * x := by group
      _ = x⁻¹ * u⁻¹ * x := by rw [hinv y hy]
      _ = (x⁻¹ * u * x⁻¹⁻¹)⁻¹ := by group
      _ = u := by rw [hinv _ hx', inv_inv]
  rw [h4] at h1
  have h5 : u * u = 1 := by
    calc u * u = u * u⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel u
  have h6 := orderOf_dvd_of_pow_eq_one (show u ^ 2 = 1 by rw [sq]; exact h5)
  rw [hu4] at h6
  norm_num at h6

theorem dsd_conj_mem {A : Subgroup M} {u : M} (hu4 : orderOf u = 4)
    (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) (g : M) {x : M} (hx : x ∈ A) :
    g * x * g⁻¹ ∈ A := by
  by_cases hg : g ∈ A
  · exact mul_mem (mul_mem hg hx) (inv_mem hg)
  · have hg' : g⁻¹ ∉ A := fun h1 => hg (by simpa using inv_mem h1)
    have hxg : x * g⁻¹ ∉ A := fun h1 => hg' (by
      have h2 := mul_mem (inv_mem hx) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2)
    have h1 := dsd_inv_mul_mem hu4 hinv hg' hxg
    rwa [inv_inv, ← mul_assoc] at h1

theorem dsd_card_le [Finite M] {A : Subgroup M} {u : M} (hu4 : orderOf u = 4)
    (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) : Nat.card M ≤ 2 * Nat.card A := by
  by_cases hall : ∀ x : M, x ∈ A
  · have hA : A = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [hA, card_top]
    omega
  · push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    have h1 := card_le_two_mul_of_cover (P := ⊤) (S := A) (h := x₀) fun x _ => by
      by_cases hx : x ∈ A
      · exact Or.inl hx
      · exact Or.inr (dsd_inv_mul_mem hu4 hinv hx₀ hx)
    rwa [card_top] at h1

theorem dsd_exists_test [Finite M] (hM : IsPGroup 2 M) {A : Subgroup M} {u : M}
    (hA : IsCyclic A) (hu : u ∈ A) (hu4 : orderOf u = 4)
    (hout : ∀ x : M, x ∉ A → orderOf x < Nat.card A)
    (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) {z : M} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ g : M, g * z = z * g) (h16 : 16 ≤ Nat.card M) :
    ∃ v : M, ∀ a : M, a * a = 1 → (v * a * v⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) = 1 →
      a = 1 ∨ a = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huz, -, -⟩ := dsd_core hA hu hu4 hout hinv hz2 hz1 hzc
  have hzA : z ∈ A := huz ▸ mul_mem hu hu
  have hcard := dsd_card_le hu4 hinv
  obtain ⟨⟨ρ, hρA⟩, hρ⟩ := hA.exists_generator
  have hρo : orderOf ρ = Nat.card A := by
    rw [← Subgroup.orderOf_mk ρ hρA]
    exact orderOf_eq_card_of_forall_mem_zpowers hρ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hM.to_subgroup A)
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set v := ρ ^ (2 ^ (k - 3)) with hv
  have hvA : v ∈ A := pow_mem hρA _
  have hvo : orderOf v = 8 := by
    have hdvd : 2 ^ (k - 3) ∣ orderOf ρ := by
      rw [hρo, hk]
      exact pow_dvd_pow 2 (by omega)
    rw [hv, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hρo, hk,
      Nat.pow_div (by omega) (by norm_num), show k - (k - 3) = 3 by omega]
  have hv2o : orderOf (v * v) = 4 := by
    rw [← sq, orderOf_pow_of_dvd (by norm_num) (by rw [hvo]; norm_num), hvo]
  have hv2 := eq_or_inv_of_orderOf_four hA hu (mul_mem hvA hvA) hu4 hv2o
  have huu : u * u ≠ 1 := by rw [huz]; exact hz1
  refine ⟨v, fun a ha2 hc2 => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨ha1, haz⟩ := hne
  have haA : a ∉ A := fun haA => haz (GH74.GLS.Stage1.Thm3.Sec6.B.cyclic_invol_unique hA haA hzA
    ha2 hz2 ha1 hz1)
  set c := v * a * v⁻¹ * a⁻¹ with hc
  have hcA : c ∈ A := by
    rw [hc, show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
    exact mul_mem hvA (dsd_conj_mem hu4 hinv a (inv_mem hvA))
  have hcc : ∀ g : M, g * c = c * g := by
    by_cases hc1 : c = 1
    · intro g
      rw [hc1, mul_one, one_mul]
    · have h1 := GH74.GLS.Stage1.Thm3.Sec6.B.cyclic_invol_unique hA hcA hzA hc2 hz2 hc1 hz1
      intro g
      rw [h1]
      exact hzc g
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hav : a * v * a⁻¹ = c * v := by
    have h1 : a * v⁻¹ * a⁻¹ = v⁻¹ * c := by rw [hc]; group
    calc a * v * a⁻¹ = (a * v⁻¹ * a⁻¹)⁻¹ := by group
      _ = c * v := by rw [h1, mul_inv_rev, inv_inv, hci]
  have hav2 : a * (v * v) * a⁻¹ = v * v := by
    calc a * (v * v) * a⁻¹ = (a * v * a⁻¹) * (a * v * a⁻¹) := by group
      _ = c * (v * c) * v := by rw [hav]; group
      _ = c * (c * v) * v := by rw [hcc v]
      _ = (c * c) * (v * v) := by group
      _ = v * v := by rw [hc2, one_mul]
  have hau := hinv a haA
  apply huu
  rcases hv2 with h1 | h1
  · rw [h1] at hav2
    rw [hav2] at hau
    calc u * u = u * u⁻¹ := by rw [← hau]
      _ = 1 := mul_inv_cancel u
  · rw [h1] at hav2
    have h2 : a * u * a⁻¹ = u := by
      calc a * u * a⁻¹ = (a * u⁻¹ * a⁻¹)⁻¹ := by group
        _ = u := by rw [hav2, inv_inv]
    rw [h2] at hau
    calc u * u = u * u⁻¹ := by rw [← hau]
      _ = 1 := mul_inv_cancel u

end DSD

end CFSG.ComponentClassification.Foote5
