module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

theorem lemmaR_abs {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (σ : A →* A) (hσ : ∀ a, σ (σ a) = a)
    (hA : Nat.card A = 16) (hfix : Nat.card {a : A // σ a = a} ≤ 4) :
    ∀ c : A, σ c = c → ∃ b : A, b * σ b = c := by
  letI : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  let φ : A →* A := MonoidHom.mk' (fun a => a * σ a) (by
    intro a b
    rw [map_mul, mul_mul_mul_comm])
  have hker : Nat.card φ.ker = Nat.card {a : A // σ a = a} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun a => by
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : σ a = a⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [h1, inv_eq_of_mul_eq_one_right (hsq a)]
      · intro h
        change a * σ a = 1
        rw [h, hsq a])
  have hrange_le : Nat.card φ.range ≤ Nat.card {a : A // σ a = a} := by
    refine Nat.card_le_card_of_injective (fun x : φ.range => ⟨x.1, ?_⟩) ?_
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      show σ x.1 = x.1
      rw [← ha]
      change σ (a * σ a) = a * σ a
      rw [map_mul, hσ]
      exact hcomm (σ a) a
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : {a : A // σ a = a} => (z : A)) hxy)
  have hf_pos : 0 < Nat.card {a : A // σ a = a} := by
    haveI : Nonempty {a : A // σ a = a} := ⟨⟨1, map_one σ⟩⟩
    exact Nat.card_pos
  have hprod : Nat.card {a : A // σ a = a} * Nat.card φ.range = 16 := by
    rw [← hker, Subgroup.card_ker_mul_card_range φ, hA]
  have hff : Nat.card {a : A // σ a = a} * Nat.card {a : A // σ a = a} = 16 := by
    apply le_antisymm
    · have h := Nat.mul_le_mul hfix hfix
      simpa using h
    · rw [← hprod]
      exact Nat.mul_le_mul_left _ hrange_le
  have hr : Nat.card φ.range = Nat.card {a : A // σ a = a} := by
    have hmul : Nat.card {a : A // σ a = a} * Nat.card φ.range =
        Nat.card {a : A // σ a = a} * Nat.card {a : A // σ a = a} := by
      rw [hprod, hff]
    exact Nat.mul_left_cancel hf_pos hmul
  have hsubset : (φ.range : Set A) ⊆ {a : A | σ a = a} := by
    intro y hy
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
    rw [← ha]
    change σ (a * σ a) = a * σ a
    rw [map_mul, hσ]
    exact hcomm (σ a) a
  have hfn : ({a : A | σ a = a} : Set A).ncard = Nat.card {a : A // σ a = a} := rfl
  have hrn : (φ.range : Set A).ncard = Nat.card φ.range := rfl
  have hEq : (φ.range : Set A) = {a : A | σ a = a} :=
    Set.eq_of_subset_of_ncard_le hsubset (by rw [hfn, hrn]; exact hr.ge)
  intro c hc
  have hcmem : c ∈ (φ.range : Set A) := hEq.symm ▸ hc
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hcmem
  exact ⟨b, hb⟩

theorem lemmaR_grp {E : Type*} [Group E] [Finite E] (N : Subgroup E) [N.Normal] (σ : E →* E)
    (hσN : ∀ x ∈ N, σ x ∈ N) (hσσ : ∀ a, σ (σ a) = a) (hsq : ∀ a : E, a * a ∈ N)
    (hcm : ∀ a b : E, a * b * a⁻¹ * b⁻¹ ∈ N) (hcard : Nat.card E = 16 * Nat.card N)
    (hfix : Nat.card {a : E // σ a * a⁻¹ ∈ N} ≤ 4 * Nat.card N) :
    ∀ w : E, σ w * w = 1 → ∃ b : E, (σ b)⁻¹ * w * b ∈ N := by
  let A := E ⧸ N
  haveI : Finite A := Quotient.finite (QuotientGroup.leftRel N)
  let π : E →* A := QuotientGroup.mk' N
  have hle : N ≤ N.comap σ := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hσN x hx
  let σ' : A →* A := QuotientGroup.map N N σ hle
  have hcommA : ∀ a b : A, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a ?_
    intro x
    refine QuotientGroup.induction_on b ?_
    intro y
    change (x : A) * (y : A) = (y : A) * (x : A)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hcm y⁻¹ x⁻¹
    simpa [mul_inv_rev, inv_inv, mul_assoc] using h
  have hsqA : ∀ a : A, a * a = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro x
    change (x : A) * (x : A) = 1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hsq x
  have hNpos : 0 < Nat.card N := by
    haveI : Nonempty N := ⟨⟨1, N.one_mem⟩⟩
    exact Nat.card_pos
  have hA : Nat.card A = 16 := by
    have h1 : Nat.card A * Nat.card N = 16 * Nat.card N := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcard]
    exact Nat.eq_of_mul_eq_mul_right hNpos h1
  have hσ'A : ∀ a : A, σ' (σ' a) = a := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro x
    change σ' (σ' (x : A)) = (x : A)
    rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hσσ x]
  let F : Subgroup A := MonoidHom.eqLocus σ' (MonoidHom.id A)
  let C : Subgroup E := F.comap π
  have hpq : ∀ a : E, a ∈ C ↔ σ a * a⁻¹ ∈ N := by
    intro a
    change a ∈ F.comap π ↔ σ a * a⁻¹ ∈ N
    rw [Subgroup.mem_comap]
    change σ' (a : A) = (a : A) ↔ σ a * a⁻¹ ∈ N
    rw [QuotientGroup.map_mk, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  have hC_le : Nat.card C ≤ 4 * Nat.card N := by
    have he : Nat.card {a : E // σ a * a⁻¹ ∈ N} = Nat.card C := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun a => (hpq a).symm)
    rw [← he]
    exact hfix
  have hC_index : C.index = F.index :=
    Subgroup.index_comap_of_surjective F (QuotientGroup.mk'_surjective N)
  have hF_index_ne : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcancel : Nat.card C = Nat.card F * Nat.card N := by
    have hE : Nat.card C * C.index = 16 * Nat.card N := by
      rw [Subgroup.card_mul_index, hcard]
    rw [hC_index] at hE
    have hA' : Nat.card F * F.index = 16 := by
      rw [Subgroup.card_mul_index, hA]
    have hmul : Nat.card C * F.index = (Nat.card F * Nat.card N) * F.index := by
      rw [hE, ← hA']
      exact mul_right_comm _ _ _
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hF_index_ne) hmul
  have hF_le : Nat.card F ≤ 4 := by
    have h1 : Nat.card F * Nat.card N ≤ 4 * Nat.card N := by
      rw [← hcancel]
      exact hC_le
    exact Nat.le_of_mul_le_mul_right h1 hNpos
  have hfixA : Nat.card {a : A // σ' a = a} ≤ 4 := hF_le
  have key : ∀ c : A, σ' c = c → ∃ b : A, b * σ' b = c :=
    lemmaR_abs hcommA hsqA σ' hσ'A hA hfixA
  intro w hw
  have hwA : σ' (w : A) = (w : A) := by
    rw [QuotientGroup.map_mk, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    have h1 : σ w = w⁻¹ := eq_inv_of_mul_eq_one_left hw
    rw [h1, ← mul_inv_rev]
    exact N.inv_mem (hsq w)
  obtain ⟨b', hb'⟩ := key (w : A) hwA
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective b'
  have hb'_eq : σ' b' = (σ b : A) := by
    rw [← hb, QuotientGroup.map_mk]
  have hw_eq : (w : A) = (b : A) * (σ b : A) := by
    calc (w : A) = b' * σ' b' := hb'.symm
      _ = (b : A) * (σ b : A) := by rw [hb'_eq, ← hb]
  refine ⟨b, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hw_eq]
  have hkey : (↑(σ b) : A)⁻¹ * ((b : A) * (σ b : A)) * (b : A) =
      (b : A) * (b : A) := by
    rw [hcommA (b : A) (σ b : A)]
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [hkey, hsqA (b : A)]

end CFSG.OddStandard.SmallF3.HarrisU33.L34
