module

public import CFSG.ClassicalInvolution.Q3.Q3TIYSu4Fix
public import CFSG.ClassicalInvolution.Q3.Q3TIYStmt
public import CFSG.ClassicalInvolution.RouteD.TWT4Model

public section

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.RouteD.SCRSu4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.TWT4

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

section Model

variable {p : ℕ} [Fact p.Prime]


theorem twinMF_two_psu4_three (hp2 : p ≠ 2) {e : ℕ} (hq : 3 ≤ p ^ e) (hmod : (p ^ e) % 4 = 3)
    {R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    {x x' : (modelUniv .PSU 4 p e Fact.out).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSU 4 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K) :
    ∃ S₁ S₂ : Subgroup (modelUniv .PSU 4 p e Fact.out).K,
      S₁ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D ∧
      S₂ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D ∧ S₁ ≠ S₂ ∧
      (∀ s ∈ S₁, ∀ t ∈ S₂, s * t = t * s) ∧ (∀ s ∈ S₁, (a * a') * s = s * (a * a')) ∧
      (∀ s ∈ S₂, (a * a') * s = s * (a * a')) ∧
      ∀ S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D,
        (∀ s ∈ S, (a * a') * s = s * (a * a')) → S = S₁ ∨ S = S₂ := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hdat := su4_twin_sq_trace hK hp2
    ((hφ R).mp hd.mem) ((hφ R').mp hd.mem')
    (fun h => hd.ne (Subgroup.map_injective φ.injective h))
    (x := φ x) (x' := φ x') ⟨x, hd.hx, rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x * φ r = φ r * φ x
      rw [← map_mul, ← map_mul, hd.cx r hr])
    (fun h => hd.nx (φ.injective (h.trans (map_one φ).symm))) ⟨x', hd.hx', rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x' * φ r = φ r * φ x'
      rw [← map_mul, ← map_mul, hd.cx' r hr])
    (fun h => hd.nx' (φ.injective (h.trans (map_one φ).symm)))
    (by
      rw [← map_inv, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hd.same)
    (a := φ a) (a' := φ a') ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq)
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq')
  obtain ⟨ι, hι2, hσι⟩ := exists_iota hK hmod
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, hcomm, hc₁, hc₂, huniq⟩ :=
    fund_centralizing_su4_three hK hp2 hq hdat.1 hdat.2 hι2 hσι
  have hmapφ : ∀ L : Subgroup (Su (GaloisField p (2 * e)) p e 4),
      (L.map φ.symm.toMonoidHom).map φ.toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    ext y
    simp
  have hS₁ : L₁.map φ.symm.toMonoidHom ∈ fundamentalSubgroups .PSU
      (modelUniv .PSU 4 p e Fact.out).D := (hφ _).mpr (by rw [hmapφ]; exact hL₁)
  have hS₂ : L₂.map φ.symm.toMonoidHom ∈ fundamentalSubgroups .PSU
      (modelUniv .PSU 4 p e Fact.out).D := (hφ _).mpr (by rw [hmapφ]; exact hL₂)
  refine ⟨L₁.map φ.symm.toMonoidHom, L₂.map φ.symm.toMonoidHom, hS₁, hS₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hmapφ L₁, ← hmapφ L₂, h]
  · rintro s ⟨l₁, hl₁, rfl⟩ t ⟨l₂, hl₂, rfl⟩
    show φ.symm l₁ * φ.symm l₂ = φ.symm l₂ * φ.symm l₁
    rw [← map_mul, ← map_mul, hcomm l₁ hl₁ l₂ hl₂]
  · rintro s ⟨l₁, hl₁, rfl⟩
    show (a * a') * φ.symm l₁ = φ.symm l₁ * (a * a')
    apply φ.injective
    rw [map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hc₁ l₁ hl₁).symm
  · rintro s ⟨l₂, hl₂, rfl⟩
    show (a * a') * φ.symm l₂ = φ.symm l₂ * (a * a')
    apply φ.injective
    rw [map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hc₂ l₂ hl₂).symm
  · intro S hS hcS
    have hSφ := (hφ S).mp hS
    have hc' : ∀ y ∈ S.map φ.toMonoidHom, y * (φ a * φ a') = (φ a * φ a') * y := by
      rintro _ ⟨s, hs, rfl⟩
      show φ s * (φ a * φ a') = (φ a * φ a') * φ s
      rw [← map_mul, ← map_mul, ← map_mul, hcS s hs]
    rcases huniq _ hSφ hc' with h | h
    · left
      refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
      rw [h, hmapφ]
    · right
      refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
      rw [h, hmapφ]

end Model

section Three


theorem card_fund_centralizing_psu4
    {R R' : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K}
    {x x' ã ã' : (modelUniv .PSU 4 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 3 1 Nat.prime_three) R R' x x') (hãR : ã ∈ R)
    (hã'R : ã' ∈ R')
    (hsq : ã * ã * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 3 1 Nat.prime_three).K)
    (hsq' : ã' * ã' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 3 1 Nat.prime_three).K) :
    Nat.card {S : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D ∧
        S ≤ Subgroup.centralizer ({ã * ã'} :
          Set (modelUniv .PSU 4 3 1 Nat.prime_three).K)} = 2 := by
  obtain ⟨S₁, S₂, h₁, h₂, hne, -, hc₁, hc₂, huniq⟩ :=
    twinMF_two_psu4_three (p := 3) (e := 1) (by norm_num) (by norm_num) (by norm_num) hd hãR hã'R
      hsq hsq'
  have hle : ∀ S : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      (∀ s ∈ S, (ã * ã') * s = s * (ã * ã')) →
        S ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 3 1 Nat.prime_three).K) :=
    fun S hS s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs).symm
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨S₁, h₁, hle S₁ hc₁⟩, ⟨S₂, h₂, hle S₂ hc₂⟩, fun h => hne (congrArg Subtype.val h), ?_⟩
  ext ⟨S, hS, hSle⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases huniq S hS (fun s hs => (Subgroup.mem_centralizer_singleton_iff.mp (hSle hs)).symm) with
    rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem twinCentralizingNe3_psu4 : TwinCentralizingNe3 .PSU 4 := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq'
  obtain ⟨S₁, _, h₁, -, -, -, hc₁, -, -⟩ :=
    twinMF_two_psu4_three (p := 3) (e := 1) (by norm_num) (by norm_num) (by norm_num) hd hãR hã'R
      hsq hsq'
  exact ⟨S₁, h₁, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hc₁ s hs).symm⟩

end Three

end CFSG.ClassicalInvolution.Q3.Q3TIY
