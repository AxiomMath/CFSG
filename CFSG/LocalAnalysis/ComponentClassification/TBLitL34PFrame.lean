module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PSL2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryTransfer
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PGroup

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem exists_frame {K : Subgroup X}
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) {x : X} (hxN : x ∈ normalizer (K : Set X))
    (hx2 : x * x = 1) :
    ∃ q : Jhat K →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧
      q.ker = center (Jhat K) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      ∃ ρ : Equiv.Perm (Fin 42), (ρ = 1 ∨ ρ = r₁ ∨ ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
        ∀ e, q (betaHat K hxN e) = ρ * q e * ρ⁻¹ := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat K hxN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have h1 := hr (betaHat K hxN e)
      rw [betaHat_betaHat K hxN hx2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact mem_bot.mp hc
  by_cases hr1 : r = 1
  · refine ⟨q, hqS, hqsurj, hqker, h3, 1, Or.inl rfl, fun e => ?_⟩
    rw [hr e, hr1]
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hr1 (congrArg Subtype.val h)
    simp only [OneMemClass.coe_one, pow_two]
    exact hr2
  have hconj : ∃ ρ : Equiv.Perm (Fin 42), (ρ = r₁ ∨ ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
      ∃ c ∈ R, r = c * ρ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact ⟨r₁, Or.inl rfl, eq_conj_of_isConj h⟩
    · exact ⟨r₂, Or.inr (Or.inl rfl), eq_conj_of_isConj h⟩
    · exact ⟨r₃, Or.inr (Or.inr (Or.inl rfl)), eq_conj_of_isConj h⟩
    · exact ⟨r₄, Or.inr (Or.inr (Or.inr rfl)), eq_conj_of_isConj h⟩
  obtain ⟨ρ, hρ, c, hcR, hc⟩ := hconj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q, hS', hsurj', by rw [hker', hqker],
    by rw [hker']; exact h3, ρ, Or.inr hρ, fun e => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr e, hc]
  group

omit [Finite X] in
theorem range_imageHom_le {K L : Subgroup X} (hLK : L ≤ K) {x : X}
    (hxN : x ∈ normalizer (K : Set X)) (hLx : L ≤ centralizer ({x} : Set X))
    {q : Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) {ρ : Equiv.Perm (Fin 42)}
    (hβ : ∀ e, q (betaHat K hxN e) = ρ * q e * ρ⁻¹) :
    (imageHom hLK q).range ≤ centralizer {ρ} ⊓ S := by
  rintro _ ⟨s, rfl⟩
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hqS _⟩
  have hfix : betaHat K hxN (jq K ⟨s, hLK s.2⟩) = jq K ⟨s, hLK s.2⟩ := by
    rw [betaHat_mk]
    congr 1
    exact Subtype.ext (conj_eq_of_mem_centralizer (hLx s.2))
  have h1 := hβ (jq K ⟨s, hLK s.2⟩)
  rw [hfix] at h1
  show q (jq K ⟨s, hLK s.2⟩) * ρ = ρ * q (jq K ⟨s, hLK s.2⟩)
  calc q (jq K ⟨s, hLK s.2⟩) * ρ = ρ * q (jq K ⟨s, hLK s.2⟩) * ρ⁻¹ * ρ := by rw [← h1]
    _ = ρ * q (jq K ⟨s, hLK s.2⟩) := by group

theorem false_of_range_eq_bot {K L : Subgroup X} (hLK : L ≤ K) {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) {Y : Type*} [Group Y]
    (q : Jhat K →* Y) (hqker : q.ker = center (Jhat K)) (hbot : (imageHom hLK q).range = ⊥) :
    False := by
  have h3 : 3 ≤ Nat.card F := by
    have h1 := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) e q
    hqker
  rw [hbot, Subgroup.card_bot, mul_one, card_sl2] at h
  exact not_dvd_two_of_three_le h3 h

theorem false_of_le_solvable {K L : Subgroup X} (hLK : L ≤ K) (hL : ⁅L, L⁆ = L) {F : Type*}
    [Field F] [Finite F] (hodd : Odd (Nat.card F)) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    {Y : Type*} [Group Y] (q : Jhat K →* Y) (hqker : q.ker = center (Jhat K)) {C : Subgroup Y}
    (hC : Group.IsSolvable C) (hle : (imageHom hLK q).range ≤ C) : False :=
  false_of_range_eq_bot hLK hodd e q hqker
    (eq_bot_of_perfect_of_le hle (commutator_range_imageHom hLK q hL) hC)

end CFSG.ComponentClassification.TBLit.L34P
