module

public import CFSG.LieType.Chevalley.SignStabilizerDataG2
public import CFSG.LieType.Chevalley.SignStabilizerDataF4
public import CFSG.LieType.Chevalley.SignStabilizerDataD4
public import CFSG.LieType.Chevalley.SignStabilizerDataE6
public import CFSG.LieType.Chevalley.SignStabilizerDataE7
public import CFSG.LieType.Chevalley.SignStabilizerDataE8

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

abbrev CharQuotient
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    Type :=
  charStabilizer χ ⧸ (kernelWeylGroup χ).subgroupOf (charStabilizer χ)

theorem card_charQuotient_le_of_orbitCheck
    {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hO : OrbitCheck τ reps entries) {B : ℕ}
    (hB : ∀ ρ < reps.length,
      Nat.card (kernelPosStabilizer (maskChar (τ := τ) (listMask (reps.getD ρ [])))) ≤ B)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : Nat.card (CharQuotient χ) ≤ B := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck hO χ
  rw [← Nat.card_congr (quotientMulEquivOfIsCharConj ht).toEquiv]
  exact card_quotient_le_card_kernelPosStabilizer.trans (hB ρ hρ)

theorem charQuotient_comm_sq_of_kernelPosStabilizer
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (h : ∀ ω ω' : WeylGroup τ, ω ∈ kernelPosStabilizer χ → ω' ∈ kernelPosStabilizer χ →
      ω * ω' = ω' * ω ∧ ω * ω = 1) (q q' : CharQuotient χ) : q * q' = q' * q ∧ q * q = 1 := by
  obtain ⟨⟨ω, hω⟩, rfl⟩ := surjective_kernelPosStabilizer (χ := χ) q
  obtain ⟨⟨ω', hω'⟩, rfl⟩ := surjective_kernelPosStabilizer (χ := χ) q'
  obtain ⟨h1, h2⟩ := h ω ω' hω hω'
  refine ⟨?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext h1)
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    exact congrArg _ (Subtype.ext h2)

theorem charQuotient_comm_sq_of_orbitCheck
    {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hO : OrbitCheck τ reps entries)
    (hE : ∀ ρ < reps.length, ∀ ω ω' : WeylGroup τ,
      ω ∈ kernelPosStabilizer (maskChar (listMask (reps.getD ρ []))) →
      ω' ∈ kernelPosStabilizer (maskChar (listMask (reps.getD ρ []))) →
        ω * ω' = ω' * ω ∧ ω * ω = 1)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (q q' : CharQuotient χ) :
    q * q' = q' * q ∧ q * q = 1 := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck hO χ
  set e := quotientMulEquivOfIsCharConj ht
  obtain ⟨p, rfl⟩ := e.surjective q
  obtain ⟨p', rfl⟩ := e.surjective q'
  obtain ⟨h1, h2⟩ := charQuotient_comm_sq_of_kernelPosStabilizer (hE ρ hρ) p p'
  exact ⟨by rw [← map_mul, ← map_mul, h1], by rw [← map_mul, h2, map_one]⟩

theorem charStabilizer_eq_of_card_le_one
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (h : Nat.card (CharQuotient χ) ≤ 1) :
    charStabilizer χ = kernelWeylGroup χ := by
  refine le_antisymm (fun w hw => ?_) kernelWeylGroup_le
  have hpos : 0 < Nat.card (CharQuotient χ) := Nat.card_pos
  have hidx : ((kernelWeylGroup χ).subgroupOf (charStabilizer χ)).index = 1 :=
    le_antisymm h hpos
  rw [Subgroup.index_eq_one] at hidx
  have : (⟨w, hw⟩ : charStabilizer χ) ∈ (kernelWeylGroup χ).subgroupOf (charStabilizer χ) := by
    rw [hidx]
    trivial
  exact this

theorem sign_character_Weyl_stabilizer_quotients
    (τ : Tag)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    kernelWeylGroup χ ≤ charStabilizer χ ∧
    ((kernelWeylGroup χ).subgroupOf (charStabilizer χ)).Normal ∧
    ((τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) → charStabilizer χ = kernelWeylGroup χ) ∧
    (τ = .E7 → Nat.card (CharQuotient χ) ∣ 2) ∧
    (τ = .D4 → Nat.card (CharQuotient χ) ∣ 4 ∧ CFSG.IsElementaryAbelian 2 (CharQuotient χ)) := by
  refine ⟨kernelWeylGroup_le, inferInstance, ?_, ?_, ?_⟩
  · rintro (rfl | rfl | rfl | rfl)
    · exact charStabilizer_eq_of_card_le_one
        (card_charQuotient_le_of_orbitCheck g2SignOrbit_check card_kernelPosStabilizer_le_G2 χ)
    · exact charStabilizer_eq_of_card_le_one
        (card_charQuotient_le_of_orbitCheck f4SignOrbit_check card_kernelPosStabilizer_le_F4 χ)
    · exact charStabilizer_eq_of_card_le_one
        (card_charQuotient_le_of_orbitCheck e6SignOrbit_check card_kernelPosStabilizer_le_E6 χ)
    · exact charStabilizer_eq_of_card_le_one
        (card_charQuotient_le_of_orbitCheck e8SignOrbit_check card_kernelPosStabilizer_le_E8 χ)
  · rintro rfl
    have h := card_charQuotient_le_of_orbitCheck e7SignOrbit_check card_kernelPosStabilizer_le_E7 χ
    have hpos : 0 < Nat.card (CharQuotient χ) := Nat.card_pos
    interval_cases (Nat.card (CharQuotient χ)) <;> decide
  · rintro rfl
    have h := card_charQuotient_le_of_orbitCheck d4SignOrbit_check card_kernelPosStabilizer_le_D4 χ
    have hcs := charQuotient_comm_sq_of_orbitCheck d4SignOrbit_check
      kernelPosStabilizer_comm_sq_D4 χ
    have hEA : CFSG.IsElementaryAbelian 2 (CharQuotient χ) :=
      { is_comm := ⟨fun a b => (hcs a b).1⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
          rw [pow_two]
          exact (hcs g g).2 }
    refine ⟨?_, hEA⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := CharQuotient χ)).1 (fun g =>
      ⟨1, by rw [pow_one, pow_two]; exact (hcs g g).2⟩)
    rw [hn] at h ⊢
    have hn2 : n ≤ 2 := by
      by_contra hn'
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> decide

end CFSG.LieType.Chevalley
