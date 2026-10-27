module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open scoped MatrixGroups

theorem e8Ten_arith {p q : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf (q : ZMod p) = 10) :
    7 < p ∧ ¬ p ∣ q ∧
      (-(q : ZMod p)) ^ 4 + (-(q : ZMod p)) ^ 3 + (-(q : ZMod p)) ^ 2 + (-(q : ZMod p)) + 1 =
        0 ∧
      (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hx] at he ⊢
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one x
    rw [he, h0] at h1
    simp at h1
  have h10 : x ^ 10 = 1 := by simpa [he] using pow_orderOf_eq_one x
  have h5ne : x ^ 5 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [he]; norm_num)
  have h2ne : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [he]; norm_num)
  have h5 : x ^ 5 + 1 = 0 := by
    have h : (x ^ 5 - 1) * (x ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) h5ne
    · exact h
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply h2ne
    linear_combination (x - 1) * h
  have hΦ : x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0 := by
    have h : (x + 1) * (x ^ 4 - x ^ 3 + x ^ 2 - x + 1) = 0 := by linear_combination h5
    exact (mul_eq_zero.1 h).resolve_left hx1
  have hdvd : 10 ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hp7' : 7 < p := by omega
  refine ⟨hp7', fun hdvd' => hx0 (hx ▸ (ZMod.natCast_eq_zero_iff q p).2 hdvd'), ?_, ?_⟩
  · linear_combination hΦ
  · refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
    push_cast
    rw [← hx]
    exact hΦ

theorem e8Ten_dvd_pow_five_add_one {p q : ℕ}
    (h : (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    p ∣ q ^ 5 + 1 := by
  have h2 : (p : ℤ) ∣ (q : ℤ) ^ 5 + 1 := by
    have : (q : ℤ) ^ 5 + 1 = ((q : ℤ) + 1) *
        ((q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left h _
  exact_mod_cast h2

theorem e8Ten_dvd_su5_order {p : ℕ} (q : ℕ) (hpd : p ∣ q ^ 5 + 1) :
    (p : ℤ) ∣ (q : ℤ) ^ 10 * (((q : ℤ) ^ 2 - 1) * (((q : ℤ) ^ 3 + 1) *
      (((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 5 + 1)))) := by
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ 5 + 1 := by exact_mod_cast hpd
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left h1 _) _) _) _

theorem e8Ten_prod_Icc_two_five (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 5, (Q ^ i - (-1) ^ i) =
      (Q ^ 2 - 1) * ((Q ^ 3 + 1) * ((Q ^ 4 - 1) * (Q ^ 5 + 1))) := by
  have e : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  rw [e]
  simp

theorem e8Ten_p_dvd_card_of_unitary_family {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {p : ℕ} (hpd : p ∣ Nat.card K ^ 5 + 1) {G : Type*} [Group G] (ρ : SL(5, L) →* G)
    (hρ : Function.Injective ρ) (Pt : Subgroup G) [Finite Pt] (H : SL(5, L))
    (hH : ∀ Z : SL(5, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 5,
        Matrix.SpecialLinearGroup.toGL Z = Matrix.SpecialLinearGroup.toGL H * Y *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) → ρ Z ∈ Pt) :
    p ∣ Nat.card Pt := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hU : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, hq2]⟩
  have hcard : (Nat.card (StatedSU 5 (ℓ ^ f) F) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 10 *
      ((((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * ((((ℓ ^ f : ℕ) : ℤ) ^ 3 + 1) *
        ((((ℓ ^ f : ℕ) : ℤ) ^ 4 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 5 + 1)))) := by
    have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 5) (by norm_num)
    rw [e8Ten_prod_Icc_two_five] at h
    simpa using h
  have hpdvd : p ∣ Nat.card (StatedSU 5 (ℓ ^ f) F) := by
    have hpd' : p ∣ (ℓ ^ f) ^ 5 + 1 := hK ▸ hpd
    have h1 := e8Ten_dvd_su5_order (ℓ ^ f) hpd'
    rw [← hcard] at h1
    exact_mod_cast h1
  let Ψ : StatedSU 5 (ℓ ^ f) F →* SL(5, L) := statedSUToSL F 5 (ℓ ^ f)
  let φ : StatedSU 5 (ℓ ^ f) F →* G := ρ.comp ((MulAut.conj H).toMonoidHom.comp Ψ)
  have hφinj : Function.Injective φ := fun Y Z h =>
    statedSUToSL_injective F 5 (ℓ ^ f) ((MulAut.conj H).injective (hρ h))
  rw [hK] at hH
  have hφP : ∀ Y, φ Y ∈ Pt := by
    intro Y
    have hY := (mem_range_statedSUToSL_iff hℓ F hF hFcard (by norm_num) (Ψ Y)).mp ⟨Y, rfl⟩
    apply hH ((MulAut.conj H).toMonoidHom (Ψ Y))
    refine ⟨Matrix.SpecialLinearGroup.toGL (Ψ Y), hY, ?_⟩
    simp [MulAut.conj_apply]
  have hle : φ.range ≤ Pt := by
    rintro _ ⟨Y, rfl⟩
    exact hφP Y
  have hcardφ : Nat.card φ.range = Nat.card (StatedSU 5 (ℓ ^ f) F) :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  rw [← hcardφ] at hpdvd
  exact hpdvd.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
