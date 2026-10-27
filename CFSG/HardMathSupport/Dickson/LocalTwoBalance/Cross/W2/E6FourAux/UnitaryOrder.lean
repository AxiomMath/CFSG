module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open scoped MatrixGroups

theorem e6Four_dvd_su4_order {p : ℕ} (q : ℕ) (hpd : p ∣ q ^ 2 + 1) :
    (p : ℤ) ∣ (q : ℤ) ^ 6 * (((q : ℤ) ^ 2 - 1) * (((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 4 - 1))) := by
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 := by exact_mod_cast hpd
  have h2 : (q : ℤ) ^ 4 - 1 = ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) := by ring
  rw [h2]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right h1 _) _) _) _

theorem e6Four_p_dvd_card_of_unitary_family {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {p : ℕ} (hpd : p ∣ Nat.card K ^ 2 + 1) {G : Type*} [Group G] (ρ : SL(4, L) →* G)
    (hρ : Function.Injective ρ) (Pt : Subgroup G) [Finite Pt] (H : SL(4, L))
    (hH : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
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
  have hcard : (Nat.card (StatedSU 4 (ℓ ^ f) F) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 6 *
      ((((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * ((((ℓ ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((ℓ ^ f : ℕ) : ℤ) ^ 4 - 1))) := by
    have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_two_four] at h
    simpa using h
  have hpdvd : p ∣ Nat.card (StatedSU 4 (ℓ ^ f) F) := by
    have hpd' : p ∣ (ℓ ^ f) ^ 2 + 1 := hK ▸ hpd
    have h1 := e6Four_dvd_su4_order (ℓ ^ f) hpd'
    rw [← hcard] at h1
    exact_mod_cast h1
  let Ψ : StatedSU 4 (ℓ ^ f) F →* SL(4, L) := statedSUToSL F 4 (ℓ ^ f)
  let φ : StatedSU 4 (ℓ ^ f) F →* G := ρ.comp ((MulAut.conj H).toMonoidHom.comp Ψ)
  have hφinj : Function.Injective φ := fun Y Z h =>
    statedSUToSL_injective F 4 (ℓ ^ f) ((MulAut.conj H).injective (hρ h))
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
  have hcardφ : Nat.card φ.range = Nat.card (StatedSU 4 (ℓ ^ f) F) :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  rw [← hcardφ] at hpdvd
  exact hpdvd.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
