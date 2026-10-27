module

import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpCount
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmProof

open CFSG.Open Matrix

abbrev OmI : Type := Fin 3 ⊕ Fin 3 ⊕ Fin 2

section Form

variable {F : Type} [Field F]

theorem quadMinus_apply (b c : F) (v : OmI → F) :
    StatedQuadMinus 4 F b c v = ∑ i : Fin 3, v (.inl i) * v (.inr (.inl i)) +
      v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2 := rfl

@[expose] def isoGrp {ι : Type} [Fintype ι] [DecidableEq ι] (Q₀ : (ι → F) → F) : Subgroup (GL ι F) where
  carrier := {A | ∀ v, Q₀ ((A : Matrix ι ι F) *ᵥ v) = Q₀ v}
  one_mem' := fun v => by simp
  mul_mem' := fun {A B} hA hB v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  inv_mem' := fun {A} hA v => by
    have := hA ((↑A⁻¹ : Matrix ι ι F) *ᵥ v)
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, eq_comm] at this

theorem statedOmega_le_isoGrp {ι : Type} [Fintype ι] [DecidableEq ι] (Q₀ : (ι → F) → F) :
    StatedOmega Q₀ ≤ isoGrp Q₀ := by
  have hcl : Subgroup.closure {A : GL ι F | ∀ v, Q₀ ((A : Matrix ι ι F) *ᵥ v) = Q₀ v} ≤
      isoGrp Q₀ := Subgroup.closure_le _ |>.mpr fun A hA => hA
  refine le_trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) hcl
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
    (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)

end Form

section Scalars

variable {F : Type} [Field F] [CharP F 2] {b c : F}

@[expose] def eU : OmI → F := Pi.single (Sum.inr (Sum.inr 0)) 1

theorem quadMinus_eU : StatedQuadMinus 4 F b c eU = 1 := by
  rw [quadMinus_apply]
  simp [eU, Pi.single_apply, Fin.sum_univ_three]

theorem scalars_subgroupOf_omega :
    (StatedScalars OmI F).subgroupOf (StatedOmega (StatedQuadMinus 4 F b c)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨u, hu⟩ := (Subgroup.mem_subgroupOf.1 hA :
    (A : GL OmI F) ∈ StatedScalars OmI F)
  have h1 := statedOmega_le_isoGrp (StatedQuadMinus 4 F b c) A.2 eU
  have h2 : ((A : GL OmI F) : Matrix OmI OmI F) *ᵥ eU = (u : F) • eU := by
    rw [← hu]
    ext i
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
  rw [h2] at h1
  have hq : ∀ (t : F) (v : OmI → F), StatedQuadMinus 4 F b c (t • v) =
      t ^ 2 * StatedQuadMinus 4 F b c v := by
    intro t v
    simp only [quadMinus_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  rw [hq, quadMinus_eU, mul_one] at h1
  have hu1 : (u : F) = 1 := K421SpProof.sq_eq_one_F F h1
  have hA1 : (A : GL OmI F) = 1 := by
    rw [← hu]
    have : u = 1 := Units.ext hu1
    rw [this, map_one]
  exact Subtype.ext hA1

noncomputable def projEquivOmega :
    StatedProj (StatedOmega (StatedQuadMinus 4 F b c)) ≃* ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
  (QuotientGroup.quotientMulEquivOfEq scalars_subgroupOf_omega).trans QuotientGroup.quotientBot

end Scalars

section Transport

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem b_ne_zero {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  subst hb
  haveI := Fintype.ofFinite F
  obtain ⟨r, hr⟩ := K421SpCountProof.spc_sq_exists (F := F) c
  have h2 := K421SpProof.two_eq_zero_F F
  exact hirr r (by linear_combination hr + c * h2)

theorem exists_model {c : ℕ → Prop} {S : Type} [Group S] (h : IsOmegaEightMinus c S) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (b d : F),
      (∀ s : F, s ^ 2 + b * s + d ≠ 0) ∧ c (Nat.card F) ∧ (∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f) ∧
        Nat.card S = ordTwistedD 4 (Nat.card F) ∧
        Nonempty (S ≃* ↥(StatedOmega (StatedQuadMinus 4 F b d))) := by
  obtain ⟨Q, hQ2, hc, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 Q hv hQ2 e
  rw [hQ2] at hm
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.2 rfl
  obtain ⟨-, K, hKf, hKfin, hK, b, d', hirr, ⟨e'⟩⟩ := hm
  haveI := charP_two_of_card_pow hK
  refine ⟨K, hKf, hKfin, this, b, d', hirr, ?_, ⟨Q.exponent, Q.exponent_pos, hK⟩, ?_,
    ⟨e'.trans projEquivOmega⟩⟩
  · rw [hK]
    have h1 := TauCeti.PrimePower.card_def Q
    rw [hQ2] at h1
    rw [← h1]
    exact hc
  · rw [hK]
    exact hcard

theorem ordTwistedD_four_eq {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) :
    ordTwistedD 4 (Nat.card F) =
      (Nat.card F ^ 7 + Nat.card F ^ 3) * Nat.card (StatedSp 3 F) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 3, ordTwistedD]
  have hodd : Odd (Nat.card F ^ 4 + 1) := by
    rw [hF, Nat.odd_iff]
    have h2 : 2 ∣ (2 ^ f) ^ 4 := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
    omega
  have hgcd : Nat.gcd 4 (Nat.card F ^ 4 + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  rw [hgcd, Nat.div_one]
  show Nat.card F ^ (4 * (4 - 1)) * (Nat.card F ^ 4 + 1) *
      ∏ i ∈ Finset.Icc 1 (4 - 1), (Nat.card F ^ (2 * i) - 1) = _
  norm_num
  ring

end Transport

end K421OmProof

end CFSG.LocalAnalysis.RankThreeUC.S15
