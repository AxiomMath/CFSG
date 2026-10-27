module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6A3Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLEquiv

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.WeakCT (spBlock hom_ext_sl2 blk exists_spMap spMap_comp_spBlock
  map_blk map_map_symm map_symm_map DoubleBondDiagram doubleBondDiagram_f4 edgeUp)
open scoped MatrixGroups Matrix

section Family

variable (K : Type) [Field K]

theorem commute_e6_sl2_two_four
    (A B : SL(2, K)) :
    Commute (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩ A)
      (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩ B) :=
  commute_simpleRootSL2_of_orth (t := TwistTag.E6) (by decide) (by decide) A B

theorem commute_e6_sl2_zero_five
    (A B : SL(2, K)) :
    Commute (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩ A)
      (simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩ B) :=
  commute_simpleRootSL2_of_orth (t := TwistTag.E6) (by decide) (by decide) A B

@[expose] def e6F4Rho
    :
    Fin 4 → SL(2, K) →* ModGL TwistTag.E6.tag K :=
  ![simpleRootSL2 TwistTag.E6.tag K ⟨1, by decide⟩, simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩,
    pairHom (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩)
      (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩) (commute_e6_sl2_two_four K),
    pairHom (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩)
      (simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩) (commute_e6_sl2_zero_five K)]

end Family

section Recognition

variable {K : Type} [Field K] [Finite K]

theorem f4_nadj_cases : ∀ i j : Fin 4, i ≠ j → ¬ edgeUp 4 i j → ¬ edgeUp 4 j i →
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
  decide

theorem f4_single_cases : ∀ i j : Fin 4, edgeUp 4 i j → ¬ (i = 1 ∧ j = 2) →
    (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) := by
  decide

omit [Finite K] in
theorem commute_e6F4Rho
    {i j : Fin 4} (hij : i ≠ j) (h1 : ¬ edgeUp 4 i j) (h2 : ¬ edgeUp 4 j i) (A B : SL(2, K)) :
    Commute (e6F4Rho K i A) (e6F4Rho K j B) := by
  have c : ∀ a b : Fin 6, a ≠ b → (Pi.single a 1 : Fin 6 → ℤ) ⬝ᵥ
      (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single b 1 : Fin 6 → ℤ)) = 0 →
      ∀ A B : SL(2, K), Commute (simpleRootSL2 TwistTag.E6.tag K a A)
        (simpleRootSL2 TwistTag.E6.tag K b B) := fun a b hab h0 A B =>
    commute_simpleRootSL2_of_orth (t := TwistTag.E6) hab h0 A B
  rcases f4_nadj_cases i j hij h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (c 1 2 (by decide) (by decide) A B).mul_right (c 1 4 (by decide) (by decide) A B)
  · exact ((c 1 2 (by decide) (by decide) B A).mul_right
      (c 1 4 (by decide) (by decide) B A)).symm
  · exact (c 1 0 (by decide) (by decide) A B).mul_right (c 1 5 (by decide) (by decide) A B)
  · exact ((c 1 0 (by decide) (by decide) B A).mul_right
      (c 1 5 (by decide) (by decide) B A)).symm
  · exact (c 3 0 (by decide) (by decide) A B).mul_right (c 3 5 (by decide) (by decide) A B)
  · exact ((c 3 0 (by decide) (by decide) B A).mul_right
      (c 3 5 (by decide) (by decide) B A)).symm

theorem exists_e6F4_short_sl3
    :
    ∃ ψ : SL(3, K) →* ModGL TwistTag.E6.tag K,
      ψ.comp (blk K 0) = e6F4Rho K 2 ∧ ψ.comp (blk K 1) = e6F4Rho K 3 := by
  obtain ⟨ψa, ha0, ha1⟩ := exists_e6_sl3 K (i := ⟨2, by decide⟩) (j := ⟨0, by decide⟩)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ψb, hb0, hb1⟩ := exists_e6_sl3 K (i := ⟨4, by decide⟩) (j := ⟨5, by decide⟩)
    (by decide) (by decide) (by decide) (by decide)
  have hca : ψa.range ≤ (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩).range ⊔
      (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩).range :=
    range_le_of_blk ψa (by rw [ha0]; exact le_sup_left) (by rw [ha1]; exact le_sup_right)
  have hcb : ψb.range ≤ (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩).range ⊔
      (simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩).range :=
    range_le_of_blk ψb (by rw [hb0]; exact le_sup_left) (by rw [hb1]; exact le_sup_right)
  have c : ∀ a b : Fin 6, a ≠ b → (Pi.single a 1 : Fin 6 → ℤ) ⬝ᵥ
      (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single b 1 : Fin 6 → ℤ)) = 0 →
      ∀ A B : SL(2, K), Commute (simpleRootSL2 TwistTag.E6.tag K a A)
        (simpleRootSL2 TwistTag.E6.tag K b B) := fun a b hab h0 A B =>
    commute_simpleRootSL2_of_orth (t := TwistTag.E6) hab h0 A B
  have hab : ∀ A B, Commute (ψa A) (ψb B) := by
    intro A B
    have hA := hca ⟨A, rfl⟩
    have hB := hcb ⟨B, rfl⟩
    rw [Subgroup.sup_eq_closure] at hA hB
    refine commute_of_mem_closure ?_ hA hB
    rintro _ (⟨A', rfl⟩ | ⟨A', rfl⟩) _ (⟨B', rfl⟩ | ⟨B', rfl⟩)
    · exact c 2 4 (by decide) (by decide) A' B'
    · exact c 2 5 (by decide) (by decide) A' B'
    · exact c 0 4 (by decide) (by decide) A' B'
    · exact c 0 5 (by decide) (by decide) A' B'
  refine ⟨pairHom ψa ψb hab, MonoidHom.ext fun A => ?_, MonoidHom.ext fun A => ?_⟩
  · rw [MonoidHom.comp_apply, pairHom_apply, ← MonoidHom.comp_apply ψa, ha0,
      ← MonoidHom.comp_apply ψb, hb0]
    rfl
  · rw [MonoidHom.comp_apply, pairHom_apply, ← MonoidHom.comp_apply ψa, ha1,
      ← MonoidHom.comp_apply ψb, hb1]
    rfl

theorem e6F4_frame_recognition
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(⨆ k, (e6F4Rho K k).range) ∧
      LieModel (↥(⨆ k, (e6F4Rho K k).range) ⧸ Subgroup.center ↥(⨆ k, (e6F4Rho K k).range))
        .F4 0 p f := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, hq3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .F4 0 p f := ⟨hp, hf, rfl⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hGF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨e⟩ : Nonempty (K ≃+* GaloisField p f) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hGF])⟩
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p f) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (f4Datum (GaloisField p f)).isFiniteType
    (Dv := (f4Datum (GaloisField p f)).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula (GaloisField p f) O
  have hE := f4_chevalleyExtras (GaloisField p f) O C hC
  have hsq : ∀ k : Fin (Tag.rank .F4),
      Steinberg.weylElement (f4Par (GaloisField p f)) k 1 ^ 2 ∈
        Steinberg.Adjoint.torus (τ := .F4) (GaloisField p f) k := by
    intro k
    have h := (f4_isCTGroupDatum (GaloisField p f)).sq_mem k
    rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .F4) k] at h
    exact h
  obtain ⟨Ψ, -, -, hqs, hlie, -⟩ := weakCT_of_frame_dl_subgroup_equiv e
    (CurtisTits.curtisTitsConclusion_f4 p f hadm) (leviConePresented_f4 _) hE rfl
    (isQuasisimple_statedSp_two (by rw [hGF, ← hK]; exact hq3)) h2 doubleBondDiagram_f4
    (f4_steinbergExtras (GaloisField p f)).torus_iSupIndep hsq
    (U := fun k => (e6F4Rho K k).range)
    (fun i j hne h1 h2 u hu v hv => by
      obtain ⟨A, rfl⟩ := hu
      obtain ⟨B, rfl⟩ := hv
      exact (commute_e6F4Rho hne h1 h2 A B).eq)
    (ρ := e6F4Rho K) (fun k => rfl) (simpleRootSL2_injective hK2 _)
    (fun i j hij hne => by
      rcases f4_single_cases i j hij hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact exists_e6_sl3 K (i := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) (by decide) (by decide)
          (by decide) (by decide)
      · exact exists_e6F4_short_sl3)
    (exists_e6_sp4 hp hp2 hK (commute_e6_sl2_two_four K))
  exact ⟨hqs, hlie⟩

end Recognition

end CFSG.ComponentClassification.CatLeafProof
