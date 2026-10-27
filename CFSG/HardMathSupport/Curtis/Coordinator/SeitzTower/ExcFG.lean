module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.E8Diag
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcE

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Ree

section


theorem exists_mulEquiv_adjoint_card {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q.card ∧
      Nonempty (ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃* adjointGroup τ F) := by
  have hF := CFSG.TauCetiBridge.card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (CFSG.TauCetiBridge.fieldOf q 1) hF
  exact ⟨CFSG.TauCetiBridge.fieldOf q 1, inferInstance, inferInstance, hF,
    ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)⟩⟩

theorem outerComm_adjoint_F4 (K : Type) [Field K] [Finite K] :
    OuterComm (adjointGroup .F4 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP K p := finite_field_prime_power_characteristic hp f.pos hK
  by_cases hp2 : p = 2
  · subst hp2
    have : CharP K ReeTag.F4.prime := ‹CharP K 2›
    obtain ⟨Θ, -, -, hker⟩ := (even_F4_exact_automorphism_normal_form f.pos K hK).2.2.1
    exact outerComm_of_hom (fun a b => mul_comm a b) Θ hker.le
  · obtain ⟨Θ, -, -, hker, -⟩ :=
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 f.pos K hK .F4
        (Or.inl rfl)).2
    exact outerComm_of_hom (SeitzNonNormal.ringEquiv_mul_comm_of_finite K) Θ hker.le

theorem outerComm_adjoint_G2 (K : Type) [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) :
    OuterComm (adjointGroup .G2 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP K p := finite_field_prime_power_characteristic hp f.pos hK
  have hchar : ringChar K = p := ringChar.eq K p
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime := ‹CharP K 3›
    obtain ⟨Θ, -, -, hker⟩ := (G2_three_exact_automorphism_normal_form f.pos K hK).2.2.1
    exact outerComm_of_hom (fun a b => mul_comm a b) Θ hker.le
  · have hK4 : 4 ≤ Nat.card K := by
      rcases (show Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h
      · exfalso
        apply hp3
        have hpow : p ^ (f : ℕ) = 3 := by rw [← hK, h]
        have hdvd : p ∣ 3 := by rw [← hpow]; exact dvd_pow_self p (PNat.ne_zero f)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
      · exact h
    obtain ⟨hnf, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form (K := K) (hchar ▸ hp3) hK4
    refine outerComm_of_normalForm
      (Set.range (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K)) ?_ fun α => ?_
    · rintro _ ⟨σ, rfl⟩ _ ⟨σ', rfl⟩
      rw [← map_mul, ← map_mul, SeitzNonNormal.ringEquiv_mul_comm_of_finite]
    · obtain ⟨g, σ, hα⟩ := hnf α
      exact ⟨g, _, ⟨σ, rfl⟩, hα⟩

theorem p1OffCharAlmostSimpleNonNormalAt_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.F4 q, hv⟩ := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm (OuterComm.of_mulEquiv e
    (outerComm_adjoint_F4 F))

theorem p1OffCharAlmostSimpleNonNormalAt_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.G2 q, hv⟩ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjoint_card
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
  have h3 : 3 ≤ Nat.card F := by
    rw [hF]
    exact (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm (OuterComm.of_mulEquiv e
    (outerComm_adjoint_G2 F h3))

end

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
