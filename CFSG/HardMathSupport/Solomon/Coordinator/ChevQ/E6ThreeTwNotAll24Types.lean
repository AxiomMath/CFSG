module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLine

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

section Types

set_option linter.unusedSectionVars false

structure TwE6Cube (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) : Prop where
  char_ne_three : ringChar K ≠ 3
  frob : ∀ c, σ c = c ^ q
  card_field : Nat.card K = q ^ 2
  three_dvd : 3 ∣ q + 1
  ne_two : q ≠ 2
  elemAbelian : IsElemAbelian 3 E
  card_E : Nat.card E = 3 ^ 3
  le_inndiag : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  not_le_inn : ¬ E ≤ twistedE6Inn K σ
  not_normalizesR : ¬ TwE6NormalizesR K σ E

@[expose] def TwE6LineDim (K : Type) [Field K] (σ : K ≃+* K)
    (f : MulAut (twistedE6RootGroup K σ)) (d : ℕ) : Prop :=
  ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧ twE6MatFixDim K σ h = d

@[expose] def TwE6LineComponentsAt (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (f : MulAut (twistedE6RootGroup K σ)) :
    Prop :=
  ∀ J : Subgroup (twistedE6RootGroup K σ),
    CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) →
      (∀ g ∈ E, J.map g.toMonoidHom = J) ∧ TwE6ComponentType J

@[expose] def TwE6LineGenAt (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (f : MulAut (twistedE6RootGroup K σ)) :
    Prop :=
  fixedPoints (Subgroup.zpowers f) ≤
    sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut (twistedE6RootGroup K σ)))
        (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F

@[expose] def TwE6LineStructureAt (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (f : MulAut (twistedE6RootGroup K σ)) :
    Prop :=
  TwE6LineComponentsAt K σ E f ∧ TwE6LineGenAt K σ E f

@[expose] def TwE6LineStructure' : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → (∀ s : twistedE6RootGroup K σ, f = MulAut.conj s → twE6FixDim K σ s ≠ 24) →
        (q = 8 → ∀ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f →
          twE6MatFixDim K σ h ≠ 28) →
        TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureD4In : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → f ∈ twistedE6Inn K σ → TwE6LineDim K σ f 30 → TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureD4Out : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → f ∉ twistedE6Inn K σ → TwE6LineDim K σ f 30 →
        TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureA2Out : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → f ∉ twistedE6Inn K σ → TwE6LineDim K σ f 24 →
        TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureA5 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 36 → TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureA1A4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E → q ≠ 8 →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 28 → TwE6LineStructureAt K σ E f

@[expose] def TwE6LineStructureD5 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 46 → TwE6LineStructureAt K σ E f

theorem twE6LineStructure'_of_types (hD : TwE6Order3Dim) (hD4In : TwE6LineStructureD4In)
    (hD4Out : TwE6LineStructureD4Out) (hA2Out : TwE6LineStructureA2Out)
    (hA5 : TwE6LineStructureA5) (hA1A4 : TwE6LineStructureA1A4) (hD5 : TwE6LineStructureD5) :
    TwE6LineStructure' := by
  intro K _ _ σ q E hcube f hfE hf1 hty hex
  obtain ⟨h, hh, hh1, hdim⟩ := twE6MatFixDim_mem_of_mem hD K σ q hcube.char_ne_three
    hcube.frob hcube.card_field hcube.three_dvd hcube.ne_two hcube.elemAbelian
    hcube.le_inndiag hfE hf1
  have hLD : ∀ d, twE6MatFixDim K σ h = d → TwE6LineDim K σ f d := fun d hd => ⟨h, hh, hd⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdim
  rcases hdim with h24 | h28 | h30 | h36 | h46
  ·
    have hout : f ∉ twistedE6Inn K σ := by
      rintro ⟨s, hs⟩
      have hq2 : 2 ≤ q := by
        have := Nat.le_of_dvd (by omega) hcube.three_dvd
        omega
      have hfd := twE6MatFixDim_of_inner K σ q hcube.frob hcube.card_field hq2 s h
        (hh.trans hs.symm)
      exact hty s hs.symm (hfd ▸ h24)
    exact hA2Out K σ q E hcube f hfE hf1 hout (hLD 24 h24)
  · have hq8 : q ≠ 8 := fun hq => hex hq h hh h28
    exact hA1A4 K σ q E hcube hq8 f hfE hf1 (hLD 28 h28)
  · by_cases hin : f ∈ twistedE6Inn K σ
    · exact hD4In K σ q E hcube f hfE hf1 hin (hLD 30 h30)
    · exact hD4Out K σ q E hcube f hfE hf1 hin (hLD 30 h30)
  · exact hA5 K σ q E hcube f hfE hf1 (hLD 36 h36)
  · exact hD5 K σ q E hcube f hfE hf1 (hLD 46 h46)

end Types

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
