module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def NormalizesRNative (τ : Tag) (K : Type) [Field K]
    (E₀ : Subgroup (adjointGroup τ K)) : Prop :=
  NormalizesRIn (ringChar K) E₀

@[expose] def F4ThreeNative (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .F4 K E₀ →
        Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

structure LangPlaneData (τ : Tag) (K : Type) [Field K] [Finite K]
    (A : Subgroup (adjointGroup τ K)) where
  w : WeylGroup τ
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g0 : ModGL τ (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)
  hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w
  c : adjointGroup τ K
  hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
    (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

@[expose] def LangPlaneData.Kills {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) (α : Fin τ.rank → ℤ) : Prop :=
  ∀ x ∈ A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
    rootDiagUnit τ a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 ∧ rootChar a α = 1

@[expose] def LangToralOrParabolic (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
      Nonempty (LangPlaneData τ K A) ∨ NormalizesRNative τ K A

@[expose] def zSplit (K : Type) [Field K] (ω : Kˣ) : adjointGroup Tag.F4 K :=
  ⟨rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω),
    torusGroup_le_adjointGroup_F4 (F4_rootDiagUnit_mem_torusGroup _)⟩

@[expose] def LangPlaneKillsRoot (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (A : Subgroup (adjointGroup τ K)) (D : LangPlaneData τ K A)
    (α : Fin τ.rank → ℤ), IsRoot τ α → D.Kills α →
      ∃ u : adjointGroup τ K, u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ ∀ x ∈ A, Commute u x

@[expose] def LangPlaneKilled (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
      ∀ D : LangPlaneData τ K A, ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ D.Kills α

@[expose] def F4PureSplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 → ∀ ω : Kˣ, orderOf ω = 3 →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ∀ D : LangPlaneData .F4 K E₀, (∀ α, IsRoot .F4 α → ¬ D.Kills α) →
        ∀ e ∈ E₀, e ≠ 1 → ∃ g : adjointGroup .F4 K, g * e * g⁻¹ = zSplit K ω

@[expose] def F4PureTwisted : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 3 ≤ Nat.card K →
    ∀ (D₁ : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D₁.Lˣ), orderOf ω = 3 →
    ∀ z : adjointGroup TwClass.f4Six.tag K,
      baseChangeGL (algebraMap K D₁.L) (z : ModGL TwClass.f4Six.tag K) =
        D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
          TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹ →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ∀ D : LangPlaneData .F4 K E₀, (∀ α, IsRoot .F4 α → ¬ D.Kills α) →
        ∀ e ∈ E₀, e ≠ 1 → ∃ g : adjointGroup .F4 K, g * e * g⁻¹ = z

@[expose] def F4RegularSolvable (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ∀ D : LangPlaneData .F4 K E₀, (∀ α, IsRoot .F4 α → ¬ D.Kills α) →
        Group.IsSolvable ↥(Subgroup.centralizer (E₀ : Set (adjointGroup .F4 K)))

@[expose] def F4ThreeTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .F4 K E₀ → planeCl E₀ = ⊤

@[expose] def E6HighInF4 (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .E6 K E₀ →
      ∃ (g : adjointGroup .E6 K) (ι : adjointGroup .F4 K →* adjointGroup .E6 K)
        (E₃ : Subgroup (adjointGroup .F4 K)),
        Function.Injective ι ∧ E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom ∧
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((ι.range : Set (adjointGroup .E6 K)) ∪
          (Subgroup.centralizer ({ι e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤

@[expose] def TwE6HighInF4 (ε : ℕ) : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = ε →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ →
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (g : twistedE6RootGroup K σ)
        (ι : adjointGroup .F4 k →* twistedE6RootGroup K σ) (E₃ : Subgroup (adjointGroup .F4 k)),
        Nat.card k = q ∧ ringChar k = ringChar K ∧ Function.Injective ι ∧
        E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom ∧
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((ι.range : Set (twistedE6RootGroup K σ)) ∪
          (Subgroup.centralizer ({ι e} : Set (twistedE6RootGroup K σ)) :
            Set (twistedE6RootGroup K σ))) = ⊤

end CFSG.LieType.SeitzGeneration.ExcHighThree
