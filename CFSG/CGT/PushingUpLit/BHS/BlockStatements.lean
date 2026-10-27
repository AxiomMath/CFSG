module

public import CFSG.CGT.PushingUpLit.BHS.CStar
public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.Quasithin.Background.G6Natural

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.Quasithin.G6 CFSG.Quasithin.A1b
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure IsBTBlock (G T E : Subgroup Γ) : Prop where
  le : E ≤ G
  residual : oResidualTwo ↥E = ⊤
  commutator : ⁅E, baum T⁆ = E
  perfect : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E
  elemAbelian : (∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x) ∧
    ∀ x ∈ pCoreOf 2 E, x ^ 2 = 1
  nonCentral : ⁅E, omegaOneCenterOf T⁆ ≠ ⊥
  type : (∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∨
    ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m

@[expose] def btBlocks (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | IsBTBlock G T E}

@[expose] def btBlocksG (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | ∃ g ∈ G, IsBTBlock G (conjSub g T) E}

@[expose] def btBlocksMax (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | E ∈ btBlocksG G T ∧ ∀ F ∈ btBlocksG G T, E ≤ F → F = E}

@[expose] def btBlocksMaxT (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  btBlocksMax G T ∩ btBlocks G T

@[expose] def blockW (E : Subgroup Γ) : Subgroup Γ :=
  ⁅omegaOneCenterOf (pCoreOf 2 E), E⁆

@[expose] def cStarStarIn (G T : Subgroup Γ) : Subgroup Γ :=
  (G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) ⊔
    (G ⊓ Subgroup.normalizer (thompsonJ T : Set Γ))

@[expose] def IsNatSL (E W : Subgroup Γ) (n : ℕ) : Prop :=
  ∃ (φ : ↥E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : ↥W →* Multiplicative (Fin 2 → GaloisField 2 n)),
    Function.Surjective φ ∧ φ.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E ∧
    Function.Surjective ψ ∧ ψ.ker = (W ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf W ∧
    ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
      ψ ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = Multiplicative.ofAdd
        ((φ e : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ w)))

@[expose] def IsNatSym (E W : Subgroup Γ) (m : ℕ) : Prop :=
  ∃ (φ : ↥E →* Equiv.Perm (Fin m)) (ψ : ↥W →* coreMod m),
    Function.Surjective φ ∧ φ.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E ∧
    Function.Surjective ψ ∧ ψ.ker = (W ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf W ∧
    ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
      ψ ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = coreAct m (φ e) (ψ w)

@[expose] def BHSLocalCStar : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T : Subgroup Γ), CharTwo G → IsSylowOf 2 T G →
    cStarIn G T ≠ G →
    ∃ 𝒢 : Set (Subgroup Γ), (∀ E ∈ 𝒢, IsBTBlock G T E) ∧
      (∀ E ∈ 𝒢, ∀ g ∈ G, conjSub g E ∈ 𝒢) ∧
      (∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) ∧
      cStarIn G T ⊔ (⨆ E ∈ 𝒢, E) = G ∧
      (∀ F : Subgroup Γ, IsBTBlock G T F → ¬ F ≤ cStarIn G T → ∃ E ∈ 𝒢, F ≤ E) ∧
      cStarIn G T ⊓ (⨆ E ∈ 𝒢, E) = ⨆ E ∈ 𝒢, cStarIn G T ⊓ E ∧
      ∀ E ∈ 𝒢,
        ((∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∧
          cStarIn G T ⊓ E = Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ) ⊓ E) ∨
        (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
          Nonempty ((((cStarIn G T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
            alternatingGroup (Fin (2 * m))))

@[expose] def BHSLocalCStarStar : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T : Subgroup Γ), CharTwo G → IsMinParabolic2 T G →
    cStarStarIn G T ≠ G →
    ∃ ℰ : Set (Subgroup Γ),
      autOn G (omegaOneCenterOf (pCoreOf 2 G)) =
        autOn (thompsonJ G ⊔ T) (omegaOneCenterOf (pCoreOf 2 G)) ∧
      autOn (thompsonJ G) (omegaOneCenterOf (pCoreOf 2 G)) =
        ⨆ E ∈ ℰ, autOn E (omegaOneCenterOf (pCoreOf 2 G)) ∧
      (∀ E ∈ ℰ, ∀ E' ∈ ℰ, autOn E (omegaOneCenterOf (pCoreOf 2 G)) ≠
          autOn E' (omegaOneCenterOf (pCoreOf 2 G)) →
        ∀ x ∈ autOn E (omegaOneCenterOf (pCoreOf 2 G)),
          ∀ y ∈ autOn E' (omegaOneCenterOf (pCoreOf 2 G)), x * y = y * x) ∧
      sSupIndep ((fun E => autOn E (omegaOneCenterOf (pCoreOf 2 G))) '' ℰ) ∧
      (∀ E ∈ ℰ, ∀ E' ∈ ℰ, ∃ t ∈ T, autOn (conjSub t E) (omegaOneCenterOf (pCoreOf 2 G)) =
        autOn E' (omegaOneCenterOf (pCoreOf 2 G))) ∧
      (∀ E ∈ ℰ, ∀ t ∈ T, ∃ E' ∈ ℰ, autOn (conjSub t E) (omegaOneCenterOf (pCoreOf 2 G)) =
        autOn E' (omegaOneCenterOf (pCoreOf 2 G))) ∧
      omegaOneCenterOf (pCoreOf 2 G) =
        (omegaOneCenterOf (pCoreOf 2 G) ⊓
            Subgroup.centralizer ((⨆ E ∈ ℰ, E : Subgroup Γ) : Set Γ)) ⊔
          ⨆ E ∈ ℰ, ⁅omegaOneCenterOf (pCoreOf 2 G), E⁆ ∧
      (∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → ⁅⁅omegaOneCenterOf (pCoreOf 2 G), E⁆, E'⁆ = ⊥) ∧
      ∀ E ∈ ℰ, (∃ n : ℕ, IsNatSL E ⁅omegaOneCenterOf (pCoreOf 2 G), E⁆ n) ∨
        ∃ n : ℕ, IsNatSym E ⁅omegaOneCenterOf (pCoreOf 2 G), E⁆ (2 ^ n + 1)

end CFSG.CGT.PushingUpLit.BHS
