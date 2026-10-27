module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentPGU
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Blk
public import CFSG.Quasithin.SteinbergCFCentralSylowInnerOuterBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def IsPR (g : PGU6) : Prop :=
  ∃ (ĝ P : Gu) (a b : F4) (i : Fin 6), (QuotientGroup.mk ĝ : PGU6) = g ∧ a ≠ b ∧
    (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b)

@[expose] def Pat4 (g : PGU6) : Prop :=
  ∃ (ĝ P : Gu) (d : Fin 6 → F4) (c : F4), (QuotientGroup.mk ĝ : PGU6) = g ∧ ĝ ^ 3 = 1 ∧
    (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d ∧
    Fintype.card (Blk d c) = 4 ∧ ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 2

@[expose] def Pat4OfSmall : Prop :=
  ∀ (g : PGU6) (J : Subgroup S6), g ^ 3 = 1 → g ≠ 1 → ¬ IsPR g → J ≤ fixSubgroup (Psi g) →
    ⁅J, J⁆ = J → 5 ∣ Nat.card J → Pat4 g

@[expose] def Pat4Inv : Prop :=
  ∀ g : PGU6, Pat4 g → g ∉ iota.range →
    ∃ t : S6, t ^ 2 = 1 ∧ t ≠ 1 ∧ Psi g t = t ∧
      ∀ J : Subgroup S6, J ≤ fixSubgroup (Psi g) → ⁅J, J⁆ = J → ∀ s ∈ J, s * t = t * s

@[expose] def PRFix : Prop :=
  ∀ g : PGU6, IsPR g →
    IsSimpleGroup ↥(fixSubgroup (Psi g)) ∧
      ⁅fixSubgroup (Psi g), fixSubgroup (Psi g)⁆ = fixSubgroup (Psi g) ∧
      11 ∣ Nat.card ↥(fixSubgroup (Psi g)) ∧
      ∀ h : PGU6, (∀ s ∈ fixSubgroup (Psi g), Psi h s = s) → h ∈ Subgroup.zpowers g

@[expose] def U42Rank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], catalogIs Y S9.isU4two →
    ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 27

@[expose] def U42E9 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], catalogIs Y S9.isU4two →
    ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ A : Subgroup Y, IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      ∀ a ∈ A, a * z = z * a

@[expose] def U42E27 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], catalogIs Y S9.isU4two →
    ∃ A : Subgroup Y, IsElemAbelian 3 A ∧ Nat.card A = 27

section Theta

variable {Ω : Type} [Group Ω]

@[expose] noncomputable def theta (L : Subgroup Ω) [L.Normal] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) :
    Ω →* MulAut S6 :=
  (autTr e).comp (CFSG.Quasithin.SteinbergCF.conjCenterQuotientHom L)

@[expose] noncomputable def Bt (B L : Subgroup Ω) [L.Normal] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) :
    Subgroup PGU6 :=
  (B.map (theta L e)).comap Psi

end Theta

structure Setup {Ω : Type} [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω) :
    Prop where
  cfg : S171.Cfg Ω 3 B x L
  maxG : S171.MaxG 3 B
  small : ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K

@[expose] def StepPat : Prop :=
  Pat4OfSmall → ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω)
    [L.Normal] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6), Setup B x L →
    (∀ b ∈ B, ∀ g : PGU6, Psi g = theta L e b → ¬ IsPR g) →
    ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → catalogIs ↥K S9.isU4two →
    IsSimpleGroup ↥K → Nat.card ↥K = 25920 →
    ∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ g : PGU6, Psi g = theta L e d → Pat4 g

@[expose] def StepBound : Prop :=
  U42Rank → ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    Setup B x L → ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → catalogIs ↥K S9.isU4two →
    IsSimpleGroup ↥K → Nat.card ↥K = 25920 →
    Nat.card B ≤ 243 ∧
      ((∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ Subgroup.centralizer (K : Set Ω) ∧
          E ≤ Subgroup.normalizer (L : Set Ω) ∧ E ≤ Subgroup.centralizer ({x} : Set Ω) ∧
          27 ≤ Nat.card E) ∨
        ∀ b ∈ B, ∃ d ∈ D, ∃ k ∈ K, b = d * k)

@[expose] def StepCaseACard : Prop :=
  U42E9 → U42E27 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    Setup B x L → ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → catalogIs ↥K S9.isU4two →
    IsSimpleGroup ↥K → Nat.card ↥K = 25920 →
    Nat.card B ≤ 243 →
    ∀ E : Subgroup Ω, IsElemAbelian 3 E → E ≤ Subgroup.centralizer (K : Set Ω) →
      E ≤ Subgroup.normalizer (L : Set Ω) → E ≤ Subgroup.centralizer ({x} : Set Ω) →
      27 ≤ Nat.card E →
    ∀ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) →
      T ≤ Subgroup.centralizer ({x} : Set Ω) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set Ω) → (⁅T, B⁆ : Subgroup Ω) ≠ ⊥ →
    Nat.card B = 243 ∧ ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (L : Set Ω)

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
