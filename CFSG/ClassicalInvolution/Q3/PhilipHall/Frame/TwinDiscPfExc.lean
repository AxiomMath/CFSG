module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPfTq
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

@[expose] def Disc13NExc (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ (∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
          M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K) →
        Subgroup.centralizer ({t * z} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc14NExc (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ (∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
          M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K) →
        Subgroup.centralizer ({u} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc14AltExc (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ (∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
            M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K) →
          Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y)

@[expose] def TwinDiscBase (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y) (K K' : Subgroup Y)
    (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W → AlphaSteps (CoreAssembly.conjClass (tightCore R))

section Generic

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem alphaStepsBase (B : TwinDiscBase n) (s : Setting n R S t₀ K K' z u J t W) :
    AlphaSteps (CoreAssembly.conjClass (tightCore R)) :=
  B Y R S t₀ K K' z u J t W s

theorem centralizer_le_normalizer_of_sylCent_dComp (I : TwinDiscBase n)
    (s : Setting n R S t₀ K K' z u J t W) {c : Y} {M₀ : Subgroup Y}
    (hM₀ : M₀ ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c)
    (hKM₀ : M₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K)
    (hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c,
      M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K) :
    Subgroup.centralizer ({c} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs := alphaStepsBase I s
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  intro g hg
  have hcM := conjSub_mem_sylCent hΩ.conjInvariant hg hM₀
  have h1 : conjSub g M₀ ∈ dComp Ω K := hall _ hcM
  have hnbr : conjSub g M₀ ∈ omegaNbr Ω (conjSub g K) := omegaNbr_conj hΩ.conjInvariant hKM₀ g
  have hnbr' : conjSub g K ∈ omegaNbr Ω (conjSub g M₀) :=
    Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (hΩ.conjInvariant g K hf.mem) hcM.1 hnbr
  have hKg : conjSub g K ∈ dComp Ω K :=
    Relation.ReflTransGen.tail h1 ⟨hΩ.conjInvariant g K hf.mem, Or.inl hnbr'⟩
  exact mem_normalizer_alpha_of_mem_dComp hs.hyp hs.trans hs.hyp51 hf hKg

theorem disc13N_of_exc (I : TwinDiscBase n) (hE : Disc13NExc n) : Disc13N n := by
  intro Y _ _ R S t₀ K K' z u J t W s
  by_cases hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
      M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K
  ·
    have hf := s.data.frame
    exact centralizer_le_normalizer_of_sylCent_dComp I s (mem_sylCent_tz_J s.core.hyp hf)
      (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)) hall
  · exact hE Y R S t₀ K K' z u J t W s hall

theorem disc14N_of_exc (I : TwinDiscBase n) (hE : Disc14NExc n) : Disc14N n := by
  intro Y _ _ R S t₀ K K' z u J t W s
  by_cases hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
      M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K
  · have hf := s.data.frame
    obtain ⟨g, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u s.core.hyp hf
    exact centralizer_le_normalizer_of_sylCent_dComp I s hJ₀
      (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz)) hall
  · exact hE Y R S t₀ K K' z u J t W s hall

theorem disc14Alt_of_exc (hE : Disc14AltExc n) : Disc14Alt n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα
  by_cases hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
      M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K
  · left
    refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
    obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR'
    have hd := hall J' ⟨hJ'Ω, R', hRJ', hRc⟩
    exact hRJ'.1.trans (le_iSup₂_of_le J' hd le_rfl)
  · right
    exact hE Y R S t₀ K K' z u J t W s hα hall

end Generic

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
