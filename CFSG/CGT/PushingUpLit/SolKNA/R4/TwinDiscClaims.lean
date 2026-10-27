module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPfTq

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


@[expose] def Disc13NR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      Subgroup.centralizer ({t * z} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc14NR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      Subgroup.centralizer ({u} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc15R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y),
    TwinCoreHypR r n Y R S t₀ →
      ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
        Data (CoreAssembly.conjClass (tightCore R)) K K' z u J t W → u ∈ W →
          alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
            ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
                sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
              ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
                M ≤ Subgroup.centralizer ({t * z} : Set Y)

@[expose] def DiscTqTzR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
          M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

@[expose] def DiscTqUR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
          M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

section Derived

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem frame_J_mem_dstarCompR (s : SettingR r n R S t₀ K K' z u J t W) :
    J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := by
  have hΩ := s.core.hyp
  have hf := s.data.frame
  exact Relation.ReflTransGen.single ⟨hf.hJ.1, Or.inl
    (omegaNbr_subset_omegaStarNbr_gen hΩ K (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)))⟩

theorem centralizer_le_sigmaStarNorm_of_sylCentR (s : SettingR r n R S t₀ K K' z u J t W) {c : Y}
    {J₀ : Subgroup Y} (hJ₀ : J₀ ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c)
    (hJ₀d : J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K)
    (hall : ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) c,
      M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K) :
    Subgroup.centralizer ({c} : Set Y) ≤ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  have hΩ := s.core.hyp
  have hK : K ∈ CoreAssembly.conjClass (tightCore R) := s.data.frame.mem
  have hJ₀Ω := hJ₀.1
  intro g hg
  have h1 : conjSub g J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    hall _ (conjSub_mem_sylCent hΩ.conjInvariant hg hJ₀)
  have hJJ : conjSub g J₀ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) J₀ :=
    (T3.mem_dstarComp_symm hK hJ₀d).2.trans h1
  have hgJn : g ∈ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) J₀ :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJ₀Ω hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJ₀d)] at hgJn

theorem c17tzR (hT : DiscTqTzR r n) (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) :
    Subgroup.centralizer ({t * z} : Set Y) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K :=
  centralizer_le_sigmaStarNorm_of_sylCentR s (mem_sylCent_tz_J s.core.hyp s.data.frame)
    (frame_J_mem_dstarCompR s) (hT Y R S t₀ K K' z u J t W s hα)

theorem centInStarR (hT : DiscTqTzR r n) (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    {M : Subgroup Y} (hMΩ : M ∈ CoreAssembly.conjClass (tightCore R))
    (hMc : M ≤ Subgroup.centralizer ({t * z} : Set Y)) :
    M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := Y)) (bot_le : ⊥ ≤ M)
  exact hT Y R S t₀ K K' z u J t W s hα M ⟨hMΩ, V, hV, hV.1.trans hMc⟩

theorem ySigmaR (hT : DiscTqUR r n) (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) :
    Subgroup.centralizer ({u} : Set Y) ≤ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  have hΩ := s.core.hyp
  have hf := s.data.frame
  obtain ⟨g, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀d : conjSub g J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    Relation.ReflTransGen.single ⟨hJ₀.1, Or.inl
      (omegaNbr_subset_omegaStarNbr_gen hΩ K (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz)))⟩
  exact centralizer_le_sigmaStarNorm_of_sylCentR s hJ₀ hJ₀d (hT Y R S t₀ K K' z u J t W s hα)

end Derived

end CFSG.CGT.PushingUpLit.SolKNA.R4
