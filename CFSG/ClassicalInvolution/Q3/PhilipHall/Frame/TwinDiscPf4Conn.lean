module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf3Orb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Norm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinDisc



section Path

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def SecLink (Ω : Set (Subgroup Y)) (H : Subgroup Y) (M N : Subgroup Y) : Prop :=
  ∃ n ∈ H, conjSub n N = M ∨ conjSub n N ∈ omegaStarNbr Ω M ∨ M ∈ omegaStarNbr Ω (conjSub n N)

@[expose] def SecPath (Ω : Set (Subgroup Y)) (H : Subgroup Y) : Subgroup Y → Subgroup Y → Prop :=
  Relation.ReflTransGen (fun A B => B ∈ Ω ∧ (SecLink Ω H A B ∨ SecLink Ω H B A))

variable {Ω : Set (Subgroup Y)} {K : Subgroup Y}

theorem mem_dstarComp_of_secPath (hΩ : ConjInvariant Ω) (_hK : K ∈ Ω) {H : Subgroup Y}
    (hH : H ≤ sigmaStarNorm Ω K) {A B : Subgroup Y} (hp : SecPath Ω H A B)
    (hA : A ∈ dstarComp Ω K) : B ∈ dstarComp Ω K := by
  induction hp with
  | refl => exact hA
  | @tail b c _ hbc ih =>
    obtain ⟨hcΩ, hl | hl⟩ := hbc
    · obtain ⟨n, hn, h⟩ := hl
      have hcn : conjSub n c ∈ dstarComp Ω K := by
        rcases h with h | h | h
        · rw [h]; exact ih
        · exact ih.tail ⟨hΩ n c hcΩ, Or.inl h⟩
        · exact ih.tail ⟨hΩ n c hcΩ, Or.inr h⟩
      exact ((mem_sigmaStarNorm_iff.mp (hH hn)) c).mpr hcn
    · obtain ⟨n, hn, h⟩ := hl
      have hbn : conjSub n b ∈ dstarComp Ω K := ((mem_sigmaStarNorm_iff.mp (hH hn)) b).mp ih
      rcases h with h | h | h
      · rw [← h]; exact hbn
      · exact hbn.tail ⟨hcΩ, Or.inr h⟩
      · exact hbn.tail ⟨hcΩ, Or.inl h⟩

theorem centralizer_le_sigmaStarNorm_z (hΩ : HypOmegaGen Ω) {z : Y} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set Y) ≤ sigmaStarNorm Ω K := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K := ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
  exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (mem_dstarComp_of_twin_gen hΩ hK hL)

theorem oddCore_comm_of_alpha {A : Subgroup Y} {a z : Y} (hα : alphaOf A = ⊥) (ha : a ∈ A)
    (ha1 : a ≠ 1) (hz : z ∈ A) {n : Y} (hn : n ∈ oddCoreOf (Subgroup.centralizer ({a} : Set Y))) :
    n * z = z * n := by
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({a} : Set Y)), A⁆ :=
    Subgroup.commutator_mem_commutator hn hz
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set Y)), A⁆ ≤ alphaOf A := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl))
  rw [hα] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))

theorem sigmaGen_le_sigmaStarNorm_gen (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) :
    sigmaGen Ω K ≤ sigmaStarNorm Ω K := by
  refine iSup₂_le fun M hM g hg => ?_
  have hMd : M ∈ dstarComp Ω K := mem_dstarComp_of_mem_dComp_gen hΩ hM
  have hMΩ : M ∈ Ω := (T3.mem_dstarComp_symm hK hMd).1
  have hgM : conjSub g M = M := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hg)
  have h1 : g ∈ sigmaStarNorm Ω M :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hMΩ
      (by rw [hgM]; exact Relation.ReflTransGen.refl)
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hMd)] at h1

end Path

section Named

@[expose] def DiscSecConnTz (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
          ∀ N ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
            SecPath (CoreAssembly.conjClass (tightCore R))
              (oddCoreOf (Subgroup.centralizer ({t * z} : Set Y))) M N

@[expose] def DiscSecConnU (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
            ∀ N ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
              SecPath (CoreAssembly.conjClass (tightCore R))
                (oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ⊔
                  rLayer (CoreAssembly.conjClass (tightCore R)) u) M N

variable {n : ℕ}

theorem discTqTz_of_conn (B : TwinDiscBase n) (h : DiscSecConnTz n) : DiscTqTz n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα M hM
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hs := alphaStepsBase B s
  have hα' : alphaOf (Subgroup.closure ({z, t} : Set Y)) = ⊥ := by
    rw [hs.alpha_zt hf]; exact hα
  have hzA : z ∈ Subgroup.closure ({z, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({z, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2]; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hH : oddCoreOf (Subgroup.centralizer ({t * z} : Set Y)) ≤ sigmaStarNorm Ω K := by
    intro n' hn'
    have hcomm : n' * z = z * n' :=
      oddCore_comm_of_alpha hα' (Subgroup.mul_mem _ htA hzA) htz1 hzA hn'
    exact centralizer_le_sigmaStarNorm_z hΩ hf.mem hf.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hKS := mem_sylCent_tz_K' hΩ hf
  exact mem_dstarComp_of_secPath hΩ.conjInvariant hf.mem hH
    (h Y R S t₀ K K' z u J t W s hα K hKS M hM) Relation.ReflTransGen.refl

theorem discTqU_of_conn (h : DiscSecConnU n) : DiscTqU n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hY M hM
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have huA : u ∈ Subgroup.closure ({u, z} : Set Y) := Subgroup.subset_closure (by simp)
  have hzA : z ∈ Subgroup.closure ({u, z} : Set Y) := Subgroup.subset_closure (by simp)
  have hH : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ⊔ rLayer Ω u ≤ sigmaStarNorm Ω K := by
    refine sup_le (fun n' hn' => ?_)
      (hY.trans (sigmaGen_le_sigmaStarNorm_gen hΩ hf.mem))
    have hcomm : n' * z = z * n' := oddCore_comm_of_alpha hα huA hf.hu1 hzA hn'
    exact centralizer_le_sigmaStarNorm_z hΩ hf.mem hf.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  obtain ⟨g, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀d : conjSub g J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJ₀.1, Or.inl
      (omegaNbr_subset_omegaStarNbr_gen hΩ K (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz)))⟩
  exact mem_dstarComp_of_secPath hΩ.conjInvariant hf.mem hH
    (h Y R S t₀ K K' z u J t W s hα hY _ hJ₀ M hM) hJ₀d

end Named

namespace Pf2

structure TwinDiscInputsPf4 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  c13Exc : Disc13NExc n
  c14Exc : Disc14NExc n
  c14AltExc : Disc14AltExc n
  normCent : DiscNormCent n
  secConnTz : DiscSecConnTz n
  secConnU : DiscSecConnU n

theorem TwinDiscInputsPf4.toPf3 {n : ℕ} (I : TwinDiscInputsPf4 n) : TwinDiscInputsPf3 n where
  thmE := I.thmE
  base := I.base
  c13Exc := I.c13Exc
  c14Exc := I.c14Exc
  c14AltExc := I.c14AltExc
  normCent := I.normCent
  tqTz := discTqTz_of_conn I.base I.secConnTz
  tqU := discTqU_of_conn I.secConnU

end Pf2


end TwinDisc


theorem twinCoreDiscPerp_of_inputsPf4 {n : ℕ} (I : TwinDisc.Pf2.TwinDiscInputsPf4 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf3 I.toPf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
