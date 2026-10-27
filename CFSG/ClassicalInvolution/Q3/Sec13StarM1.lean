module

public import CFSG.ClassicalInvolution.Q3.Sec13StarCex
public import CFSG.ClassicalInvolution.Q3.Sec13StarMu
public import CFSG.ClassicalInvolution.Q3.Sec13StarCount

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace StarCex

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {t : G} {S : Sylow 2 G}
  (c : StarCex Ω K J t S)
include c

private theorem t_mem_sylow (S' : Sylow 2 G) : t ∈ (S' : Subgroup G) :=
  CFSG.pCore_isPGroup.le_sylow_of_normal S' c.t_mem_pCore

private theorem eq_of_le_sylow
    (hpair : ∀ L ∈ Ω, L ≤ (S : Subgroup G) → L = K ∨ L = conjSub t K) {S' : Sylow 2 G}
    {A B C : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω) (hC : C ∈ Ω) (hAS : A ≤ (S' : Subgroup G))
    (hBS : B ≤ (S' : Subgroup G)) (hCS : C ≤ (S' : Subgroup G)) (hAB : A ≠ B) (hAC : A ≠ C) :
    B = C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  by_contra hBC
  have h2 : {L | L ∈ Ω ∧ L ≤ (S : Subgroup G)}.ncard ≤ 2 :=
    (Set.ncard_le_ncard (t := {K, conjSub t K}) (fun L hL => hpair L hL.1 hL.2)
      (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
  have h3 : ({A, B, C} : Set (Subgroup G)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  have hle := Set.ncard_le_ncard (s := ({A, B, C} : Set (Subgroup G)))
    (t := {L | L ∈ Ω ∧ L ≤ (S' : Subgroup G)})
    (by rintro L (rfl | rfl | rfl) <;> exact ⟨‹_›, ‹_›⟩) (Set.toFinite _)
  rw [h3, ← ncard_le_sylow_eq c.hyp.thmD.hyp.conjInvariant S S'] at hle
  omega

theorem false_of_pair (hE4 : ∀ W ∈ WSet Ω, ¬ MuIsoE4 Ω W)
    (hpair : ∀ L ∈ Ω, L ≤ (S : Subgroup G) → L = K ∨ L = conjSub t K) : False := by
  have hΩ := c.hyp.thmD.hyp
  have h2 := c.hyp.thmD.two
  obtain ⟨η, hη, hηS, hinv⟩ := c.exists_eta
  set W : Subgroup G := ⨆ V ∈ η, V
  have hW : W ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hSN := c.le_normalizer_of_invariant hinv
  have hKD : K ∈ DSet Ω W := c.hyp.mem_dSet_iff.mpr ⟨c.hK, c.hKS.trans hSN⟩
  have hconn : DbarConnected Ω W := c.hyp.dbarConnected_of_move hW (hSN c.t_mem) c.t_mul_t
    fun R hR => c.conjSub_ne (c.hyp.mem_dstarComp_of_mem_dSet hW hKD hR)
  have hdeq : dComp Ω K = dstarComp Ω K := by
    by_contra hne
    exact Q3T8.Asc77.thompsonGraphAll G Ω c.hyp.partIHyp c.hK hne hW hconn
  have hK'Ω : conjSub t K ∈ Ω := hΩ.conjInvariant t K c.hK
  have hK'S : conjSub t K ≤ (S : Subgroup G) := c.conjSub_le c.hKS
  have hK'K : conjSub t K ≠ K := c.conjSub_ne (c.hyp.mem_dstarComp_self c.hK)
  have hstep : ∀ M N : Subgroup G, (M = K ∨ M = conjSub t K) → N ∈ Ω →
      Disconnected.dAdj Ω M N → N = K ∨ N = conjSub t K := by
    intro M N hM hN hMN
    obtain ⟨hMΩ, hMt⟩ : M ∈ Ω ∧ M ≠ conjSub t M := by
      rcases hM with hM | hM <;> rw [hM]
      exacts [⟨c.hK, hK'K.symm⟩, ⟨hK'Ω, by rw [c.conjSub_conjSub]; exact hK'K⟩]
    obtain ⟨hMN', hP⟩ : M ≠ N ∧ IsPGroup 2 ↥(M ⊔ N) := by
      rcases hMN with hMN | hMN
      · obtain ⟨-, hne, hle⟩ := (TC.mem_omegaNbr_iff hΩ h2).mp hMN
        exact ⟨Ne.symm hne, (h2 M hMΩ).to_sup_of_normal_left' (h2 N hN) hle⟩
      · obtain ⟨-, hne, hle⟩ := (TC.mem_omegaNbr_iff hΩ h2).mp hMN
        exact ⟨hne, (h2 M hMΩ).to_sup_of_normal_right' (h2 N hN) hle⟩
    obtain ⟨S', hS'⟩ := hP.exists_le_sylow
    have hMS : M ≤ (S' : Subgroup G) := le_sup_left.trans hS'
    have hNt : conjSub t M = N := c.eq_of_le_sylow hpair hMΩ (hΩ.conjInvariant t M hMΩ) hN hMS
      ((conjSub_mono hMS).trans (conjSub_eq_self_of_mem (c.t_mem_sylow S')).le)
      (le_sup_right.trans hS') hMt hMN'
    rcases hM with hM | hM <;> rw [← hNt, hM]
    exacts [Or.inr rfl, Or.inl (c.conjSub_conjSub K)]
  have hcomp : ∀ L ∈ dComp Ω K, L = K ∨ L = conjSub t K := by
    intro L hL
    change Relation.ReflTransGen _ K L at hL
    induction hL with
    | refl => exact Or.inl rfl
    | tail _ hMN ih => exact hstep _ _ ih hMN.1 hMN.2
  have hD : DSet Ω W = {K, conjSub t K} := by
    ext R
    refine ⟨fun hR => hcomp R ?_, ?_⟩
    · rw [hdeq]
      exact c.hyp.mem_dstarComp_of_mem_dSet hW hKD hR
    · rintro (rfl | rfl)
      exacts [hKD, c.hyp.mem_dSet_iff.mpr ⟨hK'Ω, hK'S.trans hSN⟩]
  exact hE4 W hW (c.hyp.muIsoE4_of_dSet hη hηS c.hK hK'Ω c.hKS hK'S hK'K.symm hD)

end StarCex

end CFSG.ClassicalInvolution.Q3.Sec13
