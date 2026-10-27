module

public import CFSG.ClassicalInvolution.Q3.Q3PlanQS3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification

@[expose] def L2PrimeBalanceSolv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z : X) (L : Subgroup X), IsClassicalMember3 L z →
    L ≤ TwoLayer.subgroup X ⊔ solvableRadical X

section Centralizes

variable {X : Type} [Group X] [Finite X] {z : X} {L : Subgroup X}

theorem IsClassicalMember3.le_centralizer_of_le_centralizer (hL : IsClassicalMember3 L z)
    {T : Subgroup X} (hT : IsComponentOf T ⊤) (hTz : T ≤ Subgroup.centralizer ({z} : Set X)) :
    L ≤ Subgroup.centralizer (T : Set X) := by
  set C : Subgroup X := Subgroup.centralizer ({z} : Set X) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have hTC : IsComponentOf (T.subgroupOf C) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h := isSubnormal_subgroupOf hT.2.1 C
      rwa [Subgroup.top_subgroupOf] at h
    · exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hTz) hT.2.2
  have hLsub : IsSubnormal (L.subgroupOf C) ⊤ := by
    have h := isSubnormal_subgroupOf hL.subnormal C
    rwa [Subgroup.subgroupOf_self] at h
  have hsolv : Group.IsSolvable (L.subgroupOf C) :=
    have := hL.isSolvable
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).injective
  have hcomm := @Layer.commutes_with_solvable_subnormal C _ _ (L.subgroupOf C) hLsub hsolv
  have hle : T.subgroupOf C ≤ Layer.subgroup C := Layer.component_le hTC
  have hcent : Layer.subgroup C ≤ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : (⟨t, hTz ht⟩ : C) ∈ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    hcent (hle ht)
  have h2 := Subgroup.mem_centralizer_iff.mp h1 (⟨l, hLC hl⟩ : C) hl
  exact (congrArg Subtype.val h2).symm

end Centralizes

@[expose] def SolvableMemberSplit : Prop :=
  ∀ (X : Type) [Group X] [Finite X], classicalInvolutionOddCore X = ⊥ →
    ∀ (z : X) (L : Subgroup X), IsClassicalMember3 L z →
      L ≤ Layer.subgroup X ⊔ solvableRadical X →
      ∀ T : Subgroup X, IsComponentOf T ⊤ → ¬ T ≤ Subgroup.centralizer ({z} : Set X) → L ≤ T

theorem quasisimpleConnected3Comp_of_solvBalance (hb : L2PrimeBalanceSolv)
    (hs : SolvableMemberSplit) : QuasisimpleConnected3Comp := by
  intro Y _ _ _ hO Λ hΛ hconn hns _
  have hmem : ∀ L ∈ Λ, L ≤ Layer.subgroup Y ⊔ solvableRadical Y := by
    intro L hL
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    refine (hb Y z L hz).trans (sup_le_sup_right ?_ _)
    exact sSup_le fun _ hC => Layer.component_le (TwoComponents.ordinary_of_corefree hO hC)
  have htop : Layer.subgroup Y ⊔ solvableRadical Y = ⊤ := by
    rw [eq_top_iff, ← hΛ.generated]
    exact iSup₂_le hmem
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Y, IsComponentOf T ⊤ := by
    by_contra hno
    push Not at hno
    have hlayer : Layer.subgroup Y = ⊥ :=
      le_bot_iff.mp (sSup_le fun T hT => (hno T hT).elim)
    rw [hlayer, bot_sup_eq] at htop
    apply hns
    have hsolv : Group.IsSolvable (solvableRadical Y) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    rw [htop] at hsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := Y)).toMonoidHom)
      (Subgroup.topEquiv (G := Y)).surjective
  have hsplit : ∀ L ∈ Λ, L ≤ T ∨ L ≤ Subgroup.centralizer (T : Set Y) := by
    intro L hL
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    by_cases hTz : T ≤ Subgroup.centralizer ({z} : Set Y)
    · exact Or.inr (hz.le_centralizer_of_le_centralizer hT hTz)
    · exact Or.inl (hs Y hO z L hz (hmem L hL) T hT hTz)
  obtain ⟨L₀, hL₀, hL₀D⟩ : ∃ L ∈ Λ, ¬ L ≤ Subgroup.centralizer (T : Set Y) := by
    by_contra hall
    push Not at hall
    have hY : (⊤ : Subgroup Y) ≤ Subgroup.centralizer (T : Set Y) := by
      rw [← hΛ.generated]
      exact iSup₂_le hall
    have hcen : Subgroup.center T = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hY (Subgroup.mem_top (b : Y))) (a : Y)
        a.2).symm
    have hone : ∀ x : T ⧸ Subgroup.center T, x = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H a => exact (QuotientGroup.eq_one_iff a).mpr (hcen ▸ Subgroup.mem_top a)
    obtain ⟨x, y, hxy⟩ := @exists_pair_ne _ hT.2.2.2.toNontrivial
    exact hxy ((hone x).trans (hone y).symm)
  have hL₀T : L₀ ≤ T := (hsplit L₀ hL₀).resolve_right hL₀D
  have hall : ∀ v : ↥Λ, (nonCommGraph Λ).Reachable ⟨L₀, hL₀⟩ v → (v : Subgroup Y) ≤ T := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact hL₀T
    | @tail b c _ hadj ih =>
      rcases hsplit (c : Subgroup Y) c.2 with h | h
      · exact h
      · exfalso
        obtain ⟨-, hnc⟩ := nonCommGraph_adj.mp hadj
        exact hnc fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h hy) x (ih hx)
  have htopT : T = ⊤ := by
    rw [eq_top_iff, ← hΛ.generated]
    exact iSup₂_le fun M hM => hall ⟨M, hM⟩ (hconn.preconnected _ _)
  have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
  subst htopT
  exact Components.quasisimple_of_equiv Subgroup.topEquiv.symm hqs

theorem quasisimpleConnected3_of_solvBalance (hb : L2PrimeBalanceSolv)
    (hs : SolvableMemberSplit) : QuasisimpleConnected3 :=
  quasisimpleConnected3_of_comp (quasisimpleConnected3Comp_of_solvBalance hb hs)

end CFSG.ClassicalInvolution.Q3
