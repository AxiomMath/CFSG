module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowEnd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowFamily

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6RowParamNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem zero_orth_E6 : (0 : Fin (Tag.rank .E6)) ≠ 1 ∧ (0 : Fin (Tag.rank .E6)) ≠ 3 := by
  decide

theorem two_orth_E6 : (2 : Fin (Tag.rank .E6)) ≠ 1 ∧ (2 : Fin (Tag.rank .E6)) ≠ 3 := by
  decide

theorem rhoPerm_rhoPerm_E6 (i : Fin (Tag.rank .E6)) : rhoPerm (rhoPerm i) = i := by
  revert i
  decide

theorem rhoPerm_zero_E6 : rhoPerm (0 : Fin (Tag.rank .E6)) = 5 := by
  decide

theorem rhoPerm_two_E6 : rhoPerm (2 : Fin (Tag.rank .E6)) = 4 := by
  decide

section Rho


variable {K : Type} [Field K] {G : Type} [Group G]

theorem sigma_mem_e6ScLevi_singleton {i : Fin (Tag.rank .E6)} {x : e6Data_valid.minGroup K}
    (hx : x ∈ e6ScLevi K {i}) : sigma K (RingHom.id K) x ∈ e6ScLevi K {rhoPerm i} := by
  dsimp only [e6ScLevi] at hx ⊢
  rw [CFSG.LieType.CurtisTits.levi_singleton] at hx ⊢
  exact CFSG.LieType.Steinberg.TwistedE6.sigma_mem_rankOne (RingHom.id K) hx

theorem commute_rho_of_commute {ΦA : e6ScLevi K e6A5Nodes →* G}
    {ΦB : e6ScLevi K e6TwoA2Nodes →* G} {t : G}
    (hconjA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hconjB : ∀ x y : e6ScLevi K e6TwoA2Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦB x * t⁻¹ = ΦB y)
    {j j' : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) (hj' : j' ≠ 1 ∧ j' ≠ 3)
    (hρ : rhoPerm j = j')
    (hc : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b)) :
    ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj') b) := by
  subst hρ
  intro a b
  have ha' : sigma K (RingHom.id K) a ∈ e6ScLevi K {1} := by
    have h := sigma_mem_e6ScLevi_singleton a.2
    rwa [e6RhoPerm_one] at h
  have hb' : sigma K (RingHom.id K) b ∈ e6ScLevi K {j} := by
    have h := sigma_mem_e6ScLevi_singleton b.2
    rwa [rhoPerm_rhoPerm_E6] at h
  have hσσ : ∀ g : e6Data_valid.minGroup K, sigma K (RingHom.id K) (sigma K (RingHom.id K) g) = g :=
    CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id K) (fun _ => rfl)
  have h1 : t * scLeviRestrict ΦB one_subset_e6TwoA2Nodes ⟨_, ha'⟩ * t⁻¹ =
      scLeviRestrict ΦB one_subset_e6TwoA2Nodes a := by
    rw [scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjB _ _ (hσσ a).symm
  have h2 : t * scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) ⟨_, hb'⟩ * t⁻¹ =
      scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj') b := by
    rw [scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjA _ _ (hσσ b).symm
  have h := (hc ⟨_, ha'⟩ ⟨_, hb'⟩).map (MulAut.conj t).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [← h1, ← h2]
  exact h

theorem sigma_eq_self_of_mem_rankOne {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {x : e6Data_valid.minGroup K}
    (hx : x ∈ CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup a) :
    sigma K (RingHom.id K) x = x := by
  have hle : CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup a ≤
      MonoidHom.eqLocus (sigma K (RingHom.id K)) (MonoidHom.id _) := by
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
      change sigma K (RingHom.id K) _ = _
      rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single, ha, RingHom.id_apply]
      rfl
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
      change sigma K (RingHom.id K) _ = _
      rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single, ha, RingHom.id_apply]
      rfl
  exact hle hx

theorem sigma_eq_self_of_mem_e6ScLevi {S : Finset (Fin (Tag.rank .E6))}
    (hS : ∀ i ∈ S, rhoPerm i = i) {x : e6Data_valid.minGroup K} (hx : x ∈ e6ScLevi K S) :
    sigma K (RingHom.id K) x = x := by
  have hle : e6ScLevi K S ≤ MonoidHom.eqLocus (sigma K (RingHom.id K)) (MonoidHom.id _) := by
    show (⨆ j ∈ S, CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup j) ≤ _
    exact iSup₂_le fun i hi y hy => sigma_eq_self_of_mem_rankOne (hS i hi) hy
  exact hle hx

theorem conjB_of_range_le {ΦB : e6ScLevi K e6TwoA2Nodes →* G} {L : Subgroup G} {t : G}
    (htL : t ∈ centralizer (L : Set G)) (hB : ΦB.range ≤ L) :
    ∀ x y : e6ScLevi K e6TwoA2Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦB x * t⁻¹ = ΦB y := by
  intro x y hxy
  have hfix : ∀ i ∈ e6TwoA2Nodes, rhoPerm i = i := by decide
  have hyx : y = x := Subtype.ext (hxy.trans (sigma_eq_self_of_mem_e6ScLevi hfix x.2))
  subst hyx
  have hc := mem_centralizer_iff.1 htL (ΦB y) (hB ⟨y, rfl⟩)
  rw [← hc, mul_inv_cancel_right]

end Rho

section Param


variable {K : Type} [Field K] {G : Type} [Group G]

structure IsTwoE6GraphRowParam {L : Subgroup G} {F : Type} [Field F]
    (e : L ≃* adjointGroup .F4 F) (X₀ : Subgroup (adjointGroup .F4 F)) (t : G)
    (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦB : e6ScLevi K e6TwoA2Nodes →* G) : Prop where
  agree : ∀ x : e6ScLevi K {3}, scLeviRestrict ΦA three_subset_e6A5Nodes x =
    scLeviRestrict ΦB three_subset_e6TwoA2Nodes x
  conjA : ∀ x y : e6ScLevi K e6A5Nodes,
    (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y
  conjB : ∀ x y : e6ScLevi K e6TwoA2Nodes,
    (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦB x * t⁻¹ = ΦB y
  comm₀ : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6) b)
  comm₂ : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6) b)
  range_sup : ΦA.range ⊔ ΦB.range = twoE6Span e X₀

theorem IsTwoE6GraphRowParam.comm {L : Subgroup G} {F : Type} [Field F]
    {e : L ≃* adjointGroup .F4 F} {X₀ : Subgroup (adjointGroup .F4 F)} {t : G}
    {ΦA : e6ScLevi K e6A5Nodes →* G} {ΦB : e6ScLevi K e6TwoA2Nodes →* G}
    (h : IsTwoE6GraphRowParam e X₀ t ΦA ΦB) (j : Fin (Tag.rank .E6)) (hj : j ≠ 1 ∧ j ≠ 3) :
    ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b) := by
  rcases orth_cases_E6 hj with rfl | rfl | rfl | rfl
  · exact h.comm₀
  · exact h.comm₂
  · exact commute_rho_of_commute h.conjA h.conjB two_orth_E6 hj rhoPerm_two_E6 h.comm₂
  · exact commute_rho_of_commute h.conjA h.conjB zero_orth_E6 hj rhoPerm_zero_E6 h.comm₀

theorem IsTwoE6GraphRowParam.isTwoE6GraphFamily {L : Subgroup G} {F : Type} [Field F]
    {e : L ≃* adjointGroup .F4 F} {X₀ : Subgroup (adjointGroup .F4 F)} {t : G}
    {ΦA : e6ScLevi K e6A5Nodes →* G} {ΦB : e6ScLevi K e6TwoA2Nodes →* G}
    (h : IsTwoE6GraphRowParam e X₀ t ΦA ΦB) :
    IsTwoE6GraphFamily (twoE6Span e X₀) t K (twoGraphFamilyE6 ΦA ΦB h.comm) :=
  isTwoE6GraphFamily_twoGraphFamilyE6 h.agree h.conjA h.conjB h.range_sup

end Param

section Input


@[expose] def TwoE6ParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∃ (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦB : e6ScLevi K e6TwoA2Nodes →* G),
        IsTwoE6GraphRowParam e X₀ t ΦA ΦB

theorem twoE6FamilyInput_of_paramInput (h : TwoE6ParamInput) : TwoE6FamilyInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  obtain ⟨ΦA, ΦB, hp⟩ := h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  exact ⟨_, hp.isTwoE6GraphFamily⟩

end Input

section Row


theorem twoE6PairInput_of_paramInput (hP : TwoE6ParamInput) (hU : TwoE6UniqueInput) :
    TwoE6PairInput :=
  twoE6PairInput_of_inputs (twoE6FamilyInput_of_paramInput hP) hU

end Row

end CFSG.SeitzReduction.F4Pilot
