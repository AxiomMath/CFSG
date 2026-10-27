module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Model
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem commutes_rankOne_E7 (hadm : StatedLieAdmissible .E7 0 p f) (a b : Fin 7) (hab : a ≠ b)
    (h1 : ¬ edgeE 7 a b) (h2 : ¬ edgeE 7 b a) :
    Commutes (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a)
      (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup b) := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  have hdiv : (modelUniv .E7 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E7 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 7; decide⟩
  exact commutes_rankOne_of_cartan_eq_zero _ hext hℓ
    ((WeakCT.edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))).2.2.1 a b hab h1 h2).1

theorem exists_nodeSystem_E7_of_pair (hB1 : TypeE8.E7PairFrame p f)
    (c : ETCtx p f .E7 0 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 1 .E7 0 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} {x : G}
    (hMΩ : M ∈ Ω) (hx : IsClassicalMember p f M x) (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω M x j ∧ j 5 = K ∧ j 6 = β := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr c.hf, rfl⟩
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hMΩ hx
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {x} := mem_centralizingMembers_of_commutes c.hK hx.mem hKM
  have hβx : β ∈ centralizingMembers Ω {x} := mem_centralizingMembers_of_commutes hβ hx.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .E7 0 p f Fact.out).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := TypeEPattern.layerGeom_lift_E7 c.hq cx.d.ψ cx.d.ker_le hRK hRβ ⟨W', hW'⟩
  obtain ⟨g, hg5, hg6⟩ := hB1 RK hRK Rβ hRβ hadj hlinR 5 6 (by decide)
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  let R : Fin 7 → Subgroup (modelUniv .E7 0 p f Fact.out).K := fun a =>
    conjSub g (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a)
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D := fun a =>
    conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamental _ (hl a trivial)) g
  have hcomm : ∀ a b, a ≠ b → ¬ edgeE 7 a b → ¬ edgeE 7 b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2' => (commutes_rankOne_E7 hadm a b hab h1 h2').conjSub g
  have hstd : ∀ a b, edgeE 7 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (R a) (R b) := fun a b h => by
    obtain ⟨W₁, hW₁⟩ := stdPair_edge_E7 (F := GaloisField p f) h
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ g⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes R hRfund (fun a b => edgeE 7 a b) hcomm hstd
  refine ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hjM, hjc, hjp⟩, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj 5).1 hKx (by rw [(hj 5).2.2, hKR, hg5])
  · exact cx.eq_of_locImg_eq (hj 6).1 hβx (by rw [(hj 6).2.2, hβR, hg6])

end CFSG.ClassicalInvolution.RouteD.ETCtx
