module

public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_map_equiv map_mem_fund_iso
  map_symm_mem_fund_iso linearBlockStandardPair_map_equiv exists_isoCompatPlus exists_spin_pair
  rankOne_plusDatum_of_lt commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_nodeSystem_of_pair (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} {x : G}
    (hMΩ : M ∈ Ω) (hx : IsClassicalMember p f M x) (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω M x j ∧ j ⟨0, by norm_num⟩ = K ∧
      j ⟨1, by norm_num⟩ = β := by
  classical
  have hm : 5 ≤ 6 := by norm_num
  have hm3 : 3 ≤ 6 := by norm_num
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
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
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := Gaps.orthFacts_plus (p := p) (f := f) (m := 6) c.hp2 hm c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := p) (f := f) hm3
  have hR0f : RK.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) hm3) := map_symm_mem_fund_iso hm3 hcι hRK
  have hR1f : Rβ.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) hm3) := map_symm_mem_fund_iso hm3 hcι hRβ
  have hadj' := Gaps.ModelAdj.map_equiv ι.symm hadj
  have hlin' : ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (RK.map ι.symm.toMonoidHom)
      (Rβ.map ι.symm.toMonoidHom) := by
    obtain ⟨W₁, hW₁⟩ := hlinR
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair c.hp2 c.hq hm hR0f hR1f hadj' hlin'
  let a0 : Fin 6 := ⟨0, by norm_num⟩
  let a1 : Fin 6 := ⟨1, by norm_num⟩
  let S : Fin 6 → Subgroup (spinGroup (quadPlus 6 (GaloisField p f))) := fun a =>
    conjSub x₀ (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a)
  let R : Fin 6 → Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K := fun a =>
    (S a).map ι.toMonoidHom
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 6 p f Fact.out).D := fun a =>
    map_mem_fund_iso hm3 hcι (conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) x₀)
  have hcomm : ∀ a b, a ≠ b → ¬ edgeD 6 a b → ¬ edgeD 6 b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr
      ((commutes_rankOne_plusDatum hm3 (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1).conjSub x₀)
  have hstd : ∀ a b, edgeD 6 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (R a) (R b) := fun a b h => by
    obtain ⟨W₁, hW₁⟩ := standardPair_plusDatum_edge (F := GaloisField p f) hm3 h
    exact ⟨_, linearBlockStandardPair_map_equiv ι
      (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x₀)⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes R hRfund (fun a b => edgeD 6 a b) hcomm hstd
  have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
    ext y
    simp
  have hR0 : R a0 = RK := by
    have hS : S a0 = RK.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a0) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a0) (by show 0 + 1 < 6; omega)]
      exact hx0.symm
    show (S a0).map ι.toMonoidHom = RK
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hR1 : R a1 = Rβ := by
    have hS : S a1 = Rβ.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a1) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a1) (by show 1 + 1 < 6; omega)]
      exact hx1.symm
    show (S a1).map ι.toMonoidHom = Rβ
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  refine ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hjM, hjc, hjp⟩, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2, hR1, hβR])

end CFSG.ClassicalInvolution.RouteD.ETCtx
