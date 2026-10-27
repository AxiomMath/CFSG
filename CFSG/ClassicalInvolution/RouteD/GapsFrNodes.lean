module

public import CFSG.ClassicalInvolution.RouteD.GapsFrIso
public import CFSG.ClassicalInvolution.RouteD.GapsFrPair

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld

section Levi

variable {K : Type} [Field K] {m : ℕ}

theorem rankOne_plusDatum_of_lt (hm3 : 3 ≤ m) {k : Fin m} (hk : k.val + 1 < m) :
    rankOne (plusDatum m K hm3).rootGroup k =
      rootSL2 (plusFrame m K hm3) k.val (k.val + 1) k.isLt hk (by omega) true false := by
  have h := toStdD_single_eq (n := m) (by omega) k
  rw [rootIdxD_of_lt m hk, rootIdxD'_of_lt m hk, rootSignD_of_lt m hk] at h
  exact rootGroup_sup_eq_longSL2_range hm3 (i := k) (j := ⟨k.val + 1, hk⟩)
    (Fin.ne_of_val_ne (by simp)) true false (γ := Pi.single k 1) h

end Levi

section Nodes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_dnodes_of_pair {m : ℕ} (hm : 5 ≤ m) (c : TCtx p f .POmegaPlus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := orthFacts_plus c.hp2 hm c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := p) (f := f) hm3
  have hR0f : RK.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField p f) hm3) := map_symm_mem_fund_iso hm3 hcι hRK
  have hR1f : Rβ.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField p f) hm3) := map_symm_mem_fund_iso hm3 hcι hRβ
  have hadj' := ModelAdj.map_equiv ι.symm hadj
  have hlin' : ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (RK.map ι.symm.toMonoidHom)
      (Rβ.map ι.symm.toMonoidHom) := by
    obtain ⟨W₁, hW₁⟩ := hlinR
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair c.hp2 c.hq hm hR0f hR1f hadj' hlin'
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  let S : Fin m → Subgroup (spinGroup (quadPlus m (GaloisField p f))) := fun a =>
    conjSub x₀ (rankOne (plusDatum m (GaloisField p f) hm3).rootGroup a)
  let R : Fin m → Subgroup (modelUniv .POmegaPlus m p f Fact.out).K := fun a =>
    (S a).map ι.toMonoidHom
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus m p f Fact.out).D := fun a =>
    map_mem_fund_iso hm3 hcι (conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) x₀)
  have hcomm : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr
      ((commutes_rankOne_plusDatum hm3 (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1).conjSub x₀)
  have hstd : ∀ a b, edgeD m a b → ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (R a) (R b) :=
    fun a b h => by
      obtain ⟨W₁, hW₁⟩ := standardPair_plusDatum_edge (F := GaloisField p f) hm3 h
      exact ⟨_, linearBlockStandardPair_map_equiv ι
        (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x₀)⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes R hRfund (fun a b => edgeD m a b) hcomm hstd
  have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have hR0 : R a0 = RK := by
    have hS : S a0 = RK.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum m (GaloisField p f) hm3).rootGroup a0) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a0) (by show 0 + 1 < m; omega)]
      exact hx0.symm
    show (S a0).map ι.toMonoidHom = RK
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hR1 : R a1 = Rβ := by
    have hS : S a1 = Rβ.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum m (GaloisField p f) hm3).rootGroup a1) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a1) (by show 1 + 1 < m; omega)]
      exact hx1.symm
    show (S a1).map ι.toMonoidHom = Rβ
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hex : ∀ a, ∃ w, IsClassicalMember p f (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes p f m Ω M :=
    { J := j
      w := w
      mem := fun a => (hj a).1.1
      cl := hw
      commK := hjM
      comm := hjc
      pair := hjp }
  refine ⟨nd, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Nodes

end CFSG.ClassicalInvolution.RouteD.Gaps
