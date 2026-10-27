module

public import CFSG.ClassicalInvolution.Q3.Q3EPRows
public import CFSG.ClassicalInvolution.Q3.Q3EPFrame
public import CFSG.ClassicalInvolution.Q3.Q3EPToralGL
public import CFSG.ClassicalInvolution.Q3.Q3EPGeom
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorLie

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.exists_nodeSystem_of_pair (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} {x : G}
    (hMΩ : M ∈ Ω) (hx : IsClassicalMember3 M x) (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) Ω M x j ∧ j ⟨0, by norm_num⟩ = K ∧
      j ⟨1, by norm_num⟩ = β := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hx
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {x} := mem_centralizingMembers_of_commutes c.hK hx.mem hKM
  have hβx : β ∈ centralizingMembers Ω {x} := mem_centralizingMembers_of_commutes hβ hx.mem hβM
  have hKL := ETCtx3.IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := ETCtx3.IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) RK
      Rβ := cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := layerGeomD6_3.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  have hR0f : RK.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRK
  have hR1f : Rβ.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRβ
  have hadj' := Gaps.ModelAdj.map_equiv ι.symm hadj
  have hlin' : ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (RK.map ι.symm.toMonoidHom)
      (Rβ.map ι.symm.toMonoidHom) := by
    obtain ⟨W₁, hW₁⟩ := hlinR
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3 hR0f hR1f hadj' hlin'
  let a0 : Fin 6 := ⟨0, by norm_num⟩
  let a1 : Fin 6 := ⟨1, by norm_num⟩
  let S : Fin 6 → Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1))) := fun a =>
    conjSub x₀ (rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup a)
  let R : Fin 6 → Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K := fun a =>
    (S a).map ι.toMonoidHom
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D := fun a =>
    map_mem_fund_iso hm3 hcι (conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) x₀)
  have hcomm : ∀ a b, a ≠ b → ¬ edgeD 6 a b → ¬ edgeD 6 b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr
      ((commutes_rankOne_plusDatum hm3 (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1).conjSub x₀)
  have hstd : ∀ a b, edgeD 6 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (R a) (R b) := fun a b h => by
    obtain ⟨W₁, hW₁⟩ := standardPair_plusDatum_edge (F := GaloisField 3 1) hm3 h
    exact ⟨_, linearBlockStandardPair_map_equiv ι
      (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x₀)⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes R hRfund (fun a b => edgeD 6 a b) hcomm hstd
  have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
    ext y
    simp
  have hR0 : R a0 = RK := by
    have hS : S a0 = RK.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup a0) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a0) (by show 0 + 1 < 6; omega)]
      exact hx0.symm
    show (S a0).map ι.toMonoidHom = RK
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hR1 : R a1 = Rβ := by
    have hS : S a1 = Rβ.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup a1) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a1) (by show 1 + 1 < 6; omega)]
      exact hx1.symm
    show (S a1).map ι.toMonoidHom = Rβ
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  refine ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hjM, hjc, hjp⟩, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2, hR1, hβR])

theorem ETCtx3.IsLayerMember.of_commutes_self {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G}
    {x : G} (cx : ETCtx3 tY nY Ω N x) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hc : Commutes L N) : cx.IsLayerMember L :=
  ⟨hL, fun h => not_commutes_self3 cx.hz (h ▸ hc)⟩

theorem ETCtx3.exists_distinguisher (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {a d : Subgroup G} (ha : a ∈ Ω)
    (hd : d ∈ Ω) (hKa : Commutes K a) (hβa : Commutes β a) (hKd : Commutes K d)
    (hβd : Commutes β d) (had : Commutes a d) :
    ∃ N ∈ centralizingMembers Ω {z}, Commutes d N ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W a N := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨xd, hxd⟩ := c.hΩ.classical d hd
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hd hxd
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes c.hK hxd.mem hKd
  have hβx : β ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes hβ hxd.mem hβd
  have hax : a ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes ha hxd.mem had
  have hKL := ETCtx3.IsLayerMember.of_commutes_self cx hKx hKd
  have hβL := ETCtx3.IsLayerMember.of_commutes_self cx hβx hβd
  have haL := ETCtx3.IsLayerMember.of_commutes_self cx hax had
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) RK
      Rβ := cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨RN, hRN, ⟨W₂, hW₂⟩, hcN⟩ := adjPerp3_plus6 RK hRK Rβ hRβ hadj Ra hRa
    ((cx.commutes_iff_fund hax hKx hRa haR hKR).mp (commutes_symm hKa))
    ((cx.commutes_iff_fund hax hβx hRa haR hβR).mp (commutes_symm hβa))
  obtain ⟨N, hNx, hNd, hNR⟩ := cx.exists_member_of_fund hRN
  have hNK : Commutes N K := (cx.commutes_iff_fund hNx hKx hRN hNR hKR).mpr hcN
  exact ⟨N, mem_centralizingMembers_of_commutes hNx.1 c.hz.mem hNK,
    cx.commutes_K_of_ne hNx hNd, cx.stdPair_of_fund hax hNx hW₂ haR hNR⟩

end Nodes

section Fixed

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def RootFixedGL3 (hm3 : 3 ≤ 6) (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (a₀ : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank) {t : G}
    (htz : t * z * t⁻¹ = z) : Prop :=
  ∃ (e : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank ≃ Fin 6)
    (ι : spinGroup (quadPlus 6 (GaloisField 3 1)) ≃*
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K),
    IsoCompatP hm3 e ι ∧
    ∃ (i₀ i₁ : Fin 6) (_ : i₀ ≠ i₁) (γ₀ : Fin 6 → ℤ) (s₀ t₀ : Bool)
      (_ : toStdD 6 γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
      (k : spinGroup (quadPlus 6 (GaloisField 3 1))),
      ((((plusDatum 6 (GaloisField 3 1) hm3).rootGroup γ₀ ⊔
          (plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-γ₀)).map
            (MulAut.conj k).toMonoidHom).map ι.toMonoidHom =
        rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀) ∧
      (∀ (a b : Fin 6), a ≠ b → a ≠ i₀ → a ≠ i₁ → b ≠ i₀ → b ≠ i₁ → ∀ {γ : Fin 6 → ℤ},
        toStdD 6 γ = Pi.single a (boolSign true) + Pi.single b (boolSign false) →
          ∀ y ∈ ((plusDatum 6 (GaloisField 3 1) hm3).rootGroup γ).map (MulAut.conj k).toMonoidHom,
            Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ (ι y)) = c.d.ψ (ι y))

omit [Finite G] in
theorem rootFixedGL_of_chain_model3 (c : ETCtx3 .POmegaPlus 6 Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z) (a₀ : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank)
    {R0 R1 R2 RN : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K}
    (h0 : R0 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (h1 : R1 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (h2 : R2 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (hN : RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (hM : rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀ ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D)
    (hadj01 : Gaps.ModelAdj
      (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R0 R1)
    (hadj12 : Gaps.ModelAdj
      (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R1 R2)
    (hlin01 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R0 R1)
    (hlin12 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R1 R2)
    (hc02 : Commutes R0 R2)
    (hM0 : Commutes (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀) R0)
    (hM1 : Commutes (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀) R1)
    (hM2 : Commutes (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀) R2)
    (hadjN : Gaps.ModelAdj
      (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R0 RN)
    (hcN : Commutes R2 RN)
    (hfix0 : ∀ y ∈ R0, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y)
    (hfix1 : ∀ y ∈ R1, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y)
    (hfix2 : ∀ y ∈ R2, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y) :
    RootFixedGL3 (by norm_num : 3 ≤ 6) c a₀ ht := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  obtain ⟨W01, hW01⟩ := hlin01
  obtain ⟨W12, hW12⟩ := hlin12
  obtain ⟨x, hx0, hx1, hx2, tt, hxM⟩ := spin6_chain_frame3
    (map_symm_mem_fund_iso hm3 hcι h0) (map_symm_mem_fund_iso hm3 hcι h1)
    (map_symm_mem_fund_iso hm3 hcι h2) (map_symm_mem_fund_iso hm3 hcι hN)
    (map_symm_mem_fund_iso hm3 hcι hM)
    (Gaps.ModelAdj.map_equiv ι.symm hadj01) (Gaps.ModelAdj.map_equiv ι.symm hadj12)
    ⟨_, linearBlockStandardPair_map_equiv ι.symm hW01⟩
    ⟨_, linearBlockStandardPair_map_equiv ι.symm hW12⟩
    ((commutes_map_equiv ι.symm).mpr hc02) ((commutes_map_equiv ι.symm).mpr hM0)
    ((commutes_map_equiv ι.symm).mpr hM1) ((commutes_map_equiv ι.symm).mpr hM2)
    (Gaps.ModelAdj.map_equiv ι.symm hadjN) ((commutes_map_equiv ι.symm).mpr hcN)
  let F₀ := plusFrame 6 (GaloisField 3 1) hm3
  let θ : spinGroup (quadPlus 6 (GaloisField 3 1)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let σ := Gaps.locAut c.hΩ.conjInvariant ht
  let T : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1))) :=
    MonoidHom.eqLocus (σ.toMonoidHom.comp (θ.comp (MulAut.conj x).toMonoidHom))
      (θ.comp (MulAut.conj x).toMonoidHom)
  have hmemT : ∀ y, y ∈ T ↔ σ (θ (x * y * x⁻¹)) = θ (x * y * x⁻¹) := fun y => Iff.rfl
  have hle : ∀ (R : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (S : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))),
      R.map ι.symm.toMonoidHom = S.map (MulAut.conj x).toMonoidHom →
      (∀ r ∈ R, σ (c.d.ψ r) = c.d.ψ r) → S ≤ T := by
    intro R S hS hR y hy
    rw [hmemT]
    have hyR : x * y * x⁻¹ ∈ R.map ι.symm.toMonoidHom := by
      rw [hS]
      exact ⟨y, hy, rfl⟩
    obtain ⟨r, hr, hre⟩ := hyR
    have hι : ι (x * y * x⁻¹) = r := by
      rw [← hre]
      simp
    show σ (c.d.ψ (ι (x * y * x⁻¹))) = c.d.ψ (ι (x * y * x⁻¹))
    rw [hι]
    exact hR r hr
  have hA : ∀ a, a < 3 → Gaps.RootInN F₀ T a (a + 1) true false ∧
      Gaps.RootInN F₀ T (a + 1) a true false := by
    intro a ha
    interval_cases a
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R0 _ hx0 hfix0)
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R1 _ hx1 hfix1)
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R2 _ hx2 hfix2)
  have hAll := Gaps.rootInN_of_A_chain (n := 3) hA
  obtain ⟨γ₀, -, hγ₀⟩ := exists_mem_rootsD_toStdD_eq 6 (i := ⟨4, by norm_num⟩)
    (j := ⟨5, by norm_num⟩) (s := boolSign true) (t := boolSign tt) (by decide)
    (boolSign_eq_one_or_eq_neg_one _) (boolSign_eq_one_or_eq_neg_one _)
  refine ⟨e, ι, hcι, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩, by decide, γ₀, true, tt, hγ₀, x, ?_, ?_⟩
  · have e1 : (plusDatum 6 (GaloisField 3 1) hm3).rootGroup γ₀ ⊔
        (plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-γ₀) =
        Gaps.rootSL2 F₀ 4 5 (by norm_num) (by norm_num) (by norm_num) true tt :=
      Gaps.rootGroup_sup_eq_longSL2_range hm3 (i := ⟨4, by norm_num⟩) (j := ⟨5, by norm_num⟩)
        (by decide) true tt hγ₀
    rw [e1, ← hxM, Subgroup.map_map]
    have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    rw [hid, Subgroup.map_id]
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hij hi4 hi5 hj4 hj5 γ hγ y ⟨y', hy', rfl⟩
    have ha4 : a ≠ 4 := fun h => hi4 (Fin.ext h)
    have ha5 : a ≠ 5 := fun h => hi5 (Fin.ext h)
    have hb4 : b ≠ 4 := fun h => hj4 (Fin.ext h)
    have hb5 : b ≠ 5 := fun h => hj5 (Fin.ext h)
    have hab : a ≠ b := fun h => hij (Fin.ext h)
    obtain ⟨ha', hb', hab', hroot⟩ := hAll a b (by omega) (by omega) hab
    have hXγ : (plusDatum 6 (GaloisField 3 1) hm3).rootGroup γ =
        ((plusFrame 6 (GaloisField 3 1) hm3).longRoot (i := ⟨a, ha⟩) (j := ⟨b, hb⟩)
          (fun h => hab (congrArg Fin.val h)) true false).range :=
      plusRootGroup_eq hm3 (fun h => hab (congrArg Fin.val h)) true false hγ
    rw [hXγ] at hy'
    obtain ⟨c', rfl⟩ := hy'
    rw [← ofAdd_toAdd c']
    exact (hmemT _).mp (hroot (Multiplicative.toAdd c'))

theorem stdPair_data3 {U V : Subgroup G} {wU wV : G} (hU : IsClassicalMember3 U wU)
    (hV : IsClassicalMember3 V wV)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W U V) :
    U ≠ V ∧ ¬ Commutes U V ∧ Commute wU wV ∧ conjSub wV U = U := by
  obtain ⟨W, hW⟩ := h
  exact ⟨ne_of_linearBlockStandardPair hW, not_commutes_of_linearBlockStandardPair hW,
    Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW hU.mem hV.mem hU.orderOf_eq_two
      hV.orderOf_eq_two,
    Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW hV.mem hV.orderOf_eq_two⟩

theorem ETCtx3.rootFixedGL_of_node_system (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {j : Fin 6 → Subgroup G} (hj : NodeSystem 3 1 (edgeD 6) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hβ0 : Commutes β (j 0)) (ht : t * z * t⁻¹ = z) :
    RootFixedGL3 (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 3 1
      Nat.prime_three).D.rank) ht := by
  classical
  have hΩ := c.hΩ
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hMz : j 0 ∈ centralizingMembers Ω {z} := hj.mem 0
  obtain ⟨xM, hxM⟩ := hΩ.classical (j 0) hMz.1
  obtain ⟨j', hj', hj'0, hj'1⟩ := c.exists_nodeSystem_of_pair hsingle hβ htβ hKβ hMz.1 hxM
    (hj.commK 0) hβ0
  have hj'0' : j' 0 = K := hj'0
  have hj'1' : j' 1 = β := hj'1
  have hKN : ∀ a : Fin 6, ¬ edgeD 6 0 a → ¬ edgeD 6 a 0 → a ≠ 0 → Commutes K (j' a) := by
    intro a h1 h2' h3
    have := hj'.comm 0 a (Ne.symm h3) h1 h2'
    rwa [hj'0'] at this
  have hβN : ∀ a : Fin 6, ¬ edgeD 6 1 a → ¬ edgeD 6 a 1 → a ≠ 1 → Commutes β (j' a) := by
    intro a h1 h2' h3
    have := hj'.comm 1 a (Ne.symm h3) h1 h2'
    rwa [hj'1'] at this
  have hmem : ∀ a : Fin 6, Commutes K (j' a) → j' a ∈ centralizingMembers Ω {z} := fun a h =>
    mem_centralizingMembers_of_commutes (hj'.mem a).1 c.hz.mem (commutes_symm h)
  have hK3 := hKN 3 (by decide) (by decide) (by decide)
  have hK4 := hKN 4 (by decide) (by decide) (by decide)
  have hK5 := hKN 5 (by decide) (by decide) (by decide)
  have hβ3 := hβN 3 (by decide) (by decide) (by decide)
  have hβ4 := hβN 4 (by decide) (by decide) (by decide)
  have hβ5 := hβN 5 (by decide) (by decide) (by decide)
  have hz3 := hmem 3 hK3
  have hz4 := hmem 4 hK4
  have hz5 := hmem 5 hK5
  obtain ⟨W34, hW34⟩ := hj'.pair 3 4 (by decide)
  obtain ⟨W35, hW35⟩ := hj'.pair 3 5 (by decide)
  have hW43 := CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW34
  have hc45 : Commutes (j' 4) (j' 5) := hj'.comm 4 5 (by decide) (by decide) (by decide)
  have hL3 : c.IsLayerMember (j' 3) := ETCtx3.IsLayerMember.of_not_commutes c hz3 hz4
    (ne_of_linearBlockStandardPair hW34) (not_commutes_of_linearBlockStandardPair hW34)
  have hL4 : c.IsLayerMember (j' 4) := ETCtx3.IsLayerMember.of_not_commutes c hz4 hz3
    (ne_of_linearBlockStandardPair hW43) (not_commutes_of_linearBlockStandardPair hW43)
  have hW53 := CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW35
  have hL5 : c.IsLayerMember (j' 5) := ETCtx3.IsLayerMember.of_not_commutes c hz5 hz3
    (ne_of_linearBlockStandardPair hW53) (not_commutes_of_linearBlockStandardPair hW53)
  obtain ⟨R3, hR3, h3R⟩ := hL3.exists_fund
  obtain ⟨R4, hR4, h4R⟩ := hL4.exists_fund
  obtain ⟨R5, hR5, h5R⟩ := hL5.exists_fund
  obtain ⟨w3, hw3⟩ := hΩ.classical _ hz3.1
  obtain ⟨w4, hw4⟩ := hΩ.classical _ hz4.1
  obtain ⟨w5, hw5⟩ := hΩ.classical _ hz5.1
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 3 1 Nat.prime_three trivial hadm
  have hRM : rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup
      ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank) ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D :=
    rankOne_mem_fundamental _ (hl _ trivial)
  have hMcomm : ∀ (a : Fin 6) (R : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K),
      j' a ∈ centralizingMembers Ω {z} → locImg Ω z (j' a) = R.map c.d.ψ →
      Commutes (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup
        ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank)) R := by
    intro a R hz hR
    exact (c.commutes_iff_fund hMz hz hRM (hjimg 0) hR).mp (hj'.commK a)
  have hlin : ∀ {L L' : Subgroup G}
      {R R' : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K},
      L ∈ centralizingMembers Ω {z} → L' ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D →
      R' ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D →
      locImg Ω z L = R.map c.d.ψ → locImg Ω z L' = R'.map c.d.ψ →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L') →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R' := by
    intro L L' R R' hL hL' hR hR' hLR hLR' ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members c.hP1 hL hL' hW
    rw [hLR, hLR'] at hW'
    exact layerGeomD6_3.lift c.d.ψ c.d.ker_le R hR R' hR' ⟨W', hW'⟩
  obtain ⟨N, hNz, hN5N, hWN⟩ := c.exists_distinguisher hsingle hβ htβ hKβ hz4.1 hz5.1 hK4
    hβ4 hK5 hβ5 hc45
  have hLN : c.IsLayerMember N := ETCtx3.IsLayerMember.of_not_commutes c hNz hz4
    (ne_of_linearBlockStandardPair hWN.choose_spec).symm
    (fun h => not_commutes_of_linearBlockStandardPair hWN.choose_spec (commutes_symm h))
  obtain ⟨RN, hRN, hNR⟩ := hLN.exists_fund
  obtain ⟨wN, hwN⟩ := hΩ.classical _ hNz.1
  obtain ⟨hne43, hnc43, hcw43, hnw43⟩ := stdPair_data3 hw4 hw3 ⟨_, hW43⟩
  obtain ⟨hne35, hnc35, hcw35, hnw35⟩ := stdPair_data3 hw3 hw5 ⟨_, hW35⟩
  obtain ⟨hne4N, hnc4N, hcw4N, hnw4N⟩ := stdPair_data3 hw4 hwN hWN
  refine rootFixedGL_of_chain_model3 c ht _ hR4 hR3 hR5 hRN hRM
    (c.modelAdj_of_adj hz4 hz3 hR4 hR3 h4R h3R hw4 hw3 hne43 hnc43 hcw43 hnw43)
    (c.modelAdj_of_adj hz3 hz5 hR3 hR5 h3R h5R hw3 hw5 hne35 hnc35 hcw35 hnw35)
    (hlin hz4 hz3 hR4 hR3 h4R h3R ⟨_, hW43⟩) (hlin hz3 hz5 hR3 hR5 h3R h5R ⟨_, hW35⟩)
    ((c.commutes_iff_fund hz4 hz5 hR4 h4R h5R).mp hc45) (hMcomm 4 R4 hz4 h4R)
    (hMcomm 3 R3 hz3 h3R) (hMcomm 5 R5 hz5 h5R)
    (c.modelAdj_of_adj hz4 hNz hR4 hRN h4R hNR hw4 hwN hne4N hnc4N hcw4N hnw4N)
    ((c.commutes_iff_fund hz5 hNz hR5 h5R hNR).mp hN5N) ?_ ?_ ?_
  · exact fun y hy => c.fixed_of_commutes ht htβ hz4 hβ4 _ (by rw [h4R]; exact ⟨y, hy, rfl⟩)
  · exact fun y hy => c.fixed_of_commutes ht htβ hz3 hβ3 _ (by rw [h3R]; exact ⟨y, hy, rfl⟩)
  · exact fun y hy => c.fixed_of_commutes ht htβ hz5 hβ5 _ (by rw [h5R]; exact ⟨y, hy, rfl⟩)

theorem ETCtx3.toralNormal_plus_gl (c : ETCtx3 .POmegaPlus 6 Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z) (h2t : t * t = 1) (hKt : conjSub t K = K)
    (a₀ : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank)
    (hfix0 : ∀ x ∈ (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a₀).map
      c.d.ψ, Gaps.locAut c.hΩ.conjInvariant htz x = x)
    (hT : RootFixedGL3 (by norm_num : 3 ≤ 6) c a₀ htz) : ToralNormalE3 c htz := by
  classical
  obtain ⟨e, ι, hc, i₀, i₁, h01, γ₀, s₀, t₀, hγ₀, k, hframe, H2⟩ := hT
  have hm3 : 3 ≤ 6 := by norm_num
  have hF : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  let θ : spinGroup (quadPlus 6 (GaloisField 3 1)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have H1 : ∀ y ∈ (((plusDatum 6 (GaloisField 3 1) hm3).rootGroup γ₀ ⊔
      (plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-γ₀)).map (MulAut.conj k).toMonoidHom),
      Gaps.locAut c.hΩ.conjInvariant htz (θ y) = θ y := by
    intro y hy
    refine hfix0 _ ⟨ι y, ?_, rfl⟩
    rw [← hframe]
    exact ⟨y, hy, rfl⟩
  have hσ2 : ∀ y, Gaps.locAut c.hΩ.conjInvariant htz (Gaps.locAut c.hΩ.conjInvariant htz y) = y :=
    Gaps.locAut_locAut c.hΩ.conjInvariant htz h2t
  have hgen := TypeEPattern.range_le_iSup_fund_simplyLaced (p := 3) (f := 1) (t := .POmegaPlus)
    (n := 6) trivial hadm (Or.inr (Or.inl rfl)) c.d.ψ
  have hσr : ∀ k', Gaps.locAut c.hΩ.conjInvariant htz (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := c.locAut_mem_range htz h2t hKt hgen (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  obtain ⟨k₀, v', hk₀⟩ := toralNormal_plus_of_gl_subgroups (p := 3) (f := 1) (by norm_num)
    (le_refl 1) hF (by norm_num : 5 ≤ 6) hm3 θ hker (Gaps.locAut c.hΩ.conjInvariant htz) hσ2 hσr
    h01 hγ₀ k H1 H2
  refine ⟨ι k₀, v' ∘ e, fun γ hγ => ?_⟩
  have hγ' : γ ∘ e.symm ∈ (plusDatum 6 (GaloisField 3 1) hm3).roots := (hc γ).1.mp hγ
  obtain ⟨hnorm, hfix⟩ := hk₀ (γ ∘ e.symm) hγ'
  have hG₁ : (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup γ =
      ((plusDatum 6 (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom :=
    (hc γ).2
  have hG₂ : (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup (-γ) =
      ((plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map ι.toMonoidHom :=
    (hc (-γ)).2
  have hRG : conjSub (ι k₀) ((modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup (-γ)) =
      (((plusDatum 6 (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map ι.toMonoidHom := by
    rw [hG₁, hG₂, ← Subgroup.map_sup]
    exact TypeEPattern.conjSub_map_equiv ι k₀ _
  have himg : (conjSub (ι k₀) ((modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ =
      (((plusDatum 6 (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum 6 (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map θ := by
    rw [hRG, Subgroup.map_map]
  rw [himg]
  refine ⟨hnorm, hfix.trans ?_⟩
  rw [TypeEPattern.charOf_comp_equiv]

end Fixed

theorem e7PartnerToral3 : E7PartnerToral3 := by
  intro G _ _ _ _ K z _ _ c j hj hjimg β hβ t htβ hKβ hβ0 ht
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2t : t * t = 1 := mul_self_of_isClassicalMember3 htβ
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW htβ.mem htβ.orderOf_eq_two
  have hfix0 : ∀ x ∈ (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup
      ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant ht x = x := by
    rw [← hjimg 0]
    exact c.fixed_of_commutes ht htβ (hj.mem 0) hβ0
  exact c.toralNormal_plus_gl ht h2t hKt _ hfix0
    (c.rootFixedGL_of_node_system hsingle hj hjimg hβ htβ hKβ hβ0 ht)

end CFSG.ClassicalInvolution.Q3.Q3W
