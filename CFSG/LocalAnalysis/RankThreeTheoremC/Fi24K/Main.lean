module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Planes
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.NoSevenPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Solvable
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.KStep
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Pure
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiTwentyFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7 Subgroup
open scoped commutatorElement Pointwise

theorem map_normalizer_zpowers_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Bijective f) (x : G) :
    (Subgroup.normalizer (Subgroup.zpowers x : Set G)).map f =
      Subgroup.normalizer (Subgroup.zpowers (f x) : Set H) := by
  rw [Subgroup.map_normalizer_eq_of_bijective _ hf, MonoidHom.map_zpowers]

theorem map_conj_le_of_smul_eq {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)]
    {g : G} {P Q : Sylow p G} (h : g • P = Q) {E : Subgroup G} (hE : E ≤ (P : Subgroup G)) :
    E.map (MulAut.conj g : G →* G) ≤ (Q : Subgroup G) := by
  have hcoe : ((g • P : Sylow p G) : Subgroup G) = (Q : Subgroup G) := congrArg _ h
  have hsmul : (MulAut.conj g • (P : Subgroup G)) = (Q : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hcoe]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hmem : (MulAut.conj g) • y ∈ (MulAut.conj g • (P : Subgroup G)) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P : Subgroup G) (hE hy)
  rw [hsmul] at hmem
  simpa using hmem

theorem normalizer_zpowers_map_le {G H : Type*} [Group G] [Group H] (f : G ≃* H) (x : G)
    {W : Subgroup G} (h : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ W) :
    Subgroup.normalizer (Subgroup.zpowers (f x) : Set H) ≤ W.map (f : G →* H) := by
  have e := map_normalizer_zpowers_eq (f : G →* H) f.bijective x
  rw [MonoidHom.coe_coe] at e
  rw [← e]
  exact Subgroup.map_mono h

theorem nonempty_mulEquiv_he_of_isKGroup (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    {W' Et Jt' : Subgroup J} (hWK : CFSG.Open.IsKGroup W')
    (hWtop : W' ≠ ⊤) (hEtQ : Et ≤ Q7) (hEtc : Nat.card Et = 7 ^ 2)
    (hEtN : ∀ t ∈ Et, t ≠ 1 → Subgroup.normalizer (Subgroup.zpowers t : Set J) ≤ W')
    (hJW : Jt' ≤ W') (hJ1 : Jt' ≠ ⊥) (hJp : ⁅Jt', Jt'⁆ = Jt')
    (hJs : CFSG.Open.IsSubnormal Jt' W') :
    Nonempty (↥Jt' ≃* (TauCeti.CFSGIndex.sporadic .He).Group) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hcE, hcases⟩ := plane_cases hEtQ hEtc
  have hNc : Subgroup.normalizer (Subgroup.zpowers C7 : Set J) ≤ W' := hEtN C7 hcE C7_ne_one
  have hYne : Y7 ≠ 1 := by
    intro h
    apply C7_ne_one
    calc C7 = X7 * Y7 * X7 ^ 6 * Y7 ^ 6 := fi7_cube.2.2.1
      _ = X7 * X7 ^ 6 := by rw [h]; simp
      _ = X7 ^ 7 := by rw [← pow_succ']
      _ = 1 := fi7_cube.1
  have hXne : X7 ≠ 1 := by
    intro h
    apply C7_ne_one
    calc C7 = X7 * Y7 * X7 ^ 6 * Y7 ^ 6 := fi7_cube.2.2.1
      _ = Y7 * Y7 ^ 6 := by rw [h]; simp
      _ = Y7 ^ 7 := by rw [← pow_succ']
      _ = 1 := fi7_cube.2.1
  have hNs : IsSolvable (Subgroup.normalizer (Q7 : Set J)) := by
    have hsol : IsSolvable ↥(Subgroup.normalizer (Subgroup.zpowers C7 : Set J)) :=
      isSolvable_normalizer_zpowers (G := J) sevenLine_c card_centralizer_C7
    refine @Group.isSolvable_of_isSolvable_injective _ _ _ _
      (Subgroup.inclusion (normalizer_le_normalizer_zpowers sevenLine_c))
      (Subgroup.inclusion_injective _) hsol
  have hG : Nat.card J = 1255205709190661721292800 := card_J
  rcases hcases with hY | ⟨lam, hlam7, hXlam⟩
  ·
    have hCy : Subgroup.centralizer ({Y7} : Set J) ≤ W' :=
      (centralizer_singleton_le_normalizer_zpowers Y7).trans (hEtN Y7 hY hYne)
    exfalso
    apply hWtop
    have htop : (⊤ : Subgroup J) ≤ W' := by
      rw [← closure_normalizer_union_centralizer_Y7]
      exact (Subgroup.closure_le W').2 (Set.union_subset hNc hCy)
    exact top_le_iff.1 htop
  · rcases Nat.eq_zero_or_pos lam with h0 | hpos
    ·
      subst h0
      simp only [pow_zero, mul_one] at hXlam
      have hCX : Subgroup.centralizer ({X7} : Set J) ≤ W' :=
        (centralizer_singleton_le_normalizer_zpowers X7).trans (hEtN X7 hXlam hXne)
      exfalso
      apply hWtop
      have htop : (⊤ : Subgroup J) ≤ W' := by
        rw [← closure_normalizer_union_centralizer_X7]
        exact (Subgroup.closure_le W').2 (Set.union_subset hNc hCX)
      exact top_le_iff.1 htop
    ·
      have h1 : 1 ≤ lam := hpos
      have h6 : lam ≤ 6 := by omega
      have hwc : X7 * Y7 ^ lam ∉ Subgroup.zpowers C7 := by
        intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
        have h1 : C7 ^ (n % 7) = C7 ^ n := by
          have := zpow_mod_orderOf C7 n
          rwa [orderOf_C7, Nat.cast_ofNat] at this
        have hk0 : 0 ≤ n % 7 := Int.emod_nonneg n (by norm_num)
        obtain ⟨k, hkdef⟩ := Int.eq_ofNat_of_zero_le hk0
        have hk7 : k < 7 := by
          have hk7' : n % 7 < 7 := Int.emod_lt_of_pos n (by norm_num)
          omega
        have h2 : C7 ^ k = X7 * Y7 ^ lam := by
          rw [← hn, ← h1, hkdef, zpow_natCast]
        have h3 := fi7_cube.2.2.2.2.2 0 0 k 1 lam 0 (by norm_num) (by norm_num) hk7
          (by norm_num) (by omega) (by norm_num) (by simpa using h2)
        omega
      obtain ⟨H, hHcl, ⟨eH⟩, hQH, h, hhH, hhw⟩ := exists_he_le_closure (lam := lam) h1 h6
      have hHW : H ≤ W' := by
        refine hHcl.trans ((Subgroup.closure_le W').2 (Set.union_subset hNc ?_))
        exact (centralizer_singleton_le_normalizer_zpowers _).trans
          (hEtN _ hXlam (fun hne => hwc (hne ▸ Subgroup.one_mem _)))
      obtain ⟨bHe⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
      have eC : H ≃* CFSG.Blueprint.NativeSporadic.Carrier .He := eH.trans bHe.symm
      have hHs : IsSimpleGroup H := by
        haveI hHe : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
          CFSG.Sporadic.He.isSimpleGroup_He
        exact @MulEquiv.isSimpleGroup _ _ _ _ hHe eC
      have hHc : Nat.card H = 4030387200 := by
        rw [Nat.card_congr eC.toEquiv]
        exact CFSG.Sporadic.He.card_He
      have hwQ : X7 * Y7 ^ lam ∈ Q7 := Q7.mul_mem X7_mem (Q7.pow_mem Y7_mem lam)
      have hF1 : ∀ N : Subgroup J, ¬ 7 ∣ Nat.card N →
          H ≤ Subgroup.normalizer (N : Set J) → N = ⊥ := fun N hN hHN =>
        eq_bot_of_le_normalizer sevenLine_c hQH hwQ hwc hhH hhw hN hHN
      have hJeq : Jt' = H :=
        eq_of_isKGroup_of_le hb hOrd hG hWK hWtop hHW hHs hHc hQH card_Q7 hF1 hNs hJW hJ1 hJp hJs
      exact ⟨(MulEquiv.subgroupCongr hJeq).trans eH⟩

theorem threeFourTwoAt_fi24Prime_of_isKGroup (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hKX : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :
    ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)) ≤ 2 :=
    CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime ≠ 0
      rw [CFSG.Sporadic.Fi24.card_Fi24prime]
      norm_num)
  have hsq : 7 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) := by
    show 7 ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime
    rw [CFSG.Sporadic.Fi24.card_Fi24prime]
    norm_num
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .Fi24Prime)
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime hO
    (by norm_num) hsq
  haveI := hX
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    Finite.of_equiv _ CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv.some.toEquiv
  refine threeFourTwoAt_of_forall_model hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn e hrk hC hcomp hER hE hEc hcore hRY hKY Jt hJ hne hJp hJs hQ
  haveI := hKn
  obtain ⟨eC⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .Fi24Prime)
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv ⟨e⟩
  haveI : Finite K := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨hfac, hnc⟩ := fi24Seven_sylow_facts (K := K) ⟨e⟩
  set W : Subgroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    (Y₀.subgroupOf K).map e.toMonoidHom with hWdef
  have hW : W ≠ ⊤ := by
    intro htop
    apply hKY
    have h1 : Y₀.subgroupOf K = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [← hWdef, htop, Subgroup.map_top_of_surjective _ e.surjective]
    intro k hk
    exact Subgroup.mem_subgroupOf.mp (h1 ▸ Subgroup.mem_top (⟨k, hk⟩ : K))
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTc : Nat.card (T : Subgroup K) = 7 ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hRKc : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = 7 ^ 3 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTc]
  obtain ⟨a', ha', b', hb', hab⟩ := hnc T
  have hnabRK : ∃ x y : ↥((R : Subgroup Y) ⊓ K : Subgroup Y), x * y ≠ y * x := by
    refine ⟨⟨(a' : Y), hT ▸ Subgroup.mem_map_of_mem K.subtype ha'⟩,
      ⟨(b' : Y), hT ▸ Subgroup.mem_map_of_mem K.subtype hb'⟩, fun h => hab ?_⟩
    have hY : (a' : Y) * b' = b' * a' := congrArg Subtype.val h
    exact Subtype.ext hY
  have hTnc : ∃ x ∈ (R : Subgroup Y) ⊓ K, ∃ y ∈ (R : Subgroup Y) ⊓ K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnabRK
    exact ⟨x, x.2, y, y.2, fun h => hxy (Subtype.ext h)⟩
  have hZKc : Subgroup.center K = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab,
      Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    exact h
  have hZK : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzK, hzC⟩
    have h : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
    rw [hZKc, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h)
  have hout7 : ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eC).toEquiv]
    intro h7
    haveI : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)) :=
      MulEquiv.finite_left
    have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)) := Nat.card_pos
    have := Nat.le_of_dvd hpos h7
    omega
  obtain ⟨E', hE'RK, hE'c, hE'N⟩ :=
    exists_plane_normalizer_inf_le (p := 7) (by norm_num) R hER hE hEc hcore hZK hout7 hRKc hTnc
  have hE'K : E' ≤ K := hE'RK.trans inf_le_right
  let θ : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group ≃* ↥CFSG.Sporadic.Fi24.J :=
    e.symm.trans (eC.trans CFSG.Sporadic.Fi24.fi24EquivJ)
  let θm : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group →* ↥CFSG.Sporadic.Fi24.J := θ
  set EK : Subgroup K := E'.subgroupOf K with hEKdef
  have hEKc : Nat.card EK = 7 ^ 2 := by
    rw [hEKdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'K).toEquiv, hE'c]
  set EX : Subgroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    EK.map e.toMonoidHom with hEXdef
  have hEXc : Nat.card EX = 7 ^ 2 := by
    rw [hEXdef, Subgroup.card_map_of_injective e.injective, hEKc]
  set EXJ : Subgroup ↥CFSG.Sporadic.Fi24.J := EX.map θm with hEXJdef
  have hEXJc : Nat.card EXJ = 7 ^ 2 := by
    rw [hEXJdef, Subgroup.card_map_of_injective θ.injective, hEXc]
  have hEXJp : IsPGroup 7 EXJ := IsPGroup.of_card hEXJc
  obtain ⟨P, hP⟩ := hEXJp.exists_le_sylow
  obtain ⟨S0, hS0⟩ := Q7_sylow
  obtain ⟨gg, hgg⟩ := MulAction.exists_smul_eq ↥CFSG.Sporadic.Fi24.J P S0
  let γm : ↥CFSG.Sporadic.Fi24.J →* ↥CFSG.Sporadic.Fi24.J :=
    (MulAut.conj gg : ↥CFSG.Sporadic.Fi24.J →* ↥CFSG.Sporadic.Fi24.J)
  have hγapply : ∀ x : ↥CFSG.Sporadic.Fi24.J, γm x = gg * x * gg⁻¹ := fun x =>
    MulAut.conj_apply gg x
  have hγinj : Function.Injective γm := by
    intro x y hxy
    rw [hγapply, hγapply] at hxy
    have h1 : gg * x = gg * y := by
      have h2 := congrArg (fun z => z * gg) hxy
      simpa [mul_assoc] using h2
    exact mul_left_cancel h1
  have hγsurj : Function.Surjective γm := by
    intro y
    refine ⟨gg⁻¹ * y * gg, ?_⟩
    rw [hγapply]
    group
  have hEXJQ : EXJ.map γm ≤ Q7 := by
    have h1 : EXJ.map γm ≤ (S0 : Subgroup ↥CFSG.Sporadic.Fi24.J) :=
      map_conj_le_of_smul_eq (p := 7) hgg hP
    rwa [hS0] at h1
  let φm : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group →* ↥CFSG.Sporadic.Fi24.J :=
    γm.comp θm
  have hφinj : Function.Injective φm := hγinj.comp θ.injective
  have hφsurj : Function.Surjective φm := hγsurj.comp θ.surjective
  have hN_of_E' : ∀ y : K, (y : Y) ∈ E' → (y : Y) ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers (e y) : Set
        (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) ≤ W := by
    intro y hy hy1
    have hzy : (Subgroup.zpowers (y : Y)).subgroupOf K = Subgroup.zpowers y := by
      rw [show (y : Y) = K.subtype y from rfl, ← MonoidHom.map_zpowers K.subtype y]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    have hNs : Subgroup.normalizer (Subgroup.zpowers y : Set K) ≤ Y₀.subgroupOf K := by
      have hle : Subgroup.zpowers (y : Y) ≤ K := Subgroup.zpowers_le.2 y.2
      have heq : (Subgroup.normalizer (Subgroup.zpowers (y : Y) : Set Y)).subgroupOf K =
          Subgroup.normalizer (Subgroup.zpowers y : Set K) := by
        rw [Subgroup.subgroupOf_normalizer_eq hle, hzy]
      have hsub : (Subgroup.normalizer (Subgroup.zpowers (y : Y) : Set Y)).subgroupOf K ≤
          Y₀.subgroupOf K := by
        intro k hk
        exact hE'N (y : Y) hy hy1 ⟨Subgroup.mem_subgroupOf.1 hk, k.2⟩
      rwa [heq] at hsub
    simpa [hWdef] using normalizer_zpowers_map_le e y hNs
  set W' : Subgroup ↥CFSG.Sporadic.Fi24.J := (W.map θm).map γm with hW'def
  have hW'top : W' ≠ ⊤ := by
    intro htop
    apply hW
    have h1 : W.map θm = ⊤ := by
      refine Subgroup.map_injective hγinj ?_
      rw [Subgroup.map_top_of_surjective γm hγsurj, ← hW'def]
      exact htop
    have hθinj : Function.Injective θm := θ.injective
    refine Subgroup.map_injective hθinj ?_
    rw [h1, Subgroup.map_top_of_surjective θm θ.surjective]
  have hW'K : CFSG.Open.IsKGroup W' :=
    (hKX.of_surjective φm hφsurj).of_injective W'.subtype W'.subtype_injective
  set Jt' : Subgroup ↥CFSG.Sporadic.Fi24.J := (Jt.map θm).map γm with hJt'def
  have hJt'W : Jt' ≤ W' := by
    rw [hJt'def, hW'def]
    exact Subgroup.map_mono (Subgroup.map_mono hJ)
  have hJt'1 : Jt' ≠ ⊥ := by
    rw [hJt'def]
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ hγinj] at hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ θ.injective] at hbot
    exact hne hbot
  have hJt'p : ⁅Jt', Jt'⁆ = Jt' := by
    rw [hJt'def, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      show ⁅Jt, Jt⁆ = Jt from hJp]
  have hJt's : CFSG.Open.IsSubnormal Jt' W' := by
    rw [hJt'def, hW'def]
    exact CFSG.Open.IsSubnormal.map γm (CFSG.Open.IsSubnormal.map θm hJs)
  set E'' : Subgroup ↥CFSG.Sporadic.Fi24.J := EXJ.map γm with hE''def
  have hE''Q : E'' ≤ Q7 := by
    rw [hE''def]
    exact hEXJQ
  have hE''c : Nat.card E'' = 7 ^ 2 := by
    rw [hE''def, Subgroup.card_map_of_injective hγinj, hEXJc]
  have hE''N : ∀ t ∈ E'', t ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers t : Set ↥CFSG.Sporadic.Fi24.J) ≤ W' := by
    intro t ht ht1
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    have hy' : (y : Y) ∈ E' := Subgroup.mem_subgroupOf.1 hy
    have hy1 : (y : Y) ≠ 1 := by
      intro h1
      apply ht1
      have hy1' : y = 1 := Subtype.ext h1
      rw [hy1', map_one, map_one, map_one]
    have h0 := hN_of_E' y hy' hy1
    have h1 : Subgroup.normalizer (Subgroup.zpowers (θm (e y)) :
        Set ↥CFSG.Sporadic.Fi24.J) ≤ W.map θm := by
      rw [← map_normalizer_zpowers_eq θm ⟨θ.injective, θ.surjective⟩ (e y)]
      exact Subgroup.map_mono h0
    have h2 : Subgroup.normalizer (Subgroup.zpowers (γm (θm (e y))) :
        Set ↥CFSG.Sporadic.Fi24.J) ≤ (W.map θm).map γm := by
      rw [← map_normalizer_zpowers_eq γm ⟨hγinj, hγsurj⟩ (θm (e y))]
      exact Subgroup.map_mono h1
    rw [hW'def]
    exact h2
  have hJt'map : Jt' = Jt.map φm := by
    rw [hJt'def]
    exact Subgroup.map_map Jt γm θm
  obtain ⟨eHe⟩ := nonempty_mulEquiv_he_of_isKGroup hb hOrd hW'K hW'top hE''Q hE''c hE''N
    hJt'W hJt'1 hJt'p hJt's
  refine ⟨.sporadic .Fi24Prime, .sporadic .He, ?_, ⟨e⟩, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))))
  · let gfin : ↥Jt ≃* (TauCeti.CFSGIndex.sporadic .He).Group :=
      (Subgroup.equivMapOfInjective Jt φm hφinj).trans (hJt'map ▸ eHe)
    exact ⟨(gfin : ↥Jt →* (TauCeti.CFSGIndex.sporadic .He).Group), MulEquiv.surjective gfin⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
