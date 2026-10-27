module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LieType.ChevTwo.OppCl.SmallU33
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PI
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open scoped commutatorElement

theorem false_of_A6_U33_aux_perfect {G : Type*} [Group G] {V L C : Subgroup G} [V.Normal]
    [L.Normal] (hC : C ≤ Subgroup.centralizer (V : Set G)) (hL : L = ⁅L, L⁆ ⊔ C) :
    ⁅V, L⁆ ≤ ⁅⁅V, L⁆, L⁆ := by
  set W : Subgroup G := ⁅⁅V, L⁆, L⁆
  haveI : W.Normal := inferInstance
  let f : G →* G ⧸ W := QuotientGroup.mk' W
  have hker : f.ker = W := QuotientGroup.ker_mk' W
  have h1 : ⁅⁅L.map f, V.map f⁆, L.map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.commutator_comm L V,
      Subgroup.map_eq_bot_iff, hker]
  have h2 : ⁅⁅V.map f, L.map f⁆, L.map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hker]
  have h3 : ⁅⁅L.map f, L.map f⁆, V.map f⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : ⁅L.map f, L.map f⁆ ≤ Subgroup.centralizer (V.map f : Set (G ⧸ W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  have h5 : C.map f ≤ Subgroup.centralizer (V.map f : Set (G ⧸ W)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hC hc) v hv
    show f v * f c = f c * f v
    rw [← map_mul, ← map_mul, this]
  have h6 : L.map f ≤ Subgroup.centralizer (V.map f : Set (G ⧸ W)) := by
    conv_lhs => rw [hL]
    rw [Subgroup.map_sup]
    exact sup_le (by rw [Subgroup.map_commutator]; exact h4) h5
  have h7 : ⁅L.map f, V.map f⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h6
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hker] at h7
  rwa [Subgroup.commutator_comm] at h7

theorem false_of_A6_U33_aux_centralizes {G : Type*} [Group G] {V L C P U : Subgroup G}
    (hUV : U ≤ V) (hUL : ⁅U, L⁆ = U) (hC : C ≤ Subgroup.centralizer (V : Set G))
    (hLP : ⁅L, P⁆ ≤ C) (hPU : ⁅P, U⁆ ≤ Subgroup.centralizer (L : Set G)) : ⁅P, U⁆ = ⊥ := by
  have h1 : ⁅⁅L, P⁆, U⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLP.trans (hC.trans (Subgroup.centralizer_le hUV))
  have h2 : ⁅⁅P, U⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hPU
  have h3 : ⁅⁅U, L⁆, P⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hUL, Subgroup.commutator_comm] at h3
  exact h3

theorem false_of_A6_U33_aux_star {X : Type} [Group X] [Finite X] {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls) (hLn : L.Normal)
    (hsimple : IsSimpleGroup ↥Ls) (hcen : Subgroup.center ↥Ls = ⊥) {y : X} (hy : y ∈ cMHat L) :
    toStar T y ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup (X ⧸ gnC T) := (O2In L).map (toStar T) with hN
  have hLs : L.map (toStar T) = Ls := hL.2
  have hNLs : N ≤ Ls := by
    rintro _ ⟨o, ho, rfl⟩
    rw [← hLs]
    exact ⟨o, ho.1, rfl⟩
  have hnorm : (N.subgroupOf Ls).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨o, ho, hon⟩ : (n : X ⧸ gnC T) ∈ N := hn
    obtain ⟨l, hl, hlg⟩ : (g : X ⧸ gnC T) ∈ L.map (toStar T) := by rw [hLs]; exact g.2
    have hlo : l * o * l⁻¹ ∈ O2In L :=
      ⟨L.mul_mem (L.mul_mem hl ho.1) (L.inv_mem hl),
        (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem o ho.2 l⟩
    show (g : X ⧸ gnC T) * n * (g : X ⧸ gnC T)⁻¹ ∈ N
    refine ⟨l * o * l⁻¹, hlo, ?_⟩
    rw [map_mul, map_mul, map_inv, hon, hlg]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Ls) with hbot | htop
  · have hN1 : ∀ o ∈ O2In L, toStar T o = 1 := by
      intro o ho
      have hmem : toStar T o ∈ N := ⟨o, ho, rfl⟩
      have h1 : (⟨toStar T o, hNLs hmem⟩ : ↥Ls) ∈ N.subgroupOf Ls := hmem
      rw [hbot, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨l, hl, rfl⟩ : a ∈ L.map (toStar T) := by rw [hLs]; exact ha
    have hc : y * l * y⁻¹ * l⁻¹ ∈ O2In L :=
      ⟨L.mul_mem (hLn.conj_mem l hl y) (L.inv_mem hl),
        exists_conj_centralized_aux_commutator hy hl⟩
    have h1 := hN1 _ hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : ⁅toStar T y, toStar T l⁆ = 1 := h1
    exact ((commutatorElement_eq_one_iff_mul_comm.1 h2).symm)
  · exfalso
    have hNtop : N = Ls := by
      refine le_antisymm hNLs fun a ha => ?_
      have : (⟨a, ha⟩ : ↥Ls) ∈ N.subgroupOf Ls := by rw [htop]; trivial
      exact this
    have hN2 : IsPGroup 2 ↥N :=
      ((CFSG.pCore_isPGroup (p := 2) (G := X)).to_le inf_le_right).map (toStar T)
    have hLs2 : IsPGroup 2 ↥Ls := by rw [← hNtop]; exact hN2
    haveI := hsimple.toNontrivial
    haveI := hLs2.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Ls))
    rw [hcen, Subgroup.mem_bot] at hz
    exact hz1 (Subtype.ext hz)

theorem false_of_A6_U33_aux_inf_center {X : Type} [Group X] [Finite X] {T U : Subgroup X}
    (hT : IsPGroup 2 T) (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set X)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set X)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : X) ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : X) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set X)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem false_of_A6_U33_aux_Z1 {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {U : Subgroup X} [hUn : U.Normal] (hUV : U ≤ gnV T) (hU : U ≠ ⊥) :
    ∃ z ∈ U ⊓ CFSG.Quasithin.omegaOneCenterOf T, z ≠ 1 := by
  have hexp := (gnV_comm_exp_two hX).2
  have hU2 : IsPGroup 2 ↥U := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hexp (g : X) (hUV g.2)⟩
  have hUT : U ≤ T := (isC2_normalizer_aux0 hU2).trans (pCore_le_gnC_aux1 hX.sylow)
  have hTn : T ≤ Subgroup.normalizer (U : Set X) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hUn.conj_mem x hx t, fun hx => by
      have := hUn.conj_mem _ hx t⁻¹
      simpa [mul_assoc] using this⟩
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (false_of_A6_U33_aux_inf_center hX.sylow.2.1 hUT hTn hU)
  refine ⟨z, ⟨hz.1, ?_⟩, fun h => hz1 (Subtype.ext h)⟩
  unfold CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf CFSG.Quasithin.centerOf
  exact Subgroup.subset_closure ⟨⟨hz.2.1, hz.2.2⟩, hexp z (hUV hz.1)⟩

theorem false_of_A6_U33_aux_lift {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] (φ : A →* B) {H : Subgroup A} {Q : Subgroup B} (hQ : IsPGroup p Q)
    (hQH : Q ≤ H.map φ) : ∃ P : Subgroup A, P ≤ H ∧ IsPGroup p P ∧ P.map φ = Q := by
  set W := H ⊓ Q.comap φ
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := hQH hq
    exact ⟨⟨a, ha, hq⟩, rfl⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p W))
  have htop : ((T.mapSurjective hψ : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, (Subgroup.map_subtype_le _).trans inf_le_left,
    T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : Q) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

theorem false_of_A6_U33_aux_pElement_map {X Y : Type*} [Group X] [Finite X] [Group Y]
    (φ : X →* Y) (hφ : Function.Surjective φ) (P : Subgroup Y) :
    pElementSubgroup 2 P ≤ (pElementSubgroup 2 (P.comap φ)).map φ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pElementSubgroup
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨hyP, k, hk⟩
  have hF : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hFP : Subgroup.zpowers y ≤ (P.comap φ).map φ := by
    rw [Subgroup.map_comap_eq_self_of_surjective hφ]
    exact Subgroup.zpowers_le.2 hyP
  obtain ⟨B, hBP, hB, hBF⟩ := false_of_A6_U33_aux_lift φ hF hFP
  have hyB : y ∈ B.map φ := by rw [hBF]; exact Subgroup.mem_zpowers y
  obtain ⟨b, hb, rfl⟩ := hyB
  refine ⟨b, Subgroup.subset_closure ⟨hBP hb, ?_⟩, rfl⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hB ⟨b, hb⟩
  exact ⟨j, (Subgroup.orderOf_coe (⟨b, hb⟩ : B)).trans hj⟩

theorem false_of_A6_U33_aux_c {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) [hLn : L.Normal] {P : Subgroup (X ⧸ gnC T)} (hPLs : P ≤ Ls)
    {Z : Subgroup X} (hZ : pElementSubgroup 2 (P.comap (toStar T)) ≤ Subgroup.centralizer (Z : Set X))
    (hZC : gnC T ≤ Subgroup.centralizer (Z : Set X)) {y : X ⧸ gnC T}
    (hy : y ∈ pElementSubgroup 2 P) (hy3 : orderOf y = 3) :
    ∃ c ∈ L, c ∈ Subgroup.centralizer (Z : Set X) ∧ orderOf c = 3 := by
  obtain ⟨x, hx, rfl⟩ := false_of_A6_U33_aux_pElement_map (toStar T)
    (QuotientGroup.mk'_surjective _) P hy
  have hxP : toStar T x ∈ P := pElementSubgroup_le (P.comap (toStar T)) hx
  have hxLs : x ∈ Ls.comap (toStar T) := hPLs hxP
  rw [(liftOf_central_ext hX hLs hL).2] at hxLs
  haveI : (gnC T).Normal := inferInstance
  obtain ⟨l, hl, z, hz, hlz⟩ := Subgroup.mem_sup_of_normal_right.1 hxLs
  have hlx : l = x * z⁻¹ := by rw [← hlz]; group
  have hlC : l ∈ Subgroup.centralizer (Z : Set X) := by
    rw [hlx]
    exact Subgroup.mul_mem _ (hZ hx) (Subgroup.inv_mem _ (hZC hz))
  have hφl : toStar T l = toStar T x := by
    rw [hlx, map_mul, map_inv]
    have : toStar T z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [this, inv_one, mul_one]
  have hdvd : 3 ∣ orderOf l := by
    have := orderOf_map_dvd (toStar T) l
    rwa [hφl, hy3] at this
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := orderOf_pos l
    omega
  refine ⟨l ^ m, Subgroup.pow_mem _ hl m, Subgroup.pow_mem _ hlC m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 ⟨3, by rw [hm]; ring⟩, hm]
  exact Nat.mul_div_cancel 3 (Nat.pos_of_ne_zero hm0)

theorem false_of_A6_U33_aux_two_mul {O : Type*} [Group O] [Finite O] {r j : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) {R : Subgroup O} (hR : Nat.card R = r)
    (hN : Nat.card (Subgroup.normalizer (R : Set O)) = 2 ^ j * r) (hj : ¬ 2 ^ j ∣ r - 1) :
    ∃ g : O, orderOf g = 2 * r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (R : Set O) with hNdef
  haveI hRn : (R.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hRnc : Nat.card (R.subgroupOf N) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : R ≤ N)).toEquiv, hR]
  haveI : IsCyclic ↥(R.subgroupOf N) := isCyclic_of_prime_card hRnc
  let ψ : ↥N →* MulAut ↥(R.subgroupOf N) := MulAut.conjNormal
  have hAut : Nat.card (MulAut ↥(R.subgroupOf N)) = r - 1 := by
    rw [IsCyclic.card_mulAut, hRnc, Nat.totient_prime hr.out]
  have hkr : Nat.card ψ.ker * Nat.card ψ.range = Nat.card N := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h
    rw [h, mul_comm]
  have hrange : Nat.card ψ.range ∣ r - 1 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hker : 2 ∣ Nat.card ψ.ker := by
    by_contra hodd
    have hcop : Nat.Coprime (2 ^ j) (Nat.card ψ.ker) :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have hd : 2 ^ j ∣ Nat.card ψ.ker * Nat.card ψ.range := by
      rw [hkr, hN]
      exact dvd_mul_right _ _
    exact hj ((hcop.dvd_of_dvd_mul_left hd).trans hrange)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 2 hker
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) r (by rw [hR])
  have hψt : ψ (t : ↥N) = 1 := t.2
  have hcomm : Commute (((t : ↥N) : O)) ((x : O)) := by
    have hxN : (x : O) ∈ N := Subgroup.le_normalizer x.2
    have hmem : (⟨(x : O), hxN⟩ : ↥N) ∈ R.subgroupOf N := x.2
    have h1 := congrArg (fun z : ↥(R.subgroupOf N) => (((z : ↥N)) : O))
      (DFunLike.congr_fun hψt ⟨⟨(x : O), hxN⟩, hmem⟩)
    have h2 : (t : O) * (x : O) * (t : O)⁻¹ = (x : O) := h1
    exact (mul_inv_eq_iff_eq_mul.1 h2)
  refine ⟨((t : ↥N) : O) * (x : O), ?_⟩
  have hot : orderOf (((t : ↥N) : O)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hox : orderOf (x : O) = r := by rw [Subgroup.orderOf_coe, hx]
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime, hot, hox]
  rw [hot, hox]
  exact (Nat.coprime_primes Nat.prime_two hr.out).2 (Ne.symm hr2)

theorem false_of_A6_U33_aux_order {O : Type*} [Group O] [Finite O] {a r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (hO : Nat.card O = 2 ^ a * r)
    (hcase : ∀ k ≤ a, 2 ^ k % r = 1 → ¬ 2 ^ (a - k) ∣ r - 1) :
    ∃ g : O, orderOf g = 2 * r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := O) r (by rw [hO]; exact dvd_mul_left _ _)
  set R : Subgroup O := Subgroup.zpowers x with hRdef
  have hR : Nat.card R = r := by rw [Nat.card_zpowers, hx]
  have hRp : IsPGroup r R := IsPGroup.of_card (n := 1) (by rw [hR, pow_one])
  have hidx : R.index = 2 ^ a := by
    have h1 := Subgroup.card_mul_index R
    rw [hR, hO, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right hr.out.pos h1
  have hnd : ¬ r ∣ R.index := by
    rw [hidx]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 (hr.out.dvd_of_dvd_pow h))
  let S : Sylow r O := hRp.toSylow hnd
  have hS : (S : Subgroup O) = R := rfl
  have hmod := card_sylow_modEq_one r O
  have hdvd := Sylow.card_dvd_index S
  rw [hS, hidx] at hdvd
  obtain ⟨k, hk, hnk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hmod1 : 2 ^ k % r = 1 := by
    have h := hmod
    rw [hnk] at h
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (a := 1) hr.out.one_lt] at h
  have hNidx : (Subgroup.normalizer (R : Set O)).index = 2 ^ k := by
    rw [← hnk, Sylow.card_eq_index_normalizer S]
    rfl
  have hN : Nat.card (Subgroup.normalizer (R : Set O)) = 2 ^ (a - k) * r := by
    have h1 := Subgroup.card_mul_index (Subgroup.normalizer (R : Set O))
    rw [hNidx, hO] at h1
    refine Nat.eq_of_mul_eq_mul_right (pow_pos Nat.two_pos k) ?_
    rw [h1, mul_assoc, mul_comm r, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  exact false_of_A6_U33_aux_two_mul hr2 hR hN (hcase k hk hmod1)

theorem false_of_A6_U33_aux_normalizer {Y : Type*} [Group Y] (p : ℕ) (P : Subgroup Y) :
    P ≤ Subgroup.normalizer (pElementSubgroup p P : Set Y) := by
  have key : ∀ g ∈ P, ∀ n ∈ pElementSubgroup p P, g * n * g⁻¹ ∈ pElementSubgroup p P := by
    intro g hg n hn
    unfold pElementSubgroup at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      refine ⟨P.mul_mem (P.mul_mem hg hx.1) (P.inv_mem hg), ?_⟩
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      simpa [MulAut.conj_apply, hk] using this
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by simpa [mul_assoc] using key g⁻¹ (P.inv_mem hg) _ hx⟩

theorem false_of_A6_U33_aux_three_of_order {Y : Type} [Group Y] [Finite Y] {Ls S₀ P : Subgroup Y}
    {a b r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hcard : Nat.card Ls = 2 ^ a * (3 ^ b * r))
    (hcase : ∀ k ≤ a, 2 ^ k % r = 1 → ¬ 2 ^ (a - k) ∣ r - 1)
    (hno : ∀ g ∈ Ls, orderOf g ≠ 2 * r) (hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf S₀ Ls)
    (hP : IsMinOverBorel Ls S₀ P) : ∃ y ∈ pElementSubgroup 2 P, orderOf y = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  set O : Subgroup Y := pElementSubgroup 2 P with hOdef
  have hOP : O ≤ P := pElementSubgroup_le P
  have hPLs : P ≤ Ls := hP.1
  have hS₀Ls : S₀ ≤ Ls := hS₀.1
  have hS₀P : S₀ ≤ P := (le_inf hS₀Ls Subgroup.le_normalizer).trans hP.2.1.le
  have hS₀O : S₀ ≤ O := by
    intro s hs
    apply Subgroup.subset_closure
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hS₀.2.1 ⟨s, hs⟩
    exact ⟨hS₀P hs, k, (Subgroup.orderOf_coe (⟨s, hs⟩ : S₀)).trans hk⟩
  have hmodd : Odd (3 ^ b * r) :=
    Odd.mul (Odd.pow (by decide)) (hr.out.odd_of_ne_two hr2)
  have hS₀card : Nat.card S₀ = 2 ^ a := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hS₀.2.1
    have h1 := Subgroup.card_mul_index (S₀.subgroupOf Ls)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀Ls).toEquiv, he, hcard] at h1
    have hidx : Odd (S₀.subgroupOf Ls).index := Nat.odd_iff.2 (by
      have := hS₀.2.2
      omega)
    rcases lt_trichotomy e a with hlt | heq | hgt
    · exfalso
      have h2 : 2 ^ e * (S₀.subgroupOf Ls).index = 2 ^ e * (2 ^ (a - e) * (3 ^ b * r)) := by
        rw [h1, ← mul_assoc (2 ^ e) (2 ^ (a - e)), ← pow_add, Nat.add_sub_cancel' hlt.le]
      have h3 := Nat.eq_of_mul_eq_mul_left (pow_pos Nat.two_pos e) h2
      have h4 : Even (S₀.subgroupOf Ls).index := by
        rw [h3]
        exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
      exact (Nat.not_even_iff_odd.2 hidx) h4
    · rw [he, heq]
    · exfalso
      have h2 : 2 ^ a * (2 ^ (e - a) * (S₀.subgroupOf Ls).index) = 2 ^ a * (3 ^ b * r) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le, h1]
      have h3 := Nat.eq_of_mul_eq_mul_left (pow_pos Nat.two_pos a) h2
      have h4 : Even (3 ^ b * r) := by
        rw [← h3]
        exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
      exact (Nat.not_even_iff_odd.2 hmodd) h4
  have h3O : ¬ 3 ∣ Nat.card O := by
    intro h3
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) 3 h3
    exact hcon (y : Y) y.2 (by rw [Subgroup.orderOf_coe]; exact hy)
  have hOdvd : Nat.card O ∣ 2 ^ a * (3 ^ b * r) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (hOP.trans hPLs)
  obtain ⟨c, hc⟩ : 2 ^ a ∣ Nat.card O := by
    rw [← hS₀card]
    exact Subgroup.card_dvd_of_le hS₀O
  have hcdvd : c ∣ 3 ^ b * r := by
    rw [hc] at hOdvd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos Nat.two_pos a) hOdvd
  have h3c : ¬ 3 ∣ c := fun h => h3O (hc ▸ dvd_mul_of_dvd_right h _)
  have hcr : c ∣ r :=
    (Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3c).symm).dvd_of_dvd_mul_left
      hcdvd
  rcases (Nat.dvd_prime hr.out).1 hcr with hc1 | hcr'
  ·
    have hOcard : Nat.card O = 2 ^ a := by rw [hc, hc1, mul_one]
    have hSO : S₀ = O := Subgroup.eq_of_le_of_card_ge hS₀O (by rw [hS₀card, hOcard])
    have hPN : P ≤ Subgroup.normalizer (S₀ : Set Y) := by
      rw [hSO]
      exact false_of_A6_U33_aux_normalizer 2 P
    exact hP.2.1.not_ge (le_inf hPLs hPN)
  ·
    have hOcard : Nat.card O = 2 ^ a * r := by rw [hc, hcr']
    obtain ⟨g, hg⟩ := false_of_A6_U33_aux_order (O := ↥O) hr2 hOcard hcase
    exact hno (g : Y) (hOP.trans hPLs g.2) (by rw [Subgroup.orderOf_coe]; exact hg)

theorem false_of_A6_U33_aux_xlevel_gen (k542 : K542) {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) [hLn : L.Normal]
    (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls) {P : Subgroup X}
    (hP : P ≤ cMHat L) :
    ⁅P, ⁅gnV T, Ls.comap (toStar T)⁆⁆ = ⊥ ∧
      ∃ z ∈ ⁅gnV T, Ls.comap (toStar T)⁆ ⊓ CFSG.Quasithin.omegaOneCenterOf T, z ≠ 1 := by
  have hsmall : Small1522 ↥Ls := by
    rcases hbig with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨hsimple, hcen⟩ := small1522_simple_center hsmall
  have hLs := hl.comp
  have hL := hl.lift
  have hLfeq : Ls.comap (toStar T) = L ⊔ gnC T := (liftOf_central_ext hl.gn hLs.1 hL).2
  haveI hLfn : (Ls.comap (toStar T)).Normal := by rw [hLfeq]; infer_instance
  haveI hVn : (gnV T).Normal := by unfold gnV; infer_instance
  haveI hUn : ⁅gnV T, Ls.comap (toStar T)⁆.Normal := inferInstance
  have hUV : ⁅gnV T, Ls.comap (toStar T)⁆ ≤ gnV T := Subgroup.commutator_le_left _ _
  have hk := k542 X T hl.gn Ls hLs.1 (hl.good.shape Ls hLs).1 (by
    rcases hbig with h | ⟨d, ⟨q, hq, hd⟩, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨d, q, hq, hd, he⟩)
  have hstar : ∀ y ∈ P, toStar T y ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
    fun y hy => false_of_A6_U33_aux_star hL hLn hsimple hcen (hP hy)
  have hPU : ⁅P, ⁅gnV T, Ls.comap (toStar T)⁆⁆ ≤
      Subgroup.centralizer ((Ls.comap (toStar T) : Subgroup X) : Set X) := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    exact (hk x (hstar x hx) u hu).2
  have hperf : ⁅Ls, Ls⁆ = Ls := by
    rw [← Subgroup.map_subtype_commutator, hLs.1.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  have hLfC : Ls.comap (toStar T) = ⁅Ls.comap (toStar T), Ls.comap (toStar T)⁆ ⊔ gnC T := by
    have hmap : (Ls.comap (toStar T)).map (toStar T) = Ls :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Ls
    have h1 : (⁅Ls.comap (toStar T), Ls.comap (toStar T)⁆).map (toStar T) = Ls := by
      rw [Subgroup.map_commutator, hmap, hperf]
    have h2 := Subgroup.comap_map_eq (toStar T) ⁅Ls.comap (toStar T), Ls.comap (toStar T)⁆
    rw [h1, QuotientGroup.ker_mk'] at h2
    exact h2
  have hperfU : ⁅⁅gnV T, Ls.comap (toStar T)⁆, Ls.comap (toStar T)⁆ =
      ⁅gnV T, Ls.comap (toStar T)⁆ :=
    le_antisymm (Subgroup.commutator_le_left _ _)
      (false_of_A6_U33_aux_perfect (le_refl (gnC T)) hLfC)
  have hLP : ⁅Ls.comap (toStar T), P⁆ ≤ gnC T := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    have hc := Subgroup.mem_centralizer_iff.1 (hstar x hx) (toStar T l) hl
    have h1 : ⁅toStar T l, toStar T x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [← map_commutatorElement] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hPU0 : ⁅P, ⁅gnV T, Ls.comap (toStar T)⁆⁆ = ⊥ :=
    false_of_A6_U33_aux_centralizes hUV hperfU (le_refl (gnC T)) hLP hPU
  have hU0 : ⁅gnV T, Ls.comap (toStar T)⁆ ≠ ⊥ := by
    intro h
    have h1 : gnV T ≤ Subgroup.centralizer ((Ls.comap (toStar T) : Subgroup X) : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have h2 : Ls.comap (toStar T) ≤ gnC T := by
      intro l hl
      show l ∈ Subgroup.centralizer (gnV T : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.1 (h1 hv) l hl).symm
    have h3 : Ls ≤ ⊥ := by
      intro a ha
      obtain ⟨l, hl, rfl⟩ : a ∈ (Ls.comap (toStar T)).map (toStar T) := by
        rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
        exact ha
      exact (Subgroup.mem_bot).2 ((QuotientGroup.eq_one_iff _).2 (h2 hl))
    haveI := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Ls).1 inferInstance (le_bot_iff.1 h3)
  exact ⟨hPU0, false_of_A6_U33_aux_Z1 hl.gn hUV hU0⟩

theorem false_of_A6_U33_aux_arith (t : ℕ) : t * (t ^ 2 - 1) ≠ 360 ∧ t * (t ^ 2 - 1) ≠ 6048 := by
  have hbound : 21 ≤ t → 21 * 440 ≤ t * (t ^ 2 - 1) := fun hc => by
    have h1 : 21 ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hc 2
    exact Nat.mul_le_mul hc (by omega)
  constructor <;> intro h <;> by_cases hc : 21 ≤ t
  · have := hbound hc
    omega
  · push Not at hc
    interval_cases t <;> omega
  · have := hbound hc
    omega
  · push Not at hc
    interval_cases t <;> omega

theorem false_of_A6_U33_aux_card_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem false_of_A6_U33_aux_chev {S : Type} [Group S]
    (hbig : Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree S)
    (hcen : Subgroup.center S = ⊥) :
    IsChevTwo (S ⧸ Subgroup.center S) ∧ ¬ IsLTwoTwoPow (S ⧸ Subgroup.center S) := by
  have eQ : (S ⧸ Subgroup.center S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hcard : Nat.card S = 360 ∨ Nat.card S = 6048 := by
    rcases hbig with ⟨⟨e⟩⟩ | h
    · left
      rw [Nat.card_congr e.toEquiv]
      exact card_alternatingGroup_six
    · right
      exact (small1522_simple_center_aux5 h).2
  have hcardQ : Nat.card (S ⧸ Subgroup.center S) = 360 ∨ Nat.card (S ⧸ Subgroup.center S) = 6048 := by
    rwa [Nat.card_congr eQ.toEquiv]
  refine ⟨?_, ?_⟩
  · rcases hbig with ⟨⟨e⟩⟩ | ⟨d, hq, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ⟨eQ.trans e⟩⟩)
    · exact Or.inr (Or.inr ⟨d, Or.inr hq, ⟨eQ.trans e⟩⟩)
  · rintro (⟨⟨i, hv⟩, Q, hQp, hd, ⟨e⟩⟩ | ⟨⟨e⟩⟩)
    · have hd' : i = .A 1 Q := hd
      subst hd'
      have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      rw [hQp] at hmod
      have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hmod
      have h2 := false_of_A6_U33_aux_arith (2 ^ Q.exponent)
      rcases hcardQ with h | h
      · exact h2.1 (hc ▸ h)
      · exact h2.2 (hc ▸ h)
    · rw [Nat.card_congr e.toEquiv, false_of_A6_U33_aux_card_five] at hcardQ
      omega

theorem false_of_A6_U33_aux_no_ten (σ : Equiv.Perm (Fin 6)) : orderOf σ ≠ 10 := by
  intro h
  have hlcm := Equiv.Perm.lcm_cycleType σ
  have hsum : σ.cycleType.sum ≤ 6 := by simpa using Equiv.Perm.sum_cycleType_le σ
  have hmem : ∀ n ∈ σ.cycleType, n = 2 ∨ n = 5 := by
    intro n hn
    have h1 : n ∣ 10 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 : n ≤ 6 := (Multiset.le_sum_of_mem hn).trans hsum
    interval_cases n <;> omega
  have h5 : 5 ∈ σ.cycleType := by
    by_contra h5
    have : σ.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn h5
    rw [hlcm, h] at this
    omega
  have h2 : 2 ∈ σ.cycleType := by
    by_contra h2
    have : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn h2
      · exact dvd_rfl
    rw [hlcm, h] at this
    omega
  have h6 := Multiset.sum_erase h5
  have h7 : 2 ≤ (σ.cycleType.erase 5).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_erase_of_ne (by norm_num) |>.2 h2)
  omega

@[expose] def U33NoOrderFourteen : Prop :=
  ∀ (S : Type) [Group S], IsUThreeThree S → ∀ g : S, orderOf g ≠ 14

theorem false_of_A6_U33_aux_three (hU33 : U33NoOrderFourteen) {Y : Type} [Group Y] [Finite Y]
    {Ls S₀ P : Subgroup Y}
    (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls)
    (hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf S₀ Ls) (hP : IsMinOverBorel Ls S₀ P) :
    ∃ y ∈ pElementSubgroup 2 P, orderOf y = 3 := by
  rcases hbig with ⟨⟨e⟩⟩ | h
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine false_of_A6_U33_aux_three_of_order (a := 3) (b := 2) (r := 5) (by norm_num) ?_
      (by decide) ?_ hS₀ hP
    · rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
      norm_num
    · intro g hg hg10
      refine false_of_A6_U33_aux_no_ten ((e ⟨g, hg⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ?_
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe ⟨g, hg⟩]
      exact hg10
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    refine false_of_A6_U33_aux_three_of_order (a := 5) (b := 3) (r := 7) (by norm_num) ?_
      (by decide) ?_ hS₀ hP
    · rw [(small1522_simple_center_aux5 h).2]
      norm_num
    · intro g hg hg14
      refine hU33 ↥Ls h ⟨g, hg⟩ ?_
      rw [← Subgroup.orderOf_coe ⟨g, hg⟩]
      exact hg14

theorem u33NoOrderFourteen_holds : U33NoOrderFourteen := by
  intro S _ hS g hg
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (CFSG.AGLEmbeddingD2.McLaughlin.lieModel_of_isUThreeThree hS)
  set ψ : S →* Equiv.Perm (Fin 28) :=
    CFSG.GH74.KGroups.U33.QP.originalSubgroup.subtype.comp e.toMonoidHom with hψdef
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hψmem : ∀ x, ψ x ∈ CFSG.LieType.ChevTwo.OppCl.U33Fin.elems () := fun x =>
    (CFSG.GH74.KGroups.mem_elemsT CFSG.GH74.KGroups.U33.QP CFSG.GH74.KGroups.U33.QP_ok _).2
      (e x).2
  have hg14 : g ^ 14 = 1 := hg ▸ pow_orderOf_eq_one g
  have hx7 : (g ^ 2) ^ 7 = 1 := by rw [← pow_mul]; exact hg14
  have hs2 : g ^ 7 * g ^ 7 = 1 := by rw [← pow_add]; exact hg14
  have hx1 : g ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hg] at this
    omega
  have hs1 : g ^ 7 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hg] at this
    omega
  have hcomm : g ^ 2 * g ^ 7 = g ^ 7 * g ^ 2 := by rw [← pow_add, ← pow_add]
  have hsI : ψ (g ^ 7) ∈ CFSG.LieType.ChevTwo.OppCl.U33Fin.invsOf
      (CFSG.LieType.ChevTwo.OppCl.U33Fin.elems ()) :=
    CFSG.LieType.ChevTwo.OppCl.U33Fin.mem_invsOf.2 ⟨hψmem _, by rw [← map_mul, hs2, map_one],
      fun h => hs1 (hψinj (by rw [h, map_one]))⟩
  exact CFSG.LieType.ChevTwo.OppCl.U33Fin.F1_prop (ψ (g ^ 2)) (hψmem _)
    (by rw [← map_pow, hx7, map_one]) (fun h => hx1 (hψinj (by rw [h, map_one]))) (ψ (g ^ 7)) hsI
    (by rw [← map_mul, ← map_mul, hcomm])

theorem false_of_A6_U33_of_u33_gen (hU33 : U33NoOrderFourteen) (k542 : K542) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h23 : Row1523 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls)
    (hU : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 → A.map M.subtype ∈ uniqueSet M) : False := by
  haveI := hLn
  have hTM : T ≤ M := ctx.sylow.le
  have hl := hR.liftCtxGen ctx.gn ctx.good hLs hL
  have hsmall : Small1522 ↥Ls := by
    rcases hbig with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨hsimple, hcen⟩ := small1522_simple_center hsmall
  obtain ⟨p, hp⟩ := ctx.p_mem
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hrk : 1 < CFSG.Open.pRank p (cMBar L) := (h20 p hp Ls L hLs hL).2.1
  have hrk2 : 2 ≤ CFSG.Open.pRank p (cMHat L) := by
    refine two_le_pRank_of_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hpP hp2 (cMHat L) ?_
    have h1 : (cMHat L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (cMBar L)
    rw [h1]
    exact hrk
  obtain ⟨P₀, hP₀le, hP₀a, hP₀c⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt (cMHat L)
  have hP₀rk : 2 ≤ CFSG.Open.pRank p P₀ :=
    hrk2.trans (CFSG.SectionRank.le_pRank hpP.one_lt le_rfl hP₀a hP₀c)
  obtain ⟨hPU0, z, hz, hz1⟩ := false_of_A6_U33_aux_xlevel_gen k542 hl hbig hP₀le
  have hexp := (gnV_comm_exp_two ctx.gn).2
  haveI hVn : (gnV (T.subgroupOf M)).Normal := by unfold gnV; infer_instance
  have hZmap : (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M)).map M.subtype =
      CFSG.Quasithin.omegaOneCenterOf T := map_omegaOneCenterOf_subgroupOf hTM
  obtain ⟨Q, -, hw⟩ := ctx.witness p hp
  set Z₁ : Subgroup ↥M := ⁅gnV (T.subgroupOf M), Ls.comap (toStar (T.subgroupOf M))⁆ ⊓
    CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) with hZ₁
  have hZ1V : Z₁ ≤ gnV (T.subgroupOf M) := inf_le_left.trans (Subgroup.commutator_le_left _ _)
  have hPcent : P₀ ≤ Subgroup.centralizer (Z₁ : Set ↥M) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hPU0).trans (Subgroup.centralizer_le inf_le_left)
  have hZ1G_ne : Z₁.map M.subtype ≠ ⊥ := by
    intro h
    apply hz1
    have : (z : G) ∈ Z₁.map M.subtype := Subgroup.mem_map_of_mem _ hz
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hZ1G_p : IsPGroup 2 ↥(Z₁.map M.subtype) := by
    intro g
    obtain ⟨w, hw', hwg⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : ((w : ↥M) : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hexp w (hZ1V hw')]
      rfl
    simpa [← hwg] using h2
  have hP₀G : P₀.map M.subtype ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hP₀Gn : P₀.map M.subtype ≤ Subgroup.normalizer ((Z₁.map M.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hPcent hy) u hu)
  have hP₀Grk : 2 ≤ CFSG.Open.pRank p (P₀.map M.subtype) :=
    hP₀rk.trans (CFSG.SectionRank.pRank_le_map hpP.one_lt M.subtype M.subtype_injective P₀)
  have hZ1M : Subgroup.normalizer ((Z₁.map M.subtype : Subgroup G) : Set G) ≤ M :=
    hw.le_of_le_of_two_le_pRank hpP hP₀G hP₀Grk ⟨_, hZ1G_ne, hZ1G_p, rfl⟩ hP₀Gn
  obtain ⟨hChev, hnL2⟩ := false_of_A6_U33_aux_chev hbig hcen
  obtain ⟨S₀, P', hS₀, hP', hcentP⟩ := h23 Ls L hLs hL hChev hnL2 hbig
  have hZsub : ((CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Subgroup ↥M) : Set ↥M) ⊆
      ((gnV (T.subgroupOf M) ⊓ Subgroup.centralizer
        (((T.subgroupOf M ⊓ Subgroup.normalizer (L : Set ↥M) : Subgroup ↥M)) : Set ↥M) :
          Subgroup ↥M) : Set ↥M) := by
    intro x hx
    refine ⟨Subgroup.subset_normalClosure hx, ?_⟩
    have hxc := CFSG.Quasithin.A4.centerOf_le_centralizer _
      (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf _ hx)
    exact Subgroup.centralizer_le (inf_le_left : T.subgroupOf M ⊓ Subgroup.normalizer (L : Set ↥M) ≤
      T.subgroupOf M) hxc
  have hZcent : pElementSubgroup 2 (P'.comap (toStar (T.subgroupOf M))) ≤
      Subgroup.centralizer
        ((CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Subgroup ↥M) : Set ↥M) :=
    hcentP.trans (Subgroup.centralizer_le hZsub)
  have hZC : gnC (T.subgroupOf M) ≤ Subgroup.centralizer
      ((CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Subgroup ↥M) : Set ↥M) :=
    Subgroup.centralizer_le fun x hx => Subgroup.subset_normalClosure hx
  obtain ⟨y, hy, hy3⟩ := false_of_A6_U33_aux_three hU33 hbig hS₀ hP'
  obtain ⟨c, hcL, hcZ, hc3⟩ := false_of_A6_U33_aux_c ctx.gn hLs.1 hL hP'.1 hZcent hZC hy hy3
  have hA := hU (Subgroup.zpowers c) (Subgroup.zpowers_le.2 hcL)
    (by rw [Nat.card_zpowers, hc3])
  apply ctx.notLe
  intro g hg
  have hgZ : g ∈ Subgroup.normalizer ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf T hg
  rw [← hZmap] at hgZ
  have hw' : g⁻¹ * (c : G) * g ∈ M := by
    apply hZ1M
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhZ : h ∈ (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M)).map M.subtype :=
      Subgroup.map_mono inf_le_right hh
    obtain ⟨u, hu, hug⟩ := (Subgroup.mem_normalizer_iff.1 hgZ h).1 hhZ
    have hcu : (u : G) * (c : G) = (c : G) * (u : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hcZ u hu)
    have hu' : (u : G) = g * h * g⁻¹ := hug
    have hh' : h = g⁻¹ * (u : G) * g := by rw [hu']; group
    calc h * (g⁻¹ * (c : G) * g)
        = (g⁻¹ * (u : G) * g) * (g⁻¹ * (c : G) * g) := by rw [← hh']
      _ = g⁻¹ * ((u : G) * (c : G)) * g := by group
      _ = g⁻¹ * ((c : G) * (u : G)) * g := by rw [hcu]
      _ = (g⁻¹ * (c : G) * g) * (g⁻¹ * (u : G) * g) := by group
      _ = g⁻¹ * (c : G) * g * h := by rw [← hh']
  have hcg : (c : G) ∈ M.map (MulAut.conj g).toMonoidHom :=
    (gamma_le_of_le_lift_aux_mem_map_conj M g (c : G)).2 hw'
  have hAle : (Subgroup.zpowers c).map M.subtype ≤ M.map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨a, ⟨n, rfl⟩, rfl⟩
    simpa using (M.map (MulAut.conj g).toMonoidHom).zpow_mem hcg n
  have hMg : M.map (MulAut.conj g).toMonoidHom = M := hA.2 g hAle
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M ctx.maxLocal]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMg

theorem false_of_A6_U33_gen (k542 : K542) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h23 : Row1523 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls)
    (hU : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 → A.map M.subtype ∈ uniqueSet M) : False :=
  false_of_A6_U33_of_u33_gen u33NoOrderFourteen_holds k542 ctx hR h11 h20 h23 hLs hL hLn hbig hU

end CFSG.LocalAnalysis.RankThreeUC.S15
