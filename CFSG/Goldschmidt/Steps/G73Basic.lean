module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Completion
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Walter.W67.W1Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.Assembly.Subnormal
public import CFSG.Goldschmidt.StatementsG
import CFSG.Walter.Bender1970.S4.ComponentTools

public section

namespace CFSG.Goldschmidt

namespace G73

variable {G : Type} [Group G] [Finite G]

section Setting

variable {S : Sylow 2 G} {A : Subgroup G}

theorem centralizer_ne_top (hG : GoldSetting G S A) {s : G} (hs : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≠ ⊤ := by
  have := hG.isSimpleGroup
  intro h
  apply hs
  have hz : s ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({s} : Set G) := h ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
  · rw [h0] at hz
    exact Subgroup.mem_bot.mp hz
  · obtain ⟨a, b, hab⟩ := hG.nonabelian
    exact absurd (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a) hab

theorem benderM_nonempty (hG : GoldSetting G S A) {s : G} (hs : s ≠ 1) :
    (CFSG.Walter.benderM s).Nonempty := by
  classical
  set C := Subgroup.centralizer ({s} : Set G)
  set 𝒦 : Set (Subgroup G) := {K | IsCoatom K ∧ C ≤ K}
  have hne : 𝒦.Nonempty := by
    rcases eq_top_or_exists_le_coatom C with h | ⟨K, hK, hCK⟩
    · exact absurd h (centralizer_ne_top hG hs)
    · exact ⟨K, hK, hCK⟩
  by_cases hfp : ∃ K : Subgroup G, IsCoatom K ∧ C ≤ K ∧ CFSG.Walter.HasFixedPointFreeCore s K
  · obtain ⟨K, hK, hCK, hKfp⟩ := hfp
    exact ⟨K, hK, hCK, Or.inl hKfp⟩
  · push Not at hfp
    obtain ⟨K, ⟨hK, hCK⟩, hmax⟩ := Set.exists_max_image 𝒦
      (fun K => Nat.card (GorensteinWalter.componentLayerOf K)) (Set.toFinite 𝒦) hne
    exact ⟨K, hK, hCK, Or.inr ⟨fun K' hK' hCK' => hfp K' hK' hCK',
      fun K' hK' hCK' => hmax K' ⟨hK', hCK'⟩⟩⟩

theorem ne_bot_of_mem_benderM {s : G} (hs : s ≠ 1) {H : Subgroup G}
    (hH : H ∈ CFSG.Walter.benderM s) : H ≠ ⊥ := by
  intro h
  have := CFSG.Walter.mem_of_mem_benderM hH
  rw [h] at this
  exact hs (Subgroup.mem_bot.mp this)

theorem normalizer_eq (hG : GoldSetting G S A) {H N : Subgroup G} (hH : IsCoatom H)
    (hNH : N ≤ H) (hN : N ≠ ⊥) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = H :=
  GorensteinWalter.normalizer_eq_of_nontrivial_normal_in_coatom hG.isSimpleGroup hH hNH hN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN)

theorem le_of_mem_benderM (hG : GoldSetting G S A) {a : G} (ha : a ∈ A) {H : Subgroup G}
    (hH : H ∈ CFSG.Walter.benderM a) : A ≤ H := by
  have hab := hG.elem.1
  refine fun b hb => CFSG.Walter.centralizer_le_of_mem_benderM hH ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩))

theorem isSStarIn (hG : GoldSetting G S A) {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) :
    IsSStarIn H A := by
  obtain ⟨g, hle, hS⟩ := hG.sstar H hH
  have hAg : A ≤ conjSub g A := (le_inf le_rfl hAH).trans hle
  have heq : A = conjSub g A := Subgroup.eq_of_le_of_card_ge hAg (card_conjSub g A).le
  rwa [← heq, inf_of_le_left hAH] at hS

theorem isSStarIn_of_mem_benderM (hG : GoldSetting G S A) {a : G} (ha : a ∈ A)
    {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) : IsSStarIn H A :=
  isSStarIn hG (CFSG.Walter.ne_top_of_mem_benderM hH) (le_of_mem_benderM hG ha hH)

theorem isPGroup (hG : GoldSetting G S A) : IsPGroup 2 A :=
  S.isPGroup'.to_le hG.le

end Setting

section Components

theorem isSolvable_oddCoreOf (H : Subgroup G) : Group.IsSolvable (oddCoreOf H) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Completion.odd_card_oddCoreOf H)

omit [Finite G] in
theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H := Subgroup.map_subtype_le _

theorem le_centralizer_oddCoreOf {H K : Subgroup G} (hK : GorensteinWalter.IsComponentOf K H) :
    K ≤ Subgroup.centralizer (oddCoreOf H : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hK (isSolvable_oddCoreOf H)
      (oddCoreOf_le H) (Completion.le_normalizer_oddCoreOf H))

omit [Finite G] in
theorem normalClosureIn_le (X B : Subgroup G) : normalClosureIn X B ≤ X :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_normalClosureIn (X B : Subgroup G) :
    X ≤ Subgroup.normalizer (normalClosureIn X B : Set G) := by
  have heq : (normalClosureIn X B).subgroupOf X =
      Subgroup.normalClosure ((B.subgroupOf X : Subgroup X) : Set X) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hn : ((normalClosureIn X B).subgroupOf X).Normal := by
    rw [heq]
    exact Subgroup.normalClosure_normal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le X B)).mp hn

omit [Finite G] in
theorem inf_le_normalClosureIn (X B : Subgroup G) : B ⊓ X ≤ normalClosureIn X B :=
  fun b hb => ⟨⟨b, hb.2⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hb.1), rfl⟩

omit [Finite G] in
theorem normalClosureIn_le_of {X B N : Subgroup G} (hBN : B ⊓ X ≤ N)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) : normalClosureIn X B ≤ N := by
  have hn : (N.subgroupOf X).Normal := ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXN x.2) n).mp hn⟩
  have hle : Subgroup.normalClosure ((B.subgroupOf X : Subgroup X) : Set X) ≤ N.subgroupOf X :=
    Subgroup.normalClosure_le_normal fun x hx =>
      Subgroup.mem_subgroupOf.2 (hBN ⟨Subgroup.mem_subgroupOf.1 hx, x.2⟩)
  have h := Subgroup.map_mono (f := X.subtype) hle
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.trans inf_le_left

omit [Finite G] in
theorem normalClosureIn_mono {X Y B : Subgroup G} (hXY : X ≤ Y) :
    normalClosureIn X B ≤ normalClosureIn Y B :=
  normalClosureIn_le_of (fun _ hb => inf_le_normalClosureIn Y B ⟨hb.1, hXY hb.2⟩)
    (hXY.trans (le_normalizer_normalClosureIn Y B))

omit [Finite G] in
theorem normalClosureIn_le_center {X B : Subgroup G}
    (h : B ⊓ X ≤ Subgroup.centralizer (X : Set G)) :
    normalClosureIn X B ≤ X ⊓ Subgroup.centralizer (X : Set G) := by
  refine normalClosureIn_le_of (le_inf inf_le_right h) fun x hx => ?_
  have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy z hz
      have := hy (x⁻¹ * z * x) (X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx)
      calc z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [this]
        _ = x * y * x⁻¹ * z := by group
    · intro hy z hz
      have := hy (x * z * x⁻¹) (X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx))
      have h1 : x * z * x⁻¹ * (x * y * x⁻¹) = x * y * x⁻¹ * (x * z * x⁻¹) := this
      calc z * y = x⁻¹ * (x * z * x⁻¹ * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹ * (x * z * x⁻¹)) * x := by rw [h1]
        _ = y * z := by group
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hxC⟩

omit [Finite G] in
theorem isComponentOf_of_normalClosureIn {H B K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H B)) :
    GorensteinWalter.IsComponentOf K H :=
  CFSG.Walter.isComponentOf_of_isSubnormal (normalClosureIn_le H B)
    (CFSG.Walter.isSubnormal_subgroupOf_of_le_normalizer (normalClosureIn_le H B)
      (le_normalizer_normalClosureIn H B)) hK

theorem componentLayerOf_normalClosureIn_le (H B : Subgroup G) :
    GorensteinWalter.componentLayerOf (normalClosureIn H B) ≤
      Subgroup.centralizer (oddCoreOf H : Set G) :=
  sSup_le fun _ hJ => le_centralizer_oddCoreOf (isComponentOf_of_normalClosureIn hJ)

omit [Finite G] in
theorem componentLayerOf_componentLayerOf (Y : Subgroup G) :
    GorensteinWalter.componentLayerOf (GorensteinWalter.componentLayerOf Y) =
      GorensteinWalter.componentLayerOf Y := by
  apply le_antisymm
  · exact sSup_le fun K hK => hK.1
  · refine sSup_le fun K hK => le_sSup ?_
    exact CFSG.Walter.isComponentOf_of_le hK (CFSG.Walter.le_componentLayerOf_of_isComponentOf hK)
      (GorensteinWalter.componentLayerOf_isNormalIn Y).1

omit [Finite G] in
theorem componentLayerOf_eq_sup (Y : Subgroup G) :
    GorensteinWalter.componentLayerOf Y =
      GorensteinWalter.componentLayerOf (GorensteinWalter.componentLayerOf Y) ⊔
        oddCoreOf (CFSG.fittingSubgroupOf (GorensteinWalter.componentLayerOf Y)) := by
  rw [componentLayerOf_componentLayerOf]
  exact (sup_eq_left.mpr ((oddCoreOf_le _).trans (CFSG.fittingSubgroupOf_le _))).symm

omit [Finite G] in
theorem le_map_derivedSeries {Q P : Subgroup G} (hPQ : P ≤ Q) (hP : ⁅P, P⁆ = P) (n : ℕ) :
    P ≤ (derivedSeries Q n).map Q.subtype := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hPQ
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator]
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ _ := Subgroup.commutator_mono ih ih

omit [Finite G] in
theorem commutator_self_of_isComponentOf {K X : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K X) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.mp (CFSG.Walter.isPerfect_of_isComponentOf hK)

end Components

section Bar

omit [Finite G] in
private theorem open_isSubnormal_top {Y : Type*} [Group Y] {M : Subgroup Y}
    (h : M.IsSubnormal) : CFSG.Open.IsSubnormal M ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

omit [Finite G] in
private theorem open_isSubnormal_map {Y Z : Type*} [Group Y] [Group Z] (f : Y →* Z)
    {M N : Subgroup Y} (h : CFSG.Open.IsSubnormal M N) :
    CFSG.Open.IsSubnormal (M.map f) (N.map f) :=
  h.map f

omit [Finite G] in
private theorem open_isSubnormal_comap {Y Z : Type*} [Group Y] [Group Z] (f : Z →* Y)
    {M N : Subgroup Y} (h : CFSG.Open.IsSubnormal M N) :
    CFSG.Open.IsSubnormal (M.comap f) (N.comap f) :=
  h.comap f

theorem isComponentOf_barOf {H B J : Subgroup G}
    (hJ : GorensteinWalter.IsComponentOf J (normalClosureIn H B)) :
    CFSG.Open.IsComponentOf (barOf H J) (barOf H (normalClosureIn H B)) ∧
      preOf H (barOf H J) = J ⊔ oddCoreOf H := by
  have hJQ : J ≤ normalClosureIn H B := hJ.1
  have hJH' := isComponentOf_of_normalClosureIn hJ
  have hJH : J ≤ H := hJH'.1
  refine ⟨⟨Subgroup.map_mono fun x hx => hJQ hx, ?_, ?_⟩, ?_⟩
  · have h1 : CFSG.Open.IsSubnormal J (normalClosureIn H B) := by
      have := open_isSubnormal_map (normalClosureIn H B).subtype (open_isSubnormal_top hJ.2.1)
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hJQ] at this
    exact open_isSubnormal_map _ (open_isSubnormal_comap H.subtype h1)
  · have hq : CFSG.IsQuasisimple (J.subgroupOf H) :=
      (CFSG.Walter.isComponent_subgroupOf_of_isComponentOf hJH').1
    have hnot : ¬ J.subgroupOf H ≤ (QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore H)).ker := by
      rw [QuotientGroup.ker_mk']
      intro hle
      have hJO : J ≤ oddCoreOf H := by
        have := Subgroup.map_mono (f := H.subtype) hle
        rwa [Subgroup.map_subgroupOf_eq_of_le hJH] at this
      exact CFSG.Walter.not_le_centralizer_self_of_isComponentOf hJH'
        ((le_centralizer_oddCoreOf hJH').trans (Subgroup.centralizer_le hJO))
    have h2 := CFSG.LocalCores.isQuasisimple_map hq
      (QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore H)) hnot
    exact ⟨Group.isPerfect_def.mp h2.1, h2.2.1⟩
  · rw [preOf, barOf, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hJH]
    rfl

omit [Finite G] in
theorem mem_of_mem_sup_of_sq_eq_one {J O : Subgroup G}
    (hJO : J ≤ Subgroup.centralizer (O : Set G)) (hO : Odd (Nat.card O)) {x : G}
    (hx : x ∈ J ⊔ O) (hx2 : x ^ 2 = 1) : x ∈ J := by
  have hc : ∀ j ∈ J, ∀ o ∈ O, j * o = o * j := fun j hj o ho =>
    (Subgroup.mem_centralizer_iff.mp (hJO hj) o ho).symm
  obtain ⟨-, hset⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute J O hc
  have hx' : x ∈ ((J ⊔ O : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨j, hj, o, ho, hxe⟩ := hx'
  have hxe' : x = j * o := hxe.symm
  subst hxe'
  obtain ⟨k, hk⟩ : Odd (orderOf o) := Odd.of_dvd_nat hO (O.orderOf_dvd_natCard ho)
  have hcomm : Commute j o := hc j hj o ho
  have h1 : (j * o) ^ orderOf o = j ^ orderOf o := by
    rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  have h2 : (j * o) ^ orderOf o = j * o := by
    rw [hk, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [← h2, h1]
  exact J.pow_mem hj _

theorem eq_of_isComponentOf_le_sup {H J J' : Subgroup G}
    (hJ : GorensteinWalter.IsComponentOf J H) (hJ' : GorensteinWalter.IsComponentOf J' H)
    (hle : J' ≤ J ⊔ oddCoreOf H) : J' = J := by
  rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hJ' hJ with h | h
  · exact h
  · exfalso
    have h1 : J ≤ Subgroup.centralizer (J' : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    have h2 : oddCoreOf H ≤ Subgroup.centralizer (J' : Set G) :=
      Subgroup.le_centralizer_iff.mp (le_centralizer_oddCoreOf hJ')
    exact CFSG.Walter.not_le_centralizer_self_of_isComponentOf hJ' (hle.trans (sup_le h1 h2))

theorem le_normalClosureIn_self (h31 : S_G31) {H A J : Subgroup G} (hS : IsSStarIn H A)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (hJ : GorensteinWalter.IsComponentOf J (normalClosureIn H A)) :
    J ≤ normalClosureIn J A := by
  obtain ⟨hbar, hpre⟩ := isComponentOf_barOf hJ
  obtain ⟨-, h2, -⟩ := (h31 G H A hS).1 _ hbar
  rw [hpre] at h2
  have hJH' := isComponentOf_of_normalClosureIn hJ
  have hJO : J ≤ Subgroup.centralizer (oddCoreOf H : Set G) := le_centralizer_oddCoreOf hJH'
  have hOJ : oddCoreOf H ≤ Subgroup.centralizer (J : Set G) := Subgroup.le_centralizer_iff.mp hJO
  have hJP : J ≤ J ⊔ oddCoreOf H := le_sup_left
  have hPJ : J ⊔ oddCoreOf H ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer (hOJ.trans (Subgroup.centralizer_le_normalizer _))
  have hJc : GorensteinWalter.IsComponentOf J (J ⊔ oddCoreOf H) :=
    ⟨hJP, CFSG.Walter.isSubnormal_subgroupOf_of_le_normalizer hJP hPJ, hJ.2.2⟩
  have hN₂ : J ≤ normalClosureIn (J ⊔ oddCoreOf H) (A ⊓ (J ⊔ oddCoreOf H)) := by
    rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot hJc (normalClosureIn_le _ _)
      (le_normalizer_normalClosureIn _ _) with h | h
    · exact h
    · exfalso
      have h3 := Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      have h4 := Subgroup.le_centralizer_iff.mp (le_centralizer_oddCoreOf hJc)
      exact CFSG.Walter.not_le_centralizer_self_of_isComponentOf hJc
        (hJP.trans (h2.le.trans (sup_le h3 h4)))
  refine hN₂.trans (normalClosureIn_le_of ?_ ?_)
  · intro x hx
    exact inf_le_normalClosureIn J A ⟨hx.1.1, mem_of_mem_sup_of_sq_eq_one hJO
      (Completion.odd_card_oddCoreOf H) hx.2 (hA.2 x hx.1.1)⟩
  · exact sup_le (le_normalizer_normalClosureIn J A) (hOJ.trans
      ((Subgroup.centralizer_le (normalClosureIn_le J A)).trans
        (Subgroup.centralizer_le_normalizer _)))

theorem eq_inf_sup_inf_centralizer (h31 : S_G31) {H A J : Subgroup G} (hS : IsSStarIn H A)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (hJ : GorensteinWalter.IsComponentOf J (normalClosureIn H A)) :
    A = A ⊓ J ⊔ A ⊓ Subgroup.centralizer (J : Set G) := by
  obtain ⟨hbar, hpre⟩ := isComponentOf_barOf hJ
  obtain ⟨-, -, h4⟩ := (h31 G H A hS).1 _ hbar
  rw [hpre] at h4
  have hJH' := isComponentOf_of_normalClosureIn hJ
  have hJH : J ≤ H := hJH'.1
  have hJO : J ≤ Subgroup.centralizer (oddCoreOf H : Set G) := le_centralizer_oddCoreOf hJH'
  have hOJ : oddCoreOf H ≤ Subgroup.centralizer (J : Set G) := Subgroup.le_centralizer_iff.mp hJO
  refine le_antisymm (h4.le.trans (sup_le_sup (fun x hx => ⟨hx.1, ?_⟩) fun x hx => ⟨hx.1, ?_⟩))
    (sup_le inf_le_left inf_le_left)
  · exact mem_of_mem_sup_of_sq_eq_one hJO (Completion.odd_card_oddCoreOf H) hx.2 (hA.2 x hx.1)
  · obtain ⟨h, hh, rfl⟩ := hx.2
    have hcomm : ∀ j ∈ J, (h : G) * j * (h : G)⁻¹ * j⁻¹ ∈ oddCoreOf H := by
      intro j hj
      have hjL : (QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore H) ⟨j, hJH hj⟩ :
          H ⧸ CFSG.Open.goldschmidtOddCore H) ∈ barOf H J :=
        ⟨⟨j, hJH hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hh) _ hjL
      have h3 : QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore H)
          (h * ⟨j, hJH hj⟩ * h⁻¹ * (⟨j, hJH hj⟩ : H)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact ⟨_, h3, by simp⟩
    have hJh : J.map (MulAut.conj (h : G)).toMonoidHom = J := by
      refine eq_of_isComponentOf_le_sup hJH'
        (CFSG.Walter.isComponentOf_map_conj hJH' (Subgroup.le_normalizer h.2)) ?_
      rintro _ ⟨j, hj, rfl⟩
      have he : (MulAut.conj (h : G)).toMonoidHom j =
          ((h : G) * j * (h : G)⁻¹ * j⁻¹) * j := by
        simp [MulAut.conj_apply]
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm j hj))
        (Subgroup.mem_sup_left hj)
    have hhN : (h : G) ∈ Subgroup.normalizer (J : Set G) :=
      CFSG.Walter.map_conj_eq_iff_mem_normalizer.mp hJh
    refine CFSG.Walter.mem_centralizer_of_commutator_mem_center hJ.2.2.2.1 fun j hj => ?_
    have hjJ : (h : G) * j * (h : G)⁻¹ * j⁻¹ ∈ J :=
      J.mul_mem ((Subgroup.mem_normalizer_iff.mp hhN j).mp hj) (J.inv_mem hj)
    refine ⟨⟨_, hjJ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hOJ (hcomm j hj)) y y.2)

theorem not_inf_le_centralizer (h31 : S_G31) {H A K : Subgroup G} (hS : IsSStarIn H A)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) :
    ¬ A ⊓ K ≤ Subgroup.centralizer (K : Set G) := fun h =>
  CFSG.Walter.not_le_centralizer_self_of_isComponentOf hK
    ((le_normalClosureIn_self h31 hS hA hK).trans
      ((normalClosureIn_le_center h).trans inf_le_right))

end Bar

section Local

variable {S : Sylow 2 G} {A : Subgroup G}

theorem le_centralizer_oddCoreOf_of_le (h71 : S_G71) (hG : GoldSetting G S A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ CFSG.Walter.benderM a) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPQ : P ≤ normalClosureIn H A) :
    P ≤ GorensteinWalter.componentLayerOf (normalClosureIn H A) ∧
      P ≤ Subgroup.centralizer (oddCoreOf H : Set G) := by
  obtain ⟨n, hn⟩ := h71 G S A hG h8 a ha ha1 H hH
  have h1 := (le_map_derivedSeries hPQ hP n).trans hn
  exact ⟨h1, h1.trans (componentLayerOf_normalClosureIn_le H A)⟩

theorem le_normalClosureIn_of_not_le (hG : GoldSetting G S A) {H J : Subgroup G} (hAH : A ≤ H)
    (hJ : GorensteinWalter.IsComponentOf J H) {g : G}
    (hg : ¬ conjSub g A ⊓ J ≤ Subgroup.centralizer (J : Set G)) : J ≤ normalClosureIn H A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot hJ (normalClosureIn_le H A)
    (le_normalizer_normalClosureIn H A) with h | h
  · exact h
  · exfalso
    have hAQ : A ≤ normalClosureIn H A := (le_inf le_rfl hAH).trans (inf_le_normalClosureIn H A)
    have hJA : J ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le hAQ)
    apply hg
    intro b hb
    have hb2 : IsPGroup 2 (Subgroup.zpowers b) :=
      ((isPGroup hG).map (MulAut.conj g⁻¹).toMonoidHom).to_le (Subgroup.zpowers_le.mpr hb.1)
    have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ (hJA hb.2))
    have hR : IsPGroup 2 (A ⊔ Subgroup.zpowers b : Subgroup G) :=
      (isPGroup hG).to_sup_of_normal_left' hb2 hbN
    obtain ⟨Q, hRQ, hQ⟩ := stronglyClosed_of_le_pGroup S hG.closed hR le_sup_left
    have hbQ : b ∈ (Q : Subgroup G) := hRQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    have hbA : b ∈ A := by
      have h1 := hQ (g * b * g⁻¹) (mem_conjSub.mp hb.1) g (by simpa [mul_assoc] using hbQ)
      simpa [mul_assoc] using h1
    exact Subgroup.le_centralizer_iff.mp hJA hbA

end Local

end G73

end CFSG.Goldschmidt
