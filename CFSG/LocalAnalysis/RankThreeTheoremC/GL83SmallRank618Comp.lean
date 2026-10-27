module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
import CFSG.Adapters.GeneralizedFitting
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {B Z Y₀ : Subgroup Y}

private theorem comp618_comm (d : Data618 B Z Y₀) {x y : Y} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x :=
  congrArg Subtype.val (d.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem comp618_isPGroup_B (d : Data618 B Z Y₀) : IsPGroup 3 B :=
  IsPGroup.of_card (n := 2) (by rw [d.card_B]; norm_num)

private theorem comp618_pPrimeCore_eq_bot (d : Data618 B Z Y₀) : CFSG.pPrimeCore 3 Y = ⊥ :=
  CFSG.pPrimeCore_eq_bot_iff.mpr d.core

theorem exists_isComponentOf_top (d : Data618 B Z Y₀) :
    ∃ L : Subgroup Y, CFSG.Open.IsComponentOf L ⊤ := by
  by_contra hno
  push Not at hno
  have hE : genFittingLayer Y = ⊥ := sSup_eq_bot.mpr (fun L hL => absurd hL (hno L))
  have hF : genFittingFStar Y = CFSG.fittingSubgroup Y := by
    show genFittingFitting Y ⊔ genFittingLayer Y = _
    rw [hE, sup_bot_eq]
    rfl
  have hp : IsPGroup 3 (CFSG.fittingSubgroup Y) :=
    CFSG.isPGroup_of_nilpotent_normal _ CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent (comp618_pPrimeCore_eq_bot d)
  let P : Sylow 3 Y := (comp618_isPGroup_B d).toSylow d.sylow
  have hFB : CFSG.fittingSubgroup Y ≤ B := hp.le_sylow_of_normal P
  have hBC : B ≤ centralizer (CFSG.fittingSubgroup Y : Set Y) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact comp618_comm d (hFB hf) hb
  have hBF : B ≤ CFSG.fittingSubgroup Y := by
    have h := CFSG.Adapters.generalized_fitting_self_centralizing Y
    rw [hF] at h
    exact hBC.trans h
  have hBn : B.Normal := by
    rw [← le_antisymm hFB hBF]
    infer_instance
  exact d.proper (top_le_iff.mp
    ((normalizer_eq_top_iff.mpr hBn).symm.le.trans (d.fix_Z.trans d.cover)))

omit [Finite Y] in
private theorem comp618_conj_mem_map_of_characteristic {X : Subgroup Y} {D : Subgroup X}
    [hD : D.Characteristic] {g : Y} (hg : g ∈ normalizer (X : Set Y)) {x : Y}
    (hx : x ∈ D.map X.subtype) : g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem comp618_map_pPrimeCore_le {p : ℕ} [Fact p.Prime] {X : Subgroup Y}
    (hX : X.IsSubnormal) : (CFSG.pPrimeCore p X).map X.subtype ≤ CFSG.pPrimeCore p Y := by
  have key : ∀ {X W : Subgroup Y}, X ≤ W → W ≤ normalizer (X : Set Y) →
      (CFSG.pPrimeCore p X).map X.subtype ≤ (CFSG.pPrimeCore p W).map W.subtype := by
    intro X W hXW hWN
    have hLW : (CFSG.pPrimeCore p X).map X.subtype ≤ W :=
      (Subgroup.map_subtype_le _).trans hXW
    have hle : ((CFSG.pPrimeCore p X).map X.subtype).subgroupOf W ≤ CFSG.pPrimeCore p W := by
      apply le_sSup
      refine ⟨⟨fun l hl w => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using comp618_conj_mem_map_of_characteristic (hWN w.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLW).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore p X).map X.subtype
        = (((CFSG.pPrimeCore p X).map X.subtype).subgroupOf W).map W.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLW).symm
      _ ≤ (CFSG.pPrimeCore p W).map W.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => comp618_conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.pPrimeCore_coprime_card
  | step X W hXW _ hN ih =>
    exact (key hXW ((Subgroup.normal_subgroupOf_iff_le_normalizer hXW).mp hN)).trans ih

private theorem comp618_pPrimeCore_eq_bot_of_isSubnormal (d : Data618 B Z Y₀) {X : Subgroup Y}
    (hX : X.IsSubnormal) : CFSG.pPrimeCore 3 X = ⊥ := by
  have h := comp618_map_pPrimeCore_le (p := 3) hX
  rw [comp618_pPrimeCore_eq_bot d, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective] at h
  exact h

private theorem comp618_isSylowOf_inf (d : Data618 B Z Y₀) {X : Subgroup Y}
    (hX : X.IsSubnormal) : CFSG.ABGLocalTools.IsSylowOf 3 (B ⊓ X) X := by
  induction hX with
  | top =>
    rw [inf_top_eq, CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, comp618_isPGroup_B d, d.sylow⟩
  | step X W hXW _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hXW
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXW).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hXW] at h1

private theorem comp618_eq_one_of_mem_center {E : Type} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] (hperf : commutator E = ⊤) (S : Sylow p E) (hS : IsMulCommutative S)
    {z : E} (hz : z ∈ center E) (hzS : z ∈ (S : Subgroup E)) : z = 1 := by
  let : CommGroup S := IsMulCommutative.instCommGroup
  let tr : E →* S := MonoidHom.transfer (MonoidHom.id S)
  have htriv : tr z = 1 := by
    have hzc : z ∈ commutator E := by
      rw [hperf]
      trivial
    exact Abelianization.commutator_subset_ker tr hzc
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup E) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp ((center E).pow_mem hz k) g₀
    rw [mul_assoc, ← h]
    group
  have hpow : z ^ (S : Subgroup E).index = 1 := by
    have h := htriv
    rw [show tr z = _ from MonoidHom.transfer_eq_pow (MonoidHom.id S) z hkey] at h
    exact congrArg Subtype.val h
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨z, hzS⟩
  have h1 : orderOf z ∣ (S : Subgroup E).index := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf z ∣ p ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have hcop : Nat.Coprime (p ^ n) (S : Subgroup E).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr S.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

private theorem comp618_center_eq_bot (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : L.IsSubnormal) (hperf : commutator L = ⊤) : center L = ⊥ := by
  have hZp : IsPGroup 3 (center L) :=
    CFSG.isPGroup_of_nilpotent_normal (center L) inferInstance CommGroup.isNilpotent
      (comp618_pPrimeCore_eq_bot_of_isSubnormal d hL)
  obtain ⟨S, hS⟩ := (comp618_isSylowOf_inf d hL).exists_sylow_eq_subgroupOf
  have hSB : ∀ x : L, x ∈ (S : Subgroup L) → (x : Y) ∈ B := fun x hx =>
    (hS ▸ hx : x ∈ (B ⊓ L).subgroupOf L).1
  have hSc : IsMulCommutative (S : Subgroup L) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (comp618_comm d (x := ((a : L) : Y)) (y := ((b : L) : Y)) (hSB _ a.2) (hSB _ b.2)))⟩⟩
  rw [eq_bot_iff]
  intro z hz
  exact Subgroup.mem_bot.mpr
    (comp618_eq_one_of_mem_center hperf S hSc hz (hZp.le_sylow_of_normal S hz))

private theorem comp618_isKGroup_subgroup {X : Type} [Group X] (hX : CFSG.IsKGroup X)
    (K : Subgroup X) : CFSG.IsKGroup K :=
  hX.subgroup K

private theorem comp618_exists_ne_comm {G : Type} [Group G] [Nontrivial G]
    (hperf : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have : IsMulCommutative G := ⟨⟨h⟩⟩
  have h1 := Abelianization.commutator_subset_ker (MonoidHom.id G)
  rw [hperf, MonoidHom.ker_id, top_le_iff] at h1
  exact bot_ne_top h1

private theorem comp618_isSimpleGroup (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : IsSimpleGroup L := by
  have hsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1
  have hc : center L = ⊥ := comp618_center_eq_bot d hsn hL.2.2.1
  have : IsSimpleGroup (L ⧸ center L) := hL.2.2.2
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

omit [Finite Y] in
private theorem comp618_mem_normalizer_of_subgroupOf {L K : Subgroup Y} (hKL : K ≤ L) {k : L}
    (hk : k ∈ normalizer (K.subgroupOf L : Set L)) : (k : Y) ∈ normalizer (K : Set Y) := by
  rw [mem_normalizer_iff] at hk ⊢
  intro y
  constructor
  · intro hy
    exact (hk ⟨y, hKL hy⟩).mp hy
  · intro hy
    have hyL : y ∈ L := by
      have h1 : (k : Y) * y * (k : Y)⁻¹ ∈ L := hKL hy
      have h2 : y = (k : Y)⁻¹ * ((k : Y) * y * (k : Y)⁻¹) * (k : Y) := by group
      rw [h2]
      exact L.mul_mem (L.mul_mem (L.inv_mem k.2) h1) k.2
    exact (hk ⟨y, hyL⟩).mpr hy

omit [Finite Y] in
private theorem comp618_mem_normalizer_subgroupOf {L K : Subgroup Y} {k : L}
    (hk : (k : Y) ∈ normalizer (K : Set Y)) : k ∈ normalizer (K.subgroupOf L : Set L) := by
  rw [mem_normalizer_iff] at hk ⊢
  intro y
  exact hk y

private theorem comp618_card_inf (hKF1 : KFactSylowNormalizerIrreducible) (d : Data618 B Z Y₀)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hsimple : IsSimpleGroup L)
    (hidx : ¬ 3 ∣ (L ⊓ B).relIndex L) : Nat.card (L ⊓ B : Subgroup Y) = 3 := by
  have hsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1
  have hdvd : Nat.card (L ⊓ B : Subgroup Y) ∣ 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le (inf_le_right : L ⊓ B ≤ B)
    rwa [d.card_B] at h
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exfalso
    rw [pow_zero, Subgroup.card_eq_one] at hcard
    rw [hcard, Subgroup.relIndex_bot_left] at hidx
    have htop : CFSG.pPrimeCore 3 L = ⊤ := by
      apply le_antisymm le_top
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      rw [Subgroup.card_top]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx
    rw [comp618_pPrimeCore_eq_bot_of_isSubnormal d hsn] at htop
    exact bot_ne_top htop
  · simpa using hcard
  · exfalso
    have hBL : B ≤ L := by
      have h := Subgroup.eq_of_le_of_card_ge (inf_le_right : L ⊓ B ≤ B)
        (by rw [hcard, d.card_B]; norm_num)
      exact inf_eq_right.mp h
    refine hKF1 L (comp618_isKGroup_subgroup d.kgroup L) hsimple
      (comp618_exists_ne_comm hL.2.2.1) (B.subgroupOf L) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      ?_ ?_ (Z.subgroupOf L) (fun x hx => d.le_B hx) ?_ ?_
    · exact Subtype.ext (Subtype.ext
        (comp618_comm d (x := ((a : L) : Y)) (y := ((b : L) : Y)) a.2 b.2))
    · exact Subtype.ext (d.elem.2 (x : Y) hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
      exact d.card_B
    · rwa [Subgroup.inf_relIndex_left] at hidx
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (d.le_B.trans hBL)).toEquiv]
      exact d.card_Z
    · intro k hk
      exact comp618_mem_normalizer_subgroupOf
        (d.fix_Z (comp618_mem_normalizer_of_subgroupOf hBL hk))

theorem component_simple_card (hKF1 : KFactSylowNormalizerIrreducible) (d : Data618 B Z Y₀)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) :
    IsSimpleGroup ↥L ∧ Nat.card (L ⊓ B : Subgroup Y) = 3 ∧ ¬ 3 ∣ (L ⊓ B).relIndex L := by
  have hsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1
  have hsimple : IsSimpleGroup L := comp618_isSimpleGroup d hL
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (L ⊓ B) L := by
    rw [inf_comm]
    exact comp618_isSylowOf_inf d hsn
  obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl
  exact ⟨hsimple, comp618_card_inf hKF1 d hL hsimple hidx, hidx⟩

omit [Finite Y] in
private theorem comp618_eq_one_of_commute {L : Subgroup Y} (hc : center L = ⊥) {x : Y}
    (hxL : x ∈ L) (hx : ∀ g ∈ L, g * x = x * g) : x = 1 := by
  have hxc : (⟨x, hxL⟩ : L) ∈ center L :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hx g g.2)
  rw [hc] at hxc
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxc)

private theorem comp618_le_normalizer (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hc : center L = ⊥)
    (hcard : Nat.card (L ⊓ B : Subgroup Y) = 3) : B ≤ normalizer (L : Set Y) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1
  have hGW : CFSG.GorensteinWalter.IsComponentOf L ⊤ :=
    (CFSG.Adapters.isComponentOf_top_iff L).mp hL
  have hGW' : CFSG.GorensteinWalter.IsComponentOf (L.conjBy b) ⊤ :=
    ⟨le_top, (CFSG.GorensteinWalter.fstar_isSubnormal_conjugateSubgroup L b hsn).subgroupOf,
      CFSG.GorensteinWalter.fstar_isQuasisimple_conjugateSubgroup L b hGW.2.2⟩
  have hcomm : ⁅L, L.conjBy b⁆ = ⊥ :=
    CFSG.GorensteinWalter.component_commute_of_ne hGW hGW' (fun h => hne h.symm)
  have hcent : L ≤ centralizer (L.conjBy b : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hle : L ⊓ B ≤ L.conjBy b := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx.1, ?_⟩
    show b * x * b⁻¹ = x
    rw [comp618_comm d hb hx.2, mul_inv_cancel_right]
  have hbot : L ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (comp618_eq_one_of_commute hc hx.1
      fun g hg => (Subgroup.mem_centralizer_iff.mp (hcent hg) x (hle hx)).symm)
  rw [hbot, Subgroup.card_bot] at hcard
  omega

private theorem comp618_card_centralizer (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀)
    {L : Subgroup Y} (hsimple : IsSimpleGroup L) (hK : CFSG.IsKGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) (hc : center L = ⊥)
    (hcard : Nat.card (L ⊓ B : Subgroup Y) = 3) (hidx : ¬ 3 ∣ (L ⊓ B).relIndex L)
    (hBN : B ≤ normalizer (L : Set Y)) :
    3 ≤ Nat.card (B ⊓ centralizer (L : Set Y) : Subgroup Y) := by
  let ψ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hψ : ∀ (b : B) (x : L), ((ψ b x : L) : Y) = (b : Y) * x * (b : Y)⁻¹ := fun b x => by
    simp only [ψ, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe, coe_inclusion]
  have hinner : ∀ b : B, ∃ k : L, ψ b = MulAut.conj k := by
    intro b
    refine hKF2 L hK hsimple hnab ⟨(L ⊓ B).subgroupOf L, ?_, hidx⟩ (ψ b) ⟨1, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact hcard
    · have hb3 : b ^ 3 = 1 := Subtype.ext (d.elem.2 (b : Y) b.2)
      rw [pow_one, ← map_pow, hb3, map_one]
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hc]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    have h : k * g * k⁻¹ = g := by
      have h := congrArg (fun φ : MulAut L => φ g) hk
      simpa only [MulAut.conj_apply, MulAut.one_apply] using h
    calc g * k = k * g * k⁻¹ * k := by rw [h]
      _ = k * g := by group
  have hrange : ψ.range ≤ (MulAut.conj : L →* MulAut L).range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := hinner b
    exact ⟨k, hk.symm⟩
  have hR : Nat.card ((ψ.range).comap (MulAut.conj : L →* MulAut L)) = Nat.card ψ.range := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hrange]
  have h9 : Nat.card ψ.range ∣ 3 ^ 2 := by
    have h := Subgroup.card_range_dvd ψ
    rwa [d.card_B] at h
  have hLcard : Nat.card L = (L ⊓ B).relIndex L * 3 := by
    have h := Subgroup.relIndex_mul_card (L ⊓ B) L
    rw [inf_eq_left.mpr inf_le_left, hcard] at h
    exact h.symm
  have hL3 : Nat.card ψ.range ∣ (L ⊓ B).relIndex L * 3 := by
    rw [← hR, ← hLcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hle3 : Nat.card ψ.range ≤ 3 := by
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
    interval_cases j
    · rw [hjc]
      norm_num
    · rw [hjc]
      norm_num
    · exfalso
      rw [hjc, show (3 : ℕ) ^ 2 = 3 * 3 by norm_num] at hL3
      exact hidx (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hL3)
  have hker : ψ.ker = (centralizer (L : Set Y)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h1 : (b : Y) * y * (b : Y)⁻¹ = y := by
        have h2 := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : Y)) h
        simpa only [hψ, MulAut.one_apply] using h2
      calc y * (b : Y) = (b : Y) * y * (b : Y)⁻¹ * (b : Y) := by rw [h1]
        _ = (b : Y) * y := by group
    · intro h
      ext y
      rw [hψ, MulAut.one_apply, ← h y y.2, mul_inv_cancel_right]
  have hkerC : Nat.card ψ.ker = Nat.card (B ⊓ centralizer (L : Set Y) : Subgroup Y) := by
    rw [hker, ← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [d.card_B, hkerC] at hmul
  nlinarith

private theorem comp618_split_count (d : Data618 B Z Y₀) {ℓ C : Subgroup Y} (hℓ : ℓ ≤ B)
    (hC : C ≤ B) (hℓcard : Nat.card ℓ = 3) (hdisj : ℓ ⊓ C = ⊥) (hC3 : 3 ≤ Nat.card C) :
    Nat.card C = 3 ∧ ℓ ⊔ C = B := by
  have hdvd : ∀ {X : Subgroup Y}, X ≤ B → ∃ j ≤ 2, Nat.card X = 3 ^ j := by
    intro X hX
    have h := Subgroup.card_dvd_of_le hX
    rw [d.card_B, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
    exact (Nat.dvd_prime_pow Nat.prime_three).mp h
  have hCcard : Nat.card C = 3 := by
    obtain ⟨j, hj, hjc⟩ := hdvd hC
    interval_cases j
    · rw [hjc] at hC3
      norm_num at hC3
    · simpa using hjc
    · exfalso
      have hCeq : C = B := Subgroup.eq_of_le_of_card_ge hC (by rw [hjc, d.card_B]; norm_num)
      rw [hCeq, inf_eq_left.mpr hℓ, ← Subgroup.card_eq_one] at hdisj
      omega
  refine ⟨hCcard, Subgroup.eq_of_le_of_card_ge (sup_le hℓ hC) ?_⟩
  have h2 : 3 ∣ Nat.card (ℓ ⊔ C : Subgroup Y) := hℓcard ▸ Subgroup.card_dvd_of_le le_sup_left
  obtain ⟨j, hj, hjc⟩ := hdvd (sup_le hℓ hC)
  interval_cases j
  · rw [hjc] at h2
    norm_num at h2
  · exfalso
    have heq : ℓ = ℓ ⊔ C :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hjc, hℓcard, pow_one])
    rw [inf_eq_right.mpr (le_sup_right.trans heq.symm.le), ← Subgroup.card_eq_one] at hdisj
    omega
  · rw [hjc, d.card_B]
    norm_num

theorem component_split (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    B ≤ normalizer (L : Set Y) ∧ ∃ C : Subgroup Y, C = B ⊓ centralizer (L : Set Y) ∧
      Nat.card C = 3 ∧ (L ⊓ B) ⊓ C = ⊥ ∧ (L ⊓ B) ⊔ C = B := by
  obtain ⟨hsimple, hcard, hidx⟩ := component_simple_card hKF1 d hL
  have hsn : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1
  have hc : center L = ⊥ := comp618_center_eq_bot d hsn hL.2.2.1
  have hBN : B ≤ normalizer (L : Set Y) := comp618_le_normalizer d hL hc hcard
  refine ⟨hBN, B ⊓ centralizer (L : Set Y), rfl, ?_⟩
  have hdisj : (L ⊓ B) ⊓ (B ⊓ centralizer (L : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (comp618_eq_one_of_commute hc hx.1.1
      fun g hg => Subgroup.mem_centralizer_iff.mp hx.2.2 g hg)
  obtain ⟨hCcard, hsup⟩ := comp618_split_count d inf_le_right inf_le_left hcard hdisj
    (comp618_card_centralizer hKF2 d hsimple (comp618_isKGroup_subgroup d.kgroup L)
      (comp618_exists_ne_comm hL.2.2.1) hc hcard hidx hBN)
  exact ⟨hCcard, hdisj, hsup⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
