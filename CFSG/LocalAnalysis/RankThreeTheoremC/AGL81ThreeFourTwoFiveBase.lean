module

import CFSG.CGT.T75P.SylowSplit
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCore
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem self_le_normalizer_inf_normal {R N : Subgroup Y} [hN : N.Normal] :
    R ≤ normalizer ((R ⊓ N : Subgroup Y) : Set Y) :=
  (le_inf Subgroup.le_normalizer (le_top.trans (Subgroup.normalizer_eq_top (H := N)).ge)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

omit [Finite Y] in
theorem inf_centralizer_self_eq_bot_of_center {K : Subgroup Y} (hZ : center K = ⊥) :
    K ⊓ centralizer (K : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzC⟩
  have h : (⟨z, hzK⟩ : K) ∈ center K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h)

theorem exists_orderOf_eq_mem_center_of_le_sylow {p : ℕ} [Fact p.Prime] {R N : Subgroup Y}
    (hR : IsPGroup p R) (hNR : N ≤ R) (hRN : R ≤ normalizer (N : Set Y)) (hN : N ≠ ⊥) :
    ∃ z ∈ N, orderOf z = p ∧ ∀ g ∈ R, g * z = z * g := by
  haveI : Group.IsNilpotent R := hR.isNilpotent
  set N' : Subgroup R := N.subgroupOf R with hN'
  haveI : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hRN g.2) n).mp hn⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNR hx⟩ : R) ∈ N' := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  have hM : N' ⊓ center R ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  haveI : Nontrivial (N' ⊓ center R : Subgroup R) := (Subgroup.nontrivial_iff_ne_bot _).mpr hM
  have hMp : IsPGroup p (N' ⊓ center R : Subgroup R) := hR.to_subgroup _
  have hdvd : p ∣ Nat.card (N' ⊓ center R : Subgroup R) := by
    rcases hMp.card_eq_or_dvd with h1 | h1
    · exact absurd h1 Finite.one_lt_card.ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((x : R) : Y), (Subgroup.mem_inf.mp x.2).1, ?_, fun g hg => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp x.2).2 ⟨g, hg⟩)

theorem normalizer_zpowers_le_glbCoreOne {p : ℕ} (hp : 1 < p) {E : Subgroup Y} {z : Y}
    (hzE : z ∈ E) (hz : orderOf z = p) :
    normalizer ((zpowers z : Subgroup Y) : Set Y) ≤ CFSG.Open.GLBCore p 1 E := by
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hrank : 1 ≤ CFSG.Open.pRank p (zpowers z) :=
    CFSG.SectionRank.le_pRank hp le_rfl (CFSG.Open.isElemAbelian_zpowers hzp)
      (by rw [Nat.card_zpowers, hz, pow_one])
  exact le_sSup ⟨zpowers z, zpowers_le.mpr hzE, hrank, rfl⟩

omit [Finite Y] in
theorem mem_normalizer_zpowers_of_cyclic_normalizer {T : Subgroup Y} [Finite T]
    (hT : IsCyclic T) {z g : Y} (hz : z ∈ T) (hg : g ∈ normalizer (T : Set Y)) :
    g ∈ normalizer ((zpowers z : Subgroup Y) : Set Y) := by
  have hw : g * z * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  have hord : orderOf (g * z * g⁻¹) = orderOf z := by
    simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq z
  have heq : zpowers (⟨g * z * g⁻¹, hw⟩ : T) = zpowers (⟨z, hz⟩ : T) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
  have heq' : zpowers (g * z * g⁻¹) = zpowers z := by
    have h := congrArg (Subgroup.map T.subtype) heq
    rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  exact heq'

theorem le_openPRank_sup_of_commute {p k l : ℕ} (hp : 1 < p) {A B H : Subgroup Y}
    (hA : CFSG.Open.IsElemAbelian p A) (hB : CFSG.Open.IsElemAbelian p B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) (hAk : Nat.card A = p ^ k)
    (hBl : Nat.card B = p ^ l) (hH : A ⊔ B ≤ H) : k + l ≤ CFSG.Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp hH (hA.sup_of_commute hB hc)
    (by rw [CFSG.CGT.T75P.card_sup_of_commute hc hAB, hAk, hBl, pow_add])

theorem centralizer_subgroupOf_sup_sylow_eq_bot {p : ℕ} [Fact p.Prime] {K : Subgroup Y}
    [K.Normal] (R : Sylow p Y) (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hRC : (R : Subgroup Y) ⊓ centralizer (K : Set Y) = ⊥) :
    centralizer ((K.subgroupOf (K ⊔ (R : Subgroup Y)) : Subgroup ↥(K ⊔ (R : Subgroup Y))) :
      Set ↥(K ⊔ (R : Subgroup Y))) = ⊥ := by
  set H : Subgroup Y := K ⊔ (R : Subgroup Y) with hH
  set C : Subgroup Y := centralizer (K : Set Y) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hWp : IsPGroup p (H ⊓ C : Subgroup Y) := by
    rintro ⟨w, hwH, hwC⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hwH
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
    have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (k * r) ^ p ^ n ∈ K := by
      have hk1 : ((k : Y) : Y ⧸ K) = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul, hk1, one_mul,
        ← QuotientGroup.mk_pow, hrn, QuotientGroup.mk_one]
    have h3 : (k * r) ^ p ^ n ∈ K ⊓ C := ⟨h1, C.pow_mem hwC _⟩
    rw [hKC, Subgroup.mem_bot] at h3
    simpa using h3
  have hRW : (R : Subgroup Y) ≤ normalizer ((H ⊓ C : Subgroup Y) : Set Y) := by
    intro r hr
    have hrH : r ∈ H := (le_sup_right : (R : Subgroup Y) ≤ H) hr
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hwH, hwC⟩
      exact ⟨H.mul_mem (H.mul_mem hrH hwH) (H.inv_mem hrH), hCn.conj_mem w hwC r⟩
    · rintro ⟨hwH, hwC⟩
      refine ⟨?_, ?_⟩
      · have := H.mul_mem (H.mul_mem (H.inv_mem hrH) hwH) hrH
        simpa [mul_assoc] using this
      · have := hCn.conj_mem _ hwC r⁻¹
        simpa [mul_assoc] using this
  have hWR : H ⊓ C ≤ (R : Subgroup Y) := by
    have hsup := R.is_maximal' (IsPGroup.to_sup_of_normal_left' hWp R.isPGroup' hRW) le_sup_right
    rw [← hsup]
    exact le_sup_left
  rw [eq_bot_iff]
  intro h hh
  have hhC : (h : Y) ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_centralizer_iff.mp hh ⟨k, (le_sup_left : K ≤ H) hk⟩
      (Subgroup.mem_subgroupOf.mpr hk)
    exact congrArg Subtype.val this
  have h1 : (h : Y) ∈ (R : Subgroup Y) ⊓ C := ⟨hWR ⟨h.2, hhC⟩, hhC⟩
  rw [hRC, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).mpr (Subtype.ext h1)

theorem glbWeakCore_subgroupOf_le_subgroupOf {p : ℕ} (hp : 1 < p) {H R Y₀ : Subgroup Y}
    (hRH : R ≤ H) (hY₀ : CFSG.Open.GLBWeakCore p R ≤ Y₀) :
    CFSG.Open.GLBWeakCore p (R.subgroupOf H) ≤ Y₀.subgroupOf H := by
  refine (CFSG.PreuniquenessRankFour.Helpers.weakCore_le_iff p _ _).mpr ?_
  intro X hXR h2 h3
  set X' : Subgroup Y := X.map H.subtype with hX'
  have hXX' : X = X'.subgroupOf H :=
    (Subgroup.comap_map_eq_self_of_injective H.subtype_injective X).symm
  have hX'R : X' ≤ R := by
    have := Subgroup.map_mono (f := H.subtype) hXR
    rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at this
  have helig : CFSG.LargeEvenClassification.Helpers.weakPCoreEligible p R X' := by
    refine (CFSG.LargeEvenClassification.Helpers.weakPCoreEligible_internal hp R X' H hRH
      hX'R).mp ?_
    rw [← hXX']
    exact ⟨hXR, h2, h3⟩
  have hN : normalizer (X' : Set Y) ≤ Y₀ :=
    (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p helig.1 helig.2.1
      helig.2.2).trans hY₀
  intro n hn
  rw [Subgroup.mem_subgroupOf]
  exact hN (Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hn))

theorem card_inf_sylow_of_le_normalizer {p : ℕ} [Fact p.Prime] (R : Sylow p Y)
    {M : Subgroup Y} (hRM : (R : Subgroup Y) ≤ normalizer (M : Set Y)) :
    Nat.card ((R : Subgroup Y) ⊓ M : Subgroup Y) = p ^ (Nat.card M).factorization p := by
  set L : Subgroup Y := M ⊔ (R : Subgroup Y) with hL
  have hML : M ≤ L := le_sup_left
  have hRL : (R : Subgroup Y) ≤ L := le_sup_right
  haveI : (M.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr (sup_le Subgroup.le_normalizer hRM)
  obtain ⟨P, hP⟩ :=
    CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal (R.subtype hRL) (M.subgroupOf L)
  have h4 : ((R.subtype hRL : Sylow p L) : Subgroup L) ⊓ M.subgroupOf L =
      ((R : Subgroup Y) ⊓ M).subgroupOf L := by
    rw [Sylow.coe_subtype]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hRL)).toEquiv, ← h4, ← hP,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv]

omit [Finite Y] in
theorem isSolvable_inf_of_isSolvable_subgroupOf {K H Y₀ : Subgroup Y} (hKH : K ≤ H)
    (hs : Group.IsSolvable (Y₀.subgroupOf H)) : Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  let f : ↥(K ⊓ Y₀) →* ↥(Y₀.subgroupOf H) :=
    { toFun := fun x => ⟨⟨x, hKH (Subgroup.mem_inf.mp x.2).1⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab =>
    Subtype.ext (congrArg (fun y : ↥(Y₀.subgroupOf H) => ((y : H) : Y)) hab)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
