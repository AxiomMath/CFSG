module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SteinbergBSFreeAbelianActor
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_twoGroup_fixedPointFree {K V : Subgroup G} {q : ℕ}
    (hK2 : IsPGroup 2 K) (hKne : K ≠ ⊥)
    (hVK : V ≤ Subgroup.normalizer (K : Set G))
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q V ≤ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hKnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  refine CFSG.SectionRank.pRank_le hq.one_lt (H := V) (k := 1) ?_
  intro E hEV hE
  haveI : IsMulCommutative ↥E := hE.1
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  let act := Subgroup.conjMulDistribMulActionOfLeNormalizer E K (hEV.trans hVK)
  letI : MulDistribMulAction E K := act
  have hfree : ∀ a : E, a ≠ 1 → ∀ x : K, a • x = x → x = 1 := by
    intro a ha x hx
    have hcoe : ((a • x : K) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit E K (hEV.trans hVK) a x
    have hxa : (x : G) * (a : G) = (a : G) * (x : G) := by
      have hx' : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
        rw [← hcoe]
        exact congrArg (fun y : K => (y : G)) hx
      calc (x : G) * (a : G) = (a : G) * (x : G) * (a : G)⁻¹ * (a : G) := by
            rw [hx']
        _ = (a : G) * (x : G) := by group
    have haV : (a : G) ∈ V := hEV a.2
    have ha1 : (a : G) ≠ 1 := by
      intro h
      exact ha (Subtype.ext h)
    exact Subtype.ext (hfpf (a : G) haV ha1 (x : G) x.2 hxa)
  obtain ⟨-, hEcyc⟩ :=
    CFSG.LocalAnalysis.SteinbergBS.abelian_free_nilpotent_actor_cyclic (A := ↥E) (N := ↥K) hfree
  haveI : IsCyclic ↥E := hEcyc
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => mul_comm a b
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic E)
  have hcard : Nat.card E = orderOf x := (orderOf_eq_card_of_zpowers_eq_top hx).symm
  have hxq : x ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 (x : G) x.2
  have hdvd : orderOf x ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hxq
  have hcardq : Nat.card ↥E ≤ q := by
    rw [hcard]
    exact Nat.le_of_dvd hq.pos hdvd
  simpa [pow_one] using hcardq

theorem isComplement'_subgroupOf_of_normal_cover {K V X : Subgroup G}
    (hKX : K ≤ X) (hVX : V ≤ X) (hKnorm : (K.subgroupOf X).Normal)
    (hdisj : K ⊓ V = ⊥) (hcover : ∀ x ∈ X, ∃ k ∈ K, ∃ v ∈ V, x = k * v) :
    (V.subgroupOf X).IsComplement' (K.subgroupOf X) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxV hxK
    apply Subtype.ext
    rw [Subgroup.mem_subgroupOf] at hxV hxK
    exact Subgroup.disjoint_def.mp (disjoint_iff.mpr hdisj).symm hxV hxK
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨k, hkK, v, hvV, hx⟩ := hcover x x.2
    let kx : X := ⟨k, hKX hkK⟩
    let vx : X := ⟨v, hVX hvV⟩
    have hkx : kx ∈ K.subgroupOf X := by
      simpa [kx, Subgroup.mem_subgroupOf] using hkK
    let k'x : X := vx⁻¹ * kx * vx
    have hk'x : k'x ∈ K.subgroupOf X := hKnorm.conj_mem' kx hkx vx
    refine ⟨vx, ?_, k'x, ?_, ?_⟩
    · simpa [vx, Subgroup.mem_subgroupOf] using hvV
    · exact hk'x
    · apply Subtype.ext
      change (vx : G) * (k'x : G) = (x : G)
      calc (vx : G) * (k'x : G) = v * (v⁻¹ * k * v) := rfl
        _ = k * v := by group
        _ = x := hx.symm

private theorem inf_twoGroup_eq_bot_of_isElemAbelian {E K : Subgroup G} {q : ℕ}
    (hK2 : IsPGroup 2 K) (hE : IsElemAbelian q E) (hq : q.Prime) (hq2 : q ≠ 2) :
    E ⊓ K = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨a, ha⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  obtain ⟨b, hb⟩ := hK2.exists_card_eq
  rw [ha, hb]
  exact Nat.Coprime.pow a b ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)

private theorem exists_injective_hom_to_complement {K V X E : Subgroup G}
    (hKX : K ≤ X) (hVX : V ≤ X) (hKnorm : (K.subgroupOf X).Normal)
    (hdisj : K ⊓ V = ⊥)
    (hcover : ∀ x ∈ X, ∃ k ∈ K, ∃ v ∈ V, x = k * v)
    (hEX : E ≤ X) (hEinf : E ⊓ K = ⊥) :
    ∃ f : E →* G, Function.Injective f ∧ f.range ≤ V := by
  haveI : (K.subgroupOf X).Normal := hKnorm
  have hcomp := isComplement'_subgroupOf_of_normal_cover hKX hVX hKnorm hdisj hcover
  let e : X ⧸ (K.subgroupOf X) ≃* V :=
    (hcomp.QuotientMulEquiv).trans (Subgroup.subgroupOfEquivOfLe hVX)
  let qmap : E →* X ⧸ (K.subgroupOf X) :=
    (QuotientGroup.mk' (K.subgroupOf X)).comp (Subgroup.inclusion hEX)
  let fV : E →* V := e.toMonoidHom.comp qmap
  let fG : E →* G := V.subtype.comp fV
  have hvker : ∀ x : E, fV x = 1 → x = 1 := by
    intro x hx
    have hq1 : qmap x = 1 := e.injective (by simpa [fV] using hx)
    have hxKX : Subgroup.inclusion hEX x ∈ K.subgroupOf X :=
      (QuotientGroup.eq_one_iff _).mp hq1
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using hxKX
    have hx1 : (x : G) = 1 := by
      have hmem : (x : G) ∈ E ⊓ K := ⟨x.2, hxK⟩
      rw [hEinf, Subgroup.mem_bot] at hmem
      exact hmem
    exact Subtype.ext hx1
  have hfG : Function.Injective fG := by
    intro x y hxy
    have hfxy : fV x = fV y := Subtype.ext hxy
    have h1 : fV (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hfxy]
      group
    have h2 : x * y⁻¹ = 1 := hvker _ h1
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h2]
      _ = y := one_mul y
  have hfr : fG.range ≤ V := by
    rintro y ⟨x, rfl⟩
    exact (fV x).2
  exact ⟨fG, hfG, hfr⟩

theorem pRank_le_one_of_twoGroup_frobeniusProduct {K V W X : Subgroup G} {q : ℕ}
    (hK2 : IsPGroup 2 K) (hKne : K ≠ ⊥)
    (hKX : K ≤ X) (hVX : V ≤ X) (hWX : W ≤ X)
    (hKnorm : (K.subgroupOf X).Normal)
    (hdisj : K ⊓ V = ⊥)
    (hcover : ∀ x ∈ X, ∃ k ∈ K, ∃ v ∈ V, x = k * v)
    (hVK : V ≤ Subgroup.normalizer (K : Set G))
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q W ≤ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hVrank : CFSG.Open.pRank q V ≤ 1 :=
    pRank_le_one_of_twoGroup_fixedPointFree hK2 hKne hVK hfpf hq hq2
  refine CFSG.SectionRank.pRank_le hq.one_lt (H := W) (k := 1) ?_
  intro E hEW hE
  have hEX : E ≤ X := hEW.trans hWX
  have hEinf : E ⊓ K = ⊥ := inf_twoGroup_eq_bot_of_isElemAbelian hK2 hE hq hq2
  obtain ⟨fG, hfG, hfr⟩ :=
    exists_injective_hom_to_complement hKX hVX hKnorm hdisj hcover hEX hEinf
  haveI : IsMulCommutative ↥E := hE.1
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => mul_comm a b
  have hpow : ∀ a : E, a ^ q = 1 := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 (a : G) a.2
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have hnle : n ≤ CFSG.Open.pRank q V :=
    CFSG.SectionRank.le_pRank_of_injective hq.one_lt hcomm hpow hn fG hfG hfr
  have hn1 : n ≤ 1 := hnle.trans hVrank
  have hcard : Nat.card ↥E ≤ q := by
    calc Nat.card ↥E = q ^ n := hn
      _ ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hn1
      _ = q := pow_one q
  simpa using hcard


theorem pRank_le_one_of_twoGroup_frobeniusSup {K V W X : Subgroup G} {q : ℕ}
    (hK2 : IsPGroup 2 K) (hKne : K ≠ ⊥)
    (hKX : K ≤ X) (hVX : V ≤ X) (hWX : W ≤ X)
    (hKnorm : (K.subgroupOf X).Normal)
    (hsup : X = K ⊔ V) (hdisj : K ⊓ V = ⊥)
    (hVK : V ≤ Subgroup.normalizer (K : Set G))
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q W ≤ 1 := by
  haveI : (K.subgroupOf X).Normal := hKnorm
  have hcover : ∀ x ∈ X, ∃ k ∈ K, ∃ v ∈ V, x = k * v := by
    have hsupX : (K.subgroupOf X) ⊔ (V.subgroupOf X) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKX hVX, hsup, Subgroup.subgroupOf_self]
    intro x hx
    let xX : X := ⟨x, hx⟩
    have hxsup : xX ∈ (K.subgroupOf X) ⊔ (V.subgroupOf X) := by
      rw [hsupX]
      exact Subgroup.mem_top xX
    obtain ⟨k, hk, v, hv, hkv⟩ := (Subgroup.mem_sup_of_normal_left).mp hxsup
    exact ⟨(k : G), by simpa [Subgroup.mem_subgroupOf] using hk,
      (v : G), by simpa [Subgroup.mem_subgroupOf] using hv,
      by simpa using (congrArg (fun y : X => (y : G)) hkv).symm⟩
  exact pRank_le_one_of_twoGroup_frobeniusProduct hK2 hKne hKX hVX hWX hKnorm hdisj hcover
    hVK hfpf hq hq2

private theorem central_of_orderPrime_in_centralizer {p : ℕ}
    {P₀ C L R : Subgroup G} (hp : p.Prime)
    (hC : C = Subgroup.centralizer (P₀ : Set G)) (hP₀card : Nat.card P₀ = p)
    (hLC : L ≤ C) (hR : R = C ⊓ Subgroup.centralizer (L : Set G)) :
    P₀ ≤ R ∧ P₀.subgroupOf R ≤ Subgroup.center R := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRleC : R ≤ C := by rw [hR]; exact inf_le_left
  have hP₀C : P₀ ≤ C := by
    rw [hC]
    haveI : IsCyclic ↥P₀ := isCyclic_of_prime_card hP₀card
    exact (Subgroup.le_centralizer_iff_isMulCommutative).mpr inferInstance
  have hP₀centL : P₀ ≤ Subgroup.centralizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlC : l ∈ Subgroup.centralizer (P₀ : Set G) := by
      have h : l ∈ C := hLC hl
      rwa [hC] at h
    exact ((Subgroup.mem_centralizer_iff.mp hlC) a ha).symm
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact fun a ha => ⟨hP₀C ha, hP₀centL ha⟩
  · intro y hy
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hyG : (y : G) ∈ P₀ := by simpa [Subgroup.mem_subgroupOf] using hy
    have hxC : (x : G) ∈ Subgroup.centralizer (P₀ : Set G) := by
      have h : (x : G) ∈ C := hRleC x.2
      rwa [hC] at h
    exact ((Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyG).symm

private theorem orderPrime_mem_center_of_cyclic_pSylow {p : ℕ}
    {P₀ R : Subgroup G} (hP₀R : P₀ ≤ R) (hP₀card : Nat.card P₀ = p)
    (hP₀center : P₀.subgroupOf R ≤ Subgroup.center R)
    (hcyc : ∀ S : Subgroup G, S ≤ R → IsPGroup p S → IsCyclic S) :
    ∀ x : R, orderOf x = p → x ∈ Subgroup.center R := by
  have hP₀normal : (P₀.subgroupOf R).Normal := Subgroup.normal_of_le_center hP₀center
  intro x hxord
  have hXRp : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxord, pow_one]
  obtain ⟨S, hXS⟩ := hXRp.exists_le_sylow
  have hScyc : IsCyclic ↥(S : Subgroup R) := by
    have hmap : IsCyclic ↥((S : Subgroup R).map R.subtype) :=
      hcyc _ (Subgroup.map_subtype_le _) (S.isPGroup'.map R.subtype)
    exact (S.equivMapOfInjective R.subtype R.subtype_injective).isCyclic.mpr hmap
  haveI : IsCyclic ↥(S : Subgroup R) := hScyc
  have hP₀S : P₀.subgroupOf R ≤ (S : Subgroup R) :=
    IsPGroup.le_sylow_of_normal (p := p)
      (IsPGroup.of_card (n := 1) (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀R).toEquiv, hP₀card,
          pow_one])) S
  have hXRcard : Nat.card ↥((Subgroup.zpowers x).subgroupOf (S : Subgroup R)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXS : _ ≤ (S : Subgroup R))).toEquiv,
      Nat.card_zpowers, hxord]
  have hP₀Scard : Nat.card ↥((P₀.subgroupOf R).subgroupOf (S : Subgroup R)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀S).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀R).toEquiv, hP₀card]
  have heq : (Subgroup.zpowers x).subgroupOf (S : Subgroup R) =
      (P₀.subgroupOf R).subgroupOf (S : Subgroup R) :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hXRcard, hP₀Scard])
  have hxP₀ : x ∈ P₀.subgroupOf R := by
    have hxX : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hxS : x ∈ (S : Subgroup R) := hXS hxX
    have hxsub : (⟨x, hxS⟩ : (S : Subgroup R)) ∈
        (P₀.subgroupOf R).subgroupOf (S : Subgroup R) := by
      rw [← heq]
      simpa [Subgroup.mem_subgroupOf] using hxX
    simpa [Subgroup.mem_subgroupOf] using hxsub
  exact hP₀center hxP₀

private theorem isCyclic_sylow_of_pSubgroups_cyclic {p : ℕ} {R : Subgroup G}
    (hcyc : ∀ S : Subgroup G, S ≤ R → IsPGroup p S → IsCyclic S) :
    ∀ S : Sylow p R, IsCyclic ↥(S : Subgroup R) := by
  intro S
  have hmap : IsCyclic ↥((S : Subgroup R).map R.subtype) :=
    hcyc _ (Subgroup.map_subtype_le _) (S.isPGroup'.map R.subtype)
  exact (S.equivMapOfInjective R.subtype R.subtype_injective).isCyclic.mpr hmap

private theorem subgroupOf_centralizer_normal {L C R : Subgroup G}
    (hLC : L ≤ C) (hLnormal : (L.subgroupOf C).Normal)
    (hR : R = C ⊓ Subgroup.centralizer (L : Set G)) :
    (R.subgroupOf C).Normal := by
  have hD : ((Subgroup.centralizer (L : Set G)).subgroupOf C).Normal :=
    CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel.centralizer_subgroupOf_normal
      hLC hLnormal
  have hEq : R.subgroupOf C = (Subgroup.centralizer (L : Set G)).subgroupOf C := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [hR] at hx
      exact hx.2
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [hR]
      exact ⟨x.2, hx⟩
  rwa [hEq]

private theorem normalComplement_normal_in_centralizer {C R : Subgroup G} {HR : Subgroup R}
    (hRleC : R ≤ C) (hRC : (R.subgroupOf C).Normal)
    (hHRchar : HR.Characteristic) :
    ((HR.map R.subtype).subgroupOf C).Normal := by
  have hnormR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRleC).mp hRC
  let HG : Subgroup G := HR.map R.subtype
  have hHGR : HG ≤ R := Subgroup.map_subtype_le HR
  have hHGcharR : (HG.subgroupOf R).Characteristic := by
    have hEq : HG.subgroupOf R = HR := by
      ext y
      rw [Subgroup.mem_subgroupOf]
      change R.subtype y ∈ HR.map R.subtype ↔ y ∈ HR
      rw [Subgroup.mem_map_iff_mem R.subtype_injective]
    rw [hEq]
    exact hHRchar
  have hHGnormR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (HG : Set G) :=
    CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
      hHGR hHGcharR
  have hHGleC : HG ≤ C := hHGR.trans hRleC
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHGleC).mpr (hnormR.trans hHGnormR)

private theorem normalComplement_le_relPPrimeCore {p : ℕ} {C R : Subgroup G}
    {HR : Subgroup R} (hRleC : R ≤ C)
    (hHGnormalC : ((HR.map R.subtype).subgroupOf C).Normal)
    (hHRcop : Nat.Coprime p (Nat.card HR)) :
    HR.map R.subtype ≤ CFSG.Open.relPPrimeCore p C := by
  refine le_sSup ⟨(Subgroup.map_subtype_le HR).trans hRleC, hHGnormalC, ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective]
  exact hHRcop

private theorem characteristic_of_normalComplement {p : ℕ} [Fact p.Prime]
    {R : Subgroup G} {HR : Subgroup R} [HR.Normal]
    (hHRcop : Nat.Coprime p (Nat.card HR)) (hHRp : IsPGroup p (R ⧸ HR)) :
    HR.Characteristic := by
  refine CFSG.GroupTheory.FrobeniusNormalComplement.IsNormalPComplement.characteristic
    ⟨inferInstance, hHRcop.symm, ?_⟩
  obtain ⟨k, hk⟩ := hHRp.exists_card_eq
  exact ⟨k, by rw [Subgroup.index_eq_card, hk]⟩

private theorem qSubgroup_le_normalComplement {p q : ℕ} {R : Subgroup G} {HR : Subgroup R}
    [HR.Normal] (hp : p.Prime) (hq : q.Prime) (hHRp : IsPGroup p (R ⧸ HR)) (hqp : q ≠ p)
    {Q : Subgroup G} (hQR : Q ≤ R) (hQq : IsPGroup q Q) :
    Q ≤ HR.map R.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let img : Subgroup (R ⧸ HR) := (Q.subgroupOf R).map (QuotientGroup.mk' HR)
  have himgq : IsPGroup q img := (hQq.comap_subtype).map _
  have himgp : IsPGroup p img := hHRp.to_subgroup img
  haveI : Subsingleton ↥img := IsPGroup.subsingleton_of_ne himgp himgq (Ne.symm hqp)
  have himgbot : img = ⊥ := by
    apply Subgroup.eq_bot_iff_forall img |>.mpr
    intro y hy
    have h : (⟨y, hy⟩ : img) = ⟨1, img.one_mem⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val h
  have hle : Q.subgroupOf R ≤ HR := by
    have h := (Subgroup.map_eq_bot_iff (Q.subgroupOf R) (f := QuotientGroup.mk' HR)).mp
      himgbot
    rwa [QuotientGroup.ker_mk'] at h
  intro y hy
  have hyR : y ∈ R := hQR hy
  have hysub : (⟨y, hyR⟩ : R) ∈ Q.subgroupOf R := hy
  have hyHR : (⟨y, hyR⟩ : R) ∈ HR := hle hysub
  exact Subgroup.mem_map_of_mem R.subtype hyHR

theorem qSubgroup_le_relPPrimeCore_of_cyclic_pSubgroups {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {P₀ C L R : Subgroup G}
    (hC : C = Subgroup.centralizer (P₀ : Set G)) (hP₀card : Nat.card P₀ = p)
    (hLC : L ≤ C) (hLnormal : (L.subgroupOf C).Normal)
    (hR : R = C ⊓ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ R → IsPGroup p S → IsCyclic S)
    {Q : Subgroup G} (hQR : Q ≤ R) (hQq : IsPGroup q Q) :
    Q ≤ CFSG.Open.relPPrimeCore p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hRleC : R ≤ C := by rw [hR]; exact inf_le_left
  obtain ⟨hP₀R, hP₀center⟩ :=
    central_of_orderPrime_in_centralizer hp hC hP₀card hLC hR
  have hcen := orderPrime_mem_center_of_cyclic_pSylow hP₀R hP₀card hP₀center hcyc
  have hcomp : CFSG.HasNormalPComplement p ↥R :=
    CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central
      (isCyclic_sylow_of_pSubgroups_cyclic hcyc) hcen
  obtain ⟨HR, hHRnormal, hHRcop, hHRp⟩ := hcomp
  haveI : HR.Normal := hHRnormal
  have hHRchar : HR.Characteristic :=
    characteristic_of_normalComplement hHRcop hHRp
  have hRC : (R.subgroupOf C).Normal := subgroupOf_centralizer_normal hLC hLnormal hR
  have hHGnormalC : ((HR.map R.subtype).subgroupOf C).Normal :=
    normalComplement_normal_in_centralizer hRleC hRC hHRchar
  have hHGleCore : HR.map R.subtype ≤ CFSG.Open.relPPrimeCore p C :=
    normalComplement_le_relPPrimeCore hRleC hHGnormalC hHRcop
  exact (qSubgroup_le_normalComplement hp hq hHRp hqp hQR hQq).trans hHGleCore

end CFSG.LocalAnalysis.AGL81TheoremCD
