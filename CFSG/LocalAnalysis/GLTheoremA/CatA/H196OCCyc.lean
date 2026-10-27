module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFEH196Card
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Chev
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H196OC

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie isL2 ambiguousChev)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (Lemma123.autQ Lemma123.autQ_injective
  Lemma123.autQ_conj)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (map_glaPPrimeCoreOf_of_injective)

theorem centralizer_zpowers_eq {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem map_autQ_innerAut (Y : Type*) [Group Y] :
    (innerAut Y).map (Lemma123.autQ Y) = innerAut (Y ⧸ Subgroup.center Y) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(y : Y ⧸ Subgroup.center Y), (Lemma123.autQ_conj y).symm⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨MulAut.conj y, ⟨y, rfl⟩, Lemma123.autQ_conj y⟩

theorem coreFree_of_autQ {Y : Type*} [Group Y] (hY : commutator Y = ⊤) (p : ℕ)
    (H D : Subgroup (MulAut Y))
    (h : GLAPPrimeCoreOf p (H.map (Lemma123.autQ Y) ⊓
      Subgroup.centralizer ((D.map (Lemma123.autQ Y) : Subgroup _) : Set _)) = ⊥) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut Y))) = ⊥ := by
  set φ := Lemma123.autQ Y with hφdef
  have hφ : Function.Injective φ := Lemma123.autQ_injective hY
  have hmap : (H ⊓ Subgroup.centralizer (D : Set (MulAut Y))).map φ =
      H.map φ ⊓ Subgroup.centralizer ((D.map φ : Subgroup _) : Set _) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, ⟨hxH, hxC⟩, rfl⟩
      refine ⟨⟨x, hxH, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hxC) d hd]
    · rintro ⟨⟨x, hxH, rfl⟩, hyC⟩
      refine ⟨x, ⟨hxH, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩, rfl⟩
      apply hφ
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.1 hyC) (φ d) ⟨d, hd, rfl⟩
  have h1 := map_glaPPrimeCoreOf_of_injective p φ hφ (H ⊓ Subgroup.centralizer (D : Set (MulAut Y)))
  rw [hmap, h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h1

theorem nonabelian_centerQuot {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := nonabelian_innerAut hK
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine ⟨(x : K ⧸ Subgroup.center K), (y : K ⧸ Subgroup.center K), fun h => hab ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
  apply Lemma123.autQ_injective hK.1
  rw [map_mul, map_mul, Lemma123.autQ_conj, Lemma123.autQ_conj, ← map_mul, ← map_mul, h]


theorem coreFree_cyc_simple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hChev : IsChevSimple p S)
    {x : MulAut S} (hxord : orderOf x = p) {H : Subgroup (MulAut S)} (hH : innerAut S ≤ H)
    (hxH : x ∈ Subgroup.normalizer (H : Set (MulAut S)))
    (hexc : ¬ (p = 3 ∧ catalogIs S (onLie (isL2 27)) ∧ x ∉ innerAut S)) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hxord ▸ pow_orderOf_eq_one x
  rcases hChev with hL | hAmb
  · obtain ⟨idx, ⟨e⟩, hch⟩ := CFSG.HardMathSupport.Dickson.I271.lieType_of_catalogIs hL
    by_cases hxI : x ∈ innerAut S
    · exact CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds S hS hnc idx ⟨e⟩
        p hp hp2 hch x hxI hxord H hH
    · have hn27 : ¬ (p = 3 ∧ CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S) :=
        fun h => hexc ⟨h.1, ys03_catalogIs_of_isL227 h.2, hxI⟩
      exact CFSG.HardMathSupport.Dickson.I271.defCharOuterCoreFree_of_kdata
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCoreFree_holds
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCentInner_holds S hS hnc idx ⟨e⟩
        p hp hp2 hch hn27 x hxord hxI H hH
  · exact ys03_coreFree_of_strongBal hS hnc hp (ys03_dvd_card_amb hp2 hAmb)
      (ys03_strongBal_amb hp hp2 hS hnc hAmb) hxp hH hxH

theorem coreFree_cyc_quasi {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K)) {g : MulAut K}
    (hgp : g ^ p = 1) {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H)
    (hgH : g ∈ Subgroup.normalizer (H : Set (MulAut K)))
    (hexc : ¬ (p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27)) ∧ g ∉ innerAut K)) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({g} : Set (MulAut K))) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := finite_mulAut K
  by_cases hg1 : g = 1
  · subst hg1
    have hHC : H ⊓ Subgroup.centralizer ({1} : Set (MulAut K)) = H := by
      ext h
      simp [Subgroup.mem_centralizer_iff]
    rw [hHC]
    exact GLAPPrimeCoreOf_eq_bot_of_innerAut hK hch (I196ChevCard_holds p) hH
  have hgord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hφ : Function.Injective (Lemma123.autQ K) := Lemma123.autQ_injective hK.1
  rw [← centralizer_zpowers_eq]
  refine coreFree_of_autQ hK.1 p H (Subgroup.zpowers g) ?_
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq]
  have hxord : orderOf (Lemma123.autQ K g) = p := by rw [orderOf_injective _ hφ g, hgord]
  have hH' : innerAut (K ⧸ Subgroup.center K) ≤ H.map (Lemma123.autQ K) := by
    rw [← map_autQ_innerAut]
    exact Subgroup.map_mono hH
  have hxH' : Lemma123.autQ K g ∈
      Subgroup.normalizer ((H.map (Lemma123.autQ K) : Subgroup _) : Set (MulAut _)) :=
    Subgroup.le_normalizer_map _ ⟨g, hgH, rfl⟩
  refine coreFree_cyc_simple hp hp2 hK.2 (nonabelian_centerQuot hK) hch hxord hH' hxH' ?_
  rintro ⟨h3, hL, hxI⟩
  refine hexc ⟨h3, hL, fun hgI => hxI ?_⟩
  rw [← map_autQ_innerAut]
  exact ⟨g, hgI, rfl⟩

theorem isCoreFreeLocalType_of_card_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    {A : Subgroup (MulAut K)} (hA : CFSG.Open.IsElemAbelian p A) (hcard : Nat.card A ≤ p)
    (hL : p = 3 → catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27)) → A ≤ innerAut K) :
    IsCoreFreeLocalType p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := finite_mulAut K
  intro D hDA H hH hDN
  by_cases hD : D = ⊥
  · subst hD
    have hHC : H ⊓ Subgroup.centralizer ((⊥ : Subgroup (MulAut K)) : Set (MulAut K)) = H := by
      ext h
      simp [Subgroup.mem_centralizer_iff]
    rw [hHC]
    exact GLAPPrimeCoreOf_eq_bot_of_innerAut hK hch (I196ChevCard_holds p) hH
  obtain ⟨⟨g, hgD⟩, hg1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD
  have hg1 : g ≠ 1 := fun h => hg1' (Subtype.ext h)
  have hgp : g ^ p = 1 := hA.2 g (hDA hgD)
  have hgord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hDeq : D = Subgroup.zpowers g := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgD) ?_).symm
    rw [Nat.card_zpowers, hgord]
    exact (Subgroup.card_le_of_le hDA).trans hcard
  rw [hDeq, centralizer_zpowers_eq]
  refine coreFree_cyc_quasi hp hp2 hK hch hgp hH (hDN hgD) ?_
  rintro ⟨h3, h27, hgI⟩
  exact hgI (hL h3 h27 (hDA hgD))

end CFSG.LocalAnalysis.GLTheoremA.H196OC

end
