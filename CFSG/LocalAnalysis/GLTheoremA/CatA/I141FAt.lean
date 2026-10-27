module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

abbrev Wn (L : Subgroup G) : Subgroup G := Subgroup.normalizer (L : Set G)

abbrev Nw (p : ℕ) (L : Subgroup G) : Subgroup ↥(Wn L) := (GLAPPrimeCoreOf p L).subgroupOf (Wn L)

theorem glaPPrimeCore_conj_mem (p : ℕ) (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {n : G} (hn : n ∈ GLAPPrimeCoreOf p K) :
    g * n * g⁻¹ ∈ GLAPPrimeCoreOf p K := by
  have hK : GLBConj g K = K := mem_normalizer_iff_gLBConj_eq.1 hg
  have hEq : GLBConj g (GLAPPrimeCoreOf p K) = GLAPPrimeCoreOf p K := by
    rw [← glaPPrimeCoreOf_gLBConj, hK]
  have hn' : n ∈ GLBConj g (GLAPPrimeCoreOf p K) := by
    rw [hEq]
    exact hn
  rw [mem_gLBConj] at hn'
  exact hn'

theorem nw_normal (p : ℕ) (L : Subgroup G) : (Nw p L).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact glaPPrimeCore_conj_mem p L g.2 hn

instance (p : ℕ) (L : Subgroup G) : (Nw p L).Normal := nw_normal p L

abbrev Gam (p : ℕ) (L : Subgroup G) : Type := ↥(Wn L) ⧸ Nw p L

abbrev Hq (p : ℕ) (L : Subgroup G) : Subgroup (Gam p L) :=
  (L.subgroupOf (Wn L)).map (QuotientGroup.mk' (Nw p L))

abbrev Eq' (p : ℕ) (L E : Subgroup G) : Subgroup (Gam p L) :=
  (E.subgroupOf (Wn L)).map (QuotientGroup.mk' (Nw p L))

abbrev Jq (p : ℕ) (L J : Subgroup G) : Subgroup (Gam p L) :=
  (J.subgroupOf (Wn L)).map (QuotientGroup.mk' (Nw p L))

theorem GLAPPrimeCoreOf_eq_map (p : ℕ) (L : Subgroup G) :
    GLAPPrimeCoreOf p L = (CFSG.pPrimeCore p ↥L).map L.subtype := rfl

theorem GLAPPrimeCoreOf_le_self (p : ℕ) (L : Subgroup G) : GLAPPrimeCoreOf p L ≤ L := by
  rw [GLAPPrimeCoreOf_eq_map]
  exact Subgroup.map_subtype_le _

theorem le_wn (L : Subgroup G) : L ≤ Wn L := Subgroup.le_normalizer

theorem glaPPrimeCoreOf_le_wn (p : ℕ) (L : Subgroup G) : GLAPPrimeCoreOf p L ≤ Wn L :=
  (GLAPPrimeCoreOf_le_self p L).trans (le_wn L)

theorem not_dvd_card_GLAPPrimeCoreOf {p : ℕ} (hp : p.Prime) (L : Subgroup G) :
    ¬ p ∣ Nat.card (GLAPPrimeCoreOf p L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [GLAPPrimeCoreOf_eq_map, Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card


theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) (K : Subgroup G) :
    IsElemAbelian p (E.subgroupOf K) := by
  obtain ⟨hc, hpow⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have key : (a : G) * (b : G) = (b : G) * (a : G) := by
      have h := hc.is_comm.comm (⟨(a : G), Subgroup.mem_subgroupOf.1 a.2⟩ : ↥E)
        ⟨(b : G), Subgroup.mem_subgroupOf.1 b.2⟩
      exact congrArg Subtype.val h
    exact key
  · apply Subtype.ext
    exact hpow (a : G) (Subgroup.mem_subgroupOf.1 ha)

theorem isElemAbelian_map {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : IsElemAbelian p A) : IsElemAbelian p (A.map f) := by
  obtain ⟨hc, hpow⟩ := hA
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    have hxy : x * y = y * x := by
      have h := hc.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩
      exact congrArg Subtype.val h
    apply Subtype.ext
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow]
    have := hpow x hx
    rw [this, map_one]

theorem card_Nw (p : ℕ) (L : Subgroup G) : Nat.card (Nw p L) = Nat.card (GLAPPrimeCoreOf p L) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glaPPrimeCoreOf_le_wn p L)).toEquiv

theorem not_dvd_card_Nw {p : ℕ} (hp : p.Prime) (L : Subgroup G) : ¬ p ∣ Nat.card (Nw p L) := by
  rw [card_Nw]
  exact not_dvd_card_GLAPPrimeCoreOf hp L

abbrev piq (p : ℕ) (L : Subgroup G) : ↥(Wn L) →* Gam p L := QuotientGroup.mk' (Nw p L)

theorem mem_GLAPPrimeCoreOf_iff (p : ℕ) (L : Subgroup G) (x : ↥L) :
    (x : G) ∈ GLAPPrimeCoreOf p L ↔ x ∈ CFSG.pPrimeCore p ↥L := by
  rw [GLAPPrimeCoreOf_eq_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def psiL (p : ℕ) (L : Subgroup G) : ↥L →* ↥(Hq p L) :=
  ((piq p L).comp (Subgroup.inclusion (le_wn L))).codRestrict (Hq p L) fun x =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)

theorem psiL_surjective (p : ℕ) (L : Subgroup G) : Function.Surjective (psiL p L) := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
  exact ⟨⟨w, Subgroup.mem_subgroupOf.1 hw⟩, rfl⟩

theorem psiL_ker (p : ℕ) (L : Subgroup G) : (psiL p L).ker = CFSG.pPrimeCore p ↥L := by
  ext x
  rw [MonoidHom.mem_ker, ← mem_GLAPPrimeCoreOf_iff, ← Subgroup.mem_subgroupOf]
  unfold psiL
  rw [MonoidHom.codRestrict_apply, Subtype.ext_iff]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_one, piq, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff]
  rfl

noncomputable def hqEquiv (p : ℕ) (L : Subgroup G) : (↥L ⧸ CFSG.pPrimeCore p ↥L) ≃* ↥(Hq p L) :=
  (QuotientGroup.quotientMulEquivOfEq (psiL_ker p L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (psiL p L) (psiL_surjective p L))

theorem hq_normal (p : ℕ) (L : Subgroup G) : (Hq p L).Normal := by
  have hL : (L.subgroupOf (Wn L)).Normal := inferInstance
  exact hL.map _ (QuotientGroup.mk'_surjective _)

theorem hq_core (p : ℕ) (hp : p.Prime) (L : Subgroup G) : GLAPPrimeCoreOf p (Hq p L) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : CFSG.pPrimeCore p ↥(Hq p L) = ⊥ :=
    CFSG.pPrimeCore_eq_bot_of_mulEquiv p (hqEquiv p L) (CFSG.pPrimeCore_quotient_eq_bot hp)
  rw [GLAPPrimeCoreOf_eq_map, h, Subgroup.map_bot]

theorem isChevSimple_congr' {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevSimple q A) : IsChevSimple q B := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem hq_chev (p : ℕ) (hp : p.Prime) (L : Subgroup G)
    (hchev : IsChevSimple 2 (PSimple p L)) :
    IsChevSimple 2 (↥(Hq p L) ⧸ Subgroup.center ↥(Hq p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let e : ↥(Hq p L) ≃* PQuot p L := (hqEquiv p L).symm
  have hq : ↥(Hq p L) ⧸ Subgroup.center ↥(Hq p L) ≃* PQuot p L ⧸ Subgroup.center (PQuot p L) :=
    QuotientGroup.congr (Subgroup.center ↥(Hq p L)) (Subgroup.center (PQuot p L)) e
      (Subgroup.map_center_eq e)
  exact isChevSimple_congr' hq.symm hchev


theorem nw_le_L (p : ℕ) (L : Subgroup G) : Nw p L ≤ L.subgroupOf (Wn L) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact GLAPPrimeCoreOf_le_self p L (Subgroup.mem_subgroupOf.1 hx)

theorem centralizer_map (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E) :
    (Subgroup.centralizer ((E.subgroupOf (Wn L)) : Set ↥(Wn L))).map (piq p L) =
      Subgroup.centralizer ((Eq' p L E : Subgroup (Gam p L)) : Set (Gam p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p (E.subgroupOf (Wn L)) :=
    isPGroup_of_isElemAbelian (isElemAbelian_subgroupOf hE _)
  exact (CFSG.Semidihedral.Local.coprime_centralizer_prime_complement_core_quotient p (Nw p L)
    (not_dvd_card_Nw hp L) (E.subgroupOf (Wn L)) hA).1

theorem map_inf_of_le_ker {X : Type*} [Group X] (N A B : Subgroup X) [N.Normal] (hNA : N ≤ A) :
    (A ⊓ B).map (QuotientGroup.mk' N) = A.map (QuotientGroup.mk' N) ⊓ B.map (QuotientGroup.mk' N) := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro y ⟨hyA, hyB⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hyA
  obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.1 hyB
  have hab' : a⁻¹ * b ∈ N := (QuotientGroup.eq).1 hab.symm
  have hbA : b ∈ A := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact A.mul_mem ha (hNA hab')
  exact Subgroup.mem_map.2 ⟨b, ⟨hbA, hb⟩, hab⟩

theorem inf_map_eq (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E) :
    ((L.subgroupOf (Wn L)) ⊓ Subgroup.centralizer ((E.subgroupOf (Wn L)) : Set ↥(Wn L))).map
        (piq p L) = Hq p L ⊓ Subgroup.centralizer ((Eq' p L E : Subgroup (Gam p L)) : Set (Gam p L)) := by
  rw [map_inf_of_le_ker (Nw p L) (L.subgroupOf (Wn L)) _ (nw_le_L p L),
    centralizer_map p hp L E hE]

abbrev Cc (L E : Subgroup G) : Subgroup G := L ⊓ Subgroup.centralizer (E : Set G)

abbrev CQ (p : ℕ) (L E : Subgroup G) : Subgroup (Gam p L) :=
  Subgroup.centralizer ((Eq' p L E : Subgroup (Gam p L)) : Set (Gam p L))

theorem cc_le_wn (L E : Subgroup G) : Cc L E ≤ Wn L := inf_le_left.trans (le_wn L)

theorem mem_CA_of_mem_cc {L E : Subgroup G} {x : G} (hx : x ∈ Cc L E) :
    (⟨x, cc_le_wn L E hx⟩ : ↥(Wn L)) ∈
      Subgroup.centralizer ((E.subgroupOf (Wn L)) : Set ↥(Wn L)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  apply Subtype.ext
  have hE : (h : G) ∈ E := Subgroup.mem_subgroupOf.1 hh
  have hx' : x ∈ Subgroup.centralizer (E : Set G) := hx.2
  have := Subgroup.mem_centralizer_iff.1 hx' (h : G) hE
  exact this

def fC (p : ℕ) (L E : Subgroup G) : ↥(Cc L E) →* Gam p L :=
  (piq p L).comp (Subgroup.inclusion (cc_le_wn L E))

theorem fC_mem_hq (p : ℕ) (L E : Subgroup G) (x : ↥(Cc L E)) : fC p L E x ∈ Hq p L :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2.1)

theorem fC_mem_cq (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E)
    (x : ↥(Cc L E)) : fC p L E x ∈ CQ p L E := by
  have h := Subgroup.mem_map_of_mem (piq p L) (mem_CA_of_mem_cc x.2)
  rw [centralizer_map p hp L E hE] at h
  exact h

def fT (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E) :
    ↥(Cc L E) →* ↥(Hq p L ⊓ CQ p L E) :=
  (fC p L E).codRestrict _ fun x => Subgroup.mem_inf.2 ⟨fC_mem_hq p L E x, fC_mem_cq p hp L E hE x⟩

theorem fT_surjective (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E)
    (hEW : E ≤ Wn L) : Function.Surjective (fT p hp L E hE) := by
  rintro ⟨y, hy⟩
  have hy' := hy
  rw [← inf_map_eq p hp L E hE] at hy'
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hy'
  have hwL : (w : G) ∈ L := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hw).1
  have hwC : (w : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2 ⟨h, hEW hh⟩
      (Subgroup.mem_subgroupOf.2 hh)
    exact congrArg Subtype.val h1
  refine ⟨⟨(w : G), hwL, hwC⟩, ?_⟩
  apply Subtype.ext
  exact hwy


theorem fT_ker_not_dvd (p : ℕ) (hp : p.Prime) (L E : Subgroup G) (hE : IsElemAbelian p E) :
    ¬ p ∣ Nat.card (fT p hp L E hE).ker := by
  intro hdiv
  have hle : ((fT p hp L E hE).ker).map (Cc L E).subtype ≤ GLAPPrimeCoreOf p L := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : fT p hp L E hE x = 1 := hx
    have h1 : fC p L E x = 1 := congrArg Subtype.val hx'
    have h2 : Subgroup.inclusion (cc_le_wn L E) x ∈ Nw p L := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    exact Subgroup.mem_subgroupOf.1 h2
  refine not_dvd_card_GLAPPrimeCoreOf hp L (hdiv.trans ?_)
  rw [← Subgroup.card_map_of_injective (Cc L E).subtype_injective]
  exact Subgroup.card_dvd_of_le hle

theorem component_transfer (p : ℕ) (hp : p.Prime) (L E J : Subgroup G) (hE : IsElemAbelian p E)
    (hEW : E ≤ Wn L) (hJ : GLAPComponent p (Cc L E) J) :
    GLAPComponent p (Hq p L ⊓ CQ p L E) (Jq p L J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJC, hPC⟩ := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hbij := (CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (fT p hp L E hE) (fT_surjective p hp L E hE hEW) (fT_ker_not_dvd p hp L E hE)).1.mapsTo
  have hmap := hbij hPC
  refine (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).2 ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have hx := (fT p hp L E hE ⟨(j : G), hJC hjJ⟩).2
    exact hx
  · have heq : (Jq p L J).subgroupOf (Hq p L ⊓ CQ p L E) =
        (J.subgroupOf (Cc L E)).map (fT p hp L E hE) := by
      ext ⟨y, hy⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · intro hyJ
        obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.1 hyJ
        refine ⟨⟨(j : G), hJC (Subgroup.mem_subgroupOf.1 hj)⟩, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.1 hj
        · apply Subtype.ext
          exact hjy
      · rintro ⟨x, hx, hxy⟩
        apply Subgroup.mem_map.2
        refine ⟨Subgroup.inclusion (cc_le_wn L E) x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx), ?_⟩
        have := congrArg Subtype.val hxy
        exact this
    rw [heq]
    exact hmap

def phiJ (p : ℕ) (L J : Subgroup G) (hJL : J ≤ L) : ↥(GLAPPrimeCoreOf p J) →* Gam p L :=
  (piq p L).comp (Subgroup.inclusion ((GLAPPrimeCoreOf_le_self p J).trans (hJL.trans (le_wn L))))


theorem phiJ_ker (p : ℕ) (L J : Subgroup G) (hJL : J ≤ L) :
    (phiJ p L J hJL).ker = (GLAPPrimeCoreOf p L).subgroupOf (GLAPPrimeCoreOf p J) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' : Subgroup.inclusion ((GLAPPrimeCoreOf_le_self p J).trans (hJL.trans (le_wn L))) x ∈
        Nw p L := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 h'
  · intro h
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)

theorem relIndex_eq_card (p : ℕ) (L J : Subgroup G) (hJL : J ≤ L) :
    (GLAPPrimeCoreOf p L).relIndex (GLAPPrimeCoreOf p J) = Nat.card (phiJ p L J hJL).range := by
  rw [Subgroup.relIndex, ← phiJ_ker p L J hJL, Subgroup.index_ker]

theorem range_le_core (p : ℕ) (hp : p.Prime) (L J : Subgroup G) (hJL : J ≤ L) :
    (phiJ p L J hJL).range ≤ GLAPPrimeCoreOf p (Jq p L J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTJ : (phiJ p L J hJL).range ≤ Jq p L J := by
    rintro _ ⟨o, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (GLAPPrimeCoreOf_le_self p J o.2))
  have hcomm : ∀ g : ↥(Jq p L J), ∀ t ∈ (phiJ p L J hJL).range,
      (g : Gam p L) * t * (g : Gam p L)⁻¹ ∈ (phiJ p L J hJL).range := by
    intro g t ht
    obtain ⟨o, rfl⟩ := (MonoidHom.mem_range).1 ht
    obtain ⟨j, hj, hjg⟩ := Subgroup.mem_map.1 g.2
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have hjN : (j : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hjJ
    let o' : ↥(GLAPPrimeCoreOf p J) :=
      ⟨(j : G) * (o : G) * (j : G)⁻¹, glaPPrimeCore_conj_mem p J hjN o.2⟩
    refine ⟨o', ?_⟩
    have hOW : GLAPPrimeCoreOf p J ≤ Wn L := (GLAPPrimeCoreOf_le_self p J).trans (hJL.trans (le_wn L))
    have hval : (phiJ p L J hJL o') = piq p L (j * Subgroup.inclusion hOW o * j⁻¹) := by
      apply congrArg (piq p L)
      apply Subtype.ext
      rfl
    rw [hval, map_mul, map_mul, map_inv]
    have hg : piq p L j = (g : Gam p L) := hjg
    rw [hg]
    rfl
  have hTn : ((phiJ p L J hJL).range.subgroupOf (Jq p L J)).Normal := by
    constructor
    intro t ht g
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact hcomm g _ ht
  have hcard : Nat.Coprime p (Nat.card ((phiJ p L J hJL).range.subgroupOf (Jq p L J))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv]
    rw [← Subgroup.index_ker]
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdiv => ?_
    exact not_dvd_card_GLAPPrimeCoreOf hp J (hdiv.trans (Subgroup.index_dvd_card _))
  have hle : (phiJ p L J hJL).range.subgroupOf (Jq p L J) ≤ CFSG.pPrimeCore p ↥(Jq p L J) :=
    le_sSup ⟨hTn, hcard⟩
  intro y hy
  have hyJ : y ∈ Jq p L J := hTJ hy
  have hmem : (⟨y, hyJ⟩ : ↥(Jq p L J)) ∈ (phiJ p L J hJL).range.subgroupOf (Jq p L J) :=
    Subgroup.mem_subgroupOf.2 hy
  rw [GLAPPrimeCoreOf_eq_map]
  exact Subgroup.mem_map.2 ⟨⟨y, hyJ⟩, hle hmem, rfl⟩


@[expose] def ParityModel : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (H E J : Subgroup Γ),
    H.Normal → GLAPPrimeCoreOf p H = ⊥ → IsChevSimple 2 (↥H ⧸ Subgroup.center ↥H) →
    IsElemAbelian p E → GLAPComponent p (H ⊓ Subgroup.centralizer (E : Set Γ)) J →
    Odd (Nat.card (GLAPPrimeCoreOf p J))

theorem i141At_of_facts (hF : ParityModel) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I141At G p := by
  intro hp hp2 X L E J _hX hLX hchev hE hEL hJ
  haveI : Fact p.Prime := ⟨hp⟩
  have hJL : J ≤ L :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ).1.trans
      inf_le_left
  have hodd := hF p hp hp2 (Gam p L) (Hq p L) (Eq' p L E) (Jq p L J) (hq_normal p L)
    (hq_core p hp L) (hq_chev p hp L hchev) (isElemAbelian_map _ (isElemAbelian_subgroupOf hE _))
    (component_transfer p hp L E J hE hEL hJ)
  rw [relIndex_eq_card p L J hJL]
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (range_le_core p hp L J hJL))

end CFSG.LocalAnalysis.GLTheoremA.I141F
