module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem mem_centralizer_subgroupOf {L : Subgroup G} (hLX : L ≤ X) (b : X) :
    b ∈ Subgroup.centralizer ((L.subgroupOf X : Subgroup X) : Set X) ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have := h ⟨l, hLX hl⟩ (Subgroup.mem_subgroupOf.2 hl)
    simpa only [Subtype.ext_iff, Subgroup.coe_mul] using congrArg Subtype.val this
  · intro h l' hl'
    apply Subtype.ext
    have hl : (l' : G) ∈ L := Subgroup.mem_subgroupOf.1 hl'
    simpa only [Subgroup.coe_mul] using h _ hl

theorem mem_zpowers_subgroupOf (x b : X) : b ∈ Subgroup.zpowers x ↔ (b : G) ∈ Subgroup.zpowers (x : G) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, Subtype.ext ?_⟩
    simpa using hn

theorem isElemAbelian_subgroupOf {p : ℕ} {B : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B) :
    IsElemAbelian p (B.subgroupOf X) :=
  (isElemAbelian_map_subtype X).1 (by rw [Subgroup.map_subgroupOf_eq_of_le hBX]; exact hB)

end Helpers

section Cfg

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem cfg_subgroupOf {p : ℕ} {B L : Subgroup G} {x : G} (hBX : B ≤ X) (hLX : L ≤ X) (hxX : x ∈ X)
    (hcfg : S171.Cfg G p B x L) :
    S171.Cfg X p (B.subgroupOf X) ⟨x, hxX⟩ (L.subgroupOf X) where
  prime := hcfg.prime
  odd := hcfg.odd
  elem := isElemAbelian_subgroupOf X hBX hcfg.elem
  card_ge := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
    rw [h]
    exact hcfg.card_ge
  mem := Subgroup.mem_subgroupOf.2 hcfg.mem
  ne_one := fun h => hcfg.ne_one (congrArg Subtype.val h)
  norm := by
    intro b hb
    apply (S267.mem_normalizer_map_iff_inj X.subtype X.subtype_injective).1
    rw [Subgroup.map_subgroupOf_eq_of_le hLX]
    exact hcfg.norm (Subgroup.mem_subgroupOf.1 hb)
  qs := isQuasisimple_subgroupOf X hLX hcfg.qs
  chev2 := chevSimple_subgroupOf X hLX hcfg.chev2
  cent := by
    intro b hb
    rw [mem_centralizer_subgroupOf X hLX, mem_zpowers_subgroupOf]
    exact hcfg.cent _ (Subgroup.mem_subgroupOf.1 hb)
  cyc := by
    intro S hS hSp
    have hmap : S.map X.subtype ≤ Subgroup.centralizer (L : Set G) := by
      intro g hg
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
      exact (mem_centralizer_subgroupOf X hLX s).1 (hS hs)
    have hp : IsPGroup p (S.map X.subtype) := hSp.of_equiv (Subgroup.equivMapOfInjective S X.subtype X.subtype_injective)
    have hc := hcfg.cyc _ hmap hp
    exact isCyclic_of_injective (Subgroup.equivMapOfInjective S X.subtype X.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective S X.subtype X.subtype_injective).injective
  idiag := (innerDiagMarking_subgroupOf_iff X hBX hLX).2 hcfg.idiag

end Cfg

section Maxg

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem maxG_subgroupOf {p : ℕ} {B : Subgroup G} (hBX : B ≤ X) (hmax : S171.MaxG p B) :
    S171.MaxG p (B.subgroupOf X) := by
  intro E U hE hU hU0 hEN
  have hi := X.subtype_injective
  have hE' : IsElemAbelian p (E.map X.subtype) := (isElemAbelian_map_subtype X).2 hE
  have hU' : IsPGroup 2 (U.map X.subtype) := hU.of_equiv (Subgroup.equivMapOfInjective U X.subtype hi)
  have hU0' : U.map X.subtype ≠ ⊥ := by
    intro h
    exact hU0 ((Subgroup.map_eq_bot_iff_of_injective _ hi).1 h)
  have hEN' : E.map X.subtype ≤ Subgroup.normalizer ((U.map X.subtype : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
    exact (S267.mem_normalizer_map_iff_inj X.subtype hi).2 (hEN he)
  have h := hmax (E.map X.subtype) (U.map X.subtype) hE' hU' hU0' hEN'
  have hc : Nat.card (B.subgroupOf X) = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [hc]
  exact (card_map_subtype X).symm.le.trans h

end Maxg

section Rest

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem inducesInnerMod_of_subgroupOf {p : ℕ} {L : Subgroup G} (hLX : L ≤ X) (b : X)
    (h : InducesInnerMod p (L.subgroupOf X) b) : InducesInnerMod p L (b : G) := by
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨(l : G), Subgroup.mem_subgroupOf.1 hl, fun y hy' => ?_⟩
  have hyX : (⟨y, hLX hy'⟩ : X) ∈ L.subgroupOf X := Subgroup.mem_subgroupOf.2 hy'
  have hm := hy ⟨y, hLX hy'⟩ hyX
  rw [← map_subtype_glaPPrimeCoreOf_subgroupOf p hLX]
  exact Subgroup.mem_map.2 ⟨_, hm, by simp⟩

theorem glaPComponent_subgroupOf_iff {p : ℕ} (hp : p.Prime) {L D K : Subgroup G} (hLX : L ≤ X) (hDX : D ≤ X)
    (hKX : K ≤ X) :
    CFSG.Open.GLAPComponent p (L.subgroupOf X ⊓ Subgroup.centralizer ((D.subgroupOf X : Subgroup X) : Set X))
        (K.subgroupOf X) ↔
      CFSG.Open.GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) K := by
  have hM : (L.subgroupOf X ⊓ Subgroup.centralizer ((D.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [map_inf_cent, Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_subgroupOf_eq_of_le hDX]
  have hK : (K.subgroupOf X).map X.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKX
  have h := Y10F.glaPComponent_map_iff (X := L.subgroupOf X ⊓ Subgroup.centralizer ((D.subgroupOf X : Subgroup X) : Set X))
    (J := K.subgroupOf X) hp X.subtype_injective
  rw [hM, hK] at h
  exact h.symm

theorem commutator_le_centralizer_of_subgroupOf {T B L : Subgroup G} (hTX : T ≤ X) (hBX : B ≤ X) (hLX : L ≤ X)
    (h : (⁅T.subgroupOf X, B.subgroupOf X⁆ : Subgroup X) ≤
      Subgroup.centralizer ((L.subgroupOf X : Subgroup X) : Set X)) :
    (⁅T, B⁆ : Subgroup G) ≤ Subgroup.centralizer (L : Set G) := by
  have hEq : (⁅T.subgroupOf X, B.subgroupOf X⁆ : Subgroup X).map X.subtype = ⁅T, B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTX, Subgroup.map_subgroupOf_eq_of_le hBX]
  intro c hc
  rw [← hEq] at hc
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc
  exact (mem_centralizer_subgroupOf X hLX c').1 (h hc')

theorem le_normalizer_subgroupOf' {A C : Subgroup G} (hAX : A ≤ X) (hCX : C ≤ X)
    (h : A ≤ Subgroup.normalizer (C : Set G)) :
    A.subgroupOf X ≤ Subgroup.normalizer ((C.subgroupOf X : Subgroup X) : Set X) := by
  intro b hb
  apply (S267.mem_normalizer_map_iff_inj X.subtype X.subtype_injective).1
  rw [Subgroup.map_subgroupOf_eq_of_le hCX]
  exact h (Subgroup.mem_subgroupOf.1 hb)

theorem le_centralizer_singleton_subgroupOf {A : Subgroup G} {x : G} (hAX : A ≤ X) (hxX : x ∈ X)
    (h : A ≤ Subgroup.centralizer ({x} : Set G)) :
    A.subgroupOf X ≤ Subgroup.centralizer ({(⟨x, hxX⟩ : X)} : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hb' := Subgroup.mem_centralizer_singleton_iff.1 (h (Subgroup.mem_subgroupOf.1 hb))
  apply Subtype.ext
  simpa only [Subgroup.coe_mul] using hb'

theorem extremalType_subgroupOf_iff {p : ℕ} {L : Subgroup G} (hLX : L ≤ X) :
    S171.ExtremalType p (L.subgroupOf X) ↔ S171.ExtremalType p L := by
  unfold S171.ExtremalType
  exact and_congr Iff.rfl (exists_congr fun n => and_congr Iff.rfl
    (or_congr (catalogIs_pSimple_subgroupOf X hLX).symm (catalogIs_pSimple_subgroupOf X hLX).symm))

theorem catalogIs_center_subgroupOf_iff {L : Subgroup G} (hLX : L ≤ X) {Q : TauCeti.CFSGIndex → Prop} :
    catalogIs (↥(L.subgroupOf X) ⧸ Subgroup.center ↥(L.subgroupOf X)) Q ↔
      catalogIs (↥L ⧸ Subgroup.center ↥L) Q := by
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  exact catalogIs_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem glaStdSubPre_subgroupOf_iff {p : ℕ} {B L D K : Subgroup G} {x : G} (hxX : x ∈ X) (hBX : B ≤ X) (hLX : L ≤ X)
    (hDX : D ≤ X) (hKX : K ≤ X) :
    CFSG.Open.GLAStdSubPre p (B.subgroupOf X) ⟨x, hxX⟩ (L.subgroupOf X) (D.subgroupOf X) (K.subgroupOf X) ↔
      CFSG.Open.GLAStdSubPre p B x L D K := by
  have h := glaStdSubPre_map_iff X (p := p) (B.subgroupOf X) (L.subgroupOf X) (D.subgroupOf X) (K.subgroupOf X) ⟨x, hxX⟩
  rw [Subgroup.map_subgroupOf_eq_of_le hBX, Subgroup.map_subgroupOf_eq_of_le hLX,
    Subgroup.map_subgroupOf_eq_of_le hDX, Subgroup.map_subgroupOf_eq_of_le hKX] at h
  exact h.symm

theorem zpowers_subgroupOf_eq {β : G} (hβX : β ∈ X) :
    (Subgroup.zpowers β).subgroupOf X = Subgroup.zpowers (⟨β, hβX⟩ : X) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_zpowers_subgroupOf]

end Rest

section Small

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem commutator_subgroupOf_map {T B : Subgroup G} (hTX : T ≤ X) (hBX : B ≤ X) :
    (⁅T.subgroupOf X, B.subgroupOf X⁆ : Subgroup X).map X.subtype = ⁅T, B⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTX, Subgroup.map_subgroupOf_eq_of_le hBX]

theorem glaSmall_iff_of_mulEquiv {Ω H : Type} [Group Ω] [Group H] {K' : Subgroup Ω} {K : Subgroup H}
    (e : ↥K' ≃* ↥K) : CFSG.Assembly.LargeEvenSmall K' ↔ CFSG.Assembly.LargeEvenSmall K := by
  unfold CFSG.Assembly.LargeEvenSmall CFSG.Assembly.LargeEvenIsU42
  constructor
  · rintro (⟨F, hF, hfin, hcard, hf⟩ | hf)
    · exact Or.inl ⟨F, hF, hfin, hcard, hf.map fun f => e.symm.trans f⟩
    · exact Or.inr (hf.map fun f => e.symm.trans f)
  · rintro (⟨F, hF, hfin, hcard, hf⟩ | hf)
    · exact Or.inl ⟨F, hF, hfin, hcard, hf.map fun f => e.trans f⟩
    · exact Or.inr (hf.map fun f => e.trans f)

theorem exists_glaStdSubPre_subgroupOf {p : ℕ} {B L : Subgroup G} {x : G} (hxX : x ∈ X) (hBX : B ≤ X) (hLX : L ≤ X)
    (h : ∃ D K : Subgroup G, CFSG.Open.GLAStdSubPre p B x L D K) :
    ∃ D K : Subgroup X, CFSG.Open.GLAStdSubPre p (B.subgroupOf X) ⟨x, hxX⟩ (L.subgroupOf X) D K := by
  obtain ⟨D, K, hpre⟩ := h
  have hDX : D ≤ X := hpre.1.trans hBX
  have hKX : K ≤ X := ((hpre.2.2.2.2.2.1.1).trans inf_le_left).trans hLX
  exact ⟨D.subgroupOf X, K.subgroupOf X, (glaStdSubPre_subgroupOf_iff X hxX hBX hLX hDX hKX).2 hpre⟩

theorem small_subgroupOf {p : ℕ} {B L : Subgroup G} {x : G} (hxX : x ∈ X) (hBX : B ≤ X) (hLX : L ≤ X)
    (hsmall : ∀ D K : Subgroup G, CFSG.Open.GLAStdSubPre p B x L D K → CFSG.Assembly.LargeEvenSmall K) :
    ∀ D K : Subgroup X, CFSG.Open.GLAStdSubPre p (B.subgroupOf X) ⟨x, hxX⟩ (L.subgroupOf X) D K →
      CFSG.Assembly.LargeEvenSmall K := by
  intro D' K' h
  have h2 := (glaStdSubPre_map_iff X (p := p) (B.subgroupOf X) (L.subgroupOf X) D' K' ⟨x, hxX⟩).2 h
  rw [Subgroup.map_subgroupOf_eq_of_le hBX, Subgroup.map_subgroupOf_eq_of_le hLX] at h2
  have h3 := hsmall _ _ h2
  exact (glaSmall_iff_of_mulEquiv (Subgroup.equivMapOfInjective K' X.subtype X.subtype_injective)).2 h3

theorem exists_T_subgroupOf {T B L : Subgroup G} {x : G} (hxX : x ∈ X) (hTX : T ≤ X) (hBX : B ≤ X) (hLX : L ≤ X)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hne : (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    ∃ T' : Subgroup X, T' ≤ Subgroup.normalizer ((L.subgroupOf X : Subgroup X) : Set X) ∧
      T' ≤ Subgroup.centralizer ({(⟨x, hxX⟩ : X)} : Set X) ∧ IsPGroup 2 T' ∧
      B.subgroupOf X ≤ Subgroup.normalizer (T' : Set X) ∧ (⁅T', B.subgroupOf X⁆ : Subgroup X) ≠ ⊥ := by
  refine ⟨T.subgroupOf X, le_normalizer_subgroupOf' X hTX hLX hTN, le_centralizer_singleton_subgroupOf X hTX hxX hTC,
    IsPGroup.of_injective hT2 (Subgroup.subgroupOfEquivOfLe hTX).toMonoidHom (MulEquiv.injective _),
    le_normalizer_subgroupOf' X hBX hTX hBT, ?_⟩
  intro h
  apply hne
  rw [← commutator_subgroupOf_map X hTX hBX, h, Subgroup.map_bot]

end Small

end CFSG.LocalAnalysis.GLTheoremA.T171

end
