module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] (X : Subgroup G)

theorem mem_map_subtype {A : Subgroup X} {z : X} : (z : G) ∈ A.map X.subtype ↔ z ∈ A := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwe : w = z := Subtype.ext hwz
    exact hwe ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem isElemAbelian_map_subtype {p : ℕ} {A : Subgroup X} :
    IsElemAbelian p (A.map X.subtype) ↔ IsElemAbelian p A := by
  have e : A ≃* A.map X.subtype := Subgroup.equivMapOfInjective A X.subtype X.subtype_injective
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply e.injective
      rw [map_mul, map_mul]
      exact hc.is_comm.comm (e a) (e b)
    · apply Subtype.ext
      have h := hp (X.subtype a) ((mem_map_subtype X).2 ha)
      rw [← map_pow] at h
      simpa using h
  · rintro ⟨hc, hp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have h := congrArg e (hc.is_comm.comm (e.symm a) (e.symm b))
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, hp a ha, map_one]

theorem card_map_subtype {A : Subgroup X} : Nat.card (A.map X.subtype) = Nat.card A :=
  (Subgroup.card_map_of_injective X.subtype_injective).trans rfl

theorem normal_subgroupOf_of_le_normalizer {L : Subgroup G} (hLX : L ≤ X) (hXN : X ≤ Subgroup.normalizer (L : Set G)) :
    (L.subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hXN

theorem isQuasisimple_subgroupOf {L : Subgroup G} (hLX : L ≤ X) (hq : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.Open.IsQuasisimple ↥(L.subgroupOf X) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX) hq

theorem pSimple_subgroupOf_nonempty (p : ℕ) {L : Subgroup G} (hLX : L ≤ X) :
    Nonempty (PSimple p (L.subgroupOf X) ≃* PSimple p L) :=
  K144.pSimple_subgroupOf_equiv hLX

theorem chevSimple_subgroupOf {p : ℕ} {L : Subgroup G} (hLX : L ≤ X) (h : IsChevSimple 2 (PSimple p L)) :
    IsChevSimple 2 (PSimple p (L.subgroupOf X)) := by
  obtain ⟨e⟩ := pSimple_subgroupOf_nonempty X p hLX
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e.symm h

theorem catalogIs_pSimple_subgroupOf {p : ℕ} {L : Subgroup G} (hLX : L ≤ X) {Q : TauCeti.CFSGIndex → Prop} :
    catalogIs (PSimple p L) Q ↔ catalogIs (PSimple p (L.subgroupOf X)) Q := by
  obtain ⟨e⟩ := pSimple_subgroupOf_nonempty X p hLX
  exact (catalogIs_congr e).symm

end Basic

section Cent

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem map_inf_cent (M D : Subgroup X) :
    (M ⊓ Subgroup.centralizer (D : Set X)).map X.subtype =
      M.map X.subtype ⊓ Subgroup.centralizer ((D.map X.subtype : Subgroup G) : Set G) :=
  S267.map_inf_centralizer_inj X.subtype X.subtype_injective M D

end Cent

section Std

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem glaStdSubPre_map_iff {p : ℕ} (B L D K : Subgroup X) (x : X) :
    CFSG.Open.GLAStdSubPre p (B.map X.subtype) (x : G) (L.map X.subtype) (D.map X.subtype) (K.map X.subtype) ↔
      CFSG.Open.GLAStdSubPre p B x L D K := by
  have hi := X.subtype_injective
  constructor
  · rintro ⟨hDB, hD2, hDc, hxD, hK, hKc, hDeq⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hi).1 hDB, (isElemAbelian_map_subtype X).1 hD2,
      (card_map_subtype X).symm.trans hDc, (mem_map_subtype X).1 hxD, ?_, ?_, ?_⟩
    · apply Subgroup.map_injective hi
      rw [hK, ← map_inf_cent, Y10F.glaLayer_map hi]
    · exact (Y10F.isComponentOf_map_iff hi).1 (by rw [map_inf_cent]; exact hKc)
    · apply Subgroup.map_injective hi
      rw [hDeq, map_inf_cent]
  · rintro ⟨hDB, hD2, hDc, hxD, hK, hKc, hDeq⟩
    refine ⟨Subgroup.map_mono hDB, (isElemAbelian_map_subtype X).2 hD2, (card_map_subtype X).trans hDc,
      (mem_map_subtype X).2 hxD, ?_, ?_, ?_⟩
    · rw [← map_inf_cent, Y10F.glaLayer_map hi, hK]
    · rw [← map_inf_cent]; exact (Y10F.isComponentOf_map_iff hi).2 hKc
    · rw [← map_inf_cent, hDeq]

section Marking

theorem canonical_marking_congr {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {P : CFSG.Assembly.LargeEvenMarkProp X} {P' : CFSG.Assembly.LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ → P lab R I F ((CFSG.StandardType.centerQuotCongr f).trans θ))
    (h : CFSG.Assembly.LargeEvenMarking Y P') : CFSG.Assembly.LargeEvenMarking X P := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, (CFSG.StandardType.centerQuotCongr f).trans θ, hPP' lab R I F θ hθ⟩

theorem gla_marking_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {PA : CFSG.Assembly.LargeEvenMarkProp A} {PB : CFSG.Assembly.LargeEvenMarkProp B}
    (h1 : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : B ⧸ Subgroup.center B ≃* R), PB lab R I F θ → PA lab R I F ((CFSG.StandardType.centerQuotCongr e).trans θ))
    (h2 : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : A ⧸ Subgroup.center A ≃* R), PA lab R I F θ → PB lab R I F ((CFSG.StandardType.centerQuotCongr e.symm).trans θ)) :
    CFSG.Assembly.LargeEvenMarking A PA ↔ CFSG.Assembly.LargeEvenMarking B PB :=
  ⟨fun h => canonical_marking_congr e.symm h2 h, fun h => canonical_marking_congr e h1 h⟩

theorem largeEvenInduces_transfer {A B R : Type} [Group A] [Group B] [Group R] (e : A ≃* B)
    (θ : B ⧸ Subgroup.center B ≃* R) (φ : MulAut R) (relA : A → A → Prop) (relB : B → B → Prop)
    (hrel : ∀ a a' : A, relB (e a) (e a') ↔ relA a a') :
    CFSG.Assembly.LargeEvenInduces θ relB φ ↔
      CFSG.Assembly.LargeEvenInduces ((CFSG.StandardType.centerQuotCongr e).trans θ) relA φ := by
  unfold CFSG.Assembly.LargeEvenInduces
  constructor
  · intro h a a' haa'
    have h' := h (e a) (e a') ((hrel a a').2 haa')
    simpa only [MulEquiv.trans_apply, CFSG.StandardType.centerQuotCongr_mk] using h'
  · intro h m m' hmm
    obtain ⟨a, rfl⟩ := e.surjective m
    obtain ⟨a', rfl⟩ := e.surjective m'
    have h' := h a a' ((hrel a a').1 hmm)
    simpa only [MulEquiv.trans_apply, CFSG.StandardType.centerQuotCongr_mk] using h'

theorem innerDiagMarking_subgroupOf_iff {G : Type} [Group G] [Finite G] (X : Subgroup G) {B L : Subgroup G}
    (hBX : B ≤ X) (hLX : L ≤ X) :
    InnerDiagMarking (B.subgroupOf X) (L.subgroupOf X) ↔ InnerDiagMarking B L := by
  have hi := X.subtype_injective
  unfold InnerDiagMarking
  refine gla_marking_of_equiv (Subgroup.subgroupOfEquivOfLe hLX) ?_ ?_
  · rintro lab R _ I F θ ⟨hN, hb⟩
    refine ⟨?_, fun b' hb' => ?_⟩
    · intro b' hb'
      have hb'G : (b' : G) ∈ B := Subgroup.mem_subgroupOf.1 hb'
      apply (S267.mem_normalizer_map_iff_inj X.subtype hi).1
      rw [Subgroup.map_subgroupOf_eq_of_le hLX]
      exact hN hb'G
    · obtain ⟨φ, hφ, hind⟩ := hb (b' : G) (Subgroup.mem_subgroupOf.1 hb')
      refine ⟨φ, hφ, (largeEvenInduces_transfer (Subgroup.subgroupOfEquivOfLe hLX) θ φ _ _ ?_).1 hind⟩
      intro a a'
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Iff.rfl
  · rintro lab R _ I F θ ⟨hN', hb'⟩
    refine ⟨?_, fun b hb => ?_⟩
    · intro b hb
      have hbX : b ∈ X := hBX hb
      have hmem : (⟨b, hbX⟩ : ↥X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.2 hb
      have h2 := (S267.mem_normalizer_map_iff_inj X.subtype hi).2 (hN' hmem)
      rw [Subgroup.map_subgroupOf_eq_of_le hLX] at h2
      exact h2
    · obtain ⟨φ, hφ, hind⟩ := hb' ⟨b, hBX hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      refine ⟨φ, hφ, (largeEvenInduces_transfer (Subgroup.subgroupOfEquivOfLe hLX).symm θ φ _ _ ?_).1 hind⟩
      intro m m'
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Iff.rfl

section InnDiag

noncomputable def pQuotSubgroupOfIso {G : Type} [Group G] (X : Subgroup G) {p : ℕ} {L : Subgroup G} (hLX : L ≤ X) :
    PQuot p (L.subgroupOf X) ≃* PQuot p L :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLX)
    (LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hLX))

theorem pQuotSubgroupOfIso_mk {G : Type} [Group G] (X : Subgroup G) {p : ℕ} {L : Subgroup G} (hLX : L ≤ X)
    (l : ↥(L.subgroupOf X)) :
    pQuotSubgroupOfIso (p := p) X hLX (QuotientGroup.mk l) =
      (QuotientGroup.mk (Subgroup.subgroupOfEquivOfLe hLX l) : PQuot p L) := by
  unfold pQuotSubgroupOfIso
  exact QuotientGroup.congr_mk _ _ _ _ _

theorem indRel_subgroupOf_iff {G : Type} [Group G] [Finite G] (X : Subgroup G) {p : ℕ} {L : Subgroup G}
    (hLX : L ≤ X) (a : X) (q q' : PQuot p (L.subgroupOf X)) :
    indRel p L (a : G) (pQuotSubgroupOfIso X hLX q) (pQuotSubgroupOfIso X hLX q') ↔
      indRel p (L.subgroupOf X) a q q' := by
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l₀', rfl⟩ := QuotientGroup.mk_surjective q'
  unfold indRel
  constructor
  · rintro ⟨m, m', hm, hm', hmm⟩
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLX).symm m, (Subgroup.subgroupOfEquivOfLe hLX).symm m', ?_, ?_, ?_⟩
    · apply (pQuotSubgroupOfIso X hLX).injective
      rw [pQuotSubgroupOfIso_mk, MulEquiv.apply_symm_apply]
      exact hm.trans (by rfl)
    · apply (pQuotSubgroupOfIso X hLX).injective
      rw [pQuotSubgroupOfIso_mk, MulEquiv.apply_symm_apply]
      exact hm'.trans (by rfl)
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hmm
  · rintro ⟨n, n', hn, hn', hnn⟩
    refine ⟨Subgroup.subgroupOfEquivOfLe hLX n, Subgroup.subgroupOfEquivOfLe hLX n', ?_, ?_, ?_⟩
    · rw [← pQuotSubgroupOfIso_mk, hn]
    · rw [← pQuotSubgroupOfIso_mk, hn']
    · have := congrArg Subtype.val hnn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this

theorem innDiagOn_subgroupOf_iff {G : Type} [Group G] [Finite G] (X : Subgroup G) {p : ℕ} {A L : Subgroup G}
    (hAX : A ≤ X) (hLX : L ≤ X) :
    InnDiagOn p (A.subgroupOf X) (L.subgroupOf X) ↔ InnDiagOn p A L := by
  have hi := X.subtype_injective
  unfold InnDiagOn
  refine and_congr ?_ ?_
  · constructor
    · intro h a ha
      have hmem : (⟨a, hAX ha⟩ : ↥X) ∈ A.subgroupOf X := Subgroup.mem_subgroupOf.2 ha
      have h2 := (S267.mem_normalizer_map_iff_inj X.subtype hi).2 (h hmem)
      rw [Subgroup.map_subgroupOf_eq_of_le hLX] at h2
      exact h2
    · intro h a' ha'
      apply (S267.mem_normalizer_map_iff_inj X.subtype hi).1
      rw [Subgroup.map_subgroupOf_eq_of_le hLX]
      exact h (Subgroup.mem_subgroupOf.1 ha')
  · refine gla_marking_of_equiv (pQuotSubgroupOfIso X hLX) ?_ ?_
    · rintro lab R _ I F θ hθ a' ha'
      obtain ⟨φ, hφ, hind⟩ := hθ (a' : G) (Subgroup.mem_subgroupOf.1 ha')
      exact ⟨φ, hφ, (largeEvenInduces_transfer (pQuotSubgroupOfIso X hLX) θ φ _ _
        (fun q q' => indRel_subgroupOf_iff X hLX a' q q')).1 hind⟩
    · rintro lab R _ I F θ hθ a ha
      obtain ⟨φ, hφ, hind⟩ := hθ ⟨a, hAX ha⟩ (Subgroup.mem_subgroupOf.2 ha)
      refine ⟨φ, hφ, (largeEvenInduces_transfer (pQuotSubgroupOfIso X hLX).symm θ φ _ _ ?_).1 hind⟩
      intro q q'
      have := indRel_subgroupOf_iff X hLX ⟨a, hAX ha⟩ ((pQuotSubgroupOfIso X hLX).symm q)
        ((pQuotSubgroupOfIso X hLX).symm q')
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      exact this.symm

end InnDiag

end Marking

end Std

end CFSG.LocalAnalysis.GLTheoremA.T171

end
