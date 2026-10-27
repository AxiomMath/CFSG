module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10

section Glue

variable {G : Type} [Group G] {p : ℕ} {L : Subgroup G}

theorem indRel_total {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (q : PQuot p L) :
    ∃ q', indRel p L g q q' := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hg' : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hg
  refine ⟨QuotientGroup.mk ⟨g⁻¹ * l * g, ?_⟩, l, ⟨g⁻¹ * l * g, ?_⟩, rfl, rfl, rfl⟩
  · have := (Subgroup.mem_normalizer_iff.1 hg' l).1 l.2
    simpa using this
  · have := (Subgroup.mem_normalizer_iff.1 hg' l).1 l.2
    simpa using this

@[expose] noncomputable def indAut (p : ℕ) (L : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : MulAut (PSimple p L) :=
  chevAut p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩

theorem indAut_apply_mk {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {q q' : PQuot p L}
    (h : indRel p L g q q') :
    indAut p L g hg (QuotientGroup.mk q) = QuotientGroup.mk q' := by
  obtain ⟨l, l', rfl, rfl, hll'⟩ := h
  have := chevAut_chevQuotHom p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ l
  have e : L.normalizerMonoidHom ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ l = l' := by
    apply Subtype.ext
    simp [hll']
  rw [e] at this
  exact this

theorem induces_indRel_iff {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {R : Type}
    [Group R] (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R) {φ : MulAut R} :
    LargeEvenInduces θ (indRel p L g) φ ↔ φ = MulAut.congr θ (indAut p L g hg) := by
  have key : LargeEvenInduces θ (indRel p L g) (MulAut.congr θ (indAut p L g hg)) := by
    intro q q' h
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, indAut_apply_mk hg h]
  refine ⟨fun h => ?_, fun h => h ▸ key⟩
  ext r
  obtain ⟨x, rfl⟩ := θ.surjective r
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q', hq'⟩ := indRel_total hg q
  rw [h q q' hq', key q q' hq']

theorem indAut_mem_inner_iff [Finite G] (hp : p.Prime) {X : Subgroup G} (hL : GLAPComponent p X L)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L g hg ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) ↔ InducesInnerMod p L g := by
  rw [← chevAut_mem_inner_iff hp hL hg]
  have : indAut p L g hg = (chevAut p L ⟨g, hg⟩)⁻¹ := by
    rw [indAut, ← map_inv]
    rfl
  rw [this]
  exact inv_mem_iff

end Glue

section Clauses


variable {G : Type} [Group G] [Finite G] {p : ℕ}

@[expose] def RawInnBody (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  (∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) ∧ (∀ φ ∈ I, φ⁻¹ ∈ I) ∧ (∀ r : R, MulAut.conj r ∈ I) ∧
    ∀ f ∈ F, orderOf f = p → f ∉ I

theorem canonRawInn' (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (LargeEvenSimpleGuard (RawInnBody p)) :=
  canonRawInn hp hp2 hlab

theorem innDiag_unif_holds {L A : Subgroup G} (hA : A ≤ Subgroup.normalizer (L : Set G))
    (h : ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L) : InnDiagOn p A L := by
  refine ⟨hA, ?_⟩
  have h1 : ∀ a ∈ (A : Set G), CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L a) φ := fun a ha =>
    Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh a (Subgroup.mem_zpowers a)) (h a ha).2
  have h0 : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun _ _ _ _ _ _ => True :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) (h 1 A.one_mem).2
  have := marking_transport_family (fun (a : G) => indRel p L a) (A : Set G) (Set.toFinite _) h1 h0
  exact Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨_, hall⟩ => hall) this

theorem inner_innDiag_holds (hp : p.Prime) {X L : Subgroup G} {g : G} (hL : GLAPComponent p X L)
    (hchev : IsChevSimple 2 (PSimple p L)) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hin : InducesInnerMod p L g) : InnDiagOn p (Subgroup.zpowers g) L := by
  refine ⟨Subgroup.zpowers_le.2 hg, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have h0 := CFSG.StandardType.ChevTwo.ys08_holds (PQuot p L) hq hchev
  have h1 := canon_marking_and_labelAll_simple (P' := RawInnBody 3)
    (fun lab hlab => canonRawInn' Nat.prime_three (by norm_num) hlab) h0
  refine Canonical.largeEvenMarking_mono ?_ h1
  rintro lab R _ I F θ ⟨-, -, -, hinn, -⟩ a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hak : g ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hg k
  have hmem : indAut p L (g ^ k) hak ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) := by
    have e : indAut p L (g ^ k) hak = (indAut p L g hg) ^ k := by
      unfold indAut
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simp [zpow_neg, inv_zpow])
    rw [e]
    exact Subgroup.zpow_mem _ ((indAut_mem_inner_iff hp hL hg).2 hin) k
  obtain ⟨s, hs⟩ := hmem
  refine ⟨MulAut.congr θ (indAut p L (g ^ k) hak), ?_, (induces_indRel_iff hak θ).2 rfl⟩
  rw [← hs, congr_conj]
  exact hinn _

theorem field_nonInnDiag_holds (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hF : FieldOn p g L) : NonInnDiag p g L := by
  refine ⟨hF.1, fun hD => ?_⟩
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L g) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh g (Subgroup.mem_zpowers g)) hD.2
  have h1 := marking_transport (indRel p L g) hdiag hF.2
  have h2 := canon_marking_and_labelAll_simple (P' := RawInnBody p)
    (fun lab hlab => canonRawInn' hp hp2 hlab) h1
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨hlt, f, hf, u, hu, hord, hind⟩, φ, hφ, hind'⟩,
    hmul, hinv, hinn, hfI⟩ := Canonical.largeEvenMarking_exists h2
  have e1 := (induces_indRel_iff hF.1 θ).1 hind
  have e2 := (induces_indRel_iff hF.1 θ).1 hind'
  have e3 : φ = u * f * u⁻¹ := e2.trans e1.symm
  have hfI' : f ∈ I := by
    have : f = u⁻¹ * φ * u := by rw [e3]; group
    rw [this]
    exact hmul (u⁻¹ * φ) (hmul u⁻¹ (hinv u hu) φ hφ) u hu
  exact hfI f hf hord hfI'

end Clauses

end MI

end CFSG.LocalAnalysis.GLTheoremA
