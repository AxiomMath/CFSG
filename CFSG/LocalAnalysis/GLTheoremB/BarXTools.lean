module

public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (C : Subgroup G) : IsElemAbelian p (E.subgroupOf C) := CFSG.Open.IsElemAbelian.subgroupOf hE C

theorem injective_barX_comp {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E)
    (hEC : E ≤ C) :
    Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp
      (E.subgroupOf C).subtype) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p (E.subgroupOf C) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (E.subgroupOf C)) (Nat.card (GLAPPrimeCore p ↥C)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card))
  have hdisj := Subgroup.disjoint_of_coprime_natCard (H := E.subgroupOf C)
    (K := GLAPPrimeCore p ↥C) hcop
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hs
  have h1 : (s : ↥C) ∈ E.subgroupOf C ⊓ GLAPPrimeCore p ↥C := ⟨s.2, hs⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).2 (Subtype.ext h1)

omit [Finite G] in
theorem isElemAbelian_barX {p : ℕ} {C B : Subgroup G} (hB : IsElemAbelian p B) :
    IsElemAbelian p (barX p C B) :=
  CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hB C) _

theorem rank_barX_of_isPGroup {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E)
    (hEC : E ≤ C) : CFSG.Open.pRank p (barX p C E) = CFSG.Open.pRank p E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hE hEC
  have hrange : barX p C E = (⊤ : Subgroup ↥(E.subgroupOf C)).map f := by
    rw [hf, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  rw [hrange, pRank_map_eq_of_injective hp.one_lt f hfi, ← pRank_eq_pRank_top_subtype hp.one_lt,
    ← pRank_map_eq_of_injective hp.one_lt C.subtype C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hEC]

theorem exists_le_barX_eq {p : ℕ} (hp : p.Prime) {C B : Subgroup G} (hB : IsPGroup p B)
    (hBC : B ≤ C) {Q : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hQ : Q ≤ barX p C B) :
    ∃ E : Subgroup G, E ≤ B ∧ barX p C E = Q ∧
      CFSG.Open.pRank p E = CFSG.Open.pRank p Q := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (B.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hB hBC
  have hrange : f.range = barX p C B := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  set E₁ : Subgroup ↥(B.subgroupOf C) := Q.comap f with hE₁
  set E : Subgroup G := (E₁.map (B.subgroupOf C).subtype).map C.subtype with hE
  have hEQ : E₁.map f = Q := by
    rw [hE₁, Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.2 hQ
  have hsub : E.subgroupOf C = E₁.map (B.subgroupOf C).subtype :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  refine ⟨E, ?_, ?_, ?_⟩
  · rintro _ ⟨c, ⟨b, _, rfl⟩, rfl⟩
    exact (Subgroup.mem_subgroupOf).1 b.2
  · show (E.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) = Q
    rw [hsub, Subgroup.map_map]
    exact hEQ
  · rw [hE, pRank_map_eq_of_injective hp.one_lt C.subtype C.subtype_injective,
      pRank_map_eq_of_injective hp.one_lt (B.subgroupOf C).subtype
        (B.subgroupOf C).subtype_injective, ← hEQ,
      pRank_map_eq_of_injective hp.one_lt f hfi]

omit [Finite G] in
theorem normalizer_subgroupOf_eq {C E : Subgroup G} (hEC : E ≤ C) :
    Subgroup.normalizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C) =
      (Subgroup.normalizer (E : Set G)).subgroupOf C := by
  ext c
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have := (h ⟨g, hEC hg⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hg)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hg
      have hgC : g ∈ C := by
        have : (c : G) * g * (c : G)⁻¹ ∈ C := hEC hg
        have := C.mul_mem (C.mul_mem (C.inv_mem c.2) this) c.2
        simpa [mul_assoc] using this
      have := (h ⟨g, hgC⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hg)
      simpa [Subgroup.mem_subgroupOf] using this
  · intro h y
    have := h (y : G)
    simpa [Subgroup.mem_subgroupOf] using this

theorem normalizer_barX_le {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E)
    (hEC : E ≤ C) :
    Subgroup.normalizer ((barX p C E : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
        Set (↥C ⧸ GLAPPrimeCore p ↥C)) ≤
      barX p C (Subgroup.normalizer (E : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p (E.subgroupOf C) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  have h := normalizer_map_quotient_le (GLAPPrimeCore p ↥C)
    ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hEp
  rw [normalizer_subgroupOf_eq hEC] at h
  exact h

theorem le_of_barX_le_glbCore {p : ℕ} (hp : p.Prime) {C B M' L : Subgroup G} (k : ℕ)
    (hB : IsPGroup p B) (hBC : B ≤ C) (hLC : L ≤ C)
    (hnorm : ∀ E : Subgroup G, E ≤ B → k ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M')
    (hcore : GLAPPrimeCoreOf p C ≤ M')
    (hL : barX p C L ≤ GLBCore p k (barX p C B)) : L ≤ M' := by
  have hgen : GLBCore p k (barX p C B) ≤ barX p C M' := by
    refine sSup_le ?_
    rintro _ ⟨Q, hQB, hQk, rfl⟩
    obtain ⟨E, hEB, hEQ, hEr⟩ := exists_le_barX_eq hp hB hBC hQB
    have hEp : IsPGroup p E := hB.to_le hEB
    have hEC : E ≤ C := hEB.trans hBC
    rw [← hEQ]
    refine (normalizer_barX_le hp hEp hEC).trans ?_
    refine Subgroup.map_mono (fun y hy => ?_)
    exact (Subgroup.mem_subgroupOf).2 (hnorm E hEB (by rw [hEr]; exact hQk)
      ((Subgroup.mem_subgroupOf).1 hy))
  intro x hx
  have hxC : x ∈ C := hLC hx
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨x, hxC⟩ ∈ barX p C L :=
    ⟨⟨x, hxC⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hgen (hL hmem)
  have hyM : (y : G) ∈ M' := (Subgroup.mem_subgroupOf).1 hy
  have hker : y⁻¹ * ⟨x, hxC⟩ ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hyx
  have hker' : ((y⁻¹ * ⟨x, hxC⟩ : ↥C) : G) ∈ GLAPPrimeCoreOf p C := ⟨_, hker, rfl⟩
  have := M'.mul_mem hyM (hcore hker')
  simpa using this

omit [Finite G] in
theorem barMap_surjective {p : ℕ} {C L : Subgroup G} (hLC : L ≤ C) :
    Function.Surjective (barMap p hLC) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨(c : G), (Subgroup.mem_subgroupOf).1 hc⟩, Subtype.ext rfl⟩

theorem ker_barMap_eq {p : ℕ} (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hsn : IsSubnormal L C) : (barMap p hLC).ker = GLAPPrimeCore p ↥L := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (Subgroup.inclusion hLC l) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    set K : Subgroup ↥L := (GLAPPrimeCoreOf p C).subgroupOf L with hK
    have hnorm : K.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf p C (hLC g.2)) (n : G)).1 ((Subgroup.mem_subgroupOf).1 hn)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using h2)
    have hcop : Nat.Coprime p (Nat.card K) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_
      refine not_dvd_card_glaPPrimeCoreOf hp C (hdvd.trans ?_)
      have hc : Nat.card (K.map L.subtype) = Nat.card K :=
        Subgroup.card_map_of_injective L.subtype_injective
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hk
    have hKle : K ≤ GLAPPrimeCore p ↥L := le_sSup ⟨hnorm, hcop⟩
    exact hKle ((Subgroup.mem_subgroupOf).2 ⟨_, h1, rfl⟩)
  · intro hl
    have h1 : (l : G) ∈ GLAPPrimeCoreOf p L := ⟨l, hl, rfl⟩
    obtain ⟨c, hc, hcl⟩ := glaPPrimeCoreOf_le_of_isSubnormal hp hsn h1
    have hcl' : Subgroup.inclusion hLC l = c := Subtype.ext hcl.symm
    refine Subtype.ext ?_
    change QuotientGroup.mk' (GLAPPrimeCore p ↥C) (Subgroup.inclusion hLC l) = 1
    rw [hcl', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc

@[expose] noncomputable def quotEquivBarX {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hLC : L ≤ C) (hsn : IsSubnormal L C) :
    (↥L ⧸ GLAPPrimeCore p ↥L) ≃* ↥(barX p C L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barMap_eq hp hLC hsn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (barMap p hLC) (barMap_surjective hLC))

theorem isPiGroup_barX {p : ℕ} (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hsn : IsSubnormal L C) (h : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) :
    IsPiGroup p ↥(barX p C L) :=
  IsPiGroup.of_mulEquiv (quotEquivBarX hp hLC hsn) h

omit [Finite G] in
theorem IsHatSeven.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsHatSeven X) : IsHatSeven Y := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

omit [Finite G] in
theorem le_normalizer_alphaOf (p : ℕ) (M : Subgroup G) :
    M ≤ Subgroup.normalizer (alphaOf p M : Set G) := by
  have key : ∀ g ∈ M, GLBConj g (alphaOf p M) ≤ alphaOf p M := by
    intro g hg
    have hgn : g ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hg
    have hM : GLBConj g M = M := mem_normalizer_iff_gLBConj_eq.1 hgn
    unfold alphaOf
    simp only [GLBConj, Subgroup.map_sup, Subgroup.map_iSup]
    refine sup_le_sup ?_ ?_
    · have := (le_normalizer_pCoreOf 2 M hg)
      exact (mem_normalizer_iff_gLBConj_eq.1 this).le
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨hp3, hJM, hsn, hperf, hhat⟩ := hJ
      refine le_iSup₂_of_le (GLBConj g J) ⟨hp3, ?_, ?_, ?_, ?_⟩ le_rfl
      · calc GLBConj g J ≤ GLBConj g M := Subgroup.map_mono hJM
          _ = M := hM
      · have := isSubnormal_gLBConj hsn g
        rwa [hM] at this
      · have h1 := Subgroup.map_commutator (H₁ := J) (H₂ := J) (MulAut.conj g⁻¹).toMonoidHom
        change GLBConj g ⁅J, J⁆ = ⁅GLBConj g J, GLBConj g J⁆ at h1
        rw [← h1, hperf]
      · have hpc : (CFSG.pCore 2 ↥J).map (conjEquiv g J).toMonoidHom =
            CFSG.pCore 2 ↥(GLBConj g J) := by
          exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g J)
        exact IsHatSeven.of_mulEquiv (QuotientGroup.congr _ _ (conjEquiv g J) hpc) hhat
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g hg) ?_
  have h2 := gLBConj_mono g (key g⁻¹ (inv_mem hg))
  rwa [gLBConj_gLBConj_inv] at h2

end CFSG.LocalAnalysis.GLTheoremB
