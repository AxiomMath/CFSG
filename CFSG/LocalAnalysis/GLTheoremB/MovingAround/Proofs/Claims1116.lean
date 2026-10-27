module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Facts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Alt
public import CFSG.LocalAnalysis.GL83PartI.I_22_5
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Bar
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Omega

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design

@[expose] def Exc5 (S : Type) [Group S] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    (idx.1 = TauCeti.LieTypeIndex.tits ∨ idx.1 = TauCeti.LieTypeIndex.suzuki 2 ∨
      idx.1 = TauCeti.LieTypeIndex.reeF4 2) ∧
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def Input23_11Gen : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) (⨆ x ∈ E ⊓ A, GLBConj x K) ≤
        ⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1),
          (barX p (Cg a) (GLAPPrimeCoreOf p (Cg2 e a)) ⊔
            ⨆ (J : Subgroup G) (_ : GLAPComponent p (Cg2 e a) J ∧
                J ≤ (⨆ x ∈ E ⊓ A, GLBConj x K) ∧
                IsChevSimple q (barOf p J ⧸ Subgroup.center (barOf p J))),
              barX p (Cg a) J)

section Helpers

variable {G : Type} [Group G] [Finite G]

noncomputable def centerQuotEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)

theorem isChevSimple_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {r : ℕ}
    (h : IsChevSimple r S) : IsChevSimple r S' := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem exc5_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : Exc5 S) : Exc5 S' := by
  obtain ⟨idx, hidx, ⟨f⟩⟩ := h
  exact ⟨idx, hidx, ⟨e.symm.trans f⟩⟩

theorem isSporType_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {s : TauCeti.SporadicName}
    (h : IsSporType s S) : IsSporType s S' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

omit [Finite G] in
theorem bar_mono {p : ℕ} {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F :=
  ⟨⟨⟨fun x y => Subtype.ext (hE.comm (hFE x.2) (hFE y.2))⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

omit [Finite G] in
theorem le_cg_of_elemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x : G} (hx : x ∈ E) :
    E ≤ Cg x := fun y hy => Subgroup.mem_centralizer_iff.2 fun g hg => by
  rw [Set.mem_singleton_iff.1 hg]
  exact hE.comm hx hy

omit [Finite G] in
theorem cg2_le_left (e a : G) : Cg2 e a ≤ Cg e :=
  Subgroup.centralizer_le (by intro x hx; simp at hx ⊢; exact Or.inl hx)

omit [Finite G] in
theorem le_kx (p : ℕ) (J : Subgroup G) (x : G) : J ≤ Kx p J x :=
  le_iSup₂_of_le (1 : G) (GLAPLayer p (Cg x)).one_mem (le_of_eq (gLBConj_one J).symm)

theorem le_of_bar_le {p : ℕ} {X L M : Subgroup G} (hLX : L ≤ X) (hO : GLAPPrimeCoreOf p X ≤ M)
    (h : barX p X L ≤ barX p X M) : L ≤ M := by
  intro k hk
  obtain ⟨j, hj, hjk⟩ := exists_of_barX_le h hk (hLX hk)
  have := M.mul_mem hj (hO hjk)
  simpa using this

omit [Finite G] in
theorem barX_iSup₂_le {p : ℕ} {X : Subgroup G} {ι : Type*} {P : ι → Prop} {H : ι → Subgroup G}
    {T : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hHX : ∀ i, P i → H i ≤ X)
    (hT : ∀ i, P i → barX p X (H i) ≤ T) : barX p X (⨆ i, ⨆ (_ : P i), H i) ≤ T := by
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype with hT'
  have hle : (⨆ i, ⨆ (_ : P i), H i) ≤ T' := by
    refine iSup₂_le fun i hi => fun h hh => ?_
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨h, hHX i hi hh⟩ ∈ T :=
      hT i hi ⟨⟨h, hHX i hi hh⟩, (Subgroup.mem_subgroupOf).2 hh, rfl⟩
    exact ⟨⟨h, hHX i hi hh⟩, hmem, rfl⟩
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨t, ht, htk⟩ := hle ((Subgroup.mem_subgroupOf).1 hk)
  have : t = k := Subtype.ext htk
  rw [← this]
  exact ht

theorem card_eq_pow_pRank' {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (elemAbelian_isPGroup hE).exists_card_eq
  have h1 : m ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hm
  have h2 : CFSG.Open.pRank p E ≤ m :=
    CFSG.SectionRank.pRank_le hp.one_lt fun F hFE _ => hm ▸ Subgroup.card_le_of_le hFE
  rw [hm, le_antisymm h1 h2]

theorem card_barX_of_isPGroup {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hE : IsPGroup p E)
    (hEX : E ≤ X) : Nat.card (barX p X E) = Nat.card E := by
  have hfi := injective_barX_comp hp hE hEX
  have hrange : barX p X E =
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (E.subgroupOf X).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv]

theorem bar_le_gamma_of_gen {p : ℕ} (hp : p.Prime) {X J E : Subgroup G} (hJ : GLAPComponent p X J)
    (hEX : E ≤ X) (hEel : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hgen : barX p X J ≤ ⨆ (F : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))
        (_ : F ≤ barX p X E ⊓ Subgroup.normalizer (barX p X J : Set (↥X ⧸ GLAPPrimeCore p ↥X)) ∧
          Nat.card ↥(barX p X E ⊓ Subgroup.normalizer (barX p X J : Set (↥X ⧸ GLAPPrimeCore p ↥X))) ≤
            p * Nat.card F),
        barX p X J ⊓ Subgroup.centralizer (F : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    barX p X J ≤ GLBCore p 2 (barX p X E) := by
  have hc : CFSG.HardMathSupport.Solomon.Coordinator.I224Ctx p (barX p X E) (barX p X J) :=
    { prime := hp
      elem := isElemAbelian_barX hEel
      quasi := hJ.2.2.1.2.2
      dist := fun g _ g' _ hne =>
        CFSG.HardMathSupport.Solomon.Coordinator.i224_comm_cj hJ.2.2.1 g g' hne
      gen := hgen }
  have hom := CFSG.HardMathSupport.Solomon.Coordinator.i224_omega hc
  have hJK : barX p X J ≤
      CFSG.HardMathSupport.Solomon.Coordinator.i224K (barX p X E) (barX p X J) := by
    refine le_iSup₂_of_le (1 : ↥X ⧸ GLAPPrimeCore p ↥X) (Subgroup.one_mem _) ?_
    intro x hx
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_i224Cj]
    simpa using hx
  have hEbcard : Nat.card (barX p X E) = Nat.card E :=
    card_barX_of_isPGroup hp (elemAbelian_isPGroup hEel) hEX
  refine hJK.trans (hom.trans (iSup₂_le fun E' hE' => ?_))
  obtain ⟨hE'B, hcard⟩ := hE'
  have hE'el : IsElemAbelian p E' := isElemAbelian_of_le (isElemAbelian_barX hEel) hE'B
  have h2 : 2 ≤ CFSG.Open.pRank p E' := by
    have h1 : p ^ 3 ≤ p * Nat.card E' := by rw [← hEbcard] at hE3; exact hE3.trans hcard
    rw [card_eq_pow_pRank' hp hE'el, ← pow_succ'] at h1
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  refine (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans ?_
  exact (le_sSup ⟨E', hE'B, h2, rfl⟩ :
    Subgroup.normalizer (E' : Set (↥X ⧸ GLAPPrimeCore p ↥X)) ≤ GLBCore p 2 (barX p X E))

end Helpers

theorem prop1116_prep_of_inputs (hGen : Input23_11Gen) (hI18 : Prop115.Input18_3Gen)
    (h112 : Prop112Statement) : Prop1116PrepStatement := by
  intro G _ _ m p B M E A a K q C
  have hp : p.Prime := C.standing.prime
  have hp2 : p ≠ 2 := C.standing.ne_two
  have h111 : Prop111Statement := prop111_of_prop112 h112
  have hAel : IsElemAbelian p A := sec11_isElemAbelian_A C.toSec11
  have ha : a ∈ A := C.ha.1
  have hA0C : E ⊓ A ≤ Cg a := inf_le_right.trans (le_cg_of_elemAbelian hAel ha)
  have hA0el : IsElemAbelian p (E ⊓ A) := isElemAbelian_of_le hAel inf_le_right
  have hA0r : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := C.pair.1.2.2
  have hgen := hGen hp hp2 C.hq.1 C.hq.2.1 C.hq.2.2 C.hK C.hchev hA0C hA0el hA0r C.notIii
  by_contra hno
  apply C.notM
  have hKstar : barX p (Cg a) (⨆ x ∈ E ⊓ A, GLBConj x K) ≤ barX p (Cg a) M := by
    refine hgen.trans (iSup_le fun e => iSup_le fun he => iSup_le fun he1 => sup_le ?_ ?_)
    · rcases h112 C.toSec11 ha C.ha.2 he he1 with h | h
      · exact bar_mono h
      · exact absurd h C.notD
    · refine iSup_le fun J => iSup_le fun hJ => ?_
      obtain ⟨hJc, hJK, hJq⟩ := hJ
      by_contra hJM
      have hJM' : ¬ J ≤ M := fun h => hJM (bar_mono h)
      obtain ⟨J1, hJ1, hJstar⟩ := exists_J1_of_input18_3 hI18 C.toSec11 ha C.ha.2 he he1 hJc
      have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
      have hO : GLAPPrimeCoreOf p (Cg e) ≤ M := h111 C.toSec11 heA he1
      have hJCe : J ≤ Cg e := hJc.1.trans (cg2_le_left e a)
      have hcov : ¬ Covers p (Cg e) (M ⊓ Cg e) (Kx p J e) := by
        intro hc
        apply hJM'
        exact (le_kx p J e).trans
          (le_of_bar_le (kx_le_cg hJCe) hO (hc.trans (bar_mono inf_le_left)))
      exact hno ⟨e, J, J1,
        { toCex1116 := C, he := ⟨he, he1⟩, hJ0 := hJc, hJ0K := hJK, hJ0M := hJM', hJ0chev := hJq,
          hJ1 := hJ1, hJstar := hJstar, hcov := hcov }⟩
  have hKK : K ≤ ⨆ x ∈ E ⊓ A, GLBConj x K :=
    le_iSup₂_of_le (1 : G) (E ⊓ A).one_mem (le_of_eq (gLBConj_one K).symm)
  exact le_of_bar_le C.hK.1 (h111 C.toSec11 ha C.ha.2) ((bar_mono hKK).trans hKstar)

@[expose] def Input14_4_ChevDown : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {e a : G} {J0 J1 : Subgroup G},
    a * e = e * a → a ^ p = 1 → GLAPComponent p (Cg e) J1 →
    GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0 →
    Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 →
    ∀ r : ℕ, IsChevSimple r (barOf p J1 ⧸ Subgroup.center (barOf p J1)) →
      IsChevSimple r (barOf p J0 ⧸ Subgroup.center (barOf p J0))

@[expose] def Input3_3_OddChar : Prop :=
  ∀ (S : Type) [Group S] (q r : ℕ), IsChevSimple q S → IsChevSimple r S → q ≠ r → q = 2 ∨ r = 2

@[expose] def Input3_3_Exc5 : Prop :=
  ∀ (S : Type) [Group S], Exc5 S → ∀ q : ℕ, q ≠ 2 → ¬ IsChevSimple q S

@[expose] def Input23_10 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p r : ℕ}, p.Prime → p ≠ 2 → r ≠ p →
    ∀ {X J E : Subgroup G}, GLAPComponent p X J → E ≤ X → IsElemAbelian p E → Nat.card E ≤ p ^ 3 →
      IsChevSimple r (barOf p J ⧸ Subgroup.center (barOf p J)) →
      ¬ (r = 2 ∧ (p = 3 ∨ (p = 5 ∧ Exc5 (barOf p J ⧸ Subgroup.center (barOf p J))))) →
      barX p X J ≤ ⨆ (F : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))
        (_ : F ≤ barX p X E ⊓ Subgroup.normalizer (barX p X J : Set (↥X ⧸ GLAPPrimeCore p ↥X)) ∧
          Nat.card ↥(barX p X E ⊓ Subgroup.normalizer (barX p X J : Set (↥X ⧸ GLAPPrimeCore p ↥X))) ≤
            p * Nat.card F),
        barX p X J ⊓ Subgroup.centralizer (F : Set (↥X ⧸ GLAPPrimeCore p ↥X))

@[expose] def Input14_9_10Down : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {e a : G} {J0 J1 : Subgroup G},
    a * e = e * a → a ^ 5 = 1 → GLAPComponent 5 (Cg e) J1 →
    GLAPComponent 5 (GLAPLayer 5 (Kx 5 J0 e ⊓ Cg a)) J0 →
    Kx 5 J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 →
    Exc5 (barOf 5 J1 ⧸ Subgroup.center (barOf 5 J1)) →
    Exc5 (barOf 5 J0 ⧸ Subgroup.center (barOf 5 J0))

section PrepData

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
  {e : G} {J0 J1 : Subgroup G}

theorem prep_hea (P : Prep1116 G m p B M E A a K q e J0 J1) : a * e = e * a :=
  (sec11_isElemAbelian_A P.toSec11).comm P.ha.1 (Subgroup.mem_inf.1 P.he.1).2

theorem prep_hap (P : Prep1116 G m p B M E A a K q e J0 J1) : a ^ p = 1 :=
  (sec11_isElemAbelian_A P.toSec11).2 a P.ha.1

theorem prep_hEC (P : Prep1116 G m p B M E A a K q e J0 J1) : E ≤ Cg e :=
  le_cg_of_elemAbelian (sec11_isElemAbelian_E P.toSec11) (Subgroup.mem_inf.1 P.he.1).1

theorem prep_hAC (P : Prep1116 G m p B M E A a K q e J0 J1) : A ≤ Cg e :=
  le_cg_of_elemAbelian (sec11_isElemAbelian_A P.toSec11) (Subgroup.mem_inf.1 P.he.1).2

theorem prep_hE3 (P : Prep1116 G m p B M E A a K q e J0 J1) : 3 ≤ CFSG.Open.pRank p E :=
  P.pair.1.1.1.2

theorem prep_cardE (P : Prep1116 G m p B M E A a K q e J0 J1) : p ^ 3 ≤ Nat.card E := by
  rw [card_eq_pow_pRank' P.hp (sec11_isElemAbelian_E P.toSec11)]
  exact Nat.pow_le_pow_right P.hp.pos (prep_hE3 P)

theorem prep_conj_comp (P : Prep1116 G m p B M E A a K q e J0 J1) {g : G}
    (hg : g ∈ Subgroup.zpowers a) : GLAPComponent p (Cg e) (GLBConj g J1) := by
  have hgA : g ∈ A := (Subgroup.zpowers_le.mpr P.ha.1) hg
  have hgcomm : g * e = e * g :=
    (sec11_isElemAbelian_A P.toSec11).comm hgA (Subgroup.mem_inf.1 P.he.1).2
  have := glaPComponent_gLBConj P.hJ1 g
  rwa [gLBConj_cg_eq hgcomm] at this

theorem prep_not_all_le_gamma (P : Prep1116 G m p B M E A a K q e J0 J1)
    (h : ∀ g ∈ Subgroup.zpowers a, barX p (Cg e) (GLBConj g J1) ≤ GLBCore p 2 (barX p (Cg e) E)) :
    False := by
  apply P.hgamma
  rw [P.hJstar]
  exact barX_iSup₂_le (fun g hg => (prep_conj_comp P hg).1) h

end PrepData

theorem prop1116_chevr_of_inputs (hDown : Input14_4_ChevDown) (hPair : Input3_3_OddChar)
    (hExc : Input3_3_Exc5) (hSeitz : Input23_10) (hDown5 : Input14_9_10Down) :
    Prop1116ChevrStatement := by
  intro G _ _ m p B M E A a K q e J0 J1 P hchev2 r hr
  have hp : p.Prime := P.hp
  have hp2 : p ≠ 2 := P.standing.ne_two
  have hJ0r : IsChevSimple r (barOf p J0 ⧸ Subgroup.center (barOf p J0)) :=
    hDown hp hp2 (prep_hea P) (prep_hap P) P.hJ1 P.hJ0' P.hJstar r hr
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₃, hE₃E, hE₃el, hE₃card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 3) (prep_hE3 P)
  have hE₃C : E₃ ≤ Cg e := hE₃E.trans (prep_hEC P)
  have hmono : GLBCore p 2 (barX p (Cg e) E₃) ≤ GLBCore p 2 (barX p (Cg e) E) := by
    unfold GLBCore
    apply sSup_le_sSup
    rintro N ⟨Q, hQP, hk, hN⟩
    exact ⟨Q, hQP.trans (bar_mono hE₃E), hk, hN⟩
  have hseitz : r ≠ p →
      ¬ (r = 2 ∧ (p = 3 ∨ (p = 5 ∧ Exc5 (barOf p J1 ⧸ Subgroup.center (barOf p J1))))) → False := by
    intro hrp hne
    refine prep_not_all_le_gamma P fun g hg => ?_
    have eq : (barOf p J1 ⧸ Subgroup.center (barOf p J1)) ≃*
        (barOf p (GLBConj g J1) ⧸ Subgroup.center (barOf p (GLBConj g J1))) :=
      centerQuotEquiv (conjQuotEquiv p g J1)
    refine le_trans ?_ hmono
    refine bar_le_gamma_of_gen hp (prep_conj_comp P hg) hE₃C hE₃el hE₃card.ge ?_
    refine hSeitz hp hp2 hrp (prep_conj_comp P hg) hE₃C hE₃el hE₃card.le (isChevSimple_congr eq hr) ?_
    rintro ⟨h2, h3 | ⟨h5, hx⟩⟩
    · exact hne ⟨h2, Or.inl h3⟩
    · exact hne ⟨h2, Or.inr ⟨h5, exc5_congr eq.symm hx⟩⟩
  by_cases hrp : r = p
  ·
    rcases hPair _ q p P.hJ0chev (hrp ▸ hJ0r) P.hq.2.2 with h | h
    · exact P.hq.2.1 h
    · exact hp2 h
  by_cases hr2 : r = 2
  ·
    have hq3 : q = 3 := hchev2 (hr2 ▸ hJ0r)
    have hp3 : p ≠ 3 := fun h => P.hq.2.2 (hq3.trans h.symm)
    by_cases hexc : p = 5 ∧ Exc5 (barOf p J1 ⧸ Subgroup.center (barOf p J1))
    · obtain ⟨hp5, hx⟩ := hexc
      subst hp5
      exact hExc _ (hDown5 (prep_hea P) (prep_hap P) P.hJ1 P.hJ0' P.hJstar hx) q P.hq.2.1 P.hJ0chev
    · exact hseitz hrp fun ⟨_, h⟩ => h.elim hp3 hexc
  · exact hseitz hrp fun ⟨h, _⟩ => hr2 h

@[expose] def Input14_13Spor : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {e a : G} {J0 J1 : Subgroup G},
    a * e = e * a → a ^ p = 1 → GLAPComponent p (Cg e) J1 →
    GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0 →
    Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 →
    ∀ s : TauCeti.SporadicName, IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1)) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      IsChevSimple q (barOf p J0 ⧸ Subgroup.center (barOf p J0)) →
      GLBConj a J1 = J1 ∧
        ((p = 3 ∧ (s = .M23 ∨ s = .HS) ∧
            IsLpType 2 5 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 3 ∧ (s = .M24 ∨ s = .He) ∧
            IsLpType 2 7 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 5 ∧ s = .Suz ∧ IsLpType 2 9 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 13 ∧ s = .M ∧ IsLpType 3 3 (barOf p J0 ⧸ Subgroup.center (barOf p J0))))

@[expose] def InputSporAutRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ) (s : TauCeti.SporadicName),
    ((p = 3 ∧ (s = .M23 ∨ s = .HS ∨ s = .M24 ∨ s = .He)) ∨ (p = 5 ∧ s = .Suz) ∨ (p = 13 ∧ s = .M)) →
    CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ → IsSporType s (Y ⧸ Subgroup.center Y) →
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2

@[expose] def InputSuzFive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 5 Y = ⊥ →
    IsSporType .Suz (Y ⧸ Subgroup.center Y) →
    Subgroup.center Y = ⊥ ∧
      ∀ P : Subgroup (MulAut Y), IsPGroup 5 P → Nat.card P ≤ 25 ∧ P ≤ innerAut Y

@[expose] def Input14_4_1Field : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {a e : G} {K J0 A0 : Subgroup G} {q : ℕ},
    GLAPComponent 13 (Cg a) K → q.Prime → q ≠ 2 → q ≠ 13 →
    IsChevSimple q (barOf 13 K ⧸ Subgroup.center (barOf 13 K)) →
    A0 ≤ Cg a → IsElemAbelian 13 A0 → e ∈ A0 → e ≠ 1 →
    GLAPComponent 13 (Cg2 e a) J0 → J0 ≤ ⨆ x ∈ A0, GLBConj x K →
    IsLpType 3 3 (barOf 13 J0 ⧸ Subgroup.center (barOf 13 J0)) →
    IsLpType 3 (3 ^ 13) (barOf 13 K) ∨ IsLieOverField 3 (barOf 13 K)

section SporHelpers

variable {G : Type} [Group G] [Finite G]

theorem barX_isQuasisimple {p : ℕ} {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    CFSG.Open.IsQuasisimple ↥(barX p X J) := hJ.2.2.1.2.2

theorem barX_core_eq_bot {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    GLAPPrimeCore p ↥(barX p X J) = ⊥ := by
  have h1 : GLAPPrimeCore p (barOf p J) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  rw [← glaPPrimeCore_map_iso p (quotEquivBarX hp hJ.1 hJ.2.1), h1, Subgroup.map_bot]

noncomputable def barX_centerQuotEquiv {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) :
    (barOf p J ⧸ Subgroup.center (barOf p J)) ≃* (↥(barX p X J) ⧸ Subgroup.center ↥(barX p X J)) :=
  centerQuotEquiv (quotEquivBarX hp hJ.1 hJ.2.1)

omit [Finite G] in
theorem bar_mem_normalizer {p : ℕ} {X J : Subgroup G} (hJX : J ≤ X) {g : G} (hgX : g ∈ X)
    (hg : GLBConj g J = J) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ ∈
      Subgroup.normalizer (barX p X J : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  have hfwd : ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun j hj => mem_gLBConj.1 (hg.symm ▸ hj)
  have hbwd : ∀ j ∈ J, g⁻¹ * j * g ∈ J := fun j hj => by
    have : g⁻¹ * j * g ∈ GLBConj g J := mem_gLBConj.2 (by simpa [mul_assoc] using hj)
    rwa [hg] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨g, hgX⟩ * j * ⟨g, hgX⟩⁻¹, (Subgroup.mem_subgroupOf).2 ?_, by simp⟩
    exact hfwd _ ((Subgroup.mem_subgroupOf).1 hj)
  · rintro ⟨j, hj, hjh⟩
    refine ⟨⟨g, hgX⟩⁻¹ * j * ⟨g, hgX⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
    · exact hbwd _ ((Subgroup.mem_subgroupOf).1 hj)
    · rw [map_mul, map_mul, map_inv, hjh]
      group

omit [Finite G] in
theorem isElemAbelian_zpowers {Q : Type*} [Group Q] {p : ℕ} {t : Q} (ht : t ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers t) := by
  rw [Subgroup.zpowers_eq_closure]
  exact IsElemAbelian.closure_of_commute (by simp) (by simpa using ht)

theorem exists_pGroup_map_eq {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ} [Fact p.Prime]
    (φ : A →* B) (hφ : Function.Surjective φ) {Q : Subgroup B} (hQ : IsPGroup p Q)
    {E : Subgroup A} (hE : IsPGroup p E) (hEQ : E.map φ ≤ Q) :
    ∃ P : Subgroup A, E ≤ P ∧ IsPGroup p P ∧ P.map φ = Q := by
  set W := Q.comap φ
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, rfl⟩ := hφ q
    exact ⟨⟨a, hq⟩, rfl⟩
  have hEW : E ≤ W := fun e he => hEQ ⟨e, he, rfl⟩
  obtain ⟨T, hT⟩ := (hE.comap_of_injective W.subtype W.subtype_injective).exists_le_sylow
  have htop : ((T.mapSurjective hψ : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, fun e he => ⟨⟨e, hEW he⟩,
    hT (Subgroup.mem_comap.mpr he : (⟨e, hEW he⟩ : W) ∈ E.comap W.subtype), rfl⟩,
    T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : Q) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

theorem eq_barX_of_isSCp {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hE : IsSCp p ⊤ E) (hEX : E ≤ X)
    {F : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hEF : barX p X E ≤ F) (hF : IsElemAbelian p F) :
    F = barX p X E := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  have hEp : IsPGroup p E := elemAbelian_isPGroup hE.2.1
  obtain ⟨P, hEP, hPp, hPF⟩ := exists_pGroup_map_eq π (QuotientGroup.mk'_surjective _)
    (elemAbelian_isPGroup hF) (hEp.comap_subtype (K := X)) hEF
  have hinj : ∀ x ∈ P, ∀ y ∈ P, π x = π y → x = y := by
    intro x hx y hy hxy
    have hz2 : x * y⁻¹ ∈ GLAPPrimeCore p ↥X := by
      rw [← QuotientGroup.eq_one_iff (N := GLAPPrimeCore p ↥X)]
      have : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact this
    have hz : x * y⁻¹ ∈ P ⊓ GLAPPrimeCore p ↥X := Subgroup.mem_inf.2 ⟨P.mul_mem hx (P.inv_mem hy), hz2⟩
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card P) (Nat.card (GLAPPrimeCore p ↥X)) := by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2
        ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card))
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := P) (K := GLAPPrimeCore p ↥X) hcop
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hz
    exact mul_inv_eq_one.1 hz
  set T : Subgroup G := P.map X.subtype with hT
  have hTel : IsElemAbelian p T := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
      obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
      apply Subtype.ext
      show (x' : G) * y' = y' * x'
      have hxF : π x' ∈ F := hPF ▸ Subgroup.mem_map_of_mem π hx'
      have hyF : π y' ∈ F := hPF ▸ Subgroup.mem_map_of_mem π hy'
      have hc : π (x' * y') = π (y' * x') := by rw [map_mul, map_mul]; exact hF.comm hxF hyF
      have := hinj _ (P.mul_mem hx' hy') _ (P.mul_mem hy' hx') hc
      exact congrArg Subtype.val this
    · obtain ⟨x', hx', rfl⟩ := hx
      have hxF : π x' ∈ F := hPF ▸ Subgroup.mem_map_of_mem π hx'
      have hc : π (x' ^ p) = π 1 := by rw [map_pow, map_one]; exact hF.2 _ hxF
      have := hinj _ (P.pow_mem hx' p) _ P.one_mem hc
      simpa using congrArg Subtype.val this
  have hET : E ≤ T := fun z hz => ⟨⟨z, hEX hz⟩, hEP ((Subgroup.mem_subgroupOf).2 hz), rfl⟩
  have hTE : T = E := hE.2.2 T le_top hTel hET
  refine le_antisymm ?_ hEF
  rw [← hPF]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, (Subgroup.mem_subgroupOf).2 ?_, rfl⟩
  rw [← hTE]
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem centralizes_of_inner {Q : Type*} [Group Q] {J Eb : Subgroup Q} {eb ab : Q}
    (hZ : ∀ c ∈ J, (∀ j ∈ J, c * j = j * c) → c = 1) (hEbel : IsElemAbelian 5 Eb)
    (hEbC : ∀ y ∈ Eb, (∀ j ∈ J, y * j = j * y) → y ∈ Subgroup.zpowers eb)
    (heb : ∀ z, eb * z = z * eb)
    (hmax : ∀ t ∈ J, t ^ 5 = 1 → (∀ y ∈ Eb, y * t = t * y) → t ∈ Eb)
    (hinner : ∀ y ∈ Eb, ∃ t ∈ J, ∀ j ∈ J, y * j * y⁻¹ = t * j * t⁻¹)
    (hab : ∃ x ∈ Eb, ∀ j ∈ J, ab * j * ab⁻¹ = x * j * x⁻¹) :
    ∀ y ∈ Eb, ab * y = y * ab := by
  choose! t htJ ht using hinner
  have hsame : ∀ u ∈ J, ∀ v ∈ J, (∀ j ∈ J, u * j * u⁻¹ = v * j * v⁻¹) → u = v := by
    intro u hu v hv huv
    have hc : v⁻¹ * u = 1 := by
      refine hZ _ (J.mul_mem (J.inv_mem hv) hu) fun j hj => ?_
      calc v⁻¹ * u * j = v⁻¹ * (u * j * u⁻¹) * u := by group
        _ = v⁻¹ * (v * j * v⁻¹) * u := by rw [huv j hj]
        _ = j * (v⁻¹ * u) := by group
    calc u = v * (v⁻¹ * u) := by group
      _ = v := by rw [hc, mul_one]
  have hcomm : ∀ y ∈ Eb, ∀ y' ∈ Eb, t y * t y' = t y' * t y := by
    intro y hy y' hy'
    have key : ∀ {u v : Q}, u ∈ Eb → v ∈ Eb → ∀ j ∈ J,
        (u * v) * j * (u * v)⁻¹ = (t u * t v) * j * (t u * t v)⁻¹ := by
      intro u v hu hv j hj
      have hvj : t v * j * (t v)⁻¹ ∈ J := J.mul_mem (J.mul_mem (htJ v hv) hj) (J.inv_mem (htJ v hv))
      calc (u * v) * j * (u * v)⁻¹ = u * (v * j * v⁻¹) * u⁻¹ := by group
        _ = u * (t v * j * (t v)⁻¹) * u⁻¹ := by rw [ht v hv j hj]
        _ = t u * (t v * j * (t v)⁻¹) * (t u)⁻¹ := ht u hu _ hvj
        _ = (t u * t v) * j * (t u * t v)⁻¹ := by group
    refine hsame _ (J.mul_mem (htJ y hy) (htJ y' hy')) _ (J.mul_mem (htJ y' hy') (htJ y hy)) fun j hj => ?_
    rw [← key hy hy' j hj, ← key hy' hy j hj, hEbel.comm hy hy']
  have hpow : ∀ y ∈ Eb, ∀ n : ℕ, ∀ j ∈ J, y ^ n * j * (y ^ n)⁻¹ = t y ^ n * j * (t y ^ n)⁻¹ := by
    intro y hy n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      have hmem : t y ^ n * j * (t y ^ n)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem (J.pow_mem (htJ y hy) n) hj) (J.inv_mem (J.pow_mem (htJ y hy) n))
      calc y ^ (n + 1) * j * (y ^ (n + 1))⁻¹ = y * (y ^ n * j * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * (t y ^ n * j * (t y ^ n)⁻¹) * y⁻¹ := by rw [ih j hj]
        _ = t y * (t y ^ n * j * (t y ^ n)⁻¹) * (t y)⁻¹ := ht y hy _ hmem
        _ = t y ^ (n + 1) * j * (t y ^ (n + 1))⁻¹ := by group
  have ht5 : ∀ y ∈ Eb, t y ^ 5 = 1 := by
    intro y hy
    refine hsame _ (J.pow_mem (htJ y hy) 5) _ J.one_mem fun j hj => ?_
    calc t y ^ 5 * j * (t y ^ 5)⁻¹ = y ^ 5 * j * (y ^ 5)⁻¹ := (hpow y hy 5 j hj).symm
      _ = 1 * j * 1⁻¹ := by rw [hEbel.2 y hy]
  have hEbt : ∀ y ∈ Eb, ∀ y' ∈ Eb, y' * t y = t y * y' := by
    intro y hy y' hy'
    have h1 := ht y' hy' (t y) (htJ y hy)
    rw [hcomm y' hy' y hy, mul_inv_cancel_right] at h1
    calc y' * t y = (y' * t y * y'⁻¹) * y' := by group
      _ = t y * y' := by rw [h1]
  have htE : ∀ y ∈ Eb, t y ∈ Eb := fun y hy => hmax _ (htJ y hy) (ht5 y hy) (hEbt y hy)
  have hyt : ∀ y ∈ Eb, y * (t y)⁻¹ ∈ Subgroup.zpowers eb := by
    intro y hy
    refine hEbC _ (Eb.mul_mem hy (Eb.inv_mem (htE y hy))) fun j hj => ?_
    have hmem : (t y)⁻¹ * j * t y ∈ J := J.mul_mem (J.mul_mem (J.inv_mem (htJ y hy)) hj) (htJ y hy)
    have h1 := ht y hy _ hmem
    have h2 : t y * ((t y)⁻¹ * j * t y) * (t y)⁻¹ = j := by group
    rw [h2] at h1
    calc y * (t y)⁻¹ * j = (y * ((t y)⁻¹ * j * t y) * y⁻¹) * (y * (t y)⁻¹) := by group
      _ = j * (y * (t y)⁻¹) := by rw [h1]
  obtain ⟨x, hx, hxab⟩ := hab
  have hab_t : ∀ y ∈ Eb, ab * t y = t y * ab := by
    intro y hy
    have h1 := hxab (t y) (htJ y hy)
    rw [ht x hx (t y) (htJ y hy), hcomm x hx y hy, mul_inv_cancel_right] at h1
    calc ab * t y = (ab * t y * ab⁻¹) * ab := by group
      _ = t y * ab := by rw [h1]
  intro y hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hyt y hy)
  have hy' : y = eb ^ k * t y := by rw [hk]; group
  have hebk : ab * eb ^ k = eb ^ k * ab := (Commute.zpow_left (heb ab : Commute eb ab) k).eq.symm
  rw [hy', ← mul_assoc, hebk, mul_assoc, hab_t y hy, mul_assoc]

end SporHelpers

section Spor

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
  {e : G} {J0 J1 : Subgroup G}

theorem spor_rank (hAut : InputSporAutRank) (P : Prep1116 G m p B M E A a K q e J0 J1)
    {s : TauCeti.SporadicName}
    (hlist : (p = 3 ∧ (s = .M23 ∨ s = .HS ∨ s = .M24 ∨ s = .He)) ∨ (p = 5 ∧ s = .Suz) ∨
      (p = 13 ∧ s = .M))
    (hs : IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1)))
    (hgam : ¬ barX p (Cg e) J1 ≤ GLBCore p 2 (barX p (Cg e) E)) : CFSG.Open.pRank p E = 3 := by
  have hp : p.Prime := P.hp
  have h3 := prep_hE3 P
  by_contra hne
  have h4 : 4 ≤ CFSG.Open.pRank p E := by omega
  apply hgam
  have hY := hAut _ p s hlist (barX_isQuasisimple P.hJ1) (barX_core_eq_bot hp P.hJ1)
    (isSporType_congr (barX_centerQuotEquiv hp P.hJ1) hs)
  have hEr : CFSG.Open.pRank p (barX p (Cg e) E) = CFSG.Open.pRank p E :=
    rank_barX_of_isPGroup hp (elemAbelian_isPGroup (sec11_isElemAbelian_E P.toSec11)) (prep_hEC P)
  have h4' : 4 ≤ CFSG.Open.pRank p (barX p (Cg e) E) := hEr ▸ h4
  refine GL83.I_22_5_proved _ p hp (CFSG.pPrimeCore_quotient_eq_bot hp) _ P.hJ1.2.2.1 _
    (isElemAbelian_barX (sec11_isElemAbelian_E P.toSec11)) ?_ 2 (by norm_num) ?_
  · exact lt_of_le_of_lt hY (lt_of_lt_of_le (by norm_num : 2 < 4) h4')
  · exact le_trans (Nat.add_le_add_left hY 2) h4'

theorem spor_five (hSuz : InputSuzFive) (h104i : Lemma104_iStatement)
    (h104ii : Lemma104_iiStatement) {B M E A : Subgroup G} {K : Subgroup G}
    (P : Prep1116 G m 5 B M E A a K q e J0 J1)
    (hs : IsSporType .Suz (barOf 5 J1 ⧸ Subgroup.center (barOf 5 J1)))
    (hJ1a : GLBConj a J1 = J1)
    (hgam : ¬ barX 5 (Cg e) J1 ≤ GLBCore 5 2 (barX 5 (Cg e) E))
    (hE3 : CFSG.Open.pRank 5 E = 3) : False := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  haveI : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hEel : IsElemAbelian 5 E := sec11_isElemAbelian_E P.toSec11
  have heE : e ∈ E := (Subgroup.mem_inf.1 P.he.1).1
  have ha : a ∈ A := P.ha.1
  have hEX : E ≤ Cg e := prep_hEC P
  have hAX : A ≤ Cg e := prep_hAC P
  have heX : e ∈ Cg e := hEX heE
  have haX : a ∈ Cg e := hAX ha
  have hEA : IsPGroup 5 ↥(E ⊔ A) := h104i P.toSec11.toSec10Fails P.pair
  have hEAX : E ⊔ A ≤ Cg e := sup_le hEX hAX
  have hSC : IsSCp 5 ⊤ E := (h104ii P.toSec11.toSec10Fails P.pair).1
  have hEcard : Nat.card E = 125 := by rw [card_eq_pow_pRank' hp hEel, hE3]; norm_num
  set Eb : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := barX 5 (Cg e) E with hEb
  set Jb : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := barX 5 (Cg e) J1 with hJb
  set eb : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e) := QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨e, heX⟩
    with heb
  set ab : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e) := QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, haX⟩
    with hab
  set Nn := Subgroup.normalizer (Jb : Set (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e))) with hNn
  set Cn := Subgroup.centralizer (Jb : Set (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e))) with hCn
  have hEbel : IsElemAbelian 5 Eb := isElemAbelian_barX hEel
  have hEbcard : Nat.card Eb = 125 :=
    (card_barX_of_isPGroup hp (elemAbelian_isPGroup hEel) hEX).trans hEcard
  have heb_mem : eb ∈ Eb := ⟨⟨e, heX⟩, (Subgroup.mem_subgroupOf).2 heE, rfl⟩
  have heb_ne : eb ≠ 1 := by
    intro h
    have hinj := injective_barX_comp hp (elemAbelian_isPGroup hEel) hEX
    have h1 : (⟨⟨e, heX⟩, (Subgroup.mem_subgroupOf).2 heE⟩ : ↥(E.subgroupOf (Cg e))) = 1 :=
      hinj (by simpa [heb] using h)
    exact P.he.2 (congrArg (fun z : ↥(E.subgroupOf (Cg e)) => ((z : ↥(Cg e)) : G)) h1)
  have heb_central : ∀ z, eb * z = z * eb := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 5 ↥(Cg e)) z
    rw [heb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_singleton_iff).1 x.2).symm
  have heb_N : eb ∈ Nn := by
    rw [hNn, Subgroup.mem_normalizer_iff]
    intro h
    rw [heb_central h, mul_assoc, mul_inv_cancel, mul_one]
  have heb_C : eb ∈ Cn := Subgroup.mem_centralizer_iff.2 fun h _ => (heb_central h).symm
  have hab_N : ab ∈ Nn := bar_mem_normalizer P.hJ1.1 haX hJ1a
  have hlt : 5 * Nat.card ↥(Eb ⊓ Nn ⊓ Cn) < Nat.card ↥(Eb ⊓ Nn) := by
    by_contra hle
    push Not at hle
    apply hgam
    refine bar_le_gamma_of_gen hp P.hJ1 hEX hEel (by rw [hEcard]; norm_num) fun x hx => ?_
    refine Subgroup.mem_iSup_of_mem (Eb ⊓ Nn ⊓ Cn) (Subgroup.mem_iSup_of_mem ⟨inf_le_left, hle⟩ ⟨hx, ?_⟩)
    exact Subgroup.mem_centralizer_iff.2 fun c hc => (Subgroup.mem_centralizer_iff.1 hc.2 x hx).symm
  have hcards : Nat.card ↥(Eb ⊓ Nn) = 125 ∧ Nat.card ↥(Eb ⊓ Nn ⊓ Cn) = 5 := by
    have hd1 : Nat.card ↥(Eb ⊓ Nn ⊓ Cn) ∣ Nat.card ↥(Eb ⊓ Nn) := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(Eb ⊓ Nn) ∣ 5 ^ 3 := by
      rw [show (5 : ℕ) ^ 3 = 125 by norm_num, ← hEbcard]; exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Eb ⊓ Nn ⊓ Cn ≠ ⊥ := by
      intro h
      have : eb ∈ Eb ⊓ Nn ⊓ Cn := ⟨⟨heb_mem, heb_N⟩, heb_C⟩
      rw [h, Subgroup.mem_bot] at this
      exact heb_ne this
    have h1 : 1 < Nat.card ↥(Eb ⊓ Nn ⊓ Cn) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 hd2
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 (hieq ▸ hd1)
    rw [hieq] at hlt ⊢
    rw [hjeq] at hlt h1 ⊢
    interval_cases i <;> interval_cases j <;> simp_all
  have hEbN : Eb ≤ Nn := by
    have : Eb ⊓ Nn = Eb :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hEbcard, hcards.1])
    exact inf_eq_left.1 this
  have heb5 : eb ^ 5 = 1 := hEbel.2 eb heb_mem
  have hord : orderOf eb = 5 := orderOf_eq_prime heb5 heb_ne
  have hEbCe : Eb ⊓ Cn = Subgroup.zpowers eb := by
    have hc5 : Nat.card ↥(Eb ⊓ Cn) = 5 := by
      have := hcards.2
      rwa [inf_eq_left.2 hEbN] at this
    have hle : Subgroup.zpowers eb ≤ Eb ⊓ Cn :=
      Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨heb_mem, heb_C⟩)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, hord, hc5]
  set φ := Jb.normalizerMonoidHom with hφ
  set W : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := Eb ⊔ Subgroup.zpowers ab with hW
  have hWN : W ≤ Nn := sup_le hEbN (Subgroup.zpowers_le.2 hab_N)
  have habW : ab ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers ab)
  have hWp : IsPGroup 5 W := by
    have h1 : IsPGroup 5 (barX 5 (Cg e) (E ⊔ A)) := (hEA.comap_subtype (K := Cg e)).map _
    have habEA : ab ∈ barX 5 (Cg e) (E ⊔ A) :=
      ⟨⟨a, haX⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_sup_right ha), rfl⟩
    have hle : W ≤ barX 5 (Cg e) (E ⊔ A) :=
      sup_le (bar_mono le_sup_left) (Subgroup.zpowers_le.2 habEA)
    exact h1.to_le hle
  set g : ↥W →* MulAut ↥Jb := φ.comp (Subgroup.inclusion hWN) with hg
  set f : ↥Eb →* MulAut ↥Jb := g.comp (Subgroup.inclusion (le_sup_left : Eb ≤ W)) with hf
  have hgp : IsPGroup 5 g.range := hWp.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨hZ, hPaut⟩ := hSuz ↥Jb (barX_isQuasisimple P.hJ1) (barX_core_eq_bot hp P.hJ1)
    (isSporType_congr (barX_centerQuotEquiv hp P.hJ1) hs)
  obtain ⟨hgcard, hginn⟩ := hPaut g.range hgp
  have hfker : f.ker.map Eb.subtype = Eb ⊓ Cn := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have hy' : φ (Subgroup.inclusion hWN (Subgroup.inclusion le_sup_left y)) = 1 := hy
      have hmem := (MonoidHom.mem_ker).2 hy'
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · rintro ⟨hxE, hxC⟩
      refine ⟨⟨x, hxE⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
      have : (Subgroup.inclusion hWN (Subgroup.inclusion le_sup_left ⟨x, hxE⟩)) ∈ φ.ker := by
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact hxC
      exact this
  have hfker5 : Nat.card f.ker = 5 := by
    rw [← Subgroup.card_map_of_injective Eb.subtype_injective, hfker, hEbCe, Nat.card_zpowers, hord]
  have hfcard : Nat.card f.range = 25 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker5, hEbcard] at h
    omega
  have hfle : f.range ≤ g.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion le_sup_left y, rfl⟩
  have hfg : f.range = g.range :=
    Subgroup.eq_of_le_of_card_ge hfle (by rw [hfcard]; exact hgcard)
  have hZ' : ∀ c ∈ Jb, (∀ j ∈ Jb, c * j = j * c) → c = 1 := by
    intro c hc hcj
    have hmem : (⟨c, hc⟩ : ↥Jb) ∈ Subgroup.center ↥Jb := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (hcj z z.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hEbC' : ∀ y ∈ Eb, (∀ j ∈ Jb, y * j = j * y) → y ∈ Subgroup.zpowers eb := by
    intro y hy hyj
    rw [← hEbCe]
    exact ⟨hy, Subgroup.mem_centralizer_iff.2 fun j hj => (hyj j hj).symm⟩
  have hmax : ∀ t ∈ Jb, t ^ 5 = 1 → (∀ y ∈ Eb, y * t = t * y) → t ∈ Eb := by
    intro t _ ht5 htc
    have hFel : IsElemAbelian 5 (Eb ⊔ Subgroup.zpowers t) := by
      refine IsElemAbelian.sup_of_commute hEbel (isElemAbelian_zpowers ht5) ?_
      intro x hx z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_right (htc x hx : Commute x t) k).eq
    have hF : Eb ⊔ Subgroup.zpowers t = Eb := eq_barX_of_isSCp hp hSC hEX le_sup_left hFel
    have hmem : t ∈ Eb ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rwa [hF] at hmem
  have hinner : ∀ y ∈ Eb, ∃ t ∈ Jb, ∀ j ∈ Jb, y * j * y⁻¹ = t * j * t⁻¹ := by
    intro y hy
    have hmem : f ⟨y, hy⟩ ∈ g.range := by
      rw [← hfg]
      exact ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨t, ht⟩ := hginn hmem
    refine ⟨t, t.2, fun j hj => ?_⟩
    calc y * j * y⁻¹ = ((f ⟨y, hy⟩ ⟨j, hj⟩ : ↥Jb) : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := rfl
      _ = ((MulAut.conj t ⟨j, hj⟩ : ↥Jb) : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := by rw [ht]
      _ = t * j * t⁻¹ := rfl
  have hab' : ∃ x ∈ Eb, ∀ j ∈ Jb, ab * j * ab⁻¹ = x * j * x⁻¹ := by
    have hmem : g ⟨ab, habW⟩ ∈ f.range := by
      rw [hfg]
      exact ⟨⟨ab, habW⟩, rfl⟩
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, x.2, fun j hj => ?_⟩
    calc ab * j * ab⁻¹ = ((g ⟨ab, habW⟩ ⟨j, hj⟩ : ↥Jb) : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := rfl
      _ = ((f x ⟨j, hj⟩ : ↥Jb) : ↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e)) := by rw [hx]
      _ = x * j * x⁻¹ := rfl
  have hab_E := centralizes_of_inner hZ' hEbel hEbC' heb_central hmax hinner hab'
  have haE : ∀ z ∈ E, a * z = z * a := by
    intro z hz
    have hinj := injective_barX_comp hp hEA hEAX
    have hzX : z ∈ Cg e := hEX hz
    have hmemaz : (⟨a, haX⟩ * ⟨z, hzX⟩ : ↥(Cg e)) ∈ (E ⊔ A).subgroupOf (Cg e) :=
      (Subgroup.mem_subgroupOf).2 ((E ⊔ A).mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hz))
    have hmemza : (⟨z, hzX⟩ * ⟨a, haX⟩ : ↥(Cg e)) ∈ (E ⊔ A).subgroupOf (Cg e) :=
      (Subgroup.mem_subgroupOf).2 ((E ⊔ A).mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right ha))
    have h1 := hab_E (QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨z, hzX⟩)
      ⟨⟨z, hzX⟩, (Subgroup.mem_subgroupOf).2 hz, rfl⟩
    rw [hab, ← map_mul, ← map_mul] at h1
    have h2 := hinj (a₁ := ⟨_, hmemaz⟩) (a₂ := ⟨_, hmemza⟩) h1
    exact congrArg (fun w : ↥((E ⊔ A).subgroupOf (Cg e)) => ((w : ↥(Cg e)) : G)) h2
  have hEa : IsElemAbelian 5 (E ⊔ Subgroup.zpowers a) := by
    refine IsElemAbelian.sup_of_commute hEel (isElemAbelian_zpowers (prep_hap P)) ?_
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right ((haE y hy).symm : Commute y a) k).eq
  have hEaE : E ⊔ Subgroup.zpowers a = E := hSC.2.2 _ le_top hEa le_sup_left
  have haE' : a ∈ E := hEaE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  exact P.notD ⟨E, P.pair.1.1, haE'⟩

end Spor

theorem prop1116_spor_of_inputs (hSpor : Input14_13Spor) (hAut : InputSporAutRank) (hSuz : InputSuzFive)
    (hField : Input14_4_1Field)
    (h113 : Lemma113_iStatement) (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104vi : Lemma104_viStatement) : Prop1116SporStatement := by
  intro G _ _ m p B M E A a K q e J0 J1 P s hs
  have hp : p.Prime := P.hp
  have hp2 : p ≠ 2 := P.standing.ne_two
  obtain ⟨hJ1a, hcases⟩ := hSpor hp hp2 (prep_hea P) (prep_hap P) P.hJ1 P.hJ0' P.hJstar s hs q
    P.hq.1 P.hq.2.1 P.hq.2.2 P.hJ0chev
  have hKx : Kx p J0 e = J1 := by
    rw [P.hJstar]
    apply le_antisymm
    · exact iSup₂_le fun g hg => le_of_eq (gLBConj_eq_of_zpowers hJ1a hg)
    · exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one J1).symm)
  have hgam : ¬ barX p (Cg e) J1 ≤ GLBCore p 2 (barX p (Cg e) E) := by
    rw [← hKx]
    exact P.hgamma
  have hlist : (p = 3 ∧ (s = .M23 ∨ s = .HS ∨ s = .M24 ∨ s = .He)) ∨ (p = 5 ∧ s = .Suz) ∨
      (p = 13 ∧ s = .M) := by
    rcases hcases with ⟨h3, h | h, -⟩ | ⟨h3, h | h, -⟩ | ⟨h5, h, -⟩ | ⟨h13, h, -⟩
    · exact Or.inl ⟨h3, Or.inl h⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inr (Or.inl ⟨h5, h⟩)
    · exact Or.inr (Or.inr ⟨h13, h⟩)
  have hE3 : CFSG.Open.pRank p E = 3 := spor_rank hAut P hlist hs hgam
  rcases hcases with ⟨hp3, -, -⟩ | ⟨hp3, -, -⟩ | ⟨hp5, hsS, -⟩ | ⟨hp13, -, hL33⟩
  · subst hp3
    have := h113 P.toSec11 P.ha.1 P.ha.2 P.notD
    omega
  · subst hp3
    have := h113 P.toSec11 P.ha.1 P.ha.2 P.notD
    omega
  · subst hp5
    subst hsS
    exact spor_five hSuz h104i h104ii P hs hJ1a hgam hE3
  · subst hp13
    have hAel : IsElemAbelian 13 A := sec11_isElemAbelian_A P.toSec11
    exact P.notIv ⟨rfl, h104vi P.toSec11.toSec10Fails P.pair hE3,
      hField P.hK P.hq.1 P.hq.2.1 P.hq.2.2 P.hchev
        (inf_le_right.trans (le_cg_of_elemAbelian hAel P.ha.1)) (isElemAbelian_of_le hAel inf_le_right)
        P.he.1 P.he.2 P.hJ0 P.hJ0K hL33⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116
