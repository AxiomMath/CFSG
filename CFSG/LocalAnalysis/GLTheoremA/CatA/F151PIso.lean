module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremB

private theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  · intro h
    apply e.injective
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply]

private theorem shapeModelNormAt_of_shapeModelAt {R : Type} [Group R] [Finite R] (p : ℕ)
    (h : ShapeModelAt R p) : ShapeModelNormAt R p :=
  fun x y hx hxp hyp hcomm J hJ => (h x y hx hxp hyp hcomm J hJ).1

private theorem glaPComponent_map_mulEquiv' {p : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {X K : Subgroup A} (h : GLAPComponent p X K) :
    GLAPComponent p (X.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := h
  have hcomp₁ : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
    ext x; simp
  have hcomp₂ : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
    ext x; simp
  let eX : ↥X ≃* ↥(X.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective X e.toMonoidHom e.injective
  have hcore : (GLAPPrimeCore p ↥X).map (↑eX) =
      GLAPPrimeCore p ↥(X.map e.toMonoidHom) := by
    exact glaPPrimeCore_map_iso p eX
  let ζ : PQuot p X ≃* PQuot p (X.map e.toMonoidHom) :=
    QuotientGroup.congr (GLAPPrimeCore p ↥X) (GLAPPrimeCore p ↥(X.map e.toMonoidHom)) eX hcore
  have heX : ∀ x : ↥X, ((eX x : ↥(X.map e.toMonoidHom)) : B) = e (x : A) :=
    fun x => Subgroup.coe_equivMapOfInjective_apply X e.toMonoidHom e.injective x
  have heXsymm : ∀ y : ↥(X.map e.toMonoidHom),
      ((eX.symm y : ↥X) : A) = e.symm (y : B) := by
    intro y
    have h := heX (eX.symm y)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h, MulEquiv.symm_apply_apply]
  have hbar : ∀ S : Subgroup A,
      (barX p X S).map ζ.toMonoidHom =
        barX p (X.map e.toMonoidHom) (S.map e.toMonoidHom) := by
    intro S
    ext z
    simp only [barX, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨eX x, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact Subgroup.mem_map_of_mem e.toMonoidHom hx
      · exact (QuotientGroup.congr_mk _ _ eX hcore x).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨QuotientGroup.mk' _ (eX.symm y), ⟨eX.symm y, ?_, rfl⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hy ⊢
        obtain ⟨s, hs, hse⟩ := hy
        have hsymm : e.symm (y : ↥(X.map e.toMonoidHom)) = s := by
          rw [← hse]
          exact MulEquiv.symm_apply_apply e s
        rw [heXsymm y, hsymm]
        exact hs
      · exact (QuotientGroup.congr_mk _ _ eX hcore (eX.symm y)).trans (by
          rw [MulEquiv.apply_symm_apply]; rfl)
  refine ⟨Subgroup.map_mono hKX, hsn.map e.toMonoidHom, ?_, ?_⟩
  · have hthis := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ζ hcomp
    have htop : (⊤ : Subgroup (PQuot p X)).map
        (ζ : PQuot p X →* PQuot p (X.map e.toMonoidHom)) = ⊤ :=
      Subgroup.map_top_of_surjective ζ.toMonoidHom ζ.surjective
    rw [htop] at hthis
    convert hthis using 2
    exact (hbar K).symm
  · intro J' hJ' hJ'sn heq
    set J : Subgroup A := J'.map e.symm.toMonoidHom with hJdef
    have hJle : J ≤ K := by
      have hle' : J ≤ (K.map e.toMonoidHom).map e.symm.toMonoidHom :=
        Subgroup.map_mono (f := e.symm.toMonoidHom) hJ'.le
      rwa [Subgroup.map_map, hcomp₂, Subgroup.map_id] at hle'
    have hJlt : J < K := by
      refine lt_of_le_of_ne hJle ?_
      intro hJK
      apply hJ'.ne
      have hEq : (J'.map e.symm.toMonoidHom).map e.toMonoidHom = K.map e.toMonoidHom := by
        rw [← hJdef, hJK]
      rwa [Subgroup.map_map, hcomp₁, Subgroup.map_id] at hEq
    have hJsn : IsSubnormal J X := by
      have hle' : IsSubnormal (J'.map e.symm.toMonoidHom)
          ((X.map e.toMonoidHom).map e.symm.toMonoidHom) := hJ'sn.map e.symm.toMonoidHom
      rwa [Subgroup.map_map, hcomp₂, Subgroup.map_id] at hle'
    refine hmin J hJlt hJsn ?_
    have hJmap : J.map e.toMonoidHom = J' := by
      rw [hJdef, Subgroup.map_map, hcomp₁, Subgroup.map_id]
    exact Subgroup.map_injective ζ.injective (by
      change (barX p X J).map ζ.toMonoidHom = (barX p X K).map ζ.toMonoidHom
      rw [hbar J, hbar K, hJmap]
      exact heq)

private theorem ker_barMap_eq' {p : ℕ} {G : Type} [Group G] [Finite G]
    {C L : Subgroup G} (hLC : L ≤ C) (hsn : IsSubnormal L C) :
    (barMap p hLC).ker = GLAPPrimeCore p ↥L := by
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
        (le_normalizer_glaPPrimeCoreOf p C (hLC g.2)) (n : G)).1
        ((Subgroup.mem_subgroupOf).1 hn)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using h2)
    have hcopCard : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C)) := by
      have hcard : Nat.card (GLAPPrimeCoreOf p C) = Nat.card (GLAPPrimeCore p ↥C) := by
        rw [(show GLAPPrimeCoreOf p C = (GLAPPrimeCore p ↥C).map C.subtype by
              unfold GLAPPrimeCoreOf
              rfl),
          Subgroup.card_map_of_injective C.subtype_injective]
      rw [hcard]
      exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p (↥C)
    have hcop : Nat.Coprime p (Nat.card K) := by
      have hc : Nat.card (K.map L.subtype) = Nat.card K :=
        Subgroup.card_map_of_injective L.subtype_injective
      have hle : K.map L.subtype ≤ GLAPPrimeCoreOf p C := by
        rintro _ ⟨k, hk, rfl⟩
        exact (Subgroup.mem_subgroupOf).1 hk
      have hdvd : Nat.card K ∣ Nat.card (GLAPPrimeCoreOf p C) := by
        rw [← hc]
        exact Subgroup.card_dvd_of_le hle
      exact hcopCard.coprime_dvd_right hdvd
    have hKle : K ≤ GLAPPrimeCore p ↥L := le_sSup ⟨hnorm, hcop⟩
    exact hKle ((Subgroup.mem_subgroupOf).2
      (Subgroup.mem_map.2 ⟨Subgroup.inclusion hLC l, h1, rfl⟩))
  · intro hl
    have h1 : (l : G) ∈ GLAPPrimeCoreOf p L := ⟨l, hl, rfl⟩
    obtain ⟨c, hc, hcl⟩ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hsn h1
    have hcl' : Subgroup.inclusion hLC l = c := Subtype.ext hcl.symm
    refine Subtype.ext ?_
    change QuotientGroup.mk' (GLAPPrimeCore p ↥C) (Subgroup.inclusion hLC l) = 1
    rw [hcl', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc

private noncomputable def quotEquivBarX' {p : ℕ} {G : Type} [Group G] [Finite G]
    {C L : Subgroup G} (hLC : L ≤ C) (hsn : IsSubnormal L C) :
    (↥L ⧸ GLAPPrimeCore p ↥L) ≃* ↥(barX p C L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barMap_eq' hLC hsn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (barMap p hLC) (barMap_surjective hLC))

private theorem commutator_pQuot_of_glaPComponent {p : ℕ} {G : Type} [Group G] [Finite G]
    {X J : Subgroup G} (hJ : GLAPComponent p X J) : commutator (PQuot p J) = ⊤ := by
  have hcomp : CFSG.Open.IsQuasisimple (barX p X J) := hJ.2.2.1.2.2
  let e : PQuot p J ≃* ↥(barX p X J) := quotEquivBarX' (p := p) hJ.1 hJ.2.1
  have htop : (⊤ : Subgroup (PQuot p J)).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  have hm : (commutator (PQuot p J)).map e.toMonoidHom =
      (⊤ : Subgroup (PQuot p J)).map e.toMonoidHom := by
    rw [commutator_def, Subgroup.map_commutator, htop]
    exact hcomp.1
  exact Subgroup.map_injective e.injective hm

private theorem exists_pSimple_equiv_map {p : ℕ} {A B : Type} [Group A] [Group B]
    (φ : A ≃* B) (J : Subgroup A) :
    ∃ ψ : PSimple p J ≃* PSimple p (J.map φ.toMonoidHom),
      ∀ (y : A) (s s' : PSimple p J), indRelS p J y s s' →
        indRelS p (J.map φ.toMonoidHom) (φ y) (ψ s) (ψ s') := by
  classical
  let e : ↥J ≃* ↥(J.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective J φ.toMonoidHom φ.injective
  have he : ∀ j : ↥J, ((e j : ↥(J.map φ.toMonoidHom)) : B) = φ (j : A) :=
    fun j => Subgroup.coe_equivMapOfInjective_apply J φ.toMonoidHom φ.injective j
  have hcore : (GLAPPrimeCore p ↥J).map (↑e) =
      GLAPPrimeCore p ↥(J.map φ.toMonoidHom) := by
    exact glaPPrimeCore_map_iso p e
  let ζ : PQuot p J ≃* PQuot p (J.map φ.toMonoidHom) :=
    QuotientGroup.congr (GLAPPrimeCore p ↥J) (GLAPPrimeCore p ↥(J.map φ.toMonoidHom)) e hcore
  let ψ : PSimple p J ≃* PSimple p (J.map φ.toMonoidHom) :=
    QuotientGroup.congr (Subgroup.center (PQuot p J))
      (Subgroup.center (PQuot p (J.map φ.toMonoidHom))) ζ
      (by simpa using Subgroup.map_center_eq ζ)
  have hζ : ∀ j : ↥J, ζ (QuotientGroup.mk j) = QuotientGroup.mk (e j) := fun j => rfl
  have hψ : ∀ q : PQuot p J, ψ (QuotientGroup.mk q) = QuotientGroup.mk (ζ q) := fun q => rfl
  refine ⟨ψ, ?_⟩
  intro y s s' hs
  obtain ⟨q, q', hq, rfl, rfl⟩ := hs
  obtain ⟨l, l', hl, hl', hll⟩ := hq
  refine ⟨ζ q, ζ q', ⟨e l, e l', ?_, ?_, ?_⟩, (hψ q).symm, (hψ q').symm⟩
  · rw [← hl]; exact (hζ l).symm
  · rw [← hl']; exact (hζ l').symm
  · rw [he, he, hll]; simp

theorem shapeModelNormIso_holds : ShapeModelNormIso := by
  intro R R' _ _ _ _ e p h x' y' hx' hxp hyp hcomm J' hJ'
  let x : R := e.symm x'
  let y : R := e.symm y'
  have hx : x ≠ 1 := by
    intro hx1
    apply hx'
    calc x' = e x := (MulEquiv.apply_symm_apply e x').symm
      _ = e 1 := by rw [hx1]
      _ = 1 := map_one e
  have hxp' : x ^ p = 1 := by
    show (e.symm x') ^ p = 1
    rw [← map_pow, hxp, map_one]
  have hyp' : y ^ p = 1 := by
    show (e.symm y') ^ p = 1
    rw [← map_pow, hyp, map_one]
  have hcomm' : Commute x y := by
    show x * y = y * x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hcomm
  let J : Subgroup R := J'.map e.symm.toMonoidHom
  have hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J := by
    have h1 := glaPComponent_map_mulEquiv' (p := p) e.symm hJ'
    have h2 : (Subgroup.centralizer ({x'} : Set R')).map e.symm.toMonoidHom =
        Subgroup.centralizer ({x} : Set R) := by
      show (Subgroup.centralizer ({x'} : Set R')).map e.symm.toMonoidHom =
        Subgroup.centralizer ({e.symm x'} : Set R)
      exact map_centralizer_singleton e.symm x'
    rwa [h2] at h1
  have hyN : y ∈ Subgroup.normalizer (J : Set R) :=
    h x y hx hxp' hyp' hcomm' J hJ
  have hJmap : J.map e.toMonoidHom = J' := by
    show (J'.map e.symm.toMonoidHom).map e.toMonoidHom = J'
    rw [Subgroup.map_map,
      show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id R' by ext x; simp,
      Subgroup.map_id]
  have hy'mem : y' ∈ (Subgroup.normalizer (J : Set R)).map e.toMonoidHom := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom hyN
    rwa [show e.toMonoidHom y = y' from MulEquiv.apply_symm_apply e y'] at h
  rwa [Subgroup.map_equiv_normalizer_eq J e, hJmap] at hy'mem

theorem shapeModelIso_holds : ShapeModelIso := by
  intro hMT R R' _ _ _ _ e p h x' y' hx' hxp hyp hcomm J' hJ'
  have hy'N : y' ∈ Subgroup.normalizer (J' : Set R') :=
    (shapeModelNormIso_holds R R' e p (shapeModelNormAt_of_shapeModelAt p h))
      x' y' hx' hxp hyp hcomm J' hJ'
  refine ⟨hy'N, ?_⟩
  let x : R := e.symm x'
  let y : R := e.symm y'
  have hx : x ≠ 1 := by
    intro hx1
    apply hx'
    calc x' = e x := (MulEquiv.apply_symm_apply e x').symm
      _ = e 1 := by rw [hx1]
      _ = 1 := map_one e
  have hxp' : x ^ p = 1 := by
    show (e.symm x') ^ p = 1
    rw [← map_pow, hxp, map_one]
  have hyp' : y ^ p = 1 := by
    show (e.symm y') ^ p = 1
    rw [← map_pow, hyp, map_one]
  have hcomm' : Commute x y := by
    show x * y = y * x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hcomm
  let J : Subgroup R := J'.map e.symm.toMonoidHom
  have hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J := by
    have h1 := glaPComponent_map_mulEquiv' (p := p) e.symm hJ'
    have h2 : (Subgroup.centralizer ({x'} : Set R')).map e.symm.toMonoidHom =
        Subgroup.centralizer ({x} : Set R) := by
      show (Subgroup.centralizer ({x'} : Set R')).map e.symm.toMonoidHom =
        Subgroup.centralizer ({e.symm x'} : Set R)
      exact map_centralizer_singleton e.symm x'
    rwa [h2] at h1
  have hInn : InnDiagOn p (Subgroup.zpowers y) J :=
    (h x y hx hxp' hyp' hcomm' J hJ).2
  obtain ⟨ψ, hψ⟩ := exists_pSimple_equiv_map (p := p) e.symm J'
  have hperf : commutator (PQuot p J') = ⊤ := commutator_pQuot_of_glaPComponent hJ'
  have hind : ∀ s s' : PSimple p J', indRelS p J' y' s s' →
      indRelS p J y (ψ s) (ψ s') := fun s s' hs => hψ y' s s' hs
  exact hMT R' R p J' J y' y ψ hperf hy'N hind hInn

end CFSG.LocalAnalysis.GLTheoremA.F151

end
