module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Omega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Fld
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155XSp

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)

open scoped commutatorElement MatrixGroups

theorem l154s_exists_psp {T : Type} [Group T] (h : catalogIs T l154Symp) :
    ∃ (r m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ r ∧ Nat.card E = 2 ^ m ∧
      ¬ (r = 2 ∧ Nat.card E = 2) ∧ Nonempty (T ≃* StatedProj (StatedSp r E)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [l154Symp, onLie] at hi
  | alternating n hn => simp [l154Symp, onLie] at hi
  | sporadic s => simp [l154Symp, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | B r q =>
      have hq : q.p = 2 := by simpa [l154Symp, onLie] using hi
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [GaloisField.card q.p q.exponent (Nat.pos_iff_ne_zero.1 q.exponent_pos),
          TauCeti.PrimePower.card_def q]
      refine ⟨r, q.exponent, GaloisField q.p q.exponent, inferInstance, inferInstance, hr.1, ?_,
        ?_, ?_⟩
      · rw [hcard, TauCeti.PrimePower.card_def q, hq]
      · rw [hcard]
        exact hr.2
      · rcases (show r = 2 ∨ 3 ≤ r by have := hr.1; omega) with rfl | hr3
        · obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
            hv hcard
          exact ⟨e.trans e'.symm⟩
        · obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
            hv hq hr3 hcard
          exact ⟨e.trans e'.symm⟩
    | C r q =>
      have hq : q.p = 2 := by simpa [l154Symp, onLie] using hi
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      exact absurd hq hr.2
    | _ => simp [l154Symp, onLie] at hi

theorem l154s_tag_of_canonLabel {lab : CFSG.Assembly.LargeEvenLabel} {r m : ℕ}
    (h : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = ⟨.B, r, m⟩) (hne : ¬ (r = 2 ∧ m = 1)) :
    (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = r ∧ lab.n = m := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [CFSG.LocalAnalysis.GLTheoremA.canonLabel] at h ⊢
  · exact h
  · exact h
  · split_ifs at h <;> simp at h
  · split_ifs at h <;> simp at h
  · exact hne ⟨h.1.symm, h.2.symm⟩

theorem l154s_two_eq_zero {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    (2 : K) = 0 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact_mod_cast CharP.cast_eq_zero K 2

section Certs


theorem l154s_marking_data (hRig : GGLabelRigidInput) {p : ℕ} (hp : p.Prime)
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154Symp)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (θ : PSimple p S ≃* StatedProj (StatedSp r K)) (A U : gsp r K) (σ : K ≃+* K),
      2 ≤ r ∧ (2 : K) = 0 ∧ 4 ≤ Nat.card K ∧ σ ≠ 1 ∧
      LargeEvenInduces θ (indRel p S x) (conjAut r K A) ∧
      LargeEvenInduces θ (indRel p S y)
        (conjAut r K U * fieldAut r K σ * (conjAut r K U)⁻¹) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  have h1 := CFSG.LocalAnalysis.GLTheoremA.MI.marking_transport (indRel p S x) hdiag hF.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h1
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p S)
      (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨r, m, E, _, _, hr, hE, hne, ⟨e⟩⟩ := l154s_exists_psp hQ
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig
    hr hE hne hlab e
  have hne' : ¬ (r = 2 ∧ m = 1) := by
    rintro ⟨h2, h1⟩
    exact hne ⟨h2, by rw [hE, h1, pow_one]⟩
  obtain ⟨htag, hrank, hn⟩ := l154s_tag_of_canonLabel hcanon hne'
  have hraw' : LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : PQuot p S ⧸ Subgroup.center (PQuot p S) ≃* R,
          LargeEvenPrimeField p lab I F (LargeEvenInduces θ (indRel p S y)) ∧
            ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ) := by
    rcases htag with ht | ht
    · unfold CFSG.Assembly.LargeEvenRawDatum at hraw
      rw [ht] at hraw
      exact hraw
    · unfold CFSG.Assembly.LargeEvenRawDatum at hraw
      rw [ht] at hraw
      exact hraw
  obtain ⟨K, instF, instFin, hK, -, -, θ, ⟨-, f, hf, u, hu, hord, hindy⟩, φx, hφx, hindx⟩ := hraw'
  obtain ⟨A, hA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hφx
  obtain ⟨U, hU⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hu
  obtain ⟨σ, hσf⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_fieldAut_eq_of_mem_matFieldImage hf
  have hn1 : 1 ≤ lab.n := hΛ.1
  have h2 : (2 : K) = 0 := l154s_two_eq_zero hK
  have hσ : σ ≠ 1 := by
    rintro rfl
    rw [map_one] at hσf
    rw [← hσf, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hK4 : 4 ≤ Nat.card K := by
    rcases Nat.lt_or_ge lab.n 2 with h | h
    · exfalso
      have hn' : lab.n = 1 := by omega
      rw [hn', pow_one] at hK
      exact hσ (CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.ringEquiv_eq_one_of_card_eq_two hK σ)
    · rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h
  refine ⟨lab.rank, K, instF, instFin, θ, A, U, σ, hrank ▸ hr, h2, hK4, hσ, ?_, ?_⟩
  · rw [hA]
    exact hindx
  · rw [hU, hσf]
    exact hindy

theorem l154s_fieldOn_of_block {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hyp : y ^ p = 1) (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {r : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0)
    (θ : PSimple p S ≃* StatedProj (StatedSp r K))
    (Y : StatedSp r K →* StatedSp r K) (B : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hY : ∀ g : StatedSp r K, ((Y g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      B * glMap σ (g : GL (Fin r ⊕ Fin r) K) * B⁻¹)
    (ψ : MulAut (StatedProj (StatedSp r K)))
    (hψ : ∀ g : StatedSp r K, ψ (proj r K g) = proj r K (Y g))
    (hindy : LargeEvenInduces θ (indRel p S y) ψ)
    (D : Subgroup (StatedSp r K)) (hDq : CFSG.IsQuasisimple ↥D)
    (hJD : (chevTransfer p S J).map θ.toMonoidHom = D.map (proj r K))
    (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hN : N ≠ 0)
    (hKline : ∀ c : K, ∃ t ∈ D,
      (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        1 + c • N)
    (hmark : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧
      ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) ∧
      CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ => IsSimpleGroup R ∧
        ∃ Θ : ↥D →* R, Function.Surjective Θ ∧ Θ.ker ≤ Subgroup.center ↥D ∧
          ∀ α ∈ I, ∃ Q : GL (Fin r ⊕ Fin r) K, ∀ g : ↥D, ∃ g' : ↥D,
            ((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
              Q * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * Q⁻¹ ∧ α (Θ g) = Θ g') :
    FieldOn p y J := by
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hπinj := l154s_proj_injective (r := r) h2
  set JP : Subgroup (StatedProj (StatedSp r K)) := (chevTransfer p S J).map θ.toMonoidHom
    with hJPdef
  let ρJ : ↥J →* StatedProj (StatedSp r K) :=
    (θ.toMonoidHom.comp (chevQuotHom p S)).comp (Subgroup.inclusion hJS)
  let πD : ↥D →* StatedProj (StatedSp r K) := (proj r K).comp D.subtype
  have hπDinj : Function.Injective πD := hπinj.comp Subtype.val_injective
  have hρJmem : ∀ l : ↥J, ρJ l ∈ JP := by
    intro l
    rw [hJPdef]
    refine Subgroup.mem_map.2 ⟨chevQuotHom p S ⟨l.1, hJS l.2⟩, ?_, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hmemJP : ∀ z ∈ JP, ∃ l : ↥J, ρJ l = z := by
    intro z hz
    rw [hJPdef] at hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hc
    exact ⟨⟨s.1, Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩
  have hρΨ : ∀ l : ↥J, ∃ d : ↥D, πD d = ρJ l := by
    intro l
    have h1 : ρJ l ∈ D.map (proj r K) := hJD ▸ hρJmem l
    obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.1 h1
    exact ⟨⟨g, hg⟩, hgl⟩
  have hΨρ : ∀ d : ↥D, ∃ l : ↥J, ρJ l = πD d := by
    intro d
    have h1 : πD d ∈ JP := by
      rw [hJD]
      exact Subgroup.mem_map.2 ⟨d, d.2, rfl⟩
    exact hmemJP _ h1
  have hperfJ : commutator ↥J = ⊤ := by
    have h1 := Subgroup.map_subtype_commutator J
    rw [glaPComponent_perfect hJ] at h1
    have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)
  have hρJker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : chevQuotHom p S ⟨l.1, hJS l.2⟩ = 1 := by
      have : θ (chevQuotHom p S ⟨l.1, hJS l.2⟩) = 1 := hl
      exact (map_eq_one_iff _ θ.injective).1 this
    have h2 : (QuotientGroup.mk (⟨l.1, hJS l.2⟩ : ↥S) : PQuot p S) ∈
        Subgroup.center (PQuot p S) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ∀ s : ↥S, s * ⟨l.1, hJS l.2⟩ = ⟨l.1, hJS l.2⟩ * s := by
      intro s
      have h4 := Subgroup.mem_center_iff.1 h2 (QuotientGroup.mk s)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hSp,
        Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4 |>.symm ▸ rfl
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h5 := h3 ⟨j.1, hJS j.2⟩
    show (j : Ω) * (l : Ω) = (l : Ω) * (j : Ω)
    exact congrArg Subtype.val h5
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hJy
  have hYD : ∀ l : ↥J, ∀ d : ↥D, πD d = ρJ l →
      ∃ (l' : ↥J) (d' : ↥D), (l' : Ω) = y⁻¹ * (l : Ω) * y ∧ (d' : StatedSp r K) = Y d ∧
        πD d' = ρJ l' := by
    intro l d hd
    have hl'mem : y⁻¹ * (l : Ω) * y ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
      simpa using this
    let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, hl'mem⟩
    have hρl' : ρJ l' = ψ (ρJ l) :=
      (hindy (QuotientGroup.mk ⟨l.1, hJS l.2⟩) (QuotientGroup.mk ⟨l'.1, hJS l'.2⟩)
        ⟨⟨l.1, hJS l.2⟩, ⟨l'.1, hJS l'.2⟩, rfl, rfl, rfl⟩).symm
    obtain ⟨d', hd'⟩ := hρΨ l'
    refine ⟨l', d', rfl, ?_, hd'⟩
    apply hπinj
    have : πD d' = proj r K (Y d) := by
      rw [hd', hρl', ← hd]
      exact hψ d
    exact this
  obtain ⟨lab, hΛ, hlt, hD4, hraw⟩ := hmark
  have hperfQ : commutator (PQuot p J) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hJ).1
  refine fieldOn_of_notInner hp hp2 hJy hyp ⟨hperfQ, lab, hΛ, ?_⟩
  refine Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, ΘD, hΘDsurj, hΘDker, hreal⟩
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift ρJ πD ΘD hρΨ (fun d hd => by
    rw [hπDinj (hd.trans (map_one πD).symm), map_one])
  have hΘsurj : Function.Surjective Θ := by
    intro z
    obtain ⟨d, rfl⟩ := hΘDsurj z
    obtain ⟨l, hl⟩ := hΨρ d
    exact ⟨l, hΘ l d hl.symm⟩
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨d, hd⟩ := hρΨ l
    have hqd : ΘD d = 1 := by rw [← hΘ l d hd]; exact hl
    have hdc : d ∈ Subgroup.center ↥D := hΘDker hqd
    refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.mem_center_of_commutator_mem_center hperfJ
      fun j => ?_
    apply hρJker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    obtain ⟨d', hd'⟩ := hρΨ j
    rw [← hd, ← hd', ← map_commutatorElement]
    have : ⁅d, d'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hdc d').symm
    rw [this, map_one]
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hs Θ hΘsurj hΘker
  obtain ⟨hsJ, hnaJ⟩ := chev_pSimple_simple_nonabelian hp hJ
  refine ⟨hs, ?_, e₀, hlt, hD4, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnaJ
    exact ⟨e₀ a, e₀ b, fun h => hab (e₀.injective (by rw [map_mul, map_mul, h]))⟩
  intro hI
  set α := MulAut.congr e₀ (MI.indAut p J y hJy) with hαdef
  have hαΘ : ∀ d : ↥D, ∃ d' : ↥D, (d' : StatedSp r K) = Y d ∧ α (ΘD d) = ΘD d' := by
    intro d
    obtain ⟨l, hl⟩ := hΨρ d
    obtain ⟨l', d', hl'y, hd'Y, hd'l'⟩ := hYD l d hl.symm
    refine ⟨d', hd'Y, ?_⟩
    have e1 : ΘD d = e₀ (QuotientGroup.mk (QuotientGroup.mk l)) := by
      rw [he₀ l]
      exact (hΘ l d hl.symm).symm
    have e2 : ΘD d' = e₀ (QuotientGroup.mk (QuotientGroup.mk l')) := by
      rw [he₀ l']
      exact (hΘ l' d' hd'l').symm
    have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk l') :=
      MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, hl'y⟩
    rw [e1, e2, hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, e3]
  obtain ⟨Q, hQ⟩ := hreal α hI
  have hperfD : commutator ↥D = ⊤ := Group.isPerfect_def.mp hDq.1
  let γ : ↥D →* GL (Fin r ⊕ Fin r) K := ((StatedSp r K).subtype.comp Y).comp D.subtype
  let κ : ↥D →* GL (Fin r ⊕ Fin r) K :=
    (MulAut.conj Q).toMonoidHom.comp ((StatedSp r K).subtype.comp D.subtype)
  let Sc : GL (Fin r ⊕ Fin r) K → Prop := fun v =>
    ∃ z ∈ Subgroup.center ↥D, v = ((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K)
  have hκD : ∀ g : ↥D, ∃ g' : ↥D, κ g = ((g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∧
      α (ΘD g) = ΘD g' := by
    intro g
    obtain ⟨g', hg', hαg⟩ := hQ g
    exact ⟨g', hg'.symm, hαg⟩
  have hScS : ∀ v v', Sc v → Sc v' → v * v' = v' * v := by
    rintro v v' ⟨z, hz, rfl⟩ ⟨z', -, rfl⟩
    have := Subgroup.mem_center_iff.1 hz z'
    exact congrArg (fun w : ↥D => ((w : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) this.symm
  have hScκ : ∀ v, Sc v → ∀ g : ↥D, v * κ g = κ g * v := by
    rintro v ⟨z, hz, rfl⟩ g
    obtain ⟨g', hg', -⟩ := hκD g
    rw [hg']
    have := Subgroup.mem_center_iff.1 hz g'
    exact congrArg (fun w : ↥D => ((w : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) this.symm
  have hw : ∀ g : ↥D, Sc (γ g * (κ g)⁻¹) := by
    intro g
    obtain ⟨d', hd'Y, hαd⟩ := hαΘ g
    obtain ⟨g', hg', hαg⟩ := hκD g
    refine ⟨d' * g'⁻¹, hΘDker ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, ← hαd, ← hαg, mul_inv_cancel]
    · show ((Y g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * (κ g)⁻¹ = _
      rw [hg', ← hd'Y]
      rfl
  have hγκ : ∀ g : ↥D, γ g = κ g := hom_of_displacement hperfD γ κ Sc hScS hScκ hw
  refine l154s_false_of_conj_kline
    {g | ∃ d ∈ D, ((d : StatedSp r K) : GL (Fin r ⊕ Fin r) K) = g} B Q σ hσ ?_ N hN ?_
  · rintro g ⟨d, hd, rfl⟩
    have := hγκ ⟨d, hd⟩
    rw [← hY]
    exact this
  · intro c
    obtain ⟨t, ht, htc⟩ := hKline c
    exact ⟨_, ⟨t, ht, rfl⟩, htc⟩

theorem l154_symp_fieldOn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hQ : catalogIs (PSimple p S) l154Symp)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) : FieldOn p y J := by
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := hInn.1 (Subgroup.mem_zpowers x)
  obtain ⟨r, K, instF, instFin, θ, A, U, σ, hr, h2, hK4, hσ, hindx, hindy⟩ :=
    l154s_marking_data CFSG.StandardType.ggLabelRigidInput_holds hp hQ hInn hF
  obtain ⟨n, hK⟩ : ∃ n : ℕ, Nat.card K = 2 ^ n := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hn : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn1 : 1 ≤ n := by omega
  have hφx : conjAut r K A = MulAut.congr θ (MI.indAut p S x hxN) :=
    (MI.induces_indRel_iff hxN θ).1 hindx
  have hpow : conjAut r K A ^ p = 1 := by
    rw [hφx, ← map_pow, l154_indAut_pow_eq_one hxN hxp, map_one]
  obtain ⟨x₀, hx₀⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hrq : ¬ (r = 2 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h22⟩
    rw [← hK] at h22
    omega
  obtain ⟨-, hZ, -⟩ := CFSG.RankThree.PartOne.spProj_facts Nat.prime_two hn1 hK hr hrq
  have hx₀p : x₀ ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ
      (by rw [← hx₀]; exact hpow)
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (S ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [l154_centralizer_inv_singleton]
    exact hJ
  have hT := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  have hcompat : ∀ k : PSimple p S,
      θ (MI.indAut p S x hxN k) = MulAut.conj (proj r K x₀) (θ k) := by
    intro k
    rw [← hx₀, hφx]
    simp [MulAut.congr_apply]
  have hJP : GLAPComponent p (fixSubgroup (MulAut.conj (proj r K x₀)))
      ((chevTransfer p S J).map θ.toMonoidHom) :=
    glaPComponent_map_fixSubgroup θ.toMonoidHom
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 θ.injective]; exact bot_le) (MI.indAut p S x hxN) _
      hcompat θ.surjective hp hT
  obtain ⟨D, hDq, hJD, ⟨N, hN, hKline⟩, lab, hΛ, hlt, hD4, hraw⟩ :=
    l154s_block_data hK hn hr hp hp2 x₀ hx₀p hJP
  let Y : StatedSp r K →* StatedSp r K := (conjSp r K U).toMonoidHom.comp
    ((fieldSp r K σ).toMonoidHom.comp (conjSp r K U⁻¹).toMonoidHom)
  let B : GL (Fin r ⊕ Fin r) K := (U : GL (Fin r ⊕ Fin r) K) * glMap σ ((U⁻¹ : gsp r K) :
    GL (Fin r ⊕ Fin r) K)
  have hfield : ∀ g : GL (Fin r ⊕ Fin r) K,
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ g =
        glMap σ g := fun g => rfl
  have hY : ∀ g : StatedSp r K, ((Y g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      B * glMap σ (g : GL (Fin r ⊕ Fin r) K) * B⁻¹ := by
    intro g
    show (U : GL (Fin r ⊕ Fin r) K) *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ
        (((U⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K) * (g : GL (Fin r ⊕ Fin r) K) *
          ((U⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K)⁻¹) * (U : GL (Fin r ⊕ Fin r) K)⁻¹ = _
    rw [hfield, map_mul, map_mul, map_inv]
    simp only [B, Subgroup.coe_inv, mul_inv_rev, inv_inv, map_inv]
    group
  have hψ : ∀ g : StatedSp r K,
      (conjAut r K U * fieldAut r K σ * (conjAut r K U)⁻¹) (proj r K g) = proj r K (Y g) := by
    intro g
    rw [← map_inv]
    rfl
  exact l154s_fieldOn_of_block hp hp2 hSp hyp hJ hJy h2 θ Y B σ hσ hY _ hψ hindy D hDq hJD N hN
    hKline ⟨lab, hΛ, Or.inl hlt, fun h => hD4 h.1, hraw⟩

theorem l154OmegaFld_symp : L154OmegaFld l154Symp := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  exact l154_symp_fieldOn hp hp2 hSp hxp hyp hQ hInn hF hJ hJy

theorem l154FldOn_symp : L154FldOn l154Symp :=
  l154FldOn_of_omega l154OmegaFld_symp

end Certs

section FieldCase


theorem l154NIDOn_symp : L154NIDOn l154Symp :=
  l154NIDOn_of_fldOn l154FldOn_symp

theorem l154TD4On_symp : L154TD4On l154Symp :=
  l154TD4On_of_fldOn l154FldOn_symp

end FieldCase

end CFSG.LocalAnalysis.GLTheoremA.K155XSp
