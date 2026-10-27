module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Kind
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)

open CFSG.StandardType (markTag markRank markChar markDeg)


private theorem label_eq_of_psl_three {lab : GLALabel} {m : ℕ} (ht : markTag lab = .PSL)
    (hr : markRank lab = 3) (hc : markChar lab = 2) (hf : markDeg lab = m) :
    lab = ⟨.A, 2, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  by_cases h3 : r = 3 <;> by_cases h2 : r = 2 <;> cases t <;>
    simp_all [markTag, markRank, markChar, markDeg]

private theorem label_eq_of_psu_three {lab : GLALabel} {m : ℕ} (ht : markTag lab = .PSU)
    (hr : markRank lab = 3) (hc : markChar lab = 2) (hf : markDeg lab = m) :
    lab = ⟨.twA, 2, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  by_cases h3 : r = 3 <;> by_cases h2 : r = 2 <;> cases t <;>
    simp_all [markTag, markRank, markChar, markDeg]

private theorem label_eq_mk {L : GLALabel} {t : CFSG.Assembly.LargeEvenLieTag} {r n : ℕ}
    (ht : L.tag = t) (hr : L.rank = r) (hn : L.n = n) : L = ⟨t, r, n⟩ := by
  obtain ⟨t', r', n'⟩ := L
  subst ht hr hn
  rfl

private theorem even_of_three_dvd_sub {m : ℕ} (h : 3 ∣ 2 ^ m - 1) : Even m := by
  rcases Nat.even_or_odd m with he | ⟨k, rfl⟩
  · exact he
  · exfalso
    have h4 : 2 ^ (2 * k) % 3 = 1 := by
      rw [pow_mul]
      norm_num [Nat.pow_mod]
    have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ]
      generalize 2 ^ (2 * k) = X at h4 ⊢
      omega
    have h2 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
    generalize 2 ^ (2 * k + 1) = X at h h1 h2
    omega

private theorem odd_of_three_dvd_add {m : ℕ} (h : 3 ∣ 2 ^ m + 1) : Odd m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ho
  · exfalso
    have h1 : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul]
      norm_num [Nat.pow_mod]
    generalize 2 ^ (k + k) = X at h h1
    omega
  · exact ho

section Certs


set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem exists_label_of_fieldOn {X S : Subgroup G} {b : G} (hS : GLAPComponent 3 X S)
    (hF : FieldOn 3 b S) (hb3 : b ^ 3 = 1) (hI : Ipart 3 S b ≠ ⊥)
    (hty : catalogIs (PSimple 3 (Ipart 3 S b)) (S265.tyF 3)) :
    ∃ labK : GLALabel, FieldKind (PSimple 3 S) labK (indAut 3 S b hF.1) ∧ ∃ m : ℕ,
      (Even m ∧ 2 ≤ m ∧ canonLabel labK = ⟨.A, 2, 3 * m⟩) ∨
        (Odd m ∧ 3 ≤ m ∧ canonLabel labK = ⟨.twA, 2, 3 * m⟩) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp3 hS
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨labK, -, hnot, hkind⟩ := fieldKind_of_fieldOn hp3 (by decide) hq hF
  have hcore := FR.coreSub_of_fieldOn hp3 (by decide) FR.Res.smallDatum_holds
    (FR.Res.twF4Core_holds hp3 (by decide)) hF (FR.exists_perfect_of_ipart hp3 hF.1 hb3 hI)
  rw [FR.fixSub_indAut hF.1] at hcore
  obtain ⟨E, hEC, hE, hna, hperf, -, -⟩ := hcore
  obtain ⟨J₀, hJ₀, hIeq, hTE⟩ := FR.ipart_single hp3 hF.1 hb3 hE hEC hperf hI
  subst hTE
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hb3
  have hEc := glaPComponent_chevTransfer hp3 hF.1 hap hJ₀
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_chevTransfer hp3 hF.1 hap hJ₀
  obtain ⟨e₂⟩ := FR.nonempty_pSimple_equiv_of_simple hp3 hE hna hEc
  haveI := hE
  obtain ⟨u, v, huv⟩ := hna
  have hZE : Subgroup.center ↥(chevTransfer 3 S J₀) = ⊥ := FR.center_eq_bot_of_simple_nonab huv
  have hEtop : commutator ↥(chevTransfer 3 S J₀) = ⊤ := by
    apply Subgroup.map_injective (chevTransfer 3 S J₀).subtype_injective
    rw [map_commutator_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype, glaPComponent_perfect hEc]
  have hfix : fixSubgroup (indAut 3 S b hF.1) = fixSubgroup (chevAut 3 S ⟨b, hF.1⟩) := by
    have h : indAut 3 S b hF.1 = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h]
    ext y
    rw [mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro hy
      calc chevAut 3 S ⟨b, hF.1⟩ y
          = chevAut 3 S ⟨b, hF.1⟩ ((chevAut 3 S ⟨b, hF.1⟩)⁻¹ y) := by rw [hy]
        _ = y := MulAut.apply_inv_self _ _ _
    · intro hy
      calc (chevAut 3 S ⟨b, hF.1⟩)⁻¹ y
          = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ (chevAut 3 S ⟨b, hF.1⟩ y) := by rw [hy]
        _ = y := MulAut.inv_apply_self _ _ _
  have hEc' : GLAPComponent 3 (fixSubgroup (indAut 3 S b hF.1)) (chevTransfer 3 S J₀) := by
    rw [hfix]
    exact hEc
  have hα3 : indAut 3 S b hF.1 ^ 3 = 1 :=
    chevAut_pow_eq_one 3 S (Subgroup.inv_mem _ hF.1) (by rw [inv_pow, hb3, inv_one])
  let eZ : ↥(chevTransfer 3 S J₀) ≃* ↥(chevTransfer 3 S J₀) ⧸ Subgroup.center ↥(chevTransfer 3 S J₀) :=
    ((QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot).symm
  have hlab : ∀ {t : StatedLieTag} {n : ℕ},
      CFSG.Blueprint.LieModel ↥(chevTransfer 3 S J₀) t 3 2 n →
      ∃ labJ : GLALabel, CFSG.Assembly.LargeEvenInLambda2 labJ ∧ markTag labJ = t ∧
        markRank labJ = 3 ∧ markChar labJ = 2 ∧ markDeg labJ = n ∧
        (canonLabel labK).n = 3 * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
        (canonLabel labK).rank = (canonLabel labJ).rank := by
    intro t n hm
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hEtop
        (CFSG.Blueprint.LieModel.of_mulEquiv eZ hm)
    obtain ⟨_, _, _, _, -, -, -, htJ, hrJ, hcJ, hfJ⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawJ
    have hlJ : Y10F.HasLabel ↥(chevTransfer 3 S J₀) (fun l => l = labJ) :=
      ⟨hEtop, labJ, hlabJ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hrawJ⟩
    exact ⟨labJ, hlabJ, htJ, hrJ, hcJ, hfJ, T158Inn.t158Inn_fldPiece (PSimple 3 S) 3
      (indAut 3 S b hF.1) (chevTransfer 3 S J₀) labK labJ hp3 (by decide) hcen hkind hnot hα3 hlJ hEc'⟩
  rw [hIeq] at hty
  obtain ⟨i, hi, ⟨eT⟩⟩ := hty
  cases i with
  | cyclic _ _ => exact False.elim hi
  | alternating _ _ => exact False.elim hi
  | sporadic _ => exact False.elim hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      have hi' : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1 := hi
      obtain ⟨hr, hq2, h3⟩ := hi'
      obtain rfl : r = 2 := by omega
      have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
      rw [hcard] at h3
      have hcat : catalogIs ↥(chevTransfer 3 S J₀) (I91T.isA2n q.exponent) :=
        ⟨.lie ⟨.A 2 q, hv⟩, ⟨hq2, rfl⟩, ⟨(e₂.symm.trans e₁.symm).trans eT⟩⟩
      obtain ⟨labJ, -, htJ, hrJ, hcJ, hfJ, hn, htag, hrank⟩ :=
        hlab (I91T.lieModel_of_catalogIs_isA2n hcat)
      obtain rfl := label_eq_of_psl_three htJ hrJ hcJ hfJ
      have hev := even_of_three_dvd_sub h3
      have h2 : 2 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hev
        have := q.exponent_pos
        omega
      exact ⟨labK, hkind, q.exponent, Or.inl ⟨hev, h2, label_eq_mk htag hrank hn⟩⟩
    | twistedA r q =>
      have hi' : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1 := hi
      obtain ⟨hr, hq2, h3⟩ := hi'
      obtain rfl : r = 2 := by omega
      have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
      rw [hcard] at h3
      have hcat : catalogIs ↥(chevTransfer 3 S J₀) (S10.isU3n q.exponent) :=
        ⟨.lie ⟨.twistedA 2 q, hv⟩, ⟨hq2, rfl⟩, ⟨(e₂.symm.trans e₁.symm).trans eT⟩⟩
      obtain ⟨labJ, hlabJ, htJ, hrJ, hcJ, hfJ, hn, htag, hrank⟩ :=
        hlab (I91T.lieModel_of_catalogIs_isU3n hcat)
      obtain rfl := label_eq_of_psu_three htJ hrJ hcJ hfJ
      have hod := odd_of_three_dvd_add h3
      have h2 : 2 ≤ q.exponent := hlabJ.2.2 rfl
      have h3' : 3 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hod
        omega
      exact ⟨labK, hkind, q.exponent, Or.inr ⟨hod, h3', label_eq_mk htag hrank hn⟩⟩
    | _ => exact False.elim hi

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
