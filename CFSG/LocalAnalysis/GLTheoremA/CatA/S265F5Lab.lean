module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)

open CFSG.StandardType (markTag markRank markChar markDeg)


private theorem label_eq_of_psl_prime {lab : GLALabel} {p m : ℕ} (hp2 : p ≠ 2) (hp4 : p ≠ 4)
    (ht : markTag lab = .PSL) (hr : markRank lab = p) (hc : markChar lab = 2)
    (hf : markDeg lab = m) : lab = ⟨.A, p - 1, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  by_cases h3 : r = 3 <;> by_cases h2 : r = 2 <;> cases t <;>
    simp_all [markTag, markRank, markChar, markDeg] <;> omega

private theorem label_eq_of_psu_prime {lab : GLALabel} {p m : ℕ} (hp2 : p ≠ 2) (hp4 : p ≠ 4)
    (ht : markTag lab = .PSU) (hr : markRank lab = p) (hc : markChar lab = 2)
    (hf : markDeg lab = m) : lab = ⟨.twA, p - 1, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  by_cases h3 : r = 3 <;> by_cases h2 : r = 2 <;> cases t <;>
    simp_all [markTag, markRank, markChar, markDeg] <;> omega

private theorem label_eq_mk_aux {L : GLALabel} {t : CFSG.Assembly.LargeEvenLieTag} {r n : ℕ}
    (ht : L.tag = t) (hr : L.rank = r) (hn : L.n = n) : L = ⟨t, r, n⟩ := by
  obtain ⟨t', r', n'⟩ := L
  subst ht hr hn
  rfl

section Certs


set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem exists_label_of_fieldOn_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {X S : Subgroup G} {b : G} (hS : GLAPComponent p X S) (hF : FieldOn p b S) (hbp : b ^ p = 1)
    (hI : Ipart p S b ≠ ⊥) (hty : catalogIs (PSimple p (Ipart p S b)) (S265.tyF p)) :
    ∃ labK : GLALabel, FieldKind (PSimple p S) labK (indAut p S b hF.1) ∧ ∃ m : ℕ, 2 ≤ m ∧
      ((p ∣ 2 ^ m - 1 ∧ canonLabel labK = ⟨.A, p - 1, p * m⟩) ∨
        (p ∣ 2 ^ m + 1 ∧ canonLabel labK = ⟨.twA, p - 1, p * m⟩)) := by
  classical
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp hS
  have hcen : Subgroup.center (PSimple p S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨labK, -, hnot, hkind⟩ := S265F3.fieldKind_of_fieldOn hp hp2 hq hF
  have hcore := FR.coreSub_of_fieldOn hp hp2 FR.Res.smallDatum_holds
    (FR.Res.twF4Core_holds hp hp2) hF (FR.exists_perfect_of_ipart hp hF.1 hbp hI)
  rw [FR.fixSub_indAut hF.1] at hcore
  obtain ⟨E, hEC, hE, hna, hperf, -, -⟩ := hcore
  obtain ⟨J₀, hJ₀, hIeq, hTE⟩ := FR.ipart_single hp hF.1 hbp hE hEC hperf hI
  subst hTE
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hEc := glaPComponent_chevTransfer hp hF.1 hap hJ₀
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hF.1 hap hJ₀
  obtain ⟨e₂⟩ := FR.nonempty_pSimple_equiv_of_simple hp hE hna hEc
  haveI := hE
  obtain ⟨u, v, huv⟩ := hna
  have hZE : Subgroup.center ↥(chevTransfer p S J₀) = ⊥ := FR.center_eq_bot_of_simple_nonab huv
  have hEtop : commutator ↥(chevTransfer p S J₀) = ⊤ := by
    apply Subgroup.map_injective (chevTransfer p S J₀).subtype_injective
    rw [map_commutator_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      glaPComponent_perfect hEc]
  have hfix : fixSubgroup (indAut p S b hF.1) = fixSubgroup (chevAut p S ⟨b, hF.1⟩) := by
    have h : indAut p S b hF.1 = (chevAut p S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h]
    ext y
    rw [mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro hy
      calc chevAut p S ⟨b, hF.1⟩ y
          = chevAut p S ⟨b, hF.1⟩ ((chevAut p S ⟨b, hF.1⟩)⁻¹ y) := by rw [hy]
        _ = y := MulAut.apply_inv_self _ _ _
    · intro hy
      calc (chevAut p S ⟨b, hF.1⟩)⁻¹ y
          = (chevAut p S ⟨b, hF.1⟩)⁻¹ (chevAut p S ⟨b, hF.1⟩ y) := by rw [hy]
        _ = y := MulAut.inv_apply_self _ _ _
  have hEc' : GLAPComponent p (fixSubgroup (indAut p S b hF.1)) (chevTransfer p S J₀) := by
    rw [hfix]
    exact hEc
  have hαp : indAut p S b hF.1 ^ p = 1 :=
    chevAut_pow_eq_one p S (Subgroup.inv_mem _ hF.1) (by rw [inv_pow, hbp, inv_one])
  let eZ : ↥(chevTransfer p S J₀) ≃*
      ↥(chevTransfer p S J₀) ⧸ Subgroup.center ↥(chevTransfer p S J₀) :=
    ((QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot).symm
  have hlab : ∀ {t : StatedLieTag} {n : ℕ},
      CFSG.Blueprint.LieModel ↥(chevTransfer p S J₀) t p 2 n →
      ∃ labJ : GLALabel, CFSG.Assembly.LargeEvenInLambda2 labJ ∧ markTag labJ = t ∧
        markRank labJ = p ∧ markChar labJ = 2 ∧ markDeg labJ = n ∧
        (canonLabel labK).n = p * (canonLabel labJ).n ∧
        (canonLabel labK).tag = (canonLabel labJ).tag ∧
        (canonLabel labK).rank = (canonLabel labJ).rank := by
    intro t n hm
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hEtop
        (CFSG.Blueprint.LieModel.of_mulEquiv eZ hm)
    obtain ⟨_, _, _, _, -, -, -, htJ, hrJ, hcJ, hfJ⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawJ
    have hlJ : Y10F.HasLabel ↥(chevTransfer p S J₀) (fun l => l = labJ) :=
      ⟨hEtop, labJ, hlabJ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hrawJ⟩
    exact ⟨labJ, hlabJ, htJ, hrJ, hcJ, hfJ, T158Inn.t158Inn_fldPiece (PSimple p S) p
      (indAut p S b hF.1) (chevTransfer p S J₀) labK labJ hp hp2 hcen hkind hnot hαp hlJ hEc'⟩
  rw [hIeq] at hty
  obtain ⟨d, hv, hP, ⟨eT⟩⟩ := CatB.exists_lieIndex hty
  have eE := (e₂.symm.trans e₁.symm).trans eT
  cases d with
  | A r q =>
    obtain ⟨hr, hq2, hpq⟩ : r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card - 1 := hP
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    rw [hcard] at hpq
    have hm := (CFSG.Models.lieModel_A r q hv eE).toBlueprint (by decide)
    rw [hr, hq2] at hm
    obtain ⟨labJ, -, htJ, hrJ, hcJ, hfJ, hn, htag, hrank⟩ := hlab hm
    obtain rfl := label_eq_of_psl_prime hp2 hp4 htJ hrJ hcJ hfJ
    have h2 : 2 ≤ q.exponent := by
      have h1 := q.exponent_pos
      by_contra hlt
      have he1 : q.exponent = 1 := by omega
      have h21 : (2 : ℕ) ^ 1 - 1 = 1 := by norm_num
      rw [he1, h21] at hpq
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpq)
    exact ⟨labK, hkind, q.exponent, h2, Or.inl ⟨hpq, label_eq_mk_aux htag hrank hn⟩⟩
  | twistedA r q =>
    obtain ⟨hr, hq2, hpq⟩ : r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card + 1 := hP
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    rw [hcard] at hpq
    have hm := (CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' r q hv eE).toBlueprint
      (by decide)
    rw [hr, hq2] at hm
    obtain ⟨labJ, -, htJ, hrJ, hcJ, hfJ, hn, htag, hrank⟩ := hlab hm
    obtain rfl := label_eq_of_psu_prime hp2 hp4 htJ hrJ hcJ hfJ
    have h2 : 2 ≤ q.exponent := by
      have h1 := q.exponent_pos
      by_contra hlt
      have he1 : q.exponent = 1 := by omega
      have h21 : (2 : ℕ) ^ 1 + 1 = 3 := by norm_num
      rw [he1, h21] at hpq
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq)
    exact ⟨labK, hkind, q.exponent, h2, Or.inr ⟨hpq, label_eq_mk_aux htag hrank hn⟩⟩
  | _ => exact False.elim hP

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
