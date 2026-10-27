module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Omega
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
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
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open scoped commutatorElement

theorem l154_J_equiv_abstract {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {y : Ω}
    {X J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hJ : GLAPComponent p X J) (hJS : J ≤ S)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) {P : Type} [Group P] (θ : PSimple p S ≃* P) (ψ : MulAut P)
    (hindy : LargeEvenInduces θ (indRel p S y) ψ) {G₁ R₁ : Type} [Group G₁] [Group R₁] (Ψ : G₁ →* P)
    (q₁ : G₁ →* R₁) (hq₁s : Function.Surjective q₁) (hq₁k : q₁.ker ≤ Subgroup.center G₁)
    (hR₁ : IsSimpleGroup R₁) (hker : ∀ m, Ψ m = 1 → q₁ m = 1)
    (hJP : ∀ z : P, z ∈ (chevTransfer p S J).map θ.toMonoidHom ↔ ∃ m, Ψ m = z) :
    ∃ e₀ : PSimple p J ≃* R₁, ∀ m : G₁, ∃ m' : G₁,
      MulAut.congr e₀ (MI.indAut p J y hJy) (q₁ m) = q₁ m' ∧ Ψ m' = ψ (Ψ m) := by
  classical
  let ρS : ↥S →* P := θ.toMonoidHom.comp (chevQuotHom p S)
  let ρJ : ↥J →* P := ρS.comp (Subgroup.inclusion hJS)
  have hperfJ : commutator ↥J = ⊤ := by
    have h1 := Subgroup.map_subtype_commutator J
    rw [glaPComponent_perfect hJ] at h1
    have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)
  have hρJmem : ∀ l : ↥J, ρJ l ∈ (chevTransfer p S J).map θ.toMonoidHom := by
    intro l
    refine Subgroup.mem_map.2 ⟨chevQuotHom p S ⟨l.1, hJS l.2⟩, ?_, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hmemJP : ∀ z ∈ (chevTransfer p S J).map θ.toMonoidHom, ∃ l : ↥J, ρJ l = z := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hc
    exact ⟨⟨s.1, Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩
  have hρΨ : ∀ l : ↥J, ∃ m, Ψ m = ρJ l := fun l => (hJP _).1 (hρJmem l)
  have hΨρ : ∀ m, ∃ l : ↥J, ρJ l = Ψ m := fun m => hmemJP _ ((hJP _).2 ⟨m, rfl⟩)
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift ρJ Ψ q₁ hρΨ hker
  have hΘsurj : Function.Surjective Θ := by
    intro r
    obtain ⟨m, rfl⟩ := hq₁s r
    obtain ⟨l, hl⟩ := hΨρ m
    exact ⟨l, hΘ l m hl.symm⟩
  have hρJker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : chevQuotHom p S ⟨l.1, hJS l.2⟩ = 1 := by
      have : θ (chevQuotHom p S ⟨l.1, hJS l.2⟩) = 1 := hl
      exact (map_eq_one_iff _ θ.injective).1 this
    have h2 : (QuotientGroup.mk (⟨l.1, hJS l.2⟩ : ↥S) : PQuot p S) ∈ Subgroup.center (PQuot p S) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ∀ s : ↥S, s * ⟨l.1, hJS l.2⟩ = ⟨l.1, hJS l.2⟩ * s := by
      intro s
      have h4 := Subgroup.mem_center_iff.1 h2 (QuotientGroup.mk s)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hSp, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4 |>.symm ▸ rfl
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h5 := h3 ⟨j.1, hJS j.2⟩
    show (j : Ω) * (l : Ω) = (l : Ω) * (j : Ω)
    exact congrArg Subtype.val h5
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨m, hm⟩ := hρΨ l
    have hqm : q₁ m = 1 := by rw [← hΘ l m hm]; exact hl
    have hmc : m ∈ Subgroup.center G₁ := hq₁k (MonoidHom.mem_ker.2 hqm)
    refine mem_center_of_commutator_mem_center hperfJ fun j => ?_
    apply hρJker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    obtain ⟨m', hm'⟩ := hρΨ j
    rw [← hm, ← hm', ← map_commutatorElement]
    have : ⁅m, m'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hmc m').symm
    rw [this, map_one]
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hR₁ Θ hΘsurj hΘker
  refine ⟨e₀, fun m => ?_⟩
  obtain ⟨l, hl⟩ := hΨρ m
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hJy
  have hl'mem : y⁻¹ * (l : Ω) * y ∈ J := by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, hl'mem⟩
  have hρl' : ρJ l' = ψ (ρJ l) :=
    (hindy (QuotientGroup.mk ⟨l.1, hJS l.2⟩) (QuotientGroup.mk ⟨l'.1, hJS l'.2⟩)
      ⟨⟨l.1, hJS l.2⟩, ⟨l'.1, hJS l'.2⟩, rfl, rfl, rfl⟩).symm
  obtain ⟨m', hm'⟩ := hρΨ l'
  refine ⟨m', ?_, ?_⟩
  · have e1 : q₁ m = e₀ (QuotientGroup.mk (QuotientGroup.mk l)) := by
      rw [he₀ l]
      exact (hΘ l m hl.symm).symm
    have e2 : q₁ m' = e₀ (QuotientGroup.mk (QuotientGroup.mk l')) := by
      rw [he₀ l']
      exact (hΘ l' m' hm').symm
    have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk l') :=
      MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, rfl⟩
    rw [e1, e2, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, e3]
  · rw [hm', hρl', hl]

end CFSG.LocalAnalysis.GLTheoremA.K155X
