module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.LieRank.U43
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Module
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Transport
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.LieRank CFSG.HardMathSupport.Solomon.LocalBalance

theorem isHatSix_of_cover {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hZ : Nat.card (Subgroup.center K) = 3) {X : Type} [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (hm : CFSG.Models.LieModel X .PSL 2 3 2) : IsHatSix K := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hcl
  have e2 : X ≃* CFSG.GorensteinWalter.PSL2 F :=
    e'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  obtain ⟨a6⟩ := CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine
    (F := F) (by rw [hF]; norm_num)
  exact ⟨hq.1, hZ, ⟨(e.trans e2).trans a6⟩⟩

theorem six_le_pRank_of_O7 {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hZ : Nat.card (Subgroup.center K) = 3) {X : Type} [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (hm : CFSG.Models.LieModel X .POmegaOdd 3 3 1) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hB : CFSG.Blueprint.LieModel X .POmegaOdd 3 3 1 := by
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
    · exact Or.inl ⟨by decide, hcl⟩
    · exact absurd h0 (by norm_num)
  obtain ⟨e1⟩ := nonempty_mulEquiv_openOmega_of_lieModel hB
  have e' : K ⧸ Subgroup.center K ≃* O7.Om7 := (e.trans e1).trans O7.ProjEquivOm7
  have := CFSG.HardMathSupport.Timmesfeld.SporadicRank.lower_of_cover hq e'
    (by rw [hZ]; norm_num) (by rw [hZ]) O7.modSpec O7.noAlt_O7 O7.noFun_O7
  have hn : O7.modSpec.n = 5 := rfl
  omega

theorem five_le_pRank_of_U43 {K : Type} [Group K] [Finite K]
    (hZ : Nat.card (Subgroup.center K) = 3) {X : Type} [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (hm : CFSG.Models.LieModel X .PSU 4 3 1) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨e1⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.nonempty_mulEquiv_X₀_of_classical
    hcl
  have e' := e.trans e1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : K →* CFSG.LieType.Multipliers.U43.X₀ :=
    (e' : K ⧸ Subgroup.center K →* _).comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    simp [φ]
  refine five_le_pRank_of_cover φ hφ hker.le (Z := Subgroup.center K) hker.ge
    (fun z hz => ?_) (by rw [hZ])
  have : (⟨z, hz⟩ : Subgroup.center K) ^ 3 = 1 := by
    rw [← hZ]
    exact pow_card_eq_one'
  simpa using congrArg (fun w : Subgroup.center K => (w : K)) this

theorem isHatGTwoThree_of_cover {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ : Nat.card (Subgroup.center K) = 3) {X : Type} [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (hm : CFSG.Models.LieModel X .G2 0 3 1) :
    IsHatGTwoThree K := by
  obtain ⟨-, hcl | ⟨-, d, hd, ⟨φ⟩⟩⟩ := hm
  · exact hcl.2.elim
  obtain ⟨idx, hv⟩ := d
  cases idx <;> simp only [CFSG.Models.NamesTag] at hd
  rename_i q
  refine ⟨hq.1, hZ, q, ⟨.G2 q, hv⟩, ?_, rfl, ⟨e.trans φ⟩⟩
  rw [TauCeti.PrimePower.card_def, hd.1, hd.2]
  norm_num

end CFSG.HardMathSupport.Solomon.Coordinator
