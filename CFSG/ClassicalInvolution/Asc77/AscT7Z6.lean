module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z3
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.Asc77.AscIHLie
public import CFSG.ClassicalInvolution.Asc77.AscT7Z4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]


structure PSLLayer (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Φ : Set (Subgroup G)) where
  ψ : (modelUniv .PSL 4 p f Fact.out).K →* G
  ker_le : ψ.ker ≤ Subgroup.center (modelUniv .PSL 4 p f Fact.out).K
  range_eq : ψ.range = omegaGen Φ
  fund : ∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D,
    L = R.map ψ

theorem admissible_psl4 (hq : 5 ≤ p ^ f) : StatedLieAdmissible .PSL 4 p f := by
  refine ⟨Fact.out, ?_, by norm_num, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  · simp
  · simp

theorem nonempty_pslLayer_of_omegaLie {Φ : Set (Subgroup G)} (D : OmegaLie p f Φ)
    (hcard : D.card = 1) (i : Fin D.card) (hit : D.tag i = .PSL) (hir : D.rank i = 4)
    (hie : D.exp i = f) : Nonempty (PSLLayer p f Φ) := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  have key : ∀ (t : StatedLieTag) (k e : ℕ) (ψ : (modelUniv t k p e Fact.out).K →* G),
      t = .PSL → k = 4 → e = f → ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
      ψ.range = omegaGen Φ →
      (∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, L = R.map ψ) →
      Nonempty (PSLLayer p f Φ) := by
    rintro t k e ψ rfl rfl rfl hker hr hf
    exact ⟨⟨ψ, hker, hr, hf⟩⟩
  refine key _ _ _ (D.hom i) hit hir hie (D.ker_le_center i) ?_ ?_
  · have h1 : ⨆ j, (D.hom j).range = (D.hom i).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j i])
        (le_iSup (fun j => (D.hom j).range) i)
    rw [← h1]
    exact D.generate
  · intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Subsingleton.elim j i
    exact ⟨R, hR, hLR⟩

namespace PSLLayer

variable {Φ : Set (Subgroup G)} (P : PSLLayer p f Φ)

theorem finite_U (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Finite (modelUniv .PSL 4 p f Fact.out).K :=
  ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) (admissible_psl4 hq)

theorem perfect_U : Group.IsPerfect (modelUniv .PSL 4 p f Fact.out).K :=
  CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (n := 4) (by norm_num)

theorem injOn_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {L : Subgroup G}
    {R : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hLR : L = R.map P.ψ) (eL : Nonempty (↥L ≃* SL(2, GaloisField p f))) :
    ∀ x ∈ R, P.ψ x = 1 → x = 1 := by
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    (n := 4) (by trivial) (admissible_psl4 hq) (by decide) (by decide) hR
  obtain ⟨e₂⟩ := eL
  have := finite_U (p := p) (f := f) hp2 hq
  intro x hx hψ
  refine eq_one_of_map_eq_one_of_card_eq P.ψ ?_ hx hψ
  rw [← hLR]
  exact (Nat.card_congr e₂.toEquiv).trans (Nat.card_congr e₁.toEquiv).symm


theorem pair_of_member (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Φ : Set (Subgroup G)}
    (P : PSLLayer p f Φ) {K K' L : Subgroup G}
    {RK RK' : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hL : L ∈ Φ)
    (eK : Nonempty (↥K ≃* SL(2, GaloisField p f)))
    (eL : Nonempty (↥L ≃* SL(2, GaloisField p f))) {z t e a b : G}
    (hzK : IsUniqueInvolution K z) (htL : IsUniqueInvolution L t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (he : e ∈ omegaGen Φ)
    (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e) (hne : K ≠ L)
    (hnc : ¬ Commutes K L) :
    ∃ RL : Subgroup (modelUniv .PSL 4 p f Fact.out).K,
      RL ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D ∧ L = RL.map P.ψ ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W RK RL) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W K L := by
  obtain ⟨RL, hRL, hLR⟩ := P.fund L hL
  have have_perf := perfect_U (p := p) (f := f)
  have := finite_U (p := p) (f := f) hp2 hq
  have hU : (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K),
        (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K)⁆ :=
    (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K))).ge
  have hR₁ : RK ≤ ⁅RK, RK⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) (admissible_psl4 hq)
      (by omega) RK hRK
  have hi₁ := P.injOn_fund hp2 hq hRK hKR eK
  have hi₃ := P.injOn_fund hp2 hq hRL hLR eL
  have hcomm' : Commutes (RK.map P.ψ) (RK'.map P.ψ) := by
    rw [← hKR, ← hKR']
    exact hcomm
  obtain ⟨c₁, hc₁, c₂, hc₂, ho₁, ho₂, -, -, hcc⟩ := exists_commuting_lifts P.ψ P.ker_le hU hR₁
    hi₁ hi₃ (hKR ▸ ha) (hKR' ▸ hb) hcomm' (P.range_eq ▸ he)
    (fun y hy => hec y (P.range_eq ▸ hy)) haa hzK.sq hzK.ne_one (hLR ▸ htL.mem) htab htL.sq
    htL.ne_one
  have hne' : RK.map P.ψ ≠ RL.map P.ψ := by
    rw [← hKR, ← hLR]
    exact hne
  have hnc' : ¬ Commutes (RK.map P.ψ) (RL.map P.ψ) := by
    rw [← hKR, ← hLR]
    exact hnc
  obtain ⟨h1, h2⟩ := psl_pair_of_lifts hp2 hq (admissible_psl4 hq) P.ψ P.ker_le hRK hRL hc₁ hc₂
    ho₁ ho₂ hcc hne' hnc'
  exact ⟨RL, hRL, hLR, h1, by rw [← hKR, ← hLR] at h2; exact h2⟩

theorem sup_eq_omegaGen (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Φ : Set (Subgroup G)}
    (P : PSLLayer p f Φ) {K J J' : Subgroup G}
    {RK RJ RJ' : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hRJ' : RJ' ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hJR : J = RJ.map P.ψ) (hJ'R : J' = RJ'.map P.ψ)
    (h1 : ∃ W, LinearBlockStandardPair (GaloisField p f) W RJ' RK)
    (h2 : ∃ W, LinearBlockStandardPair (GaloisField p f) W RK RJ) (hc : Commutes J J') :
    J' ⊔ K ⊔ J = omegaGen Φ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf0⟩
  have := finite_U (p := p) (f := f) hp2 hq
  have have_perf := perfect_U (p := p) (f := f)
  have have_perf' : Group.IsPerfect SL(4, GaloisField p f) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (n := 4) (by norm_num)
  have hR₃ : RJ' ≤ ⁅RJ', RJ'⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) (admissible_psl4 hq) (by omega) RJ' hRJ'
  have hcomm : Commutes RJ' RJ := by
    refine commutes_of_map_commutes P.ψ P.ker_le hR₃ ?_
    rw [← hJR, ← hJ'R]
    exact hc.symm
  have htop : RJ' ⊔ RK ⊔ RJ = ⊤ :=
    sup_eq_top_of_chain (F := GaloisField p f) Fact.out (GaloisField.card p f hf0) (by omega)
      h1 h2 hcomm
  rw [hKR, hJR, hJ'R, ← Subgroup.map_sup, ← Subgroup.map_sup, htop, Subgroup.map_top,
    P.range_eq]

end PSLLayer

end T7Z

end CFSG.ClassicalInvolution.Asc77
