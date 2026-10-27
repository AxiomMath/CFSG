module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsField
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCentLProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K3Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)

section Model

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem three_le_of_mem_center (h : T29Setup X L x) (hZ3 : Nat.card (center ↥L) ∣ 3)
    (hxZ : x ∈ (center ↥L).map L.subtype) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  haveI hLn : L.Normal := h.normal
  haveI : ((center ↥L).map L.subtype).Normal := normal_map_center_subtype L
  have hcard : Nat.card ↥((center ↥L).map L.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h3
    · exfalso
      apply T29Setup.ne_one h
      have hbot : (center ↥L).map L.subtype = ⊥ := by
        rw [Subgroup.card_eq_one.1 h1, Subgroup.map_bot]
      rw [hbot] at hxZ
      exact Subgroup.mem_bot.1 hxZ
    · exact h3
  exact three_le_of_mem_normal_card_three hcard hxZ h.pRank_top_eq

theorem LModel.not_mem_centralizer (h : T29Setup X L x) (M : LModel L π p f K ν)
    (hZ3 : Nat.card (center ↥L) ∣ 3) : x ∉ centralizer (L : Set X) := by
  intro hxC
  have hc := h.cent
  by_cases hxL : x ∈ L
  · have hxZ : x ∈ (center ↥L).map L.subtype := by
      refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 fun l => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.1 hxC (l : X) l.2
    have := three_le_of_mem_center h hZ3 hxZ
    omega
  · have := M.three_le_of_mem_centralizer (T29Setup.pow_three h) hxL hxC
    omega

theorem LModel.exists_isTypeThree (h : T29Setup X L x) (M : LModel L π p f K ν)
    (hZ3 : Nat.card (center ↥L) ∣ 3) :
    ∃ y : GL (Fin 3) K, IsLiftAt ν x y ∧ IsTypeThree π (p ^ f) K y := by
  haveI hLn : L.Normal := h.normal
  have hx3 := T29Setup.pow_three h
  have hc := h.cent
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  have hxC := M.not_mem_centralizer h hZ3
  rcases M.dichotomy hx3 with ⟨y, hy⟩ | ⟨σ, H, hf⟩
  swap
  · have := M.three_le_of_isFieldAt hx3 hf
    omega
  have hyZ : y ∉ zPi π 3 (p ^ f) K := fun hz =>
    hxC (mem_centralizer_of_isLiftAt M hy
      (mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz))
  have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have h1 := hy.pow M 3
    rw [hx3] at h1
    have h2 := (isLiftAt_one_of_mem_centralizer (ν := ν)
      (one_mem (centralizer (L : Set X)))).inv_mul_mem_zPi M h1
    rwa [inv_one, one_mul] at h2
  obtain ⟨y', ⟨z, hz, rfl⟩, hcases⟩ :=
    exists_lift_cases M.piField M.modThree hτ hτ1 hy.mem hyZ hy3
  have hzH : z ∈ glPi π 3 (p ^ f) K := by
    rw [zPi_eq M.hπ M.hq' hτ hτ1] at hz
    exact (Subgroup.mem_inf.1 hz).1
  have hy' : IsLiftAt ν x (y * z) :=
    hy.mul_scalar hzH (mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz)
  rcases hcases with ⟨g, hg, hD⟩ | ⟨g, hg, e, he, hD⟩ | hT
  rotate_right
  · exact ⟨_, hy', hT⟩
  all_goals exfalso
  all_goals rcases M.cases with hinj | ⟨hZ, hproj⟩
  · by_cases hxL : x ∈ L
    · refine M.false_of_cover_inner h hinj hZ3 hxL fun hxZ => ?_
      have := three_le_of_mem_center h hZ3 hxZ
      omega
    obtain ⟨u, -, hu⟩ := diagTau_eq_diagUnits' hτ
    have := M.three_le_of_cover_diag hinj hx3 hxL hy' hg (one_mem _)
      (by rw [mul_one, hD, hu])
    omega
  · have hC := h.centralizer_eq_bot hZ
    obtain ⟨φ, σ, H, hφ3, hφ⟩ := M.exists_isFieldAt hC h.pRank_top_eq
    refine M.false_of_proj_inner h hproj ?_ hφ3 hφ
    have hin : IsInnerMat π (p ^ f) K (y * z) := by
      refine ⟨g * diagTau hτ * g⁻¹, ?_, 1, one_mem _, ?_⟩
      · exact conj_mem_slPi M.hπ hg (diagTau_mem_slPi M.hπ M.hq' hτ)
      · rw [← hD]
        group
    obtain ⟨l, hl, hlc⟩ := hy'.exists_of_isInnerMat M hin
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hlc
    rw [← hlc]
    exact hl
  · by_cases hxL : x ∈ L
    · refine M.false_of_cover_inner h hinj hZ3 hxL fun hxZ => ?_
      have := three_le_of_mem_center h hZ3 hxZ
      omega
    have := M.three_le_of_cover_diag hinj hx3 hxL hy' hg (one_mem _) (a := e) (b := 1) (c := 1)
      (by rw [mul_one, hD]; rfl)
    omega
  · have hC := h.centralizer_eq_bot hZ
    obtain ⟨φ, σ, H, hφ3, hφ⟩ := M.exists_isFieldAt hC h.pRank_top_eq
    refine M.false_of_proj_inner h hproj ?_ hφ3 hφ
    have h9 := modNine_of_orderOf M.piField M.modThree hφ.order
    have hyZ' : y * z ∉ zPi π 3 (p ^ f) K := fun h' => hyZ (by
      have := mul_mem h' (inv_mem hz)
      rwa [mul_inv_cancel_right] at this)
    have hy3' : (y * z) ^ 3 ∈ zPi π 3 (p ^ f) K := by
      have hc' := commute_of_mem_statedScalars
        (mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz) y
      rw [Commute.mul_pow (show Commute y z from hc') 3]
      exact mul_mem hy3 (pow_mem hz 3)
    have hinner := (rank3II_4_10_two M.piField M.modThree hτ hτ1 hy'.mem hyZ' hy3').2
      (Or.inr ⟨⟨y * z, ⟨1, one_mem _, (mul_one _).symm⟩, g, hg, e, he, hD⟩, h9⟩)
    obtain ⟨l, hl, hlm⟩ := hinner
    obtain ⟨μ, hμH, hμ, -⟩ := exists_det_eq_cube_of_inner M.piField M.modThree hy'.mem hl hlm
    obtain ⟨l', hl', hlc⟩ := hy'.exists_of_isInnerMat M ⟨l, hl, _, ⟨μ, rfl⟩, hμ⟩
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hlc
    rw [← hlc]
    exact hl'

theorem LModel.t29_concl (h : T29Setup X L x) (M : LModel L π p f K ν)
    (hZ3 : Nat.card (center ↥L) ∣ 3) :
    InducesInnDiagNonInner L x ∧ CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) ∧
      ((∃ y : X, IsPGroup 3 (zpowers y) ∧ InducesNontrivialFieldAut L y) ∨
        9 ≤ Nat.card (CFSG.pCore 3 X)) := by
  haveI hLn : L.Normal := h.normal
  have hx3 := T29Setup.pow_three h
  have hcore := h.gLAPPrimeCore_eq_bot
  obtain ⟨y, hy, hT⟩ := M.exists_isTypeThree h hZ3
  have hxL := M.not_mem_of_isTypeThree hy hT
  have hpg : ∀ φ : X, φ ^ 3 = 1 → IsPGroup 3 (zpowers φ) := fun φ hφ3 g => by
    obtain ⟨g, hg⟩ := g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφ3, one_zpow]
  refine ⟨M.inducesInnDiagNonInner_of_isTypeThree hcore hy hT, ?_, ?_⟩
  · rcases M.cases with hinj | ⟨-, hproj⟩
    · obtain ⟨v, hvZ, hv3, hv1, hvx, hall⟩ := M.commute_of_cover hinj hZ3 hy hT
      have hvL : v ∈ L := Subgroup.map_subtype_le _ hvZ
      exact hasNormalPComplement_of_pair h.cent hx3 hv3 hv1 hvx
        (fun h' => hxL ((zpowers_le.2 hvL) h')) fun g hg _ => hall g hg
    · obtain ⟨v, hvL, hv3, hv1, hvx, hall⟩ := M.commute_of_proj hproj hxL hx3 hy hT
      exact hasNormalPComplement_of_pair h.cent hx3 hv3 hv1 hvx
        (fun h' => hxL ((zpowers_le.2 hvL) h')) hall
  · rcases M.cases with hinj | ⟨hZ, -⟩
    · by_cases h9 : 9 ≤ Nat.card (CFSG.pCore 3 X)
      · exact Or.inr h9
      by_cases hf : ∃ (φ : X) (σ : K ≃+* K) (H : GL (Fin 3) K), φ ^ 3 = 1 ∧ IsFieldAt ν φ σ H
      · obtain ⟨φ, σ, H, hφ3, hφ⟩ := hf
        exact Or.inl ⟨φ, hpg φ hφ3, inducesNontrivialFieldAut_of_isFieldAt M hcore hφ⟩
      push Not at hf
      exact absurd (M.false_of_no_field_cover hinj
        (T29Setup.centralizer_le_of_card_pCore h (by omega)) h.pRank_top_eq hx3 hy hT
        fun φ σ H hφ3 => hf φ σ H hφ3) id
    · obtain ⟨φ, σ, H, hφ3, hφ⟩ := M.exists_isFieldAt (h.centralizer_eq_bot hZ) h.pRank_top_eq
      exact Or.inl ⟨φ, hpg φ hφ3, inducesNontrivialFieldAut_of_isFieldAt M hcore hφ⟩

end Model

section Certificates


theorem t29LThreeEpsCase_holds : T29LThreeEpsCase := by
  intro X _ _ L x h hT hZ3
  obtain ⟨π, p, f, K, _, ν, M⟩ := exists_lModel h.comp.2.2 hT hZ3
  exact M.t29_concl h hZ3

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
