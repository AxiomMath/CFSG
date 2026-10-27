module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GU
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.Open (genFittingFStar)
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

namespace E3S3Gen

theorem exists_conj_psu3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {a b : StatedProj (StatedSU 3 (p ^ f) K)} (ha : orderOf a = 2)
    (hb : orderOf b = 2) : ∃ g : StatedProj (StatedSU 3 (p ^ f) K), g * a * g⁻¹ = b := by
  set φ := ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := 3) (by norm_num) with hφ
  have hφa := RankThree.Classical.isConj_unitaryProj_unitaryInvT h hp2 (s := φ.symm a)
    (by rw [MulEquiv.orderOf_eq]; exact ha)
  have hφb := RankThree.Classical.isConj_unitaryProj_unitaryInvT h hp2 (s := φ.symm b)
    (by rw [MulEquiv.orderOf_eq]; exact hb)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hφa.trans hφb.symm)
  refine ⟨φ g, ?_⟩
  have h1 := congrArg φ hg
  rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

end E3S3Gen

theorem e3S3GenU3_proved : E3S3GenU3 := by
  intro X _ _ hsimp p f hp hp2 hl t s ht hs htN hsN hts hne
  have := hsimp
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hl
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq : (3, p ^ f) ≠ (3, 2) := by
    intro h32
    have h2 : p ^ f = 2 := congrArg Prod.snd h32
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
    omega
  have hsP : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
    ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl hq
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar X)) with
      h0 | h0
    · exact h0
    · exfalso
      have hsub : Subsingleton (FStarQuot X) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        exact QuotientGroup.eq.mpr (by rw [h0]; exact Subgroup.mem_top _)
      have : Nontrivial (StatedProj (StatedSU 3 (p ^ f) K)) := hsP.toNontrivial
      exact not_subsingleton _ e₀.symm.injective.subsingleton
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv hZ
  exact E3S3Gen.sup_centralizer_eq_top_of_normal (eF.trans e₀)
    (fun a b ha hb hab hab' => E3C269G.sup_centralizer_eq_top_psu3 h hp2 ha hb hab hab')
    (fun a b ha hb => E3S3Gen.exists_conj_psu3 h hp2 ha hb) htN hsN ht hs hts hne

end CFSG.ClassicalInvolution.Q3.TL4
