module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZTwoA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZTwoB
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271.TabMFive

section Griess


theorem not_two_pow_five_dvd_MGriess
    (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder)
    {z d : MGriess} (hz : orderOf z = 7) (hd : orderOf d = 7)
    (hzd : ∀ (g : MGriess) (m : ℕ), g * z * g⁻¹ ≠ d ^ m)
    (htA : ∃ t : MGriess, orderOf t = 2 ∧ t * d = d * t ∧
      Nat.card ↥(Subgroup.centralizer ({t} : Set MGriess)) = 2 * CFSG.Open.monsterBabyOrder)
    (huB : ∃ u : MGriess, orderOf u = 2 ∧ u * d = d * u ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess)) = twoBCentralizerOrder ∧
      35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess) ⊓
        Subgroup.centralizer ({d} : Set MGriess))) :
    ¬ 2 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set MGriess)) := by
  obtain ⟨⟨hfin, -, -, -⟩, -⟩ := id hE
  haveI : Finite MGriess := hfin
  refine tabMSeven_not_dvd_of_involutions (by norm_num) fun v hvz hv => ?_
  have hzv : v * z = z * v := Subgroup.mem_centralizer_singleton_iff.1 hvz
  rcases hcls_of_existence hE hB v hv with hvA | hvB
  ·
    exfalso
    obtain ⟨t, ht, htd, htc⟩ := htA
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_card_twoA hE hv ht hvA htc)
    have hty : t * (c * z * c⁻¹) = (c * z * c⁻¹) * t := by
      rw [← hc]
      calc c * v * c⁻¹ * (c * z * c⁻¹) = c * (v * z) * c⁻¹ := by group
        _ = c * (z * v) * c⁻¹ := by rw [hzv]
        _ = c * z * c⁻¹ * (c * v * c⁻¹) := by group
    have hyz : orderOf (c * z * c⁻¹) = 7 := by rw [orderOf_conj_eq, hz]
    obtain ⟨g, m, hg⟩ := exists_conj_pow_of_twoA hE ht htc hd htd hyz hty
    exact hzd (g * c) m (by rw [← hg]; group)
  ·
    obtain ⟨u, hu, hud, huc, hud'⟩ := huB
    rw [inf_comm]
    rcases card_dvd_or_conj_of_twoB hE hB hd hu hud huc hud' hv hvB hz hzv with h | ⟨g, m, hg⟩
    · intro h32
      exact absurd (h32.trans h) (by norm_num)
    · exact absurd hg (hzd g m)

end Griess

section Gmat


open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG)

theorem tabMSeven_not_two_pow_five_dvd
    {z : Gmat} (hz : orderOf z = 7)
    (hzd : ∀ (g : Gmat) (m : ℕ), g * z * g⁻¹ ≠ dG ^ m)
    (htA : ∃ t : Gmat, orderOf t = 2 ∧ t * dG = dG * t ∧
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder)
    (huB : ∃ u : Gmat, orderOf u = 2 ∧ u * dG = dG * u ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) =
        CFSG.Monster.Existence.twoBCentralizerOrder ∧
      35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
        Subgroup.centralizer ({dG} : Set Gmat))) :
    ¬ 2 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  have hB := card_nativeB
  let e : MGriess ≃* ↥Gmat :=
    CFSG.YGroups.Y443.griessEquivGmat CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  have hdG : orderOf dG = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime CFSG.AGLEmbedding.Norton.MON5_7.dG_pow
      CFSG.AGLEmbedding.Norton.MON5_7.dG_ne_one
  have h := not_two_pow_five_dvd_MGriess hE hB (z := e.symm z) (d := e.symm dG)
    (by rw [MulEquiv.orderOf_eq]; exact hz) (by rw [MulEquiv.orderOf_eq]; exact hdG)
    (fun g m hgm => hzd (e g) m (by
      have h1 := congrArg e hgm
      rwa [map_mul, map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at h1))
    (by
      obtain ⟨t, ht, htd, htc⟩ := htA
      refine ⟨e.symm t, by rw [MulEquiv.orderOf_eq]; exact ht, ?_, ?_⟩
      · rw [← map_mul, ← map_mul, htd]
      · rw [← natCard_centralizer_map e, MulEquiv.apply_symm_apply]
        exact htc)
    (by
      obtain ⟨u, hu, hud, huc, hud'⟩ := huB
      refine ⟨e.symm u, by rw [MulEquiv.orderOf_eq]; exact hu, ?_, ?_, ?_⟩
      · rw [← map_mul, ← map_mul, hud]
      · rw [← natCard_centralizer_map e, MulEquiv.apply_symm_apply]
        exact huc
      · rw [← natCard_centralizer_inf_map e, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
        exact hud')
  rwa [← natCard_centralizer_map e, MulEquiv.apply_symm_apply] at h

end Gmat

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
