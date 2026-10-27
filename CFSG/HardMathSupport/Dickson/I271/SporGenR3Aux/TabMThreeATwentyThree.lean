module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

theorem dvd_card_centralizer_inf_yMc
    (hG : Gmat = AutO) (h : (yMc hG).ker ≤ yJ.ker) {ζ : MGriess}
    (hζ3 : orderOf ζ = 3) (hDζ : (yMc hG).range ≤ Subgroup.centralizer ({ζ} : Set MGriess))
    (hker : ∀ d : ↥(yMc hG).range, coverHom (yMc hG) yJ h d = 1 ↔
      (d : MGriess) ∈ Subgroup.zpowers ζ) :
    23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ} : Set MGriess)) := by
  have hl : yW23.length % 2 = 0 := by decide +kernel
  have hc : ∀ c ∈ yW23, c < 11 := by decide +kernel
  have h4 : 4 ∉ yW23 := by decide +kernel
  have hmv : yW23 ∈ yMoves := by
    unfold yMoves
    exact List.mem_cons_self
  let v := yWordC yW23 hl hc
  have hv23 : yKM (v : YGroup 4 4 2) ^ 23 = 1 := yKM_yW23_pow
  have hv1 : yKM (v : YGroup 4 4 2) ≠ 1 := yKM_yMoves hmv
  have hw23 : yMc hG v ^ 23 ∈ Subgroup.zpowers ζ := by
    have h1 : coverHom (yMc hG) yJ h ((yMc hG).rangeRestrict (v ^ 23)) = 1 := by
      rw [coverHom_rangeRestrict h, yJ_eq_one_iff, SubgroupClass.coe_pow, map_pow]
      exact hv23
    have h2 := (hker _).1 h1
    rwa [MonoidHom.coe_rangeRestrict, map_pow] at h2
  have hpow : (yMc hG v ^ 3) ^ 23 = 1 := by
    have h3 : orderOf (yMc hG v ^ 23) ∣ 3 := hζ3 ▸ orderOf_dvd_of_mem_zpowers hw23
    rw [← pow_mul, mul_comm, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hne : yMc hG v ^ 3 ≠ 1 := by
    intro h1
    have hk : v ^ 3 ∈ yJ.ker := h (by rw [MonoidHom.mem_ker, map_pow]; exact h1)
    have hk' := (yJ_eq_one_iff _).1 (MonoidHom.mem_ker.1 hk)
    rw [SubgroupClass.coe_pow, map_pow] at hk'
    have hg := pow_gcd_eq_one.2 ⟨hk', hv23⟩
    rw [show Nat.gcd 3 23 = 1 by norm_num, pow_one] at hg
    exact hv1 hg
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hord : orderOf (yMc hG v ^ 3) = 23 := orderOf_eq_prime hpow hne
  have hT : yMc hG v ^ 3 ∈ Subgroup.centralizer ({tGriess} : Set MGriess) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute tGriess (yMc hG v) := tGriess_comm_yM_evalWord hG hc h4
    exact (hcomm.pow_right 3).eq.symm
  have hZ : yMc hG v ^ 3 ∈ Subgroup.centralizer ({ζ} : Set MGriess) :=
    hDζ (Subgroup.pow_mem _ (MonoidHom.mem_range.2 ⟨v, rfl⟩) 3)
  have hdvd := orderOf_dvd_natCard (⟨yMc hG v ^ 3, Subgroup.mem_inf.2 ⟨hT, hZ⟩⟩ :
    ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓ Subgroup.centralizer ({ζ} : Set MGriess)))
  rwa [Subgroup.orderOf_mk, hord] at hdvd

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
