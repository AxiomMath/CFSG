module

public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData
public import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGEven
public import CFSG.Quasithin.Background.F7TwoInvSeed

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

variable {X : Type} [Group X]

theorem card_of_lieModel_l34 (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
    (CFSG.ComponentClassification.FooteLit.KG.statedClassicalModel_of_lieModel_psl h)

theorem center_eq_bot_of_lieModel_l34 (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) :
    Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hcard := card_of_lieModel_l34 h
  have hnc : ¬ IsMulCommutative X := by
    intro hcomm
    haveI : IsMulCommutative X := hcomm
    have hp : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcard] at hp
    exact (by norm_num : ¬ Nat.Prime 20160) hp
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc

theorem eq_one_of_commute_involution_l34
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    {v y : X} (hv : orderOf v = 2) (hyv : y * v = v * y) (hy : y ^ 3 = 1) : y = 1 := by
  have hmem : y ∈ Subgroup.centralizer ({v} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyv
  have h64 : Nat.card (Subgroup.centralizer ({v} : Set X)) = 64 :=
    CFSG.ComponentClassification.FooteLit.KG.card_centralizer_of_lieModel_l34 h v hv
  exact CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime
    (U := Subgroup.centralizer ({v} : Set X)) hmem (by rw [h64]; norm_num) hy

theorem eq_one_of_conj_fixed_l34
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) {τ : MulAut X} {x : X}
    (hτx : τ = MulAut.conj x) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    {y : X} (hyτ : τ y = y) (hy : y ^ 3 = 1) : y = 1 := by
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_lieModel_l34 h
  have hxx : x * x = 1 :=
    CFSG.Quasithin.F7Two.mul_self_eq_one_of_conj_mul_self hZ (by rw [← hτx]; exact hτ2)
  have hx2 : orderOf x = 2 := by
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hτ1 (by simp [hτx])
    exact orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hcomm : y * x = x * y := by
    have hxy : x * y * x⁻¹ = y := by
      simpa only [hτx, MulAut.conj_apply] using hyτ
    calc y * x = (x * y * x⁻¹) * x := by rw [hxy]
      _ = x * y := by group
  exact eq_one_of_commute_involution_l34 h hx2 hcomm hy

theorem false_of_l34 {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {τ : MulAut X} {B : Subgroup X} (D : LayerData X A τ B)
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) : False := by
  obtain ⟨x, hx⟩ := D.inner (by rw [card_of_lieModel_l34 h]; norm_num)
  exact D.false_of_W1 fun y hy hy3 =>
    eq_one_of_conj_fixed_l34 h hx D.ne_one (D.sq_A τ D.mem_A) hy hy3

end CFSG.GF2Type.Smith1979.OmegaPlus
