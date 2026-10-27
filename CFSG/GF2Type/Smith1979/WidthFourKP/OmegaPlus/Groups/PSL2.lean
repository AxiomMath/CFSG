module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData
public import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27Inv
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open CFSG.AGLEmbedding
open scoped MatrixGroups

variable {X : Type} [Group X]

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private theorem card_psl2GF_seven : Nat.card (PSL2GF 7 1) = 168 := by
  have hF : Nat.card (GaloisField 7 1) = 7 := by
    simpa using GaloisField.card 7 1 (by norm_num : (1 : ℕ) ≠ 0)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 7 1)) :=
    ⟨7, 1, by norm_num, by norm_num, by norm_num, hF⟩
  rw [show PSL2GF 7 1 = CFSG.GorensteinWalter.PSL2 (GaloisField 7 1) from rfl,
    CFSG.GorensteinWalter.psl2_card_formula (GaloisField 7 1) hodd, hF]
  norm_num

private theorem card_psl2GF_eight : Nat.card (PSL2GF 2 3) = 504 := by
  rw [show PSL2GF 2 3 = PSL(2, GaloisField 2 3) from rfl,
    CFSG.Walter.psl2_even_card (f := 3) (by norm_num)]
  norm_num

theorem isSimpleGroup_of_mulEquiv_psl27 (e : X ≃* PSL2GF 7 1) : IsSimpleGroup X := by
  haveI : IsSimpleGroup (PSL2GF 7 1) :=
    isSimpleGroup_psl2GF (p := 7) (n := 1) (by norm_num)
  exact MulEquiv.isSimpleGroup e

theorem exists_ne_comm_of_mulEquiv_psl27 (e : X ≃* PSL2GF 7 1) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI : IsMulCommutative X := isMulCommutative_iff.mpr h
  have hprime : (Nat.card X).Prime :=
    (Group.is_simple_iff_prime_card).mp (isSimpleGroup_of_mulEquiv_psl27 e)
  have hcard : Nat.card X = 168 :=
    (Nat.card_congr e.toEquiv).trans card_psl2GF_seven
  rw [hcard] at hprime
  exact (by norm_num : ¬ Nat.Prime 168) hprime

theorem card_mulAut_le_of_mulEquiv_psl27 (e : X ≃* PSL2GF 7 1) :
    Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  have hAut : Nat.card (MulAut X) = Nat.card (MulAut (PSL2GF 7 1)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hcard : Nat.card X = Nat.card (PSL2GF 7 1) := Nat.card_congr e.toEquiv
  rw [hAut, card_mulAut_psl2GF 7 1 (by norm_num : 1 ≤ 1), hcard, card_psl2GF_seven]
  norm_num

theorem eq_one_of_commute_involution_psl27 (e : X ≃* PSL2GF 7 1)
    {v y : X} (hv : orderOf v = 2) (hyv : y * v = v * y) (hy : y ^ 3 = 1) : y = 1 := by
  letI : Fintype (GaloisField 7 1) := Fintype.ofFinite _
  let z : PSL2GF 7 1 := e v
  have hzord : orderOf z = 2 := by
    change orderOf (e v) = 2
    rw [MulEquiv.orderOf_eq, hv]
  have hz2 : z * z = 1 := by
    simpa [hzord, pow_two] using pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    omega
  have hF7 : Fintype.card (GaloisField 7 1) = 7 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 7 1 (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num
  have hCcard : Nat.card (Subgroup.centralizer ({z} : Set (PSL2GF 7 1))) = 8 :=
    CFSG.Quasithin.E217R4.cent2_psl hF7 hz2 hz1
  have hyz : e y ∈ Subgroup.centralizer ({z} : Set (PSL2GF 7 1)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e v = e v * e y
    rw [← map_mul, ← map_mul, hyv]
  have hy3 : (e y) ^ 3 = 1 := by
    rw [← map_pow, hy, map_one]
  have hcop : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({z} : Set (PSL2GF 7 1)))) 3 := by
    rw [hCcard]
    norm_num
  have hey1 : e y = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hyz hcop hy3
  exact e.injective (by simpa using hey1)

theorem isSimpleGroup_of_mulEquiv_psl28 (e : X ≃* PSL2GF 2 3) : IsSimpleGroup X := by
  haveI : IsSimpleGroup (PSL2GF 2 3) :=
    isSimpleGroup_psl2GF (p := 2) (n := 3) (by norm_num)
  exact MulEquiv.isSimpleGroup e

theorem exists_ne_comm_of_mulEquiv_psl28 (e : X ≃* PSL2GF 2 3) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI : IsMulCommutative X := isMulCommutative_iff.mpr h
  have hprime : (Nat.card X).Prime :=
    (Group.is_simple_iff_prime_card).mp (isSimpleGroup_of_mulEquiv_psl28 e)
  have hcard : Nat.card X = 504 :=
    (Nat.card_congr e.toEquiv).trans card_psl2GF_eight
  rw [hcard] at hprime
  exact (by norm_num : ¬ Nat.Prime 504) hprime

theorem card_mulAut_of_mulEquiv_psl28 (e : X ≃* PSL2GF 2 3) :
    Nat.card (MulAut X) = 3 * Nat.card X := by
  have hAut : Nat.card (MulAut X) = Nat.card (MulAut (PSL2GF 2 3)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hcard : Nat.card X = Nat.card (PSL2GF 2 3) := Nat.card_congr e.toEquiv
  rw [hAut, card_mulAut_psl2GF 2 3 (by norm_num : 1 ≤ 3), hcard, card_psl2GF_eight]
  norm_num

theorem eq_one_of_commute_involution_psl28 (e : X ≃* PSL2GF 2 3)
    {v y : X} (hv : orderOf v = 2) (hyv : y * v = v * y) (hy : y ^ 3 = 1) : y = 1 := by
  let z : PSL2GF 2 3 := e v
  have hzord : orderOf z = 2 := by
    change orderOf (e v) = 2
    rw [MulEquiv.orderOf_eq, hv]
  have hP : IsPGroup 2 (Subgroup.centralizer ({z} : Set (PSL2GF 2 3))) :=
    CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hzord
  have hyz : e y ∈ Subgroup.centralizer ({z} : Set (PSL2GF 2 3)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e v = e v * e y
    rw [← map_mul, ← map_mul, hyv]
  have hy3 : (e y) ^ 3 = 1 := by
    rw [← map_pow, hy, map_one]
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({z} : Set (PSL2GF 2 3)))) 3 := by
    rw [hk]
    exact Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  have hey1 : e y = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hyz hcop hy3
  exact e.injective (by simpa using hey1)

private theorem center_eq_bot_of_mulEquiv_psl28 (e : X ≃* PSL2GF 2 3) :
    Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := isSimpleGroup_of_mulEquiv_psl28 e
  obtain ⟨a, b, hab⟩ := exists_ne_comm_of_mulEquiv_psl28 e
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    (fun h => hab (h.is_comm.comm a b))

theorem eq_one_of_conj_fixed_psl28 (e : X ≃* PSL2GF 2 3) {τ : MulAut X} {x : X}
    (hτx : τ = MulAut.conj x) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    {y : X} (hyτ : τ y = y) (hy : y ^ 3 = 1) : y = 1 := by
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv_psl28 e
  have hτ2' : MulAut.conj x * MulAut.conj x = 1 := by
    rwa [hτx] at hτ2
  have hx2 : x * x = 1 :=
    CFSG.Quasithin.F7Two.mul_self_eq_one_of_conj_mul_self hZ hτ2'
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hτ1 (by simp [hτx])
  have hxord : orderOf x = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hcomm : y * x = x * y := by
    have hxy : x * y * x⁻¹ = y := by
      simpa only [hτx, MulAut.conj_apply] using hyτ
    calc y * x = (x * y * x⁻¹) * x := by rw [hxy]
      _ = x * y := by group
  exact eq_one_of_commute_involution_psl28 e hxord hcomm hy

theorem false_of_psl27 [Finite X] {A : Subgroup (MulAut X)} {τ : MulAut X}
    {B : Subgroup X} (D : LayerData X A τ B) (e : X ≃* CFSG.AGLEmbedding.PSL2GF 7 1) : False := by
  haveI : IsSimpleGroup X := isSimpleGroup_of_mulEquiv_psl27 e
  exact D.false_of_outTwo (exists_ne_comm_of_mulEquiv_psl27 e)
    (card_mulAut_le_of_mulEquiv_psl27 e)
    (fun v y hv hyv hy => eq_one_of_commute_involution_psl27 e hv hyv hy)

theorem false_of_psl28 [Finite X] {A : Subgroup (MulAut X)} {τ : MulAut X}
    {B : Subgroup X} (D : LayerData X A τ B) (e : X ≃* CFSG.AGLEmbedding.PSL2GF 2 3) : False := by
  haveI : IsSimpleGroup X := isSimpleGroup_of_mulEquiv_psl28 e
  obtain ⟨x, hx⟩ := D.inner_of_outOdd (exists_ne_comm_of_mulEquiv_psl28 e) (k := 3)
    (by norm_num : Odd 3) (card_mulAut_of_mulEquiv_psl28 e)
  exact D.false_of_W1 fun y hyτ hy =>
    eq_one_of_conj_fixed_psl28 e hx D.ne_one (D.sq_A τ D.mem_A) hyτ hy

end CFSG.GF2Type.Smith1979.OmegaPlus
