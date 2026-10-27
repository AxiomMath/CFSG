module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0

public section

namespace CFSG.SectionRank.QTK

open Matrix
open CFSG.Assembly.RankThreeEven (localRank)

variable {K : Type} [Field K]

@[expose] def sl2DiagHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun t := ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    change (!![((1 : Kˣ) : K), 0; 0, ((1⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    change (!![((s * t : Kˣ) : K), 0; 0, (((s * t)⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) =
      !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] def sl2UpperHom : Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun c := ⟨!![1, c.toAdd; 0, 1], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    change (!![1, Multiplicative.toAdd (1 : Multiplicative K); 0, 1] : Matrix (Fin 2) (Fin 2) K) =
      1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change (!![1, (a * b).toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) K) =
      !![1, a.toAdd; 0, 1] * !![1, b.toAdd; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp] theorem coe_sl2DiagHom (t : Kˣ) :
    ((sl2DiagHom t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

@[simp] theorem coe_sl2UpperHom (c : Multiplicative K) :
    ((sl2UpperHom c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, c.toAdd; 0, 1] := rfl

theorem sl2DiagHom_injective : Function.Injective (sl2DiagHom (K := K)) := fun s t h => by
  have h1 : (!![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    congrFun (congrFun (congrArg Subtype.val h) 0) 0
  exact Units.ext (by simpa using h1)

theorem sl2UpperHom_injective : Function.Injective (sl2UpperHom (K := K)) := fun a b h => by
  have h1 : (!![1, a.toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (!![1, b.toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 1 :=
    congrFun (congrFun (congrArg Subtype.val h) 0) 1
  exact Multiplicative.toAdd.injective (by simpa using h1)

theorem sl2Diag_mul_upper (t : Kˣ) (c : Multiplicative K) :
    sl2DiagHom t * sl2UpperHom c =
      sl2UpperHom (Multiplicative.ofAdd ((t : K) ^ 2 * c.toAdd)) * sl2DiagHom t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc]
  field_simp

theorem sl2Diag_conj_upper (t : Kˣ) (c : Multiplicative K) :
    sl2DiagHom t * sl2UpperHom c * (sl2DiagHom t)⁻¹ =
      sl2UpperHom (Multiplicative.ofAdd ((t : K) ^ 2 * c.toAdd)) :=
  mul_inv_eq_of_eq_mul (sl2Diag_mul_upper t c)

theorem one_le_localRank_of_SL2 [Finite K] [CharP K 2] {S : Type} [Group S] [Finite S]
    (ι : SpecialLinearGroup (Fin 2) K →* S) (hι : Function.Injective ι) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ Nat.card Kˣ) : 1 ≤ localRank r S := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' r hrd
  set U := (sl2UpperHom (K := K)).range
  have hU2 : IsPGroup 2 U := by
    rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hc2 : c ^ 2 = 1 := Multiplicative.toAdd.injective (by
      rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero])
    rw [pow_one, SubgroupClass.coe_pow, ← map_pow, hc2, map_one, OneMemClass.coe_one]
  have hU1 : U ≠ ⊥ := fun h => by
    have hm : sl2UpperHom (Multiplicative.ofAdd (1 : K)) ∈ U := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one sl2UpperHom] at hm
    have h1 := congrArg Multiplicative.toAdd (sl2UpperHom_injective hm)
    rw [toAdd_ofAdd, toAdd_one] at h1
    exact one_ne_zero h1
  have hdU : sl2DiagHom t ∈ Subgroup.normalizer (U : Set (SpecialLinearGroup (Fin 2) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, (sl2Diag_conj_upper t c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨Multiplicative.ofAdd (((t⁻¹ : Kˣ) : K) ^ 2 * c.toAdd), ?_⟩
      have hg : g = sl2DiagHom t⁻¹ * sl2UpperHom c * (sl2DiagHom t⁻¹)⁻¹ := by
        rw [hc, map_inv, inv_inv]
        group
      rw [hg, sl2Diag_conj_upper]
  refine one_le_localRank_of_mem_normalizer hr.one_lt (R := U.map ι)
    ((Subgroup.map_eq_bot_iff_of_injective U hι).not.2 hU1) (hU2.map ι)
    (Subgroup.le_normalizer_map ι ⟨_, hdU, rfl⟩) ?_
  rw [orderOf_injective ι hι, orderOf_injective _ sl2DiagHom_injective, ht]

end CFSG.SectionRank.QTK
