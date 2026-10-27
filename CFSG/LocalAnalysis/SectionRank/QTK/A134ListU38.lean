module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven CFSG.RankThree.PartTwo.Census
open CFSG.Assembly.RankThreeEven (localRank)

theorem oddLocalWitness_psu_three_eight {S : Type} [Group S] [Finite S]
    (hm : StatedClassicalModel S .PSU 3 2 3) : OddLocalWitness S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine OddLocalWitness.of_mulEquiv e ⟨3, Nat.prime_three, by norm_num,
    CFSG.Quasithin.A3Facts.psu_three_eight_two_le_pRank hK, ?_⟩
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [hcard] at hg
  set ζ : Kˣ := g ^ 7 with hζdef
  have hζ : orderOf ζ = 9 := by
    rw [hζdef, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hζ9 : ζ ^ 9 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    omega
  have hq : (2 ^ 3 : ℕ) ≠ 0 := by norm_num
  set d : Fin 3 → Kˣ := ![ζ, ζ, ζ⁻¹ ^ 2] with hd
  have hprod : ∏ i, d i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← pow_two, ← mul_pow, mul_inv_cancel, one_pow]
  have hd9 : d ^ (2 ^ 3 + 1) = 1 := by
    funext i
    fin_cases i <;> simp [hd, Pi.pow_apply]
    · exact hζ9
    · exact hζ9
    · rw [← pow_mul, show 2 * 9 = 9 * 2 from rfl, pow_mul, hζ9, one_pow]
  set x : StatedSU 3 (2 ^ 3) K := ⟨torusDiag d, torusDiag_mem_SU hq hprod hd9⟩
  set t : StatedSU 3 (2 ^ 3) K := ⟨swapGL (K := K) (by norm_num), swapGL_mem_statedSU hU _⟩
  have hd01 : ∀ i j : Fin 3, i.val < 2 → j.val < 2 → ((d i : Kˣ) : K) = ((d j : Kˣ) : K) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hxt : x * t = t * x := Subtype.ext (Units.ext (by
    change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * (1 + swapBlock 3 K) =
      (1 + swapBlock 3 K) * (torusDiag d : Matrix (Fin 3) (Fin 3) K)
    rw [coe_torusDiag]
    exact diagonal_mul_swap hd01))
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    change (1 + swapBlock 3 K) * (1 + swapBlock 3 K) = 1
    exact one_add_mul_one_add (swapBlock_mul_self (by norm_num))))
  have hinv : ((ζ ^ 2) ^ 3)⁻¹ = ζ ^ 3 := by
    rw [← pow_mul]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hζ9)
  have hd3 : d ^ 3 = fun _ => ζ ^ 3 := by
    funext i
    fin_cases i <;> simp [hd, Pi.pow_apply, hinv]
  set T := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ 3) K)
  have hx3 : x ^ 3 ∈ T := by
    rw [Subgroup.mem_subgroupOf]
    refine ⟨ζ ^ 3, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    change Matrix.scalar (Fin 3) ((ζ ^ 3 : Kˣ) : K) =
      ((torusDiag d ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← map_pow, hd3, coe_torusDiag]
    rfl
  have hscal : ∀ y : StatedSU 3 (2 ^ 3) K, y ∈ T →
      ∃ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c :=
    fun y hy => by
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨c, by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]⟩
  have hxT : x ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal x h
    change (torusDiag d : Matrix (Fin 3) (Fin 3) K) = _ at hc
    rw [coe_torusDiag] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h2 := congrFun (congrFun hc 2) 2
    simp only [diagonal_apply_eq, Matrix.scalar_apply] at h0 h2
    have hu : ζ = ζ⁻¹ ^ 2 := Units.ext (by simpa [hd] using h0.trans h2.symm)
    apply hζ3
    calc ζ ^ 3 = ζ⁻¹ ^ 2 * ζ ^ 2 := by rw [← hu, ← pow_succ']
      _ = 1 := by rw [← mul_pow, inv_mul_cancel, one_pow]
  have htT : t ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal t h
    change 1 + swapBlock 3 K = _ at hc
    have h01 := congrFun (congrFun hc 0) 1
    simp [swapBlock, Matrix.scalar_apply] at h01
  set xb : StatedProj (StatedSU 3 (2 ^ 3) K) := QuotientGroup.mk x
  set tb : StatedProj (StatedSU 3 (2 ^ 3) K) := QuotientGroup.mk t
  have hxb3 : xb ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx3
  have hxb1 : xb ≠ 1 := fun h => hxT ((QuotientGroup.eq_one_iff x).mp h)
  have htb1 : tb ≠ 1 := fun h => htT ((QuotientGroup.eq_one_iff t).mp h)
  have htb2 : tb ^ 2 = 1 := by rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
  have hxtb : Commute xb tb := by
    change (QuotientGroup.mk x : StatedProj (StatedSU 3 (2 ^ 3) K)) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxt]
  have hne : Subgroup.zpowers tb ≠ ⊥ := fun h =>
    htb1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers tb))
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne (isPGroup_zpowers_of_sq htb2)
    (mem_normalizer_zpowers hxtb) (orderOf_eq_prime hxb3 hxb1)

end CFSG.SectionRank.QTK
