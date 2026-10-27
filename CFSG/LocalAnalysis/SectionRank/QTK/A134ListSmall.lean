module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenPlus8
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def rotL4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0;
       1, 1, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, 1]

@[expose] def trL4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0;
       0, 1, 0, 0;
       0, 0, 1, 1;
       0, 0, 0, 1]

theorem rotL4_facts : rotL4 * (rotL4 * rotL4) = 1 ∧ trL4 * trL4 = 1 ∧
    rotL4 * trL4 = trL4 * rotL4 ∧ rotL4.det = 1 ∧ trL4.det = 1 ∧ rotL4 0 0 = 0 ∧
    rotL4 2 2 = 1 ∧ trL4 2 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def rotL5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0;
       1, 1, 0, 0, 0;
       0, 0, 1, 0, 0;
       0, 0, 0, 1, 0;
       0, 0, 0, 0, 1]

@[expose] def trL5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0;
       0, 1, 0, 0, 0;
       0, 0, 1, 1, 0;
       0, 0, 0, 1, 0;
       0, 0, 0, 0, 1]

theorem rotL5_facts : rotL5 * (rotL5 * rotL5) = 1 ∧ trL5 * trL5 = 1 ∧
    rotL5 * trL5 = trL5 * rotL5 ∧ rotL5.det = 1 ∧ trL5.det = 1 ∧ rotL5 0 0 = 0 ∧
    rotL5 2 2 = 1 ∧ trL5 2 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem one_le_localRank_three_of_matrices {n : ℕ} {X T : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hX3 : X * (X * X) = 1) (hT2 : T * T = 1) (hXT : X * T = T * X) (hdX : X.det = 1)
    (hdT : T.det = 1) {i j k l : Fin n} (hXi : X i i = 0) (hXj : X j j = 1) (hkl : k ≠ l)
    (hTkl : T k l = 1) : 1 ≤ localRank 3 (StatedProj (StatedSL n K)) := by
  set u := unitOfCube X hX3
  set v := unitOfSq T hT2
  have hmem : ∀ w : GL (Fin n) (ZMod 2), (w : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 →
      castGLι K w ∈ StatedSL n K := fun w hw => Subgroup.subset_closure (by
    change (castMat K (w : Matrix (Fin n) (Fin n) (ZMod 2))).det = 1
    rw [castMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hw, map_one])
  set x : StatedSL n K := ⟨castGLι K u, hmem u hdX⟩
  set t : StatedSL n K := ⟨castGLι K v, hmem v hdT⟩
  have hu3 : u ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, pow_succ', pow_two, Units.val_one]
    exact hX3)
  have hv2 : v ^ 2 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
    exact hT2)
  have huv : u * v = v * u := Units.ext hXT
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    change castGLι K u ^ 3 = 1
    rw [← map_pow, hu3, map_one])
  have ht2 : t ^ 2 = 1 := Subtype.ext (by
    change castGLι K v ^ 2 = 1
    rw [← map_pow, hv2, map_one])
  have hxt : x * t = t * x := Subtype.ext (by
    change castGLι K u * castGLι K v = castGLι K v * castGLι K u
    rw [← map_mul, ← map_mul, huv])
  have hscal : ∀ y : StatedSL n K, y ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) →
      ∃ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c :=
    fun y hy => by
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨c, by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]⟩
  set xb : StatedProj (StatedSL n K) := QuotientGroup.mk x
  set tb : StatedProj (StatedSL n K) := QuotientGroup.mk t
  have hxb1 : xb ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := hscal x ((QuotientGroup.eq_one_iff x).mp h)
    have hi := congrFun (congrFun hc i) i
    have hj := congrFun (congrFun hc j) j
    change cast2 K (X i i) = _ at hi
    change cast2 K (X j j) = _ at hj
    rw [hXi, map_zero, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hi
    rw [hXj, map_one, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hj
    exact zero_ne_one (hi.trans hj.symm)
  have htb1 : tb ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := hscal t ((QuotientGroup.eq_one_iff t).mp h)
    have hk := congrFun (congrFun hc k) l
    change cast2 K (T k l) = _ at hk
    rw [hTkl, map_one, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hkl] at hk
    exact one_ne_zero hk
  have hxb3 : xb ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one]
  have htb2 : tb ^ 2 = 1 := by rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
  have hxtb : Commute xb tb := by
    change (QuotientGroup.mk x : StatedProj (StatedSL n K)) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxt]
  have hne : Subgroup.zpowers tb ≠ ⊥ := fun h =>
    htb1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers tb))
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne (isPGroup_zpowers_of_sq htb2)
    (mem_normalizer_zpowers hxtb) (orderOf_eq_prime hxb3 hxb1)

variable {K}

theorem oddLocalWitness_psl_four_five {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hm : StatedClassicalModel S .PSL n 2 1) : OddLocalWitness S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  refine OddLocalWitness.of_mulEquiv e ⟨3, Nat.prime_three, by norm_num,
    CFSG.Quasithin.A3Facts.psl_two_le_pRank_three (by omega), ?_⟩
  rcases hn with rfl | rfl
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rotL4_facts
    exact one_le_localRank_three_of_matrices K h1 h2 h3 h4 h5 h6 h7 (by decide) h8
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rotL5_facts
    exact one_le_localRank_three_of_matrices K h1 h2 h3 h4 h5 h6 h7 (by decide) h8

end CFSG.SectionRank.QTK
