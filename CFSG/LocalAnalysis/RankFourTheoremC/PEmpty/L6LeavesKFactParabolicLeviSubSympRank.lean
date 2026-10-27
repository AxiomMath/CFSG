module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubLinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars scalars_eq_center card_scalars_dvd
  card_SL_eq card_GL_eq)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torusHom_injective)

theorem two_le_pRank_sp_of_dvd_sub_one {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSp n K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvdK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hrq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvdK
  have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hkey : ∀ m : ℕ, ζ ^ m = 1 → r ∣ m := fun m hm => hζ ▸ orderOf_dvd_of_pow_eq_one hm
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  let u : StatedSp n K := torusHom (Pi.mulSingle i0 ζ)
  let v : StatedSp n K := torusHom (Pi.mulSingle i1 ζ)
  have hcomm : Commute u v := by
    show u * v = v * u
    simp only [u, v, ← map_mul]
    congr 1
    exact mul_comm _ _
  have hu : u ^ r = 1 := by
    simp only [u, ← map_pow]
    rw [← Pi.mulSingle_pow, hζr, Pi.mulSingle_one, map_one]
  have hv : v ^ r = 1 := by
    simp only [v, ← map_pow]
    rw [← Pi.mulSingle_pow, hζr, Pi.mulSingle_one, map_one]
  refine GL83.I713.two_le_pRank_of_commute hr hcomm hu hv ?_
  intro a b hab
  have h1 : torusHom (Pi.mulSingle i0 ζ ^ a * Pi.mulSingle i1 ζ ^ b) = 1 := by
    simp only [map_mul, map_pow]
    exact hab
  have h2 := torusHom_injective (h1.trans (map_one torusHom).symm)
  have e0 := congrFun h2 i0
  have e1 := congrFun h2 i1
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi01,
    Pi.mulSingle_eq_of_ne hi01.symm, one_pow, mul_one, one_mul, Pi.one_apply] at e0 e1
  exact ⟨hkey a e0, hkey b e1⟩

section SLArith

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_SL_mul {k : ℕ} :
    Nat.card (SpecialLinearGroup (Fin k) K) =
      Nat.card (SpecialLinearGroup (Fin k) K ⧸ Subgroup.center (SpecialLinearGroup (Fin k) K)) *
        Nat.card (Subgroup.center (SpecialLinearGroup (Fin k) K)) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem card_center_SL_dvd {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin k) K)) ∣ Nat.card K - 1 := by
  rw [← scalars_eq_center k K]
  exact card_scalars_dvd hk

theorem card_center_SL_two : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) K)) = 1 := by
  rw [← scalars_eq_center 2 K, LinearCover.scalars_two_eq_bot K, Subgroup.card_bot]

theorem dvd_card_slQuot {k : ℕ} (hk : 2 ≤ k) {p j : ℕ} (hp : p.Prime) (hj2 : 2 ≤ j) (hjk : j ≤ k)
    (hpj : p ∣ Nat.card K ^ j - 1) (hnd : ¬ p ∣ Nat.card K - 1) :
    p ∣ Nat.card (SpecialLinearGroup (Fin k) K ⧸
      Subgroup.center (SpecialLinearGroup (Fin k) K)) := by
  have h1 : p ∣ Nat.card (SpecialLinearGroup (Fin k) K) := by
    rw [card_SL_eq (by omega)]
    exact Dvd.dvd.mul_left (hpj.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1)
      (Finset.mem_Icc.2 ⟨hj2, hjk⟩))) _
  rw [card_SL_mul] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · exact h
  · exact absurd (h.trans (card_center_SL_dvd (by omega))) hnd

theorem dvd_card_slQuot_of_dvd_sub_one {k : ℕ} (hk : 2 ≤ k) {f : ℕ}
    (hf : f ∣ Nat.card K - 1) :
    f ∣ Nat.card (SpecialLinearGroup (Fin k) K ⧸
      Subgroup.center (SpecialLinearGroup (Fin k) K)) := by
  have hX := card_SL_eq (K := K) (n := k) (by omega)
  have hmul := card_SL_mul (K := K) (k := k)
  have hz := card_center_SL_dvd (K := K) (k := k) (by omega)
  have hzpos : 0 < Nat.card (Subgroup.center (SpecialLinearGroup (Fin k) K)) := Nat.card_pos
  have hdvdq2 : ∀ j : ℕ, Nat.card K - 1 ∣ Nat.card K ^ j - 1 := fun j =>
    Nat.sub_one_dvd_pow_sub_one (Nat.card K) j
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have hk2 : k = 2 := by omega
    subst hk2
    have hz1 := card_center_SL_two (K := K)
    have hXT : Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card (SpecialLinearGroup (Fin 2) K ⧸
        Subgroup.center (SpecialLinearGroup (Fin 2) K)) := by rw [hmul, hz1, mul_one]
    refine hf.trans ((hdvdq2 2).trans ?_)
    have h2 : Nat.card K ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 2, (Nat.card K ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩)
    rw [← hXT, hX]
    exact Dvd.dvd.mul_left h2 _
  · have hsq : (Nat.card K - 1) ^ 2 ∣ Nat.card (SpecialLinearGroup (Fin k) K) := by
      rw [hX]
      refine Dvd.dvd.mul_left ?_ _
      have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 k := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        omega
      have h23 := Finset.prod_dvd_prod_of_subset _ _ (fun j => Nat.card K ^ j - 1) hsub
      rw [Finset.prod_pair (by norm_num)] at h23
      refine (?_ : (Nat.card K - 1) ^ 2 ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)).trans h23
      rw [pow_two]
      exact mul_dvd_mul (hdvdq2 2) (hdvdq2 3)
    rw [hmul, mul_comm] at hsq
    exact hf.trans (dvd_of_sq_dvd_mul hzpos hz hsq)

theorem three_dvd_card_slQuot {k : ℕ} (hk : 2 ≤ k) (hq : Nat.card K = 2) :
    3 ∣ Nat.card (SpecialLinearGroup (Fin k) K ⧸
      Subgroup.center (SpecialLinearGroup (Fin k) K)) := by
  have hX := card_SL_eq (K := K) (n := k) (by omega)
  have hmul := card_SL_mul (K := K) (k := k)
  have hz := card_center_SL_dvd (K := K) (k := k) (by omega)
  rw [hq] at hz
  have hz1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin k) K)) = 1 := Nat.dvd_one.1 hz
  have hXT : Nat.card (SpecialLinearGroup (Fin k) K) = Nat.card (SpecialLinearGroup (Fin k) K ⧸
      Subgroup.center (SpecialLinearGroup (Fin k) K)) := by rw [hmul, hz1, mul_one]
  rw [← hXT, hX, hq]
  refine Dvd.dvd.mul_left ?_ _
  have h2 : 2 ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 k, (2 ^ j - 1) :=
    Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hk⟩)
  simpa using h2

end SLArith

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
