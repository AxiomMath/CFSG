module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.StandardType

section

variable {τ : Tag} {K : Type} [Field K]

theorem sq_eq_one_of_zpowMatrix_cartan_eq_one [Finite K] (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (t : Fin τ.rank → Kˣ) (ht : zpowMatrix (G := Kˣ) τ.cartan t = 1) : t ^ 2 = 1 := by
  rcases hτ with rfl | rfl
  · have hcard : Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker = (Nat.card K - 1).gcd 2 := by
      rw [card_ker_zpowMatrix_eq smithE7 smithE7P'_mul smithE7P_mul smithE7Q_mul,
        card_ker_zpowMatrix_diagonal]
      simp only [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
      change ∏ i : Fin 7, (Nat.card K - 1).gcd (smithE7D i) = _
      simp [smithE7D, Fin.prod_univ_succ]
    have h1 : (⟨t, (MonoidHom.mem_ker).2 ht⟩ :
        (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker) ^
        Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker = 1 := pow_card_eq_one'
    have h2 : t ^ Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker = 1 :=
      congrArg Subtype.val h1
    obtain ⟨m, hm⟩ : Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker ∣ 2 := by
      rw [hcard]
      exact Nat.gcd_dvd_right _ _
    rw [hm, pow_mul, h2, one_pow]
  · have h := congrArg (zpowMatrix (G := Kˣ) cartanInvE8) ht
    rw [zpowMatrix_zpowMatrix, cartan_mul_cartanInvE8, zpowMatrix_one, map_one] at h
    rw [h, one_pow]

noncomputable def cubeCoordTorusPow
    (x : Fin τ.rank → (powMonoidHom 3 : Kˣ →* Kˣ).ker) : TableBExc.torusPow τ K 3 :=
  ⟨⟨(torusCoordHom τ K fun i => (x i : Kˣ) : torusGroup τ K),
      CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (SetLike.coe_mem _)⟩,
    SetLike.coe_mem _, Subtype.ext (by
      have hx : (fun i => (x i : Kˣ)) ^ 3 = 1 := funext fun i => (MonoidHom.mem_ker).1 (x i).2
      have h : (torusCoordHom τ K fun i => (x i : Kˣ)) ^ 3 = 1 := by
        rw [← map_pow, hx, map_one]
      have h' := congrArg Subtype.val h
      exact h')⟩

theorem cubeCoordTorusPow_injective [Finite K] (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    Function.Injective (cubeCoordTorusPow (τ := τ) (K := K)) := by
  intro x y hxy
  have h : torusCoordHom τ K (fun i => (x i : Kˣ)) = torusCoordHom τ K (fun i => (y i : Kˣ)) :=
    Subtype.ext (congrArg (fun g : TableBExc.torusPow τ K 3 => ((g : adjointGroup τ K) : ModGL τ K))
      hxy)
  set d : Fin τ.rank → Kˣ := (fun i => (x i : Kˣ)) * (fun i => (y i : Kˣ))⁻¹ with hd
  have hd1 : torusCoordHom τ K d = 1 := by
    rw [hd, map_mul, map_inv, h, mul_inv_cancel]
  have hd2 : d ^ 2 = 1 :=
    sq_eq_one_of_zpowMatrix_cartan_eq_one hτ d ((torusCoordHom_eq_one_iff d).1 hd1)
  have hx : (fun i => (x i : Kˣ)) ^ 3 = 1 := funext fun i => (MonoidHom.mem_ker).1 (x i).2
  have hy : (fun i => (y i : Kˣ)) ^ 3 = 1 := funext fun i => (MonoidHom.mem_ker).1 (y i).2
  have hd3 : d ^ 3 = 1 := by
    rw [hd, mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hd0 : d = 1 :=
    calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
      _ = 1 := by rw [hd3, hd2]; simp
  funext i
  have hi := congrFun hd0 i
  rw [hd, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_eq_one] at hi
  exact Subtype.ext hi

theorem three_pow_rank_le_card_torusPow [Finite K] (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (h3 : 3 ∣ Nat.card K - 1) : 3 ^ τ.rank ≤ Nat.card (TableBExc.torusPow τ K 3) := by
  have hfin : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hcard : Nat.card (powMonoidHom 3 : Kˣ →* Kˣ).ker = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units]
    exact Nat.gcd_eq_right h3
  have := Nat.card_le_card_of_injective _ (cubeCoordTorusPow_injective (τ := τ) (K := K) hτ)
  rwa [Nat.card_fun, hcard, Nat.card_fin] at this

end

section

variable {τ : Tag} {K : Type} [Field K]

theorem torusPow_three_pow_eq_one : ∀ a ∈ TableBExc.torusPow τ K 3, a ^ 3 = 1 :=
  fun _ ha => (TableBExc.mem_torusPow.1 ha).2

theorem torusPow_mul_comm :
    ∀ a ∈ TableBExc.torusPow τ K 3, ∀ b ∈ TableBExc.torusPow τ K 3, a * b = b * a :=
  fun _ ha _ hb => Subtype.ext
    (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (TableBExc.mem_torusPow.1 ha).1)
      (torusGroup_le_diagonalGroup (TableBExc.mem_torusPow.1 hb).1))

theorem torusPow_normalized :
    ∀ n ∈ monomialSub τ K, ∀ v ∈ TableBExc.torusPow τ K 3,
      n * v * n⁻¹ ∈ TableBExc.torusPow τ K 3 := by
  intro n hn v hv
  have hN := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.1
  have hvM : (v : ModGL τ K) ∈ monomialSubgroup τ K := torusGroup_le_monomialSubgroup
    (TableBExc.mem_torusPow.1 hv).1
  have hc := hN.conj_mem ⟨(v : ModGL τ K), hvM⟩
    (Subgroup.mem_subgroupOf.2 (TableBExc.mem_torusPow.1 hv).1)
    ⟨(n : ModGL τ K), Subgroup.mem_subgroupOf.1 hn⟩
  refine ⟨Subgroup.mem_subgroupOf.1 hc, ?_⟩
  rw [conj_pow, (TableBExc.mem_torusPow.1 hv).2, mul_one, mul_inv_cancel]

end

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
