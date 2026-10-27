module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcTits
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.CentralCover

variable (τ : Tag) (K : Type) [Field K] [Finite K]

@[expose] noncomputable def torusN : (Fin τ.rank → Kˣ) →* ↥(monomialSub τ K) :=
  MonoidHom.codRestrict
    ((Subgroup.inclusion (torusGroup_le_adjointGroup (τ := τ) (K := K))).comp
      (torusCoordHom τ K)) (monomialSub τ K) (fun t => by
    have h1 : (Subgroup.inclusion (torusGroup_le_adjointGroup (τ := τ) (K := K))
        (torusCoordHom τ K t)) ∈ torusSub τ K := by
      rw [Subgroup.mem_subgroupOf]
      exact (torusCoordHom τ K t).2
    rw [← borelSub_inf_monomialSub] at h1
    exact h1.2)

theorem monoι_torusN (t : Fin τ.rank → Kˣ) :
    monoι τ K (torusN τ K t) = (torusCoordHom τ K t : ModGL τ K) := rfl

theorem prod_zpow_sum_aux {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (a : G) (c : ι → ℤ) :
    ∏ j ∈ s, a ^ c j = a ^ ∑ j ∈ s, c j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

@[expose] def mact {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) : Fin r → Kˣ :=
  fun k => ∏ j, t j ^ M k j

variable {K}

theorem mact_one {r : ℕ} (t : Fin r → Kˣ) : mact K (1 : Matrix (Fin r) (Fin r) ℤ) t = t := by
  ext1 k
  simp [mact, Matrix.one_apply, Finset.prod_ite_eq]

theorem mact_mul {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mact K (M * N) t = mact K M (mact K N t) := by
  ext1 k
  simp only [mact, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← prod_zpow_sum_aux]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem mact_add {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mact K (M + N) t = mact K M t * mact K N t := by
  ext1 k
  simp [mact, zpow_add, Finset.prod_mul_distrib]

theorem mact_mul_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (s t : Fin r → Kˣ) :
    mact K M (s * t) = mact K M s * mact K M t := by
  ext1 k
  simp [mact, mul_zpow, Finset.prod_mul_distrib]

@[expose] def Rmat (τ : Tag) (i : Fin τ.rank) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  1 - Matrix.of fun k j => if k = i then τ.cartan j i else 0

theorem mact_Rmat (i : Fin τ.rank) (t : Fin τ.rank → Kˣ) :
    mact K (Rmat τ i) t = t * Pi.mulSingle i (∏ j, t j ^ (-τ.cartan j i)) := by
  ext1 k
  by_cases hk : k = i
  · subst hk
    simp only [mact, Rmat, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, if_true,
      zpow_sub, Pi.mul_apply, Pi.mulSingle_eq_same, zpow_neg]
    have h : ∀ x, (t x ^ (if k = x then (1 : ℤ) else 0)) * (t x ^ τ.cartan x k)⁻¹ =
        (if k = x then t x else 1) * (t x ^ τ.cartan x k)⁻¹ := by
      intro x
      split_ifs <;> simp
    rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq]
    simp [Finset.prod_inv_distrib]
  · simp [mact, Rmat, Matrix.one_apply, hk, Finset.prod_ite_eq, Pi.mulSingle_eq_of_ne hk]

theorem conj_torusN (i : Fin τ.rank) (t : Fin τ.rank → Kˣ) :
    weylRep τ K i * torusN τ K t * (weylRep τ K i)⁻¹ = torusN τ K (mact K (Rmat τ i) t) := by
  apply monoι_injective
  rw [map_mul, map_mul, map_inv, monoι_weylRep, monoι_torusN, monoι_torusN, coe_torusCoordHom,
    weylElt_conj_listProd_torusElt, mact_Rmat, map_mul]
  have e := coe_torusCoordHom_mulSingle (τ := τ) (R := K) i (∏ j, t j ^ (-τ.cartan j i))
  rw [Subgroup.coe_mul, coe_torusCoordHom, e]

theorem torusN_comm (u v : Fin τ.rank → Kˣ) : torusN τ K u * torusN τ K v = torusN τ K v * torusN τ K u := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem weylRep_sq_eq_torusN (i : Fin τ.rank) :
    weylRep τ K i ^ 2 = torusN τ K (Pi.mulSingle i (-1)) := by
  apply monoι_injective
  rw [weylRep_sq, monoι_torusN, coe_torusCoordHom_mulSingle]

theorem Z0_le_range_torusN : Z0 τ K ≤ (torusN τ K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨_, (weylRep_sq_eq_torusN τ i).symm⟩

theorem conj_word (l : List (Fin τ.rank)) (t : Fin τ.rank → Kˣ) :
    (l.map (weylRep τ K)).prod * torusN τ K t * ((l.map (weylRep τ K)).prod)⁻¹ =
      torusN τ K (mact K (l.map (Rmat τ)).prod t) := by
  induction l generalizing t with
  | nil => simp [mact_one]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mact_mul, mul_inv_rev,
      ← conj_torusN, ← ih]
    group

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
