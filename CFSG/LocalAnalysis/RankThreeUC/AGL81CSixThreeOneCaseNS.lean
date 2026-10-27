module

import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneHallHigman
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCenter
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneTrace
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneQD
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndCrit
import CFSG.LargeExtraspecial.S9FiveB
import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open scoped commutatorElement

private theorem sq_mem_center_of_commutator_mem_zpowers {P : Type*} [Group P] {z : P}
    (hz : z ∈ Subgroup.center P) (hzord : orderOf z = 2)
    (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.zpowers z) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hc := hcomm x y
  have hcz : ⁅x, y⁆ ∈ Subgroup.center P := (Subgroup.zpowers_le.mpr hz) hc
  have hxy : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  have hcx : x * ⁅x, y⁆ = ⁅x, y⁆ * x := Subgroup.mem_center_iff.mp hcz x
  have hc2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    rcases (CFSG.RankThree.GroupTheory.SteinbergBY.mem_zpowers_of_orderOf_eq_two hzord).mp hc
      with h | h
    · rw [h]; simp
    · rw [h]
      have hz2 : z ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
      rw [← pow_two]
      exact hz2
  have h1 : x ^ 2 * y = y * x ^ 2 := by
    calc x ^ 2 * y = x * (x * y) := by rw [pow_two]; group
      _ = x * (⁅x, y⁆ * (y * x)) := by rw [hxy]
      _ = (x * ⁅x, y⁆) * (y * x) := by group
      _ = (⁅x, y⁆ * x) * (y * x) := by rw [hcx]
      _ = ⁅x, y⁆ * (x * y) * x := by group
      _ = ⁅x, y⁆ * (⁅x, y⁆ * (y * x)) * x := by rw [hxy]
      _ = (⁅x, y⁆ * ⁅x, y⁆) * (y * (x * x)) := by group
      _ = y * x ^ 2 := by rw [hc2, one_mul, pow_two]
  exact h1.symm

private theorem map_le_center_of_characteristic_abelian {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hG : oPPrimeHull p G = G)
    (hO : CFSG.pCore p ↥G = ⊥) {A : Subgroup ↥(CFSG.pCore 2 ↥G)}
    (hA : A.Characteristic) (hab : IsMulCommutative ↥A) :
    A.map (CFSG.pCore 2 ↥G).subtype ≤ Subgroup.center ↥G := by
  classical
  let Q := CFSG.pCore 2 ↥G
  haveI : Q.Normal := CFSG.pCore_normal
  haveI : A.Characteristic := hA
  have hAn : (A.map Q.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  haveI : (A.map Q.subtype).Normal := hAn
  have hQp : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  have hAp : IsPGroup 2 ↥(A.map Q.subtype) := hQp.to_le (Subgroup.map_subtype_le A)
  have hAs : IsSolvable ↥(A.map Q.subtype) := @IsNilpotent.to_isSolvable _ _ hAp.isNilpotent
  refine le_center_of_solvable_normal hp5 (σ := Fin 2 ⊕ Fin 2) (by simp) hG hO _
    hAs ?_
  intro _ S a _ b _
  haveI : IsMulCommutative ↥A := hab
  exact isMulCommutative_iff.mp (Subgroup.map_isMulCommutative A Q.subtype) a b

private theorem eq_one_or_neg_one_of_mem_statedSp_of_matrix_eq_scalar [Fact (Nat.Prime 5)]
    {g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)} (hg : g ∈ CFSG.Open.StatedSp 2 (ZMod 5))
    {c : ZMod 5} (hc : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
      Matrix.scalar (Fin 2 ⊕ Fin 2) c) :
    g = 1 ∨ g = -1 := by
  have hmem := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := 2) (K := ZMod 5)).mp hg
  rw [hc] at hmem
  have hsq : c * c = 1 := by
    have hentry := congrFun (congrFun hmem (Sum.inl 0)) (Sum.inr 0)
    simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.fromBlocks_apply₁₂] using hentry
  have hfac : (c - 1) * (c + 1) = 0 := by
    have h : (c - 1) * (c + 1) = c * c - 1 := by ring
    rw [h, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · left
    apply Units.ext
    rw [hc, show c = 1 from sub_eq_zero.mp h, Units.val_one]
    rw [← Matrix.diagonal_one (n := Fin 2 ⊕ Fin 2) (α := ZMod 5)]
    rw [Matrix.scalar_apply]
  · right
    apply Units.ext
    rw [hc, show c = -1 from eq_neg_of_add_eq_zero_left h, Units.val_neg, Units.val_one]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.neg_apply]
      rfl
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.neg_apply,
        hij]
      exact neg_zero.symm

private theorem le_center_of_five_elements_centralize [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (h : ∀ x : ↥G, orderOf x = 5 → ∀ q ∈ CFSG.pCore 2 ↥G, x * q = q * x) :
    CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G := by
  let Q := CFSG.pCore 2 ↥G
  have hσ : Fintype.card (Fin 2 ⊕ Fin 2) < 5 := by
    have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
    rw [hcard]
    norm_num
  have hle : oPPrimeHull 5 (⊤ : Subgroup ↥G) ≤ Subgroup.centralizer (Q : Set ↥G) := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨-, k, hk⟩
    have hx5k : x ^ 5 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hx5 : x ^ 5 = 1 :=
      pow_prime_eq_one_of_card_lt (G := G) hσ hx5k
    by_cases hx1 : x = 1
    · subst hx1
      exact Subgroup.one_mem _
    · exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (h x (orderOf_eq_prime hx5 hx1) q hq).symm
  rw [oPPrimeHull_top_of_eq hG] at hle
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) q hq).symm

private theorem neg_one_mem_map_of_eq_neg_one {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))}
    {Q : Subgroup ↥G} {z : ↥Q}
    (hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1) :
    (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) ∈ Q.map G.subtype := by
  rw [← hzneg]
  exact Subgroup.mem_map_of_mem G.subtype z.2

private theorem eq_one_or_neg_one_of_mem_map_of_centralizer
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} {Q : Subgroup ↥G} {z : ↥Q}
    (hzcenter : Subgroup.center ↥Q = Subgroup.zpowers z) (hzord : orderOf z = 2)
    (hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1) :
    ∀ w ∈ Q.map G.subtype, (∀ v ∈ Q.map G.subtype, w * v = v * w) → w = 1 ∨ w = -1 := by
  rintro w ⟨x, hx, rfl⟩ hxw
  have hxQ : (⟨x, hx⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Q.subtype_injective
    apply G.subtype_injective
    have h := hxw (G.subtype (y : ↥G)) (Subgroup.mem_map_of_mem G.subtype y.2)
    simpa using h.symm
  have hxz : (⟨x, hx⟩ : ↥Q) ∈ Subgroup.zpowers z := by rw [← hzcenter]; exact hxQ
  rcases (CFSG.RankThree.GroupTheory.SteinbergBY.mem_zpowers_of_orderOf_eq_two hzord).mp hxz
    with h1 | hz1
  · left
    simpa using congrArg (fun t : ↥Q => (t : GL (Fin 2 ⊕ Fin 2) (ZMod 5))) h1
  · right
    exact (congrArg (fun t : ↥Q => (t : GL (Fin 2 ⊕ Fin 2) (ZMod 5))) hz1).trans hzneg

private theorem commutator_eq_one_or_neg_one_of_mem_map
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} {Q : Subgroup ↥G} {z : ↥Q}
    (hzord : orderOf z = 2)
    (hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1)
    (hzcomm : ∀ x y : ↥Q, ⁅x, y⁆ ∈ Subgroup.zpowers z) :
    ∀ w ∈ Q.map G.subtype, ∀ v ∈ Q.map G.subtype,
      w * v * w⁻¹ * v⁻¹ = 1 ∨ w * v * w⁻¹ * v⁻¹ = -1 := by
  rintro w ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  let xQ : ↥Q := ⟨x, hx⟩
  let yQ : ↥Q := ⟨y, hy⟩
  have hc : ⁅xQ, yQ⁆ ∈ Subgroup.zpowers z := hzcomm xQ yQ
  have hmap : G.subtype x * G.subtype y * (G.subtype x)⁻¹ * (G.subtype y)⁻¹ =
      ((⁅xQ, yQ⁆ : ↥Q) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) := by
    simp [commutatorElement_def, xQ, yQ, Subgroup.coe_mul, Subgroup.coe_inv]
  rcases (CFSG.RankThree.GroupTheory.SteinbergBY.mem_zpowers_of_orderOf_eq_two hzord).mp hc
    with h1 | hz1
  · left
    have h1' : ((⁅xQ, yQ⁆ : ↥Q) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 := by
      rw [h1]; simp
    rw [hmap, h1']
  · right
    have hzGL : ((⁅xQ, yQ⁆ : ↥Q) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 := by
      rw [hz1]; simpa using hzneg
    rw [hmap]
    exact hzGL

private theorem trace_le_and_scalar_of_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} {Q : Subgroup ↥G} [Q.Normal] {z : ↥Q}
    (hzcenter : Subgroup.center ↥Q = Subgroup.zpowers z) (hzord : orderOf z = 2)
    (hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1)
    (hzcomm : ∀ x y : ↥Q, ⁅x, y⁆ ∈ Subgroup.zpowers z) :
    Nat.card ↥Q ≤ 32 ∧
      (Nat.card ↥Q = 32 → ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5),
        (∀ w ∈ Q.map G.subtype, w * M = M * w) →
          ∃ c : ZMod 5, M = Matrix.scalar (Fin 2 ⊕ Fin 2) c) := by
  have h20 : (2 : ZMod 5) ≠ 0 := by
    intro h
    have hdvd : 5 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 5).mp h
    norm_num at hdvd
  have h40 : ((Fintype.card (Fin 2 ⊕ Fin 2) : ZMod 5)) ≠ 0 := by
    have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
    rw [hcard]
    intro h
    have hdvd : 5 ∣ 4 := (ZMod.natCast_eq_zero_iff 4 5).mp h
    norm_num at hdvd
  have htrace := card_le_and_scalar_of_symplecticType (F := ZMod 5) (σ := Fin 2 ⊕ Fin 2)
    h20 h40 (neg_one_mem_map_of_eq_neg_one hzneg)
    (eq_one_or_neg_one_of_mem_map_of_centralizer hzcenter hzord hzneg)
    (commutator_eq_one_or_neg_one_of_mem_map hzord hzneg hzcomm)
  have hcard : Nat.card ↥(Q.map G.subtype) = Nat.card ↥Q :=
    Subgroup.card_map_of_injective G.subtype_injective
  refine ⟨?_, ?_⟩
  · have h := htrace.1
    rw [hcard] at h
    simpa using h
  · intro h32 M hM
    exact htrace.2 (by rw [hcard, h32]; norm_num) M hM

private theorem eq_one_or_neg_one_of_commute_of_card_thirty_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod 5))
    {Q : Subgroup ↥G} [Q.Normal] (hcard : Nat.card ↥Q = 32)
    (hscalar : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5),
      (∀ w ∈ Q.map G.subtype, w * M = M * w) →
        ∃ c : ZMod 5, M = Matrix.scalar (Fin 2 ⊕ Fin 2) c)
    {g : ↥G} (hgcomm : ∀ q ∈ Q, g * q = q * g) :
    (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1 ∨
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 := by
  have hgM : ∀ w ∈ Q.map G.subtype,
      (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) *
        ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
      ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) * w := by
    rintro w ⟨x, hx, rfl⟩
    have hx' : (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) * x = x * (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) :=
      congrArg (fun t : ↥G => (t : GL (Fin 2 ⊕ Fin 2) (ZMod 5))) (hgcomm x hx)
    exact (congrArg (fun u : GL (Fin 2 ⊕ Fin 2) (ZMod 5) =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))) hx').symm
  obtain ⟨c, hc⟩ := hscalar _ hgM
  exact eq_one_or_neg_one_of_mem_statedSp_of_matrix_eq_scalar (hGS g.2) hc

private theorem eq_five_of_not_le_center_pCore_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hG : oPPrimeHull p G = G)
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) : p = 5 := by
  by_contra hpne
  have hO : CFSG.pCore p ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 ↥G) := CFSG.pCore_isPGroup
  have hQsolv : IsSolvable ↥(CFSG.pCore 2 ↥G) :=
    @IsNilpotent.to_isSolvable _ _ hQp.isNilpotent
  exact hO2 (le_center_of_solvable_normal hp5 (σ := Fin 2 ⊕ Fin 2) (by simp) hG hO
    (CFSG.pCore 2 ↥G) hQsolv (fun h => absurd h hpne))

private theorem not_isMulCommutative_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    ¬ IsMulCommutative ↥(CFSG.pCore 2 ↥G) := by
  intro hcomm
  apply hO2
  have hO : CFSG.pCore 5 ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 ↥G) := CFSG.pCore_isPGroup
  have hQsolv : IsSolvable ↥(CFSG.pCore 2 ↥G) :=
    @IsNilpotent.to_isSolvable _ _ hQp.isNilpotent
  refine le_center_of_solvable_normal (p := 5) (by norm_num) (σ := Fin 2 ⊕ Fin 2) (by simp)
    hG hO (CFSG.pCore 2 ↥G) hQsolv ?_
  intro _ S a _ b _
  exact isMulCommutative_iff.mp hcomm a b

private theorem structure_of_central_pCore_two [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    IsCyclic ↥(CFSG.pCore 2 ↥G) ∨
      ∃ z ∈ Subgroup.center ↥(CFSG.pCore 2 ↥G), orderOf z = 2 ∧
        (∀ x ∈ Subgroup.center ↥(CFSG.pCore 2 ↥G), orderOf x = 2 → x = z) ∧
        (∀ x y : ↥(CFSG.pCore 2 ↥G), ⁅x, y⁆ ∈ Subgroup.zpowers z) ∧
        ∃ E : Subgroup ↥(CFSG.pCore 2 ↥G),
          E ⊔ Subgroup.center ↥(CFSG.pCore 2 ↥G) = ⊤ ∧
          E ⊓ Subgroup.center ↥(CFSG.pCore 2 ↥G) = Subgroup.zpowers z ∧
          ∃ w : ℕ, 1 ≤ w ∧
            Nat.card (↥(CFSG.pCore 2 ↥G) ⧸ Subgroup.center ↥(CFSG.pCore 2 ↥G)) =
              2 ^ (2 * w) := by
  let Q := CFSG.pCore 2 ↥G
  have hQp : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  have hO : CFSG.pCore 5 ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hO2
    change Q ≤ Subgroup.center ↥G
    rw [hbot]
    exact bot_le
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hsymp : ∀ A : Subgroup ↥Q, A.Characteristic → IsMulCommutative ↥A → IsCyclic ↥A := by
    intro A hA hab
    have hmap := map_le_center_of_characteristic_abelian (p := 5) (by norm_num) hG hO hA hab
    haveI : IsCyclic ↥(Subgroup.center ↥G) := isCyclic_center_of_isIrreducibleOn hirr
    haveI : IsCyclic ↥(A.map Q.subtype) :=
      isCyclic_of_injective (Subgroup.inclusion hmap) (Subgroup.inclusion_injective hmap)
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective A Q.subtype Q.subtype_injective)).mpr
      ‹IsCyclic ↥(A.map Q.subtype)›
  have hcen : ∀ A : Subgroup ↥Q, A.Characteristic → IsMulCommutative ↥A →
      A ≤ Subgroup.center ↥Q := by
    intro A hA hab
    have hmap := map_le_center_of_characteristic_abelian (p := 5) (by norm_num) hG hO hA hab
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.mp (hmap (Subgroup.mem_map_of_mem Q.subtype ha)) (q : ↥G)
  exact CFSG.RankThree.PartTwo.Sec4.Census.structure_of_central (P := ↥Q) hQp hsymp hcen

private theorem center_eq_zpowers_and_neg_one_of_mem_center [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod 5)) (hG : oPPrimeHull 5 G = G)
    (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    {z : ↥(CFSG.pCore 2 ↥G)} (hz : z ∈ Subgroup.center ↥(CFSG.pCore 2 ↥G))
    (hzord : orderOf z = 2) :
    Subgroup.center ↥(CFSG.pCore 2 ↥G) = Subgroup.zpowers z ∧
      ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 := by
  let Q := CFSG.pCore 2 ↥G
  have hQp : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  have hO : CFSG.pCore 5 ↥G = ⊥ := pCore_eq_bot_of_isIrreducibleOn hirr
  have hZchar : (Subgroup.center ↥Q).Characteristic := Subgroup.centerCharacteristic
  have hZle : (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.center ↥G :=
    map_le_center_of_characteristic_abelian (p := 5) (by norm_num) hG hO hZchar inferInstance
  have hZimage : IsPGroup 2 ↥((Subgroup.center ↥Q).map Q.subtype) :=
    (hQp.to_subgroup (Subgroup.center ↥Q)).map Q.subtype
  have hZcard_le_image : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) ≤ 2 :=
    card_le_two_of_le_center (p := 5) rfl hGS hirr hZimage hZle
  have hZcard_le : Nat.card ↥(Subgroup.center ↥Q) ≤ 2 := by
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at hZcard_le_image
  have hZcard_ge : 2 ≤ Nat.card ↥(Subgroup.center ↥Q) := by
    have hcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
    have hdvd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
    rw [hcard] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = 2 := le_antisymm hZcard_le hZcard_ge
  have hZeq' : Subgroup.zpowers z = Subgroup.center ↥Q := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZcard, Nat.card_zpowers, hzord]
  have hZeq : Subgroup.center ↥Q = Subgroup.zpowers z := hZeq'.symm
  have hzG_center : Q.subtype z ∈ Subgroup.center ↥G :=
    hZle (Subgroup.mem_map_of_mem Q.subtype hz)
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hzG2 : Q.subtype z ^ 2 = 1 := by
    rw [← map_pow, hz2, map_one]
  have hzG1 : Q.subtype z ≠ 1 := by
    intro h
    have hz1 : z = 1 := Q.subtype_injective h
    rw [hz1, orderOf_one] at hzord
    omega
  have hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 :=
    eq_neg_one_of_mem_center hirr hzG_center hzG2 hzG1
  exact ⟨hZeq, hzneg⟩

private theorem card_eq_eight_or_thirty_two {Q : Type*} [Group Q] {z : Q}
    (hZeq : Subgroup.center Q = Subgroup.zpowers z) (hzord : orderOf z = 2) {w : ℕ}
    (hw1 : 1 ≤ w) (hquot : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ (2 * w))
    (hle : Nat.card Q ≤ 32) : Nat.card Q = 8 ∨ Nat.card Q = 32 := by
  have hcard : Nat.card Q = 2 ^ (2 * w) * 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
    rw [hquot, hZeq, Nat.card_zpowers, hzord] at h
    exact h
  have h2w : 2 * w ≤ 4 := by
    have hle' : 2 ^ (2 * w) * 2 ≤ 2 ^ 4 * 2 := by
      calc 2 ^ (2 * w) * 2 = Nat.card Q := hcard.symm
        _ ≤ 32 := hle
        _ = 2 ^ 4 * 2 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (Nat.le_of_mul_le_mul_right hle' (by norm_num))
  have hw : w = 1 ∨ w = 2 := by omega
  rcases hw with rfl | rfl
  · left; rw [hcard]; norm_num
  · right; rw [hcard]; norm_num

private theorem false_of_card_eight [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G)
    (hcard : Nat.card ↥(CFSG.pCore 2 ↥G) = 8) : False := by
  let Q := CFSG.pCore 2 ↥G
  have hQn : Q.Normal := CFSG.pCore_normal
  have hσ : Fintype.card (Fin 2 ⊕ Fin 2) < 5 := by
    have hc : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
    rw [hc]; norm_num
  have hle : oPPrimeHull 5 (⊤ : Subgroup ↥G) ≤ Subgroup.centralizer (Q : Set ↥G) := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨-, k, hk⟩
    have hx5k : x ^ 5 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hx5 : x ^ 5 = 1 :=
      pow_prime_eq_one_of_card_lt (G := G) hσ hx5k
    refine Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (commute_of_card_eight hcard hx5 ?_ q hq).symm
    intro q hq
    exact hQn.conj_mem q hq x
  rw [oPPrimeHull_top_of_eq hG] at hle
  apply hO2
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) q hq).symm

private theorem isExtraspecialPGroup_of_center_zpowers {Q : Type*} [Group Q] [Finite Q]
    (hQp : IsPGroup 2 Q) {z : Q} (hZeq : Subgroup.center Q = Subgroup.zpowers z)
    (hzord : orderOf z = 2) (hzcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers z)
    (hnab : ∃ x : Q, x ∉ Subgroup.zpowers z) : CFSG.IsExtraspecialPGroup 2 Q := by
  have hz : z ∈ Subgroup.center Q := by rw [hZeq]; exact Subgroup.mem_zpowers z
  have hsq : ∀ x : Q, x ^ 2 ∈ Subgroup.zpowers z := by
    intro x
    have h := sq_mem_center_of_commutator_mem_zpowers hz hzord hzcomm x
    rwa [hZeq] at h
  have hcent : ∀ x : Q, (∀ y : Q, x * y = y * x) → x ∈ Subgroup.zpowers z := by
    intro x hx
    rw [← hZeq]
    exact Subgroup.mem_center_iff.mpr fun y => (hx y).symm
  exact CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hQp
    (by rw [Nat.card_zpowers, hzord]) (Subgroup.zpowers_le.mpr hz) hzcomm hsq hcent hnab

private theorem exists_mulAut_order_five_of_not_le_center [Fact (Nat.Prime 5)]
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 5))} (hG : oPPrimeHull 5 G = G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    ∃ α : MulAut ↥(CFSG.pCore 2 ↥G), orderOf α = 5 := by
  have hnotall : ¬ ∀ x : ↥G, orderOf x = 5 →
      ∀ q ∈ CFSG.pCore 2 ↥G, x * q = q * x := by
    intro hall
    exact hO2 (le_center_of_five_elements_centralize hG hall)
  push Not at hnotall
  obtain ⟨x, hxord, q0, hq0, hxq0⟩ := hnotall
  have hx5 : x ^ 5 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxord] at h
  have hxN : x ∈ Subgroup.normalizer (CFSG.pCore 2 ↥G : Set ↥G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  let α : MulAut ↥(CFSG.pCore 2 ↥G) :=
    (CFSG.pCore 2 ↥G).normalizerMonoidHom ⟨x, hxN⟩
  refine ⟨α, ?_⟩
  have hα5 : α ^ 5 = 1 := by
    change ((CFSG.pCore 2 ↥G).normalizerMonoidHom ⟨x, hxN⟩) ^ 5 = 1
    rw [← map_pow, show (⟨x, hxN⟩ :
      ↥(Subgroup.normalizer (CFSG.pCore 2 ↥G : Set ↥G))) ^ 5 = 1 from
      Subtype.ext (by simpa using hx5), map_one]
  have hαne : α ≠ 1 := by
    intro hα1
    apply hxq0
    have hq : α ⟨q0, hq0⟩ = ⟨q0, hq0⟩ := by rw [hα1]; rfl
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe (CFSG.pCore 2 ↥G) ⟨x, hxN⟩
      ⟨q0, hq0⟩
    have hq' := congrArg (fun t : ↥(CFSG.pCore 2 ↥G) => (t : ↥G)) hq
    rw [hq'] at hcoe
    have hconj : (q0 : ↥G) = x * q0 * x⁻¹ := by simpa using hcoe
    calc x * q0 = (x * q0 * x⁻¹) * x := by group
      _ = q0 * x := by rw [← hconj]
  have hdvd : orderOf α ∣ 5 := orderOf_dvd_of_pow_eq_one hα5
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
  · exact absurd (orderOf_eq_one_iff.mp h1) hαne
  · exact h5

private theorem isQ8D8Type_of_structure [Fact (Nat.Prime 5)]
    {Q : Type} [Group Q] [Finite Q] {z : Q} (hQp : IsPGroup 2 Q)
    (hZeq : Subgroup.center Q = Subgroup.zpowers z) (hzord : orderOf z = 2)
    (hzcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers z)
    (hnab : ∃ x : Q, x ∉ Subgroup.zpowers z) (hcard : Nat.card Q = 32)
    (α : MulAut Q) (hα : orderOf α = 5) : IsQ8D8Type Q :=
  isQ8D8Type_of_extraspecial
    (isExtraspecialPGroup_of_center_zpowers hQp hZeq hzord hzcomm hnab) hcard α hα

theorem structure_of_pCore_two_not_le_center {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : oPPrimeHull p G = G) (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    p = 5 ∧ IsQ8D8Type ↥(CFSG.pCore 2 ↥G) ∧ Nat.card ↥(CFSG.pCore 2 ↥G) = 32 ∧
      ∀ g : ↥G, (∀ q ∈ CFSG.pCore 2 ↥G, g * q = q * g) →
        (g : GL (Fin 2 ⊕ Fin 2) (ZMod p)) = 1 ∨
          (g : GL (Fin 2 ⊕ Fin 2) (ZMod p)) = -1 := by
  classical
  have hp_eq : p = 5 := eq_five_of_not_le_center_pCore_two hp5 hG hirr hO2
  subst hp_eq
  let Q : Subgroup ↥G := CFSG.pCore 2 ↥G
  have hQnab : ¬ IsMulCommutative ↥Q := not_isMulCommutative_pCore_two hG hirr hO2
  rcases structure_of_central_pCore_two hG hirr hO2 with
    hcyc | ⟨z, hz, hzord, -, hzcomm, -, -, -, w, hw1, hquot⟩
  · exfalso
    haveI : IsCyclic ↥Q := hcyc
    exact hQnab IsCyclic.isMulCommutative
  obtain ⟨hZeq, hzneg⟩ := center_eq_zpowers_and_neg_one_of_mem_center hGS hG hirr hz hzord
  have htrace := trace_le_and_scalar_of_pCore_two hZeq hzord hzneg hzcomm
  rcases card_eq_eight_or_thirty_two hZeq hzord hw1 hquot htrace.1 with hcard8 | hcard32
  · exfalso
    exact false_of_card_eight hG hO2 hcard8
  · have hna : ∃ x : ↥Q, x ∉ Subgroup.zpowers z := by
      by_contra h
      push Not at h
      apply hQnab
      exact isMulCommutative_iff.mpr fun a b =>
        (Subgroup.mem_center_iff.mp (by rw [hZeq]; exact h a) b).symm
    obtain ⟨α, hα⟩ := exists_mulAut_order_five_of_not_le_center hG hO2
    have hQ8 : IsQ8D8Type ↥Q :=
      isQ8D8Type_of_structure (CFSG.pCore_isPGroup (p := 2) (G := ↥G)) hZeq hzord hzcomm hna
        hcard32 α hα
    exact ⟨rfl, hQ8, hcard32,
      fun g hgcomm =>
        eq_one_or_neg_one_of_commute_of_card_thirty_two hGS hcard32 (htrace.2 hcard32) hgcomm⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
