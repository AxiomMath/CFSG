module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod 3)

theorem sl_ext {n : ℕ} {a b : SL(n, ZMod 3)} (h : (a : Mat n) = b) : a = b :=
  Subtype.ext h

theorem exists_mulEquiv_sl5 {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSL 5 3 1) :
    Nonempty (X ≃* SL(5, ZMod 3)) := by
  classical
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  have hbot : scalars 5 K = ⊥ := by
    rw [eq_bot_iff]
    rintro A ⟨c, hc, hA⟩
    have h2 : c ^ 2 = 1 := by
      have := pow_card_eq_one (G := Kˣ) (x := c)
      rwa [Fintype.card_units, hK3] at this
    have hc1 : c = 1 := by
      calc c = c ^ 5 * (c ^ 2)⁻¹ ^ 2 := by group
        _ = 1 := by rw [hc, h2, inv_one, one_pow, one_mul]
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hA, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  have φ : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hK3).symm
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot.trans
    (CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 5))))⟩

theorem mul_self_of_mem_center {n : ℕ} {z : SL(n, ZMod 3)}
    (hz : z ∈ Subgroup.center (SL(n, ZMod 3))) : z * z = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by omega)] at hr
    exact zero_ne_one hr
  have hrr : r * r = 1 := (by decide : ∀ r : ZMod 3, r ≠ 0 → r * r = 1) r hr0
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, ← map_mul, hrr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_mul_self {G : Type*} [Group G] {M : Subgroup G} (hMo : Odd (Nat.card M))
    {m : G} (hm : m ∈ M) (hmm : m * m = 1) : m = 1 := by
  have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hmm])
  have hodd : Odd (orderOf m) := hMo.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hm)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem noOddNormal_top {k : ℕ} (hk : 1 ≤ k) :
    NoOddNormal (⊤ : Subgroup (SL(2 + k, ZMod 3))) := by
  intro M _ hMn hMo
  have hMn' : M.Normal := ⟨fun m hm g => by
    have := hMn.conj_mem ⟨m, Subgroup.mem_top m⟩ hm ⟨g, Subgroup.mem_top g⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this⟩
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 3) (n := 2 + k)
    (by omega) (Or.inl (by omega))).2.1
  set π := QuotientGroup.mk' (Subgroup.center (SL(2 + k, ZMod 3)))
  have := hMn'.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with h | h
  · rw [eq_bot_iff]
    intro m hm
    have hmz : m ∈ Subgroup.center _ := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center _)]
      exact (Subgroup.map_eq_bot_iff _).mp h hm
    exact eq_one_of_mul_self hMo hm (mul_self_of_mem_center hmz)
  · exfalso
    obtain ⟨m, hm, hmd⟩ : π (blockInvolution (ZMod 3) k) ∈ M.map π := h ▸ Subgroup.mem_top _
    set d := blockInvolution (ZMod 3) k with hd
    have hc : m⁻¹ * d ∈ Subgroup.center _ := QuotientGroup.eq.mp hmd
    set c := m⁻¹ * d with hcdef
    have hc2 := mul_self_of_mem_center hc
    have hd2 : d * d = 1 := by rw [hd, ← sq]; exact blockInvolution_sq
    have hcd : Commute c⁻¹ d := (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) d).symm
    have hcc : c⁻¹ * c⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hc2, inv_one]
    have hmc : m = d * c⁻¹ := by rw [hcdef]; group
    have hmm : m * m = 1 := by rw [hmc, hcd.mul_mul_mul_comm, hd2, hcc, one_mul]
    have hm1 := eq_one_of_mul_self hMo hm hmm
    rw [hcdef, hm1, inv_one, one_mul] at hc
    exact blockInvolution_not_mem_center (K := ZMod 3) (by decide) hk hc

@[expose] def u₁ : SL(2 + 3, ZMod 3) := blockInvolution (ZMod 3) 3

@[expose] def negOne₄ : SL(4, ZMod 3) := ⟨-1, by rw [Matrix.det_neg, Matrix.det_one]; decide⟩

@[expose] def blk₄ : SL(4, ZMod 3) →* SL(4 + 1, ZMod 3) := blockSL (ZMod 3) 4 1

theorem coe_blk₄ (X : SL(4, ZMod 3)) :
    ((blk₄ X : SL(4 + 1, ZMod 3)) : Mat (4 + 1)) = diagBlock (X : Mat 4) 1 :=
  rfl

@[expose] def u₂ : SL(4 + 1, ZMod 3) := blk₄ negOne₄

theorem coe_u₁ : (u₁ : Mat (2 + 3)) = diagBlock (-1) 1 :=
  coe_blockInvolution

theorem coe_u₂ : (u₂ : Mat (4 + 1)) = diagBlock (-1) 1 :=
  rfl

theorem exists_conj_u {z : SL(5, ZMod 3)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ c : SL(5, ZMod 3), c⁻¹ * z * c = u₁ ∨ c⁻¹ * z * c = u₂ := by
  have hI : (z : Matrix (Fin 5) (Fin 5) (ZMod 3)) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, ha, P, hP⟩ := ModelFacts.exists_sl_conj_diagonal (F := ZMod 3) (by decide)
    (by norm_num) hI
  set D : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
    diagonal (fun j : Fin 5 => if j.val < a then (-1 : ZMod 3) else 1) with hD
  have hdetD : D.det = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, z.2, P.2, one_mul, one_mul] at this
    exact this.symm
  set δ : SL(5, ZMod 3) := ⟨D, hdetD⟩
  have hzδ : z * P = P * δ := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hP)
  have hconj : P⁻¹ * z * P = δ := by rw [mul_assoc, hzδ, ← mul_assoc, inv_mul_cancel, one_mul]
  have hδ : (δ : Matrix (Fin 5) (Fin 5) (ZMod 3)) = D := rfl
  rw [hD, det_diagonal, Fin.prod_univ_five] at hdetD
  refine ⟨P, ?_⟩
  rw [hconj]
  interval_cases a
  · exfalso
    apply hz1
    have h1 : δ = 1 := sl_ext (by rw [hδ, hD]; decide)
    calc z = P * (P⁻¹ * z * P) * P⁻¹ := by group
      _ = 1 := by rw [hconj, h1, mul_one, mul_inv_cancel]
  · exact absurd hdetD (by decide)
  · exact Or.inl (sl_ext (by rw [hδ, coe_u₁, hD]; decide))
  · exact absurd hdetD (by decide)
  · exact Or.inr (sl_ext (by rw [hδ, coe_u₂, hD]; decide))
  · exact absurd hdetD (by decide)

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
