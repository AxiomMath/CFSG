module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI2a0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma dI2a_closure_pair_iff {a b u : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    u ∈ closure ({a, b} : Set G) ↔ u = 1 ∨ u = a ∨ u = b ∨ u = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private lemma dI2a_y_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) : x₁ ^ 2 * x₁ ^ 2 = 1 := by
  have h4 : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [h.c11.wreath.ord_x₁] at this
  rw [← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4]

private lemma dI2a_y_z_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
  CFSG.Open.IsElemAbelian.comm (WreathRel.fourGrp_eq_omega h.c11.wreath).2.1
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma dI2a_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om) (u : G) :
    u ∈ fourGrp x₁ x₂ ↔
      u = 1 ∨ u = x₁ ^ 2 ∨ u = (x₁ * x₂) ^ 2 ∨ u = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  rw [fourGrp]
  exact dI2a_closure_pair_iff (dI2a_y_sq h) h.c11.wreath.sq_x₁x₂_mul_self
    (dI2a_y_z_comm h)

private lemma dI2a_z4pow2_pow_four (x : Outside.Z4pow 2) : x ^ 4 = 1 := by
  revert x
  decide +kernel

private lemma dI2a_A_pow_four (h : Q13Om t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho) : a ^ 4 = 1 := by
  obtain ⟨e⟩ := q13a_A_iso h
  have h2 : (⟨a, ha⟩ : ↥(q13A t tau x₁ x₂ rho)) ^ 4 = 1 :=
    e.injective (by rw [map_pow, dI2a_z4pow2_pow_four, map_one])
  simpa using congrArg Subtype.val h2

private noncomputable def dI2a_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) →*
      ↥(fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G)) where
  toFun a :=
    ⟨(a : G) * (a : G), by
      have haA : (a : G) ∈ q13A t tau x₁ x₂ rho := (Subgroup.mem_inf.mp a.2).1
      have hcomm : (a : G) * lam = lam * (a : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp a.2).2
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hs : ((a : G) * (a : G)) * ((a : G) * (a : G)) = 1 := by
          calc ((a : G) * (a : G)) * ((a : G) * (a : G))
              = (a : G) ^ 2 * (a : G) ^ 2 := by rw [pow_two]
            _ = (a : G) ^ 4 := by rw [← pow_add]
            _ = 1 := dI2a_A_pow_four h haA
        exact q13b_omega1_A h ((a : G) * (a : G)) (Subgroup.mul_mem _ haA haA) hs
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc ((a : G) * (a : G)) * lam = (a : G) * ((a : G) * lam) := by group
          _ = (a : G) * (lam * (a : G)) := by rw [hcomm]
          _ = ((a : G) * lam) * (a : G) := by group
          _ = (lam * (a : G)) * (a : G) := by rw [hcomm]
          _ = lam * ((a : G) * (a : G)) := by group⟩
  map_one' := Subtype.ext (by simp)
  map_mul' := by
    intro a b
    apply Subtype.ext
    show ((a : G) * (b : G)) * ((a : G) * (b : G)) =
      ((a : G) * (a : G)) * ((b : G) * (b : G))
    calc ((a : G) * (b : G)) * ((a : G) * (b : G))
        = (a : G) * ((b : G) * ((a : G) * (b : G))) := by group
      _ = (a : G) * ((b : G) * (a : G)) * (b : G) := by group
      _ = (a : G) * ((a : G) * (b : G)) * (b : G) := by
            rw [q13a_A_comm h (b : G) (Subgroup.mem_inf.mp b.2).1 (a : G)
              (Subgroup.mem_inf.mp a.2).1]
      _ = ((a : G) * (a : G)) * ((b : G) * (b : G)) := by group

private lemma dI2a_sq_coe (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (a : ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G))) :
    ((dI2a_sq h a : ↥(fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G))) : G) =
      (a : G) * (a : G) := rfl

private lemma dI2a_sq_ker (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (dI2a_sq h).ker =
      (fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G)).subgroupOf
        (q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hsq
    have hval : (a : G) * (a : G) = 1 := by
      rw [← dI2a_sq_coe h a]
      exact congrArg Subtype.val hsq
    exact ⟨q13b_omega1_A h (a : G) (Subgroup.mem_inf.mp a.2).1 hval,
      (Subgroup.mem_inf.mp a.2).2⟩
  · rintro ⟨hV, _⟩
    apply Subtype.ext
    show (a : G) * (a : G) = 1
    have h2 := ((WreathRel.fourGrp_eq_omega h.c11.wreath).2.1).2 (a : G) hV
    simpa [pow_two] using h2

private lemma dI2a_CV_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G) = zpowers ((x₁ * x₂) ^ 2) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    have hcomm : v * lam = lam * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have hfix : lam * v * lam⁻¹ = v := by
      calc lam * v * lam⁻¹ = (v * lam) * lam⁻¹ := by rw [← hcomm]
        _ = v := by group
    rcases (dI2a_mem_V h v).mp hvV with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exfalso
      have hy : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 * 1 := by
        rw [← (q13c_lam_y h), hfix, mul_one]
      exact (q13b_z_facts h).1 (mul_left_cancel hy)
    · exact Subgroup.mem_zpowers _
    · exfalso
      have hconj : lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹ = x₁ ^ 2 := by
        calc lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹
            = (lam * x₁ ^ 2 * lam⁻¹) * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) := by group
          _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by
                rw [q13c_lam_y h]
                congr 1
                calc lam * (x₁ * x₂) ^ 2 * lam⁻¹ = ((x₁ * x₂) ^ 2 * lam) * lam⁻¹ := by
                      rw [q13c_lam_z h]
                  _ = (x₁ * x₂) ^ 2 := by group
          _ = x₁ ^ 2 := by
                rw [mul_assoc, (q13b_z_facts h).2, mul_one]
      have hy : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 * 1 := by
        rw [← hfix, hconj, mul_one]
      exact (q13b_z_facts h).1 (mul_left_cancel hy)
  · rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    refine ⟨Subgroup.subset_closure (by simp), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (q13c_lam_z h).symm

private lemma dI2a_D_card (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [dI2a_CV_eq h, Nat.card_zpowers]
  exact orderOf_eq_prime (by simpa [pow_two] using (q13b_z_facts h).2) (q13b_z_facts h).1

private lemma dI2a_sq_ker_card (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card (dI2a_sq h).ker = 2 := by
  have hDC : fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G) ≤
      q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G) := by
    intro x hx
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨q13a_V_le_A h hxV, hxC⟩
  rw [dI2a_sq_ker h,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
  exact dI2a_D_card h

private theorem dI2a_C_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) ≤ 4 := by
  let A := q13A t tau x₁ x₂ rho
  let C := A ⊓ centralizer ({lam} : Set G)
  let D := fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G)
  change Nat.card ↥C ≤ 4
  have hDC : D ≤ C := by
    intro x hx
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨q13a_V_le_A h hxV, hxC⟩
  have hker : Nat.card (dI2a_sq h).ker = 2 := by
    have hkereq : (dI2a_sq h).ker = D.subgroupOf C := dI2a_sq_ker h
    rw [hkereq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact dI2a_D_card h
  have hrange : Nat.card (dI2a_sq h).range ≤ 2 := by
    calc Nat.card (dI2a_sq h).range ≤ Nat.card ↥D :=
          Subgroup.card_le_card_group (H := (dI2a_sq h).range)
      _ = 2 := dI2a_D_card h
  have hcard := card_ker_mul_card_range (dI2a_sq h)
  rw [hker] at hcard
  calc Nat.card ↥C = 2 * Nat.card (dI2a_sq h).range := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hrange
    _ = 4 := by norm_num

private theorem dI2a_exists (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∃ a ∈ q13A t tau x₁ x₂ rho, lam * a * lam⁻¹ = a ∧ a * a = (x₁ * x₂) ^ 2 := by
  let A := q13A t tau x₁ x₂ rho
  let C := A ⊓ centralizer ({lam} : Set G)
  let D := fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G)
  have hCcard : Nat.card ↥C = 4 := by
    change Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) = 4
    exact le_antisymm (dI2a_C_le h) (q13d_card_CA_lam_ge h)
  have hDcard : Nat.card ↥D = 2 := dI2a_D_card h
  have hker : Nat.card (dI2a_sq h).ker = 2 := dI2a_sq_ker_card h
  have hrange : Nat.card (dI2a_sq h).range = 2 := by
    have hcard := card_ker_mul_card_range (dI2a_sq h)
    rw [hker, hCcard] at hcard
    omega
  have htop : (dI2a_sq h).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hrange, hDcard])
  have hzD : (x₁ * x₂) ^ 2 ∈ D := by
    change (x₁ * x₂) ^ 2 ∈ (fourGrp x₁ x₂ ⊓ centralizer ({lam} : Set G))
    rw [dI2a_CV_eq h]
    exact Subgroup.mem_zpowers _
  have hzmem : (⟨(x₁ * x₂) ^ 2, hzD⟩ : ↥D) ∈ (dI2a_sq h).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨c, hc⟩ := hzmem
  have hcz : (c : G) * (c : G) = (x₁ * x₂) ^ 2 := by
    have hcc : ((dI2a_sq h c : ↥D) : G) = (x₁ * x₂) ^ 2 := by rw [hc]
    rwa [dI2a_sq_coe h c] at hcc
  refine ⟨(c : G), (Subgroup.mem_inf.mp c.2).1, ?_, hcz⟩
  have hcomm : (c : G) * lam = lam * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
  calc lam * (c : G) * lam⁻¹ = (lam * (c : G)) * lam⁻¹ := rfl
    _ = ((c : G) * lam) * lam⁻¹ := by rw [← hcomm]
    _ = (c : G) := by group

theorem q13d_card_CA_lam_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) ≤ 4 :=
  dI2a_C_le h

theorem q13d_exists_a_sq_z (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∃ a ∈ q13A t tau x₁ x₂ rho, lam * a * lam⁻¹ = a ∧ a * a = (x₁ * x₂) ^ 2 :=
  dI2a_exists h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
