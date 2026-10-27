module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLc

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG
open scoped commutatorElement

theorem exists_le_of_comm_mem {G H : Type*} [Group G] [Group H] {C : Subgroup G} (Φ : C →* H)
    (hΦ : Function.Injective Φ) (T : Subgroup H) (hT : ∀ x y : C, Φ ⁅x, y⁆ ∈ T) :
    ∃ S : Subgroup G, ⁅C, C⁆ ≤ S ∧ Nat.card S ∣ Nat.card T ∧
      ∀ g (hg : g ∈ C), Φ ⟨g, hg⟩ ∈ T → g ∈ S := by
  refine ⟨(T.comap Φ).map C.subtype, ?_, ?_, fun g hg hgT => ⟨⟨g, hg⟩, hgT, rfl⟩⟩
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, hT _ _, map_commutatorElement C.subtype _ _⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective,
      ← Subgroup.card_map_of_injective hΦ]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)

theorem not_dvd_sq_SU2 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ 2 ^ (2 * padicValNat 2 (q ^ 2 - 1) + 1) ∣ (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have h0 : q * (q ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero (by omega) h2
  have := le_v2_of_dvd (Nat.mul_ne_zero h0 h0) hd dvd_rfl
  rw [padicValNat.mul h0 h0, v2_SL2 hq hq3] at this
  omega

theorem not_dvd_SU3 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ 2 ^ (2 * padicValNat 2 (q ^ 2 - 1)) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : q ^ 3 + 1 ≠ 0 := by positivity
  have hq0 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have := le_v2_of_dvd (Nat.mul_ne_zero hq0 (Nat.mul_ne_zero h2 h3)) hd dvd_rfl
  rw [padicValNat.mul hq0 (Nat.mul_ne_zero h2 h3), padicValNat.pow, v2_odd hq, mul_zero,
    zero_add, padicValNat.mul h2 h3, v2_cube_add_one hq] at this
  have hsplit := v2_sq_sub_one_split hq3
  have h1 : 1 ≤ padicValNat 2 (q - 1) := by
    obtain ⟨k, rfl⟩ := hq
    exact one_le_padicValNat_of_dvd (by omega) ⟨k, by omega⟩
  omega

theorem not_dvd_SL2_sq {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ 2 ^ (2 * padicValNat 2 (q ^ 2 - 1)) ∣ q ^ 2 * (q ^ 4 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  have h4 : q ^ 4 - 1 ≠ 0 := by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hq0 : q ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have := le_v2_of_dvd (Nat.mul_ne_zero hq0 h4) hd dvd_rfl
  rw [padicValNat.mul hq0 h4, padicValNat.pow, v2_odd hq, mul_zero, zero_add,
    v2_four hq hq3] at this
  have := three_le_v2 hq hq3
  omega

section Card

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {V : Type*}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}

theorem card_ker_unitaryDet (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd1 : 1 ≤ Module.finrank K V) :
    Nat.card (LinearGroups.unitaryDet B).ker = Nat.card (sesqSpecialUnitaryGroup B) := by
  rw [(LinearGroups.unitary_full_group_order h hB hBl rfl hd1).2.2.2.2.1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le B)).toEquiv

theorem card_sesqSU_one (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : Module.finrank K V = 1) : Nat.card (sesqSpecialUnitaryGroup B) = 1 := by
  have := (LinearGroups.unitary_full_group_order h hB hBl hd le_rfl).2.1
  rw [show (1 : ℕ) * (1 - 1) / 2 = 0 by rfl, pow_zero, one_mul,
    Finset.Icc_eq_empty (by norm_num), Finset.prod_empty] at this
  exact_mod_cast this

theorem card_sesqSU_two (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : Module.finrank K V = 2) :
    Nat.card (sesqSpecialUnitaryGroup B) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have := (LinearGroups.unitary_full_group_order h hB hBl hd (by norm_num)).2.1
  rw [show (2 : ℕ) * (2 - 1) / 2 = 1 by rfl, pow_one,
    show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton] at this
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos f)
  have e : ((p ^ f * ((p ^ f) ^ 2 - 1) : ℕ) : ℤ) =
      (Nat.card (sesqSpecialUnitaryGroup B) : ℤ) := by
    rw [this]
    push_cast [h2]
    ring
  exact_mod_cast e.symm

theorem card_sesqSU_three (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : Module.finrank K V = 3) :
    Nat.card (sesqSpecialUnitaryGroup B) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have := (LinearGroups.unitary_full_group_order h hB hBl hd (by norm_num)).2.1
  rw [show (3 : ℕ) * (3 - 1) / 2 = 3 by rfl, show Finset.Icc 2 3 = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)] at this
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos f)
  have e : (((p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) : ℕ) : ℤ) =
      (Nat.card (sesqSpecialUnitaryGroup B) : ℤ) := by
    rw [this]
    push_cast [h2]
    ring
  exact_mod_cast e.symm

end Card

section Inner

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsL4U4
  UnitaryOut ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank StabU DiagU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem le_map_commutator_centralizer {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α)
    {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, α x = x) :
    M ≤ (⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆).map (thU p f K) := by
  set C := (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype with hC
  have hcomm_le : ⁅M, M⁆ ≤ C.map (thU p f K) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨Y₁, rfl⟩ := thU_surjective u
    obtain ⟨Y₂, rfl⟩ := thU_surjective v
    refine ⟨⁅Y₁, Y₂⁆, ?_, by rw [map_commutatorElement]⟩
    rw [hC, SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement,
      Subgroup.mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod (le_refl _) (mem_center_of_isCU_fix h hα (hfix _ hu))
      (mem_center_of_isCU_fix h hα (hfix _ hv))
  have h1 : M ≤ C.map (thU p f K) := by
    rw [← hM]
    exact hcomm_le
  rw [Subgroup.map_commutator, ← hM]
  exact Subgroup.commutator_mono h1 h1

theorem toSesq_mem_centralizer {A : GL (Fin 4) K} (hA : A ∈ uMat h 4)
    {g : unitarySU p f K 4}
    (hg : g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) :
    toSesq h 4 g ∈ Subgroup.centralizer {toSesqU h hA} := by
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) * Matrix.GeneralLinearGroup.toLin A =
    Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)
  rw [← map_mul, ← map_mul, hg]

end Inner

end CFSG.ComponentClassification.GSThmB.P211
