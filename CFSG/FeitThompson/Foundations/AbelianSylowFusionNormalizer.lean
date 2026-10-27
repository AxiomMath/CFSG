module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ}

private theorem conj_smul_eq_of_subgroupOf {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) {c : K}
    (h : MulAut.conj c • A.subgroupOf K = B.subgroupOf K) :
    MulAut.conj (c : G) • A = B := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
    have hzA : (c : G)⁻¹ * z * (c : G) ∈ A := by simpa [MulAut.conj, mul_assoc] using hz
    have hzK : z ∈ K := by
      have hrw : z = (c : G) * ((c : G)⁻¹ * z * (c : G)) * (c : G)⁻¹ := by group
      rw [hrw]
      exact K.mul_mem (K.mul_mem c.2 (hA hzA)) (K.inv_mem c.2)
    have hmem : (⟨z, hzK⟩ : K) ∈ MulAut.conj c • A.subgroupOf K := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf]
      simpa [MulAut.conj, mul_assoc] using hzA
    rw [h, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · intro hz
    have hmem : (⟨z, hB hz⟩ : K) ∈ MulAut.conj c • A.subgroupOf K := by
      rw [h, Subgroup.mem_subgroupOf]; exact hz
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf] at hmem
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.conj, mul_assoc] using hmem

variable [Finite G] [Fact p.Prime]

theorem exists_mem_normalizer_conj_inv_eq {P : Subgroup G} [IsMulCommutative P]
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) {x y g : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : g⁻¹ * x * g = y) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), n⁻¹ * x * n = y := by
  have hQmem : ∀ z : G, z ∈ MulAut.conj g⁻¹ • P ↔ g * z * g⁻¹ ∈ P := by
    intro z
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj, mul_assoc]
  have hcardQ :
      Nat.card (MulAut.conj g⁻¹ • P : Subgroup G) = p ^ (Nat.card G).factorization p := by
    rw [natCard_conj_smul, hP]
  have hPC : P ≤ Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro w rfl
    exact setLike_mul_comm (s := P) hy hz
  have hQC : (MulAut.conj g⁻¹ • P : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro w rfl
    have hw : g * z * g⁻¹ ∈ P := (hQmem z).mp hz
    have hcomm := setLike_mul_comm (s := P) hx hw
    have hz' : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [← hxy, hz']
    calc g⁻¹ * x * g * (g⁻¹ * (g * z * g⁻¹) * g)
        = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hcomm]
      _ = g⁻¹ * (g * z * g⁻¹) * g * (g⁻¹ * x * g) := by group
  obtain ⟨c, hc⟩ := exists_conj_smul_eq (G := Subgroup.centralizer ({y} : Set G)) (p := p)
    (natCard_subgroupOf_eq_pow_factorization hcardQ hQC)
    (natCard_subgroupOf_eq_pow_factorization hP hPC)
  have hcQP : MulAut.conj (c : G) • (MulAut.conj g⁻¹ • P : Subgroup G) = P :=
    conj_smul_eq_of_subgroupOf hQC hPC hc
  refine ⟨g * (c : G)⁻¹, mem_normalizer_iff_conj_inv_smul_eq.mpr ?_, ?_⟩
  · have hinv : (g * (c : G)⁻¹)⁻¹ = (c : G) * g⁻¹ := by group
    rw [hinv, map_mul, ← smul_smul]
    exact hcQP
  · have hcy : (c : G) * y = y * (c : G) :=
      (Subgroup.mem_centralizer_iff.mp c.2 y rfl).symm
    calc (g * (c : G)⁻¹)⁻¹ * x * (g * (c : G)⁻¹)
        = (c : G) * (g⁻¹ * x * g) * (c : G)⁻¹ := by group
      _ = (c : G) * y * (c : G)⁻¹ := by rw [hxy]
      _ = y := by rw [hcy]; group

theorem exists_conj_inv_smul_eq_and_conj_inv_eq {P : Subgroup G} [IsMulCommutative P]
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) {x y g : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : g⁻¹ * x * g = y) :
    ∃ n : G, MulAut.conj n⁻¹ • P = P ∧ n⁻¹ * x * n = y := by
  obtain ⟨n, hn, hn2⟩ := exists_mem_normalizer_conj_inv_eq hP hx hy hxy
  exact ⟨n, mem_normalizer_iff_conj_inv_smul_eq.mp hn, hn2⟩

theorem exists_mem_normalizer_conj_inv_eq_of_sylow (P : Sylow p G)
    [IsMulCommutative (P : Subgroup G)] {x y g : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : g⁻¹ * x * g = y) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n⁻¹ * x * n = y :=
  exists_mem_normalizer_conj_inv_eq (P := (P : Subgroup G)) P.card_eq_multiplicity hx hy hxy

theorem isConj_iff_exists_mem_normalizer {P : Subgroup G} [IsMulCommutative P]
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    IsConj x y ↔ ∃ n ∈ Subgroup.normalizer (P : Set G), n⁻¹ * x * n = y := by
  refine ⟨fun h => ?_, fun ⟨n, _, hn⟩ => isConj_iff.mpr ⟨n⁻¹, by simpa using hn⟩⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact exists_mem_normalizer_conj_inv_eq hP hx hy (g := c⁻¹) (by simpa using hc)

end

end CFSG.FeitThompson
