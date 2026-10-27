module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Eigen
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.BlockModel
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem commute_transport_iff {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}
    {h : UnitaryFieldData p f K} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) (M N : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    Commute (R * M * transportInv h R) (R * N * transportInv h R) ↔ Commute M N := by
  rw [commute_iff_eq, commute_iff_eq, transport_mul_mul hR, transport_mul_mul hR]
  constructor
  · intro hmn
    have h := congrArg (fun X => transportInv h R * X * R) hmn
    rw [transportInv_transport hR, transportInv_transport hR] at h
    exact h
  · intro hmn
    rw [hmn]

theorem commute_hypTransport_iff {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}
    {h : UnitaryFieldData p f K} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) {B : GL (Fin (2 * r + ε)) K}
    {D : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hB : (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = R * D * transportInv h R)
    (g : hypSU h r ε) :
    Commute ((hypTransport h hR g : unitarySU p f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K) B ↔
      Commute (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) D := by
  rw [← Commute.units_val_iff, coe_hypTransport, hB]
  exact commute_transport_iff hR _ _

theorem exists_centralizer_factors {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (hn : Even n) {d : ℕ} {B : GL (Fin d) K} (hB : B ∈ StatedSU d (2 ^ n) K) (hB3 : B ^ 3 = 1) :
    ∃ (k a : ℕ) (L₁ L₂ : Subgroup ↥(StatedSU d (2 ^ n) K)),
      (∀ x ∈ L₁, Commute (x : GL (Fin d) K) B) ∧
      (∀ x ∈ L₂, Commute (x : GL (Fin d) K) B) ∧
      (∀ x ∈ L₁, ∀ y ∈ L₂, Commute x y) ∧
      (∀ x y : ↥(StatedSU d (2 ^ n) K), Commute (x : GL (Fin d) K) B →
        Commute (y : GL (Fin d) K) B → ⁅x, y⁆ ∈ L₁ ⊔ L₂) ∧
      Nonempty (L₁ ≃* StatedSU k (2 ^ n) K) ∧ Nonempty (L₂ ≃* StatedSL a K) := by
  haveI : CharP K 2 := h.charP
  obtain ⟨ω, hω, hωbar⟩ := exists_cube_root h hn
  have hω1 : ω ≠ 1 := by
    intro hω1
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [hω1, one_pow, add_assoc, h2, add_zero] at hω
    exact one_ne_zero hω
  have h1ω2 : (1 : K) ≠ ω ^ 2 := by
    intro h1
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    have hω0 : ω = 0 := by
      rw [← h1, add_assoc, add_comm ω 1, ← add_assoc, h2, zero_add] at hω
      exact hω
    rw [hω0, pow_two, mul_zero] at h1
    exact one_ne_zero h1
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h'
    have h2 : ω + ω = 0 := CharTwo.add_self_eq_zero ω
    rw [← h', h2, zero_add] at hω
    exact one_ne_zero hω
  have hbarB : ((B : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (B : Matrix (Fin d) (Fin d) K) = 1 :=
    ((mem_unitarySU_iff h).mp hB).2
  have hB3mat : (B : Matrix (Fin d) (Fin d) K) ^ 3 = 1 := by
    simpa using congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hB3
  obtain ⟨a, k, R, hd, hR, hBR⟩ := exists_eigen_basis h hbarB hB3mat hω hωbar
  subst hd
  obtain ⟨M₁, M₂, hM₁D, hM₂D, hM₁M₂, hcommblocks, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    exists_hypSU_blocks h a k hω1 h1ω2 hωω2
  have hBmat_eq : (B : Matrix (Fin (2 * a + k)) (Fin (2 * a + k)) K) =
      R * hypDiag a k ω 1 (ω ^ 2) * transportInv h R := by
    rw [← hBR, Matrix.mul_assoc, mul_transportInv hR, Matrix.mul_one]
  have hcomm_hyp : ∀ g : hypSU h a k,
      Commute ((hypTransport h hR g : unitarySU 2 n K (2 * a + k)) : GL (Fin (2 * a + k)) K) B ↔
        Commute (((g : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K))
          (hypDiag a k ω 1 (ω ^ 2)) :=
    fun g => commute_hypTransport_iff hR hBmat_eq g
  refine ⟨k, a, M₁.map (hypTransport h hR).toMonoidHom,
    M₂.map (hypTransport h hR).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    exact (hcomm_hyp m).mpr (hM₁D m hm)
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    exact (hcomm_hyp m).mpr (hM₂D m hm)
  · intro x hx y hy
    obtain ⟨m₁, hm₁, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨m₂, hm₂, rfl⟩ := Subgroup.mem_map.mp hy
    have hmm := hM₁M₂ m₁ hm₁ m₂ hm₂
    rw [commute_iff_eq] at hmm ⊢
    simpa only [map_mul] using congrArg ((hypTransport h hR).toMonoidHom) hmm
  · intro x y hxB hyB
    let x' : hypSU h a k := (hypTransport h hR).symm x
    let y' : hypSU h a k := (hypTransport h hR).symm y
    have hx'T : (hypTransport h hR) x' = x := MulEquiv.apply_symm_apply _ _
    have hy'T : (hypTransport h hR) y' = y := MulEquiv.apply_symm_apply _ _
    have hx'D : Commute (((x' : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K))
        (hypDiag a k ω 1 (ω ^ 2)) := by
      apply (hcomm_hyp x').mp
      rw [hx'T]
      exact hxB
    have hy'D : Commute (((y' : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K))
        (hypDiag a k ω 1 (ω ^ 2)) := by
      apply (hcomm_hyp y').mp
      rw [hy'T]
      exact hyB
    have hmem : ⁅x', y'⁆ ∈ M₁ ⊔ M₂ := hcommblocks x' y' hx'D hy'D
    have hxy : (hypTransport h hR).toMonoidHom ⁅x', y'⁆ = ⁅x, y⁆ := by
      rw [map_commutatorElement]
      rw [show (hypTransport h hR).toMonoidHom x' = x from hx'T,
        show (hypTransport h hR).toMonoidHom y' = y from hy'T]
    rw [← hxy, ← Subgroup.map_sup M₁ M₂ (hypTransport h hR).toMonoidHom]
    exact Subgroup.mem_map_of_mem (hypTransport h hR).toMonoidHom hmem
  · exact ⟨(M₁.equivMapOfInjective (hypTransport h hR).toMonoidHom
        (hypTransport h hR).injective).symm.trans e₁⟩
  · exact ⟨(M₂.equivMapOfInjective (hypTransport h hR).toMonoidHom
        (hypTransport h hR).injective).symm.trans e₂⟩

end CFSG.LieType.SemisimpleCentralizers.OrderThree
