module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreSylow
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RDiag

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem inv_comm_of_comm {v z : F} (hvz : v * z = z * v) : v⁻¹ * z = z * v⁻¹ := by
  calc v⁻¹ * z = v⁻¹ * (z * v) * v⁻¹ := by group
    _ = v⁻¹ * (v * z) * v⁻¹ := by rw [hvz]
    _ = z * v⁻¹ := by group

omit [Finite F] in
theorem conj_eq_of_comm {v z : F} (hvz : v * z = z * v) : v⁻¹ * z * v = z := by
  calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
    _ = v⁻¹ * (v * z) := by rw [hvz]
    _ = z := by group

omit [Finite F] in
theorem conjSub_inv_ne {K : Subgroup F} {v : F} (hv : v ∉ Subgroup.normalizer (K : Set F)) :
    conjSub v⁻¹ K ≠ K := fun h =>
  hv (by
    have := (Subgroup.normalizer (K : Set F)).inv_mem (AscHypOmega.mem_normalizer_of_conjSub_eq h)
    simpa using this)

theorem exists_twin_sylow {K : Subgroup F} {z v : F} (hK : IsClassical2A7 ⊤ K z)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v)
    (hvK : conjSub v⁻¹ K ≠ K) (hn : v * v ∈ Subgroup.normalizer (K : Set F)) :
    ∃ R : Subgroup F, IsPGroup 2 R ∧ v ∈ R ∧
      IsSylow2In (R ⊓ (K ⊔ conjSub v⁻¹ K)) (K ⊔ conjSub v⁻¹ K) ∧
      IsSylow2In (R ⊓ K) K ∧ IsSylow2In (R ⊓ conjSub v⁻¹ K) (conjSub v⁻¹ K) ∧
      (∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q) ∧
      ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K := by
  classical
  obtain ⟨-, hK'N, hKN', hcomm⟩ := twin_facts_a7 hK (inv_comm_of_comm hvz) hvK.symm
  set K' : Subgroup F := conjSub v⁻¹ K with hK'
  set M : Subgroup F := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (K : Set F) := sup_le Subgroup.le_normalizer hK'N
  have hMN' : M ≤ Subgroup.normalizer (K' : Set F) := sup_le hKN' Subgroup.le_normalizer
  have hvM : v ∈ Subgroup.normalizer (M : Set F) := by
    apply AscHypOmega.mem_normalizer_of_conjSub_eq (n := v)
    have h1 : conjSub v M = conjSub v K ⊔ conjSub v K' := by
      rw [hM, conjSub, Subgroup.map_sup]
      rfl
    have h2 : conjSub v K' = K := by
      rw [hK', ← conjSub_mul, mul_inv_cancel, conjSub_one]
    have h3 : conjSub v K = K' := by
      have hn' : conjSub (v * v) K = K := conjSub_eq_of_mem_normalizer hn
      calc conjSub v K = conjSub (v⁻¹ * (v * v)) K := by congr 1; group
        _ = conjSub v⁻¹ (conjSub (v * v) K) := conjSub_mul _ _ _
        _ = K' := by rw [hn']
    rw [h1, h2, h3, sup_comm]
  set X : Subgroup F := M ⊔ Subgroup.zpowers v with hX
  have hXN : X ≤ Subgroup.normalizer (M : Set F) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hvM)
  obtain ⟨R, hRX, hvR⟩ := IsSylow2In.exists_ge hv2 (le_sup_right : Subgroup.zpowers v ≤ X)
  have hR2 : IsPGroup 2 R := hRX.2.1
  have hvR' : v ∈ R := hvR (Subgroup.mem_zpowers v)
  have hRM : IsSylow2In (R ⊓ M) M := isSylow2In_inf_of_le_normalizer hRX le_sup_left hXN
  have hRK : IsSylow2In (R ⊓ K) K := by
    have := isSylow2In_inf_of_le_normalizer hRM hKM hMN
    rwa [inf_assoc, inf_eq_right.mpr hKM] at this
  have hRK' : IsSylow2In (R ⊓ K') K' := by
    have := isSylow2In_inf_of_le_normalizer hRM hK'M hMN'
    rwa [inf_assoc, inf_eq_right.mpr hK'M] at this
  refine ⟨R, hR2, hvR', hRM, hRK, hRK', ?_, ?_⟩
  · intro q hq q' hq'
    have h1 : ⁅q, q'⁆ ∈ oddCoreOf K :=
      (hcomm (Subgroup.commutator_mem_commutator hq.2 hq'.2)).1
    have h2 : ⁅q, q'⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hq.1 hq'.1) (R.inv_mem hq.1)) (R.inv_mem hq'.1)
    have h4 : ⁅q, q'⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
        (hR2.to_le (Subgroup.zpowers_le.mpr h2))
    exact commutatorElement_eq_one_iff_mul_comm.mp h4
  · intro q hq
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hvR') hq.1) hvR', ?_⟩
    have := conj_mem_conjSub (n := v⁻¹) hq.2
    rwa [inv_inv] at this

theorem exists_kappa {K : Subgroup F} {z v : F} (hK : IsClassical2A7 ⊤ K z)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v ∉ Subgroup.normalizer (K : Set F))
    (hn : v * v ∈ Subgroup.normalizer (K : Set F))
    (hnt : ¬ ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K) :
    ∃ κ ∈ K, κ * κ = z ∧ (v * v)⁻¹ * κ * (v * v) = κ⁻¹ ∧
      κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ := by
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hv4]
    norm_num
  obtain ⟨R, hR2, hvR, -, hRK, -, hcomm, hinv⟩ :=
    exists_twin_sylow hK hv2 hvz (conjSub_inv_ne hvK) hn
  have hn2 : (v * v) * (v * v) = 1 := by
    have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
    calc (v * v) * (v * v) = v ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  obtain ⟨κ, hκ, hκ2, hκn⟩ :=
    exists_inverted hK hR2 hRK (R.mul_mem hvR hvR) hn2 hn hnt
  exact ⟨κ, hκ.2, hκ2, hκn, hcomm κ hκ _ (hinv κ hκ)⟩

end CFSG.ClassicalInvolution.A7Core
