module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP21b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP21b2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped IsMulCommutative


lemma fzl21b_stage1_strong (N : Type) [Group N] (φ : N →* MulAut fz21b_X)
    (N₀ : Subgroup N) [N₀.Normal] (e : N ⧸ N₀ ≃* FzSigma4) (hφ : Function.Injective φ)
    (hInv : ∀ n ∈ N₀, n ≠ 1 → ∀ x : fz21b_X, φ n x = x⁻¹) :
    ∃ N₁ : Subgroup N, N₁.Normal ∧ (∀ n ∈ N₁, n ^ 2 = 1) ∧ N₀ ≤ N₁ ∧
      N₁ = fz21b_V.comap (e.toMonoidHom.comp (QuotientGroup.mk' N₀)) ∧
      ∃ K : Subgroup N, K.Normal ∧ N₀ ≤ K ∧ N₁ ≤ K ∧
        (∀ n ∈ K, ∀ z ∈ fz21b_Z, φ n z = z) := by
  classical
  let π : N →* FzSigma4 := e.toMonoidHom.comp (QuotientGroup.mk' N₀)
  have hπker : π.ker = N₀ := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' N₀)).ker = N₀
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N₀) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hπsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective N₀)
  let χ : N →* MulAut fz21b_Z := (MulAut.characteristic fz21b_Z).comp φ
  let K : Subgroup N := χ.ker
  have hKfix : ∀ n ∈ K, ∀ z ∈ fz21b_Z, φ n z = z := by
    intro n hn z hz
    have h1 : χ n = 1 := MonoidHom.mem_ker.mp hn
    have h2 : (MulAut.characteristic fz21b_Z (φ n)) ⟨z, hz⟩ = ⟨z, hz⟩ := by
      have hχ : χ n = (MulAut.characteristic fz21b_Z) (φ n) := rfl
      rw [← hχ, h1]
      rfl
    exact congrArg Subtype.val h2
  have hN₀K : N₀ ≤ K := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hχ : χ n = (MulAut.characteristic fz21b_Z) (φ n) := rfl
    rw [hχ]
    refine MulEquiv.ext (fun z => ?_)
    apply Subtype.ext
    change φ n (z : fz21b_X) = (z : fz21b_X)
    by_cases hn1 : n = 1
    · simp [hn1]
    rw [hInv n hn hn1 z]
    exact inv_eq_of_mul_eq_one_right (by
      have hz2 : (z : fz21b_X) ^ 2 = 1 := MonoidHom.mem_ker.mp (fz21b_Z_le_X0 z.2)
      rw [← pow_two]; exact hz2)
  have hKnormal : K.Normal := MonoidHom.normal_ker χ
  have hKne : K ≠ N₀ := by
    intro hKN
    have hinj : Function.Injective (QuotientGroup.lift N₀ χ hN₀K) := by
      rw [QuotientGroup.injective_lift_iff]
      exact hKN.symm
    have hle : Nat.card (N ⧸ N₀) ≤ Nat.card (MulAut fz21b_Z) :=
      Nat.card_le_card_of_injective _ hinj
    have hq : Nat.card (N ⧸ N₀) = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; decide
    rw [hq, fz21b_Z_aut_card] at hle
    omega
  let N₁ : Subgroup N := fz21b_V.comap π
  have hN₁normal : N₁.Normal := fz21b_V_normal.comap π
  have hVle : fz21b_V ≤ K.map π := by
    refine fz21b_V_le_of_normal (M := K.map π) (hKnormal.map π hπsurj) ?_
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hle : K ≤ π.ker := (Subgroup.map_eq_bot_iff (f := π) K).mp hbot
    rw [hπker] at hle
    exact hKne (le_antisymm hle hN₀K)
  have hN₁K : N₁ ≤ K := by
    intro n hn
    have hπn : π n ∈ fz21b_V := Subgroup.mem_comap.mp hn
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (hVle hπn)
    have hnk : n * k⁻¹ ∈ N₀ := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hkπ, mul_inv_cancel]
    have hmem : n * k⁻¹ ∈ K := hN₀K hnk
    have : n = (n * k⁻¹) * k := by group
    rw [this]
    exact K.mul_mem hmem hk
  have hN₁sq : ∀ n ∈ N₁, n ^ 2 = 1 := by
    intro n hn
    by_contra hne
    have hn2N₀ : n ^ 2 ∈ N₀ := by
      rw [← hπker, MonoidHom.mem_ker, map_pow]
      exact fz21b_V_sq_one (π n) (Subgroup.mem_comap.mp hn)
    have hg2 : ∀ x : fz21b_X, φ n (φ n x) = x⁻¹ := by
      intro x
      have h1 : φ n (φ n x) = (φ (n ^ 2)) x := by
        rw [pow_two, map_mul, MulAut.mul_apply]
      rw [h1]
      exact hInv (n ^ 2) hn2N₀ hne x
    let g : MulAut fz21b_X := φ n
    have hg : ∀ x, g (g x) = x⁻¹ := hg2
    let ψ : fz21b_X0 →* fz21b_X :=
      { toFun := fun y => (y : fz21b_X) * g (y : fz21b_X)
        map_one' := by simp
        map_mul' := by
          intro a b
          simp only [Subgroup.coe_mul, map_mul]
          ac_rfl }
    have hy_mem : ∀ c : fz21b_X, c * g c ∈ fz21b_X0 := by
      intro c
      rw [fz21b_X0, MonoidHom.mem_ker]
      show (c * g c) ^ 2 = 1
      have hfix : g (c ^ 2) = c ^ 2 :=
        hKfix n (hN₁K hn) (c ^ 2) ⟨c, by rw [powMonoidHom_apply]⟩
      calc (c * g c) ^ 2 = c ^ 2 * (g c) ^ 2 := by rw [mul_pow]
        _ = c ^ 2 * g (c ^ 2) := by rw [← map_pow]
        _ = c ^ 2 * c ^ 2 := by rw [hfix]
        _ = 1 := by rw [← pow_add]; exact fz21b_X_pow_four c
    have hψy : ∀ c : fz21b_X, ψ ⟨c * g c, hy_mem c⟩ = c ^ 2 := by
      intro c
      show (c * g c) * g (c * g c) = c ^ 2
      rw [map_mul, hg c]
      have hfix : g (c ^ 2) = c ^ 2 :=
        hKfix n (hN₁K hn) (c ^ 2) ⟨c, by rw [powMonoidHom_apply]⟩
      calc (c * g c) * (g c * c⁻¹) = c * (g c * g c) * c⁻¹ := by ac_rfl
        _ = c * g (c ^ 2) * c⁻¹ := by rw [← map_mul, ← pow_two]
        _ = c * c ^ 2 * c⁻¹ := by rw [hfix]
        _ = c ^ 2 := by
          rw [mul_comm c (c ^ 2), mul_assoc]
          exact (congrArg (fun x => c ^ 2 * x) (mul_inv_cancel c)).trans (mul_one _)
    have hZle : fz21b_Z ≤ ψ.range := by
      intro z hz
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz
      exact MonoidHom.mem_range.mpr ⟨⟨c * g c, hy_mem c⟩, by rw [hψy c]; exact hc⟩
    have hZker : fz21b_Z.subgroupOf fz21b_X0 ≤ ψ.ker := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [MonoidHom.mem_ker]
      show (z : fz21b_X) * g (z : fz21b_X) = 1
      have hfix : g (z : fz21b_X) = (z : fz21b_X) := hKfix n (hN₁K hn) (z : fz21b_X) hz
      rw [hfix, ← pow_two]
      exact MonoidHom.mem_ker.mp z.2
    have hle2 : Nat.card ψ.range ≤ 2 :=
      fz21b_range_card_le_two fz21b_X0 (fz21b_Z.subgroupOf fz21b_X0) fz21b_X0_index ψ hZker
    have hle4 : Nat.card fz21b_Z ≤ Nat.card ψ.range := Subgroup.card_le_of_le hZle
    rw [fz21b_Z_card] at hle4
    omega
  have hN₀N₁ : N₀ ≤ N₁ := by
    intro n hn
    rw [Subgroup.mem_comap]
    have h1 : π n = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact hn
    rw [h1]
    exact fz21b_V.one_mem
  exact ⟨N₁, hN₁normal, hN₁sq, hN₀N₁, rfl, K, hKnormal, hN₀K, hN₁K, hKfix⟩

end CFSG.OddStandard.SmallF3.FritzII
