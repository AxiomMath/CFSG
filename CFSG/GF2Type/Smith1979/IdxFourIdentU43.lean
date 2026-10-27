module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.LieType.Multipliers.U43 (X₀ F9)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six

theorem fixed_all_card_le :
    Fintype.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // ∀ s : F9, act s x = x} ≤ 3 := by
  decide +kernel

theorem card_le_three_of_fixed_all {B : Subgroup X₀} (hB : B ≤ thetaBar.range)
    (hfix : ∀ s : Multiplicative F9, ∀ b ∈ B, tBar s * b * (tBar s)⁻¹ = b) : Nat.card B ≤ 3 := by
  choose g hg using fun b : B => (hB b.2 : (b : X₀) ∈ thetaBar.range)
  have hfixed : ∀ b : B, ∀ s : F9, act s (g b).toAdd = (g b).toAdd := by
    intro b s
    have h1 := tBar_conj (Multiplicative.ofAdd s) (g b)
    rw [hg b, hfix _ b b.2] at h1
    have h3 := thetaBar_injective ((hg b).trans h1)
    exact (congrArg Multiplicative.toAdd h3).symm
  let f : B → {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // ∀ s : F9, act s x = x} :=
    fun b => ⟨(g b).toAdd, hfixed b⟩
  have hf : Function.Injective f := by
    intro b b' hbb'
    have h1 : (g b).toAdd = (g b').toAdd := congrArg Subtype.val hbb'
    apply Subtype.ext
    rw [← hg b, ← hg b', Multiplicative.toAdd.injective h1]
  calc Nat.card B ≤ Nat.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // ∀ s : F9, act s x = x} :=
        Nat.card_le_card_of_injective f hf
    _ = Fintype.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // ∀ s : F9, act s x = x} :=
        Nat.card_eq_fintype_card
    _ ≤ 3 := fixed_all_card_le

theorem exists_tBar_mul_of_mem_Psub {x : X₀} (hx : x ∈ Psub) :
    ∃ s : Multiplicative F9, ∃ a ∈ thetaBar.range, x = tBar s * a := by
  obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
  exact ⟨s, (tBar s)⁻¹ * a * ((tBar s)⁻¹)⁻¹,
    tBar_mem_normalizer (tBar.range.inv_mem ⟨s, rfl⟩) ha, by group⟩

theorem normal_range_thetaBar_subgroupOf : (thetaBar.range.subgroupOf Psub).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨s, a, ha, hg⟩ := exists_tBar_mul_of_mem_Psub g.2
  have h1 : a * (n : X₀) * a⁻¹ ∈ thetaBar.range := mul_mem (mul_mem ha hn) (inv_mem ha)
  have h2 := tBar_mem_normalizer (t := tBar s) ⟨s, rfl⟩ h1
  have h3 : ((g * n * g⁻¹ : Psub) : X₀) = tBar s * (a * (n : X₀) * a⁻¹) * (tBar s)⁻¹ := by
    show (g : X₀) * n * (g : X₀)⁻¹ = _
    rw [hg]
    group
  rw [h3]
  exact h2

theorem relIndex_range_thetaBar_Psub : thetaBar.range.relIndex Psub = 9 := by
  have h2 := Subgroup.relIndex_mul_card thetaBar.range Psub
  have hAP : thetaBar.range ⊓ Psub = thetaBar.range := inf_eq_left.2 A_le_Psub
  rw [hAP, card_range_thetaBar, card_Psub] at h2
  have : thetaBar.range.relIndex Psub * 3 ^ 4 = 9 * 3 ^ 4 := by rw [h2]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

theorem elemAbelian_eq_range_thetaBar {B : Subgroup X₀} (hB : B ≤ Psub)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hpow : ∀ x ∈ B, x ^ 3 = 1)
    (hcard : Nat.card B = 3 ^ 4) : B = thetaBar.range := by
  clear hpow
  by_cases hBA : B ≤ thetaBar.range
  · exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hcard, card_range_thetaBar])
  exfalso
  have hcent : ∀ (s : Multiplicative F9) (a : X₀), a ∈ thetaBar.range → tBar s * a ∈ B →
      ∀ f ∈ (thetaBar.range ⊓ B : Subgroup X₀), tBar s * f * (tBar s)⁻¹ = f := by
    rintro s a ha hsa f ⟨hfA, hfB⟩
    have h1 : tBar s * a * f = f * (tBar s * a) := hcomm _ hsa f hfB
    have h2 : a * f = f * a := thetaBar_comm a f ha hfA
    have h3 : tBar s * f * a = f * tBar s * a := by
      calc tBar s * f * a = tBar s * (f * a) := mul_assoc _ _ _
        _ = tBar s * (a * f) := by rw [h2]
        _ = tBar s * a * f := (mul_assoc _ _ _).symm
        _ = f * (tBar s * a) := h1
        _ = f * tBar s * a := (mul_assoc _ _ _).symm
    exact mul_inv_eq_iff_eq_mul.mpr (mul_right_cancel h3)
  have hF9 : Nat.card (thetaBar.range ⊓ B : Subgroup X₀) ≤ 9 := by
    obtain ⟨e, heB, heA⟩ := SetLike.not_le_iff_exists.mp hBA
    obtain ⟨s, a, ha, rfl⟩ := exists_tBar_mul_of_mem_Psub (hB heB)
    have hs : s ≠ 1 := by
      rintro rfl
      exact heA (by simpa using ha)
    exact card_le_nine_of_fixed hs inf_le_left (hcent s a ha heB)
  have : Finite Psub := Nat.finite_of_card_ne_zero (by rw [card_Psub]; norm_num)
  have hN := normal_range_thetaBar_subgroupOf
  let ψ : B →* Psub ⧸ thetaBar.range.subgroupOf Psub :=
    (QuotientGroup.mk' (thetaBar.range.subgroupOf Psub)).comp (Subgroup.inclusion hB)
  have hker : ψ.ker = thetaBar.range.subgroupOf B := by
    ext b
    simp [ψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hr : thetaBar.range.relIndex B = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hQ : Nat.card (Psub ⧸ thetaBar.range.subgroupOf Psub) = 9 := by
    rw [← relIndex_range_thetaBar_Psub]
    rfl
  have hr9 : Nat.card ψ.range ≤ 9 := by
    rw [← hQ]
    exact Subgroup.card_le_card_group _
  have h1 := Subgroup.relIndex_mul_card thetaBar.range B
  rw [hcard, hr] at h1
  have hr_ge : 9 ≤ Nat.card ψ.range := by
    by_contra hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ (not_le.mp hlt)) hF9
    omega
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hQ]
    omega
  have hcent_all : ∀ s : Multiplicative F9, ∀ f ∈ (thetaBar.range ⊓ B : Subgroup X₀),
      tBar s * f * (tBar s)⁻¹ = f := by
    intro s
    have hs : tBar s ∈ Psub := ⟨1, one_mem _, tBar s, ⟨s, rfl⟩, (one_mul _).symm⟩
    have hmem : (QuotientGroup.mk ⟨tBar s, hs⟩ :
        Psub ⧸ thetaBar.range.subgroupOf Psub) ∈ ψ.range := by
      rw [hrange]
      exact Subgroup.mem_top _
    obtain ⟨b, hb⟩ := hmem
    have hb' : QuotientGroup.mk (Subgroup.inclusion hB b) =
        (QuotientGroup.mk ⟨tBar s, hs⟩ : Psub ⧸ thetaBar.range.subgroupOf Psub) := hb
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hb'
    have hb'' : (b : X₀)⁻¹ * tBar s ∈ thetaBar.range := hb'
    refine hcent s ((b : X₀)⁻¹ * tBar s)⁻¹ (inv_mem hb'') ?_
    have : tBar s * ((b : X₀)⁻¹ * tBar s)⁻¹ = b := by group
    rw [this]
    exact b.2
  have h3 := card_le_three_of_fixed_all (inf_le_left : thetaBar.range ⊓ B ≤ thetaBar.range)
    hcent_all
  have h4 := Nat.mul_le_mul hr9 h3
  omega

end CFSG.GF2Type.Smith1979.IdxFour
