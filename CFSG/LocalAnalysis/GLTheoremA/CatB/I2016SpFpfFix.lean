module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpCase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpGap

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Open CFSG.RankThree.Classical CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.LocalAnalysis.GLTheoremA.I2016
open CFSG.RankThree.PartOne.KCPrimary Polynomial

open CFSG.LocalAnalysis.ComponentInitial in
theorem card_unitary_four {E : Type} [Field E] (hE : UnitaryFieldData 2 1 E) {W : Type} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hsymm : Hf.IsSymm)
    (hsep : Hf.SeparatingLeft) (hn : Module.finrank E W = 4) :
    Nat.card (sesqUnitaryGroup Hf) = 77760 := by
  have h := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hn (by norm_num)).1
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

private theorem m_eq_four_of_class {g : StatedSp 4 (ZMod 2)} {s₀ m : ℕ}
    {A₀ A₁ B : Subgroup (StatedSp 4 (ZMod 2))} (hC : Sp8Class g s₀ m A₀ A₁)
    (hB : Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) = B)
    (hcard : Nat.card ↥B = 77760) : m = 4 := by
  have hsup : A₀ ⊔ A₁ = B := hC.centralizer_eq.symm.trans hB
  have hsum := hC.sum_eq
  have hone := hC.one_le
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl
  ·
    obtain rfl : s₀ = 3 := by omega
    obtain ⟨e₀⟩ : Nonempty (↥A₀ ≃* StatedSp 3 (ZMod 2)) :=
      (hC.fixed.resolve_left (by norm_num)).2
    have hcardA₀ : Nat.card ↥A₀ = 1451520 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_three
    have hle : A₀ ≤ B := (le_sup_left : A₀ ≤ A₀ ⊔ A₁).trans hsup.le
    have := Subgroup.card_le_of_le hle
    omega
  ·
    obtain rfl : s₀ = 2 := by omega
    have h1 := card_sup_le hC.commute
    rw [hsup, hcard, card_product_two hC] at h1
    omega
  ·
    obtain rfl : s₀ = 1 := by omega
    have h1 := card_sup_le hC.commute
    rw [hsup, hcard, card_product_three hC] at h1
    omega
  · rfl

theorem fixedPointFree_of_class {g : StatedSp 4 (ZMod 2)} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hC : Sp8Class g 0 4 A₀ A₁) :
    ∀ v : V8, spEnd g v = v → v = 0 := by
  have hA0 : A₀ = ⊥ := by
    rcases hC.fixed with h | h
    · exact h.2
    · exact absurd h.1 (by norm_num)
  have hCA : Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) = A₁ := by
    rw [hC.centralizer_eq, hA0, bot_sup_eq]
  have hA₁card : Nat.card ↥A₁ = 77760 := by
    obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hC.unitary
    rw [Nat.card_congr e₁.toEquiv]
    exact card_unitary_four hE hsymm hsep hdim
  obtain ⟨s₀, hC'⟩ := exists_class_spSupported hg3 hg1
  obtain ⟨s₁, hs₁, hs4⟩ := dimension_count hg3 hg1
  rw [m_eq_four_of_class hC' hCA hA₁card] at hs4
  have hs0 : s₁ = 0 := by omega
  have hfin : Module.finrank (ZMod 2) ↥(primaryComponent (spEnd g) (X - 1 : (ZMod 2)[X])) = 0 := by
    rw [hs₁, hs0, mul_zero]
  have hzero := finrank_zero_iff_forall_zero.1 hfin
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have blocks := sp8_blocks g (orderOf_eq_prime hg3 hg1)
  intro v hv
  have hmem : v ∈ primaryComponent (spEnd g) (X - 1 : (ZMod 2)[X]) := by
    rw [blocks.fixed_eq]
    exact LinearMap.mem_ker.2 (by simp [hv])
  simpa using congrArg Subtype.val (hzero ⟨v, hmem⟩)

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
