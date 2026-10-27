module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreInduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem lThreeTwoCoreOdd_of_modFix (hS : CFSG.AGLEmbedding.CatalogOuterSolvable)
    (hmod : ∀ (Y : Type) [Group Y] [Finite Y] (a : Y), IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y) →
      orderOf a = 3 → ModFix Y a) : LThreeTwoCoreOdd := by
  intro N _ _ hK I N₀ Y A hI h3 hA hAY hYN₀ hY hC
  haveI := hI
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hA] : 3 ∣ Nat.card A)
  have haY : (a : N) ∈ Y := hAY a.2
  set aY : ↥Y := ⟨a, haY⟩ with haYdef
  have haYord : orderOf aY = 3 := by
    rw [haYdef, Subgroup.orderOf_mk, Subgroup.orderOf_coe, ha]
  have hAeq : Subgroup.zpowers (a : N) = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact a.2
    · rw [hA, Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  haveI : Finite ↥Y := inferInstance
  let ρ : ↥Y →* MulAut ↥I := (MulAut.conjNormal : N →* MulAut ↥I).comp Y.subtype
  have hρ : ∀ (y : ↥Y) (x : ↥I), ((ρ y x : ↥I) : N) = (y : N) * x * (y : N)⁻¹ := fun y x => rfl
  let J : Subgroup ↥I := (I ⊓ N₀).subgroupOf I
  have hJ : ActInv ρ J := by
    intro y x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact (ρ y x).2
    · rw [hρ]
      exact N₀.mul_mem (N₀.mul_mem (hYN₀ y.2) hx.2) (N₀.inv_mem (hYN₀ y.2))
  have hfix : ∀ x : ↥I, ρ aY x = x → x ∈ J := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (a : N) * x * (a : N)⁻¹ = x := by
      have := congrArg Subtype.val hx
      rw [hρ] at this
      exact this
    have hcomm : (x : N) ∈ Subgroup.centralizer (A : Set N) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hAeq] at hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have h1 : (a : N) * x = x * a := by
        rw [mul_inv_eq_iff_eq_mul] at hx'
        exact hx'
      have : Commute (a : N) (x : N) := h1
      exact (this.zpow_left k).eq
    exact ⟨x.2, hC ⟨x.2, hcomm⟩⟩
  have := core_odd hS (Y := ↥Y) (a := aY) hY haYord (hmod ↥Y aY hY haYord) (Nat.card ↥I) ↥I rfl
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hK I) h3 ρ J hJ hfix
  exact this

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
