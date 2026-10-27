module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem M_inverted_data
    {G : Type} [Group G]
    (hE : MonsterExistenceStatement G) {s : G} (hs : orderOf s = 3) (hinv : InvertedByTwoA s) :
    ∃ (α : G) (H : Subgroup G), α * α = 1 ∧ α * s * α⁻¹ = s⁻¹ ∧ IsSimpleGroup ↥H ∧
      (∃ a b : ↥H, a * b ≠ b * a) ∧
      (Nat.card ↥H = 4089470473293004800 ∨ Nat.card ↥H = 90745943887872000) ∧
      (∀ h ∈ H, α * h = h * α) ∧ (∀ h ∈ H, s * h = h * s) ∧
      (∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H) ∧
      (∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1) := by
  obtain ⟨-, α, hαα, hαs, -, i, hi, hsh⟩ :=
    invertedByTwoA_data hE Nat.prime_three (by norm_num) hs hinv
  set H := Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)
  have hHs : IsSimpleGroup ↥H ∧
      (Nat.card ↥H = 4089470473293004800 ∨ Nat.card ↥H = 90745943887872000) := by
    fin_cases i
    · simp [suborbitClassOrder] at hi
    · simp [suborbitClassOrder] at hi
    · simp [suborbitClassOrder] at hi
    · obtain ⟨e⟩ : Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.Fi23) := hsh
      refine ⟨@MulEquiv.isSimpleGroup ↥H _ CFSG.Blueprint.NativeSporadic.Fi23 Units.instGroup
        CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e, Or.inl ?_⟩
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    · obtain ⟨e⟩ : Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.Th) := hsh
      refine ⟨@MulEquiv.isSimpleGroup ↥H _ CFSG.Blueprint.NativeSporadic.Th Units.instGroup
        CFSG.Milestones.fam_th_simplicity e, Or.inr ?_⟩
      rw [Nat.card_congr e.toEquiv, CFSG.RankThree.OddKernel.card_Th_eq]
    · simp [suborbitClassOrder] at hi
    · simp [suborbitClassOrder] at hi
    · simp [suborbitClassOrder] at hi
    · simp [suborbitClassOrder] at hi
  obtain ⟨hsimp, hcard⟩ := hHs
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hc
    let _ : CommGroup ↥H :=
      { (inferInstance : Group ↥H) with
        mul_comm := fun a b => by
          by_contra hab
          exact hc ⟨a, b, hab⟩ }
    have hp := IsSimpleGroup.prime_card (α := ↥H)
    rcases hcard with h | h <;> rw [h] at hp <;> norm_num at hp
  have hcen : Subgroup.center ↥H = ⊥ := by
    refine (hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H)).resolve_right ?_
    intro htop
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center ↥H := by
      rw [htop]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm
  have hmem : ∀ q : G, α * q = q * α → s * q = q * s → q ∈ H := fun q hαq hsq =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hαq.symm,
      Subgroup.mem_centralizer_singleton_iff.2 hsq.symm⟩
  refine ⟨α, H, hαα, hαs, hsimp, hnab, hcard, fun h hh => ?_, fun h hh => ?_,
    fun q hαq hsq h hh => ?_, fun q hαq hsq hq => ?_⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hh).1).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hh).2).symm
  · have hqH := hmem q hαq hsq
    exact H.mul_mem (H.mul_mem hqH hh) (H.inv_mem hqH)
  · have hqH := hmem q hαq hsq
    have hc : (⟨q, hqH⟩ : ↥H) ∈ Subgroup.center ↥H :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hq g.1 g.2).symm
    rw [hcen, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc

end CFSG.HardMathSupport.Dickson.Sec6.BM
