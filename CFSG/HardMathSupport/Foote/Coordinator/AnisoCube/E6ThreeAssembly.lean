module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeLines
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.LineCases
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.NegRadical
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.PlaneLines
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.PlaneRadical
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Radicals

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

section Residual

@[expose] def E6ThreeD4Lines : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K), IsSignedFrame K ψ →
    (∀ i, Function.Injective (ψ i)) → (∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) →
    ∀ (p : ℕ) (g : SL(3, K)), p.Prime → p ≠ 3 → p ≠ r →
      p ∣ Nat.card K ^ 2 + Nat.card K + 1 → orderOf g = p → ∀ s : ℕ, s < 3 →
      ∀ u : adjointGroup Tag.E6 K,
        ((u : ModGL Tag.E6 K) ∈ parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ∨
          (u : ModGL Tag.E6 K) ∈ negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) →
        Commute u (ψ 0 g * ψ 1 (g ^ (Nat.card K ^ s))) → u ∈ hyperClosure p ⊤ (cube ψ g)

end Residual

section Main

theorem e6ThreeRadicalAdj_of_d4Lines (h : E6ThreeD4Lines) (K : Type) [Field K] [Finite K]
    (r : ℕ) [Fact r.Prime] [CharP K r] (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K)
    (hψ : IsSignedFrame K ψ) (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) : E6ThreeRadicalAdj K r ψ := by
  intro p g hp hp3 hpr hord hg
  obtain ⟨hpq, -⟩ := dvd_sq_add_add_one_of_orderOf_eq_three hp hord
  obtain ⟨ψL, hLinj, hLcomm, hψL⟩ := exists_three_sl3_E6_signed (FiniteField.Extension K r 3)
  have hψ' : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (e6A2Frame i γ) (ε * c) := by
    intro i γ hγ
    refine ⟨(e6A2Sign i γ : K), ?_, hψ i γ hγ⟩
    rcases e6A2Sign_eq i γ with h1 | h1 <;> rw [h1] <;> simp
  have hZ : ∀ x : SL(3, K), x ^ p = 1 → (∀ A, Commute x A) → x = 1 :=
    fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc
  have hNQ : negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ≤ adjointGroup Tag.E6 K :=
    rootSpan_le_adjointGroup K _
  have hline : ∀ B : Subgroup (adjointGroup Tag.E6 K), B ≤ plane ψ g →
      B.relIndex (plane ψ g) = p → ∀ u : adjointGroup Tag.E6 K,
      ((u : ModGL Tag.E6 K) ∈ parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ∨
        (u : ModGL Tag.E6 K) ∈ negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) →
      u ∈ Subgroup.centralizer (B : Set (adjointGroup Tag.E6 K)) →
      u ∈ hyperClosure p ⊤ (cube ψ g) := by
    intro B hB hBi u hu huC
    obtain ⟨x, y, hx, hy, hxy, hbB⟩ :=
      exists_pow_mul_pow_mem_of_relIndex hinj hcomm hp hZ hg hB hBi
    have hub : Commute u (ψ 0 (g ^ x) * ψ 1 (g ^ y)) :=
      ((Subgroup.mem_centralizer_iff.1 huC) _ hbB).symm
    rcases line_cases hp (Nat.card K) hx hy hxy with ⟨hxn, s, hs⟩ | ⟨hxy', hD4⟩
    ·
      have hs' : (y : ZMod p) = (x : ZMod p) * ((Nat.card K ^ (s : ℕ) : ℕ) : ZMod p) := by
        rw [hs]
        push_cast
        rfl
      have hu' := centralizer_pow_mul_pow_le hcomm hp hg hxn hs'
        (Subgroup.mem_centralizer_singleton_iff.2 hub.eq)
      exact h K r ψ hψ hinj hcomm p g hp hp3 hpr hpq hg s s.isLt u hu
        (Subgroup.mem_centralizer_singleton_iff.1 hu')
    ·
      have hu2 : (u : ModGL Tag.E6 K) ∈ ((adjointGroup Tag.E6 K).subtype.comp (ψ 2)).range := by
        rcases hu with hu | hu
        · exact mem_range_two_of_mem_radical_of_commute hψ hψL hLinj hLcomm hp hp3 hpr hpq hg
            hxy' hD4 hu (hub.map (adjointGroup Tag.E6 K).subtype)
        · exact mem_range_two_of_commute
            (S := negRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
            (fun _ _ hv hva => mem_rootSpan_negRadicalRoots_inter_of_mem_centralizer hv hva)
            (fun _ hα => not_mem_block_zero_one_of_neg_mem_radical hα)
            (parabolicLevi_le_normalizer_negRadical _ _) hψ hψL hLinj hLcomm hp hp3 hpr hpq hg
            hxy' hD4 hu (hub.map (adjointGroup Tag.E6 K).subtype)
      obtain ⟨z, hz⟩ := hu2
      exact range_le_hyperClosure_cube hinj hcomm hp hp3 hg 2 ⟨z, Subtype.ext hz⟩
  refine ⟨parabolicRadicalIn Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1),
    (negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)).subgroupOf (adjointGroup Tag.E6 K),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Fintype.ofFinite K
    exact isPGroup_radicalIn_E6 K
  · exact (isPGroup_negRadical K _).of_equiv (Subgroup.subgroupOfEquivOfLe hNQ).symm
  · intro u _
    have : IsSimpleGroup (adjointGroup Tag.E6 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
    have hAB := adjointGroup_le_parabolicRadical_sup_negRadical K (r := r) e6PlaneLeviSet_ne_univ u.2
    rw [parabolicRadicalIn, ← Subgroup.subgroupOf_sup (CFSG.LieType.Chevalley.parabolicRadical_le_adjointGroup _) hNQ]
    exact Subgroup.mem_subgroupOf.2 hAB
  · exact plane_le_normalizer_radicalIn_E6 K ψ hψ' g
  · intro x hx
    have hL : ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
        parabolicLevi Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
      plane_le_parabolicLevi_E6 K ψ hψ' g ⟨x, hx, rfl⟩
    have hN := parabolicLevi_le_normalizer_negRadical K _ hL
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro y
    have hy := hN (y : ModGL Tag.E6 K)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hy
  · rintro B hB hBi u ⟨huQ, huC⟩
    exact hline B hB hBi u (Or.inl (Subgroup.mem_subgroupOf.1 huQ)) huC
  · rintro B hB hBi u ⟨huQ, huC⟩
    exact hline B hB hBi u (Or.inr (Subgroup.mem_subgroupOf.1 huQ)) huC

end Main

section Final

theorem excCubeHighAt_E6_three_of_d4Lines (h : E6ThreeD4Lines) :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.E6 3 := by
  refine excCubeHighAt_E6_three_of_radicalAdj fun K _ _ r _ _ => ?_
  obtain ⟨ψ, hinj, hcomm, hψ⟩ := exists_three_sl3_E6_signed K
  exact ⟨ψ, hinj, hcomm, e6ThreeRadicalAdj_of_d4Lines h K r ψ hψ hinj hcomm⟩

end Final

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
