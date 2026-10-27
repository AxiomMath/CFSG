module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem cl_commutator_le_of_mul_self_mem {H N : Subgroup G}
    (hn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hsq : ∀ h ∈ H, h * h ∈ N) : ⁅H, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 := hsq (a * b) (H.mul_mem ha hb)
  have h2 := hn b⁻¹ (H.inv_mem hb) _ (N.inv_mem (hsq a ha))
  have h3 := N.inv_mem (hsq b hb)
  rw [commutatorElement_def]
  have heq : a * b * a⁻¹ * b⁻¹ =
      a * b * (a * b) * (b⁻¹ * (a * a)⁻¹ * b⁻¹⁻¹) * (b * b)⁻¹ := by group
  rw [heq]
  exact N.mul_mem (N.mul_mem h1 h2) h3

theorem IsComponentIn.le_commutator {K H H' : Subgroup G} (hK : IsComponentIn K H)
    (hKH' : K ≤ H') : K ≤ ⁅H', H'⁆ := by
  have hP : Group.IsPerfect K := hK.isQuasisimple.1
  calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ ⁅H', H'⁆ := Subgroup.commutator_mono hKH' hKH'

theorem IsComponentIn.eq_of_isQuasisimple {K X : Subgroup G} (hK : IsComponentIn K X)
    (hX : CFSG.IsQuasisimple X) : K = X := by
  rcases hK.2.2.lt_normal with htop | ⟨N, hNn, hKN, hNlt⟩
  · refine le_antisymm hK.1 fun a ha => ?_
    have : (⟨a, ha⟩ : ↥X) ∈ K.subgroupOf X := by rw [htop]; exact Subgroup.mem_top _
    exact this
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hNn with hNtop | hNc
    · exact absurd hNtop hNlt.ne
    · refine absurd (fun k hk => ?_) hK.not_le_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hk' : (⟨k, hK.1 hk⟩ : ↥X) ∈ center ↥X := hNc (hKN hk)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk' ⟨m, hK.1 hm⟩)

theorem IsComponentIn.not_isSolvable {K H : Subgroup G} (hK : IsComponentIn K H) :
    ¬ Group.IsSolvable H := by
  intro hH
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK.1)
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.isQuasisimple
  have : Group.IsPerfect K := hK.isQuasisimple.1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem IsComponentIn.le_or_le_of_commute [Finite G] {K A B : Subgroup G}
    (hK : IsComponentIn K (A ⊔ B)) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : K ≤ A ∨ K ≤ B := by
  have hBA : B ≤ centralizer (A : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb
  have hAB : A ≤ centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hAN : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le le_normalizer (hBA.trans (centralizer_le_normalizer _))
  have hBN : A ⊔ B ≤ normalizer (B : Set G) :=
    sup_le (hAB.trans (centralizer_le_normalizer _)) le_normalizer
  have hAn := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hAN
  have hBn := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hBN
  rcases CFSG.LocalCores.component_normal_subgroup hK.2 hAn with hA | hA
  · exact Or.inl fun k hk => hA (show (⟨k, hK.1 hk⟩ : ↥(A ⊔ B)) ∈ K.subgroupOf (A ⊔ B) from hk)
  rcases CFSG.LocalCores.component_normal_subgroup hK.2 hBn with hB | hB
  · exact Or.inr fun k hk => hB (show (⟨k, hK.1 hk⟩ : ↥(A ⊔ B)) ∈ K.subgroupOf (A ⊔ B) from hk)
  exfalso
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hA hB
  have hcen : A ⊔ B ≤ centralizer (K : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_centralizer_iff.mp (hA (show (⟨k, hK.1 hk⟩ : ↥(A ⊔ B)) ∈
        K.subgroupOf (A ⊔ B) from hk)) ⟨a, le_sup_left (b := B) ha⟩ ha
      exact (congrArg Subtype.val this).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_centralizer_iff.mp (hB (show (⟨k, hK.1 hk⟩ : ↥(A ⊔ B)) ∈
        K.subgroupOf (A ⊔ B) from hk)) ⟨b, le_sup_right (a := A) hb⟩ hb
      exact (congrArg Subtype.val this).symm
  exact hK.not_le_centralizer (hK.1.trans hcen)

theorem IsComponentIn.of_normal {K H H' : Subgroup G} (hK : IsComponentIn K H) (hHH' : H ≤ H')
    (hn : (H.subgroupOf H').Normal) : IsComponentIn K H' := by
  refine isComponentIn_of_subnormal (hK.1.trans hHH') hK.isQuasisimple ?_
  refine Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono H' hK.1) ?_ hn.isSubnormal
  have heq : (K.subgroupOf H').subgroupOf (H.subgroupOf H') =
      (K.subgroupOf H).comap (Subgroup.subgroupOfEquivOfLe hHH').toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  rw [heq]
  exact hK.2.2.comap _

end CFSG.OddStandard.SmallF3.Omega
