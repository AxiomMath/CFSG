module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {C : Type} [Group C]

theorem component_conj (ψ β : MulAut C) {K : Subgroup C}
    (hK : Assembly.IsComponentOf K (fixedSubgroup β))
    (hKn : (K.subgroupOf (fixedSubgroup β)).Normal) :
    Assembly.IsComponentOf (K.map ψ.toMonoidHom) (fixedSubgroup (ψ * β * ψ⁻¹)) ∧
      ((K.map ψ.toMonoidHom).subgroupOf (fixedSubgroup (ψ * β * ψ⁻¹))).Normal := by
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := fixedSubgroup_congr ψ β
  rw [hc] at hfix
  refine ⟨hfix ▸ isComponentOf_map_of_equiv ψ hK, ?_⟩
  rw [hfix]
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 g.2
  have hkF : k ∈ fixedSubgroup β := hK.1 hk
  have h1 := hKn.conj_mem ⟨k, hkF⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf] at h1 ⊢
  refine ⟨y * k * y⁻¹, h1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hkn hyg ⊢
  rw [hkn, hyg]
  rfl

theorem not_smallType_of_conj {ψ β γ : MulAut C} (hψ : ψ * β * ψ⁻¹ = γ)
    (h : ∀ K : Subgroup C, Assembly.IsComponentOf K (fixedSubgroup γ) →
      (K.subgroupOf (fixedSubgroup γ)).Normal → ¬ SmallType K)
    {K : Subgroup C} (hK : Assembly.IsComponentOf K (fixedSubgroup β))
    (hKn : (K.subgroupOf (fixedSubgroup β)).Normal) : ¬ SmallType K := by
  obtain ⟨h1, h2⟩ := component_conj ψ β hK hKn
  rw [hψ] at h1 h2
  intro hs
  exact h _ h1 h2 ((smallType_congr (ψ.subgroupMap K)).1 hs)

theorem center_eq_bot_of_isSimpleGroup' {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

theorem ne_bot_of_assembly_isQuasisimple {K : Subgroup C} (hK : Assembly.IsQuasisimple K) :
    K ≠ ⊥ := by
  intro h
  subst h
  have hs := hK.2
  have : Subsingleton (↥(⊥ : Subgroup C) ⧸ center ↥(⊥ : Subgroup C)) := by
    have : Subsingleton ↥(⊥ : Subgroup C) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      rw [(Subgroup.mem_bot.1 x.2), (Subgroup.mem_bot.1 y.2)]
    infer_instance
  exact not_nontrivial _ (IsSimpleGroup.toNontrivial (G := ↥(⊥ : Subgroup C) ⧸
    center ↥(⊥ : Subgroup C)))

theorem eq_of_isSubnormal_of_isSimpleGroup {J : Subgroup C} [IsSimpleGroup J] :
    ∀ {H M : Subgroup C}, Assembly.IsSubnormal H M → M = J → H ≠ ⊥ → H = J := by
  intro H M h
  induction h with
  | refl => exact fun h _ => h
  | @step H M' M hle hnormal _ ih =>
    intro hMJ hH
    have hM' : M' = J := ih hMJ (fun h => hH (le_bot_iff.1 (h ▸ hle)))
    subst hM'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf M') with h | h
    · exfalso
      apply hH
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hle hx⟩ : M') ∈ H.subgroupOf M' := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · exact le_antisymm hle fun x hx => by
        have : (⟨x, hx⟩ : M') ∈ H.subgroupOf M' := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 this

theorem eq_of_isComponentOf_of_isSimpleGroup {K J : Subgroup C} [IsSimpleGroup J]
    (hK : Assembly.IsComponentOf K J) : K = J :=
  eq_of_isSubnormal_of_isSimpleGroup hK.2.1 rfl (ne_bot_of_assembly_isQuasisimple hK.2.2)

theorem eq_of_isComponentOf_of_normal_simple {K J F : Subgroup C} [IsSimpleGroup J]
    (hJF : J ≤ F) (hJn : (J.subgroupOf F).Normal)
    (hsolv : Group.IsSolvable (F ⧸ J.subgroupOf F)) (hK : Assembly.IsComponentOf K F) :
    K = J := by
  have hKJ : K ≤ J := by
    intro y hy
    have hf := MonoidHom.range_eq_bot_iff.1
      (LieType.Chevalley.OddToralOrdinary.range_eq_bot_of_commutator_eq_top hK.2.2.1
        ((QuotientGroup.mk' (J.subgroupOf F)).comp (Subgroup.inclusion hK.1)))
    have hy' : (QuotientGroup.mk (Subgroup.inclusion hK.1 ⟨y, hy⟩) : F ⧸ J.subgroupOf F) = 1 :=
      DFunLike.congr_fun hf ⟨y, hy⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hK.1 ⟨y, hy⟩)).1 hy'
  have hKc : Assembly.IsComponentOf K J :=
    LieType.Chevalley.OddToralOrdinary.isComponentOf_of_le_of_le hK hKJ hJF
  exact eq_of_isComponentOf_of_isSimpleGroup hKc

theorem eq_of_isComponentOf_of_commutator_eq {K J F : Subgroup C} [IsSimpleGroup J]
    (hJ : ⁅F, F⁆ = J) (hK : Assembly.IsComponentOf K F) : K = J := by
  have hKJ : K ≤ J := by
    have h1 : ⁅K, K⁆ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hK.1 hK.1
    have h2 : ⁅K, K⁆ = K := by
      rw [← Subgroup.map_subtype_commutator, hK.2.2.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h2, ← hJ]
    exact h1
  have hJF : J ≤ F := hJ ▸ Subgroup.commutator_le_self F
  exact eq_of_isComponentOf_of_isSimpleGroup
    (LieType.Chevalley.OddToralOrdinary.isComponentOf_of_le_of_le hK hKJ hJF)

theorem isComponentOf_comap_of_injective {H : Type} [Group H] (ι : H →* C)
    (hι : Function.Injective ι) {L : Subgroup C} {F : Subgroup H}
    (hL : Assembly.IsComponentOf L (F.map ι)) : Assembly.IsComponentOf (L.comap ι) F := by
  have hLr : L ≤ ι.range := hL.1.trans (Subgroup.map_le_range ι F)
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hL.1 hx
    rw [← hι hyx]
    exact hy
  · have h := LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap ι hL.2.1
    rwa [Subgroup.comap_map_eq_self_of_injective hι] at h
  · have e : L.comap ι ≃* L :=
      ((L.comap ι).equivMapOfInjective ι hι).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr))
    exact assembly_isQuasisimple_of_equiv e.symm hL.2.2

end CFSG.ComponentClassification.ExcSelector
