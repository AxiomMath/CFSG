module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


theorem normal_commutator_subgroupOf {G : Type*} [Group G] (D : Subgroup G) :
    (⁅D, D⁆.subgroupOf D).Normal := by
  have h : (⁅D, D⁆.subgroupOf D) = commutator D := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  rw [h]
  infer_instance

theorem isSubnormal_commutator_subgroupOf {G : Type*} [Group G] (D : Subgroup G) :
    (⁅D, D⁆.subgroupOf D).IsSubnormal :=
  Subgroup.Normal.isSubnormal (normal_commutator_subgroupOf D)

structure IsLangFrame (τ : Tag) (K₂ : Type) [Field K₂] (p : ℕ) (Γ E : Subgroup (ModGL τ K₂)) :
    Prop where
  E_le_torus : E ≤ torusGroup τ K₂
  E_le_Γ : E ≤ Γ
  sylow : ∀ F : Subgroup (ModGL τ K₂), F ≤ Γ → (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
    ∃ h ∈ Γ, F.map (MulAut.conj h).toMonoidHom ≤ E
  generation : ⨆ β : {β : Fin τ.rank → ℤ // IsRoot τ β}, rootRankOneGroup τ K₂ β.1 ⊓ Γ = Γ
  component : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → ∀ a : Fin τ.rank → K₂ˣ,
    rootDiagUnit τ a ∈ E → rootDiagUnit τ a ≠ 1 → rootChar a β = 1 →
    ∃ L : Subgroup (ModGL τ K₂), rootRankOneGroup τ K₂ β ⊓ Γ ≤ L ∧
      L ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧ CFSG.IsQuasisimple L ∧
      (L.subgroupOf (Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)

theorem closure_rootRankOne_eq_top {τ : Tag} {K₂ : Type} [Field K₂] {Γ : Subgroup (ModGL τ K₂)}
    (hgen : ⨆ β : {β : Fin τ.rank → ℤ // IsRoot τ β}, rootRankOneGroup τ K₂ β.1 ⊓ Γ = Γ) :
    Subgroup.closure {s : ↥Γ | ∃ β, IsRoot τ β ∧ (s : ModGL τ K₂) ∈ rootRankOneGroup τ K₂ β} =
      ⊤ := by
  set S : Set ↥Γ := {s : ↥Γ | ∃ β, IsRoot τ β ∧ (s : ModGL τ K₂) ∈ rootRankOneGroup τ K₂ β}
  have hle : (⨆ β : {β : Fin τ.rank → ℤ // IsRoot τ β}, rootRankOneGroup τ K₂ β.1 ⊓ Γ) ≤
      (Subgroup.closure S).map Γ.subtype := by
    refine iSup_le fun β r hr => ?_
    exact ⟨⟨r, hr.2⟩, Subgroup.subset_closure ⟨β.1, β.2, hr.1⟩, rfl⟩
  rw [eq_top_iff]
  rintro γ -
  have h1 : (γ : ModGL τ K₂) ∈
      ⨆ β : {β : Fin τ.rank → ℤ // IsRoot τ β}, rootRankOneGroup τ K₂ β.1 ⊓ Γ := by
    rw [hgen]
    exact γ.2
  obtain ⟨c, hc, hcγ⟩ := hle h1
  have : c = γ := Subtype.ext hcγ
  exact this ▸ hc

theorem innerPlaneBalance_of_langFrame {τ : Tag} {K₂ : Type} [Field K₂] [Finite K₂] {p : ℕ}
    (hp : p.Prime) {Γ E : Subgroup (ModGL τ K₂)} (hF : IsLangFrame τ K₂ p Γ E)
    (hinj : Function.Injective (MulAut.conj : ↥Γ →* MulAut ↥Γ)) : InnerPlaneBalance p ↥Γ := by
  classical
  have : Finite (ModGL τ K₂) := finite_modGL
  intro D hDin hDe hDc H hH
  set D₀ : Subgroup ↥Γ := D.comap (MulAut.conj : ↥Γ →* MulAut ↥Γ) with hD₀
  have hDD : D₀.map (MulAut.conj : ↥Γ →* MulAut ↥Γ) = D := Subgroup.map_comap_eq_self hDin
  have hD₀c : Nat.card D₀ = p ^ 2 := by
    rw [← hDc, ← hDD, Subgroup.card_map_of_injective hinj]
  have hD₀p : ∀ x ∈ D₀, x ^ p = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hDe.2 _ hx
  obtain ⟨h, hhΓ, hhE⟩ := hF.sylow (D₀.map Γ.subtype) (Subgroup.map_subtype_le _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD₀p x hx, map_one])
    (by rw [Subgroup.card_map_of_injective Γ.subtype_injective, hD₀c])
  set k : ↥Γ := ⟨h, hhΓ⟩ with hk
  set D₁ : Subgroup ↥Γ := D₀.map (MulAut.conj k).toMonoidHom with hD₁
  have hD₁E : ∀ x ∈ D₁, (x : ModGL τ K₂) ∈ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hhE ⟨(x : ModGL τ K₂), ⟨x, hx, rfl⟩, rfl⟩
  have hD₁c : p < Nat.card (D₁.map Γ.subtype) := by
    rw [Subgroup.card_map_of_injective Γ.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, hD₀c]
    nlinarith [hp.two_le]
  have hD₁p : ∀ x ∈ D₁.map Γ.subtype, x ^ p = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have : (MulAut.conj k x) ^ p = 1 := by
      rw [← map_pow, hD₀p x hx, map_one]
    simpa using congrArg Subtype.val this
  have hD₁T : D₁.map Γ.subtype ≤ torusGroup τ K₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hF.E_le_torus (hD₁E x hx)
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj k) (hH ⟨k, rfl⟩) ?_
  have hmap : D.map (MulAut.conj (MulAut.conj k)).toMonoidHom =
      D₁.map (MulAut.conj : ↥Γ →* MulAut ↥Γ) := by
    conv_lhs => rw [← hDD]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  refine localDeltaIn_eq_bot_of_inner_components_ambient (A := Γ) hp hinj hH D₁
    (closure_rootRankOne_eq_top hF.generation) ?_
  rintro s ⟨β, hβ, hsβ⟩
  obtain ⟨a, ⟨d', hd', hda⟩, ha1, hχ⟩ := exists_rootChar_eq_one hp hD₁T hD₁p hD₁c β
  have hda' : (d' : ModGL τ K₂) = rootDiagUnit τ a := hda
  have hdE : rootDiagUnit τ a ∈ E := hda' ▸ hD₁E d' hd'
  have ha1' : rootDiagUnit τ a ≠ 1 := ha1
  obtain ⟨L, hsL, hLC, hLq, hLsn, hLp⟩ := hF.component β hβ a hdE ha1' hχ
  refine ⟨d', hd', fun h1 => ha1' (by rw [← hda', h1]; rfl), L, hsL ⟨hsβ, s.2⟩, ?_, hLq, ?_, hLp⟩
  · rw [hda']
    exact hLC
  · rw [hda']
    exact hLsn

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
