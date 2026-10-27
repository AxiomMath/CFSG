module

public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

variable {k : Type} [Field k] [Finite k]

theorem ker_comp_mk'_center {X Y : Type*} [Group X] [Group Y] (ψ : X ⧸ center X ≃* Y) :
    (ψ.toMonoidHom.comp (QuotientGroup.mk' (center X))).ker = center X := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, EmbeddingLike.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem map_commutator_eq_top_of_sl2 (hk : 5 ≤ Nat.card k) {X : Type*} [Group X]
    (π : X →* SpecialLinearGroup (Fin 2) k) {Y : Subgroup X} (hY : Y.map π = ⊤) :
    (⁅Y, Y⁆ : Subgroup X).map π = ⊤ := by
  have := LinearGroups.special_linear_dimension_two_perfect (SL2Closed.exists_four_of_five_le hk)
  rw [map_commutator, hY]
  exact Group.IsPerfect.commutator_eq_top

theorem commutator_inf_ker_eq_bot
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {X : Type*}
    [Group X] (π : X →* SpecialLinearGroup (Fin 2) k) {Y : Subgroup X} (hY : Y.map π = ⊤)
    (hYk : Y ⊓ π.ker ≤ center X) : ⁅Y, Y⁆ ⊓ π.ker = ⊥ := by
  set C : Subgroup X := ⁅Y, Y⁆ with hCdef
  have hCY : C ≤ Y := commutator_le_self Y
  have hC : C.map π = ⊤ := map_commutator_eq_top_of_sl2 hk π hY
  have hdec : ∀ y ∈ Y, ∃ c ∈ C, c⁻¹ * y ∈ Y ⊓ π.ker := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ : π y ∈ C.map π := hC ▸ mem_top _
    refine ⟨c, hc, mem_inf.2 ⟨mul_mem (inv_mem (hCY hc)) hy, ?_⟩⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
  have hperf : ⁅C, C⁆ = C := by
    refine le_antisymm (commutator_le_self C) (commutator_le.2 fun a ha b hb => ?_)
    obtain ⟨c, hc, hz⟩ := hdec a ha
    obtain ⟨d, hd, hw⟩ := hdec b hb
    have e : ⁅a, b⁆ = ⁅c, d⁆ := by
      have ha' : a = c * (c⁻¹ * a) := by group
      have hb' : b = d * (d⁻¹ * b) := by group
      rw [ha', hb', TorusLift.commutatorElement_mul_central_left (hYk hz),
        TorusLift.commutatorElement_mul_central_right (hYk hw)]
    rw [e]
    exact commutator_mem_commutator hc hd
  have : Group.IsPerfect C := Subgroup.isPerfect_iff.2 hperf
  let ρ : C →* SpecialLinearGroup (Fin 2) k := π.comp C.subtype
  have hρ : Function.Surjective ρ := by
    intro g
    obtain ⟨c, hc, rfl⟩ : g ∈ C.map π := hC ▸ mem_top _
    exact ⟨⟨c, hc⟩, rfl⟩
  have hρker : ρ.ker ≤ Subgroup.center C := by
    intro c hc
    rw [mem_center_iff]
    intro d
    exact Subtype.ext (mem_center_iff.1 (hYk (mem_inf.2 ⟨hCY c.2, hc⟩)) d)
  obtain ⟨σ, hσ⟩ := SL2Closed.sl2_exists_section_of_central hk hk9 hρ hρker
  have hbot := SL2Closed.ker_eq_bot_of_section ρ hρker σ hσ
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxC, hxk⟩ := mem_inf.1 hx
  have : (⟨x, hxC⟩ : C) ∈ ρ.ker := hxk
  rw [hbot, mem_bot] at this
  exact mem_bot.2 (congrArg Subtype.val this)

theorem center_eq_bot_of_sl2
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {X : Type*}
    [Group X] [Group.IsPerfect X] (ψ : X ⧸ center X ≃* SpecialLinearGroup (Fin 2) k) :
    center X = ⊥ := by
  set π := ψ.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hπ : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker := ker_comp_mk'_center ψ
  obtain ⟨σ, hσ⟩ := SL2Closed.sl2_exists_section_of_central hk hk9 hπ hker.le
  rw [← hker]
  exact SL2Closed.ker_eq_bot_of_section π hker.le σ hσ

theorem center_eq_bot_of_sl2_prod
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {X : Type*}
    [Group X] [Group.IsPerfect X]
    (ψ : X ⧸ center X ≃* SpecialLinearGroup (Fin 2) k × SpecialLinearGroup (Fin 2) k) :
    center X = ⊥ := by
  set π := ψ.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hπ : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker := ker_comp_mk'_center ψ
  set π₁ := (MonoidHom.fst _ _).comp π
  set π₂ := (MonoidHom.snd _ _).comp π
  have hπ12 : ∀ x : X, π x = (π₁ x, π₂ x) := fun x => rfl
  have hk1 : ∀ x : X, π₁ x = 1 → π₂ x = 1 → x ∈ center X := fun x h1 h2 => by
    rw [← hker, MonoidHom.mem_ker, hπ12, h1, h2, Prod.mk_one_one]
  have hX1 : π₂.ker.map π₁ = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨x, hx⟩ := hπ (a, 1)
    refine ⟨x, ?_, ?_⟩
    · exact MonoidHom.mem_ker.2 (congrArg Prod.snd hx)
    · exact congrArg Prod.fst hx
  have hX2 : π₁.ker.map π₂ = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨x, hx⟩ := hπ (1, b)
    refine ⟨x, ?_, ?_⟩
    · exact MonoidHom.mem_ker.2 (congrArg Prod.fst hx)
    · exact congrArg Prod.snd hx
  have hY1 := commutator_inf_ker_eq_bot hk hk9 π₁ hX1 fun x hx => hk1 x hx.2 hx.1
  have hY2 := commutator_inf_ker_eq_bot hk hk9 π₂ hX2 fun x hx => hk1 x hx.1 hx.2
  have hY2n : (⁅π₁.ker, π₁.ker⁆ : Subgroup X).Normal := inferInstance
  set Y₁ : Subgroup X := ⁅π₂.ker, π₂.ker⁆
  set Y₂ : Subgroup X := ⁅π₁.ker, π₁.ker⁆
  have hY1m : Y₁.map π₁ = ⊤ := map_commutator_eq_top_of_sl2 hk π₁ hX1
  have hY2m : Y₂.map π₂ = ⊤ := map_commutator_eq_top_of_sl2 hk π₂ hX2
  have hY1k : Y₁ ≤ π₂.ker := commutator_le_self _
  have hY2k : Y₂ ≤ π₁.ker := commutator_le_self _
  have hdec : ∀ x : X, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, (y₁ * y₂)⁻¹ * x ∈ center X := by
    intro x
    obtain ⟨y₁, hy₁, e₁⟩ : π₁ x ∈ Y₁.map π₁ := hY1m ▸ mem_top _
    obtain ⟨y₂, hy₂, e₂⟩ : π₂ x ∈ Y₂.map π₂ := hY2m ▸ mem_top _
    refine ⟨y₁, hy₁, y₂, hy₂, hk1 _ ?_ ?_⟩
    · rw [map_mul, map_inv, map_mul, MonoidHom.mem_ker.1 (hY2k hy₂), mul_one, e₁,
        inv_mul_cancel]
    · rw [map_mul, map_inv, map_mul, MonoidHom.mem_ker.1 (hY1k hy₁), one_mul, e₂,
        inv_mul_cancel]
  have htop : (⊤ : Subgroup X) ≤ Y₁ ⊔ Y₂ := by
    rw [← Group.IsPerfect.commutator_eq_top (G := X), _root_.commutator_def]
    refine commutator_le.2 fun a _ b _ => ?_
    obtain ⟨y₁, hy₁, y₂, hy₂, hz⟩ := hdec a
    obtain ⟨y₁', hy₁', y₂', hy₂', hw⟩ := hdec b
    set u := y₁ * y₂
    set v := y₁' * y₂'
    have hu : u ∈ Y₁ ⊔ Y₂ := mul_mem (mem_sup_left hy₁) (mem_sup_right hy₂)
    have hv : v ∈ Y₁ ⊔ Y₂ := mul_mem (mem_sup_left hy₁') (mem_sup_right hy₂')
    have ha : a = u * (u⁻¹ * a) := by group
    have hb : b = v * (v⁻¹ * b) := by group
    rw [ha, hb]
    generalize u⁻¹ * a = z at hz
    generalize v⁻¹ * b = w at hw
    have e : ⁅u * z, v * w⁆ = ⁅u, v⁆ := by
      rw [TorusLift.commutatorElement_mul_central_left hz,
        TorusLift.commutatorElement_mul_central_right hw]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
  refine eq_bot_iff.2 fun z hz => ?_
  have hzk : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup_of_normal_right.1 (htop (mem_top z))
  have h1 : π₁ (y₁ * y₂) = 1 := congrArg Prod.fst hzk
  have h2 : π₂ (y₁ * y₂) = 1 := congrArg Prod.snd hzk
  rw [map_mul, MonoidHom.mem_ker.1 (hY2k hy₂), mul_one] at h1
  have hy1 : y₁ = 1 := mem_bot.1 (hY1 ▸ mem_inf.2 ⟨hy₁, h1⟩)
  rw [hy1, one_mul] at h2 ⊢
  exact hY2 ▸ mem_inf.2 ⟨hy₂, h2⟩

end CFSG.LocalAnalysis.EvenBN.Common
