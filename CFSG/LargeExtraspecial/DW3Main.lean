module

public import CFSG.LargeExtraspecial.DW3Inv
public import CFSG.LargeExtraspecial.DW3Split
public import CFSG.LargeExtraspecial.DW4Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W3

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting CFSG.LargeExtraspecial.DW
  CFSG.LargeExtraspecial.DW.W4
open scoped IsMulCommutative MatrixGroups

abbrev V₃ : Type := Fin 3 → ZMod 2

@[expose] noncomputable def glToLin₃ : GL (Fin 3) (ZMod 2) ≃* (V₃ ≃ₗ[ZMod 2] V₃) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem card_stabilizer_of_finrank_four {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hE : finrank (ZMod 2) E = 4) {e : E} (he : e ≠ 0) :
    Nat.card (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e) = 1344 := by
  have horbit : MulAction.orbit (E ≃ₗ[ZMod 2] E) e = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      exact fun h => he (g.injective (by rw [map_zero]; exact h))
    · intro hv
      obtain ⟨f, d, hfd, hτ⟩ := exists_transvection_apply_eq he hv
      exact ⟨LinearEquiv.transvection hfd, hτ⟩
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hcardE : Nat.card E = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hE]
    norm_num
  have hidx : (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e).index = 15 := by
    rw [MulAction.index_stabilizer, horbit, show {v : E | v ≠ 0} = Set.univ \ {0} by
      ext v
      simp, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcardE]
  have hGL : Nat.card (E ≃ₗ[ZMod 2] E) = 20160 := by
    rw [card_linearEquiv_eq hE, Matrix.card_GL_field]
    simp [Fin.prod_univ_four, ZMod.card]
  have h := Subgroup.card_mul_index (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e)
  rw [hidx, hGL] at h
  omega

variable {X : Type*} [Group X] [Finite X] {T : Setting X}

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt} (H : Hyp T W₁ W₂)
include H

theorem exists_levi (hsurj : Function.Surjective H.res) {x : X} (hxM : x ∈ T.M)
    (hxQ : x ∉ T.QG) (hx : x * x = 1) {A : Subgroup X} [IsElementaryAbelian 2 A]
    (hA : MaxEA T A) (hAx : ∀ a ∈ A, x * a = a * x) {U₀ U₀' : Subgroup X}
    (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z) (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) :
    ∃ L : Subgroup X, L ≤ T.M ∧ L ≤ normalizer (U₀' : Set X) ∧
      (∀ l ∈ L, l ∈ T.QG → l = 1) ∧ Nat.card L = 168 := by
  set L₂ : Subgroup X := normalizer (U₀ : Set X) ⊓ normalizer (U₀' : Set X) ⊓ T.M with hL₂
  have hL₂M : L₂ ≤ T.M := inf_le_right
  let φ := (Module.finBasisOfFinrankEq (ZMod 2) W₁ H.finrank₁).equivFun
  let η : L₂ →* GL (Fin 3) (ZMod 2) :=
    glToLin₃.symm.toMonoidHom.comp
      ((congrGL φ).toMonoidHom.comp (H.res.comp (Subgroup.inclusion hL₂M)))
  have hη : ∀ j : L₂, η j = glToLin₃.symm (congrGL φ (H.res ⟨j, hL₂M j.2⟩)) := fun _ => rfl
  have hzL₂ : T.z ∈ L₂ := by
    have hzn : ∀ U : Subgroup X, U ≤ T.QG → T.z ∈ normalizer (U : Set X) := fun U hU =>
      mem_normalizer_of_conj_mem fun u hu => by
        rw [← T.z_comm_QG (hU hu), mul_inv_cancel_right]
        exact hu
    exact ⟨⟨hzn U₀ fun _ h => hU₀.mem_QG h, hzn U₀' fun _ h => hU₀'.mem_QG h⟩, T.z_mem_M⟩
  have hres1 : ∀ {m : T.M}, (m : X) ∈ T.QG → H.res m = 1 := fun h => H.res_eq_one_of_mem_QG h
  have hη1 : ∀ j : L₂, η j = 1 ↔ H.res ⟨j, hL₂M j.2⟩ = 1 := fun j => by
    rw [hη, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  have hsurjη : Function.Surjective η := by
    intro g
    obtain ⟨m, hm⟩ := hsurj ((congrGL φ).symm (glToLin₃ g))
    obtain ⟨ν, hν, hν₁, hν₂⟩ := H.exists_mul_mem_normalizer hU₀ hU₀' m.2
    refine ⟨⟨ν * m, ⟨hν₁, hν₂⟩, T.M.mul_mem (T.QG_le_M hν) m.2⟩, ?_⟩
    rw [hη]
    have e : (⟨ν * m, hL₂M ⟨⟨hν₁, hν₂⟩, T.M.mul_mem (T.QG_le_M hν) m.2⟩⟩ : T.M) =
        ⟨ν, T.QG_le_M hν⟩ * m := rfl
    rw [e, map_mul, hres1 hν, one_mul, hm, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hker : ∀ j : L₂, η j = 1 ↔ j = 1 ∨ j = ⟨T.z, hzL₂⟩ := by
    intro j
    rw [hη1]
    constructor
    · intro hj
      have hjQ := H.mem_QG_of_res_eq_one hj
      rcases H.eq_one_or_z_of_mem_normalizer hU₀ hU₀' hjQ j.2.1.1 j.2.1.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact map_one H.res
      · exact hres1 T.z_mem_QG
  obtain ⟨ν, hν, hν₁, hν₂⟩ := H.exists_mul_mem_normalizer hU₀ hU₀' hxM
  have hℓM : ν * x ∈ T.M := T.M.mul_mem (T.QG_le_M hν) hxM
  have hxℓ : x * (ν * x)⁻¹ ∈ T.QG := by
    rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    exact T.QG.inv_mem hν
  have hℓ2 := H.mul_self_eq_one_of_maxEA hU₀ hU₀' hℓM hν₁ hν₂ hx hxℓ hA hAx
  let ℓ : L₂ := ⟨ν * x, ⟨hν₁, hν₂⟩, hℓM⟩
  have hℓ1 : η ℓ ≠ 1 := by
    intro h
    have hℓQ := H.mem_QG_of_res_eq_one ((hη1 ℓ).mp h)
    apply hxQ
    have e : x = ν⁻¹ * (ν * x) := by group
    rw [e]
    exact T.QG.mul_mem (T.QG.inv_mem hν) hℓQ
  obtain ⟨σ, hσ⟩ := exists_section_of_involution η hsurjη hker
    (fun h => T.z_ne_one (congrArg Subtype.val h))
    (fun j => Subtype.ext (T.z_comm (hL₂M j.2)).symm) (Subtype.ext T.z_mul_z)
    (j₀ := ℓ) (Subtype.ext hℓ2) hℓ1
  have hσinj : Function.Injective σ := fun a b hab => by
    rw [← hσ a, ← hσ b, hab]
  set L : Subgroup X := (L₂.subtype.comp σ).range with hL
  have hLL₂ : L ≤ L₂ := by
    rintro _ ⟨a, rfl⟩
    exact (σ a).2
  refine ⟨L, hLL₂.trans hL₂M, hLL₂.trans (inf_le_left.trans inf_le_right), ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ hQ
    have h1 : η (σ a) = 1 := (hη1 _).mpr (hres1 hQ)
    rw [hσ] at h1
    rw [h1, map_one]
  · have hinj : Function.Injective (L₂.subtype.comp σ) :=
      Subtype.val_injective.comp hσinj
    rw [hL, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_GL_three]

theorem nonempty_centralizer_mulEquiv (hsurj : Function.Surjective H.res) {x : X}
    (hxM : x ∈ T.M) (hxQ : x ∉ T.QG) (hx : x * x = 1) {A : Subgroup X}
    [IsElementaryAbelian 2 A] (hA : MaxEA T A) (hAx : ∀ a ∈ A, x * a = a * x) :
    Nonempty (centralizer ({T.z} : Set X) ≃*
      centralizer ({cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) := by
  have := isElementaryAbelian_clPre H.ts₁
  have := isElementaryAbelian_clPre H.ts₂
  obtain ⟨U₀, hU₀⟩ := exists_isZCompl (A := T.clPre W₁) (T.z_mem_clPre W₁) T.z_ne_one T.z_mul_z
  obtain ⟨U₀', hU₀'⟩ :=
    exists_isZCompl (A := T.clPre W₂) (T.z_mem_clPre W₂) T.z_ne_one T.z_mul_z
  obtain ⟨L, hLM, hLN, hLQ, hLcard⟩ := H.exists_levi hsurj hxM hxQ hx hA hAx hU₀ hU₀'
  set C := mulSub U₀' L hLN with hC
  have hCM : C ≤ T.M := by
    rintro _ ⟨w, hw, l, hl, rfl⟩
    exact T.M.mul_mem (T.QG_le_M (hU₀'.mem_QG hw)) (hLM hl)
  have hCcard : Nat.card C = 2 ^ 3 * 168 := by
    rw [card_mulSub hLN fun g hg hgL => hLQ g hgL (hU₀'.mem_QG hg), hU₀'.card_eq,
      H.symm.card₁, hLcard]
  have hCU : ∀ c ∈ C, c ∈ T.clPre W₁ → c = 1 := by
    rintro _ ⟨w, hw, l, hl, rfl⟩ hc
    have hlQ : l ∈ T.QG := by
      have e : l = w⁻¹ * (w * l) := by group
      rw [e]
      exact T.QG.mul_mem (T.QG.inv_mem (hU₀'.mem_QG hw)) hc.1
    rw [hLQ l hl hlQ, mul_one] at hc ⊢
    rcases H.eq_one_or_z_of_mem hc (hU₀'.le hw) with h | h
    · exact h
    · exact absurd (h ▸ hw) hU₀'.not_mem
  have hVM : T.clPre W₁ ≤ T.M := fun _ hy => T.QG_le_M hy.1
  let V : Subgroup T.M := (T.clPre W₁).subgroupOf T.M
  have : V.Normal := ⟨fun n hn g => H.conj_mem_clPre g.2 hn⟩
  have : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVM
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have : Finite (Additive V ≃ₗ[ZMod 2] Additive V) :=
    Finite.of_injective (fun f : Additive V ≃ₗ[ZMod 2] Additive V => (f : Additive V → Additive V))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have hzV : T.zM ∈ V := T.z_mem_clPre W₁
  set z'' : Additive V := Additive.ofMul ⟨T.zM, hzV⟩ with hz''
  set Γ := MulAction.stabilizer (Additive V ≃ₗ[ZMod 2] Additive V) z'' with hΓ
  have hcentV : centralizer (V : Set T.M) ≤ V := by
    intro g hg
    refine H.mem_clPre_of_mem_M g.2 fun y hy => ?_
    have := mem_centralizer_iff.mp hg ⟨y, hVM hy⟩ hy
    exact (congrArg Subtype.val this).symm
  have hmem : ∀ h : T.M, conjLinear V h ∈ Γ := by
    intro h
    change conjLinear V h z'' = z''
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coe_conjLinear_apply]
    apply Subtype.ext
    change (h : X) * T.z * (h : X)⁻¹ = T.z
    rw [T.z_comm h.2, mul_inv_cancel_right]
  let C' : Subgroup T.M := C.subgroupOf T.M
  let ψ : C' →* Γ := ((conjLinear V).comp C'.subtype).codRestrict Γ fun c => hmem c
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have h1 : conjLinear V (c : T.M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    obtain ⟨e, he⟩ := (conjLinear_eq_one_iff V hcentV _).mp h1
    have hcV : ((c : T.M) : X) ∈ T.clPre W₁ := he ▸ (Additive.toMul e).2
    exact mem_bot.mpr (Subtype.ext (Subtype.ext (hCU _ c.2 hcV)))
  have hcardC' : Nat.card C' = Nat.card C := Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv
  have hfinV : finrank (ZMod 2) (Additive V) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = Nat.card V from rfl,
      Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, H.card_clPre₁] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hz0 : z'' ≠ 0 := fun h => T.z_ne_one
    (congrArg (fun x : V => ((x : T.M) : X)) (Additive.ofMul.injective h))
  have hΓcard : Nat.card Γ = 1344 := card_stabilizer_of_finrank_four hfinV hz0
  have hψ : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [hΓcard, hcardC', hCcard]; norm_num)
  let X' : SplittingOn V Γ :=
    { centralizer_le := hcentV
      mem := hmem
      σ := C'.subtype.comp (MulEquiv.ofBijective ψ hψ).symm.toMonoidHom
      conjLinear_σ := fun f =>
        congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply f) }
  obtain ⟨b, hb⟩ := exists_basis_eq hfinV (by norm_num) hz0
  obtain ⟨e₁⟩ := X'.nonempty_centralizer_mulEquiv b (by norm_num) hzV hb (fun f hf => by
    change f z'' = z''
    rw [← hb]
    exact hf)
  have htop : centralizer ({T.zM} : Set T.M) = ⊤ := eq_top_iff.mpr fun g _ =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (T.z_comm g.2))
  exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans e₁⟩

end Hyp

end CFSG.LargeExtraspecial.DW.W3
