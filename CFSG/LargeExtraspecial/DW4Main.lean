module

public import CFSG.LargeExtraspecial.DW4Carm
public import CFSG.LargeExtraspecial.DW4Model
public import CFSG.LargeExtraspecial.DWModelSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting CFSG.LargeExtraspecial.DW
open scoped IsMulCommutative MatrixGroups

variable {X : Type*} [Group X]

@[expose] def mulSub (U L : Subgroup X) (hL : L ≤ normalizer (U : Set X)) : Subgroup X where
  carrier := {g | ∃ u ∈ U, ∃ l ∈ L, u * l = g}
  mul_mem' := by
    rintro _ _ ⟨u, hu, l, hl, rfl⟩ ⟨u', hu', l', hl', rfl⟩
    exact ⟨u * (l * u' * l⁻¹), U.mul_mem hu ((mem_normalizer_iff.mp (hL hl) u').mp hu'),
      l * l', L.mul_mem hl hl', by group⟩
  one_mem' := ⟨1, U.one_mem, 1, L.one_mem, mul_one 1⟩
  inv_mem' := by
    rintro _ ⟨u, hu, l, hl, rfl⟩
    exact ⟨l⁻¹ * u⁻¹ * l⁻¹⁻¹, (mem_normalizer_iff.mp (hL (L.inv_mem hl)) u⁻¹).mp (U.inv_mem hu),
      l⁻¹, L.inv_mem hl, by group⟩

theorem mem_mulSub {U L : Subgroup X} {hL : L ≤ normalizer (U : Set X)} {g : X} :
    g ∈ mulSub U L hL ↔ ∃ u ∈ U, ∃ l ∈ L, u * l = g := Iff.rfl

theorem card_mulSub [Finite X] {U L : Subgroup X} (hL : L ≤ normalizer (U : Set X))
    (hUL : ∀ g ∈ U, g ∈ L → g = 1) : Nat.card (mulSub U L hL) = Nat.card U * Nat.card L := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : U × L =>
    (⟨(p.1 : X) * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩ : mulSub U L hL)) ⟨?_, ?_⟩)
  · rintro ⟨u, l⟩ ⟨u', l'⟩ h
    have h1 : (u : X) * l = u' * l' := congrArg Subtype.val h
    have h2 : (u' : X)⁻¹ * u = l' * (l : X)⁻¹ := by
      calc (u' : X)⁻¹ * u = (u' : X)⁻¹ * (u * l) * (l : X)⁻¹ := by group
        _ = (u' : X)⁻¹ * (u' * l') * (l : X)⁻¹ := by rw [h1]
        _ = l' * (l : X)⁻¹ := by group
    have h3 := hUL _ (U.mul_mem (U.inv_mem u'.2) u.2) (h2 ▸ L.mul_mem l'.2 (L.inv_mem l.2))
    have hu : u = u' := Subtype.ext (by
      have := h3
      rw [inv_mul_eq_one] at this
      exact this.symm)
    have hl : l = l' := Subtype.ext (by
      rw [hu] at h1
      exact mul_left_cancel h1)
    rw [hu, hl]
  · rintro ⟨g, u, hu, l, hl, rfl⟩
    exact ⟨⟨⟨u, hu⟩, ⟨l, hl⟩⟩, rfl⟩

variable [Finite X] {T : Setting X}

omit [Finite X] in
theorem IsZCompl.card_eq {U : Subgroup X} {W : Submodule (ZMod 2) T.Qt}
    (hU : IsZCompl U (T.clPre W) T.z) : Nat.card U = Nat.card W :=
  Nat.card_congr (Equiv.ofBijective (fun u : U => (⟨T.cl u, hU.cl_mem u.2⟩ : W))
    ⟨fun u u' h => Subtype.ext (hU.eq_of_cl_eq u.2 u'.2 (congrArg Subtype.val h)),
      fun w => by
        obtain ⟨u, hu, hw⟩ := hU.exists_cl_eq w.2
        exact ⟨⟨u, hu⟩, Subtype.ext hw⟩⟩)

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt} (H : Hyp T W₁ W₂)
include H

theorem nonempty_centralizer_mulEquiv (hsurj : Function.Surjective H.res)
    (hx : ∃ x : T.M, x * x = 1 ∧ IsRank2Inv (H.res x)) :
    Nonempty (centralizer ({T.z} : Set X) ≃*
      centralizer ({cornerTransvection (N := 6) (by norm_num)} : Set (SL(6, ZMod 2)))) := by
  have := isElementaryAbelian_clPre H.ts₁
  have := isElementaryAbelian_clPre H.ts₂
  obtain ⟨U₀, hU₀⟩ := exists_isZCompl (A := T.clPre W₁) (T.z_mem_clPre W₁) T.z_ne_one T.z_mul_z
  obtain ⟨U₀', hU₀'⟩ :=
    exists_isZCompl (A := T.clPre W₂) (T.z_mem_clPre W₂) T.z_ne_one T.z_mul_z
  obtain ⟨L, hLM, hLN, hLQ, -, hLcard⟩ := H.exists_levi hsurj hx hU₀ hU₀'
  set C := mulSub U₀' L hLN with hC
  have hCM : C ≤ T.M := by
    rintro _ ⟨w, hw, l, hl, rfl⟩
    exact T.M.mul_mem (T.QG_le_M (hU₀'.mem_QG hw)) (hLM hl)
  have hCcard : Nat.card C = 2 ^ 4 * 20160 := by
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
  have hfinV : finrank (ZMod 2) (Additive V) = 5 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = Nat.card V from rfl,
      Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, H.card_clPre₁] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hz0 : z'' ≠ 0 := fun h => T.z_ne_one
    (congrArg (fun x : V => ((x : T.M) : X)) (Additive.ofMul.injective h))
  have hΓcard : Nat.card Γ = 322560 := card_stabilizer_of_finrank_five hfinV hz0
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

theorem exists_isRank2Inv_of_le {E : Subgroup X} (hEM : E ≤ T.M)
    (hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hsq : ∀ e ∈ E, e * e = 1)
    (hcard : 2 ^ 9 ≤ Nat.card E) : ∃ x : T.M, x * x = 1 ∧ IsRank2Inv (H.res x) := by
  obtain ⟨f, hf⟩ : ∃ f : E →* (W₁ ≃ₗ[ZMod 2] W₁), f = H.res.comp (Subgroup.inclusion hEM) :=
    ⟨_, rfl⟩
  have hfe : ∀ e : E, f e = H.res (Subgroup.inclusion hEM e) := fun e => by rw [hf]; rfl
  have hker : Nat.card f.ker ≤ 2 ^ 5 := by
    have hA : Nat.card (E ⊓ T.QG : Subgroup X) ≤ 2 ^ (T.width + 1) :=
      T.card_le_of_commute inf_le_right fun x hx y hy => hcomm x hx.1 y hy.1
    rw [H.width] at hA
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : f.ker => (⟨((k : E) : X), (k : E).2,
        H.mem_QG_of_res_eq_one ((hfe k).symm.trans (MonoidHom.mem_ker.mp k.2))⟩ :
          (E ⊓ T.QG : Subgroup X)))
      fun k k' hkk' => by
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg Subtype.val hkk'
        exact this) hA
  have hrange : 16 ≤ Nat.card f.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    have h2 : 2 ^ 9 ≤ Nat.card f.range * 2 ^ 5 :=
      hcard.trans (h1.le.trans (Nat.mul_le_mul_left _ hker))
    omega
  obtain ⟨y, ⟨e, rfl⟩, hy⟩ := exists_isRank2Inv H.finrank₁ f.range
    (by
      rintro _ ⟨e, rfl⟩
      rw [← map_mul, show e * e = 1 from Subtype.ext (hsq e e.2), map_one])
    hrange
  exact ⟨Subgroup.inclusion hEM e, Subtype.ext (hsq e e.2), (hfe e) ▸ hy⟩

end Hyp

end CFSG.LargeExtraspecial.DW.W4
