module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCenterFourSevenGenerated

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module
open scoped commutatorElement IsMulCommutative
open LinearMap (BilinForm)

namespace CyclicLayerFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem sub_mem_orthogonal_of_fix {g : bilinIsometryGroup b} {T : Submodule (ZMod 2) V}
    (hg : ∀ t ∈ T, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) t = t)
    (v : V) :
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v ∈
      b.orthogonal T := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro t ht
  show b t (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v) = 0
  have h := g.2 t v
  rw [hg t ht] at h
  rw [map_sub, h, sub_self]

theorem finrank_add_finrank_orthogonal_eq (hnd : b.Nondegenerate)
    (T : Submodule (ZMod 2) V) :
    finrank (ZMod 2) T + finrank (ZMod 2) (b.orthogonal T) = finrank (ZMod 2) V := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := b) T
  rw [hnd.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at h
  exact h

theorem card_le_two_of_fix (hnd : b.Nondegenerate) (hV : finrank (ZMod 2) V = 4)
    {T : Submodule (ZMod 2) V} (hT : finrank (ZMod 2) T = 3) (A : Subgroup (bilinIsometryGroup b))
    (hA : ∀ g ∈ A, ∀ t ∈ T,
      (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) t = t) :
    Nat.card A ≤ 2 := by
  classical
  have hTne : T ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hT
    omega
  obtain ⟨v₀, -, hv₀⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hTne)
  have hsup : T ⊔ (ZMod 2) ∙ v₀ = ⊤ := by
    have hlt : T < T ⊔ (ZMod 2) ∙ v₀ := lt_of_le_of_ne le_sup_left fun h =>
      hv₀ (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (T ⊔ (ZMod 2) ∙ v₀)
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hperp : finrank (ZMod 2) (b.orthogonal T) = 1 := by
    have := finrank_add_finrank_orthogonal_eq hnd T
    omega
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (b.orthogonal T) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hperp, Nat.card_zmod, pow_one]
  let φ : A → b.orthogonal T := fun g =>
    ⟨(((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v₀ - v₀, sub_mem_orthogonal_of_fix (hA g g.2) v₀⟩
  have hφ : Function.Injective φ := by
    intro g g' h
    have h1 := congrArg Subtype.val h
    simp only [φ, sub_left_inj] at h1
    have hspan : Submodule.span (ZMod 2) ((T : Set V) ∪ {v₀}) = ⊤ := by
      rw [Submodule.span_union, Submodule.span_eq]
      exact hsup
    have hext := LinearMap.ext_on hspan (f := (((g : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
      (g := (((g' : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)) (by
      rintro v (hv | hv)
      · rw [hA g g.2 v hv, hA g' g'.2 v hv]
      · rw [Set.mem_singleton_iff.mp hv]
        exact h1)
    exact Subtype.ext (Subtype.ext (Units.ext hext))
  have := Nat.card_le_card_of_injective φ hφ
  rwa [hcard] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem orthogonal_span_sub_eq (hnd : b.Nondegenerate) (S : Set (bilinIsometryGroup b))
    (x : V) :
    x ∈ b.orthogonal (Submodule.span (ZMod 2) {u | ∃ g ∈ S, ∃ v : V,
      u = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v}) ↔
      ∀ g ∈ S, ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x = x := by
  constructor
  · intro hx g hg
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    have h1 : ∀ v, b (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) x =
        b v x := by
      intro v
      have := hx _ (Submodule.subset_span ⟨g, hg, v, rfl⟩)
      change b (_ - v) x = 0 at this
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : ∀ w, b w (x - ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x)
        = 0 := by
      intro w
      set gl := ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      have hw : w = gl ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) w) := by
        rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl
      rw [map_sub, hw, h1, g.2]
      exact sub_self _
    have h3 := hnd.2 _ (fun w => h2 w)
    exact (sub_eq_zero.mp h3).symm
  · intro hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    show b u x = 0
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, hg, v, rfl⟩ := hu
      have h := g.2 v x
      rw [hx g hg] at h
      rw [map_sub, LinearMap.sub_apply, h, sub_self]
    | zero => simp
    | add u w _ _ hu hw => rw [map_add, LinearMap.add_apply, hu, hw, add_zero]
    | smul a u _ hu => rw [map_smul, LinearMap.smul_apply, hu, smul_zero]

end Linear

section Action

variable {H : Type*} [Group H] (Y D : Subgroup H) [Y.Normal] [D.Normal]

theorem subgroupOf_le_comap_conjNormal (h : H) :
    Y.subgroupOf D ≤ (Y.subgroupOf D).comap (MulAut.conjNormal h : MulAut D).toMonoidHom := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  show ((MulAut.conjNormal h x : D) : H) ∈ Y
  rw [MulAut.conjNormal_apply]
  exact ‹Y.Normal›.conj_mem _ hx h

@[expose] noncomputable def layerQuot (h : H) : D ⧸ Y.subgroupOf D →* D ⧸ Y.subgroupOf D :=
  QuotientGroup.map _ _ (MulAut.conjNormal h : MulAut D).toMonoidHom
    (subgroupOf_le_comap_conjNormal Y D h)

theorem layerQuot_mk (h : H) (x : D) :
    layerQuot Y D h (x : D ⧸ Y.subgroupOf D) =
      ((MulAut.conjNormal h x : D) : D ⧸ Y.subgroupOf D) :=
  rfl

variable [IsElementaryAbelian 2 (D ⧸ Y.subgroupOf D)]

omit [D.Normal] in
theorem layer_ext {f g : Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))}
    (hfg : ∀ x : D, f (Additive.ofMul (x : D ⧸ Y.subgroupOf D)) =
      g (Additive.ofMul (x : D ⧸ Y.subgroupOf D))) : f = g := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (x : D ⧸ Y.subgroupOf D) := by
    rw [hx]
    rfl
  rw [hv]
  exact hfg x

@[expose] noncomputable def layerEnd :
    H →* Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) where
  toFun h := (MonoidHom.toAdditive (layerQuot Y D h)).toZModLinearMap 2
  map_one' := layer_ext Y D fun x => by
    show Additive.ofMul (layerQuot Y D 1 (x : D ⧸ Y.subgroupOf D)) =
      Additive.ofMul (x : D ⧸ Y.subgroupOf D)
    rw [layerQuot_mk, map_one]
    rfl
  map_mul' g h := layer_ext Y D fun x => by
    show Additive.ofMul (layerQuot Y D (g * h) (x : D ⧸ Y.subgroupOf D)) =
      Additive.ofMul (layerQuot Y D g (layerQuot Y D h (x : D ⧸ Y.subgroupOf D)))
    simp only [layerQuot_mk, map_mul, MulAut.mul_apply]

theorem layerEnd_ofMul_mk (h : H) (x : D) :
    layerEnd Y D h (Additive.ofMul (x : D ⧸ Y.subgroupOf D)) =
      Additive.ofMul ((MulAut.conjNormal h x : D) : D ⧸ Y.subgroupOf D) :=
  rfl

variable {Y D}

@[expose] noncomputable def layerIso {b : BilinForm (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))}
    (hbH : ∀ (h : H) (x y : D),
      b (Additive.ofMul (MulAut.conjNormal h x : D ⧸ Y.subgroupOf D))
        (Additive.ofMul (MulAut.conjNormal h y : D ⧸ Y.subgroupOf D)) =
      b (Additive.ofMul (x : D ⧸ Y.subgroupOf D)) (Additive.ofMul (y : D ⧸ Y.subgroupOf D))) :
    H →* bilinIsometryGroup b :=
  (layerEnd Y D).toHomUnits.codRestrict _ fun h u v => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul u)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hu : u = Additive.ofMul (x : D ⧸ Y.subgroupOf D) := by
      rw [hx]
      rfl
    have hv : v = Additive.ofMul (y : D ⧸ Y.subgroupOf D) := by
      rw [hy]
      rfl
    rw [hu, hv]
    exact hbH h x y

theorem layerEnd_eq_one_iff (h : H) :
    layerEnd Y D h = 1 ↔ ∀ x : D, ((MulAut.conjNormal h x : D) : D ⧸ Y.subgroupOf D) =
      (x : D ⧸ Y.subgroupOf D) := by
  constructor
  · intro h1 x
    have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) =>
      f (Additive.ofMul (x : D ⧸ Y.subgroupOf D))) h1
    simp only [layerEnd_ofMul_mk, Module.End.one_apply] at h2
    exact Additive.ofMul.injective h2
  · intro h1
    refine layer_ext Y D fun x => ?_
    rw [layerEnd_ofMul_mk, Module.End.one_apply, h1 x]

theorem layerIso_eq_one_iff {b : BilinForm (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))}
    (hbH : ∀ (h : H) (x y : D),
      b (Additive.ofMul (MulAut.conjNormal h x : D ⧸ Y.subgroupOf D))
        (Additive.ofMul (MulAut.conjNormal h y : D ⧸ Y.subgroupOf D)) =
      b (Additive.ofMul (x : D ⧸ Y.subgroupOf D)) (Additive.ofMul (y : D ⧸ Y.subgroupOf D)))
    (h : H) :
    layerIso hbH h = 1 ↔ ∀ x : D, ((MulAut.conjNormal h x : D) : D ⧸ Y.subgroupOf D) =
      (x : D ⧸ Y.subgroupOf D) := by
  rw [← layerEnd_eq_one_iff]
  constructor
  · intro h1
    exact congrArg (fun g : bilinIsometryGroup b =>
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
        Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)))) h1
  · intro h1
    exact Subtype.ext (Units.ext h1)

end Action

section Counting

open CFSG.LargeEvenClassification.Helpers

theorem card_frattini_quotient_eq {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X) :
    Nat.card (X ⧸ frattini X) = 2 ^ pGeneratorRank 2 X := by
  obtain ⟨-, -, -, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hX
  rw [hd, pGeneratorRank, hd, Nat.log_pow (by norm_num)]

theorem index_chain {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {C Dp N : Subgroup G} [C.Normal] [Dp.Normal] [N.Normal] (hCD : C ≤ Dp) (hDN : Dp ≤ N) :
    ((frattini N).map N.subtype ⊔ ⁅N, ⊤⁆).relIndex N ≤
      2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) *
        ((C ⊔ (((frattini N).map N.subtype ⊔ ⁅N, ⊤⁆) ⊓ Dp)).relIndex Dp *
          2 ^ pGeneratorRank 2 C) := by
  obtain ⟨-, hEn, hEN, -⟩ := p_group_Frattini_coinvariant_generator_bound hG N rfl
  set E := (frattini N).map N.subtype ⊔ ⁅N, ⊤⁆ with hEdef
  have hNp : IsPGroup 2 N := hG.to_subgroup N
  have hΦE : (frattini N).map N.subtype ≤ E := le_sup_left
  have hΦN : (frattini N).map N.subtype ≤ N := map_subtype_le _
  have h1 := Subgroup.relIndex_mul_relIndex E (Dp ⊔ E) N le_sup_right (sup_le hDN hEN)
  have h2 : (Dp ⊔ E).relIndex N ≤ 2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) := by
    have hle : (Dp ⊔ E).relIndex N ≤ (Dp ⊔ (frattini N).map N.subtype).relIndex N :=
      Subgroup.relIndex_le_of_le_left (sup_le_sup_left hΦE Dp)
        (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    refine hle.trans ?_
    let f := QuotientGroup.mk' (Dp.subgroupOf N)
    have heq : (Dp ⊔ (frattini N).map N.subtype).subgroupOf N =
        ((frattini N).map f).comap f := by
      rw [Subgroup.subgroupOf_sup hDN hΦN, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_comm]
      congr 1
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [Subgroup.relIndex, heq, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective _), ← card_frattini_quotient_eq (hNp.to_quotient _)]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le
      (frattini_quotient_le_map hNp (Dp.subgroupOf N)))
  have h3 : E.relIndex (Dp ⊔ E) = (E ⊓ Dp).relIndex Dp := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right]
  have h4 := Subgroup.relIndex_mul_relIndex (E ⊓ Dp) (C ⊔ (E ⊓ Dp)) Dp le_sup_right
    (sup_le hCD inf_le_right)
  have h5 : (E ⊓ Dp).relIndex (C ⊔ (E ⊓ Dp)) ≤ 2 ^ pGeneratorRank 2 C := by
    have : (E ⊓ Dp).Normal := Subgroup.normal_inf_normal _ _
    rw [Subgroup.relIndex_sup_right, ← card_frattini_quotient_eq (hG.to_subgroup C)]
    refine Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le ?_)
    have hCp : IsPGroup 2 C := hG.to_subgroup C
    rw [frattini_eq_pow_sup_commutator hCp]
    refine sup_le ?_ ?_
    · rw [closure_le]
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      refine ⟨mem_sup_left ?_, Dp.pow_mem (hCD c.2) 2⟩
      have : Fact (IsPGroup 2 N) := ⟨hNp⟩
      exact ⟨⟨c, hDN (hCD c.2)⟩ ^ 2,
        CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ c _
      rw [Subgroup.mem_subgroupOf]
      have e : ((⁅a, c⁆ : C) : G) = ⁅(a : G), (c : G)⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      refine ⟨mem_sup_right ?_, ?_⟩
      · have ha : (a : G) ∈ N := hDN (hCD a.2)
        exact Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := ⊤) ha (mem_top (c : G))
      · have hc : ⁅(a : G), (c : G)⁆ ∈ Dp :=
          Dp.mul_mem (Dp.mul_mem (Dp.mul_mem (hCD a.2) (hCD c.2)) (Dp.inv_mem (hCD a.2)))
            (Dp.inv_mem (hCD c.2))
        exact hc
  calc E.relIndex N = E.relIndex (Dp ⊔ E) * (Dp ⊔ E).relIndex N := h1.symm
    _ = (E ⊓ Dp).relIndex Dp * (Dp ⊔ E).relIndex N := by rw [h3]
    _ ≤ (E ⊓ Dp).relIndex Dp * 2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) :=
        Nat.mul_le_mul_left _ h2
    _ = (E ⊓ Dp).relIndex (C ⊔ (E ⊓ Dp)) * (C ⊔ (E ⊓ Dp)).relIndex Dp *
          2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) := by rw [h4]
    _ ≤ 2 ^ pGeneratorRank 2 C * (C ⊔ (E ⊓ Dp)).relIndex Dp *
          2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h5)
    _ = 2 ^ pGeneratorRank 2 (N ⧸ Dp.subgroupOf N) *
          ((C ⊔ (E ⊓ Dp)).relIndex Dp * 2 ^ pGeneratorRank 2 C) := by ring

end Counting

end CyclicLayerFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LargeEvenClassification.Helpers CyclicLayerFour CenterFourSixtyFour in
theorem cyclic_layer_symplectic_four_extension_seven_generated {H : Type*} [Group H] [Finite H]
    {Y D Q : Subgroup H} [Y.Normal] [D.Normal] [Q.Normal] (hYD : Y ≤ D) (hDQ : D ≤ Q)
    (_hQ : IsPGroup 2 Q) (hY : IsCyclic Y) (hQD : D.relIndex Q ≤ 2)
    [IsElementaryAbelian 2 (D ⧸ Y.subgroupOf D)] (hV : Nat.card (D ⧸ Y.subgroupOf D) = 16)
    (b : BilinForm (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) (hb : b.IsAlt)
    (hnd : b.Nondegenerate)
    (hbH : ∀ (h : H) (x y : D),
      b (Additive.ofMul (MulAut.conjNormal h x : D ⧸ Y.subgroupOf D))
        (Additive.ofMul (MulAut.conjNormal h y : D ⧸ Y.subgroupOf D)) =
      b (Additive.ofMul (x : D ⧸ Y.subgroupOf D)) (Additive.ofMul (y : D ⧸ Y.subgroupOf D)))
    (hker : ∀ h : H, (∀ x : D, ((MulAut.conjNormal h x : D) : D ⧸ Y.subgroupOf D) =
      (x : D ⧸ Y.subgroupOf D)) ↔ h ∈ Q) :
    ∀ P : Subgroup H, IsPGroup 2 P →
      let π : D → Additive (D ⧸ Y.subgroupOf D) := fun x =>
        Additive.ofMul (x : D ⧸ Y.subgroupOf D)
      let W : Submodule (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) :=
        Submodule.span (ZMod 2) {v | ∃ x : D, (x : H) ∈ P ∧ v = π x}
      let WR : Submodule (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) :=
        Submodule.span (ZMod 2) {v | ∃ (h : H) (x : D), h ∈ P ∧ (x : H) ∈ P ∧
          v = π (MulAut.conjNormal h x) - π x}
      let r := pGeneratorRank 2 (P ⧸ Q.subgroupOf P)
      let c := finrank (ZMod 2) (W ⧸ WR.comap W.subtype)
      let dC := pGeneratorRank 2 (Y.subgroupOf P)
      let dND := pGeneratorRank 2
        (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P))
      r ≤ 3 ∧ (r = 0 → c ≤ 4) ∧ (r = 1 → c ≤ 3) ∧ (r = 2 ∨ r = 3 → c ≤ 2) ∧
      pGeneratorRank 2 P ≤ dC + dND + c + r ∧ dC + dND + c + r ≤ 7 ∧
      (∃ S : Finset P, S.card ≤ 7 ∧ closure (S : Set P) = ⊤) ∧
      (∀ (L : Subgroup P) [L.Normal], IsElementaryAbelian 2 (P ⧸ L) →
        Nat.card (P ⧸ L) ≤ 2 ^ 7) ∧
      (Q = D → ∃ S : Finset P, S.card ≤ 6 ∧ closure (S : Set P) = ⊤) := by
  classical
  intro P hP π W WR r c dC dND
  have : Finite (Additive (D ⧸ Y.subgroupOf D)) := inferInstanceAs (Finite (D ⧸ Y.subgroupOf D))
  have : FiniteDimensional (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (D ⧸ Y.subgroupOf D))
    rw [Nat.card_zmod] at h
    have h' : (2 : ℕ) ^ finrank (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)) = 2 ^ 4 := by
      rw [← h]
      exact hV
    exact Nat.pow_right_injective (le_refl 2) h'
  obtain ⟨e, he⟩ := BinarySymplecticSix.exists_isSymplecticBasis hb hnd (n := 2)
    (by rw [hdim])
  let ψ : H →* bilinIsometryGroup b := layerIso hbH
  have hψ : ∀ h : H, ψ h = 1 ↔ h ∈ Q := fun h => (layerIso_eq_one_iff hbH h).trans (hker h)
  have hψapp : ∀ (h : H) (x : D), (((ψ h : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
        Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) (π x) =
      π (MulAut.conjNormal h x) := fun h x => rfl
  have hπmul : ∀ x y : D, π (x * y) = π x + π y := fun x y => by
    simp only [π, QuotientGroup.mk_mul, ofMul_mul]
  have hπone : π 1 = 0 := by
    simp only [π, QuotientGroup.mk_one, ofMul_one]
  have hWmem : ∀ v, v ∈ W ↔ ∃ x : D, (x : H) ∈ P ∧ v = π x := by
    intro v
    refine ⟨fun hv => ?_, fun hv => Submodule.subset_span hv⟩
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨1, P.one_mem, hπone.symm⟩
    | add u w _ _ hu hw =>
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨x * y, P.mul_mem hx hy, (hπmul x y).symm⟩
    | smul a u _ hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
      · exact ⟨1, P.one_mem, by rw [zero_smul, hπone]⟩
      · exact ⟨x, hx, one_smul _ _⟩
  have hWRW : WR ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨h, x, hh, hx, rfl⟩
    refine W.sub_mem ((hWmem _).mpr ⟨MulAut.conjNormal h x, ?_, rfl⟩) ((hWmem _).mpr ⟨x, hx, rfl⟩)
    rw [MulAut.conjNormal_apply]
    exact P.mul_mem (P.mul_mem hh hx) (P.inv_mem hh)
  have hgenWR : ∀ h ∈ P, ∀ w ∈ W, (((ψ h : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
        Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) w - w ∈ WR := by
    intro h hh w hw
    obtain ⟨x, hx, rfl⟩ := (hWmem w).mp hw
    exact Submodule.subset_span ⟨h, x, hh, hx, by rw [hψapp]⟩
  have hc : c + finrank (ZMod 2) WR = finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_quotient_add_finrank (WR.comap W.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe hWRW).finrank_eq] at h1
    exact h1
  have hW4 : finrank (ZMod 2) W ≤ 4 := hdim ▸ Submodule.finrank_le W
  let φP : P →* bilinIsometryGroup b := ψ.comp P.subtype
  have hkerP : φP.ker = Q.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hψ x
  have hRp : IsPGroup 2 (P ⧸ Q.subgroupOf P) := hP.to_quotient _
  have hRr : Nat.card ((P ⧸ Q.subgroupOf P) ⧸ frattini (P ⧸ Q.subgroupOf P)) = 2 ^ r :=
    card_frattini_quotient_eq hRp
  have hRA : Nat.card (P ⧸ Q.subgroupOf P) = Nat.card φP.range := by
    rw [← hkerP]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φP).toEquiv
  have hr3 : r ≤ 3 := by
    let ι : P ⧸ Q.subgroupOf P →* StatedSp 2 (ZMod 2) :=
      (BinarySymplecticSix.spCoord he).toMonoidHom.comp
        ((QuotientGroup.kerLift φP).comp
          (QuotientGroup.quotientMulEquivOfEq hkerP.symm).toMonoidHom)
    have hι : Function.Injective ι :=
      (BinarySymplecticSix.spCoord he).injective.comp
        ((QuotientGroup.kerLift_injective φP).comp (MulEquiv.injective _))
    have h8 := card_frattini_quotient_le_eight hRp ι hι
    rw [hRr] at h8
    exact le_of_two_pow_le_two_pow (m := 3) (by simpa using h8)
  have hRcard : 2 ^ r ≤ Nat.card (P ⧸ Q.subgroupOf P) := by
    rw [← hRr]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hout : 1 ≤ r → ∃ h ∈ P, h ∉ Q := by
    intro hr1
    by_contra hcon
    push Not at hcon
    have htop : Q.subgroupOf P = ⊤ := Subgroup.subgroupOf_eq_top.mpr hcon
    have h1 : Nat.card (P ⧸ Q.subgroupOf P) = 1 := by
      rw [← Subgroup.index, htop, Subgroup.index_top]
    have := Nat.one_lt_two_pow (show r ≠ 0 by omega)
    omega
  have hfix3 : ∀ T : Submodule (ZMod 2) (Additive (D ⧸ Y.subgroupOf D)),
      finrank (ZMod 2) T = 3 → (∀ h ∈ P, ∀ t ∈ T, (((ψ h : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
          Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) t = t) →
      Nat.card (P ⧸ Q.subgroupOf P) ≤ 2 := by
    intro T hT hTfix
    rw [hRA]
    refine card_le_two_of_fix hnd hdim hT φP.range ?_
    rintro _ ⟨p, rfl⟩ t ht
    exact hTfix p p.2 t ht
  have hWRpos : (∃ h ∈ P, ∃ w ∈ W, (((ψ h : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
        Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) w ≠ w) →
      1 ≤ finrank (ZMod 2) WR := by
    rintro ⟨h, hh, w, hw, hne⟩
    by_contra h0
    have hbot : WR = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have := hgenWR h hh w hw
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
    exact hne this
  have hWtop : finrank (ZMod 2) W = 4 → W = ⊤ := fun h4 =>
    Submodule.eq_top_of_finrank_eq (by rw [h4, hdim])
  have hc1 : r = 1 → c ≤ 3 := by
    intro hr
    by_cases hW3 : finrank (ZMod 2) W ≤ 3
    · omega
    · have hWt := hWtop (by omega)
      obtain ⟨h, hhP, hhQ⟩ := hout (by omega)
      have hnt := (hker h).not.mpr hhQ
      push Not at hnt
      obtain ⟨x, hx⟩ := hnt
      have h1 := hWRpos ⟨h, hhP, π x, hWt ▸ Submodule.mem_top, by
        rw [hψapp]
        exact fun h' => hx (Additive.ofMul.injective h')⟩
      omega
  have hc23 : r = 2 ∨ r = 3 → c ≤ 2 := by
    intro hr
    have hR4 : 4 ≤ Nat.card (P ⧸ Q.subgroupOf P) := by
      have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    by_cases hW2 : finrank (ZMod 2) W ≤ 2
    · omega
    · by_cases hW3 : finrank (ZMod 2) W = 3
      · by_contra hcon
        have hWR0 : finrank (ZMod 2) WR = 0 := by omega
        have hbot : WR = ⊥ := Submodule.finrank_eq_zero.mp hWR0
        have := hfix3 W hW3 fun h hh w hw => by
          have h1 := hgenWR h hh w hw
          rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
          exact h1
        omega
      · have hWt := hWtop (by omega)
        let Sset : Set (bilinIsometryGroup b) := φP.range
        have hWReq : WR = Submodule.span (ZMod 2) {u | ∃ g ∈ Sset, ∃ v,
            u = ((g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
              Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) v - v} := by
          refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
          · rintro _ ⟨h, x, hh, -, rfl⟩
            exact Submodule.subset_span ⟨φP ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, π x, by rw [← hψapp]; rfl⟩
          · rintro _ ⟨_, ⟨p, rfl⟩, v, rfl⟩
            exact hgenWR p p.2 v (hWt ▸ Submodule.mem_top)
        have hperp := finrank_add_finrank_orthogonal_eq hnd WR
        have hfixed : ∀ x, x ∈ b.orthogonal WR ↔ ∀ h ∈ P, (((ψ h : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) :
              Module.End (ZMod 2) (Additive (D ⧸ Y.subgroupOf D))) x = x := by
          intro x
          rw [hWReq, orthogonal_span_sub_eq hnd]
          constructor
          · intro hx h hh
            exact hx (φP ⟨h, hh⟩) ⟨⟨h, hh⟩, rfl⟩
          · rintro hx _ ⟨p, rfl⟩
            exact hx p p.2
        rw [hdim] at hperp
        have hcW : c = finrank (ZMod 2) (b.orthogonal WR) := by
          rw [hWt, finrank_top, hdim] at hc
          omega
        by_contra hcon
        by_cases hF3 : finrank (ZMod 2) (b.orthogonal WR) = 3
        · have := hfix3 (b.orthogonal WR) hF3 fun h hh t ht => (hfixed t).mp ht h hh
          omega
        · have hF4 : finrank (ZMod 2) (b.orthogonal WR) = 4 := by
            have := Submodule.finrank_le (b.orthogonal WR)
            rw [hdim] at this
            omega
          have hFt : b.orthogonal WR = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hF4, hdim])
          obtain ⟨h, hhP, hhQ⟩ := hout (by omega)
          apply hhQ
          rw [← hker h]
          intro x
          have := (hfixed (π x)).mp (hFt ▸ Submodule.mem_top) h hhP
          rw [hψapp] at this
          exact Additive.ofMul.injective this
  obtain ⟨-, -, hEN, -, dP, dQ, dN, hdP, hdQ, hdN, hle, S, hS, hSc⟩ :=
    p_group_Frattini_coinvariant_generator_bound hP (Q.subgroupOf P) rfl
  set E : Subgroup P := (frattini (Q.subgroupOf P)).map (Q.subgroupOf P).subtype ⊔
    ⁅Q.subgroupOf P, ⊤⁆ with hEdef
  have hdQr : dQ = r := by
    rw [hRr] at hdQ
    exact (Nat.pow_right_injective (le_refl 2) hdQ).symm
  have hdPeq : pGeneratorRank 2 P = dP := by
    rw [card_frattini_quotient_eq hP] at hdP
    exact Nat.pow_right_injective (le_refl 2) hdP
  have hYP : Y.subgroupOf P ≤ D.subgroupOf P := fun x hx => hYD hx
  have hDP : D.subgroupOf P ≤ Q.subgroupOf P := fun x hx => hDQ hx
  have hchain := index_chain hP hYP hDP
  rw [← hEdef] at hchain
  have hstep6 : (Y.subgroupOf P ⊔ (E ⊓ D.subgroupOf P)).relIndex (D.subgroupOf P) ≤ 2 ^ c := by
    let ι₀ : D.subgroupOf P →* D :=
      { toFun := fun x => ⟨((x : P) : H), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let ρ : D.subgroupOf P →* D ⧸ Y.subgroupOf D := (QuotientGroup.mk' _).comp ι₀
    have hρker : ρ.ker = (Y.subgroupOf P).subgroupOf (D.subgroupOf P) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    let X : Subgroup (D.subgroupOf P) := (E ⊓ D.subgroupOf P).subgroupOf (D.subgroupOf P)
    have heq : (Y.subgroupOf P ⊔ (E ⊓ D.subgroupOf P)).subgroupOf (D.subgroupOf P) =
        (X.map ρ).comap ρ := by
      rw [Subgroup.subgroupOf_sup hYP inf_le_right, Subgroup.comap_map_eq, hρker, sup_comm]
    have hrange : Subgroup.toAddSubgroup ρ.range = W.toAddSubgroup := by
      ext v
      rw [Additive.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, hWmem]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨ι₀ x, (x : P).2, ?_⟩
        rw [← ofMul_toMul v, ← hx]
        rfl
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨⟨x, hx⟩, x.2⟩, rfl⟩
    have hWRle : WR.toAddSubgroup ≤ Subgroup.toAddSubgroup (X.map ρ) := by
      have : WR ≤ AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (X.map ρ)) := by
        rw [Submodule.span_le]
        rintro _ ⟨h, x, hh, hx, rfl⟩
        rw [SetLike.mem_coe, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
        let hP' : P := ⟨h, hh⟩
        let xP : P := ⟨x, hx⟩
        have hxN : xP ∈ Q.subgroupOf P := hDQ x.2
        have hcD : ⁅hP', xP⁆ ∈ D.subgroupOf P := by
          rw [Subgroup.mem_subgroupOf]
          simp only [hP', xP, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
          exact D.mul_mem (‹D.Normal›.conj_mem _ x.2 h) (D.inv_mem x.2)
        refine ⟨⟨⁅hP', xP⁆, hcD⟩, ?_, ?_⟩
        · show (⟨⁅hP', xP⁆, hcD⟩ : D.subgroupOf P) ∈
            (E ⊓ D.subgroupOf P).subgroupOf (D.subgroupOf P)
          rw [Subgroup.mem_subgroupOf]
          refine ⟨mem_sup_right ?_, hcD⟩
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator (mem_top hP') hxN
        · show (QuotientGroup.mk (ι₀ ⟨⁅hP', xP⁆, hcD⟩) : D ⧸ Y.subgroupOf D) =
            Additive.toMul (π (MulAut.conjNormal h x) - π x)
          simp only [π, toMul_sub, toMul_ofMul, ← QuotientGroup.mk_div]
          congr 1
          apply Subtype.ext
          simp [ι₀, hP', xP, commutatorElement_def, MulAut.conjNormal_apply, div_eq_mul_inv]
      exact this
    rw [Subgroup.relIndex, heq, Subgroup.index_comap, ← Subgroup.relIndex_toAddSubgroup,
      hrange]
    refine (AddSubgroup.relIndex_le_of_le_left hWRle ?_).trans ?_
    · rw [AddSubgroup.relIndex]
      exact AddSubgroup.index_ne_zero_of_finite
    · have h2c := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ WR.comap W.subtype)
      rw [Nat.card_zmod] at h2c
      rw [← h2c]
      exact le_of_eq rfl
  have hdC : dC ≤ 1 := by
    have hCc : IsCyclic (Y.subgroupOf P) := by
      let j : Y.subgroupOf P →* Y :=
        { toFun := fun x => ⟨((x : P) : H), x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact isCyclic_of_injective j fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) hab))
    have hCp : IsPGroup 2 (Y.subgroupOf P) := hP.to_subgroup _
    obtain ⟨-, -, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hCp
    have hcyc : IsCyclic (Y.subgroupOf P ⧸ frattini (Y.subgroupOf P)) :=
      isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hexp : Monoid.exponent (Y.subgroupOf P ⧸ frattini (Y.subgroupOf P)) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    rw [IsCyclic.exponent_eq_card, card_frattini_quotient_eq hCp] at hexp
    have := Nat.le_of_dvd (by norm_num) hexp
    exact le_of_two_pow_le_two_pow (m := 1) (by simpa using this)
  have hND : Nat.card (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P)) ≤ 2 := by
    change (D.subgroupOf P).relIndex (Q.subgroupOf P) ≤ 2
    rw [← Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      ← Subgroup.inf_relIndex_right, show D ⊓ P ⊓ (Q ⊓ P) = D ⊓ (Q ⊓ P) by
        rw [inf_assoc, inf_comm P, inf_assoc, inf_idem], Subgroup.inf_relIndex_right]
    refine (Subgroup.relIndex_le_of_le_right inf_le_left ?_).trans hQD
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hNDp : IsPGroup 2 (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P)) :=
    (hP.to_subgroup _).to_quotient _
  have hdND : dND ≤ 1 := by
    have h1 := card_frattini_quotient_eq hNDp
    have h2 : Nat.card ((Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P)) ⧸
        frattini (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P))) ≤ 2 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans hND
    rw [h1] at h2
    exact le_of_two_pow_le_two_pow (m := 1) (by simpa using h2)
  have hdN' : dN ≤ dC + dND + c := by
    have h1 : 2 ^ dN ≤ 2 ^ (dC + dND + c) := by
      rw [← hdN]
      calc Nat.card (Q.subgroupOf P ⧸ E.subgroupOf (Q.subgroupOf P))
          = E.relIndex (Q.subgroupOf P) := rfl
        _ ≤ 2 ^ dND * ((Y.subgroupOf P ⊔ (E ⊓ D.subgroupOf P)).relIndex (D.subgroupOf P) *
            2 ^ dC) := hchain
        _ ≤ 2 ^ dND * (2 ^ c * 2 ^ dC) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hstep6)
        _ = 2 ^ (dC + dND + c) := by rw [← pow_add, ← pow_add]; ring_nf
    exact le_of_two_pow_le_two_pow h1
  have hcr : c + r ≤ 5 := by
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h
    · omega
    · have := hc1 h
      omega
    · have := hc23 (Or.inl h)
      omega
    · have := hc23 (Or.inr h)
      omega
  refine ⟨hr3, fun _ => by omega, hc1, hc23, by omega, by omega, ⟨S, by omega, hSc⟩,
    fun L _ hEA => ?_, fun hQD' => ⟨S, ?_, hSc⟩⟩
  · have hle' : frattini P ≤ L := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary
      (p := 2) L (fun a b => hEA.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p a)
    have h1 : L.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hle'
    have h2 : (frattini P).index = 2 ^ dP := hdP
    calc Nat.card (P ⧸ L) = L.index := rfl
      _ ≤ (frattini P).index := Nat.le_of_dvd (by rw [h2]; positivity) h1
      _ = 2 ^ dP := h2
      _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hdND0 : dND = 0 := by
      have htop : (D.subgroupOf P).subgroupOf (Q.subgroupOf P) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        rw [hQD']
      have h1 := card_frattini_quotient_eq hNDp
      have h2 : Nat.card ((Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P)) ⧸
          frattini (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P))) ≤ 1 := by
        refine (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans ?_
        rw [← Subgroup.index, htop, Subgroup.index_top]
      rw [h1] at h2
      have h3 : (2 : ℕ) ^ dND ≤ 1 := h2
      by_contra h0
      have := Nat.one_lt_two_pow h0
      omega
    omega

end CFSG.LocalAnalysis.GorensteinLyons
