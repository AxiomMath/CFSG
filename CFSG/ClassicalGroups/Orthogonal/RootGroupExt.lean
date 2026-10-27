module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed
public import CFSG.ClassicalGroups.ExtendIdentity
public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def Eom (Q : QuadraticForm K V) (u w : V) : Gom Q :=
  ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩

theorem Eom_app {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (x : V) :
    (Eom Q u w).app x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u :=
  eichler_apply hu hw x

theorem Eom_mem_Lom {u w : V} (hw : polar Q u w = 0) : Eom Q u w ∈ Lom Q u :=
  eichler_mem_rootGroup hw

theorem Eom_mul_self [CharP K 2] {u w : V} (hw : polar Q u w = 0) :
    Eom Q u w * Eom Q u w = 1 :=
  Subtype.ext (sq_eq_one_of_mem_rootGroup CharTwo.two_eq_zero (eichler_mem_rootGroup hw))

theorem closure_Lom_insert_Eom [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) {u u' w : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) (hw : polar Q u' w = 0)
    (hQw : Q w ≠ 0) :
    Subgroup.closure ((Lom Q u : Set (Gom Q)) ∪ {Eom Q u' w}) = ⊤ :=
  closure_subgroupOf_insert_eq_top (elementaryGroup Q) (rootGroup Q u)
    (rootGroup_le_elementaryGroup Q u) _ (eichler_mem_elementaryGroup Q u' w)
    (rootGroup_sup_zpowers_eichler hQ hu hu' huu' hw hQw)

theorem Gom.ext' {g h : Gom Q} (H : ∀ x, g.app x = h.app x) : g = h :=
  Subtype.ext (LinearEquiv.ext H)

theorem exists_gom_pair (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q} (h : P.Orth P')
    {a a' b b' : V} (ha : Q a = 0) (ha' : Q a' = 0) (hb : Q b = 0) (hb' : Q b' = 0)
    (haa' : polar Q a a' = 1) (hbb' : polar Q b b' = 1) :
    ∃ g : Gom Q, g.app a = b ∧ g.app a' = b' := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [polar_zero_left] at haa'; exact zero_ne_one haa'
  have hb0 : b ≠ 0 := by rintro rfl; rw [polar_zero_left] at hbb'; exact zero_ne_one hbb'
  obtain ⟨g₀, hg₀, hg₀a⟩ := exists_mem_elementaryGroup_apply_eq hQ h ha0 hb0 (by rw [ha, hb])
  set g₀' : Gom Q := ⟨g₀, hg₀⟩
  have hx : polar Q b (g₀'.app a') = 1 := by
    rw [← hg₀a]
    exact (polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q hg₀) a a').trans haa'
  have hQx : Q (g₀'.app a') = Q b' := by
    rw [hb', show g₀'.app a' = g₀ a' from rfl,
      map_of_mem (elementaryGroup_le_orthogonalGroup Q hg₀), ha']
  have key := eichler_apply_eq_of_polar_eq hb hQx hx hbb' one_ne_zero
  refine ⟨Eom Q b ((1 : K)⁻¹ • (b' - g₀'.app a')) * g₀', ?_, ?_⟩
  · rw [Gom.app_mul]
    show eichler Q b _ (g₀ a) = b
    rw [hg₀a, eichler_apply_self]
  · rw [Gom.app_mul]
    exact key

theorem HypPair.isCompl_perp (P : HypPair Q) : IsCompl (Submodule.span K {P.e, P.f}) P.perp := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [HypPair.mem_perp] at hxp
    obtain ⟨h1, h2⟩ := hxp
    simp only [polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, P.polar_fe,
      P.polar_ff] at h1 h2
    have ha : a = 0 := by linear_combination h2
    have hb : b = 0 := by linear_combination h1
    rw [ha, hb, zero_smul, zero_smul, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr ⟨polar Q x P.f • P.e + polar Q x P.e • P.f, ?_, P.proj x,
      P.proj_mem_perp x, (P.eq_add_proj x).symm⟩
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem HypPair.polar_eq_zero_of_mem_span_perp (P : HypPair Q) {p w : V}
    (hp : p ∈ Submodule.span K {P.e, P.f}) (hw : w ∈ P.perp) : polar Q p w = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [HypPair.mem_perp] at hw
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hw.1, hw.2]
  ring

section ExtOm

variable {P W : Submodule K V} (hPW : IsCompl P W)

@[expose] noncomputable def extEquiv : (W ≃ₗ[K] W) →* (V ≃ₗ[K] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp
    ((Units.map (extHom hPW)).comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.toMonoidHom)

theorem extEquiv_add (g : W ≃ₗ[K] W) {p w : V} (hp : p ∈ P) (hw : w ∈ W) :
    extEquiv hPW g (p + w) = p + (g ⟨w, hw⟩ : V) :=
  extLin_add hPW _ hp hw

theorem extEquiv_eichler (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) (x y : W) :
    extEquiv hPW (eichler (Q.restrict W) x y) = eichler Q (x : V) (y : V) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_add_eq hPW v
  rw [extEquiv_add hPW _ hp hw]
  by_cases h : Q (x : V) = 0 ∧ polar Q (x : V) (y : V) = 0
  · have hx' : (Q.restrict W) x = 0 := h.1
    have hxy' : polar (Q.restrict W) x y = 0 := by rw [polar_restrict]; exact h.2
    rw [eichler_apply hx' hxy', eichler_apply h.1 h.2]
    have hpx : polar Q p (x : V) = 0 := horth p hp x x.2
    have hpy : polar Q p (y : V) = 0 := horth p hp y y.2
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, polar_add_left, hpx,
      hpy, zero_add]
    have e1 : polar (Q.restrict W) ⟨w, hw⟩ x = polar Q w (x : V) := polar_restrict _ _
    have e2 : polar (Q.restrict W) ⟨w, hw⟩ y = polar Q w (y : V) := polar_restrict _ _
    have e3 : (Q.restrict W) y = Q (y : V) := rfl
    rw [e1, e2, e3]
    module
  · have h' : ¬((Q.restrict W) x = 0 ∧ polar (Q.restrict W) x y = 0) := fun h2 =>
      h ⟨h2.1, by rw [← polar_restrict]; exact h2.2⟩
    rw [eichler_of_not h', eichler_of_not h]
    rfl

theorem extEquiv_mem_elementaryGroup (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0)
    {g : W ≃ₗ[K] W} (hg : g ∈ elementaryGroup (Q.restrict W)) :
    extEquiv hPW g ∈ elementaryGroup Q := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, w, -, -, rfl⟩ := hg
    rw [extEquiv_eichler hPW horth]
    exact eichler_mem_elementaryGroup Q _ _
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

@[expose] noncomputable def extId (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) :
    Gom (Q.restrict W) →* Gom Q :=
  ((extEquiv hPW).comp (elementaryGroup (Q.restrict W)).subtype).codRestrict (elementaryGroup Q)
    (fun g => extEquiv_mem_elementaryGroup hPW horth g.2)

theorem extId_app (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) (g' : Gom (Q.restrict W))
    {p w : V} (hp : p ∈ P) (hw : w ∈ W) :
    (extId hPW horth g').app (p + w) = p + (g'.app ⟨w, hw⟩ : V) :=
  extEquiv_add hPW _ hp hw

theorem extId_Eom (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) (x y : W) :
    extId hPW horth (Eom (Q.restrict W) x y) = Eom Q (x : V) (y : V) :=
  Subtype.ext (extEquiv_eichler hPW horth x y)

theorem extId_mem_Lom (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) (x : W) {g : Gom (Q.restrict W)}
    (hg : g ∈ Lom (Q.restrict W) x) : extId hPW horth g ∈ Lom Q (x : V) := by
  obtain ⟨y, hy, hgy⟩ := mem_rootGroup.mp hg
  have hg' : g = Eom (Q.restrict W) x y := Subtype.ext hgy.symm
  rw [hg', extId_Eom hPW horth]
  exact Eom_mem_Lom (by rw [← polar_restrict]; exact hy)

theorem extId_app_of_mem (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) (g : Gom (Q.restrict W))
    {p : V} (hp : p ∈ P) : (extId hPW horth g).app p = p := by
  have := extId_app hPW horth g hp W.zero_mem
  have h0 : g.app ⟨0, W.zero_mem⟩ = 0 := by
    show ((g : W ≃ₗ[K] W) ⟨0, W.zero_mem⟩) = 0
    exact map_zero (g : W ≃ₗ[K] W)
  rw [h0] at this
  simpa using this

end ExtOm

theorem smul_mem_fixedSub_Lom {M : Type*} [AddCommGroup M] [DistribMulAction (Gom Q) M]
    {x : Gom Q} {v : V} (hx : x.app v = v) {a : M}
    (ha : a ∈ fixedSub M (Lom Q v : Set (Gom Q))) :
    x • a ∈ fixedSub M (Lom Q v : Set (Gom Q)) := by
  intro l hl
  have hxv : x⁻¹.app v = v := by
    have := Gom.app_inv_app x v
    rwa [hx] at this
  have hconj : x⁻¹ * l * x⁻¹⁻¹ ∈ Lom Q v := by
    have := conj_mem_Lom x⁻¹ hl
    rwa [hxv] at this
  calc l • x • a = x • (x⁻¹ * l * x⁻¹⁻¹) • a := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
    _ = x • a := by rw [ha _ hconj]

universe uK uV uM

section Step

variable {K : Type uK} [Field K] [Finite K] [CharP K 2] {V : Type uV} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

theorem omega_step (hQ : (polarBilin Q).Nondegenerate) (Ph : HypPair Q) (x₁ x₁' w : Ph.perp)
    (hx₁ : Q (x₁ : V) = 0) (hx₁' : Q (x₁' : V) = 0) (hxx : polar Q (x₁ : V) (x₁' : V) = 1)
    (hw₁ : polar Q (x₁ : V) (w : V) = 0) (hw₂ : polar Q (x₁' : V) (w : V) = 0)
    (hQw : Q (w : V) ≠ 0) {e : ℕ}
    (hIH : ∀ (M' : Type uM) [AddCommGroup M'] [Finite M'], (∀ x : M', x + x = 0) →
      ∀ [DistribMulAction (Gom (Q.restrict Ph.perp)) M'],
      IsCompl (fixedSub M' (Lom (Q.restrict Ph.perp) x₁ : Set (Gom (Q.restrict Ph.perp))))
        (fixedSub M' (Lom (Q.restrict Ph.perp) x₁' : Set (Gom (Q.restrict Ph.perp)))) →
      ∃ n : ℕ, Nat.card M' = Nat.card K ^ (e * n))
    {M : Type uM} [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0)
    [DistribMulAction (Gom Q) M]
    (hdec : IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q)))
      (fixedSub M (Lom Q Ph.f : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 * e * n) := by
  have hPW := Ph.isCompl_perp
  have horth : ∀ p ∈ Submodule.span K {Ph.e, Ph.f}, ∀ w ∈ Ph.perp, polar Q p w = 0 :=
    fun p hp w hw => Ph.polar_eq_zero_of_mem_span_perp hp hw
  set π := extId hPW horth with hπ
  have hperp : ∀ y : Ph.perp, polar Q Ph.e (y : V) = 0 ∧ polar Q Ph.f (y : V) = 0 :=
    fun y => HypPair.mem_perp.mp y.2
  let Ph' : HypPair Q := ⟨x₁, x₁', hx₁, hx₁', hxx⟩
  have hOrth : Ph.Orth Ph' :=
    ⟨(hperp x₁).1, (hperp x₁').1, (hperp x₁).2, (hperp x₁').2⟩
  have hxx' : polar Q (x₁' : V) (x₁ : V) = 1 := by rw [polar_comm, hxx]
  obtain ⟨g₁, hg₁u, hg₁f⟩ := exists_gom_pair hQ hOrth Ph.Q_e Ph.Q_f hx₁ hx₁' Ph.polar_ef hxx
  obtain ⟨g₂, hg₂, -⟩ := exists_gom_pair hQ hOrth hx₁ hx₁' hx₁' hx₁ hxx hxx'
  obtain ⟨g₃, hg₃, -⟩ := exists_gom_pair hQ hOrth Ph.Q_e Ph.Q_f Ph.Q_f Ph.Q_e Ph.polar_ef
    Ph.polar_fe
  have hdecP : IsCompl (fixedSub M (Lom Q (x₁ : V) : Set (Gom Q)))
      (fixedSub M (Lom Q (x₁' : V) : Set (Gom Q))) := by
    have := isCompl_fixedSub_conj g₁ hdec
    rwa [image_conj_Lom g₁ Ph.e, image_conj_Lom g₁ Ph.f, hg₁u, hg₁f] at this
  have hcardP : Nat.card (fixedSub M (Lom Q (x₁ : V) : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q (x₁' : V) : Set (Gom Q))) := by
    have := card_fixedSub_Lom (M := M) g₂ (x₁ : V)
    rw [hg₂] at this
    exact this.symm
  have hcardu : Nat.card (fixedSub M (Lom Q Ph.f : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q Ph.e : Set (Gom Q))) := by
    have := card_fixedSub_Lom (M := M) g₃ Ph.e
    rwa [hg₃] at this
  have hgen₁ := closure_Lom_insert_Eom hQ hx₁' hx₁ (by rw [hxx']; exact one_ne_zero) hw₁ hQw
  have hgen₂ := closure_Lom_insert_Eom hQ hx₁ hx₁' (by rw [hxx]; exact one_ne_zero) hw₂ hQw
  have hpol : ∀ (y z : Ph.perp), polar (Q.restrict Ph.perp) y z = polar Q (y : V) (z : V) :=
    fun y z => polar_restrict y z
  have hau : (Eom Q (x₁ : V) (w : V)).app Ph.e = Ph.e :=
    eichler_apply_of_polar_eq_zero (hperp x₁).1 (hperp w).1
  have hcu : (Eom Q (x₁' : V) (w : V)).app Ph.e = Ph.e :=
    eichler_apply_of_polar_eq_zero (hperp x₁').1 (hperp w).1
  obtain ⟨hsup, hinf⟩ := step_decomp h2 (P₁ := Lom Q (x₁ : V)) (P₂ := Lom Q (x₁' : V))
    (a := Eom Q (x₁ : V) (w : V)) (c := Eom Q (x₁' : V) (w : V)) (Eom_mem_Lom hw₁)
    (Eom_mem_Lom hw₂) (Eom_mul_self hw₁) (Eom_mul_self hw₂) hgen₁ hgen₂ hdecP hcardP
    (E₁ := π '' (Lom (Q.restrict Ph.perp) x₁ : Set (Gom (Q.restrict Ph.perp))))
    (E₂ := π '' (Lom (Q.restrict Ph.perp) x₁' : Set (Gom (Q.restrict Ph.perp))))
    ⟨Eom (Q.restrict Ph.perp) x₁ w, Eom_mem_Lom (by rw [hpol]; exact hw₁),
      extId_Eom hPW horth x₁ w⟩
    (by rintro _ ⟨g, hg, rfl⟩; exact extId_mem_Lom hPW horth x₁ hg)
    ⟨Eom (Q.restrict Ph.perp) x₁' w, Eom_mem_Lom (by rw [hpol]; exact hw₂),
      extId_Eom hPW horth x₁' w⟩
    (by rintro _ ⟨g, hg, rfl⟩; exact extId_mem_Lom hPW horth x₁' hg)
    (W := fixedSub M (Lom Q Ph.e : Set (Gom Q)))
    (fun w hw => smul_mem_fixedSub_Lom hau hw)
    (fun w hw => smul_mem_fixedSub_Lom hcu hw)
  have hW : ∀ (g' : Gom (Q.restrict Ph.perp)) (w : M),
      w ∈ fixedSub M (Lom Q Ph.e : Set (Gom Q)) →
        π g' • w ∈ fixedSub M (Lom Q Ph.e : Set (Gom Q)) := fun g' w hw =>
    smul_mem_fixedSub_Lom (extId_app_of_mem hPW horth g' (Submodule.subset_span (by simp))) hw
  letI inst : DistribMulAction (Gom (Q.restrict Ph.perp))
      (fixedSub M (Lom Q Ph.e : Set (Gom Q))) :=
    restrictAction π (fixedSub M (Lom Q Ph.e : Set (Gom Q))) hW
  have hdec' := isCompl_fixedSub_restrict π (fixedSub M (Lom Q Ph.e : Set (Gom Q))) hW
    (Lom (Q.restrict Ph.perp) x₁ : Set (Gom (Q.restrict Ph.perp)))
    (Lom (Q.restrict Ph.perp) x₁' : Set (Gom (Q.restrict Ph.perp))) hsup hinf
  have h2' : ∀ x : fixedSub M (Lom Q Ph.e : Set (Gom Q)), x + x = 0 := fun x =>
    Subtype.ext (h2 x)
  obtain ⟨n, hn⟩ := hIH (fixedSub M (Lom Q Ph.e : Set (Gom Q))) h2' hdec'
  refine ⟨n, ?_⟩
  have hsq := card_eq_sq (M := M) hdec.symm hcardu
  rw [hsq, hn, ← pow_mul]
  congr 1
  ring

end Step

end CFSG.ClassicalGroups.Orthogonal
