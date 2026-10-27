module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightRadicalMeet

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒟₁" => ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
local notation "𝐛₁" => ptB₁ hzC hz hb φ he
local notation "λ₁" => ptLin hzC hsup hinf hz hb hnd hV φ he halt
local notation "sE" => OddQuadraticFive.sE

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_eq_ptGr_mul {w : 𝔼} (hw : ptQuad e w = 0) :
    pt₁ hzC hz hb φ he ((w, 0), 0) = ptGr hzC hz hb φ he w * ptGr hzC hz hb φ he 0 := by
  rw [ptGr, ptGr, ← map_mul, ← ofAdd_add, grV, grV, hw, QuadraticMap.map_zero, Prod.mk_add_mk,
    Prod.mk_add_mk, add_zero, add_zero, add_self_eq_zero_zmod_two]

theorem ptLin_fix_of_comm (m : 𝒩₁) {w : 𝔼} (hw : ptQuad e w = 0)
    (hcomm : (m : G) * pt₁ hzC hz hb φ he ((w, 0), 0) = pt₁ hzC hz hb φ he ((w, 0), 0) * m) :
    sE (λ₁ m) w = w := by
  set ρ := ptAct hzC hsup hinf hz hb hnd hV φ he halt with hρ
  have h1 : (m : G) * pt₁ hzC hz hb φ he ((w, 0), 0) * (m : G)⁻¹ =
      pt₁ hzC hz hb φ he ((w, 0), 0) := by
    rw [hcomm, mul_inv_cancel_right]
  have h2 : (m : G) * pt₁ hzC hz hb φ he ((w, 0), 0) * (m : G)⁻¹ =
      pt₁ hzC hz hb φ he (grV (ptQuad e) (ρ m w) + grV (ptQuad e) (ρ m 0)) := by
    rw [pt₁_eq_ptGr_mul hzC hz hb φ he hw,
      show (m : G) * (ptGr hzC hz hb φ he w * ptGr hzC hz hb φ he 0) * (m : G)⁻¹ =
        ((m : G) * ptGr hzC hz hb φ he w * (m : G)⁻¹) *
          ((m : G) * ptGr hzC hz hb φ he 0 * (m : G)⁻¹) by group,
      ← ptGr_ptAct hzC hsup hinf hz hb hnd hV φ he halt,
      ← ptGr_ptAct hzC hsup hinf hz hb hnd hV φ he halt, pt₁_add]
  rw [h2] at h1
  have h3 := congrArg (fun x : (𝔼 × ZMod 2) × ZMod 2 => x.1.1)
    (pt₁_injective hzC hinf hz hb φ he h1)
  simp only [grV, Prod.fst_add] at h3
  rw [hρ, ptLin_spec hzC hsup hinf hz hb hnd hV φ he halt m w, add_assoc,
    add_self_eq_zero_zmod_two, add_zero] at h3
  exact h3

abbrev triple (s : bilinIsometryGroup (b.restrict 𝔼)) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (b (sE s (ptF₂ he)) (ptF₂ he), b (sE s (ptF₂ he)) (ptF₃ he), b (sE s (ptF₃ he)) (ptF₃ he))

include hzC hsup hinf hz hb hnd hV he halt in
theorem mul_comm_of_mem_D₂_radA {d a : G} (hd : d ∈ 𝒟) (ha : a ∈ 𝒜) : d * a = a * d := by
  obtain ⟨ν, -, -, -, hν4, -, -, -⟩ :=
    translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  obtain ⟨B, rfl⟩ := (mem_A_iff hzC hinf hz φ he).1 ha
  have h := hν4 ⟨d, hd⟩ B 0
  rw [zero_smul, add_zero] at h
  calc d * ((θ₂).symm (Multiplicative.ofAdd (B, 0)) : G) =
      d * ((d : G)⁻¹ * (θ₂).symm (Multiplicative.ofAdd (B, 0)) * d) := by
        rw [show (d : G) = ((⟨d, hd⟩ : 𝒟) : G) from rfl, h]
    _ = _ := by group

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptQuad_ptE₃ : ptQuad e (ptE₃ he) = 0 := by
  rw [ptQuad_apply]
  simp

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_e₂_mem_radA : pt₁ hzC hz hb φ he ((ptE₂ he, 0), 0) ∈ 𝒜 := by
  rw [pt₁, ptHom_pt]
  exact ptE_mem_radA he hb φ

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_e₃_mem_radA : pt₁ hzC hz hb φ he ((ptE₃ he, 0), 0) ∈ 𝒜 := by
  rw [pt₁, ptHom_pt]
  refine mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq]
  exact pointElt_mem_pointwiseStabilizer he hb (mem_pairOrth_inl_two he)
    (Submodule.subset_span ⟨2, rfl⟩) _

theorem ptLin_fix_of_centralizes (m : 𝒩₁) (hm : ∀ a ∈ 𝒜, (m : G) * a = a * m) :
    sE (λ₁ m) (ptE₂ he) = ptE₂ he ∧ sE (λ₁ m) (ptE₃ he) = ptE₃ he :=
  ⟨ptLin_fix_of_comm hzC hsup hinf hz hb hnd hV φ he halt m (ptQuad_ptE₂ he)
      (hm _ (pt₁_e₂_mem_radA hzC hz hb φ he)),
    ptLin_fix_of_comm hzC hsup hinf hz hb hnd hV φ he halt m (ptQuad_ptE₃ he)
      (hm _ (pt₁_e₃_mem_radA hzC hz hb φ he))⟩

abbrev ptLinA : 𝒜 →* bilinIsometryGroup (b.restrict 𝔼) :=
  (λ₁).comp (inclusion fun _ ha => (mem_inf.1 (radA_le_stab hzC hb hnd φ he ha)).1)

theorem ker_ptLinA : (ptLinA hzC hsup hinf hz hb hnd hV φ he halt).ker =
    (𝒜₁ ⊓ 𝒜).subgroupOf 𝒜 := by
  ext a
  rw [MonoidHom.mem_ker, mem_subgroupOf, ← radA_inf_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt]
  change λ₁ _ = 1 ↔ _
  rw [← mem_ptD₁_iff_ptLin]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

omit [Finite G] in
include hb hnd hV he in
theorem card_radA : Nat.card 𝒜 = 64 :=
  (pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf).2.1

theorem card_range_ptLinA : Nat.card (ptLinA hzC hsup hinf hz hb hnd hV φ he halt).range = 8 := by
  have h1 := (ptLinA hzC hsup hinf hz hb hnd hV φ he halt).ker.card_mul_index
  rw [Subgroup.index_ker, ker_ptLinA,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : 𝒜₁ ⊓ 𝒜 ≤ 𝒜)).toEquiv,
    card_J hb φ he, card_radA hb hnd hV φ he] at h1
  omega

theorem exists_radA_triple (t : ZMod 2 × ZMod 2 × ZMod 2) :
    ∃ a : 𝒜, triple he (ptLinA hzC hsup hinf hz hb hnd hV φ he halt a) = t := by
  have hcomm : ∀ x ∈ 𝒜, ∀ y ∈ 𝒜, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian (pullSub_radical hb hnd hV φ
      (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf).1 hx hy
  have hfix : ∀ a : 𝒜, sE (ptLinA hzC hsup hinf hz hb hnd hV φ he halt a) (ptE₂ he) = ptE₂ he ∧
      sE (ptLinA hzC hsup hinf hz hb hnd hV φ he halt a) (ptE₃ he) = ptE₃ he := fun a =>
    ptLin_fix_of_centralizes hzC hsup hinf hz hb hnd hV φ he halt _ fun x hx => hcomm _ a.2 _ hx
  set f : (ptLinA hzC hsup hinf hz hb hnd hV φ he halt).range → ZMod 2 × ZMod 2 × ZMod 2 :=
    fun s => triple he s with hf
  have hinj : Function.Injective f := by
    rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨a', rfl⟩⟩ h
    apply Subtype.ext
    obtain ⟨h1, h2⟩ := hfix a
    obtain ⟨h1', h2'⟩ := hfix a'
    have h3 := congrArg Prod.fst h
    have h4 := congrArg (fun p => p.2.1) h
    have h5 := congrArg (fun p => p.2.2) h
    exact eq_of_fix hb he h1 h2 h1' h2' h3 h4 h5
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [card_range_ptLinA, Nat.card_prod, Nat.card_prod, Nat.card_zmod])
  obtain ⟨⟨_, ⟨a, rfl⟩⟩, ha⟩ := hbij.2 t
  exact ⟨a, ha⟩

theorem exists_radA_inv_mul_mem_ptD₁ {c : G} (hcD : c ∈ 𝒟) (hcN : c ∈ 𝒩₁) :
    ∃ a ∈ 𝒜, a⁻¹ * c ∈ 𝒟₁ := by
  have hfix := ptLin_fix_of_centralizes hzC hsup hinf hz hb hnd hV φ he halt ⟨c, hcN⟩
    fun a ha => mul_comm_of_mem_D₂_radA hzC hsup hinf hz hb hnd hV φ he halt hcD ha
  obtain ⟨a, ha⟩ := exists_radA_triple hzC hsup hinf hz hb hnd hV φ he halt
    (triple he (λ₁ ⟨c, hcN⟩))
  have hfixa := ptLin_fix_of_centralizes hzC hsup hinf hz hb hnd hV φ he halt
    ⟨a, (mem_inf.1 (radA_le_stab hzC hb hnd φ he a.2)).1⟩ fun x hx =>
      mul_comm_of_isElementaryAbelian (pullSub_radical hb hnd hV φ
        (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf).1 a.2 hx
  have heq : λ₁ ⟨a, (mem_inf.1 (radA_le_stab hzC hb hnd φ he a.2)).1⟩ = λ₁ ⟨c, hcN⟩ :=
    eq_of_fix hb he hfixa.1 hfixa.2 hfix.1 hfix.2 (congrArg Prod.fst ha)
      (congrArg (fun p => p.2.1) ha) (congrArg (fun p => p.2.2) ha)
  refine ⟨a, a.2, ?_⟩
  have hmem := (mem_ptD₁_iff_ptLin hzC hsup hinf hz hb hnd hV φ he halt
    (⟨a, (mem_inf.1 (radA_le_stab hzC hb hnd φ he a.2)).1⟩⁻¹ * ⟨c, hcN⟩)).2 (by
      rw [map_mul, map_inv, heq, inv_mul_cancel])
  exact hmem

include hzC hsup hinf hz hb hnd hV he halt in
theorem comm_mem_radI {d : G} (hd : d ∈ 𝒟) :
    z⁻¹ * d⁻¹ * z * d ∈ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym := by
  obtain ⟨ν, hν1, -⟩ := translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  have h := hν1 ⟨d, hd⟩
  exact (BinarySymThreeOrbit.mem_layerSub θ₂).2 ⟨_, (Multiplicative.toAdd (ν ⟨d, hd⟩)).2, h⟩

include hzC hsup hinf hz hb hnd hV he halt in
theorem sq_mem_radI {d : G} (hd : d ∈ 𝒟) :
    d * d ∈ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym := by
  obtain ⟨-, -, -, -, -, -, -, hsq⟩ :=
    translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  rw [← hsq, ← sq]
  exact Subgroup.subset_closure ⟨d, hd, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hzC hinf hz he in
theorem radI_le_radA : BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym ≤ 𝒜 :=
  (BinarySymThreeOrbit.layerSub_mono θ₂ le_top).trans (layerSub_top_eq hzC hinf hz φ he).le

include hzC hsup hinf hz hb hnd hV he halt in
theorem comm_mul_of_mem_D₂ {d d' : G} (hd : d ∈ 𝒟) (hd' : d' ∈ 𝒟) :
    z⁻¹ * (d * d')⁻¹ * z * (d * d') = (z⁻¹ * d⁻¹ * z * d) * (z⁻¹ * d'⁻¹ * z * d') := by
  set x := z⁻¹ * d⁻¹ * z * d with hx
  set x' := z⁻¹ * d'⁻¹ * z * d' with hx'
  have hxA : x ∈ 𝒜 := radI_le_radA hzC hinf hz φ he
    (comm_mem_radI hzC hsup hinf hz hb hnd hV φ he halt hd)
  have hx'A : x' ∈ 𝒜 := radI_le_radA hzC hinf hz φ he
    (comm_mem_radI hzC hsup hinf hz hb hnd hV φ he halt hd')
  have hc := mul_comm_of_mem_D₂_radA hzC hsup hinf hz hb hnd hV φ he halt hd' hxA
  have hab := mul_comm_of_isElementaryAbelian (pullSub_radical hb hnd hV φ
    (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf).1 hxA hx'A
  have h1 : d⁻¹ * z * d = z * x := by rw [hx]; group
  calc z⁻¹ * (d * d')⁻¹ * z * (d * d') = z⁻¹ * (d'⁻¹ * (d⁻¹ * z * d) * d') := by group
    _ = z⁻¹ * (d'⁻¹ * z * (d' * x)) := by
      rw [h1, show d'⁻¹ * (z * x) * d' = d'⁻¹ * z * (x * d') by group, ← hc]
    _ = x' * x := by rw [hx']; group
    _ = x * x' := hab.symm

theorem exists_mem_ptD₁_comm_eq {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂lab : ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C₂,
      z⁻¹ * c⁻¹ * z * c = (θ₂).symm (Multiplicative.ofAdd (B, 0))) (x x' : ZMod 2) :
    ∃ k ∈ C₂ ⊓ 𝒟₁, z⁻¹ * k⁻¹ * z * k = tauHom φ he (Multiplicative.ofAdd (jSym 0 x x')) := by
  obtain ⟨c, hc, hcl⟩ := hC₂lab _ (jSym_mem_altSym x x')
  rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one] at hcl
  have hcN : c ∈ 𝒩₁ := (mem_ptN_iff_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt
    (hC₂D hc)).2 (hcl ▸ tauHom_jSym_mem_ptA hb φ he 0 x x')
  obtain ⟨a, ha, haD⟩ := exists_radA_inv_mul_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
    (hC₂D hc) hcN
  have haC₂ : a ∈ C₂ := by
    rw [← hC₂R] at ha
    exact (mem_inf.1 ha).1
  refine ⟨a⁻¹ * c, mem_inf.2 ⟨mul_mem (inv_mem haC₂) hc, haD⟩, ?_⟩
  have hza : a * z = z * a := RadicalLabels.mul_comm_z hzC (pullSub_le φ _ ha)
  rw [← hcl]
  calc z⁻¹ * (a⁻¹ * c)⁻¹ * z * (a⁻¹ * c) = z⁻¹ * c⁻¹ * (a * z) * a⁻¹ * c := by group
    _ = z⁻¹ * c⁻¹ * z * c := by rw [hza]; group

theorem inf_ptD₁_le {C₁ C₂ : Subgroup G} (hC₁N : ∀ g ∈ 𝒩₁, ∀ c ∈ C₁, g * c * g⁻¹ ∈ C₁)
    (hC₁z : ((zpowers z : Set G) * (C₁ : Set G)) = 𝒟₁)
    (hkey : ∀ x ∈ 𝒟₁, x ∉ C₁ → ∀ f ∈ C₁, x⁻¹ * f⁻¹ * x * f ∈ zpowers 𝐛₁ → f ∈ 𝒜₁)
    (hC₂D : C₂ ≤ 𝒟) (hC₂ab : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂lab : ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C₂,
      z⁻¹ * c⁻¹ * z * c = (θ₂).symm (Multiplicative.ofAdd (B, 0))) :
    C₂ ⊓ 𝒟₁ ≤ C₁ := by
  intro x hx
  by_contra hxC
  have hzN : z ∈ 𝒩₁ := le_normalizer (mem_sup_right (mem_zpowers z))
  have hF : ∀ f ∈ C₂ ⊓ 𝒟₁, f ∈ C₁ → z⁻¹ * f⁻¹ * z * f = 1 := by
    intro f hf hfC
    have hcomm : x⁻¹ * f⁻¹ * x * f = 1 := by
      rw [show x⁻¹ * f⁻¹ * x * f = x⁻¹ * f⁻¹ * (x * f) by group, hC₂ab x hx.1 f hf.1]
      group
    have hfA := hkey x hx.2 hxC f hfC (hcomm ▸ one_mem _)
    have hfz : f * z = z * f := RadicalLabels.mul_comm_z hzC (pullSub_le φ _ hfA)
    rw [show z⁻¹ * f⁻¹ * z * f = z⁻¹ * f⁻¹ * (z * f) by group, ← hfz]
    group
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz, sq] at h
  have hout : ∀ y ∈ 𝒟₁, y ∉ C₁ → ∃ c ∈ C₁, y = z * c := by
    intro y hy hyC
    have hy' : y ∈ (𝒟₁ : Set G) := hy
    rw [← hC₁z] at hy'
    obtain ⟨t, ht, c, hc, rfl⟩ := hy'
    rcases eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
    · exact absurd (show (1 : G) * c ∈ C₁ by rw [one_mul]; exact hc) hyC
    · exact ⟨c, hc, rfl⟩
  have hprod : ∀ y ∈ 𝒟₁, y ∉ C₁ → ∀ y' ∈ 𝒟₁, y' ∉ C₁ → y * y' ∈ C₁ := by
    intro y hy hyC y' hy' hy'C
    obtain ⟨c, hc, rfl⟩ := hout y hy hyC
    obtain ⟨c', hc', rfl⟩ := hout y' hy' hy'C
    have h := hC₁N z hzN c hc
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzi] at h
    rw [show z * c * (z * c') = z * c * z * c' by group]
    exact mul_mem h hc'
  obtain ⟨k₁, hk₁, hk₁c⟩ := exists_mem_ptD₁_comm_eq hzC hsup hinf hz hb hnd hV φ he halt hC₂D
    hC₂R hC₂lab 1 0
  obtain ⟨k₂, hk₂, hk₂c⟩ := exists_mem_ptD₁_comm_eq hzC hsup hinf hz hb hnd hV φ he halt hC₂D
    hC₂R hC₂lab 0 1
  have hne : ∀ x x' : ZMod 2, (x, x') ≠ (0, 0) →
      tauHom φ he (Multiplicative.ofAdd (jSym 0 x x')) ≠ 1 := by
    intro x x' hxx h
    rw [← map_one (tauHom φ he)] at h
    have h1 := ofAdd_eq_one.1 (tauHom_injective φ he h)
    have h2 := jSym_injective (h1.trans (Subtype.ext (by
      change (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = jMat 0 0 0
      decide)))
    exact hxx (Prod.ext h2.2.1 h2.2.2)
  have hk₁C : k₁ ∉ C₁ := fun h => hne 1 0 (by decide) (hk₁c ▸ hF k₁ hk₁ h)
  have hk₂C : k₂ ∉ C₁ := fun h => hne 0 1 (by decide) (hk₂c ▸ hF k₂ hk₂ h)
  have hk₁₂ := hprod k₁ hk₁.2 hk₁C k₂ hk₂.2 hk₂C
  have h12 := hF (k₁ * k₂) (mul_mem hk₁ hk₂) hk₁₂
  rw [comm_mul_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hk₁.1) (hC₂D hk₂.1), hk₁c,
    hk₂c, ← map_mul, ← ofAdd_add, jSym_add] at h12
  exact hne 1 1 (by decide) (by simpa using h12)

abbrev J₀Sub : Subgroup G := 𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym

theorem kSubgroup_structure {C₁ C₂ : Subgroup G} (hC₁D : C₁ ≤ 𝒟₁)
    (hC₁N : ∀ g ∈ 𝒩₁, ∀ c ∈ C₁, g * c * g⁻¹ ∈ C₁)
    (hC₁z : ((zpowers z : Set G) * (C₁ : Set G)) = 𝒟₁) (hC₁B : C₁ ⊓ ptSub φ z hb e = 𝒜₁)
    (hC₁sq : closure {x | ∃ c ∈ C₁, c ^ 2 = x} = zpowers 𝐛₁)
    (hkey : ∀ x ∈ 𝒟₁, x ∉ C₁ → ∀ f ∈ C₁, x⁻¹ * f⁻¹ * x * f ∈ zpowers 𝐛₁ → f ∈ 𝒜₁)
    (hC₂D : C₂ ≤ 𝒟) (hC₂ab : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜)
    (hC₂lab : ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C₂,
      z⁻¹ * c⁻¹ * z * c = (θ₂).symm (Multiplicative.ofAdd (B, 0))) :
    C₁ ⊓ C₂ = C₂ ⊓ 𝒟₁ ∧ IsElementaryAbelian 2 (C₁ ⊓ C₂ : Subgroup G) ∧
      Nat.card (C₁ ⊓ C₂ : Subgroup G) = 32 ∧ (C₁ ⊓ C₂) ⊓ 𝒜 = 𝒜₁ ⊓ 𝒜 ∧
      (fun k => z⁻¹ * k⁻¹ * z * k) '' ((C₁ ⊓ C₂ : Subgroup G) : Set G) =
        (J₀Sub hzC hinf hz hb φ he : Set G) ∧
      conjClass (C₁ ⊓ C₂) z = z • (J₀Sub hzC hinf hz hb φ he : Set G) ∧
      C₂ ⊓ 𝒩₁ = 𝒜 ⊔ (C₁ ⊓ C₂) ∧ Nat.card (C₂ ⊓ 𝒩₁ : Subgroup G) = 256 := by
  have hA₁C₁ : 𝒜₁ ≤ C₁ := hC₁B ▸ inf_le_left
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hD₁N : 𝒟₁ ≤ 𝒩₁ := ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt
  have hle := inf_ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hC₁N hC₁z hkey hC₂D hC₂ab hC₂R
    hC₂lab
  have hK : C₁ ⊓ C₂ = C₂ ⊓ 𝒟₁ := le_antisymm (fun k hk => ⟨hk.2, hC₁D hk.1⟩)
    (fun k hk => ⟨hle hk, hk.1⟩)
  have hcommK : ∀ k ∈ C₁ ⊓ C₂, z⁻¹ * k⁻¹ * z * k ∈ J₀Sub hzC hinf hz hb φ he := by
    intro k hk
    refine ⟨(mem_ptN_iff_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hk.2)).1
      (hD₁N (hC₁D hk.1)), comm_mem_radI hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hk.2)⟩
  have himage : (fun k => z⁻¹ * k⁻¹ * z * k) '' ((C₁ ⊓ C₂ : Subgroup G) : Set G) =
      (J₀Sub hzC hinf hz hb φ he : Set G) := by
    ext j
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hcommK k hk
    · intro hj
      obtain ⟨x, x', rfl⟩ := (mem_J₀_iff hzC hinf hz hb φ he).1 hj
      obtain ⟨k, hk, hkc⟩ := exists_mem_ptD₁_comm_eq hzC hsup hinf hz hb hnd hV φ he halt hC₂D
        hC₂R hC₂lab x x'
      exact ⟨k, hK ▸ hk, hkc⟩
  have hcommHom : ∀ (M : Subgroup G), M ≤ 𝒟 → ∃ κ : M →* G, ∀ m : M,
      κ m = z⁻¹ * (m : G)⁻¹ * z * m := fun M hM =>
    ⟨MonoidHom.mk' (fun m : M => z⁻¹ * (m : G)⁻¹ * z * m) fun m m' => by
      change z⁻¹ * ((m : G) * m')⁻¹ * z * (m * m') = _
      exact comm_mul_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt (hM m.2) (hM m'.2),
      fun m => rfl⟩
  have hker : ∀ c ∈ C₂, z⁻¹ * c⁻¹ * z * c = 1 ↔ c ∈ 𝒜 := by
    intro c hc
    rw [← hC₂z c hc]
    constructor
    · intro h
      have h1 : c⁻¹ * z * c = z := by
        calc c⁻¹ * z * c = z * (z⁻¹ * c⁻¹ * z * c) := by group
          _ = z := by rw [h, mul_one]
      calc c * z = c * (c⁻¹ * z * c) := by rw [h1]
        _ = z * c := by group
    · intro h
      rw [show z⁻¹ * c⁻¹ * z * c = z⁻¹ * c⁻¹ * (z * c) by group, ← h]
      group
  have hKA : (C₁ ⊓ C₂) ⊓ 𝒜 = 𝒜₁ ⊓ 𝒜 := by
    rw [hK, inf_right_comm, inf_comm C₂ 𝒜, inf_of_le_left hAC₂,
      radA_inf_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt]
  have hcardK : Nat.card (C₁ ⊓ C₂ : Subgroup G) = 32 := by
    obtain ⟨κ, hκ⟩ := hcommHom (C₁ ⊓ C₂) fun k hk => hC₂D hk.2
    have hrange : κ.range = J₀Sub hzC hinf hz hb φ he := by
      ext j
      rw [MonoidHom.mem_range, ← SetLike.mem_coe, ← himage]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, k.2, (hκ k).symm⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, hκ _⟩
    have hkerκ : κ.ker = ((C₁ ⊓ C₂) ⊓ 𝒜).subgroupOf (C₁ ⊓ C₂) := by
      ext k
      rw [MonoidHom.mem_ker, hκ, mem_subgroupOf, hker k k.2.2]
      exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
    have h1 := κ.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hkerκ, hKA,
      Nat.card_congr (subgroupOfEquivOfLe (show 𝒜₁ ⊓ 𝒜 ≤ C₁ ⊓ C₂ from
        fun x hx => ⟨hA₁C₁ hx.1, hAC₂ hx.2⟩)).toEquiv, card_J hb φ he,
      card_J₀ hzC hinf hz hb φ he] at h1
    rw [← h1]
  have hKe : IsElementaryAbelian 2 (C₁ ⊓ C₂ : Subgroup G) := by
    refine isElementaryAbelian_of_forall (fun x hx y hy => hC₂ab x hx.2 y hy.2) fun k hk => ?_
    have h1 : k * k ∈ zpowers 𝐛₁ := by
      rw [← hC₁sq, ← sq]
      exact Subgroup.subset_closure ⟨k, hk.1, rfl⟩
    have h2 := sq_mem_radI hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hk.2)
    have h3 : k * k ∈ zpowers 𝐛₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym :=
      ⟨h1, h2⟩
    rw [ptI_inf_radI hzC hinf hz hb φ he, mem_bot] at h3
    exact h3
  have hconj : conjClass (C₁ ⊓ C₂) z = z • (J₀Sub hzC hinf hz hb φ he : Set G) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine Set.mem_smul_set.2 ⟨z⁻¹ * k⁻¹⁻¹ * z * k⁻¹, hcommK k⁻¹ (inv_mem hk), ?_⟩
      rw [smul_eq_mul, inv_inv]
      group
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Set.mem_smul_set.1 hx
      rw [← himage] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [smul_eq_mul, inv_inv]
      group
  have hAN : 𝒜 ≤ 𝒩₁ := fun a ha => (mem_inf.1 (radA_le_stab hzC hb hnd φ he ha)).1
  have hE₀ : C₂ ⊓ 𝒩₁ = 𝒜 ⊔ (C₁ ⊓ C₂) := by
    apply le_antisymm
    · rintro c ⟨hc, hcN⟩
      obtain ⟨a, ha, haD⟩ := exists_radA_inv_mul_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
        (hC₂D hc) hcN
      have hk : a⁻¹ * c ∈ C₁ ⊓ C₂ := by
        rw [hK]
        exact mem_inf.2 ⟨mul_mem (inv_mem (hAC₂ ha)) hc, haD⟩
      rw [show c = a * (a⁻¹ * c) by group]
      exact mul_mem_sup ha hk
    · exact sup_le (le_inf hAC₂ hAN) (le_inf inf_le_right fun k hk => hD₁N (hC₁D hk.1))
  have hcardE : Nat.card (C₂ ⊓ 𝒩₁ : Subgroup G) = 256 := by
    obtain ⟨κ, hκ⟩ := hcommHom (C₂ ⊓ 𝒩₁) fun c hc => hC₂D hc.1
    have hrange : κ.range = J₀Sub hzC hinf hz hb φ he := by
      ext j
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨c, rfl⟩
        rw [hκ]
        exact ⟨(mem_ptN_iff_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt (hC₂D c.2.1)).1 c.2.2,
          comm_mem_radI hzC hsup hinf hz hb hnd hV φ he halt (hC₂D c.2.1)⟩
      · intro hj
        rw [← SetLike.mem_coe, ← himage] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        exact ⟨⟨k, hk.2, hD₁N (hC₁D hk.1)⟩, hκ _⟩
    have hkerκ : κ.ker = (𝒜).subgroupOf (C₂ ⊓ 𝒩₁) := by
      ext c
      rw [MonoidHom.mem_ker, hκ, mem_subgroupOf, hker c c.2.1]
    have h1 := κ.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hkerκ,
      Nat.card_congr (subgroupOfEquivOfLe (le_inf hAC₂ hAN)).toEquiv,
      card_radA hb hnd hV φ he, card_J₀ hzC hinf hz hb φ he] at h1
    rw [← h1]
  exact ⟨hK, hKe, hcardK, hKA, himage, hconj, hE₀, hcardE⟩

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
