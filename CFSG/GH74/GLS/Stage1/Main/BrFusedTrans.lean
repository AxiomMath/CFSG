module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedCtx
public import CFSG.GH74.GLS.Stage1.Main.BrFusedAbs
public import CFSG.GH74.GLS.Stage1.Main.BrModel

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Trans

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {Gs : Type} [Group Gs]
  [Finite Gs] {p f : ℕ}

abbrev FusedCtx.X (C : FusedCtx z S ε Gs p f) : Subgroup Gs :=
  layerTimesSylow C.z₁ (C.S₁ : Subgroup Gs)

variable (C : FusedCtx z S ε Gs p f)

omit [Finite G] [Finite Gs] in
theorem FusedCtx.X_eq : C.X = C.E₁ ⊔ C.E₂ ⊔ (C.S₁ : Subgroup Gs) := by
  unfold FusedCtx.X layerTimesSylow
  show IVK.Ez C.z₁ ⊔ _ = _
  rw [C.pkg.layer]

omit [Finite G] [Finite Gs] in
theorem FusedCtx.E₁_le_X : C.E₁ ≤ C.X := by
  rw [C.X_eq]; exact le_sup_left.trans le_sup_left

omit [Finite G] [Finite Gs] in
theorem FusedCtx.E₂_le_X : C.E₂ ≤ C.X := by
  rw [C.X_eq]; exact le_sup_right.trans le_sup_left

omit [Finite G] [Finite Gs] in
theorem FusedCtx.S₁_le_X : (C.S₁ : Subgroup Gs) ≤ C.X := by
  rw [C.X_eq]; exact le_sup_right

omit [Finite G] [Finite Gs] in
theorem FusedCtx.E_le_X : C.E₁ ⊔ C.E₂ ≤ C.X := sup_le C.E₁_le_X C.E₂_le_X

@[expose] noncomputable def FusedCtx.emb : ↥C.X →* CentralizerBar z :=
  (Stage1.Thm3.Sec8.layerSBar z S).subtype.comp C.Ψ.symm.toMonoidHom

omit [Finite G] [Finite Gs] in
theorem FusedCtx.emb_injective : Function.Injective C.emb :=
  Subtype.coe_injective.comp C.Ψ.symm.injective

@[expose] noncomputable def FusedCtx.pull (K : Subgroup Gs) : Subgroup (CentralizerBar z) :=
  (K.subgroupOf C.X).map C.emb

omit [Finite G] [Finite Gs] in
theorem FusedCtx.mem_pull_iff (K : Subgroup Gs) (y : CentralizerBar z) :
    y ∈ C.pull K ↔ ∃ hy : y ∈ Stage1.Thm3.Sec8.layerSBar z S,
      ((C.Ψ ⟨y, hy⟩ : ↥C.X) : Gs) ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(C.Ψ.symm x).2, ?_⟩
    have : (⟨(C.emb x : CentralizerBar z), (C.Ψ.symm x).2⟩ : ↥(Stage1.Thm3.Sec8.layerSBar z S)) =
        C.Ψ.symm x := rfl
    rw [this, MulEquiv.apply_symm_apply]
    exact hx
  · rintro ⟨hy, hyK⟩
    refine ⟨C.Ψ ⟨y, hy⟩, hyK, ?_⟩
    show ((C.Ψ.symm (C.Ψ ⟨y, hy⟩) : ↥(Stage1.Thm3.Sec8.layerSBar z S)) : CentralizerBar z) = y
    rw [MulEquiv.symm_apply_apply]

omit [Finite G] [Finite Gs] in
theorem FusedCtx.perfect_E₁ : Group.IsPerfect ↥(C.E₁.subgroupOf C.X) :=
  haveI : Group.IsPerfect ↥C.E₁ := C.pkg.data.comps.quasi₁.1
  Group.IsPerfect.ofSurjective (G := ↥C.E₁) (G' := ↥(C.E₁.subgroupOf C.X))
    (f := (Subgroup.subgroupOfEquivOfLe C.E₁_le_X).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe C.E₁_le_X).symm.surjective

omit [Finite G] [Finite Gs] in
theorem FusedCtx.perfect_E₂ : Group.IsPerfect ↥(C.E₂.subgroupOf C.X) :=
  haveI : Group.IsPerfect ↥C.E₂ := C.pkg.data.comps.quasi₂.1
  Group.IsPerfect.ofSurjective (G := ↥C.E₂) (G' := ↥(C.E₂.subgroupOf C.X))
    (f := (Subgroup.subgroupOfEquivOfLe C.E₂_le_X).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe C.E₂_le_X).symm.surjective

omit [Finite G] [Finite Gs] in
theorem FusedCtx.S₁_le_Cen : (C.S₁ : Subgroup Gs) ≤ centralizer ({C.z₁} : Set Gs) := fun s hs =>
  Subgroup.mem_centralizer_singleton_iff.mpr ((comm_of_center C.pkg.data.syl.z_cen).2 s hs)

omit [Finite G] [Finite Gs] in
theorem FusedCtx.X_le_Cen : C.X ≤ centralizer ({C.z₁} : Set Gs) :=
  layerTimesSylow_le_Cen C.S₁_le_Cen

omit [Finite G] [Finite Gs] in
theorem FusedCtx.normal_E : ((C.E₁ ⊔ C.E₂).subgroupOf C.X).Normal := by
  constructor
  intro n hn g
  have hn' : (n : Gs) ∈ C.E₁ ⊔ C.E₂ := hn
  have hg : (g : Gs) ∈ centralizer ({C.z₁} : Set Gs) := C.X_le_Cen g.2
  have h1 : (n : Gs) ∈ IVK.Ez C.z₁ := by rw [C.pkg.layer]; exact hn'
  have := Ez_conj_mem hg h1
  rw [C.pkg.layer] at this
  exact this

omit [Finite G] in
theorem FusedCtx.oRes_X : oResidual 2 ↥C.X = (C.E₁ ⊔ C.E₂).subgroupOf C.X := by
  have hT : IsPGroup 2 ↥(((C.S₁ : Subgroup Gs)).subgroupOf C.X) :=
    C.S₁.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe C.S₁_le_X).symm
  have hY : C.E₁.subgroupOf C.X ⊔ C.E₂.subgroupOf C.X ⊔ (C.S₁ : Subgroup Gs).subgroupOf C.X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup C.E₁_le_X C.E₂_le_X,
      ← Subgroup.subgroupOf_sup C.E_le_X C.S₁_le_X, ← C.X_eq]
    exact Subgroup.subgroupOf_self _
  have hN : (C.E₁.subgroupOf C.X ⊔ C.E₂.subgroupOf C.X).Normal := by
    rw [← Subgroup.subgroupOf_sup C.E₁_le_X C.E₂_le_X]
    exact C.normal_E
  rw [oResidual_two_eq C.perfect_E₁ C.perfect_E₂ hN hT hY,
    ← Subgroup.subgroupOf_sup C.E₁_le_X C.E₂_le_X]

omit [Finite G] [Finite Gs] in
theorem FusedCtx.pull_sup {K K' : Subgroup Gs} (hK : K ≤ C.X) (hK' : K' ≤ C.X) :
    C.pull (K ⊔ K') = C.pull K ⊔ C.pull K' := by
  unfold FusedCtx.pull
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

omit [Finite G] in
theorem FusedCtx.comps_X :
    {K : Subgroup ↥C.X | IsComponent K} = {C.E₁.subgroupOf C.X, C.E₂.subgroupOf C.X} := by
  have hcomp := C.pkg.data.comps
  have hT : IsPGroup 2 ↥((C.S₁ : Subgroup Gs).subgroupOf C.X) :=
    C.S₁.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe C.S₁_le_X).symm
  have hY : C.E₁.subgroupOf C.X ⊔ C.E₂.subgroupOf C.X ⊔ (C.S₁ : Subgroup Gs).subgroupOf C.X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup C.E₁_le_X C.E₂_le_X,
      ← Subgroup.subgroupOf_sup C.E_le_X C.S₁_le_X, ← C.X_eq]
    exact Subgroup.subgroupOf_self _
  have hN : (C.E₁.subgroupOf C.X ⊔ C.E₂.subgroupOf C.X).Normal := by
    rw [← Subgroup.subgroupOf_sup C.E₁_le_X C.E₂_le_X]
    exact C.normal_E
  exact comps_of_sup_pgroup ((isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe C.E₁_le_X)).2 hcomp.quasi₁)
    ((isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe C.E₂_le_X)).2 hcomp.quasi₂)
    (fun a ha b hb => Subtype.ext (hcomp.comm _ ha _ hb)) hN hT hY

theorem FusedCtx.layer_eq_pull (hSp : IsPGroup 2 ↥(barOf z S)) :
    layer (CentralizerBar z) = C.pull (C.E₁ ⊔ C.E₂) := by
  have hLY : layer (CentralizerBar z) ≤ Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup]; exact le_sup_left
  have hSY : barOf z S ≤ Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup]; exact le_sup_right
  have hN : ((layer (CentralizerBar z)).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)).Normal := by
    have : (layer (CentralizerBar z)).Normal := by
      have := CFSG.LocalCores.layer_characteristic (G := CentralizerBar z)
      infer_instance
    exact this.subgroupOf _
  have hperf : (layer (CentralizerBar z)).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S) ≤
      oResidual 2 ↥(Stage1.Thm3.Sec8.layerSBar z S) := by
    apply perfect_le_oResidual
    have hp : Group.IsPerfect ↥(layer (CentralizerBar z)) :=
      Subgroup.isPerfect_iff.mpr CFSG.LocalCores.layer_perfect
    have e := Subgroup.subgroupOfEquivOfLe hLY
    exact Group.IsPerfect.ofSurjective (G := ↥(layer (CentralizerBar z)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have hT : IsPGroup 2 ↥((barOf z S).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
  have hY : (layer (CentralizerBar z)).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S) ⊔
      (barOf z S).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLY hSY, ← layerSBar_eq_sup]
    exact Subgroup.subgroupOf_self _
  have hres := oResidual_sup_eq hN hperf hT hY
  calc layer (CentralizerBar z) =
        ((layer (CentralizerBar z)).subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)).map
          (Stage1.Thm3.Sec8.layerSBar z S).subtype := (Subgroup.map_subgroupOf_eq_of_le hLY).symm
    _ = (oResidual 2 ↥(Stage1.Thm3.Sec8.layerSBar z S)).map (Stage1.Thm3.Sec8.layerSBar z S).subtype := by
        rw [hres]
    _ = C.pull (C.E₁ ⊔ C.E₂) := by
        unfold FusedCtx.pull FusedCtx.emb
        rw [← C.oRes_X, ← Subgroup.map_map,
          Stage1.Thm6.Prod.map_oResidual C.Ψ.symm.toMonoidHom C.Ψ.symm.surjective Nat.prime_two]

omit [Finite G] [Finite Gs] in
theorem FusedCtx.pull_eq_map (K : Subgroup Gs) :
    C.pull K = ((K.subgroupOf C.X).map C.Ψ.symm.toMonoidHom).map
      (Stage1.Thm3.Sec8.layerSBar z S).subtype := by
  unfold FusedCtx.pull FusedCtx.emb
  rw [Subgroup.map_map]

omit [Finite G] [Finite Gs] in
theorem FusedCtx.pull_mono {K K' : Subgroup Gs} (h : K ≤ K') : C.pull K ≤ C.pull K' :=
  Subgroup.map_mono (fun _ hx => h hx)

theorem FusedCtx.pull_isComponent (hSp : IsPGroup 2 ↥(barOf z S)) {K : Subgroup Gs}
    (hKE : K ≤ C.E₁ ⊔ C.E₂) (hK : IsComponent (K.subgroupOf C.X)) : IsComponent (C.pull K) := by
  have hLn : (layer (CentralizerBar z)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := CentralizerBar z)
    infer_instance
  have hLY : layer (CentralizerBar z) ≤ Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup]; exact le_sup_left
  have hKL : C.pull K ≤ layer (CentralizerBar z) := by
    rw [C.layer_eq_pull hSp]; exact C.pull_mono hKE
  rw [C.pull_eq_map] at hKL ⊢
  exact isComponent_map_subtype_of_le_normal hLn hLY (isComponent_map_of_isComponent C.Ψ.symm hK) hKL

include C in
theorem FusedCtx.centralizer_layer_le (hcen : Cen2 G z S) :
    ∀ γ : CentralizerBar z, (∀ l ∈ layer (CentralizerBar z), l * γ = γ * l) →
      γ ∈ layer (CentralizerBar z) := by
  have hSp : IsPGroup 2 ↥(barOf z S) := (isSylowOf_barOf hcen.sylow).isPGroup
  have hO : pPrimeCore 2 (CentralizerBar z) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _
  have hLn : (layer (CentralizerBar z)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := CentralizerBar z)
    infer_instance
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S) ⊤ := isSylowOf_barOf hcen.sylow
  have hcomp := C.pkg.data.comps
  have hz₁S : C.z₁ ∈ (C.S₁ : Subgroup Gs) := (comm_of_center C.pkg.data.syl.z_cen).1
  have hz₁X : C.z₁ ∈ C.X := C.S₁_le_X hz₁S
  have hz₁E : C.z₁ ∈ C.E₁ ⊔ C.E₂ := Subgroup.mem_sup_left hcomp.z_mem₁
  have hz₁sq : C.z₁ * C.z₁ = 1 := by
    have := pow_orderOf_eq_one C.z₁
    rwa [C.pkg.data.syl.z_inv, pow_two] at this
  set ζ : CentralizerBar z := C.emb ⟨C.z₁, hz₁X⟩ with hζdef
  have hζL : ζ ∈ layer (CentralizerBar z) := by
    rw [C.layer_eq_pull hSp]
    exact ⟨⟨C.z₁, hz₁X⟩, hz₁E, rfl⟩
  have hζ : ζ * ζ = 1 := by
    rw [hζdef, ← map_mul]
    have : (⟨C.z₁, hz₁X⟩ * ⟨C.z₁, hz₁X⟩ : ↥C.X) = 1 := Subtype.ext hz₁sq
    rw [this, map_one]
  have hcT : ∀ x ∈ barOf z S, (∀ l ∈ layer (CentralizerBar z), l * x = x * l) → x = 1 ∨ x = ζ := by
    intro x hxT hxc
    have hxΓ : x ∈ Stage1.Thm3.Sec8.layerSBar z S := by
      rw [layerSBar_eq_sup]; exact Subgroup.mem_sup_right hxT
    set w : ↥C.X := C.Ψ ⟨x, hxΓ⟩ with hw
    have hwS : (w : Gs) ∈ (C.S₁ : Subgroup Gs) := (C.hΨ ⟨x, hxΓ⟩).1 hxT
    have hwc : ∀ k ∈ C.E₁ ⊔ C.E₂, (w : Gs) * k = k * (w : Gs) := by
      intro k hk
      have hkX : k ∈ C.X := C.E_le_X hk
      have hl : C.emb ⟨k, hkX⟩ ∈ layer (CentralizerBar z) := by
        rw [C.layer_eq_pull hSp]
        exact ⟨⟨k, hkX⟩, hk, rfl⟩
      have h1 := hxc _ hl
      have h2 : C.Ψ.symm ⟨k, hkX⟩ * ⟨x, hxΓ⟩ = ⟨x, hxΓ⟩ * C.Ψ.symm ⟨k, hkX⟩ := Subtype.ext h1
      have h3 := congrArg C.Ψ h2
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
      exact congrArg Subtype.val h3.symm
    have hmem := C.pkg.data.syl.cs _ hwS hwc
    rcases eq_one_or_eq_of_mem_zpowers_sq hz₁sq hmem with h | h
    · left
      have : w = 1 := Subtype.ext h
      have h1 : (⟨x, hxΓ⟩ : ↥(Stage1.Thm3.Sec8.layerSBar z S)) = 1 :=
        C.Ψ.injective (by rw [← hw, this, map_one])
      exact congrArg Subtype.val h1
    · right
      have : w = ⟨C.z₁, hz₁X⟩ := Subtype.ext h
      have h1 : (⟨x, hxΓ⟩ : ↥(Stage1.Thm3.Sec8.layerSBar z S)) = C.Ψ.symm ⟨C.z₁, hz₁X⟩ := by
        apply C.Ψ.injective
        rw [← hw, this, MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val h1
  exact centralizer_le_of_sylow_inf hO hLn hT hζL hζ hcT

include C in
theorem FusedCtx.innerE_eq (hcen : Cen2 G z S) : InnerE z = layer (CentralizerBar z) := by
  unfold InnerE
  refine sup_eq_left.2 fun γ hγ => C.centralizer_layer_le hcen γ fun l hl => ?_
  exact (Subgroup.mem_centralizer_iff.1 hγ l hl)

theorem FusedCtx.LBar_eq_pull (hcen : Cen2 G z S) : LBar z = C.pull (C.E₁ ⊔ C.E₂) := by
  rw [Stage1.Thm6.Prod.LBar_eq z, C.innerE_eq hcen, inf_eq_right.2
    (perfect_le_oPrimePResidual' (Subgroup.isPerfect_iff.mpr CFSG.LocalCores.layer_perfect)),
    C.layer_eq_pull (isSylowOf_barOf hcen.sylow).isPGroup]

theorem FusedCtx.mem_LC_iff (hcen : Cen2 G z S) {s : G} (hsC : s ∈ Cen z) (hs : s ∈ S)
    (hy : toBar z ⟨s, hsC⟩ ∈ Stage1.Thm3.Sec8.layerSBar z S) :
    s ∈ LC z ↔ ((C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩ : ↥C.X) : Gs) ∈ C.E₁ ⊔ C.E₂ := by
  obtain ⟨k, hk⟩ := hcen.sylow.isPGroup ⟨s, hs⟩
  have hk' : (⟨s, hsC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) ⟨s, hsC⟩ hk', C.LBar_eq_pull hcen, C.mem_pull_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩

theorem FusedCtx.exists_sigma' (hcen : Cen2 G z S) :
    ∃ σ : ↥S ≃* ↥(C.S₁ : Subgroup Gs), ∀ s : ↥S,
      ∃ (hsC : (s : G) ∈ Cen z) (hy : toBar z ⟨s, hsC⟩ ∈ Stage1.Thm3.Sec8.layerSBar z S),
        ((σ s : ↥(C.S₁ : Subgroup Gs)) : Gs) = ((C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩ : ↥C.X) : Gs) ∧
        ((s : G) ∈ LC z ↔ ((σ s : ↥(C.S₁ : Subgroup Gs)) : Gs) ∈ C.E₁ ⊔ C.E₂) := by
  have hSC : S ≤ Cen z := hcen.sylow.le
  have hSp : IsPGroup 2 ↥S := hcen.sylow.isPGroup
  have hSN : S ⊓ OddCore z = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact Subgroup.mem_bot.2 (eq_one_of_mem_pgroup_oddCore hSp hs.1 hs.2)
  let β := barEquiv z S hSC hSN
  have hle : barOf z S ≤ Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup]; exact le_sup_right
  let ρ₀ : ↥(barOf z S) →* Gs :=
    C.X.subtype.comp (C.Ψ.toMonoidHom.comp (Subgroup.inclusion hle))
  have hρ₀ : ∀ y, ρ₀ y ∈ (C.S₁ : Subgroup Gs) := fun y => (C.hΨ ⟨y.1, hle y.2⟩).1 y.2
  let ρ : ↥(barOf z S) →* ↥(C.S₁ : Subgroup Gs) := ρ₀.codRestrict _ hρ₀
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ρ₀ a = ρ₀ b := congrArg (fun w : ↥(C.S₁ : Subgroup Gs) => (w : Gs)) hab
    have h2 : C.Ψ (Subgroup.inclusion hle a) = C.Ψ (Subgroup.inclusion hle b) := Subtype.ext h1
    exact Subgroup.inclusion_injective hle (C.Ψ.injective h2)
  have hρsurj : Function.Surjective ρ := by
    intro x
    have hxX : (x : Gs) ∈ C.X := C.S₁_le_X x.2
    set y : ↥(Stage1.Thm3.Sec8.layerSBar z S) := C.Ψ.symm ⟨x, hxX⟩ with hy
    have hΨy : ((C.Ψ y : ↥C.X) : Gs) = x := by
      rw [hy, MulEquiv.apply_symm_apply]
    have hyS : (y : CentralizerBar z) ∈ barOf z S := (C.hΨ y).2 (by rw [hΨy]; exact x.2)
    refine ⟨⟨y, hyS⟩, Subtype.ext ?_⟩
    show ((C.Ψ (Subgroup.inclusion hle ⟨y, hyS⟩) : ↥C.X) : Gs) = x
    exact hΨy
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥S ≃* ↥(C.S₁ : Subgroup Gs),
      ∀ s, ((σ s : ↥(C.S₁ : Subgroup Gs)) : Gs) = ρ₀ (β s) :=
    ⟨β.trans (MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩), fun s => rfl⟩
  refine ⟨σ, fun s => ?_⟩
  have hsC : (s : G) ∈ Cen z := hSC s.2
  have hy : toBar z ⟨s, hsC⟩ ∈ Stage1.Thm3.Sec8.layerSBar z S :=
    hle ⟨⟨s, hsC⟩, s.2, rfl⟩
  refine ⟨hsC, hy, ?_, ?_⟩
  · rw [hσ]
    rfl
  · rw [C.mem_LC_iff hcen hsC s.2 hy, hσ]
    rfl

theorem FusedCtx.exists_sigma (hcen : Cen2 G z S) :
    ∃ σ : ↥S ≃* ↥(C.S₁ : Subgroup Gs), ∀ s : ↥S,
      ((s : G) ∈ LC z ↔ ((σ s : ↥(C.S₁ : Subgroup Gs)) : Gs) ∈ C.E₁ ⊔ C.E₂) := by
  obtain ⟨σ, hσ⟩ := C.exists_sigma' hcen
  exact ⟨σ, fun s => (hσ s).choose_spec.choose_spec.2⟩

end Trans

end CFSG.GH74.GLS.Stage1.Main
