module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesPrimeField
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayer

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section NatCentralizer

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

theorem natural_unit_centralizer_root (x : SL(2, F)) (T : (AddMonoid.End (Fin 2 → F))ˣ)
    (hT2 : T * T = 1)
    (hnorm : T ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ))
    (hcomm : ∀ g : SL(2, F), x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range →
      T * natEnd F g = natEnd F g * T) :
    ∃ g : SL(2, F), x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range ∧ T = natEnd F g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : (AddMonoid.End (Fin 2 → F))ˣ := natEnd F x with ha
  have hainv : natEnd F x⁻¹ = a⁻¹ := map_inv _ _
  have hnormrange : ∀ y : SL(2, F), natEnd F y ∈
      Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := fun y =>
    Subgroup.le_normalizer ⟨y, rfl⟩
  set T' : (AddMonoid.End (Fin 2 → F))ˣ := a⁻¹ * T * a with hT'
  have hT'2 : T' * T' = 1 := by
    calc T' * T' = a⁻¹ * (T * T) * a := by rw [hT']; group
      _ = 1 := by rw [hT2]; group
  have hT'norm : T' ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ hnorm) (hnormrange x)
    rw [← hainv]
    exact hnormrange _
  have hT'comm : ∀ t : F, T' * natEnd F (uElt t) = natEnd F (uElt t) * T' := by
    intro t
    have hg : x⁻¹ * (x * uElt t * x⁻¹) * x ∈ (upperUnipotent (F := F)).range :=
      (mem_rootGroup_iff _).mpr ⟨t, by group⟩
    have h1 := hcomm (x * uElt t * x⁻¹) hg
    rw [map_mul, map_mul, ← ha, hainv] at h1
    set u := natEnd F (uElt t) with hu
    calc T' * u = a⁻¹ * (T * (a * u * a⁻¹)) * a := by rw [hT']; group
      _ = a⁻¹ * ((a * u * a⁻¹) * T) * a := by rw [h1]
      _ = u * T' := by rw [hT']; group
  let P : Subgroup (AddMonoid.End (Fin 2 → F))ˣ := Subgroup.zpowers T'
  have hP : ∀ y ∈ P, y ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ∧
      ∀ t : F, y * natEnd F (uElt t) = natEnd F (uElt t) * y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨Subgroup.zpow_mem _ hT'norm k, fun t =>
      ((show Commute T' (natEnd F (uElt t)) from hT'comm t).zpow_left k).eq⟩
  have hyy : ∀ y ∈ P, y * y = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← (Commute.refl T').mul_zpow k, hT'2, one_zpow]
  have hpg : IsPGroup 2 P := fun y =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hyy y.1 y.2)⟩
  obtain ⟨t, ht⟩ := pSubgroup_centralizer_root P hP hpg T' (Subgroup.mem_zpowers T')
  refine ⟨x * uElt t * x⁻¹, (mem_rootGroup_iff _).mpr ⟨t, by group⟩, ?_⟩
  rw [map_mul, map_mul, ← ha, hainv, ← ht, hT']
  group

omit [Fintype F] [CharP F 2] in
theorem exists_rootLine_eq (ℓ : Submodule F (Fin 2 → F)) (hℓ : Module.finrank F ℓ = 1) :
    ∃ x : SL(2, F), ℓ = rootLine x := by
  obtain ⟨⟨v, hvmem⟩, hv0, hall⟩ := finrank_eq_one_iff'.1 hℓ
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hℓv : ℓ = Submodule.span F {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hall ⟨w, hw⟩
      have : c • v = w := congrArg Subtype.val hc
      rw [← this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hvmem
  have he0 : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨x, hx⟩ := exists_smul_eq_of_ne_zero (Pi.single 0 1 : Fin 2 → F) v he0 hv0'
  exact ⟨x, by rw [hℓv, rootLine, hx]⟩

omit [Fintype F] [CharP F 2] in
theorem natEndHom_injective : Function.Injective (natEndHom F) := by
  intro g h hgh
  apply Subtype.ext
  ext i j
  have := congrArg (fun f : AddMonoid.End (Fin 2 → F) => f (Pi.single j 1) i) hgh
  simpa [natEndHom_apply, Matrix.mulVec_single_one] using this

end NatCentralizer

section ConjEnd

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {F : Type*} [Field F]

@[expose] def conjEnd (β : W ≃+ (Fin 2 → F)) :
    (W ≃ₗ[ZMod 2] W) →* AddMonoid.End (Fin 2 → F) where
  toFun g := AddMonoidHom.mk' (fun v => β (g (β.symm v))) fun v w => by
    simp only [map_add]
  map_one' := AddMonoidHom.ext fun v => by
    show β ((1 : W ≃ₗ[ZMod 2] W) (β.symm v)) = v
    simp
  map_mul' g h := AddMonoidHom.ext fun v => by
    show β ((g * h) (β.symm v)) = β (g (β.symm (β (h (β.symm v)))))
    simp

theorem conjEnd_apply (β : W ≃+ (Fin 2 → F)) (g : W ≃ₗ[ZMod 2] W) (v : Fin 2 → F) :
    conjEnd β g v = β (g (β.symm v)) := rfl

theorem conjEnd_injective (β : W ≃+ (Fin 2 → F)) : Function.Injective (conjEnd β) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro w
  have := congrArg (fun f : AddMonoid.End (Fin 2 → F) => f (β w)) hgh
  simp only [conjEnd_apply, AddEquiv.symm_apply_apply] at this
  exact β.injective this

end ConjEnd

section Abstract

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] {X : Type*} [Group X]

theorem exists_element_of_commute (φ : X →* (W ≃ₗ[ZMod 2] W)) (β : W ≃+ (Fin 2 → F))
    (Ls As Es : Subgroup X) (x : SL(2, F))
    (hLs : ∀ g : SL(2, F), ∃ l ∈ Ls, conjEnd β (φ l) = natEndHom F g)
    (hLs' : ∀ l ∈ Ls, ∃ g : SL(2, F), conjEnd β (φ l) = natEndHom F g)
    (hAs : ∀ g : SL(2, F), (∃ a ∈ As, conjEnd β (φ a) = natEndHom F g) ↔
      x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range)
    (hEn : ∀ e ∈ Es, ∀ l ∈ Ls, e * l * e⁻¹ ∈ Ls)
    (hE2 : ∀ e ∈ Es, e * e = 1) (hcomm : ∀ e ∈ Es, ∀ a ∈ As, e * a = a * e)
    {e : X} (he : e ∈ Es) : ∃ a ∈ As, φ e = φ a := by
  let Ψ : X →* (AddMonoid.End (Fin 2 → F))ˣ := ((conjEnd β).comp φ).toHomUnits
  have hΨval : ∀ y, (Ψ y).val = conjEnd β (φ y) := fun y => rfl
  have hΨnat : ∀ y g, conjEnd β (φ y) = natEndHom F g → Ψ y = natEnd F g := fun y g h =>
    Units.ext (by rw [hΨval, natEnd_val]; exact h)
  have hT2 : Ψ e * Ψ e = 1 := by rw [← map_mul, hE2 e he, map_one]
  have hTinv : (Ψ e)⁻¹ = Ψ e := inv_eq_of_mul_eq_one_right hT2
  have hfwd : ∀ h ∈ (natEnd F).range, Ψ e * h * (Ψ e)⁻¹ ∈ (natEnd F).range := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨l, hl, hlg⟩ := hLs g
    obtain ⟨g', hg'⟩ := hLs' _ (hEn e he l hl)
    refine ⟨g', ?_⟩
    rw [← hΨnat _ _ hg', ← hΨnat _ _ hlg, map_mul, map_mul, map_inv]
  have hnorm : Ψ e ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfwd h
    · intro hh
      have h2 := hfwd _ hh
      have e3 : Ψ e * (Ψ e * h * (Ψ e)⁻¹) * (Ψ e)⁻¹ = h := by
        rw [hTinv]
        calc Ψ e * (Ψ e * h * Ψ e) * Ψ e = (Ψ e * Ψ e) * h * (Ψ e * Ψ e) := by group
          _ = h := by rw [hT2]; group
      rw [← e3]
      exact h2
  have hcomm' : ∀ g : SL(2, F), x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range →
      Ψ e * natEnd F g = natEnd F g * Ψ e := by
    intro g hg
    obtain ⟨a, ha, hag⟩ := (hAs g).2 hg
    rw [← hΨnat _ _ hag, ← map_mul, ← map_mul, hcomm e he a ha]
  obtain ⟨g, hg, hTg⟩ := natural_unit_centralizer_root x (Ψ e) hT2 hnorm hcomm'
  obtain ⟨a, ha, hag⟩ := (hAs g).2 hg
  refine ⟨a, ha, conjEnd_injective β ?_⟩
  have h1 : conjEnd β (φ e) = natEndHom F g := by
    rw [← natEnd_val, ← hTg]
    rfl
  rw [h1, hag]

end Abstract

section VLevel

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem isElementaryAbelian_of_le {G : Type*} [Group G] {p : ℕ} {D E : Subgroup G} (hDE : D ≤ E)
    (h : CFSG.IsElementaryAbelian p E) : CFSG.IsElementaryAbelian p D :=
  CFSG.IsElementaryAbelian.of_le h hDE

theorem isInvariant_commGL_of_le_normalizer {L N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hN : N ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) :
    Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) N (commGL L ⊤) := by
  intro g hg u hu
  have h1 := commSub_map (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) (H := L) (g := g) (hN hg)
    (⊤ : Submodule (ZMod 2) V)
  have h2 : (⊤ : Submodule (ZMod 2) V).map
      ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) g : V →ₗ[ZMod 2] V) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact (g : V ≃ₗ[ZMod 2] V).surjective
  rw [h2] at h1
  have h3 : commGL L ⊤ = (commGL L ⊤).map (g : V →ₗ[ZMod 2] V) := h1
  show g u ∈ commGL L ⊤
  rw [h3]
  exact ⟨u, hu, rfl⟩

theorem commGL_commGL_of_perfect {L : Subgroup (V ≃ₗ[ZMod 2] V)} (hL : Group.IsPerfect ↥L) :
    commGL L (commGL L ⊤) = commGL L ⊤ := by
  have h := commSub_commSub_of_perfect ((MonoidHom.id (V ≃ₗ[ZMod 2] V)).comp L.subtype) hL
  have e1 : ∀ U : Submodule (ZMod 2) V,
      commSub ((MonoidHom.id (V ≃ₗ[ZMod 2] V)).comp L.subtype) ⊤ U = commGL L U := by
    intro U
    unfold commSub
    congr 1
    ext w
    constructor
    · rintro ⟨b, -, u, hu, rfl⟩
      exact ⟨b, b.2, u, hu, rfl⟩
    · rintro ⟨b, hb, u, hu, rfl⟩
      exact ⟨⟨b, hb⟩, trivial, u, hu, rfl⟩
  rw [e1, e1] at h
  exact h

theorem fix_of_actW_eq_one {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) {x : ↥(L ⊔ A)}
    (hx : actW L A I hAn hI x = 1) : ∀ u ∈ I, (x : V ≃ₗ[ZMod 2] V) u - u ∈ fixGL L := by
  intro u hu
  have h1 : actW L A I hAn hI x (Submodule.Quotient.mk ⟨u, hu⟩) =
      Submodule.Quotient.mk ⟨u, hu⟩ := by
    rw [hx]
    rfl
  rw [actW_mk, Submodule.Quotient.eq] at h1
  intro l hl
  have e : ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x ⟨u, hu⟩ - ⟨u, hu⟩ : ↥I) : V) =
      (x : V ≃ₗ[ZMod 2] V) u - u := by
    rw [Submodule.coe_sub, resSub_apply]
    rfl
  have h2 : (l : V ≃ₗ[ZMod 2] V)
      ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x ⟨u, hu⟩ - ⟨u, hu⟩ : ↥I) : V) =
      ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x ⟨u, hu⟩ - ⟨u, hu⟩ : ↥I) : V) :=
    h1 l hl
  rw [e] at h2
  exact h2

theorem actW_trivial_fixes {L E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEn : E ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ E) (commGL L ⊤))
    (hperf : Group.IsPerfect ↥L)
    (hfaith : ∀ x ∈ L, (∀ v ∈ commGL L ⊤, x v - v ∈ fixGL L) → x = 1)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ E)
    (hφ : actW L E (commGL L ⊤) hEn hIE ⟨b, Subgroup.mem_sup_right hb⟩ = 1) :
    (∀ l ∈ L, b * l = l * b) ∧ ∀ u ∈ commGL L ⊤, b u = u := by
  have hz : ∀ u ∈ commGL L ⊤, b u - u ∈ fixGL L := fix_of_actW_eq_one hEn hIE hφ
  have hcomm : ∀ l ∈ L, b * l = l * b := by
    intro l hl
    have hbn : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hEn hb) l).1 hl
    have hc : b * l * b⁻¹ * l⁻¹ ∈ L := L.mul_mem hbn (L.inv_mem hl)
    have hcX : actW L E (commGL L ⊤) hEn hIE ⟨b * l * b⁻¹ * l⁻¹, Subgroup.mem_sup_left hc⟩ = 1 := by
      have e : (⟨b * l * b⁻¹ * l⁻¹, Subgroup.mem_sup_left hc⟩ : ↥(L ⊔ E)) =
          ⟨b, Subgroup.mem_sup_right hb⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ *
            ⟨b, Subgroup.mem_sup_right hb⟩⁻¹ * ⟨l, Subgroup.mem_sup_left hl⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hφ]
      group
    have hcfix := fix_of_actW_eq_one hEn hIE hcX
    have hc1 : b * l * b⁻¹ * l⁻¹ = 1 := hfaith _ hc fun v hv => hcfix v hv
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)
  refine ⟨hcomm, fun u hu => ?_⟩
  have hI' : commGL L (commGL L ⊤) = commGL L ⊤ := commGL_commGL_of_perfect hperf
  have hle : commGL L (commGL L ⊤) ≤ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
    rw [commSub_le_iff]
    intro l hl w hw
    rw [LinearMap.mem_ker]
    have h1 : b (l w) = l (b w) := by
      have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ w) (hcomm l hl)
      simpa using this
    have h2 : l (b w - w) = b w - w := hz w hw l hl
    rw [map_sub] at h2
    show b ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) l w - w) - ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) l w - w) = 0
    simp only [MonoidHom.id_apply, map_sub, h1]
    calc l (b w) - b w - (l w - w) = (l (b w) - l w) - (b w - w) := by abel
      _ = 0 := by rw [h2]; exact sub_self _
  have hu' : u ∈ commGL L (commGL L ⊤) := by rw [hI']; exact hu
  have := hle hu'
  rw [LinearMap.mem_ker] at this
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
  exact sub_eq_zero.1 this

end VLevel

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem isPerfect_Lc (ctx : FamilyCtx H T n F r Lc) (i : Fin r) : Group.IsPerfect ↥(Lc i) :=
  (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (ctx.hLc.isComp i).1) (ctx.hLc.isComp i).2.1).1

omit [Finite V] in
theorem offender_le_normalizer (ctx : FamilyCtx H T n F r Lc) {A E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) (hE : IsOffender H E)
    (hAE : A ≤ E) : E ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := fun e he =>
  mem_normalizer_of_commute ctx hA hmove (hE.1 he) fun a ha =>
    congrArg Subtype.val (hE.2.2.1.1.1.1 ⟨e, he⟩ ⟨a, hAE ha⟩)

theorem natural_action_eq (ctx : FamilyCtx H T n F r Lc) {A E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (hN : NatData (Lc i) A (ctx.α i)) (hE : IsOffender H E) (hAE : A ≤ E) :
    ∀ e ∈ E, ∃ a ∈ A, (∀ l ∈ Lc i, (a⁻¹ * e) * l = l * (a⁻¹ * e)) ∧
      ∀ u ∈ commGL (Lc i) ⊤, (a⁻¹ * e) u = u := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have : CharP F 2 := charP_two_of_card_eq ctx.hF
  have hEel : CFSG.IsElementaryAbelian 2 E := hE.2.2.1
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hEn := offender_le_normalizer ctx hA hmove hE hAE
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  have hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) :=
    isInvariant_sup_subgroup hd.inv_L (isInvariant_commGL_of_le_normalizer hEn)
  obtain ⟨hAL, -, β, hβ, ℓ, hℓ1, hℓ⟩ := hN
  obtain ⟨x, rfl⟩ := exists_rootLine_eq ℓ hℓ1
  let φ := actW (Lc i) E (commGL (Lc i) ⊤) hEn hIE
  have hβ' : ∀ (l : ↥(Lc i)) (w : ↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)),
      β (φ ⟨l, Subgroup.mem_sup_left l.2⟩ w) =
        (thetaL (Lc i) (ctx.α i) l : Matrix (Fin 2) (Fin 2) F).mulVec (β w) := by
    intro l w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    show β (actW (Lc i) E (commGL (Lc i) ⊤) hEn hIE ⟨l, Subgroup.mem_sup_left l.2⟩
      (Submodule.Quotient.mk u)) = _
    rw [actW_mk hEn hIE ⟨l, Subgroup.mem_sup_left l.2⟩ u]
    exact hβ l u (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE
      ⟨l, Subgroup.mem_sup_left l.2⟩ u) (resSub_apply _ _ _ _ _ u)
  have hconj : ∀ l : ↥(Lc i), conjEnd β (φ ⟨l, Subgroup.mem_sup_left l.2⟩) =
      natEndHom F (thetaL (Lc i) (ctx.α i) l) := by
    intro l
    apply AddMonoidHom.ext
    intro v
    refine (conjEnd_apply β _ v).trans ?_
    rw [hβ', β.apply_symm_apply]
    rfl
  intro e he
  obtain ⟨a, ha, hφ⟩ := exists_element_of_commute φ β ((Lc i).subgroupOf (Lc i ⊔ E))
    (A.subgroupOf (Lc i ⊔ E)) (E.subgroupOf (Lc i ⊔ E)) x
    (fun g => by
      obtain ⟨l, rfl⟩ := thetaL_surjective (Lc i) (ctx.α i) g
      exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, l.2, hconj l⟩)
    (fun l hl => ⟨_, hconj ⟨l.1, hl⟩⟩)
    (fun g => by
      constructor
      · rintro ⟨a', ha', hcg⟩
        have haL : (a' : V ≃ₗ[ZMod 2] V) ∈ Lc i := hAL ha'
        have e1 : conjEnd β (φ a') = natEndHom F (thetaL (Lc i) (ctx.α i) ⟨a', haL⟩) :=
          hconj ⟨a', haL⟩
        have hgθ : thetaL (Lc i) (ctx.α i) ⟨a', haL⟩ = g :=
          natEndHom_injective (e1.symm.trans hcg)
        have hmem : g ∈ (A.subgroupOf (Lc i)).map (thetaL (Lc i) (ctx.α i)) :=
          ⟨⟨a', haL⟩, ha', hgθ⟩
        exact (conj_mem_range_iff_fixes_line x g).2 ((hℓ g).1 hmem)
      · intro h
        obtain ⟨a', ha', hθ⟩ := (hℓ g).2 ((conj_mem_range_iff_fixes_line x g).1 h)
        exact ⟨⟨a', Subgroup.mem_sup_left a'.2⟩, ha', by rw [hconj a', hθ]⟩)
    (fun e' he' l hl => (Subgroup.mem_normalizer_iff.1 (hEn he') l.1).1 hl)
    (fun e' he' => Subtype.ext (by
      have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) (e' : V ≃ₗ[ZMod 2] V)
        he'
      simpa [pow_two] using h2))
    (fun e' he' a' ha' => Subtype.ext (hcommE _ he' _ (hAE ha')))
    (e := ⟨e, Subgroup.mem_sup_right he⟩) he
  have haA : (a : V ≃ₗ[ZMod 2] V) ∈ A := ha
  refine ⟨a, haA, ?_⟩
  have hb : (a : V ≃ₗ[ZMod 2] V)⁻¹ * e ∈ E := E.mul_mem (E.inv_mem (hAE haA)) he
  have hφ1 : φ ⟨(a : V ≃ₗ[ZMod 2] V)⁻¹ * e, Subgroup.mem_sup_right hb⟩ = 1 := by
    have e2 : (⟨(a : V ≃ₗ[ZMod 2] V)⁻¹ * e, Subgroup.mem_sup_right hb⟩ : ↥(Lc i ⊔ E)) =
        a⁻¹ * ⟨e, Subgroup.mem_sup_right he⟩ := Subtype.ext rfl
    rw [e2, map_mul, map_inv, ← hφ]
    group
  exact actW_trivial_fixes hEn hIE (isPerfect_Lc ctx i) (ctx.layer.faithful_W i) hb hφ1

theorem natural_split (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i)
    {A E : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A) {i : Fin r}
    (hmove : ⁅Lc i, A⁆ ≠ ⊥) (hE : IsOffender H E) (hAE : A ≤ E) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ E ∧ A ⊓ D = ⊥ ∧ E = A ⊔ D ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) D = Nat.card V ∧ ∀ d ∈ D, ∀ l ∈ Lc i, d * l = l * d := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hN : NatData (Lc i) A (ctx.α i) :=
    (alt_dichotomy ctx hA i hmove).resolve_right fun h => h.2.2.1 (hglob i A hA hmove)
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  have hact := natural_action_eq ctx hA hmove hN hE hAE
  have hEn := offender_le_normalizer ctx hA hmove hE hAE
  have hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) :=
    isInvariant_sup_subgroup hd.inv_L (isInvariant_commGL_of_le_normalizer hEn)
  have hEw : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E = Nat.card V :=
    le_antisymm (ctx.layer.upper_bound E hE.1 hE.2.1 hE.2.2.1) hE.2.2.2
  obtain ⟨D, hDE, hAD, hED, hDfix, hDw⟩ := split_offender hAE hE.2.2.1
    (weight_eq_of_mem ctx hA) hEw (W := commGL (Lc i) ⊤) hd.V_split
    (fun a ha hfix => by
      have := hd.A_faithful_I ⟨a, ha⟩ (LinearEquiv.ext fun w =>
        Subtype.ext (by rw [resSub_apply]; exact hfix w w.2))
      exact congrArg Subtype.val this)
    (fun e he => by
      obtain ⟨a, ha, -, hfix⟩ := hact e he
      refine ⟨a, ha, fun w hw => ?_⟩
      have h1 := hfix w hw
      rw [LinearEquiv.mul_apply] at h1
      calc e w = a (a⁻¹ (e w)) := (gl_apply_inv_apply _ _).symm
        _ = a w := by rw [h1])
  refine ⟨D, hDE, hAD, hED, hDw, fun d hd' l hl => ?_⟩
  have hφ : actW (Lc i) E (commGL (Lc i) ⊤) hEn hIE ⟨d, Subgroup.mem_sup_right (hDE hd')⟩ = 1 := by
    refine actW_eq_one_of_disp_mem_fix hEn hIE (x := ⟨d, Subgroup.mem_sup_right (hDE hd')⟩) ?_
    intro w hw
    show d w - w ∈ fixGL (Lc i)
    rw [hDfix d hd' w hw, sub_self]
    exact Submodule.zero_mem _
  exact (actW_trivial_fixes hEn hIE (isPerfect_Lc ctx i) (ctx.layer.faithful_W i) (hDE hd')
    hφ).1 l hl

theorem natural_offenderSplit (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) : OffenderSplit H := by
  intro A E hA hAE hE
  obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
  obtain ⟨D, hDE, hAD, hED, hDw, -⟩ := natural_split ctx hglob hA hi hE hAE
  refine ⟨D, hDE, hAD, hED, ?_⟩
  by_cases hD : D = ⊥
  · exact Or.inl hD
  · exact Or.inr ⟨hDE.trans hE.1, hD, isElementaryAbelian_of_le hDE hE.2.2.1, hDw.ge⟩

end Natural

end CFSG.QuasithinUnique.Setup.Lift
