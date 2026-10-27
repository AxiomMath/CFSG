module

public import CFSG.LargeExtraspecial.DWTransConj
public import CFSG.LargeExtraspecial.DWTransAxis
public import CFSG.LargeExtraspecial.DWTransGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

variable (S) in
@[expose] noncomputable def axisForm (A : Subgroup G) (y : G) : Dual (ZMod 2) (S.clSub A) :=
  (S.q.polarBilin.flip (S.cl y)) ∘ₗ (S.clSub A).subtype

theorem axisForm_apply (y : G) (v : S.clSub A) : axisForm S A y v = polar S.q v (S.cl y) :=
  rfl

variable (S) in
@[expose] noncomputable def Ubar (A : Subgroup G) (h : G) : Subgroup S.O :=
  ((conjSub A h ⊓ S.M).subgroupOf S.M).map S.ρ

theorem Ubar_le_Mbar (h : G) : Ubar S A h ≤ S.Mbar := map_le_range _ _

@[expose] def fixer (φ : Dual (ZMod 2) (S.clSub A)) :
    Subgroup (S.clSub A ≃ₗ[ZMod 2] S.clSub A) where
  carrier := {g | ∀ w, φ w = 0 → g w = w}
  mul_mem' {g g'} hg hg' w hw := by
    change g (g' w) = w
    rw [hg' w hw, hg w hw]
  one_mem' _ _ := rfl
  inv_mem' {g} hg w hw := by
    change g.symm w = w
    rw [LinearEquiv.symm_apply_eq, hg w hw]

variable (S) in
@[expose] noncomputable def axisCore (A : Subgroup G) : Submodule (ZMod 2) S.Qt where
  carrier := {w | w ∈ S.clSub A ∧ ∀ h' : G, h' * S.z * h'⁻¹ ∈ S.QG → h' * S.z * h'⁻¹ ∉ A →
    polar S.q w (S.cl (h' * S.z * h'⁻¹)) = 0}
  add_mem' {w w'} hw hw' := ⟨Submodule.add_mem _ hw.1 hw'.1, fun h' h1 h2 => by
    rw [polar_add_left, hw.2 h' h1 h2, hw'.2 h' h1 h2, add_zero]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ _ => polar_zero_left _ _⟩
  smul_mem' c w hw := ⟨Submodule.smul_mem _ c hw.1, fun h' h1 h2 => by
    rw [polar_smul_left, hw.2 h' h1 h2, smul_zero]⟩

variable (S) in
@[expose] noncomputable def coreStab (hM : S.M ≤ normalizer (A : Set G)) : Subgroup S.Mbar where
  carrier := {g | ∀ w ∈ S.clSub A, ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ axisCore S A ∧
    (w ∈ axisCore S A → ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)}
  mul_mem' {g g'} hg hg' w hw := by
    have hg'w := MaxEA.apply_mem_clSub hM g'.2 hw
    change ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w ∈ _ ∧
      (_ → ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w)
    refine ⟨?_, fun hwc => by rw [(hg' w hw).2 hwc, (hg w hw).2 hwc]⟩
    rw [show ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
      (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        ((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
        (((g' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) by abel]
    exact Submodule.add_mem _ (hg _ hg'w).1 (hg' w hw).1
  one_mem' w _ := ⟨by
    change w - w ∈ axisCore S A
    rw [sub_self]
    exact Submodule.zero_mem _, fun _ => rfl⟩
  inv_mem' {g} hg w hw := by
    have hw' := MaxEA.apply_mem_clSub hM (g⁻¹ : S.Mbar).2 hw
    have key := hg _ hw'
    have e : ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g⁻¹ : S.Mbar) : S.O).1 w) = w := by
      change ((g * g⁻¹ : S.Mbar) : S.O).1 w = w
      rw [mul_inv_cancel]
      rfl
    rw [e] at key
    refine ⟨?_, fun hwc => ?_⟩
    · have := Submodule.neg_mem _ key.1
      rwa [neg_sub] at this
    · have h1 := (hg w hw).2 hwc
      change ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm w = w
      rw [LinearEquiv.symm_apply_eq, h1]

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) {h : G}
  (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
include hA hM hxQ hxA

omit hM in
theorem axisForm_ne_zero : axisForm S A (h * S.z * h⁻¹) ≠ 0 := by
  intro h0
  refine hxA (hA.mem_of_forall_polar hxQ fun a ha => ?_)
  have := LinearMap.congr_fun h0 ⟨S.cl a, S.cl_mem_clSub ha (hA.le_QG ha)⟩
  rwa [axisForm_apply, LinearMap.zero_apply] at this

omit hM in
theorem finrank_ker_axisForm :
    finrank (ZMod 2) (LinearMap.ker (axisForm S A (h * S.z * h⁻¹))) = S.width - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (axisForm S A (h * S.z * h⁻¹))
  have h2 : finrank (ZMod 2) (LinearMap.range (axisForm S A (h * S.z * h⁻¹))) = 1 := by
    have hle := Submodule.finrank_le (LinearMap.range (axisForm S A (h * S.z * h⁻¹)))
    rw [finrank_self] at hle
    have hne : finrank (ZMod 2) (LinearMap.range (axisForm S A (h * S.z * h⁻¹))) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      exact hA.axisForm_ne_zero hxQ hxA
    omega
  rw [h2, hA.finrank_clSub] at h1
  omega

theorem resAt_Ubar_fix {u : S.O} (hu : u ∈ Ubar S A h) (v : S.clSub A)
    (hv : axisForm S A (h * S.z * h⁻¹) v = 0) :
    resAt S A hM ⟨u, Ubar_le_Mbar h hu⟩ v = v := by
  apply Subtype.ext
  rw [coe_resAt_apply]
  obtain ⟨⟨b, hbM⟩, hb, rfl⟩ := hu
  replace hb : b ∈ conjSub A h ⊓ S.M := hb
  obtain ⟨a, haA, haQ, hav⟩ := S.mem_clSub_iff.mp v.2
  rw [axisForm_apply, ← hav, S.polar_cl_eq_zero_iff haQ hxQ] at hv
  have hab := hA.commute_of_commute hM hxQ hxA haA hv hb.1 (S.mem_M_iff.mp hb.2)
  rw [← hav, S.ρ_cl ⟨b, hbM⟩ haQ]
  change S.cl (b * a * b⁻¹) = S.cl a
  rw [← hab, mul_inv_cancel_right]

omit hM in
theorem card_conjSub_inf_M_ge : 2 ^ S.width ≤ Nat.card (conjSub A h ⊓ S.M : Subgroup G) := by
  set T := S.conjBy h
  have hT := hA.conj h
  have hne : h * S.z * h⁻¹ ≠ S.z := hA.conj_ne_z hxA
  have hzT : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl hxQ hne
  let χ : conjSub A h →* Multiplicative (ZMod 2) :=
    { toFun := fun b => Multiplicative.ofAdd (polar T.q (T.cl b) (T.cl S.z))
      map_one' := by
        change Multiplicative.ofAdd (polar T.q (T.cl 1) (T.cl S.z)) = 1
        rw [T.cl_one, polar_zero_left]
        rfl
      map_mul' := fun b b' => by
        change Multiplicative.ofAdd (polar T.q (T.cl ((b : G) * b')) (T.cl S.z)) =
          Multiplicative.ofAdd (polar T.q (T.cl b) (T.cl S.z)) *
            Multiplicative.ofAdd (polar T.q (T.cl b') (T.cl S.z))
        rw [T.cl_mul (hT.le_QG b.2) (hT.le_QG b'.2), polar_add_left]
        rfl }
  have hker : χ.ker = (conjSub A h ⊓ S.M).subgroupOf (conjSub A h) := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change Multiplicative.ofAdd (polar T.q (T.cl b) (T.cl S.z)) = 1 ↔ _
    rw [show (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 0 from rfl,
      Multiplicative.ofAdd.injective.eq_iff, T.polar_cl_eq_zero_iff (hT.le_QG b.2) hzT,
      mem_inf, S.mem_M_iff]
    exact ⟨fun hc => ⟨b.2, hc⟩, fun hc => hc.2⟩
  have h1 := card_ker_mul_card_range χ
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left :
    conjSub A h ⊓ S.M ≤ conjSub A h)).toEquiv, hT.card_eq, S.width_conjBy] at h1
  have h2 : Nat.card χ.range ≤ 2 := by
    calc Nat.card χ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [pow_succ] at h1
  nlinarith

theorem card_Ubar_ge : 2 ^ (S.width - 1) ≤ Nat.card (Ubar S A h) := by
  set C := conjSub A h ⊓ S.M
  have hC := hA.card_conjSub_inf_M_ge hxQ hxA
  set f : C →* S.O := S.ρ.comp (inclusion (inf_le_right : C ≤ S.M))
  have hrange : f.range = Ubar S A h := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : f.ker = S.QG.subgroupOf C := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have h1 := card_ker_mul_card_range f
  rw [hrange, hker] at h1
  have hx2 : (h * S.z * h⁻¹) * (h * S.z * h⁻¹) = 1 := by
    rw [show (h * S.z * h⁻¹) * (h * S.z * h⁻¹) = h * (S.z * S.z) * h⁻¹ by group, S.z_mul_z,
      mul_one, mul_inv_cancel]
  have hk : Nat.card (S.QG.subgroupOf C) ≤ 2 := by
    have hle : (S.QG.subgroupOf C).map C.subtype ≤ zpowers (h * S.z * h⁻¹) := by
      rintro _ ⟨b, hb, rfl⟩
      replace hb : (b : G) ∈ S.QG := hb
      rw [Setting.mem_zpowers_iff_of_mul_self hx2]
      exact hA.eq_of_mem_conjSub_of_mem_QG hM hxQ hxA b.2.1 hb
    calc Nat.card (S.QG.subgroupOf C) = Nat.card ((S.QG.subgroupOf C).map C.subtype) :=
          (card_map_of_injective C.subtype_injective).symm
      _ ≤ Nat.card (zpowers (h * S.z * h⁻¹)) := Subgroup.card_le_of_le hle
      _ = orderOf (h * S.z * h⁻¹) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [pow_two, hx2])
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hpos : 0 < Nat.card (Ubar S A h) := by
    rcases Nat.eq_zero_or_pos (Nat.card (Ubar S A h)) with h0 | h0
    · rw [h0, mul_zero] at h1
      omega
    · exact h0
  rcases Nat.eq_zero_or_pos S.width with h0 | h0
  · rw [h0]
    exact hpos
  · have : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    nlinarith

omit [IsElementaryAbelian 2 A] hA hM hxQ hxA in
theorem finite_clSub : Finite (S.clSub A) := by
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  exact Finite.of_injective _ Subtype.val_injective

omit [IsElementaryAbelian 2 A] hA hM hxQ hxA in
theorem finite_linearEquiv_clSub : Finite (S.clSub A ≃ₗ[ZMod 2] S.clSub A) := by
  have := finite_clSub (S := S) (A := A)
  exact Finite.of_injective (fun e : S.clSub A ≃ₗ[ZMod 2] S.clSub A => (e : S.clSub A → S.clSub A))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem exists_Ubar_resAt_eq {g : S.clSub A ≃ₗ[ZMod 2] S.clSub A}
    (hg : g ∈ fixer (axisForm S A (h * S.z * h⁻¹))) :
    ∃ u, ∃ hu : u ∈ Ubar S A h, resAt S A hM ⟨u, Ubar_le_Mbar h hu⟩ = g := by
  have := finite_clSub (S := S) (A := A)
  have := finite_linearEquiv_clSub (S := S) (A := A)
  set φ := axisForm S A (h * S.z * h⁻¹)
  set H' := ((Ubar S A h).subgroupOf S.Mbar).map (resAt S A hM)
  have hle : H' ≤ fixer φ := by
    rintro _ ⟨⟨u, huM⟩, hu, rfl⟩ w hw
    exact hA.resAt_Ubar_fix hM hxQ hxA (u := u) hu w hw
  have hcard : Nat.card (fixer φ) ≤ Nat.card H' := by
    calc Nat.card (fixer φ) ≤ Nat.card (LinearMap.ker φ) :=
          card_le_of_forall_fix (hA.axisForm_ne_zero hxQ hxA) _ fun g hg => hg
      _ = 2 ^ (S.width - 1) := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
            hA.finrank_ker_axisForm hxQ hxA]
      _ ≤ Nat.card (Ubar S A h) := hA.card_Ubar_ge hM hxQ hxA
      _ = Nat.card H' := by
          rw [card_map_of_injective (hA.resAt_injective hM),
            Nat.card_congr (subgroupOfEquivOfLe (Ubar_le_Mbar h)).toEquiv]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hg
  obtain ⟨⟨u, huM⟩, hu, rfl⟩ := hg
  exact ⟨u, hu, rfl⟩

omit [IsElementaryAbelian 2 A] hA hxQ hxA in
theorem apply_mem_axisCore {m : S.O} (hm : m ∈ S.Mbar) {w : S.Qt} (hw : w ∈ axisCore S A) :
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ axisCore S A := by
  refine ⟨apply_mem_clSub hM hm hw.1, fun h' h1 h2 => ?_⟩
  obtain ⟨m₀, rfl⟩ := hm
  have hm₀ := m₀.2
  have e : S.cl (h' * S.z * h'⁻¹) = ((S.ρ m₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (((m₀ : G)⁻¹ * h') * S.z * ((m₀ : G)⁻¹ * h')⁻¹)) := by
    rw [S.ρ_cl m₀ (by
      rw [show (m₀ : G)⁻¹ * h' * S.z * ((m₀ : G)⁻¹ * h')⁻¹ =
        (m₀ : G)⁻¹ * (h' * S.z * h'⁻¹) * ((m₀ : G)⁻¹)⁻¹ by group]
      exact S.conj_mem_QG (S.M.inv_mem hm₀) h1)]
    congr 1
    group
  rw [e, polar_apply_apply]
  refine hw.2 _ ?_ ?_
  · rw [show (m₀ : G)⁻¹ * h' * S.z * ((m₀ : G)⁻¹ * h')⁻¹ =
      (m₀ : G)⁻¹ * (h' * S.z * h'⁻¹) * ((m₀ : G)⁻¹)⁻¹ by group]
    exact S.conj_mem_QG (S.M.inv_mem hm₀) h1
  · intro hA'
    apply h2
    have := (mem_normalizer_iff.mp (hM hm₀) _).mp hA'
    rwa [show (m₀ : G) * ((m₀ : G)⁻¹ * h' * S.z * ((m₀ : G)⁻¹ * h')⁻¹) * (m₀ : G)⁻¹ =
      h' * S.z * h'⁻¹ by group] at this

theorem card_Ubar : Nat.card (Ubar S A h) = 2 ^ (S.width - 1) := by
  have := finite_clSub (S := S) (A := A)
  have := finite_linearEquiv_clSub (S := S) (A := A)
  refine le_antisymm ?_ (hA.card_Ubar_ge hM hxQ hxA)
  set φ := axisForm S A (h * S.z * h⁻¹)
  set H' := ((Ubar S A h).subgroupOf S.Mbar).map (resAt S A hM)
  have hle : H' ≤ fixer φ := by
    rintro _ ⟨⟨u, huM⟩, hu, rfl⟩ w hw
    exact hA.resAt_Ubar_fix hM hxQ hxA (u := u) hu w hw
  calc Nat.card (Ubar S A h) = Nat.card H' := by
        rw [card_map_of_injective (hA.resAt_injective hM),
          Nat.card_congr (subgroupOfEquivOfLe (Ubar_le_Mbar h)).toEquiv]
    _ ≤ Nat.card (fixer φ) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (LinearMap.ker φ) :=
        card_le_of_forall_fix (hA.axisForm_ne_zero hxQ hxA) _ fun g hg => hg
    _ = 2 ^ (S.width - 1) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
          hA.finrank_ker_axisForm hxQ hxA]

omit [IsElementaryAbelian 2 A] hA hxQ hxA in
theorem coreStab_normal : (coreStab S hM).Normal := by
  refine ⟨fun g hg m w hw => ?_⟩
  have hmw := apply_mem_clSub hM (m⁻¹ : S.Mbar).2 hw
  have hinv : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.Mbar) : S.O).1 w) = w := by
    change ((m * m⁻¹ : S.Mbar) : S.O).1 w = w
    rw [mul_inv_cancel]
    rfl
  change ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((m⁻¹ : S.Mbar) : S.O).1 w)) - w ∈ _ ∧ (_ → ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.Mbar) : S.O).1 w)) = w)
  refine ⟨?_, fun hwc => ?_⟩
  · rw [show ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((m⁻¹ : S.Mbar) : S.O).1 w)) - w = ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.Mbar) : S.O).1 w) -
          ((m⁻¹ : S.Mbar) : S.O).1 w) by rw [map_sub, hinv]]
    exact apply_mem_axisCore hM m.2 (hg _ hmw).1
  · rw [(hg _ hmw).2 (apply_mem_axisCore hM (m⁻¹ : S.Mbar).2 hwc), hinv]

omit hxQ hxA in
theorem coreStab_isPGroup : IsPGroup 2 (coreStab S hM) := by
  intro g
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  change ((g : S.Mbar) : S.O) * ((g : S.Mbar) : S.O) = 1
  refine hA.eq_one_of_forall_clSub hM (S.Mbar.mul_mem (g : S.Mbar).2 (g : S.Mbar).2)
    fun w hw => ?_
  have hd := (g.2 w hw).1
  change ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w
  have hfix := (g.2 _ hd.1).2 hd
  rw [show ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w +
    (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) by abel, map_add, hfix]
  rw [show ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w + (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
    w + ((((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
      (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) by abel, ZModModule.add_self, add_zero]

theorem eq_zero_of_mem_axisCore {v : S.Qt} (hv : v ∈ axisCore S A) : v = 0 := by
  by_contra hv0
  set φ := axisForm S A (h * S.z * h⁻¹)
  have hφv : φ ⟨v, hv.1⟩ = 0 := hv.2 h hxQ hxA
  obtain ⟨u, hu, hut⟩ := hA.exists_Ubar_resAt_eq hM hxQ hxA
    (g := LinearEquiv.transvection hφv) fun w hw => by rw [transvection_apply, hw, zero_smul,
      add_zero]
  have happ : ∀ w (hw : w ∈ S.clSub A), (u : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + φ ⟨w, hw⟩ • v := by
    intro w hw
    have := congrArg (fun e => ((e ⟨w, hw⟩ : S.clSub A) : S.Qt)) hut
    simp only [coe_resAt_apply] at this
    rw [this, transvection_apply]
    rfl
  have hmem : (⟨u, Ubar_le_Mbar h hu⟩ : S.Mbar) ∈ coreStab S hM := by
    intro w hw
    refine ⟨?_, fun hwc => ?_⟩
    · change (u : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ _
      rw [happ w hw, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hv
    · change (u : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
      rw [happ w hw, show φ ⟨w, hw⟩ = 0 from hwc.2 h hxQ hxA, zero_smul, add_zero]
  have hle : coreStab S hM ≤ CFSG.pCore 2 S.Mbar :=
    le_sSup ⟨coreStab_normal hM, hA.coreStab_isPGroup hM⟩
  rw [S.pCore_Mbar_eq_bot] at hle
  have hu1 : u = 1 := congrArg Subtype.val ((mem_bot).mp (hle hmem))
  obtain ⟨e, he⟩ : ∃ e : S.clSub A, φ e = 1 := by
    by_contra! hne
    refine hA.axisForm_ne_zero hxQ hxA (LinearMap.ext fun w => ?_)
    rcases zmod_two_eq_zero_or_one (φ w) with h0 | h1
    · exact h0
    · exact absurd h1 (hne w)
  have h2 := happ e e.2
  rw [hu1, show φ ⟨e, e.2⟩ = 1 from he, one_smul] at h2
  exact hv0 (by simpa using h2.symm)

theorem resAt_surjective_of_mem : Function.Surjective (resAt S A hM) := by
  have := finite_clSub (S := S) (A := A)
  have : FiniteDimensional (ZMod 2) (S.clSub A) := Module.Finite.of_finite
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_axes _ {f | ∃ h' : G, h' * S.z * h'⁻¹ ∈ S.QG ∧ h' * S.z * h'⁻¹ ∉ A ∧
    f = axisForm S A (h' * S.z * h'⁻¹)} (fun v hv => ?_) fun f ⟨h', h1, h2, hf⟩ d hd => ?_
  · have hc : (v : S.Qt) ∈ axisCore S A := ⟨v.2, fun h' h1 h2 => hv _ ⟨h', h1, h2, rfl⟩⟩
    exact Subtype.ext (hA.eq_zero_of_mem_axisCore hM hxQ hxA hc)
  · subst hf
    obtain ⟨u, hu, hut⟩ := hA.exists_Ubar_resAt_eq hM h1 h2 (g := LinearEquiv.transvection hd)
      fun w hw => by rw [transvection_apply, hw, zero_smul, add_zero]
    exact ⟨_, ⟨_, hut⟩, fun x => transvection_apply hd x⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
