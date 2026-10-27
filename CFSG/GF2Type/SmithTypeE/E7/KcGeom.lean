module

public import CFSG.GF2Type.SmithTypeE.E7.ClsGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

@[expose] def C0 : Submodule (ZMod 2) V12 where
  carrier := {v | v.1 = 0 ∧ v.2 5 = 0}
  add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c v hv => ⟨by simp [hv.1], by simp [hv.2]⟩

theorem mem_C0_iff (v : V12) : v ∈ C0 ↔ v.1 = 0 ∧ v.2 5 = 0 := Iff.rfl

@[expose] def Lin01 : Submodule (ZMod 2) V12 :=
  Submodule.span (ZMod 2) {((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
    ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))}

theorem eq_one_of_ne_zero_zmod2 {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have key : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
  exact key a h

theorem q12_pair_of_off (a b : Fin 6 → ZMod 2) (h : ∀ i, i ≠ 5 → a i = 0) :
    q12 (a, b) = a 5 * b 5 := by
  rw [q12_apply]
  apply Finset.sum_eq_single (5 : Fin 6)
  · intro k _ hk
    show a k * b k = 0
    rw [h k hk, zero_mul]
  · intro h5
    exact absurd (Finset.mem_univ _) h5

theorem zmod2_eq_of_mul_eq_one : ∀ s t : ZMod 2, s * t = 1 → s = t := by decide

theorem C0_le_Cc : C0 ≤ Cc := by
  intro v hv
  obtain ⟨h1, h2⟩ := (mem_C0_iff v).1 hv
  refine (mem_Cc_iff v).2 ⟨fun i _ => ?_, ?_⟩
  · simp [h1]
  · simp [h1, h2]

theorem mem_Cc_iff_perp (v : V12) :
    v ∈ Cc ↔ (∀ y ∈ C0, B12 v y = 0) ∧ (v ∈ C0 ∨ q12 v = 1) := by
  obtain ⟨a, b⟩ := v
  constructor
  · intro hv
    have h1 : ∀ i : Fin 6, i ≠ 5 → a i = 0 := fun i hi => ((mem_Cc_iff (a, b)).1 hv).1 i hi
    have h2 : a 5 = b 5 := ((mem_Cc_iff (a, b)).1 hv).2
    refine ⟨fun y hy => Cc_isotropic hv (C0_le_Cc hy), ?_⟩
    by_cases ha : a 5 = 0
    · left
      refine (mem_C0_iff (a, b)).2 ⟨?_, h2.symm.trans ha⟩
      funext i
      by_cases hi : i = 5
      · subst hi
        exact ha
      · exact h1 i hi
    · right
      rw [q12_pair_of_off a b h1, ← h2, zmod2_mul_self]
      exact eq_one_of_ne_zero_zmod2 ha
  · rintro ⟨hperp, hCq⟩
    have hA : ∀ i : Fin 6, i ≠ 5 → a i = 0 := by
      intro i hi
      have hy : ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) ∈ C0 := by
        refine (mem_C0_iff _).2 ⟨rfl, ?_⟩
        simp [Pi.single_apply, hi, Ne.symm hi]
      have h0 := hperp _ hy
      rwa [B12_zero_single_right] at h0
    refine (mem_Cc_iff (a, b)).2 ⟨hA, ?_⟩
    rcases hCq with hC | hq
    · obtain ⟨h1, h2⟩ := (mem_C0_iff (a, b)).1 hC
      have h1' : a = 0 := h1
      have h2' : b 5 = 0 := h2
      simp [h1', h2']
    · rw [q12_pair_of_off a b hA] at hq
      exact zmod2_eq_of_mul_eq_one _ _ hq

theorem Cc_singular_iff_C0 (v : V12) : (v ∈ Cc ∧ q12 v = 0) ↔ v ∈ C0 := by
  constructor
  · rintro ⟨hv, hq⟩
    exact (mem_C0_iff v).2 ((Cc_singular_iff v hv).1 hq)
  · intro hv
    have hc : v ∈ Cc := C0_le_Cc hv
    exact ⟨hc, (Cc_singular_iff v hc).2 ((mem_C0_iff v).1 hv)⟩

theorem finrank_C0 : Module.finrank (ZMod 2) C0 = 5 := by
  have e : {y : Fin 6 → ZMod 2 // y 5 = 0} ≃ C0 :=
    { toFun := fun y => ⟨(0, y.1), (mem_C0_iff _).2 ⟨rfl, y.2⟩⟩
      invFun := fun v => ⟨v.1.2, ((mem_C0_iff v.1).1 v.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun v => Subtype.ext (Prod.ext ((mem_C0_iff v.1).1 v.2).1.symm rfl) }
  have hcard : Nat.card C0 = 32 := (Nat.card_congr e).symm.trans clsCard_T
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥C0)
  rw [hcard, Nat.card_zmod] at h
  have h5 : (2 : ℕ) ^ Module.finrank (ZMod 2) C0 = 2 ^ 5 := h.symm.trans (by norm_num)
  exact Nat.pow_right_injective (le_refl 2) h5

theorem Lin01_le_C0 : Lin01 ≤ C0 := by
  unfold Lin01
  refine Submodule.span_le.2 ?_
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact SetLike.mem_coe.2 ((mem_C0_iff _).2 ⟨rfl, by simp [Pi.single_apply]⟩)
  · exact SetLike.mem_coe.2 ((mem_C0_iff _).2 ⟨rfl, by simp [Pi.single_apply]⟩)

theorem linearIndependent_Lin01 :
    LinearIndependent (ZMod 2) ![((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
      ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrArg (fun v : V12 => v.2 0) h
  have h1 := congrArg (fun v : V12 => v.2 1) h
  simp [Pi.single_apply] at h0 h1
  exact ⟨h0, h1⟩

theorem finrank_Lin01 : Module.finrank (ZMod 2) Lin01 = 2 := by
  have hr : ({((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
      ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))} : Set V12) =
      Set.range ![((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
        ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))] :=
    (Matrix.range_cons_cons_empty _ _ _).symm
  unfold Lin01
  rw [hr, finrank_span_eq_card linearIndependent_Lin01, Fintype.card_fin]

theorem dec12_64 : dec12 64 = ((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)) := by
  decide

theorem dec12_128 : dec12 128 = ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2)) := by
  decide

theorem le_ker_of_mem_dualAnnihilator {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {U : Submodule (ZMod 2) W} {f : Module.Dual (ZMod 2) W} (hf : f ∈ U.dualAnnihilator) :
    U ≤ LinearMap.ker f := by
  intro w hw
  exact LinearMap.mem_ker.2 ((Submodule.mem_dualAnnihilator f).1 hf w hw)

theorem finrank_ker_add_one {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {f : Module.Dual (ZMod 2) W} (hf : f ≠ 0) :
    Module.finrank (ZMod 2) (LinearMap.ker f) + 1 = Module.finrank (ZMod 2) W := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf (LinearMap.ext fun x => by simp [hcon x])
  have hfw : f w = 1 := eq_one_of_ne_zero_zmod2 hw
  have hsurj : Function.Surjective f := fun c =>
    ⟨c • w, by rw [map_smul, hfw, smul_eq_mul, mul_one]⟩
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hsurj
  have h1 : Module.finrank (ZMod 2) (LinearMap.range f) = 1 := by
    rw [hrange, finrank_top, Module.finrank_self]
  have h2 : Module.finrank (ZMod 2) (LinearMap.range f) +
      Module.finrank (ZMod 2) (LinearMap.ker f) = Module.finrank (ZMod 2) W :=
    LinearMap.finrank_range_add_finrank_ker f
  omega

theorem eq_of_ker_eq_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {f g : Module.Dual (ZMod 2) W} (hk : LinearMap.ker f = LinearMap.ker g) : f = g := by
  have hiff : ∀ w, f w = 0 ↔ g w = 0 := by
    intro w
    constructor
    · intro h
      have hw : w ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
      rw [hk] at hw
      exact LinearMap.mem_ker.1 hw
    · intro h
      have hw : w ∈ LinearMap.ker g := LinearMap.mem_ker.2 h
      rw [← hk] at hw
      exact LinearMap.mem_ker.1 hw
  refine LinearMap.ext fun w => ?_
  by_cases h : f w = 0
  · rw [h, (hiff w).1 h]
  · have hg : g w ≠ 0 := fun h' => h ((hiff w).2 h')
    rw [eq_one_of_ne_zero_zmod2 h, eq_one_of_ne_zero_zmod2 hg]

theorem exists_dual_ker_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {H : Submodule (ZMod 2) W}
    (hH : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W) :
    ∃ f : Module.Dual (ZMod 2) W, LinearMap.ker f = H := by
  have hq0 : Module.finrank (ZMod 2) (W ⧸ H) + Module.finrank (ZMod 2) H =
      Module.finrank (ZMod 2) W :=
    Submodule.finrank_quotient_add_finrank H
  have hq : Module.finrank (ZMod 2) (W ⧸ H) = 1 := by omega
  let e : (W ⧸ H) ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hq])
  refine ⟨(e : (W ⧸ H) →ₗ[ZMod 2] ZMod 2).comp H.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem card_hyperplane_eq_card_dual {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (U : Submodule (ZMod 2) W) :
    Nat.card {H : Submodule (ZMod 2) W //
        U ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W} =
      Nat.card {f : Module.Dual (ZMod 2) W // f ≠ 0 ∧ f ∈ U.dualAnnihilator} := by
  let Φ : {f : Module.Dual (ZMod 2) W // f ≠ 0 ∧ f ∈ U.dualAnnihilator} →
      {H : Submodule (ZMod 2) W //
        U ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W} :=
    fun f => ⟨LinearMap.ker f.1, le_ker_of_mem_dualAnnihilator f.2.2, finrank_ker_add_one f.2.1⟩
  have hinj : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    have hk : LinearMap.ker f.1 = LinearMap.ker g.1 := congrArg Subtype.val hfg
    exact eq_of_ker_eq_zmod2 hk
  have hsurj : Function.Surjective Φ := by
    rintro ⟨H, hUH, hfin⟩
    obtain ⟨f, hfH⟩ := exists_dual_ker_eq hfin
    have hHtop : H ≠ ⊤ := by
      intro hH
      rw [hH, finrank_top] at hfin
      omega
    have hf0 : f ≠ 0 := by
      intro h0
      apply hHtop
      rw [← hfH, h0, LinearMap.ker_zero]
    have hfU : f ∈ U.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      apply LinearMap.mem_ker.1
      rw [hfH]
      exact hUH hw
    exact ⟨⟨f, hf0, hfU⟩, Subtype.ext hfH⟩
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩).symm

theorem card_dualAnnihilator_ne_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (U : Submodule (ZMod 2) W) :
    Nat.card {f : Module.Dual (ZMod 2) W // f ≠ 0 ∧ f ∈ U.dualAnnihilator} =
      2 ^ (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) U) - 1 := by
  classical
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hA : Module.finrank (ZMod 2) U.dualAnnihilator
      = Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) U :=
    Nat.eq_sub_of_add_eq' hdim
  have hcard : Nat.card U.dualAnnihilator
      = 2 ^ (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hA, Nat.card_zmod]
  haveI : Finite U.dualAnnihilator := Module.finite_of_finite (R := ZMod 2)
  let e : {f : Module.Dual (ZMod 2) W // f ≠ 0 ∧ f ∈ U.dualAnnihilator} ≃
      {a : U.dualAnnihilator // a ≠ 0} :=
    { toFun := fun f => ⟨⟨f.1, f.2.2⟩, fun h => f.2.1 (congrArg Subtype.val h)⟩
      invFun := fun a => ⟨a.1.1, fun h => a.2 (Subtype.ext h), a.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hopt : Nat.card (Option {a : U.dualAnnihilator // a ≠ 0})
      = Nat.card U.dualAnnihilator :=
    Nat.card_congr (Equiv.optionSubtypeNe (0 : U.dualAnnihilator))
  rw [Finite.card_option, hcard] at hopt
  rw [Nat.card_congr e]
  exact Nat.eq_sub_of_add_eq hopt

theorem map_comap_subtype_of_le {W H : Submodule (ZMod 2) V12} (hHW : H ≤ W) :
    (H.comap W.subtype).map W.subtype = H := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hHW]

theorem card_between_eq {W U : Submodule (ZMod 2) V12} (hUW : U ≤ W)
    (hW : Module.finrank (ZMod 2) W = 6) :
    Nat.card {H : Submodule (ZMod 2) V12 //
        U ≤ H ∧ H ≤ W ∧ Module.finrank (ZMod 2) H = 5} =
      Nat.card {H : Submodule (ZMod 2) W //
        U.comap W.subtype ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W} := by
  have hsub : Function.Injective W.subtype := Submodule.injective_subtype W
  have hU : (U.comap W.subtype).map W.subtype = U := map_comap_subtype_of_le hUW
  have fwd : ∀ H : {H : Submodule (ZMod 2) V12 // U ≤ H ∧ H ≤ W ∧ Module.finrank (ZMod 2) H = 5},
      U.comap W.subtype ≤ H.1.comap W.subtype ∧
        Module.finrank (ZMod 2) (H.1.comap W.subtype) + 1 = Module.finrank (ZMod 2) W := by
    intro H
    obtain ⟨hUH, hHW, hH⟩ := H.2
    refine ⟨Submodule.comap_mono hUH, ?_⟩
    have h1 : Module.finrank (ZMod 2) (H.1.comap W.subtype) = Module.finrank (ZMod 2) H.1 :=
      (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq
    omega
  have bwd : ∀ H' : {H : Submodule (ZMod 2) W //
      U.comap W.subtype ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W},
      U ≤ H'.1.map W.subtype ∧ H'.1.map W.subtype ≤ W ∧
        Module.finrank (ZMod 2) (H'.1.map W.subtype) = 5 := by
    intro H'
    obtain ⟨hUH', hH'⟩ := H'.2
    refine ⟨?_, Submodule.map_subtype_le W H'.1, ?_⟩
    · calc U = (U.comap W.subtype).map W.subtype := hU.symm
        _ ≤ H'.1.map W.subtype := Submodule.map_mono hUH'
    · have h1 : Module.finrank (ZMod 2) (H'.1.map W.subtype) = Module.finrank (ZMod 2) H'.1 :=
        Submodule.finrank_map_subtype_eq W H'.1
      omega
  exact Nat.card_congr
    { toFun := fun H => ⟨H.1.comap W.subtype, (fwd H).1, (fwd H).2⟩
      invFun := fun H' => ⟨H'.1.map W.subtype, (bwd H').1, (bwd H').2.1, (bwd H').2.2⟩
      left_inv := fun H => Subtype.ext (map_comap_subtype_of_le H.2.2.1)
      right_inv := fun H' => Subtype.ext (Submodule.comap_map_eq_of_injective hsub H'.1) }

theorem card_hyperplanes {W U : Submodule (ZMod 2) V12} (hUW : U ≤ W)
    (hW : Module.finrank (ZMod 2) W = 6) (hU : Module.finrank (ZMod 2) U = 2) :
    Nat.card {H : Submodule (ZMod 2) V12 //
      U ≤ H ∧ H ≤ W ∧ Module.finrank (ZMod 2) H = 5} = 15 := by
  rw [card_between_eq hUW hW, card_hyperplane_eq_card_dual, card_dualAnnihilator_ne_zero]
  have h1 : Module.finrank (ZMod 2) (U.comap W.subtype) = Module.finrank (ZMod 2) U :=
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq
  rw [h1, hU, hW]
  norm_num

section Cert


theorem C0_le_F : C0 ≤ planeSub 0 := by
  intro v hv
  exact mem_F_iff.2 ((mem_C0_iff v).1 hv).1

theorem finrank_comap_inr_of_le_F {P : Submodule (ZMod 2) V12} (hP : P ≤ planeSub 0) :
    Module.finrank (ZMod 2)
        (P.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))) =
      Module.finrank (ZMod 2) P := by
  have hmap : (P.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))).map
      (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)) = P := by
    rw [Submodule.map_comap_eq, inf_eq_right]
    intro z hz
    exact LinearMap.mem_range.mpr ⟨z.2, Prod.ext (mem_F_iff.mp (hP hz)).symm rfl⟩
  have e := Submodule.equivMapOfInjective
    (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))
    LinearMap.inr_injective
    (P.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)))
  rw [LinearEquiv.finrank_eq e, hmap]

theorem exists_linearEquiv_map_eq {V5 H1 : Submodule (ZMod 2) (Fin 6 → ZMod 2)}
    (h : Module.finrank (ZMod 2) V5 = Module.finrank (ZMod 2) H1) :
    ∃ g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
      (∀ y ∈ V5, g y ∈ H1) ∧ ∀ z ∈ H1, ∃ y ∈ V5, g y = z := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq V5 H1 h)
  refine ⟨g, fun y hy => ?_, fun z hz => ?_⟩
  · have h1 : g y = (LinearEquiv.ofFinrankEq V5 H1 h ⟨y, hy⟩ : Fin 6 → ZMod 2) :=
      (hg ⟨y, hy⟩).symm
    rw [h1]
    exact (LinearEquiv.ofFinrankEq V5 H1 h ⟨y, hy⟩).2
  · obtain ⟨x, hx⟩ := (LinearEquiv.ofFinrankEq V5 H1 h).surjective ⟨z, hz⟩
    exact ⟨x.1, x.2, (hg x).symm.trans (congrArg Subtype.val hx)⟩

theorem exists_GL6_mulVec_eq (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    ∃ A : GL6, ∀ y, (A : M6) *ᵥ y = g y := by
  have hc : (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)).comp
      (g.symm : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) = LinearMap.id :=
    LinearMap.ext fun y => g.apply_symm_apply y
  have hc' : (g.symm : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)).comp
      (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) = LinearMap.id :=
    LinearMap.ext fun y => g.symm_apply_apply y
  have h1 : LinearMap.toMatrix' (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) *
      LinearMap.toMatrix' (g.symm : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have h2 : LinearMap.toMatrix' (g.symm : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) *
      LinearMap.toMatrix' (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  refine ⟨Units.mk _ _ h1 h2, fun y => ?_⟩
  exact LinearMap.toMatrix'_mulVec (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) y

theorem exists_stab0_map_C0_aux {H : Submodule (ZMod 2) V12} (hH : H ≤ planeSub 0)
    (hfin : Module.finrank (ZMod 2) H = 5)
    (hC0F : C0 ≤ planeSub 0) (hC0 : Module.finrank (ZMod 2) C0 = 5) :
    ∃ τ : Stab0, C0.map (sig τ.1).toLinearMap = H := by
  obtain ⟨g, hg1, hg2⟩ := exists_linearEquiv_map_eq
    (V5 := C0.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)))
    (H1 := H.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)))
    (by rw [finrank_comap_inr_of_le_F hC0F, finrank_comap_inr_of_le_F hH, hC0, hfin])
  obtain ⟨A, hA⟩ := exists_GL6_mulVec_eq g
  obtain ⟨τ, hτ, hAτ⟩ := exists_mem_stab0_Ablk_eq A
  have hsig : ∀ y, sig τ (0, y) = (0, g y) := fun y => by
    rw [apply_F (sig τ) (stab_F hτ) y, hAτ, hA y]
  refine ⟨⟨τ, hτ⟩, ?_⟩
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv0 : v = (0, v.2) := Prod.ext ((mem_C0_iff v).mp hv).1 rfl
    have hyC : v.2 ∈ C0.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)) :=
      Submodule.mem_comap.mpr (by rw [LinearMap.inr_apply, ← hv0]; exact hv)
    show sig τ v ∈ H
    rw [hv0, hsig]
    exact Submodule.mem_comap.mp (hg1 _ hyC)
  · intro hz
    have hz0 : z = (0, z.2) := Prod.ext (mem_F_iff.mp (hH hz)) rfl
    have hz2 : z.2 ∈ H.comap (LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)) :=
      Submodule.mem_comap.mpr (by rw [LinearMap.inr_apply, ← hz0]; exact hz)
    obtain ⟨y, hy, hgy⟩ := hg2 _ hz2
    refine Submodule.mem_map.mpr ⟨(0, y), Submodule.mem_comap.mp hy, ?_⟩
    show sig τ (0, y) = z
    rw [hsig, hgy]
    exact hz0.symm

theorem exists_stab0_map_C0 {H : Submodule (ZMod 2) V12} (hH : H ≤ planeSub 0)
    (hfin : Module.finrank (ZMod 2) H = 5) :
    ∃ τ : Stab0, C0.map (sig τ.1).toLinearMap = H :=
  exists_stab0_map_C0_aux hH hfin C0_le_F finrank_C0

end Cert

end CFSG.GF2Type.SmithTypeE.E7
