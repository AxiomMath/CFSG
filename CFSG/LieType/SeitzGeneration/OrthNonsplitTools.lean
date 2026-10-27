module

public import CFSG.LieType.SeitzGeneration.OrthNonsplitDims
public import CFSG.LieType.SeitzGeneration.OrthEx
public import CFSG.LieType.SeitzGeneration.HyperEx

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  OrthBlk

section Hyper

theorem mem_hyperClosure_of_commute {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Y} (hE : Nat.card E = p ^ 3) {a b k : Y} (ha : a ∈ E) (hb : b ∈ E)
    (hab : Commute a b) (hap : a ^ p = 1) (hbp : b ^ p = 1)
    (hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) (hka : Commute k a)
    (hkb : Commute k b) : k ∈ hyperClosure p ⊤ E := by
  obtain ⟨P, -, -, hPcard, hPform⟩ := exists_plane_of_two hp hab hap hbp hind
  have hPE : P ≤ E := fun y hy => by
    obtain ⟨i, j, rfl⟩ := hPform y hy
    exact E.mul_mem (E.zpow_mem ha i) (E.zpow_mem hb j)
  refine Subgroup.subset_closure ⟨Subgroup.mem_top k, P, hPE, ?_, fun f hf => ?_⟩
  · have h := Subgroup.relIndex_mul_card P E
    rw [inf_of_le_left hPE, hPcard, hE] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) ?_
    rw [h]
    ring
  · obtain ⟨i, j, rfl⟩ := hPform f hf
    exact ((hka.zpow_right i).mul_right (hkb.zpow_right j)).eq.symm

end Hyper

namespace OrthNS

section Stab

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def stab (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ u ∈ U, g u ∈ U ∧ g.symm u ∈ U}
  mul_mem' := fun {a b} ha hb u hu => ⟨(ha _ (hb u hu).1).1, (hb _ (ha u hu).2).2⟩
  one_mem' := fun u hu => ⟨hu, hu⟩
  inv_mem' := fun {a} ha u hu => ⟨(ha u hu).2, by
    change a.symm.symm u ∈ U
    rw [LinearEquiv.symm_symm]
    exact (ha u hu).1⟩

theorem mem_stab {U : Submodule K V} {g : V ≃ₗ[K] V} :
    g ∈ stab U ↔ ∀ u ∈ U, g u ∈ U ∧ g.symm u ∈ U := Iff.rfl

@[expose] def res (U : Submodule K V) : stab U →* (U ≃ₗ[K] U) where
  toFun g := restrictEquiv U g.1 (fun u hu => (mem_stab.mp g.2 u hu).1)
    (fun u hu => (mem_stab.mp g.2 u hu).2)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[simp] theorem coe_res_apply (U : Submodule K V) (g : stab U) (u : U) :
    (res U g u : V) = (g : V ≃ₗ[K] V) u := rfl

end Stab

section Ext

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

@[expose] def extU {U : Submodule K V} (hU : PolarNondegOn Q U) :
    (U ≃ₗ[K] U) →* (V ≃ₗ[K] V) where
  toFun a := glue (isCompl_perp hU) a 1
  map_one' := glue_one _
  map_mul' a b := by rw [← glue_mul, one_mul]

theorem extU_def {U : Submodule K V} (hU : PolarNondegOn Q U) (a : U ≃ₗ[K] U) :
    extU hU a = glue (isCompl_perp hU) a 1 := rfl

theorem extU_apply_mem {U : Submodule K V} (hU : PolarNondegOn Q U) (a : U ≃ₗ[K] U) {u : V}
    (hu : u ∈ U) : extU hU a u = (a ⟨u, hu⟩ : V) := by
  have := glue_apply (isCompl_perp hU) a 1 ⟨u, hu⟩ 0
  rw [extU_def]
  simpa using this

theorem extU_apply_perp {U : Submodule K V} (hU : PolarNondegOn Q U) (a : U ≃ₗ[K] U) {r : V}
    (hr : r ∈ perp Q U) : extU hU a r = r := by
  have := glue_apply (isCompl_perp hU) a 1 0 ⟨r, hr⟩
  rw [extU_def]
  simpa using this

theorem extU_injective {U : Submodule K V} (hU : PolarNondegOn Q U) :
    Function.Injective (extU hU) := fun a b hab => LinearEquiv.ext fun u => Subtype.ext (by
  rw [← extU_apply_mem hU a u.2, ← extU_apply_mem hU b u.2, hab])

theorem extU_eq_of_agree {U : Submodule K V} (hU : PolarNondegOn Q U) {a : U ≃ₗ[K] U}
    {g : V ≃ₗ[K] V} (h1 : ∀ u : U, g u = (a u : V)) (h2 : ∀ r ∈ perp Q U, g r = r) :
    extU hU a = g := LinearEquiv.ext fun v => by
  obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hU).sup_eq_top ▸
    Submodule.mem_top (x := v))
  rw [map_add, map_add, extU_apply_perp hU a hr, h2 r hr, extU_apply_mem hU a hu, h1 ⟨u, hu⟩]

theorem extU_mem_eichlerGroupOn {U : Submodule K V} (hU : PolarNondegOn Q U) {a : U ≃ₗ[K] U}
    (ha : a ∈ elementaryGroup (Q.comp U.subtype)) : extU hU a ∈ eichlerGroupOn Q U := by
  obtain ⟨g, hg, hga⟩ := exists_mem_eichlerGroupOn_of_mem_elementaryGroup ha
  rw [extU_eq_of_agree hU hga fun r hr => eichlerGroupOn_apply_of_orth hg fun u' hu' => by
    rw [polar_comm]
    exact mem_perp.mp hr u' hu']
  exact hg

omit [FiniteDimensional K V] in
theorem eichler_comp_subtype_apply {U : Submodule K V} (e w u : U) :
    ((eichler (Q.comp U.subtype) e w u : U) : V) = eichler Q (e : V) (w : V) (u : V) := by
  by_cases h : Q (e : V) = 0 ∧ polar Q (e : V) (w : V) = 0
  · have h' : (Q.comp U.subtype) e = 0 ∧ polar (Q.comp U.subtype) e w = 0 :=
      ⟨h.1, by rw [polar_comp_subtype']; exact h.2⟩
    rw [eichler_apply h.1 h.2, eichler_apply h'.1 h'.2]
    simp only [polar_comp_subtype', QuadraticMap.comp_apply, Submodule.coe_sub,
      Submodule.coe_add, Submodule.coe_smul, Submodule.subtype_apply]
  · have h' : ¬ ((Q.comp U.subtype) e = 0 ∧ polar (Q.comp U.subtype) e w = 0) := fun h'' =>
      h ⟨h''.1, by rw [← polar_comp_subtype']; exact h''.2⟩
    rw [eichler_of_not h, eichler_of_not h']
    rfl

theorem extU_eichler {U : Submodule K V} (hU : PolarNondegOn Q U) (e w : U) :
    extU hU (eichler (Q.comp U.subtype) e w) = eichler Q (e : V) (w : V) := by
  refine extU_eq_of_agree hU (fun u => (eichler_comp_subtype_apply e w u).symm) fun r hr => ?_
  exact eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact mem_perp.mp hr _ e.2)
    (by rw [polar_comm]; exact mem_perp.mp hr _ w.2)

omit [FiniteDimensional K V] in
theorem eichlerGroupOn_le_elementaryGroup (U : Submodule K V) :
    eichlerGroupOn Q U ≤ elementaryGroup Q :=
  eichlerGroupOn_le fun e _ w _ => eichler_mem_elementaryGroup Q e w

theorem commute_of_mem_eichlerGroupOn {U : Submodule K V} (hU : PolarNondegOn Q U)
    {h y : V ≃ₗ[K] V} (hh : h ∈ eichlerGroupOn Q U)
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hyU : y ∈ stab U)
    (hc : ∀ u ∈ U, h (y u) = y (h u)) : Commute h y := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hU).sup_eq_top ▸
    Submodule.mem_top (x := v))
  have hr' := mem_perp.mp hr
  have h2 : h r = r := eichlerGroupOn_apply_of_orth hh fun u' hu' => by
    rw [polar_comm]
    exact hr' u' hu'
  have h3 : h (y r) = y r := eichlerGroupOn_apply_of_orth hh fun u' hu' => by
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hyO r (y.symm u')
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [h1, polar_comm]
    exact hr' _ ((mem_stab.mp hyU) u' hu').2
  simp only [LinearEquiv.mul_apply, map_add, hc u hu, h2, h3]

end Ext

section Singular

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def hypPairSub {W : Submodule K V} (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    HypPair (Q.comp W.subtype) :=
  ⟨⟨P.e, he⟩, ⟨P.f, hf⟩, P.Q_e, P.Q_f, by rw [polar_comp_subtype']; exact P.polar_ef⟩

theorem hypPairSub_orth {W : Submodule K V} {P P' : HypPair Q} (he : P.e ∈ W) (hf : P.f ∈ W)
    (he' : P'.e ∈ W) (hf' : P'.f ∈ W) (h : P.Orth P') :
    (hypPairSub P he hf).Orth (hypPairSub P' he' hf') :=
  ⟨by rw [polar_comp_subtype']; exact h.ee, by rw [polar_comp_subtype']; exact h.ef,
    by rw [polar_comp_subtype']; exact h.fe, by rw [polar_comp_subtype']; exact h.ff⟩

theorem exists_ts_three_comp [Finite K] [FiniteDimensional K V] {W : Submodule K V}
    (hW : PolarNondegOn Q W) (h8 : 8 ≤ finrank K W) :
    ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, (Q.comp W.subtype) x = 0 := by
  obtain ⟨P₁, P₂, P₃, h1e, h1f, h2e, h2f, h3e, h3f, h12, h13, h23⟩ :=
    exists_three_hypPairs_in hW h8
  exact exists_totallySingular_of_hypPairs (hypPairSub_orth h1e h1f h2e h2f h12)
    (hypPairSub_orth h1e h1f h3e h3f h13) (hypPairSub_orth h2e h2f h3e h3f h23)

end Singular

end OrthNS

end CFSG.LieType.SeitzGeneration
