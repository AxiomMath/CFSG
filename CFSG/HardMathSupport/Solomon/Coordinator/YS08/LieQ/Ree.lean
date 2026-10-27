module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeStd
public import CFSG.LieType.ChevTwo.OppositeFixedExcBase

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.Open CFSG.LieType.ChevTwo.Semi

set_option linter.unusedSectionVars false

section Ree

@[expose] def ReeLIAt (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)
    (j : Fin ReeTag.F4.fixedOrbitCount) : Prop :=
  ∀ x : ↥(ReeTag.F4.reeGamma K a),
    (∀ r ∈ reeQJ ReeTag.F4 K a (some j), x * r = r * x) → x ∈ reeQJ ReeTag.F4 K a (some j)

@[expose] def ReeLI (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ) : Prop :=
  ∀ j : Fin ReeTag.F4.fixedOrbitCount, ReeLIAt K a j

@[expose] def ReeLIOddAt (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)
    (j : Fin ReeTag.F4.fixedOrbitCount) : Prop :=
  ∀ x : ↥(ReeTag.F4.reeGamma K a), Nat.Coprime (orderOf x) 2 →
    (∀ r ∈ reeQJ ReeTag.F4 K a (some j), x * r = r * x) → x = 1

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeQJ_some_le_none (j : Fin ReeTag.F4.fixedOrbitCount) :
    reeQJ ReeTag.F4 K a (some j) ≤ reeQJ ReeTag.F4 K a none := fun x hx =>
  mem_reeQJ.2 (reeStd_posUnipotent_le_parabolicRadical_empty
    (parabolicRadical_le_posUnipotent _ (mem_reeQJ.1 hx)))

theorem reeLI_none (h : ReeLI K a) (x : ↥(ReeTag.F4.reeGamma K a))
    (hx : ∀ r ∈ reeQJ ReeTag.F4 K a none, x * r = r * x) : x ∈ reeQJ ReeTag.F4 K a none :=
  reeQJ_some_le_none ⟨0, by decide⟩
    (h ⟨0, by decide⟩ x fun r hr => hx r (reeQJ_some_le_none _ hr))

theorem reeGamma_centralizer_le (h : ReeLI K a) {R : Subgroup ↥(ReeTag.F4.reeGamma K a)}
    (hR : IsRadical 2 R) : ∀ x, (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  obtain ⟨h0, hp, hc, -⟩ := hR
  obtain ⟨g, j, hN, hQ⟩ := ree_standard_position (t := ReeTag.F4) R h0 hp
  obtain ⟨hRQ, -⟩ := CFSG.LieType.ChevTwo.std_position g hc (ree_QJ_pgroup j)
    (ree_PJ_le_normalizer j) hN hQ
  have hLIj : ∀ y : ↥(ReeTag.F4.reeGamma K a),
      (∀ r ∈ reeQJ ReeTag.F4 K a j, y * r = r * y) → y ∈ reeQJ ReeTag.F4 K a j := by
    cases j with
    | none => exact reeLI_none h
    | some j => exact h j
  intro x hx
  have hy : ∀ r ∈ reeQJ ReeTag.F4 K a j, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
    intro r hr
    rw [← hRQ] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have hs' := hx s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hs']
      _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group
  have h1 := hLIj (g⁻¹ * x * g) hy
  rw [← hRQ] at h1
  obtain ⟨s, hs, hse⟩ := h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hse
  have : x = s := by
    have h2 : g * (g⁻¹ * s * g) * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hse]
    simpa using h2.symm
  rw [this]
  exact hs

theorem radRigidInner_reeGamma_of_oddLI (h : ∀ j, ReeLIOddAt K a j) :
    RadRigidInner 2 ↥(ReeTag.F4.reeGamma K a) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  intro R hR x hx hxo
  obtain ⟨h0, hp, hc, -⟩ := hR
  obtain ⟨g, j, hN, hQ⟩ := ree_standard_position (t := ReeTag.F4) R h0 hp
  obtain ⟨hRQ, -⟩ := CFSG.LieType.ChevTwo.std_position g hc (ree_QJ_pgroup j)
    (ree_PJ_le_normalizer j) hN hQ
  have hy : ∀ r ∈ reeQJ ReeTag.F4 K a j, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
    intro r hr
    rw [← hRQ] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have hs' := hx s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hs']
      _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group
  have hyo : Nat.Coprime (orderOf (g⁻¹ * x * g)) 2 := by
    have h1 : orderOf (g⁻¹ * x * g) = orderOf x := by simpa using orderOf_conj_eq g⁻¹ x
    rwa [h1]
  have h1 : g⁻¹ * x * g = 1 := by
    cases j with
    | none => exact h ⟨0, by decide⟩ _ hyo fun r hr => hy r (reeQJ_some_le_none _ hr)
    | some j => exact h j _ hyo hy
  have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [h1] at this
  simpa using this

theorem closure_reePJ_eq_top :
    Subgroup.closure (⋃ j : Fin ReeTag.F4.fixedOrbitCount,
      (reePJ ReeTag.F4 K a (some j) : Set ↥(ReeTag.F4.reeGamma K a))) = ⊤ := by
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup ↥(ReeTag.F4.reeGamma K a), Y = Subgroup.closure
      (⋃ j : Fin ReeTag.F4.fixedOrbitCount,
        (reePJ ReeTag.F4 K a (some j) : Set ↥(ReeTag.F4.reeGamma K a))) := ⟨_, rfl⟩
  rw [← hY]
  have hPY : ∀ j : Fin ReeTag.F4.fixedOrbitCount, reePJ ReeTag.F4 K a (some j) ≤ Y :=
    fun j x hx => by
      rw [hY]
      exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨j, hx⟩)
  obtain ⟨Y', hY'⟩ : ∃ Y' : Subgroup (ModGL ReeTag.F4.tag K),
      Y' = Y.map (ReeTag.F4.reeGamma K a).subtype := ⟨_, rfl⟩
  have hYle : Y' ≤ ReeTag.F4.reeGamma K a := by
    rw [hY']
    exact Subgroup.map_subtype_le Y
  have hmem : ∀ x : ↥(ReeTag.F4.reeGamma K a), x ∈ Y → (x : ModGL ReeTag.F4.tag K) ∈ Y' :=
    fun x hx => by
      rw [hY']
      exact ⟨x, hx, rfl⟩
  have hP : ∀ (j : Fin ReeTag.F4.fixedOrbitCount) (x : ModGL ReeTag.F4.tag K),
      x ∈ ReeTag.F4.reeParabolic K a {j} → x ∈ Y' := by
    intro j x hx
    have hxΓ : x ∈ ReeTag.F4.reeGamma K a := reeParabolic_le ReeTag.F4 K a _ hx
    refine hmem ⟨x, hxΓ⟩ (hPY j ?_)
    rw [reePJ_some]
    exact Subgroup.mem_subgroupOf.2 hx
  have hB : ReeTag.F4.reeFixedBorel K a ≤ Y' := fun b hb =>
    hP ⟨0, by decide⟩ b (reeFixedBorel_le_reeParabolic ReeTag.F4 K a _ hb)
  obtain ⟨h1, -⟩ := ree_Borel_overgroup_classification ReeTag.F4 a K Y' hB hYle
  have hu : {j | canonicalRep (coxeterSystem ReeTag.F4.tag) K
      (ReeTag.F4.fixedOrbitElement j) ∈ Y'} = Set.univ :=
    Set.eq_univ_of_forall fun j =>
      hP j _ (canonicalRep_mem_reeParabolic ReeTag.F4 K a (Set.mem_singleton j))
  rw [hu] at h1
  have hΓP : ReeTag.F4.reeGamma K a = ReeTag.F4.reeParabolic K a Set.univ := by
    obtain ⟨h, -⟩ := ree_Borel_overgroup_classification ReeTag.F4 a K (ReeTag.F4.reeGamma K a)
      reeFixedBorel_le_reeGamma le_rfl
    have hu' : {j | canonicalRep (coxeterSystem ReeTag.F4.tag) K
        (ReeTag.F4.fixedOrbitElement j) ∈ ReeTag.F4.reeGamma K a} = Set.univ :=
      Set.eq_univ_of_forall fun j =>
        (canonicalRep_mem_reeFixedMonomial ReeTag.F4 K a (ReeTag.fixedOrbitElement_mem j)).2
    rw [hu'] at h
    exact h
  rw [eq_top_iff]
  intro x _
  have hx : (x : ModGL ReeTag.F4.tag K) ∈ Y' := by
    rw [h1, ← hΓP]
    exact x.2
  rw [hY'] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem radicalGen_reeGamma (h : ReeLI K a) (U : Sylow 2 ↥(ReeTag.F4.reeGamma K a)) :
    RadicalGen 2 ↥(ReeTag.F4.reeGamma K a) (U : Subgroup ↥(ReeTag.F4.reeGamma K a)) := by
  have hUp := isPGroup_reeFixedPosUnipotent_subgroupOf (t := ReeTag.F4) (K := K) (a := a)
  have hUi := not_dvd_index_reeFixedPosUnipotent (t := ReeTag.F4) (K := K) (a := a)
  refine RadicalGen.of_sylow (hUp.toSylow hUi) ?_ U
  unfold RadicalGen
  rw [eq_top_iff, ← closure_reePJ_eq_top (K := K) (a := a)]
  refine Subgroup.closure_mono ?_
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  refine ⟨reeQJ ReeTag.F4 K a (some j), ree_QJ_pgroup _, ?_, h j, ree_PJ_le_normalizer _ hj⟩
  show reeQJ ReeTag.F4 K a (some j) ≤
    (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a)
  rw [← reeQJ_none]
  exact reeQJ_some_le_none j

theorem radRigid_reeGamma_of_LI (h : ReeLI K a) : RadRigid 2 ↥(ReeTag.F4.reeGamma K a) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  exact radRigid_of_gen (q := 2) ((holds_reeGamma ReeTag.F4 K a).holdsTits : HoldsTits _ 2)
    (fun R hR => reeGamma_centralizer_le h hR) (radicalGen_reeGamma h)

end Ree

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
