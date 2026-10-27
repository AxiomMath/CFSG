module

public import CFSG.LieType.Chevalley.RootOps.CommAll

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

namespace RootOperatorFamily

variable
    (F : RootOperatorFamily τ) (R : Type) [CommRing R]

@[expose] def eltUnitHom (α : Root τ) :
    Multiplicative R →* (Module.End R (RootModule τ R))ˣ where
  toFun c := F.eltUnit R α c.toAdd
  map_one' := F.eltUnit_zero α
  map_mul' c d := F.eltUnit_add α c.toAdd d.toAdd

@[expose] def ringRootSubgroup
    (α : Root τ) : Subgroup (Module.End R (RootModule τ R))ˣ :=
  (F.eltUnitHom R α).range

variable {F R}

theorem mem_ringRootSubgroup
    {α : Root τ} {g : (Module.End R (RootModule τ R))ˣ} :
    g ∈ F.ringRootSubgroup R α ↔ ∃ c : R, F.eltUnit R α c = g :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem eltUnit_mem_ringRootSubgroup
    (α : Root τ) (c : R) :
    F.eltUnit R α c ∈ F.ringRootSubgroup R α :=
  mem_ringRootSubgroup.2 ⟨c, rfl⟩

theorem map_conj_ringRootSubgroup
    {α β : Root τ} (g : (Module.End R (RootModule τ R))ˣ)
    {u : R → R} (hu : Function.Surjective u)
    (h : ∀ c, g * F.eltUnit R α c * g⁻¹ = F.eltUnit R β (u c)) :
    (F.ringRootSubgroup R α).map (MulAut.conj g).toMonoidHom = F.ringRootSubgroup R β := by
  ext x
  simp only [Subgroup.mem_map, mem_ringRootSubgroup, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨u c, (h c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨c', rfl⟩ := hu c
    exact ⟨_, ⟨c', rfl⟩, h c'⟩

theorem map_conj_weylElt_ringRootSubgroup
    (i : Fin τ.rank) (α : Root τ) :
    (F.ringRootSubgroup R α).map (MulAut.conj (weylElt τ R i 1)).toMonoidHom =
      F.ringRootSubgroup R (simple τ i • α) :=
  F.map_conj_ringRootSubgroup _ (u := fun c => (F.sign i α : R) * c)
    (fun c => ⟨(F.sign i α : R) * c, by
      beta_reduce
      rw [← mul_assoc, F.sign_cast_mul_self, one_mul]⟩)
    (F.weylElt_mul_eltUnit_mul_inv i α)

variable (F R) in
@[expose] def RingCommContained
    (α β : Root τ) : Prop :=
  ∀ x ∈ F.ringRootSubgroup R α, ∀ y ∈ F.ringRootSubgroup R β, x * y * x⁻¹ * y⁻¹ ∈
    ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      F.ringRootSubgroup R γ

theorem ringCommContained_iff
    {α β : Root τ} :
    F.RingCommContained R α β ↔ ∀ c d : R,
      F.eltUnit R α c * F.eltUnit R β d * (F.eltUnit R α c)⁻¹ * (F.eltUnit R β d)⁻¹ ∈
        ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
          F.ringRootSubgroup R γ := by
  constructor
  · exact fun h c d =>
      h _ (F.eltUnit_mem_ringRootSubgroup α c) _ (F.eltUnit_mem_ringRootSubgroup β d)
  · intro h x hx y hy
    obtain ⟨c, rfl⟩ := mem_ringRootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_ringRootSubgroup.1 hy
    exact h c d

theorem RingCommContained.symm
    {α β : Root τ} (h : F.RingCommContained R α β) :
    F.RingCommContained R β α := by
  intro y hy x hx
  have hmem := inv_mem (h x hx y hy)
  rw [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at hmem
  have hle : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      F.ringRootSubgroup R γ) ≤
      ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • β.1 + b • α.1),
        F.ringRootSubgroup R γ :=
    biSup_mono fun γ ⟨a, b, ha, hb, hγ⟩ => ⟨b, a, hb, ha, by rw [hγ, add_comm]⟩
  exact hle hmem

theorem map_conj_weylElt_iSup_ringRootSubgroup
    (i : Fin τ.rank) (P : Root τ → Prop) :
    (⨆ (γ : Root τ) (_ : P γ), F.ringRootSubgroup R γ).map
        (MulAut.conj (weylElt τ R i 1)).toMonoidHom =
      ⨆ (γ : Root τ) (_ : P ((simple τ i)⁻¹ • γ)), F.ringRootSubgroup R γ := by
  simp only [Subgroup.map_iSup, F.map_conj_weylElt_ringRootSubgroup]
  apply le_antisymm
  · exact iSup₂_le fun γ hγ =>
      le_iSup₂_of_le (simple τ i • γ) (by rwa [inv_smul_smul]) le_rfl
  · refine iSup₂_le fun γ hγ => le_iSup₂_of_le ((simple τ i)⁻¹ • γ) hγ ?_
    rw [smul_inv_smul]

theorem ring_comm_transport
    (i : Fin τ.rank) {α β : Root τ} (h : F.RingCommContained R α β) :
    F.RingCommContained R (simple τ i • α) (simple τ i • β) := by
  intro x hx y hy
  rw [← F.map_conj_weylElt_ringRootSubgroup] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj (weylElt τ R i 1)).toMonoidHom
    (h x hx y hy)
  rw [F.map_conj_weylElt_iSup_ringRootSubgroup, map_mul, map_mul, map_mul, map_inv,
    map_inv] at hmem
  have hle : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      ((simple τ i)⁻¹ • γ).1 = a • α.1 + b • β.1), F.ringRootSubgroup R γ) ≤
      ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
        γ.1 = a • (simple τ i • α).1 + b • (simple τ i • β).1), F.ringRootSubgroup R γ := by
    refine biSup_mono fun γ ⟨a, b, ha, hb, hγ⟩ => ⟨a, b, ha, hb, ?_⟩
    rw [coe_smul_root] at hγ
    rw [coe_smul_root, coe_smul_root, ← smul_inv_smul (simple τ i) γ.1, hγ, smul_add,
      smul_comm (simple τ i) a, smul_comm (simple τ i) b]
  exact hle hmem

theorem ring_comm_transport_list
    (l : List (Fin τ.rank)) {α β : Root τ}
    (h : F.RingCommContained R α β) :
    F.RingCommContained R ((l.map (simple τ)).prod • α) ((l.map (simple τ)).prod • β) := by
  induction l with
  | nil => simpa using h
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, mul_smul]
    exact F.ring_comm_transport i ih

end RootOperatorFamily

namespace RootOps

open RootWalk

variable (R : Type) [CommRing R]

@[expose] noncomputable def factorsUnit
    (fs : List Factor) (c d : R) :
    (Module.End R (RootModule τ R))ˣ :=
  (fs.map fun f => if h : f.2.2.1 < τ.rootCertificate.roots.length then
    (rootOperatorFamily τ).eltUnit R (rootAt τ f.2.2.1 h) ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)
    else 1).prod

theorem coe_factorsUnit
    (fs : List Factor) (c d : R) :
    ((factorsUnit (τ := τ) R fs c d : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) = factorsProd τ R fs c d := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [factorsUnit, List.map_cons, List.prod_cons, ← factorsUnit, factorsProd_cons,
      Units.val_mul, ih]
    split_ifs <;> rfl

theorem ringCommContained_of_repCheck
    (hv : allValid τ = true) {a b : ℕ} {fs : List Factor}
    (h : repCheck τ a b fs = true) (α β : Root τ) (ha : rootPos α = a) (hb : rootPos β = b) :
    (rootOperatorFamily τ).RingCommContained R α β := by
  have hcone : ∀ f ∈ fs, coneOk τ a b f = true := by
    simp only [repCheck, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1.2
  rw [RootOperatorFamily.ringCommContained_iff]
  intro c d
  set F := rootOperatorFamily τ
  have hop := elt_mul_elt_of_repCheck (R := R) hv h α β ha hb c d
  have hgrp : F.eltUnit R α c * F.eltUnit R β d * (F.eltUnit R α c)⁻¹ *
      (F.eltUnit R β d)⁻¹ = factorsUnit R fs c d := by
    have : F.eltUnit R α c * F.eltUnit R β d =
        factorsUnit R fs c d * F.eltUnit R β d * F.eltUnit R α c := by
      refine Units.ext ?_
      simp only [Units.val_mul, RootOperatorFamily.coe_eltUnit, coe_factorsUnit]
      exact hop
    rw [this]
    group
  rw [hgrp]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
  have hc := hcone f hf
  simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨⟨⟨hg, hp⟩, hq⟩, hv'⟩ := hc
  simp only [hg, ↓reduceDIte]
  refine (le_iSup₂ (f := fun (γ : Root τ)
    (_ : ∃ a' b' : ℕ, 1 ≤ a' ∧ 1 ≤ b' ∧ γ.1 = a' • α.1 + b' • β.1) => F.ringRootSubgroup R γ)
    (rootAt τ f.2.2.1 hg) ⟨f.1, f.2.1, hp, hq, ?_⟩) (F.eltUnit_mem_ringRootSubgroup _ _)
  rw [CFSG.LieType.Ree.vecBEq_iff] at hv'
  rw [← root_rootPos α, ← root_rootPos β, ha, hb]
  exact hv'

theorem ringCommContained_of_checks
    (hv : allValid τ = true) (htab : tabCheck τ = true)
    {reps : List (ℕ × ℕ × List Factor)} {cover : List ℕ} (hreps : repsCheck τ reps = true)
    (hcover : coverCheck τ reps cover = true) (i : Fin τ.rank) (β : Root τ)
    (hβ : 0 < height β.1) (hne : β ≠ simpleRoot τ i) :
    (rootOperatorFamily τ).RingCommContained R (simpleRoot τ i) β := by
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hcover
  obtain ⟨hpairs, hwalk⟩ := hcover
  have hmem := mem_neededPairs i β hβ hne
  rw [← hpairs, List.mem_map] at hmem
  obtain ⟨e, he, hpe⟩ := hmem
  obtain ⟨hr, hw⟩ := hwalk e he
  set x := reps.getD (coverRep e) (0, 0, []) with hx
  have hxmem : x ∈ reps := by
    rw [hx, List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hrep : repCheck τ x.1 x.2.1 x.2.2 = true := by
    simp only [repsCheck, List.all_eq_true] at hreps
    exact hreps x hxmem
  have hab : x.1 < τ.rootCertificate.roots.length ∧ x.2.1 < τ.rootCertificate.roots.length := by
    simp only [repCheck, Bool.and_eq_true, Nat.blt_eq] at hrep
    exact ⟨hrep.1.1.1, hrep.1.1.2⟩
  have hcomm := ringCommContained_of_repCheck R hv hrep (rootAt τ x.1 hab.1)
    (rootAt τ x.2.1 hab.2) (rootPos_rootAt _) (rootPos_rootAt _)
  set w := decodeWord τ 64 (coverWord e)
  have ht := (rootOperatorFamily τ).ring_comm_transport_list w hcomm
  obtain ⟨-, -, h3, h4⟩ := walkPair_spec htab w hab.1 hab.2
  have hw' : walkPair τ w (x.1, x.2.1) = ((i : ℕ), rootPos β) := by
    rw [← hpe]
    exact hw
  rw [hw'] at h3 h4
  obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have e1 : (w.map (simple τ)).prod • rootAt τ x.1 hab.1 = simpleRoot τ i := by
    apply Subtype.ext
    rw [coe_smul_root]
    exact h3.symm.trans (hb i)
  have e2 : (w.map (simple τ)).prod • rootAt τ x.2.1 hab.2 = β := by
    apply Subtype.ext
    rw [coe_smul_root]
    exact h4.symm.trans (root_rootPos β)
  rwa [e1, e2] at ht

end RootOps

theorem ringCommContained_simpleRoot
    (τ : Tag) (R : Type) [CommRing R] (i : Fin τ.rank)
    (β : Root τ) (hβ : 0 < height β.1) (hne : β ≠ simpleRoot τ i) :
    (rootOperatorFamily τ).RingCommContained R (simpleRoot τ i) β :=
  RootOps.ringCommContained_of_checks R (RootOps.dataChecks τ).valid (RootOps.dataChecks τ).tab
    (RootOps.repsCheck_repsOf τ) (RootOps.coverCheck_coverOf τ) i β hβ hne

theorem ringCommContained_pos
    (R : Type) [CommRing R] (α β : Root τ) (hα : 0 < height α.1)
    (hβ : 0 < height β.1) (hne : α ≠ β) : (rootOperatorFamily τ).RingCommContained R α β := by
  induction h : (height α.1).toNat using Nat.strong_induction_on generalizing α β with
  | _ n ih =>
    by_cases hs : ∃ i, α = simpleRoot τ i
    · obtain ⟨i, rfl⟩ := hs
      exact ringCommContained_simpleRoot τ R i β hβ (Ne.symm hne)
    push Not at hs
    have hns : ∀ i, α.1 ≠ Pi.single i 1 := fun i h => hs i (Subtype.ext h)
    obtain ⟨i, hr, hrpos, hrlt⟩ := exists_reflect_height_lt α.2 hα hns
    by_cases hb : β = simpleRoot τ i
    · subst hb
      exact (ringCommContained_simpleRoot τ R i α hα hne).symm
    have hβ' : 0 < height (reflect τ i β.1) :=
      height_reflect_pos β.2 hβ fun h => hb (Subtype.ext h)
    have hne' : simple τ i • α ≠ simple τ i • β := fun h => hne (smul_left_cancel _ h)
    have hrec := ih (height (reflect τ i α.1)).toNat (by omega) (simple τ i • α)
      (simple τ i • β) (by rw [coe_smul_root, simple_smul]; exact hrpos)
      (by rw [coe_smul_root, simple_smul]; exact hβ') hne' (by rw [coe_smul_root, simple_smul])
    have := (rootOperatorFamily τ).ring_comm_transport i hrec
    rwa [smul_smul, (coxeterSystem τ).simple_mul_simple_self, one_smul, smul_smul,
      (coxeterSystem τ).simple_mul_simple_self, one_smul] at this

end CFSG.LieType.Chevalley
