module

public import CFSG.LieType.Chevalley.A2Commutator
public import CFSG.LieType.Chevalley.SimplyLacedCommutation
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix
open scoped commutatorElement

variable {τ : Tag}

theorem commutatorElement_mul_mul {G : Type*} [Group G] {y y' a a' : G} (h1 : Commute y' a)
    (h2 : Commute y a') (h3 : Commute y ⁅y', a'⁆) (h4 : Commute a ⁅y', a'⁆) :
    ⁅y * y', a * a'⁆ = ⁅y, a⁆ * ⁅y', a'⁆ := by
  set z := ⁅y', a'⁆ with hz
  have k1 : y' * a * y'⁻¹ = a := by rw [h1.eq]; group
  have k2 : y' * a' * y'⁻¹ = z * a' := by rw [hz, commutatorElement_def]; group
  have k3 : y * z * y⁻¹ = z := by rw [h3.eq]; group
  have k4 : y * a' * y⁻¹ = a' := by rw [h2.eq]; group
  have k5 : z * a⁻¹ = a⁻¹ * z := (h4.symm.inv_right).eq
  calc ⁅y * y', a * a'⁆ = y * ((y' * a * y'⁻¹) * (y' * a' * y'⁻¹)) * y⁻¹ * a'⁻¹ * a⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (y * a * y⁻¹) * (y * z * y⁻¹) * (y * a' * y⁻¹) * a'⁻¹ * a⁻¹ := by
        rw [k1, k2]; group
    _ = (y * a * y⁻¹) * (z * a⁻¹) := by rw [k3, k4]; group
    _ = ⁅y, a⁆ * z := by rw [k5, commutatorElement_def]; group

theorem rootForm_comm (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (u v : Fin τ.rank → ℤ) :
    u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) = v ⬝ᵥ (τ.symmetrizedCartan *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, symmetrizedCartan_transpose hτ, dotProduct_comm]

theorem not_isRoot_nsmul_add_nsmul_of_rootForm_nonneg
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h0 : 0 ≤ α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • α + b • β) := by
  intro h
  have hγ := rootForm_self hτ h
  have h0' : 0 ≤ β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α) := by rw [rootForm_comm hτ]; exact h0
  rw [← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β] at hγ
  simp only [add_dotProduct, dotProduct_add, mulVec_add, mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, rootForm_self hτ hα, rootForm_self hτ hβ] at hγ
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hab : (0 : ℤ) ≤ a * b := by positivity
  nlinarith [mul_nonneg hab h0, mul_nonneg hab h0']

private theorem rootSubgroup_commute_of_rootForm_nonneg_aux
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (R : Type) [CommRing R]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β)
    (h0 : 0 ≤ α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β))
    {x y : (Module.End R (RootModule τ R))ˣ} (hx : x ∈ rootSubgroup τ R α)
    (hy : y ∈ rootSubgroup τ R β) : x * y = y * x := by
  have hne' : α ≠ -β := fun h => by
    subst h
    rw [neg_dotProduct, rootForm_self hτ hβ] at h0
    exact absurd h0 (by norm_num)
  have hlin := Steinberg.Adjoint.linIndepPair_of_ne hα hβ hne hne'
  obtain ⟨w, hwα, hwβ⟩ := Steinberg.Adjoint.exists_weyl_height_pos hα hβ hlin
  have hwne : (⟨w • α, IsRoot.smul hα w⟩ : Root τ) ≠ ⟨w • β, IsRoot.smul hβ w⟩ := fun h =>
    hne (smul_left_cancel _ (congrArg Subtype.val h))
  have hc := ringCommContained_pos R ⟨w • α, IsRoot.smul hα w⟩ ⟨w • β, IsRoot.smul hβ w⟩ hwα hwβ
    hwne
  obtain ⟨ω, -, hω⟩ := (coxeterSystem τ).exists_isReduced w⁻¹
  have ht := (rootOperatorFamily τ).ring_comm_transport_list ω hc
  have hprod : (ω.map (simple τ)).prod = w⁻¹ := hω.symm
  have e1 : (ω.map (simple τ)).prod • (⟨w • α, IsRoot.smul hα w⟩ : Root τ) = ⟨α, hα⟩ :=
    Subtype.ext (by rw [coe_smul_root, hprod, inv_smul_smul])
  have e2 : (ω.map (simple τ)).prod • (⟨w • β, IsRoot.smul hβ w⟩ : Root τ) = ⟨β, hβ⟩ :=
    Subtype.ext (by rw [coe_smul_root, hprod, inv_smul_smul])
  rw [e1, e2] at ht
  rw [rootSubgroup_eq_ringRootSubgroup R hα] at hx
  rw [rootSubgroup_eq_ringRootSubgroup R hβ] at hy
  have hmem := ht x hx y hy
  have hbot : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      γ.1 = a • (⟨α, hα⟩ : Root τ).1 + b • (⟨β, hβ⟩ : Root τ).1),
      (rootOperatorFamily τ).ringRootSubgroup R γ) = ⊥ :=
    iSup₂_eq_bot.2 fun γ ⟨a, b, ha, hb, hγ⟩ =>
      absurd (hγ ▸ γ.2) (not_isRoot_nsmul_add_nsmul_of_rootForm_nonneg hτ hα hβ h0 ha hb)
  rw [hbot, Subgroup.mem_bot] at hmem
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hmem, one_mul]

private theorem weylElt_inv_conj_mem_rootSubgroup_aux
    (R : Type) [CommRing R] (i : Fin τ.rank)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ rootSubgroup τ R β) :
    (weylElt τ R i 1)⁻¹ * g * weylElt τ R i 1 ∈ rootSubgroup τ R (reflect τ i β) := by
  rw [← reflect_reflect τ i β, ← map_conj_weylElt_rootSubgroup R i (IsRoot.reflect i hβ)] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  simpa [MulAut.conj_apply, mul_assoc] using hh

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem baseChange_prod_reverse_weylElt
    (l : List ℕ) :
    BaseChange f (((l.map fun i => weylElt τ R (τ.idx i) 1).reverse.prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (((l.map fun i => weylElt τ S (τ.idx i) 1).reverse.prod :
        (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction l with
  | nil => simpa using BaseChange.one (τ := τ) (f := f)
  | cons a l ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      Units.val_mul]
    exact ih.mul (BaseChange.weylElt_one _)

theorem baseChange_pinnedX
    (α : Fin τ.rank → ℤ) (c : R) :
    BaseChange f (pinnedX τ R α c : Module.End R (RootModule τ R))
      (pinnedX τ S α (f c) : Module.End S (RootModule τ S)) := by
  have hW := baseChange_prod_reverse_weylElt (τ := τ) f (pinnedData τ α).2.1
  have hx := BaseChange.xOp (τ := τ) (f := f) (pinnedData τ α).1 ((pinnedData τ α).2.2 • c)
  rw [map_zsmul] at hx
  simp only [pinnedX, pinnedWeyl, Units.val_mul]
  exact (hW.mul hx).mul (BaseChange.units_inv hW)

end BaseChange

open MvPolynomial in
theorem pinnedX_commute_of_rootForm_nonneg
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {R : Type*} [CommRing R] {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (h0 : 0 ≤ α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) (c d : R) :
    Commute (pinnedX τ R α c) (pinnedX τ R β d) := by
  have h := rootSubgroup_commute_of_rootForm_nonneg_aux hτ (MvPolynomial (Fin 2) ℤ) hα hβ hne h0
    (Subgroup.subset_closure ⟨X 0, rfl⟩) (Subgroup.subset_closure ⟨X 1, rfl⟩)
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hl := (baseChange_pinnedX (τ := τ) g α (X 0)).mul (baseChange_pinnedX g β (X 1))
  have hr := (baseChange_pinnedX (τ := τ) g β (X 1)).mul (baseChange_pinnedX g α (X 0))
  rw [hg0, hg1] at hl hr
  rw [← Units.val_mul, h, Units.val_mul] at hl
  exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hl.unique hr)

theorem rootSubgroup_commute_of_rootForm_nonneg
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {R : Type*} [CommRing R] {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (h0 : 0 ≤ α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β))
    {x y : (Module.End R (RootModule τ R))ˣ} (hx : x ∈ rootSubgroup τ R α)
    (hy : y ∈ rootSubgroup τ R β) : Commute x y := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  exact pinnedX_commute_of_rootForm_nonneg hτ hα hβ hne h0 c d

open Polynomial in
theorem weylElt_inv_conj_mem_rootSubgroup
    {R : Type*} [CommRing R] (i : Fin τ.rank)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ rootSubgroup τ R β) :
    (weylElt τ R i 1)⁻¹ * g * weylElt τ R i 1 ∈ rootSubgroup τ R (reflect τ i β) := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  obtain ⟨p, hp⟩ := mem_rootSubgroup.1 (weylElt_inv_conj_mem_rootSubgroup_aux ℤ[X] i hβ
    (Subgroup.subset_closure ⟨X, rfl⟩))
  set e : ℤ[X] →+* R := eval₂RingHom (Int.castRingHom R) c
  have he : e X = c := eval₂_X _ _
  have hl := ((BaseChange.units_inv (BaseChange.weylElt_one (τ := τ) (f := e) i)).mul
    (baseChange_pinnedX e β X)).mul (BaseChange.weylElt_one (τ := τ) (f := e) i)
  rw [he, ← Units.val_mul, ← Units.val_mul, ← hp] at hl
  refine mem_rootSubgroup.2 ⟨e p, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul]
  exact (baseChange_pinnedX (τ := τ) e (reflect τ i β) p).unique hl

theorem xUnit_mem_rootSubgroup
    {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) :
    xUnit τ R i c ∈ rootSubgroup τ R (Pi.single i 1) :=
  Subgroup.subset_closure ⟨c, pinnedX_single _ _ i c⟩

theorem yUnit_mem_rootSubgroup
    {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) :
    yUnit τ R i c ∈ rootSubgroup τ R (-Pi.single i 1) :=
  Subgroup.subset_closure ⟨c, pinnedX_neg_single _ _ i c⟩

theorem commutatorElement_yUnit_weylConj
    {R : Type*} [CommRing R] {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) (a b : R) :
    ⁅yUnit τ R i (-a), weylElt τ R i (-1) * xUnit τ R j b * weylElt τ R i 1⁆ =
      xUnit τ R j (a * b) := by
  have hy : yUnit τ R i (-a) = (weylElt τ R i 1)⁻¹ * xUnit τ R i a * weylElt τ R i 1 := by
    have h := weylElt_mul_xOp_mul_inv (R := R) i (-1) a
    rw [weylElt_inv, neg_neg, inv_neg, inv_one, Units.val_neg, Units.val_one, neg_one_sq,
      mul_one] at h
    refine Units.ext ?_
    rw [weylElt_inv, Units.val_mul, Units.val_mul, coe_yUnit, coe_xUnit, h]
  have hc := (a2_simple_root_commutator τ R i j hij hji a b).1
  rw [hy, ← weylElt_inv, commutatorElement_def]
  calc (weylElt τ R i 1)⁻¹ * xUnit τ R i a * weylElt τ R i 1 *
        ((weylElt τ R i 1)⁻¹ * xUnit τ R j b * weylElt τ R i 1) *
        ((weylElt τ R i 1)⁻¹ * xUnit τ R i a * weylElt τ R i 1)⁻¹ *
        ((weylElt τ R i 1)⁻¹ * xUnit τ R j b * weylElt τ R i 1)⁻¹ =
      (weylElt τ R i 1)⁻¹ *
        (xUnit τ R i a * xUnit τ R j b * (xUnit τ R i a)⁻¹ * (xUnit τ R j b)⁻¹) *
          weylElt τ R i 1 := by group
    _ = xUnit τ R j (a * b) := by
      rw [← xUnit_neg, ← xUnit_neg, hc, ← weylElt_inv]
      group

end CFSG.LieType.Chevalley
