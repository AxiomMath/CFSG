module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidE6

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.GraphAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev rhoE6 : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

section Lattice

variable {n : ℕ}

theorem eq_sum_single (v : Fin n → ℤ) : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℤ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem addMonoidHom_apply_eq_of_single {F G : (Fin n → ℤ) →+ (Fin n → ℤ)}
    (h : ∀ i, F (Pi.single i 1) = G (Pi.single i 1)) (v : Fin n → ℤ) : F v = G v := by
  rw [eq_sum_single v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, h i]

@[expose] def sigmaHom {τ : Tag} (u : WeylGroup τ) (π : Equiv.Perm (Fin τ.rank)) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun v := u • permLattice π v
  map_zero' := by
    show u • (0 : Fin τ.rank → ℤ) = 0
    exact smul_zero u
  map_add' x y := by
    show u • (permLattice π x + permLattice π y) = _
    exact smul_add u _ _

theorem sigmaHom_apply {τ : Tag} (u : WeylGroup τ) (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : sigmaHom u π v = u • permLattice π v :=
  rfl

@[expose] def smulHom {τ : Tag} (w : WeylGroup τ) : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun v := w • v
  map_zero' := smul_zero w
  map_add' := smul_add w

end Lattice

section Characters

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_apply_eq_of_single (a : Fin τ.rank → Kˣ) (F : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (h : ∀ i, rootChar a (F (Pi.single i 1)) = rootChar a (Pi.single i 1)) (v : Fin τ.rank → ℤ) :
    rootChar a (F v) = rootChar a v := by
  conv_lhs => rw [eq_sum_single v, map_sum, CFSG.LieType.Chevalley.rootChar_sum]
  conv_rhs => rw [eq_sum_single v, CFSG.LieType.Chevalley.rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, h i]

theorem rootChar_pow_three {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ 3 = 1) (v : Fin τ.rank → ℤ) :
    rootChar a v ^ 3 = 1 := by
  simp only [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]

end Characters

section RootLines

variable {τ : Tag} {K : Type} [Field K]

@[expose] def MapsRootLinesBy (g : ModGL τ K) (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) : Prop :=
  ∀ α, IsRoot τ α → IsRoot τ (f α) ∧ ∃ c : Kˣ,
    (g : Module.End K (RootModule τ K)) (rootVec τ K α) = (c : K) • rootVec τ K (f α)

theorem MapsRootLinesBy.congr {g : ModGL τ K} {f f' : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hg : MapsRootLinesBy g f) (h : ∀ α, f α = f' α) : MapsRootLinesBy g f' := fun α hα => by
  rw [← h α]
  exact hg α hα

theorem MapsRootLinesBy.mul {g h : ModGL τ K} {f f' : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hg : MapsRootLinesBy g f) (hh : MapsRootLinesBy h f') : MapsRootLinesBy (g * h) (f ∘ f') := by
  intro α hα
  obtain ⟨hα', c', h'⟩ := hh α hα
  obtain ⟨hα'', c, h⟩ := hg (f' α) hα'
  refine ⟨hα'', c' * c, ?_⟩
  rw [Units.val_mul, Module.End.mul_apply, h', map_smul, h, smul_smul, Function.comp_apply,
    Units.val_mul]

theorem mapsRootLinesBy_of_mapsRootLines {g : ModGL τ K} {w : WeylGroup τ}
    (hg : MapsRootLines g w) : MapsRootLinesBy g (w • ·) := fun α hα =>
  ⟨IsRoot.smul hα w, hg α hα⟩

theorem mapsRootLinesBy_diagramMap (t : TwistTag) :
    MapsRootLinesBy (diagramMap t K) (permLattice t.perm) := fun α hα =>
  ⟨hα.permLattice t.cartan_perm, 1, by rw [diagramMap_rootVec t K α hα, Units.val_one, one_smul]⟩

theorem mapsRootLinesBy_rootDiagUnit
    (c : Fin τ.rank → Kˣ) : MapsRootLinesBy (rootDiagUnit τ c) id := fun α hα =>
  ⟨hα, rootChar c α, rootDiag_rootVec c hα⟩

theorem MapsRootLinesBy.apply_eq {g : ModGL τ K}
    {f f' : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : MapsRootLinesBy g f)
    (hf' : MapsRootLinesBy g f') {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : f α = f' α := by
  obtain ⟨h1, c, hc⟩ := hf α hα
  obtain ⟨h2, c', hc'⟩ := hf' α hα
  exact eq_of_smul_rootVec_eq h1 h2 (hc.symm.trans hc')

theorem MapsRootLinesBy.comm_of_commute {g h : ModGL τ K}
    {f f' : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hg : MapsRootLinesBy g f)
    (hh : MapsRootLinesBy h f') (hc : Commute g h) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    f (f' α) = f' (f α) := by
  have h1 := hg.mul hh
  have h2 := hh.mul hg
  rw [← hc.eq] at h2
  exact h1.apply_eq h2 hα

theorem MapsRootLinesBy.rootChar_eq_of_commute
    {g : ModGL τ K} {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hg : MapsRootLinesBy g f) {a : Fin τ.rank → Kˣ} (hc : Commute g (rootDiagUnit τ a))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : rootChar a (f α) = rootChar a α := by
  obtain ⟨hfα, c, hgc⟩ := hg α hα
  have h1 := congrArg (fun x : ModGL τ K => (x : Module.End K (RootModule τ K)) (rootVec τ K α))
    hc.eq
  simp only [Units.val_mul, Module.End.mul_apply] at h1
  change (g : Module.End K (RootModule τ K)) (rootDiag a (rootVec τ K α)) =
    rootDiag a ((g : Module.End K (RootModule τ K)) (rootVec τ K α)) at h1
  rw [rootDiag_rootVec a hα, map_smul, hgc, map_smul, rootDiag_rootVec a hfα, smul_smul,
    smul_smul] at h1
  have h2 := eq_of_smul_rootVec_eq_smul hfα h1
  rw [mul_comm] at h2
  exact (Units.ext (mul_left_cancel₀ c.ne_zero h2)).symm

theorem sigmaHom_smul_comm_of_commute {g h : ModGL τ K}
    {u w : WeylGroup τ} {π : Equiv.Perm (Fin τ.rank)} (hg : MapsRootLinesBy g (sigmaHom u π))
    (hh : MapsRootLinesBy h (w • ·)) (hc : Commute g h) (v : Fin τ.rank → ℤ) :
    sigmaHom u π (w • v) = w • sigmaHom u π v :=
  addMonoidHom_apply_eq_of_single (F := (sigmaHom u π).comp (smulHom w))
    (G := (smulHom w).comp (sigmaHom u π)) (fun i => hg.comm_of_commute hh hc (IsRoot.basis i)) v

theorem rootChar_sigmaHom_of_commute
    {g : ModGL τ K} {u : WeylGroup τ} {π : Equiv.Perm (Fin τ.rank)}
    (hg : MapsRootLinesBy g (sigmaHom u π)) {a : Fin τ.rank → Kˣ}
    (hc : Commute g (rootDiagUnit τ a)) (v : Fin τ.rank → ℤ) :
    rootChar a (sigmaHom u π v) = rootChar a v :=
  rootChar_apply_eq_of_single a (sigmaHom u π)
    (fun i => hg.rootChar_eq_of_commute hc (IsRoot.basis i)) v

end RootLines

section Monomial


theorem exists_monomial_of_commute_regular {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ7 : 7 < ℓ) {ζ : Lˣ} (hζ : orderOf ζ = ℓ) (zv : Fin Tag.E6.rank → ℤ)
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (ℓ : ℤ) ∣ ∑ j, zv j * α j)
    {g : ModGL Tag.E6 L} (hg : g ∈ adjointGroup Tag.E6 L)
    (hc : Commute (g * graphP L) (rootDiagUnit Tag.E6 fun j => ζ ^ zv j)) :
    ∃ (u : WeylGroup Tag.E6) (c : Fin Tag.E6.rank → Lˣ),
      g = canonicalRep (coxeterSystem Tag.E6) L u * rootDiagUnit Tag.E6 c := by
  set P : ModGL Tag.E6 L := diagramMap TwistTag.E6 L
  set a' : Fin Tag.E6.rank → Lˣ := fun j => ζ ^ zv j
  set z' : Fin Tag.E6.rank → ℤ := fun j => zv (rhoE6.symm j) with hz'
  set b' : Fin Tag.E6.rank → Lˣ := fun j => ζ ^ z' j
  have hPd : P * rootDiagUnit Tag.E6 a' = rootDiagUnit Tag.E6 b' * P :=
    diagramMap_mul_rootDiagUnit (t := TwistTag.E6) a'
  have hgb : g * rootDiagUnit Tag.E6 b' = rootDiagUnit Tag.E6 a' * g := by
    have h1 : g * P * rootDiagUnit Tag.E6 a' = rootDiagUnit Tag.E6 a' * (g * P) := hc.eq
    rw [mul_assoc, hPd, ← mul_assoc, ← mul_assoc] at h1
    exact mul_right_cancel h1
  have hconj : g * rootDiagUnit Tag.E6 b' * g⁻¹ = rootDiagUnit Tag.E6 a' := by
    rw [hgb, mul_inv_cancel_right]
  obtain ⟨u, hu⟩ :=
    (exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 L a' b').1.1 ⟨g, hg, hconj⟩
  have hnu := (rootDiagUnit_eq_conj_canonicalRep_iff a' b' u).2 hu
  set n := canonicalRep (coxeterSystem Tag.E6) L u
  have hmem : n⁻¹ * g ∈ toralCentralizer Tag.E6 L b' := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L u)) hg, ?_⟩
    have hb : rootDiagUnit Tag.E6 b' * n⁻¹ = n⁻¹ * rootDiagUnit Tag.E6 a' := by
      rw [hnu]
      group
    have hcomm : rootDiagUnit Tag.E6 b' * (n⁻¹ * g) = n⁻¹ * g * rootDiagUnit Tag.E6 b' := by
      rw [← mul_assoc, hb, mul_assoc, mul_assoc, hgb]
    rw [hcomm, mul_inv_cancel_right]
  have hreg' : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (ℓ : ℤ) ∣ ∑ j, z' j * α j := by
    intro α hα
    have hα' : IsRoot Tag.E6 (permLattice rhoE6.symm α) :=
      hα.permLattice (cartan_perm_symm TwistTag.E6.cartan_perm)
    have e : ∑ j, z' j * α j = ∑ j, zv j * permLattice rhoE6.symm α j := by
      refine (Equiv.sum_comp rhoE6 (fun j => z' j * α j)).symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hz', permLattice, Equiv.symm_symm, Equiv.symm_apply_apply, Function.comp_apply]
    rw [e]
    exact hreg _ hα'
  have hT : toralCentralizer Tag.E6 L b' = torusGroup Tag.E6 L :=
    CFSG.ComponentClassification.Burgoyne.E2.toralCentralizer_eq_torusGroup_of_regular
      (τ := Tag.E6) (Or.inl rfl) hℓ hℓ7 hζ z' hreg'
  rw [hT] at hmem
  obtain ⟨c, hc'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmem
  exact ⟨u, c, by rw [← hc', mul_inv_cancel_left]⟩

end Monomial

section Shift

@[expose] def e6OmegaSum : Fin Tag.E6.rank → ℤ := ![2, 2, 3, 4, 3, 2]

theorem permLattice_e6Omega3_add :
    permLattice rhoE6 e6Omega3 + e6Omega3 = (3 : ℤ) • e6OmegaSum := by
  have h : ∀ i : Fin Tag.E6.rank, permLattice rhoE6 e6Omega3 i + e6Omega3 i =
      3 * e6OmegaSum i := by
    decide +kernel
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact h i

theorem rootChar_e6Shift_eq_one_of_hom {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6} (hw : ∀ v, rootChar a (w • v) = rootChar a v)
    (σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ)) (l : Fin Tag.E6.rank → ℤ)
    (hσΩ : σ e6Omega3 + e6Omega3 = (3 : ℤ) • l) (hσw : ∀ v, σ (w • v) = w • σ v)
    (hχσ : ∀ v, rootChar a (σ v) = rootChar a v) :
    rootChar a (e6Shift w) = 1 := by
  have h3 : (3 : ℤ) • (σ (e6Shift w) + e6Shift w) = (3 : ℤ) • (w • l - l) := by
    have e1 : (3 : ℤ) • (σ (e6Shift w) + e6Shift w) =
        w • σ e6Omega3 - σ e6Omega3 + (w • e6Omega3 - e6Omega3) := by
      rw [smul_add, ← map_zsmul, three_smul_e6Shift, map_sub, hσw]
    rw [e1, smul_sub, ← smul_comm w (3 : ℤ) l, ← hσΩ, smul_add]
    abel
  have h1 : σ (e6Shift w) + e6Shift w = w • l - l :=
    smul_right_injective _ (by norm_num : (3 : ℤ) ≠ 0) h3
  have hsq : rootChar a (e6Shift w) * rootChar a (e6Shift w) = 1 := by
    have e := congrArg (rootChar a) h1
    rw [rootChar_add, hχσ, rootChar_sub, hw, mul_inv_cancel] at e
    exact e
  calc rootChar a (e6Shift w) =
        rootChar a (e6Shift w) * (rootChar a (e6Shift w) * rootChar a (e6Shift w)) := by
        rw [hsq, mul_one]
    _ = rootChar a (e6Shift w) ^ 3 := by rw [pow_three]
    _ = 1 := rootChar_pow_three ha _

theorem rootChar_e6Shift_eq_one {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6} (hw : ∀ v, rootChar a (w • v) = rootChar a v)
    (u : WeylGroup Tag.E6)
    (hσw : ∀ v, sigmaHom u rhoE6 (w • v) = w • sigmaHom u rhoE6 v)
    (hχσ : ∀ v, rootChar a (sigmaHom u rhoE6 v) = rootChar a v) :
    rootChar a (e6Shift w) = 1 := by
  refine rootChar_e6Shift_eq_one_of_hom ha hw (sigmaHom u rhoE6)
    (u • e6OmegaSum - e6Shift u) ?_ hσw hχσ
  rw [sigmaHom_apply, eq_sub_of_add_eq permLattice_e6Omega3_add,
    smul_sub u ((3 : ℤ) • e6OmegaSum) e6Omega3,
    smul_comm u (3 : ℤ), smul_sub (3 : ℤ), three_smul_e6Shift]
  abel

end Shift

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.GraphAux
