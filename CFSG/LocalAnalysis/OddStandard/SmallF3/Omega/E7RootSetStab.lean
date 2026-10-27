module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLift
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution TauCeti
  QuadraticMap


theorem redV_surj (x : V) : ∃ v : Fin Tag.E7.rank → ℤ, redV v = x :=
  ⟨fun i => (((x i).val : ℕ) : ℤ), by
    funext i
    simp only [redV, Int.cast_natCast, ZMod.natCast_zmod_val]⟩

noncomputable def weylInt (w : WeylGroup Tag.E7) :
    Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  LinearMap.toMatrix' (weylAction (isFiniteType_cartan Tag.E7) w)

theorem weylInt_mulVec (w : WeylGroup Tag.E7) (v : Fin Tag.E7.rank → ℤ) :
    (weylInt w).mulVec v = w • v := by
  rw [CFSG.LieType.Chevalley.smul_def]
  exact LinearMap.toMatrix'_mulVec _ _

noncomputable def weylMat (w : WeylGroup Tag.E7) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (weylInt w).map (Int.castRingHom (ZMod 3))

theorem weylMat_mulVec (w : WeylGroup Tag.E7) (v : Fin Tag.E7.rank → ℤ) :
    (weylMat w).mulVec (redV v) = redV (w • v) := by
  funext i
  have h := RingHom.map_mulVec (Int.castRingHom (ZMod 3)) (weylInt w) v i
  rw [weylInt_mulVec] at h
  exact h.symm

theorem weylMat_one : weylMat 1 = 1 := by
  unfold weylMat weylInt
  rw [map_one, LinearMap.toMatrix'_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem weylMat_mul (w w' : WeylGroup Tag.E7) : weylMat (w * w') = weylMat w * weylMat w' := by
  unfold weylMat weylInt
  rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul]
  rfl

noncomputable def rhoEquiv (w : WeylGroup Tag.E7) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofLinear (Matrix.toLin' (weylMat w)) (Matrix.toLin' (weylMat w⁻¹))
    (by rw [← Matrix.toLin'_mul, ← weylMat_mul, mul_inv_cancel, weylMat_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← weylMat_mul, inv_mul_cancel, weylMat_one, Matrix.toLin'_one])

theorem rhoEquiv_redV (w : WeylGroup Tag.E7) (v : Fin Tag.E7.rank → ℤ) :
    rhoEquiv w (redV v) = redV (w • v) := by
  show Matrix.toLin' (weylMat w) (redV v) = _
  rw [Matrix.toLin'_apply]
  exact weylMat_mulVec w v

theorem qForm_redV (u : Fin Tag.E7.rank → ℤ) :
    qForm (redV u) = 2 * ((iform u u : ℤ) : ZMod 3) := by
  have h1 := QuadraticMap.polar_self qForm (redV u)
  rw [CFSG.StandardType.e7LiftP11_polarV_redV, nsmul_eq_mul] at h1
  rw [h1]
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  push_cast
  rw [← mul_assoc, h22, one_mul]

theorem rhoEquiv_mem (w : WeylGroup Tag.E7) :
    rhoEquiv w ∈ TauCeti.QuadraticMap.orthogonalGroup qForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  obtain ⟨v, rfl⟩ := redV_surj x
  rw [rhoEquiv_redV, qForm_redV, qForm_redV, iform_smul]

noncomputable def rho : WeylGroup Tag.E7 →* OGroup qForm where
  toFun w := ⟨rhoEquiv w, rhoEquiv_mem w⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    show Matrix.toLin' (weylMat 1) x = x
    rw [weylMat_one, Matrix.toLin'_one]
    rfl
  map_mul' w w' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    show Matrix.toLin' (weylMat (w * w')) x =
      Matrix.toLin' (weylMat w) (Matrix.toLin' (weylMat w') x)
    rw [weylMat_mul, Matrix.toLin'_mul]
    rfl

theorem rho_apply_redV (w : WeylGroup Tag.E7) (v : Fin Tag.E7.rank → ℤ) :
    ((rho w : OGroup qForm) : V ≃ₗ[ZMod 3] V) (redV v) = redV (w • v) :=
  rhoEquiv_redV w v

theorem iform_single_left (i : Fin Tag.E7.rank) (v : Fin Tag.E7.rank → ℤ) :
    iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) v = ∑ j, Tag.cartan Tag.E7 i j * v j := by
  have hsym : Tag.symmetrizedCartan Tag.E7 = Tag.cartan Tag.E7 := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer]
    exact one_mul _
  rw [iform, hsym]
  simp [Pi.single_apply]

theorem redV_sub (u v : Fin Tag.E7.rank → ℤ) : redV (u - v) = redV u - redV v := by
  funext i
  exact Int.cast_sub _ _

theorem redV_zsmul (c : ℤ) (v : Fin Tag.E7.rank → ℤ) :
    redV (c • v) = (c : ZMod 3) • redV v := by
  funext i
  show ((c * v i : ℤ) : ZMod 3) = (c : ZMod 3) * ((v i : ℤ) : ZMod 3)
  exact Int.cast_mul _ _

theorem qV_redV_single (i : Fin Tag.E7.rank) :
    qV (redV (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) = 1 := by
  rw [← qForm_apply, qForm_redV, iform_single_left]
  have h : ∑ j, Tag.cartan Tag.E7 i j * (Pi.single i 1 : Fin Tag.E7.rank → ℤ) j = 2 := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    revert i
    decide
  rw [h]
  all_goals first | decide | norm_num

theorem rho_simple (i : Fin Tag.E7.rank) :
    rho (simple Tag.E7 i) =
      reflEl (redV (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) (qV_redV_single i) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, rfl⟩ := redV_surj x
  show ((rho (simple Tag.E7 i) : OGroup qForm) : V ≃ₗ[ZMod 3] V) (redV v) =
    ((reflEl (redV (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) (qV_redV_single i) : OGroup qForm) :
      V ≃ₗ[ZMod 3] V) (redV v)
  rw [rho_apply_redV, reflEl_apply, simple_smul, reflect, redV_sub, redV_zsmul]
  unfold rxV
  rw [← polar_qForm, CFSG.StandardType.e7LiftP11_polarV_redV, iform_single_left]

def tau0 : (ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3)) := ((-1 : (ZMod 3)ˣ), 1)

theorem detSpinorNorm_rho_simple (i : Fin Tag.E7.rank) :
    detSpinorNorm e7QForm_nondegenerate (rho (simple Tag.E7 i)) = tau0 := by
  rw [rho_simple]
  exact detSpinorNorm_reflEl e7QForm_nondegenerate _ _

theorem detSpinorNorm_rho_word (ω : List (Fin Tag.E7.rank)) :
    detSpinorNorm e7QForm_nondegenerate (rho ((coxeterSystem Tag.E7).wordProd ω)) =
      tau0 ^ ω.length := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, map_mul, ih, detSpinorNorm_rho_simple,
      List.length_cons, pow_succ']

theorem tau0_pow_eq_one_iff (n : ℕ) : tau0 ^ n = 1 ↔ Even n := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    simp only [tau0, Prod.pow_fst, Prod.fst_one] at h1
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 h1
  · rintro ⟨k, rfl⟩
    rw [← two_mul, pow_mul]
    have h2 : tau0 ^ 2 = 1 := by
      refine Prod.ext ?_ ?_
      · simp only [tau0, Prod.pow_fst, Prod.fst_one]; decide
      · simp only [tau0, Prod.pow_snd, Prod.snd_one, one_pow]
    rw [h2, one_pow]

theorem lengthParity_word (ω : List (Fin Tag.E7.rank)) :
    (coxeterSystem Tag.E7).lengthParity ((coxeterSystem Tag.E7).wordProd ω) =
      Multiplicative.ofAdd (ω.length : ZMod 2) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, CoxeterSystem.lengthParity_simple,
      List.length_cons, ← ofAdd_add]
    push_cast
    rw [add_comm]

theorem rho_mem_omega_iff (w : WeylGroup Tag.E7) :
    rho w ∈ omegaGroup e7QForm_nondegenerate ↔
      (coxeterSystem Tag.E7).lengthParity w = 1 := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.E7).wordProd_surjective w
  rw [mem_omegaGroup_iff, detSpinorNorm_rho_word, lengthParity_word, tau0_pow_eq_one_iff,
    ofAdd_eq_one, ZMod.natCast_eq_zero_iff_even]

theorem mem_rootSet_iff {x : V} : x ∈ rootSet ↔ ∃ α, IsRoot Tag.E7 α ∧ redV α = x := by
  rw [← Finset.mem_coe, rootSet_eq_image]
  exact Iff.rfl

theorem rho_image_rootSet (w : WeylGroup Tag.E7) : rootSet.image (rhoEquiv w) = rootSet := by
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨α, hα, rfl⟩ := mem_rootSet_iff.1 hy
    rw [rhoEquiv_redV]
    exact mem_rootSet_iff.2 ⟨w • α, IsRoot.smul hα w, rfl⟩
  · intro hx
    obtain ⟨α, hα, rfl⟩ := mem_rootSet_iff.1 hx
    refine ⟨redV (w⁻¹ • α), mem_rootSet_iff.2 ⟨w⁻¹ • α, IsRoot.smul hα w⁻¹, rfl⟩, ?_⟩
    rw [rhoEquiv_redV, smul_inv_smul]

theorem rho_injective : Function.Injective rho := by
  intro w w' h
  refine ext_single fun i => ?_
  have h1 : redV (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) =
      redV (w' • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) := by
    rw [← rho_apply_redV, ← rho_apply_redV, h]
  exact redV_injOn_roots (IsRoot.smul (IsRoot.basis i) w) (IsRoot.smul (IsRoot.basis i) w') h1

noncomputable def evenWeyl : Subgroup (WeylGroup Tag.E7) :=
  (coxeterSystem Tag.E7).lengthParity.ker

noncomputable def rhoOmega (w : evenWeyl) : omegaGroup e7QForm_nondegenerate :=
  ⟨rho w, (rho_mem_omega_iff _).2 w.2⟩

theorem toEq_rhoOmega (w : evenWeyl) :
    toEq e7QForm_nondegenerate (rhoOmega w) = rhoEquiv w := by
  rw [toEq_eq_coe]
  rfl

theorem rhoOmega_mem_stabilizer (w : evenWeyl) :
    rhoOmega w ∈ MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet := by
  rw [MulAction.mem_stabilizer_iff, CFSG.OddStandard.SmallF3.Omega.E7RootSet.smul_def,
    toEq_rhoOmega]
  exact rho_image_rootSet w

noncomputable def rhoStab (w : evenWeyl) :
    MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet :=
  ⟨rhoOmega w, rhoOmega_mem_stabilizer w⟩

theorem rhoStab_injective : Function.Injective rhoStab := by
  intro w w' h
  have h1 : rho (w : WeylGroup Tag.E7) = rho (w' : WeylGroup Tag.E7) :=
    congrArg (fun g : MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet =>
      ((g : omegaGroup e7QForm_nondegenerate) : OGroup qForm)) h
  exact Subtype.ext (rho_injective h1)

theorem rhoStab_surjective : Function.Surjective rhoStab := by
  rintro ⟨g, hg⟩
  rw [MulAction.mem_stabilizer_iff, CFSG.OddStandard.SmallF3.Omega.E7RootSet.smul_def,
    toEq_eq_coe] at hg
  obtain ⟨w, hw⟩ := exists_weyl_of_image_rootSet (g : OGroup qForm) hg
  have hrho : rho w = (g : OGroup qForm) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := redV_surj x
    exact (rho_apply_redV w v).trans (hw v).symm
  have hmem : (coxeterSystem Tag.E7).lengthParity w = 1 := by
    rw [← rho_mem_omega_iff, hrho]
    exact g.2
  exact ⟨⟨w, hmem⟩, Subtype.ext (Subtype.ext hrho)⟩

theorem lengthParity_range : (coxeterSystem Tag.E7).lengthParity.range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro a
  have h : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
  rcases h a with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨(coxeterSystem Tag.E7).simple ⟨0, by decide⟩, CoxeterSystem.lengthParity_simple _ _⟩

theorem index_evenWeyl : evenWeyl.index = 2 := by
  rw [evenWeyl, Subgroup.index_ker, lengthParity_range, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod 2

theorem natCard_evenWeyl : Nat.card evenWeyl = 1451520 := by
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 := by
    haveI : Fintype (WeylGroup Tag.E7) := Fintype.ofFinite _
    exact (CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2
  have h := Subgroup.card_mul_index evenWeyl
  rw [index_evenWeyl, hW] at h
  omega

theorem card_stabilizer_rootSet (hQ : qForm.Nondegenerate) :
    Nat.card (MulAction.stabilizer (omegaGroup hQ) rootSet) = 1451520 := by
  rw [← natCard_evenWeyl]
  exact (Nat.card_congr (Equiv.ofBijective rhoStab ⟨rhoStab_injective, rhoStab_surjective⟩)).symm

theorem isCoatom_stabilizer_rootSet_of_certificates :
    IsCoatom (MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet) :=
  isCoatom_stabilizer_rootSet' (card_stabilizer_rootSet e7QForm_nondegenerate)

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
