module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

section Gram

variable {p f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData p f K) {V : Type*}
  [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_sourceSU_gram (b : Basis ι K V) (G : Matrix ι ι K) (h : V → V → K)
    (hh : ∀ x y, h x y = gramForm hU G (b.equivFun x) (b.equivFun y)) :
    (sourceSL K V ⊓ sourceIsometry h).map (sourceGLEquiv b).toMonoidHom = gramSU hU G := by
  ext A
  rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, mem_gramSU]
  set g := (sourceGLEquiv b).symm A
  have hg : LinearMap.toMatrix b b (g : Module.End K V) = A := by
    rw [← coe_sourceGLEquiv, MulEquiv.apply_symm_apply]
  have hgv : ∀ x, b.equivFun ((g : Module.End K V) x) = (A : Matrix ι ι K) *ᵥ b.equivFun x := by
    intro x
    rw [← hg]
    exact (LinearMap.toMatrix_mulVec_repr b b (g : Module.End K V) x).symm
  have hdet : g ∈ sourceSL K V ↔ (A : Matrix ι ι K).det = 1 := by
    rw [sourceSL, MonoidHom.mem_ker]
    change LinearMap.det (Matrix.toLin b b (A : Matrix ι ι K)) = 1 ↔ _
    rw [LinearMap.det_toLin]
  have hiso : g ∈ sourceIsometry h ↔
      ∀ u v, gramForm hU G ((A : Matrix ι ι K) *ᵥ u) ((A : Matrix ι ι K) *ᵥ v) =
        gramForm hU G u v := by
    change (∀ x y, h ((g : Module.End K V) x) ((g : Module.End K V) y) = h x y) ↔ _
    simp only [hh, hgv]
    constructor
    · intro H u v
      have := H (b.equivFun.symm u) (b.equivFun.symm v)
      rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    · intro H x y
      exact H _ _
  rw [hdet, hiso, gramForm_isometry_iff, and_comm]

end Gram

theorem sourceClassicalModel_of_stated_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSU n p f) : SourceClassicalModel X .PSU n p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hadm.1, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  set hh : (Fin n → K) → (Fin n → K) → K := fun x y => gramForm hU 1 x y with hhdef
  have hsymm := gramForm_isSymm hU (G := (1 : Matrix (Fin n) (Fin n) K))
    (by rw [Matrix.map_one _ (map_zero hU.bar) (map_one hU.bar), transpose_one])
  have hsep := gramForm_separatingLeft hU (G := (1 : Matrix (Fin n) (Fin n) K))
    (by rw [det_one]; exact one_ne_zero)
  have hmap : (sourceSL K (Fin n → K) ⊓ sourceIsometry hh).map
      (sourceGLEquiv (Pi.basisFun K (Fin n))).toMonoidHom = StatedSU n (p ^ f) K := by
    rw [map_sourceSU_gram hU (Pi.basisFun K (Fin n)) 1 hh fun x y => rfl, ← unitarySU_eq_gramSU]
  refine ⟨hadm, K, inferInstance, inferInstance, Fin n → K, inferInstance, inferInstance,
    inferInstance, sourceSL K (Fin n → K) ⊓ sourceIsometry hh, ⟨e.trans (quotientInfCongr
      (sourceGLEquiv (Pi.basisFun K (Fin n))).symm ?_ ?_)⟩, hK, Module.finrank_fin_fun K, hh,
    ⟨fun x x' y => LinearMap.map_add₂ _ _ _ _, fun x y y' => map_add _ _ _, fun a b x y => ?_,
      fun x y => ?_, ?_⟩, rfl⟩
  · rw [← hmap, Subgroup.map_map]
    simp
  · rw [← map_sourceScalars_sourceGLEquiv (Pi.basisFun K (Fin n)), Subgroup.map_map]
    simp
  · simp only [hhdef, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, hU.bar_apply]
    ring
  · rw [hhdef, ← hU.bar_apply]
    exact (hsymm.eq x y).symm
  · ext x
    refine ⟨fun hx => Set.mem_singleton_iff.mpr (hsep x hx), fun hx y => ?_⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact LinearMap.map_zero₂ _ _

theorem stated_of_sourceClassicalModel_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .PSU n p f) : StatedClassicalModel X .PSU n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, hh, ⟨hadd, hadd', hsmul, hsymm, hrad⟩,
    rfl⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hadm.1, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hadm.1⟩
  have : CharP K p := hU.charP
  have hσ : ∀ c : K, CFSG.LieType.BorelTits.unitaryInvolution K p f c = hU.bar c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hU.bar_apply]
  let B : V →ₛₗ[hU.bar] V →ₗ[K] K := LinearMap.mk₂'ₛₗ hU.bar (RingHom.id K) hh hadd
    (fun c x y => by
      have h1 := hsmul c 1 x y
      rw [one_smul, mul_one] at h1
      rw [h1, hU.bar_apply, smul_eq_mul])
    hadd'
    (fun c x y => by
      have h1 := hsmul 1 c x y
      rw [one_smul, one_pow, one_mul] at h1
      rw [h1, smul_eq_mul, RingHom.id_apply])
  have hB : ∀ x y, B x y = hh x y := fun x y => rfl
  let b := Module.finBasisOfFinrankEq K V hV
  let G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => hh (b i) (b j)
  have hcoord : ∀ x y, hh x y = gramForm hU G (b.equivFun x) (b.equivFun y) := by
    let B' : V →ₛₗ[hU.bar] V →ₗ[K] K := LinearMap.mk₂'ₛₗ hU.bar (RingHom.id K)
      (fun x y => gramForm hU G (b.equivFun x) (b.equivFun y))
      (fun x x' y => by rw [map_add, LinearMap.map_add₂])
      (fun c x y => by rw [map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul])
      (fun x y y' => by rw [map_add, map_add])
      (fun c x y => by rw [map_smul, map_smul, RingHom.id_apply])
    have hbi : ∀ i, b.equivFun (b i) = Pi.single i 1 := fun i => by
      rw [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single]
    have hext : B = B' := by
      refine LinearMap.ext_basis b b fun i j => ?_
      change hh (b i) (b j) = gramForm hU G (b.equivFun (b i)) (b.equivFun (b j))
      rw [hbi, hbi, gramForm_single]
      rfl
    intro x y
    rw [← hB, hext]
    rfl
  have hG : CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K p f)
      G = G := by
    ext i j
    simp only [CFSG.LieType.Universal.Unitary.conjTr, transpose_apply, map_apply, hσ, G,
      Matrix.of_apply]
    rw [hsymm, ← hU.bar_apply, hU.bar_bar]
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    set x := b.equivFun.symm fun i => hU.bar (v i)
    have hx : x ∈ {x | ∀ y, hh x y = 0} := fun y => by
      have hbar : (fun a => hU.bar (b.equivFun x a)) = v := by
        funext a
        rw [LinearEquiv.apply_symm_apply, hU.bar_bar]
      rw [hcoord, gramForm_apply, hbar, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
    rw [hrad, Set.mem_singleton_iff] at hx
    apply hv0
    funext a
    have := congrFun (congrArg b.equivFun hx) a
    rw [LinearEquiv.apply_symm_apply, map_zero] at this
    have h2 := congrArg hU.bar this
    rwa [hU.bar_bar, Pi.zero_apply, map_zero] at h2
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one hK hG hdet
  have hP' : ((P : Matrix (Fin n) (Fin n) K).map hU.bar)ᵀ * G * P = 1 := by
    have hmapP : (P : Matrix (Fin n) (Fin n) K).map
        (CFSG.LieType.BorelTits.unitaryInvolution K p f) =
          (P : Matrix (Fin n) (Fin n) K).map hU.bar := by
      ext i j
      exact hσ _
    rw [CFSG.LieType.Universal.Unitary.conjTr, hmapP] at hP
    exact hP
  let e₁ : (Fin n → K) ≃ₗ[K] (Fin n → K) := LinearEquiv.ofLinearMap
    (Matrix.toLin' ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (Matrix.toLin' (P : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
  let b' : Basis (Fin n) K V := Basis.ofEquivFun (b.equivFun.trans e₁)
  have hb' : ∀ x, b.equivFun x = (P : Matrix (Fin n) (Fin n) K) *ᵥ b'.equivFun x := by
    intro x
    rw [Basis.equivFun_ofEquivFun, LinearEquiv.trans_apply]
    change b.equivFun x = (P : Matrix (Fin n) (Fin n) K) *ᵥ
      (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b.equivFun x)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hcoord' : ∀ x y, hh x y = gramForm hU 1 (b'.equivFun x) (b'.equivFun y) := by
    intro x y
    rw [hcoord, hb', hb', gramForm_mulVec, hP']
  have hmap : (sourceSL K V ⊓ sourceIsometry hh).map (sourceGLEquiv b').toMonoidHom =
      StatedSU n (p ^ f) K := by
    rw [map_sourceSU_gram hU b' 1 hh hcoord', ← unitarySU_eq_gramSU]
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (quotientInfCongr (sourceGLEquiv b')
    hmap (map_sourceScalars_sourceGLEquiv b'))⟩⟩

end CFSG.Blueprint.EvenSource
