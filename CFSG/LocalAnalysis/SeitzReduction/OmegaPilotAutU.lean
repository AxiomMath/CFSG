module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)

section RootSylow

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isPGroup_rootGroup [CharP K 2] (u : V) : IsPGroup 2 (rootGroup Q u) := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  change eichler Q u w ^ 2 = 1
  rw [pow_two, eichler_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul,
    eichler_zero_right]

@[expose] def rootFixSub (u u' : V) : Subgroup (V ≃ₗ[K] V) :=
  rootGroup Q u' ⊓ MulAction.stabilizer (V ≃ₗ[K] V) u

theorem rootFixSub_le_normalizer (u u' : V) :
    rootFixSub (Q := Q) u u' ≤ normalizer (rootGroup Q u : Set (V ≃ₗ[K] V)) := by
  rintro g ⟨hg, hgu⟩
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
    exact eichler_mem_orthogonalGroup Q u' w
  have hgu' : g u = (1 : K) • u := by
    rw [one_smul]
    exact (MulAction.mem_stabilizer_iff.mp hgu)
  have hginv : g⁻¹ u = (1 : K) • u := by
    rw [one_smul]
    calc g⁻¹ u = g⁻¹ (g u) := by rw [hgu', one_smul]
      _ = u := LinearEquiv.inv_apply_apply' g u
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_rootGroup_of_apply_eq_smul hgO hgu' hh, fun hh => ?_⟩
  have := conj_mem_rootGroup_of_apply_eq_smul (inv_mem hgO) hginv hh
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

@[expose] def rootSylowSub (u u' : V) : Subgroup (V ≃ₗ[K] V) :=
  rootGroup Q u ⊔ rootFixSub (Q := Q) u u'

theorem isPGroup_rootSylowSub [CharP K 2] (u u' : V) :
    IsPGroup 2 (rootSylowSub (Q := Q) u u') :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_rootGroup u)
    ((isPGroup_rootGroup u').to_le inf_le_left) (rootFixSub_le_normalizer u u')

theorem eichler_mem_rootSylowSub_left {u w : V} (hw : polar Q u w = 0) (u' : V) :
    eichler Q u w ∈ rootSylowSub (Q := Q) u u' :=
  le_sup_left (a := rootGroup Q u) (eichler_mem_rootGroup hw)

theorem eichler_mem_rootSylowSub_right {u u' w : V} (hu : polar Q u u' = 0)
    (hw' : polar Q u' w = 0) (hw : polar Q u w = 0) :
    eichler Q u' w ∈ rootSylowSub (Q := Q) u u' :=
  le_sup_right (a := rootGroup Q u)
    ⟨eichler_mem_rootGroup hw', MulAction.mem_stabilizer_iff.mpr
      (eichler_apply_of_polar_eq_zero hu hw)⟩

end RootSylow

section Image

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def rootSylowBar (u u' : Fin d → K) :
    Subgroup (matrixProjectiveDerived Q) :=
  ((rootSylowSub (Q := Q) u u').subgroupOf (orthDerived Q)).map (projHom Q)

theorem isPGroup_rootSylowBar [CharP K 2] (u u' : Fin d → K) :
    IsPGroup 2 (rootSylowBar (Q := Q) u u') :=
  ((isPGroup_rootSylowSub u u').comap_subtype).map _

theorem projHom_mem_rootSylowBar {u u' : Fin d → K} {E : orthDerived Q}
    (hE : (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootSylowSub (Q := Q) u u') :
    projHom Q E ∈ rootSylowBar (Q := Q) u u' :=
  ⟨E, hE, rfl⟩

theorem exists_conj_mem_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (U : Sylow p X) :
    ∃ x : X, ∀ y ∈ P, x * y * x⁻¹ ∈ (U : Subgroup X) := by
  obtain ⟨U', hU'⟩ := hP.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq X U' U
  refine ⟨x, fun y hy => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simpa [mul_assoc] using hU' hy

@[expose] noncomputable def rootGroupBar (u : Fin d → K) : Subgroup (matrixProjectiveDerived Q) :=
  ((rootGroup Q u).subgroupOf (orthDerived Q)).map (projHom Q)

theorem isPGroup_rootGroupBar [CharP K 2] (u : Fin d → K) :
    IsPGroup 2 (rootGroupBar (Q := Q) u) :=
  ((isPGroup_rootGroup u).comap_subtype).map _

end Image

section AutU

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_map_ne_zero_of_hypPair (P : HypPair Q) : ∃ v, Q v ≠ 0 := by
  refine ⟨P.e + P.f, ?_⟩
  rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]
  norm_num

theorem mem_range_conj_of_fix_rootGroup [Finite K] [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q)
    (hβ : ∀ E : orthDerived Q, (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootGroup Q P₁.e →
      β (projHom Q E) = projHom Q E) :
    β ∈ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
  obtain ⟨g, rfl⟩ := hβE
  have hQ' := exists_map_ne_zero_of_hypPair P₁
  have hcomm : ∀ w ∈ (⊤ : Submodule K (Fin d → K)), polar Q P₁.e w = 0 →
      ∀ x ∈ (⊤ : Submodule K (Fin d → K)),
        simMap g (eichler Q P₁.e w x) = eichler Q P₁.e w (simMap g x) := by
    intro w _ hw x _
    exact commute_of_kappa_projHom_eq hQ' g
      (E := ⟨eichler Q P₁.e w, eichler_mem_orthDerived hQ hT _ _⟩)
      (hβ _ (eichler_mem_rootGroup hw)) x
  obtain ⟨-, γ, hγ0, x₀, -, -, hφ⟩ := eq_smul_eichler_of_commute (polarNondegOn_top hQ) h₁₂
    Submodule.mem_top Submodule.mem_top Submodule.mem_top Submodule.mem_top
    (Units.ne_zero (multiplier Q g)) (simMap_smul g) (map_simMap g)
    (fun _ _ => Submodule.mem_top) hcomm
  exact ⟨_, (kappa_eq_conj_of_eq_smul g ⟨eichler Q P₁.e x₀, eichler_mem_orthDerived hQ hT _ _⟩
    hγ0 fun y => hφ y Submodule.mem_top).symm⟩

theorem mem_range_conj_of_fix_sylow_of_mem_image [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) (U : Sylow 2 (matrixProjectiveDerived Q))
    {β : MulAut (matrixProjectiveDerived Q)} (hβE : β ∈ matrixProjectiveImage Q)
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived Q)), β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow (isPGroup_rootGroupBar (Q := Q) P₁.e) U
  set β' := (MulAut.conj x)⁻¹ * β * MulAut.conj x with hβ'
  have hβ'E : β' ∈ matrixProjectiveImage Q := by
    have hc : MulAut.conj x ∈ matrixProjectiveImage Q :=
      matrixProjective_inner_le_image Q ⟨x, rfl⟩
    exact mul_mem (mul_mem (inv_mem hc) hβE) hc
  obtain ⟨z, hz⟩ := mem_range_conj_of_fix_rootGroup hQ hT h₁₂ hβ'E fun E hE => by
    have hy := hβ _ (hx _ ⟨E, hE, rfl⟩)
    rw [hβ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hy, MulAut.inv_apply,
      MulEquiv.symm_apply_eq, MulAut.conj_apply]
  refine ⟨x * z * x⁻¹, ?_⟩
  have hβeq : β = MulAut.conj x * β' * (MulAut.conj x)⁻¹ := by
    rw [hβ']
    group
  rw [hβeq, ← hz, map_mul, map_mul, map_inv]

end AutU

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem exists_sylow_map_mulEquiv [Finite Y] {p : ℕ} [Fact p.Prime] (e : X ≃* Y) (U : Sylow p X) :
    ∃ U' : Sylow p Y, ∀ x : X, x ∈ (U : Subgroup X) ↔ e x ∈ (U' : Subgroup Y) := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, fun x => ?_⟩
  change x ∈ (U : Subgroup X) ↔ e x ∈ (U : Subgroup X).map e.toMonoidHom
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mulAut_congr_conj' (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem autU_of_mulEquiv [Finite Y] (e : X ≃* Y)
    (hY : ∀ (U : Sylow 2 Y) (β : MulAut Y), (∀ u ∈ (U : Subgroup Y), β u = u) →
      β ∈ (MulAut.conj : Y →* MulAut Y).range)
    (U : Sylow 2 X) (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U', hU'⟩ := exists_sylow_map_mulEquiv e U
  obtain ⟨y, hy⟩ := hY U' (MulAut.congr e β) fun u hu => by
    obtain ⟨x, rfl⟩ := e.surjective u
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hβ x ((hU' x).2 hu)]
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [mulAut_congr_conj', MulEquiv.apply_symm_apply, ← hy]

end Transport

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_range_conj_of_fix_sylow_plus {n : ℕ} (hn : 5 ≤ n)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))), β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))).range := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have h0 := isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin n)
  have h1 := isHypCoord_coordinateQuadPlus (K := K) (⟨1, by omega⟩ : Fin n)
  refine mem_range_conj_of_fix_sylow_of_mem_image hQ hT
    (h0.orth h1 (pairDisjoint_plus (by simp [Fin.ext_iff]))) U ?_ hβ
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
  exact Subgroup.mem_top β

theorem mem_range_conj_of_fix_sylow_minus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)))
    (β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)))
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))),
      β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c) →*
      MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))).range := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have h0 := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c
    (⟨0, by omega⟩ : Fin (n - 1))
  have h1 := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c
    (⟨1, by omega⟩ : Fin (n - 1))
  refine mem_range_conj_of_fix_sylow_of_mem_image hQ hT
    (h0.orth h1 (pairDisjoint_minus _ (by simp [Fin.ext_iff]))) U ?_ hβ
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

theorem mem_range_conj_of_fix_sylow_plus_of_mulEquiv {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (hn : 5 ≤ n) (U : Sylow 2 X)
    (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range :=
  autU_of_mulEquiv e (fun U β hβ => mem_range_conj_of_fix_sylow_plus hn U β hβ) U β hβ

theorem mem_range_conj_of_fix_sylow_minus_of_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (U : Sylow 2 X)
    (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range :=
  autU_of_mulEquiv e (fun U β hβ => mem_range_conj_of_fix_sylow_minus hn hirr U β hβ) U β hβ

theorem autU2_minus_of_mulEquiv {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) :
    ∀ (U : Sylow 2 X) (β : MulAut X), β ^ 2 = 1 → (∀ u ∈ (U : Subgroup X), β u = u) →
      β ∈ (MulAut.conj : X →* MulAut X).range :=
  fun U β _ hβ => mem_range_conj_of_fix_sylow_minus_of_mulEquiv hn hirr e U β hβ

theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {x : X} {m : ℕ}
    (hx : x ^ 2 ^ m = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨m, Subtype.ext ?_⟩
  change (x ^ k) ^ 2 ^ m = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem mem_range_conj_of_fix_sylow_plus_four_of_pow
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) {m : ℕ} (hβm : β ^ 2 ^ m = 1)
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))), β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by omega)
  have h0 := isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin 4)
  have h1 := isHypCoord_coordinateQuadPlus (K := K) (⟨1, by omega⟩ : Fin 4)
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  obtain ⟨ψ, hψ⟩ := CFSG.ComponentClassification.RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four
    f.pos hK (Subgroup.zpowers β) (isPGroup_zpowers_of_pow_eq_one hβm)
  set β' := ψ⁻¹ * β * ψ with hβ'
  have hβ'E : β' ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    apply hψ
    refine ⟨β, Subgroup.mem_zpowers β, ?_⟩
    change MulAut.conj ψ⁻¹ β = β'
    rw [MulAut.conj_apply, inv_inv]
  set U' : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    U.mapSurjective (f := (ψ⁻¹ : MulAut _).toMonoidHom) (ψ⁻¹ : MulAut _).surjective with hU'
  have hU'β : ∀ u ∈ (U' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      β' u = u := by
    rintro _ ⟨u, hu, rfl⟩
    change (ψ⁻¹ * β * ψ) (ψ⁻¹ u) = ψ⁻¹ u
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hβ u hu]
  obtain ⟨z, hz⟩ := mem_range_conj_of_fix_sylow_of_mem_image hQ hT
    (h0.orth h1 (pairDisjoint_plus (by simp))) U' hβ'E hU'β
  refine ⟨ψ z, ?_⟩
  have hβeq : β = ψ * β' * ψ⁻¹ := by
    rw [hβ']
    group
  rw [hβeq, ← hz]
  ext y
  simp [MulAut.conj_apply]

theorem mem_range_conj_of_fix_sylow_plus_of_pow {n : ℕ} (hn : 4 ≤ n)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) {m : ℕ} (hβm : β ^ 2 ^ m = 1)
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))), β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))).range := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    exact mem_range_conj_of_fix_sylow_plus_four_of_pow U β hβm hβ
  · exact mem_range_conj_of_fix_sylow_plus h5 U β hβ

theorem mem_range_conj_of_fix_sylow_plus_of_mul_self {n : ℕ} (hn : 4 ≤ n)
    (U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus n K)))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hβ2 : β * β = 1)
    (hβ : ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))), β u = u) :
    β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))).range :=
  mem_range_conj_of_fix_sylow_plus_of_pow hn U β (m := 1) (by rw [pow_one, _root_.sq, hβ2]) hβ

theorem autU2_plus_of_mulEquiv {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (hn : 4 ≤ n) :
    ∀ (U : Sylow 2 X) (β : MulAut X), β ^ 2 = 1 → (∀ u ∈ (U : Subgroup X), β u = u) →
      β ∈ (MulAut.conj : X →* MulAut X).range := by
  intro U β hβ2 hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U', hU'⟩ := exists_sylow_map_mulEquiv e U
  obtain ⟨y, hy⟩ := mem_range_conj_of_fix_sylow_plus_of_pow hn U' (MulAut.congr e β) (m := 1)
    (by rw [pow_one, ← map_pow, hβ2, map_one]) fun u hu => by
      obtain ⟨x, rfl⟩ := e.surjective u
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hβ x ((hU' x).2 hu)]
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [mulAut_congr_conj', MulEquiv.apply_symm_apply, ← hy]

end Coordinates

end CFSG.SeitzReduction.OmegaPilot
