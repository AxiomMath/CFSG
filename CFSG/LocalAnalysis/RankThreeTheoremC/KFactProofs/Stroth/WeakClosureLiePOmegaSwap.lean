module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieFormDet
public import CFSG.GroupTheory.WeirSylow.OrthogonalTori
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module QuadraticMap
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] noncomputable def negIsom {S₀ : FormSpace K K} (hS₀ : IsQuadSpace S₀) : S₀.isom :=
  ⟨LinearEquiv.neg K, mem_formIsometryGroup.2 fun x y => by
    obtain ⟨Q, hQF, -⟩ := hS₀
    rw [LinearEquiv.neg_apply, hQF, hQF, QuadraticMap.map_neg]⟩

private theorem negIsom_apply {S₀ : FormSpace K K} (hS₀ : IsQuadSpace S₀) (v : S₀.V) :
    (negIsom hS₀ : S₀.V ≃ₗ[K] S₀.V) v = -v :=
  rfl

theorem negIsom_conj {S₀ : FormSpace K K} (hS₀ : IsQuadSpace S₀) (g : S₀.isom) :
    negIsom hS₀ * g * (negIsom hS₀)⁻¹ = g := by
  have hcomm : negIsom hS₀ * g = g * negIsom hS₀ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp [negIsom]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem swap_polar_smul {V : Type} [AddCommGroup V] [Module K V] (c : K)
    (Q : QuadraticForm K V) (x y : V) : polar (c • Q) x y = c * polar Q x y := by
  simp only [polar, QuadraticMap.smul_apply, smul_eq_mul]
  ring

private theorem swap_parallelogram {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) : Q (x + y) + Q (x - y) = 2 * (Q x + Q y) := by
  have h1 : Q (x - y) = Q x + Q y - polar Q x y := by
    rw [sub_eq_add_neg x y, QuadraticMap.map_add Q x (-y), QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right]
    ring
  rw [QuadraticMap.map_add Q x y, h1]
  ring

private noncomputable def swapBlockLin {V : Type} [AddCommGroup V] [Module K V]
    (τ : V ≃ₗ[K] V) : (Fin 2 → V) →ₗ[K] (Fin 2 → V) :=
  LinearMap.pi ![τ.toLinearMap.comp ((LinearMap.proj 0 : (Fin 2 → V) →ₗ[K] V) -
      (LinearMap.proj 1 : (Fin 2 → V) →ₗ[K] V)),
    τ.toLinearMap.comp ((LinearMap.proj 0 : (Fin 2 → V) →ₗ[K] V) +
      (LinearMap.proj 1 : (Fin 2 → V) →ₗ[K] V))]

private theorem swapBlockLin_zero {V : Type} [AddCommGroup V] [Module K V] (τ : V ≃ₗ[K] V)
    (x : Fin 2 → V) : swapBlockLin τ x 0 = τ (x 0 - x 1) :=
  rfl

private theorem swapBlockLin_one {V : Type} [AddCommGroup V] [Module K V] (τ : V ≃ₗ[K] V)
    (x : Fin 2 → V) : swapBlockLin τ x 1 = τ (x 0 + x 1) :=
  rfl

private theorem swapBlockLin_injective {V : Type} [AddCommGroup V] [Module K V]
    (hK : (2 : K) ≠ 0) (τ : V ≃ₗ[K] V) : Function.Injective (swapBlockLin τ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : τ (x 0 - x 1) = 0 := (swapBlockLin_zero τ x).symm.trans (congrFun hx 0)
  have h1 : τ (x 0 + x 1) = 0 := (swapBlockLin_one τ x).symm.trans (congrFun hx 1)
  have ha : x 0 - x 1 = 0 := by rwa [LinearEquiv.map_eq_zero_iff] at h0
  have hb : x 0 + x 1 = 0 := by rwa [LinearEquiv.map_eq_zero_iff] at h1
  have h2 : (2 : K) • x 0 = 0 := by
    rw [two_smul]
    calc x 0 + x 0 = (x 0 - x 1) + (x 0 + x 1) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  have hx0 : x 0 = 0 := (smul_eq_zero.1 h2).resolve_left hK
  have hx1 : x 1 = 0 := (sub_eq_zero.1 ha).symm.trans hx0
  funext i
  fin_cases i
  · exact hx0
  · exact hx1

private noncomputable def swapBlockEquiv {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : (2 : K) ≠ 0) (τ : V ≃ₗ[K] V) :
    (Fin 2 → V) ≃ₗ[K] (Fin 2 → V) :=
  LinearEquiv.ofBijective (swapBlockLin τ)
    ⟨swapBlockLin_injective hK τ,
      LinearMap.injective_iff_surjective.1 (swapBlockLin_injective hK τ)⟩

private theorem swapBlockLin_sum {V : Type} [AddCommGroup V] [Module K V] (Q₀ : QuadraticForm K V)
    (hK : (2 : K) ≠ 0) (τ : V ≃ₗ[K] V) (hτ : ∀ v, Q₀ (τ v) = (2 : K)⁻¹ * Q₀ v) (x : Fin 2 → V) :
    Q₀ (swapBlockLin τ x 0) + Q₀ (swapBlockLin τ x 1) = Q₀ (x 0) + Q₀ (x 1) := by
  rw [swapBlockLin_zero, swapBlockLin_one, hτ, hτ, ← mul_add, add_comm (Q₀ (x 0 - x 1)),
    swap_parallelogram Q₀ (x 0) (x 1), ← mul_assoc, inv_mul_cancel₀ hK, one_mul]

private theorem swap_mul_mem_commutator_of_conj {G : Type} [Group G] {S h m : G}
    (hSS : S * S = 1) (hm : h * S * h⁻¹ = m) : S * m ∈ commutator G := by
  have hSinv : S⁻¹ = S := inv_eq_of_mul_eq_one_right hSS
  have key : S * m = ⁅S, h⁆ := by
    rw [commutatorElement_def, hSinv, ← hm]
    simp only [mul_assoc]
  rw [key]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top S) (Subgroup.mem_top h)

private theorem swap_conj_factor {G : Type} [Group G] (S m T : G) :
    S * m * T * (S * m)⁻¹ = S * (m * T * m⁻¹) * S⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

private theorem swap_sub_comm_charTwo [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    (a b : W) : a - b = b - a := by
  rw [CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K,
    CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K, add_comm]

theorem swap_mul_negIsom_mem_commutator (hK : (2 : K) ≠ 0) [Finite K] {S₀ : FormSpace K K}
    (hS₀ : IsQuadSpace S₀) {d : ℕ} (hdim : finrank K S₀.V = 2 * d) :
    piPermIsom S₀ 2 (Equiv.swap 0 1) * piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)) ∈
      commutator (FormSpace.pi fun _ : Fin 2 => S₀).isom := by
  obtain ⟨Q₀, hQF, hnd⟩ := id hS₀
  have hQ'nd : (polarBilin ((2 : K)⁻¹ • Q₀)).Nondegenerate := by
    refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
    refine hnd.1 v fun w => ?_
    rw [polarBilin_apply_apply]
    have h := hv w
    rw [swap_polar_smul] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hK)
  have hPlus : IsPlusType ((2 : K)⁻¹ • Q₀) ↔ IsPlusType Q₀ := by
    constructor
    · rintro ⟨W, hW, hWs⟩
      refine ⟨W, hW, fun x hx => ?_⟩
      have h := hWs x hx
      rw [QuadraticMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hK)
    · rintro ⟨W, hW, hWs⟩
      refine ⟨W, hW, fun x hx => ?_⟩
      rw [QuadraticMap.smul_apply, smul_eq_mul, hWs x hx, mul_zero]
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hQ'nd hnd hdim hdim hPlus
  obtain ⟨τ, hτ⟩ : ∃ τ : S₀.V ≃ₗ[K] S₀.V, ∀ v, Q₀ (τ v) = (2 : K)⁻¹ * Q₀ v := by
    refine ⟨e.toLinearEquiv, fun v => ?_⟩
    have h := e.map_app v
    rw [QuadraticMap.smul_apply, smul_eq_mul] at h
    exact h
  have hE : swapBlockEquiv hK τ ∈ (FormSpace.pi fun _ : Fin 2 => S₀).isom := by
    refine mem_formIsometryGroup.2 fun x y => ?_
    change ∑ i, S₀.F (swapBlockLin τ x i) (swapBlockLin τ y i) = ∑ i, S₀.F (x i) (y i)
    simp only [hQF, Fin.sum_univ_two]
    exact swapBlockLin_sum Q₀ hK τ hτ x
  obtain ⟨h, hh⟩ : ∃ h : (FormSpace.pi fun _ : Fin 2 => S₀).isom,
      ∀ x, (h : (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V)) x = swapBlockLin τ x :=
    ⟨⟨swapBlockEquiv hK τ, hE⟩, fun x => rfl⟩
  have hconj : h * piPermIsom S₀ 2 (Equiv.swap 0 1) =
      piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)) * h := by
    apply Subtype.ext
    refine LinearEquiv.ext fun (x : Fin 2 → S₀.V) => ?_
    change (h : (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V))
        ((piPermIsom S₀ 2 (Equiv.swap 0 1) : (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V)) x) =
      (piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)) : (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V))
        ((h : (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V)) x)
    rw [hh, hh]
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [swapBlockLin_zero, piPermIsom_apply, piPermIsom_apply, piDiagIsom_apply,
        Pi.mulSingle_eq_same, negIsom_apply, swapBlockLin_zero, Equiv.swap_inv,
        Equiv.swap_apply_left, Equiv.swap_apply_right, ← neg_sub (x 0) (x 1), map_neg]
    · rw [swapBlockLin_one, piPermIsom_apply, piPermIsom_apply, piDiagIsom_apply,
        Pi.mulSingle_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), Equiv.swap_inv,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
      show τ (x 1 + x 0) = τ (x 0 + x 1)
      rw [add_comm]
  have hm : h * piPermIsom S₀ 2 (Equiv.swap 0 1) * h⁻¹ =
      piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)) := by
    rw [hconj, mul_assoc, mul_inv_cancel, mul_one]
  have hSS : piPermIsom S₀ 2 (Equiv.swap 0 1) * piPermIsom S₀ 2 (Equiv.swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  exact swap_mul_mem_commutator_of_conj hSS hm

theorem finrank_commSpace_swap [CharP K 2] (S₀ : FormSpace K K) :
    finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
      ((piPermIsom S₀ 2 (Equiv.swap 0 1) : (FormSpace.pi fun _ : Fin 2 => S₀).isom) :
        (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V))) = finrank K S₀.V := by
  let ι : S₀.V →ₗ[K] (Fin 2 → S₀.V) := LinearMap.pi fun _ => LinearMap.id
  have hι : Function.Injective ι := fun a b hab => congrFun hab 0
  have hιapply : ∀ (a : S₀.V) (i : Fin 2), ι a i = a := fun _ _ => rfl
  have hsub : CFSG.RankThree.OrthogonalInvolutions.commSpace
      ((piPermIsom S₀ 2 (Equiv.swap 0 1) : (FormSpace.pi fun _ : Fin 2 => S₀).isom) :
        (Fin 2 → S₀.V) ≃ₗ[K] (Fin 2 → S₀.V)) = LinearMap.range ι := by
    ext x
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace, LinearMap.mem_range]
    constructor
    · rintro ⟨(v : Fin 2 → S₀.V), rfl⟩
      refine ⟨v 1 - v 0, ?_⟩
      refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · rw [hιapply, Pi.sub_apply, piPermIsom_apply, Equiv.swap_inv, Equiv.swap_apply_left]
      · rw [hιapply, Pi.sub_apply, piPermIsom_apply, Equiv.swap_inv, Equiv.swap_apply_right]
        exact swap_sub_comm_charTwo (K := K) _ _
    · rintro ⟨a, rfl⟩
      refine ⟨(Pi.single (1 : Fin 2) a : Fin 2 → S₀.V), ?_⟩
      refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · rw [hιapply, Pi.sub_apply, piPermIsom_apply, Equiv.swap_inv, Equiv.swap_apply_left,
          Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), sub_zero]
      · rw [hιapply, Pi.sub_apply, piPermIsom_apply, Equiv.swap_inv, Equiv.swap_apply_right,
          Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), zero_sub]
        exact CFSG.RankThree.OrthogonalInvolutions.neg_vec_eq K a
  rw [hsub, LinearMap.finrank_range_of_inj hι]

theorem swap_mul_negIsom_conj {S₀ : FormSpace K K} (hS₀ : IsQuadSpace S₀) {C : Type} [Group C]
    (ρ : C →* S₀.isom) (c : Fin 2 → C) :
    (piPermIsom S₀ 2 (Equiv.swap 0 1) * piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀))) *
        piDiagIsom S₀ 2 (fun i => ρ (c i)) *
        (piPermIsom S₀ 2 (Equiv.swap 0 1) * piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)))⁻¹ =
      piDiagIsom S₀ 2 (fun i => ρ ((c ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) i)) := by
  have hmT : piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)) *
      piDiagIsom S₀ 2 (fun i => ρ (c i)) *
      (piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀)))⁻¹ =
      piDiagIsom S₀ 2 (fun i => ρ (c i)) := by
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Pi.mulSingle_eq_same]
      exact mul_inv_eq_iff_eq_mul.1 (negIsom_conj hS₀ (ρ (c 0)))
    · rw [Pi.mulSingle_eq_of_ne hi, one_mul, mul_one]
  have hST : piPermIsom S₀ 2 (Equiv.swap 0 1) * piDiagIsom S₀ 2 (fun i => ρ (c i)) *
      (piPermIsom S₀ 2 (Equiv.swap 0 1))⁻¹ =
      piDiagIsom S₀ 2 (fun i => ρ ((c ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) i)) := by
    rw [piPermIsom_conj, Equiv.swap_inv]
    rfl
  rw [swap_conj_factor, hmT, hST]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
