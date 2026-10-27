module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Defs

variable {K : Type} [Field K] (n : ℕ) (b c : K) (i j : Fin (n - 1))

@[expose] noncomputable def leafV₀ : Vm n K := minusVec n i true - minusVec n i false

@[expose] noncomputable def leafV₁ : Vm n K :=
  b • minusVec n i true + c • minusVec n j true - minusVec n j false

@[expose] noncomputable def leafIota : (Fin 2 → K) →ₗ[K] Vm n K :=
  (LinearMap.proj (0 : Fin 2)).smulRight (leafV₀ n i) +
    (LinearMap.proj (1 : Fin 2)).smulRight (leafV₁ n b c i j)

@[expose] noncomputable def planeLin : (Fin 2 → K) →ₗ[K] Vm n K where
  toFun := planeVec n
  map_add' := planeVec_add n
  map_smul' := fun r w => planeVec_smul n r w

theorem leafIota_apply (x : Fin 2 → K) :
    leafIota n b c i j x = x 0 • leafV₀ n i + x 1 • leafV₁ n b c i j := by
  simp [leafIota]

theorem planeLin_apply (w : Fin 2 → K) : planeLin n w = planeVec n w := rfl

end Defs

section Basic

variable {K : Type} [Field K] {n : ℕ} (b c : K) {i j : Fin (n - 1)} (hij : i ≠ j)

include hij

omit hij in
private theorem polar_v₀_v₀ :
    polar (quadMinus n K b c) (leafV₀ n i) (leafV₀ n i) = -2 := by
  unfold leafV₀
  simp only [polar_sub_left, polar_sub_right, polar_minusVec_minusVec n b c]
  simp
  ring

private theorem polar_v₀_v₁ :
    polar (quadMinus n K b c) (leafV₀ n i) (leafV₁ n b c i j) = -b := by
  unfold leafV₀ leafV₁
  simp only [polar_sub_left, polar_sub_right, polar_add_right, polar_smul_right,
    polar_minusVec_minusVec n b c]
  simp [hij]

private theorem polar_v₁_v₀ :
    polar (quadMinus n K b c) (leafV₁ n b c i j) (leafV₀ n i) = -b := by
  rw [polar_comm]
  exact polar_v₀_v₁ b c hij

private theorem polar_v₁_v₁ :
    polar (quadMinus n K b c) (leafV₁ n b c i j) (leafV₁ n b c i j) = -(2 * c) := by
  unfold leafV₁
  simp only [polar_sub_left, polar_sub_right, polar_add_left, polar_add_right, polar_smul_left,
    polar_smul_right, polar_minusVec_minusVec n b c]
  simp [hij, hij.symm]
  ring

theorem polar_leafIota (x y : Fin 2 → K) :
    polar (quadMinus n K b c) (leafIota n b c i j x) (leafIota n b c i j y) =
      -polar (quadMinus n K b c) (planeLin n x) (planeLin n y) := by
  rw [leafIota_apply, leafIota_apply, planeLin_apply, planeLin_apply, polar_planeVec_planeVec]
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    polar_v₀_v₀ (n := n) (i := i) b c, polar_v₀_v₁ b c hij, polar_v₁_v₀ b c hij,
    polar_v₁_v₁ b c hij, polarPlane, smul_eq_mul]
  ring

end Basic

section Main

variable {K : Type} [Field K] [Finite K] {n : ℕ} {b c : K}

theorem exists_leaf_frame (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hodd : Odd (Nat.card K))
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ∃ F_N : OPFrame (quadMinus n K b c),
      leafV₀ n i ∈ F_N.span ∧ (∀ w, planeVec n w ∈ F_N.span) ∧
      (∀ x ∈ F_N.span, ∀ k : Fin (n - 1), k ≠ i → k ≠ j → ∀ u,
        polar (quadMinus n K b c) x (minusVec n k u) = 0) ∧
      ((minusHyp n b c).toFrame hij s t).La (-1) * F_N.La (-1) =
        F_N.La (-1) * ((minusHyp n b c).toFrame hij s t).La (-1) ∧
      Module.finrank K ↥(((minusHyp n b c).toFrame hij s t).span ⊓ F_N.span) = 2 ∧
      ¬ Commutes ((minusHyp n b c).toFrame hij s t).La.range F_N.La.range ∧
      ((minusHyp n b c).toFrame hij s t).La.range ≠ F_N.La.range := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hΔ : (4 * c - b ^ 2 : K) ≠ 0 := CFSG.LieType.BorelTits.four_mul_sub_sq_ne_zero hirr
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : K, Δ = 4 * c - b ^ 2 := ⟨_, rfl⟩
  have hΔ' : Δ ≠ 0 := hΔdef ▸ hΔ
  let w : Fin 2 → Fin 2 → K := fun a => Pi.single a 1
  let w' : Fin 2 → Fin 2 → K := ![![2 * c / Δ, -b / Δ], ![-b / Δ, 2 / Δ]]
  have hdual : ∀ a a', polar (quadMinus n K b c) (planeLin n (w a)) (planeLin n (w' a')) =
      if a = a' then 1 else 0 := by
    intro a a'
    rw [planeLin_apply, planeLin_apply, polar_planeVec_planeVec]
    fin_cases a <;> fin_cases a' <;> simp [polarPlane, w, w'] <;> field_simp <;> rw [hΔdef] <;>
      ring
  have hw : ∀ x : Fin 2 → K, ∃ a b' : K, x = a • w 0 + b' • w 1 := fun x =>
    ⟨x 0, x 1, by
      ext k
      fin_cases k <;> simp [w]⟩
  have hw' : ∀ x : Fin 2 → K, ∃ a b' : K, x = a • w' 0 + b' • w' 1 := fun x =>
    ⟨2 * x 0 + b * x 1, b * x 0 + 2 * c * x 1, by
      ext k
      fin_cases k <;> simp [w'] <;> field_simp <;> rw [hΔdef] <;> ring⟩
  have hQι : ∀ x, quadMinus n K b c (leafIota n b c i j x) = -quadMinus n K b c (planeLin n x) :=
    fun x => by
    have h := polar_leafIota b c hij x x
    rw [polar_self_eq_two_mul, polar_self_eq_two_mul] at h
    have h' : (2 : K) * (quadMinus n K b c (leafIota n b c i j x) +
        quadMinus n K b c (planeLin n x)) = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp h').resolve_left h2
    linear_combination this
  have horth : ∀ x y, polar (quadMinus n K b c) (leafIota n b c i j x) (planeLin n y) = 0 :=
    fun x y => by
    rw [leafIota_apply, planeLin_apply]
    unfold leafV₀ leafV₁
    simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_minusVec_planeVec n b c]
    simp
  obtain ⟨F_N, hι, hα, hle⟩ := exists_frame_of_neg_planes h2 (leafIota n b c i j) (planeLin n)
    hQι horth w w' hdual hw hw'
  set F_D := (minusHyp n b c).toFrame hij s t with hFD
  have hvecD : ∀ k : Fin (n - 1), (k = i ∨ k = j) → ∀ r, minusVec n k r ∈ F_D.span :=
    fun k hk r => Balance.Bootstrap.vec_mem_span_toFrame (minusHyp n b c) hij s t hk r
  have hD1 : ∀ x, leafIota n b c i j x ∈ F_D.span := fun x => by
    rw [leafIota_apply]
    unfold leafV₀ leafV₁
    exact F_D.span.add_mem (F_D.span.smul_mem _ (F_D.span.sub_mem (hvecD i (Or.inl rfl) true)
      (hvecD i (Or.inl rfl) false)))
      (F_D.span.smul_mem _ (F_D.span.sub_mem (F_D.span.add_mem
        (F_D.span.smul_mem _ (hvecD i (Or.inl rfl) true))
        (F_D.span.smul_mem _ (hvecD j (Or.inr rfl) true))) (hvecD j (Or.inr rfl) false)))
  have hD2 : ∀ x, planeLin n x ∈ F_D.perp := fun x => by
    rw [Frame.mem_perp_iff_forall_incl]
    intro Y
    simp only [Frame.incl_apply, polar_add_right, polar_smul_right, planeLin_apply]
    simp [hFD, HypFrame.toFrame, polar_planeVec_minusVec n b c]
  obtain ⟨hcomm, hinter, hinj⟩ := neg_planes_data h2 F_D F_N (leafIota n b c i j) (planeLin n)
    hQι w w' hdual hw hι hα hle hD1 hD2
  have hfin : Module.finrank K ↥(F_D.span ⊓ F_N.span) = 2 := by
    rw [hinter, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have hFDiso : IsFundamental (quadMinus n K b c) F_D.La.range (F_D.La (-1)) :=
    IsFundamental.of_frame F_D
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : Vm n K, u₂ = c • minusVec n j true + minusVec n j false :=
    ⟨_, rfl⟩
  have hv₀ι : leafIota n b c i j (Pi.single 0 1) = leafV₀ n i := by
    rw [leafIota_apply]
    simp
  have hv₀N : leafV₀ n i ∈ F_N.span := hv₀ι ▸ hι _
  have hv₀D : leafV₀ n i ∈ F_D.span := hv₀ι ▸ hD1 _
  have hu₂D : u₂ ∈ F_D.span := by
    rw [hu₂]
    exact F_D.span.add_mem (F_D.span.smul_mem _ (hvecD j (Or.inr rfl) true))
      (hvecD j (Or.inr rfl) false)
  have hu₂ι : ∀ x, polar (quadMinus n K b c) u₂ (leafIota n b c i j x) = 0 := fun x => by
    rw [leafIota_apply, hu₂]
    unfold leafV₀ leafV₁
    simp only [polar_add_left, polar_add_right, polar_sub_right, polar_smul_left,
      polar_smul_right, polar_minusVec_minusVec n b c]
    simp [hij.symm]
  have hu₂α : ∀ x, polar (quadMinus n K b c) u₂ (planeLin n x) = 0 := fun x => by
    rw [planeLin_apply, hu₂]
    simp only [polar_add_left, polar_smul_left, polar_minusVec_planeVec n b c]
    simp
  have hu₂N : u₂ ∈ F_N.perp := by
    rw [Frame.mem_perp_iff_forall_incl F_N]
    intro Y
    obtain ⟨y, ⟨a, rfl⟩, z, ⟨a', rfl⟩, hsum⟩ := Submodule.mem_sup.mp (hle ⟨Y, rfl⟩)
    rw [← hsum, polar_add_right, hu₂ι, hu₂α, add_zero]
  have hperpN : ∀ x ∈ F_N.span, ∀ k : Fin (n - 1), k ≠ i → k ≠ j → ∀ u,
      polar (quadMinus n K b c) x (minusVec n k u) = 0 := by
    intro x hx k hki hkj u
    obtain ⟨y, ⟨a, rfl⟩, z, ⟨a', rfl⟩, rfl⟩ := Submodule.mem_sup.mp (hle hx)
    rw [polar_add_left, planeLin_apply, polar_planeVec_minusVec n b c, add_zero, leafIota_apply]
    unfold leafV₀ leafV₁
    simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_minusVec_minusVec n b c]
    simp [hki.symm, hkj.symm]
  have hv₀ne : leafV₀ (K := K) n i ≠ 0 := by
    intro h
    have : polar (quadMinus n K b c) (leafV₀ n i) (minusVec n i false) = 1 := by
      unfold leafV₀
      simp only [polar_sub_left, polar_minusVec_minusVec n b c]
      simp
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hu₂ne : u₂ ≠ 0 := by
    intro h
    have : polar (quadMinus n K b c) u₂ (minusVec n j true) = 1 := by
      rw [hu₂]
      simp only [polar_add_left, polar_smul_left, polar_minusVec_minusVec n b c]
      simp
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hncomm : ¬ Commutes F_D.La.range F_N.La.range := by
    intro hc
    have hcg : ∀ l ∈ F_D.La.range, F_N.La (-1) * l = l * F_N.La (-1) := fun l hl =>
      (hc l hl _ ⟨-1, rfl⟩).symm
    have hneg : negSpace (F_D.La (-1)) = F_D.span := negSpace_La_neg_one h2 F_D
    exact eigen_contradiction h2 hFDiso (F_N.La_mem_orthogonalGroup (-1)) F_N.La_neg_one_mul_self
      hcg (hneg ▸ hv₀D) (hneg ▸ hu₂D) hv₀ne hu₂ne
      ((Frame.mem_span_iff_inv F_N h2).mp hv₀N) ((Frame.mem_perp_iff_fix F_N h2).mp hu₂N)
  have hne : F_D.La.range ≠ F_N.La.range := by
    intro h
    have h1 : IsFundamental (quadMinus n K b c) F_D.La.range (F_N.La (-1)) := by
      rw [h]
      exact IsFundamental.of_frame F_N
    have h2' : F_D.La (-1) = F_N.La (-1) := IsFundamental.involution_unique hodd hFDiso h1
    have hsp : F_D.span = F_N.span := by
      rw [← negSpace_La_neg_one h2 F_D, ← negSpace_La_neg_one h2 F_N, h2']
    have h4 : Module.finrank K ↥(F_D.span ⊓ F_N.span) = 4 := by
      rw [← hsp, inf_idem]
      exact Frame.finrank_span F_D
    omega
  exact ⟨F_N, hv₀N, hα, hperpN, hcomm, hfin, hncomm, hne⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TwinSmall
