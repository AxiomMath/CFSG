module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.RootSL2.Adjust
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem ringEquiv_eq_id_of_trace {K : Type} [Field K] (σ : K ≃+* K)
    (h3 : ∀ x, σ (σ (σ x)) = x)
    (hg : ∀ t : K, t ≠ 0 → (t + t⁻¹) ^ 2 + 8 * (t + t⁻¹) =
      (σ t + (σ t)⁻¹) ^ 2 + 8 * (σ t + (σ t)⁻¹)) : ∀ x, σ x = x := by
  have key : ∀ t : K, t ≠ 0 → σ (t + t⁻¹) = t + t⁻¹ := by
    intro t ht
    have hs : σ (t + t⁻¹) = σ t + (σ t)⁻¹ := by rw [map_add, map_inv₀]
    have h := hg t ht
    set u := t + t⁻¹ with hu
    set s := σ u with hsdef
    have hs' : s = σ t + (σ t)⁻¹ := hs
    rw [← hs'] at h
    have hfac : (u - s) * (u + s + 8) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact (sub_eq_zero.1 h1).symm
    · have hs2 : s = -8 - u := by linear_combination h1
      have hss : σ s = u := by
        rw [hs2, map_sub, map_neg, map_ofNat, ← hsdef]
        linear_combination (-1 : K) * hs2
      have := h3 u
      rw [← hsdef, hss] at this
      exact this
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hk := key x hx
  rw [map_add, map_inv₀] at hk
  have hy : σ x ≠ 0 := (map_ne_zero σ).2 hx
  have hfac : (σ x - x) * (1 - (x * σ x)⁻¹) = 0 := by
    have e : (σ x - x) * (1 - (x * σ x)⁻¹) = (σ x + (σ x)⁻¹) - (x + x⁻¹) := by
      field_simp
      ring
    rw [e, hk, sub_self]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact sub_eq_zero.1 h1
  · have h2 : x * σ x = 1 := by
      have : (x * σ x)⁻¹ = 1 := by linear_combination -h1
      exact inv_eq_one.1 this
    have h3' : σ x = x⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : σ (σ x) = x := by rw [h3', map_inv₀, h3', inv_inv]
    have := h3 x
    rw [h4] at this
    exact this

theorem rootExponents_D4 (i : Fin Tag.D4.rank) :
    (rootExponents .D4 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .D4 i).count (-2) = 1 ∧
      (rootExponents .D4 i).count (-1) = 8 ∧ (rootExponents .D4 i).count 0 = 6 ∧
      (rootExponents .D4 i).count 1 = 8 ∧ (rootExponents .D4 i).count 2 = 1 := by
  revert i
  decide +kernel

section Torus


variable {K : Type} [Field K]

theorem trace_torusElt_D4 (i : Fin Tag.D4.rank) (c : Kˣ) :
    LinearMap.trace K (RootModule Tag.D4 K)
        (torusElt Tag.D4 K i c : Module.End K (RootModule Tag.D4 K)) =
      ((c : K) + ((c⁻¹ : Kˣ) : K)) ^ 2 + 8 * ((c : K) + ((c⁻¹ : Kˣ) : K)) + 8 := by
  have h := sum_torusEigen_of_counts (L := K) i c (rootExponents_D4 i)
  have h2 : LinearMap.trace K (RootModule Tag.D4 K)
      (torusElt Tag.D4 K i c : Module.End K (RootModule Tag.D4 K)) =
        ∑ b : Label Tag.D4, torusEigen i c b := by
    rw [trace_rootModule_eq_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [CFSG.RankThree.Chevalley.torusElt_single]
    simp
  rw [h2, h]
  norm_num [Tag.rank]

end Torus

section Main


variable {K : Type} [Field K] [Finite K]

theorem normalizer_inner {i : Fin Tag.D4.rank} {Φ : ModGL Tag.D4 K}
    {η : MulAut (adjointGroup Tag.D4 K)}
    (hΦ : ∀ x : adjointGroup Tag.D4 K,
      ((η x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = Φ * (x : ModGL Tag.D4 K) * Φ⁻¹)
    (hη3 : ∀ x, η (η (η x)) = x)
    (hηJ : (rankOneRep Tag.D4 K i).range.map η.toMonoidHom = (rankOneRep Tag.D4 K i).range) :
    ∃ w ∈ (rankOneRep Tag.D4 K i).range, ∀ y ∈ (rankOneRep Tag.D4 K i).range,
      η y = w * y * w⁻¹ := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨v, hv, hα⟩ := exists_pairAut_adjust (rankOneRep_ker i) hηJ
  rw [sl2RootX_rankOneRep, sl2RootY_rankOneRep] at hα
  obtain ⟨a, σ, hx, hy, hd⟩ := exists_rankOne_params hα
  set ρ := rankOneRep Tag.D4 K i with hρ
  set α : MulAut (adjointGroup Tag.D4 K) := MulAut.conj v * η with hαdef
  have hJη : ∀ y ∈ ρ.range, η y ∈ ρ.range := fun y hy => by
    have : η y ∈ ρ.range.map η.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rwa [hηJ] at this
  set e : adjointGroup Tag.D4 K := v * η v * η (η v) with hedef
  have hα3 : ∀ x, α (α (α x)) = e * x * e⁻¹ := by
    intro x
    simp only [hαdef, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hη3, hedef]
    group
  have hX3 : ∀ c, e * adjX Tag.D4 K i c * e⁻¹ =
      adjX Tag.D4 K i ((a : K) * σ ((a : K) * σ ((a : K) * σ c))) := by
    intro c
    rw [← hα3, hx, hx, hx]
  have he : e ∈ ρ.range := mul_mem (mul_mem hv (hJη _ hv)) (hJη _ (hJη _ hv))
  obtain ⟨p, hp⟩ := exists_sq_of_conj_upper (rankOneRep_ker i) he
    (μ := fun c => (a : K) * σ ((a : K) * σ ((a : K) * σ c)))
    (fun c => by rw [rankOneRep_upper, hX3 c, rankOneRep_upper])
  have hexp : ∀ c, (a : K) * σ ((a : K) * σ ((a : K) * σ c)) =
      ((a : K) * σ a * σ (σ a)) * σ (σ (σ c)) := by
    intro c
    simp only [map_mul]
    ring
  have hN : (a : K) * σ a * σ (σ a) = (p : K) ^ 2 := by
    have h1 := hp 1
    rw [hexp, map_one, map_one, map_one, mul_one, mul_one] at h1
    exact h1
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    have h1 := hp x
    rw [hexp, hN] at h1
    have hp2 : (p : K) ^ 2 ≠ 0 := pow_ne_zero 2 p.ne_zero
    exact mul_left_cancel₀ hp2 h1
  have hconj : ∀ t : Kˣ, ((v : ModGL Tag.D4 K) * Φ) * torusElt Tag.D4 K i t *
      ((v : ModGL Tag.D4 K) * Φ)⁻¹ = torusElt Tag.D4 K i (Units.map σ.toMonoidHom t) := by
    intro t
    have h := congrArg (fun x : adjointGroup Tag.D4 K => (x : ModGL Tag.D4 K)) (hd t)
    simp only [hαdef, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      hΦ] at h
    rw [mul_inv_rev]
    calc _ = (v : ModGL Tag.D4 K) * (Φ * torusElt Tag.D4 K i t * Φ⁻¹) * (v : ModGL Tag.D4 K)⁻¹ := by
          group
      _ = _ := h
  have htrace : ∀ t : Kˣ, ((t : K) + ((t⁻¹ : Kˣ) : K)) ^ 2 + 8 * ((t : K) + ((t⁻¹ : Kˣ) : K)) =
      (σ (t : K) + (σ (t : K))⁻¹) ^ 2 + 8 * (σ (t : K) + (σ (t : K))⁻¹) := by
    intro t
    have h1 : LinearMap.trace K (RootModule Tag.D4 K)
        (torusElt Tag.D4 K i (Units.map σ.toMonoidHom t) : Module.End K (RootModule Tag.D4 K)) =
        LinearMap.trace K (RootModule Tag.D4 K)
          (torusElt Tag.D4 K i t : Module.End K (RootModule Tag.D4 K)) := by
      set Ψ : ModGL Tag.D4 K := (v : ModGL Tag.D4 K) * Φ with hΨ
      rw [← hconj t]
      have h2 : ((Ψ * torusElt Tag.D4 K i t * Ψ⁻¹ : ModGL Tag.D4 K) :
          Module.End K (RootModule Tag.D4 K)) =
          (Ψ : Module.End K (RootModule Tag.D4 K)) *
            ((torusElt Tag.D4 K i t : Module.End K (RootModule Tag.D4 K)) *
              ((Ψ⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))) := by
        simp only [Units.val_mul, mul_assoc]
      rw [h2, LinearMap.trace_mul_comm, mul_assoc, Units.inv_mul, mul_one]
    rw [trace_torusElt_D4, trace_torusElt_D4] at h1
    simp only [Units.coe_map, Units.val_inv_eq_inv_val] at h1
    have h1' : (σ (t : K) + (σ (t : K))⁻¹) ^ 2 + 8 * (σ (t : K) + (σ (t : K))⁻¹) + 8 =
        ((t : K) + (t : K)⁻¹) ^ 2 + 8 * ((t : K) + (t : K)⁻¹) + 8 := h1
    rw [Units.val_inv_eq_inv_val]
    linear_combination -h1'
  have hσ : ∀ x, σ x = x := ringEquiv_eq_id_of_trace σ hσ3 fun t ht => by
    simpa using htrace (Units.mk0 t ht)
  have hN3 : (a : K) ^ 3 = (p : K) ^ 2 := by
    simp only [hσ] at hN
    linear_combination hN
  obtain ⟨r, hr2⟩ : ∃ r : Kˣ, (r : K) ^ 2 = (a : K) := by
    refine ⟨a ^ 2 * p⁻¹, ?_⟩
    have ha : (a : K) ≠ 0 := a.ne_zero
    have hp0 : (p : K) ≠ 0 := p.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hN3
  have hx' : ∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K ((r : K) ^ 2 * c)) := by
    intro c
    rw [rankOneRep_upper, hx, rankOneRep_upper, hr2, hσ]
  have hy' : ∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (((r⁻¹ : Kˣ) : K) ^ 2 * c)) := by
    intro c
    rw [rankOneRep_lower, hy, rankOneRep_lower, hσ]
    congr 2
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, hr2]
  have hconjd := eq_conj_diag (ρ := ρ) (α := α) (r := r) hx' hy'
  refine ⟨v⁻¹ * ρ (sl2Diag K r), mul_mem (inv_mem hv) ⟨_, rfl⟩, fun y hy => ?_⟩
  have h1 := hconjd y hy
  have h2 : α y = v * η y * v⁻¹ := rfl
  rw [h2] at h1
  calc η y = v⁻¹ * (v * η y * v⁻¹) * v := by group
    _ = v⁻¹ * (ρ (sl2Diag K r) * y * (ρ (sl2Diag K r))⁻¹) * v := by rw [h1]
    _ = (v⁻¹ * ρ (sl2Diag K r)) * y * (v⁻¹ * ρ (sl2Diag K r))⁻¹ := by group

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2
