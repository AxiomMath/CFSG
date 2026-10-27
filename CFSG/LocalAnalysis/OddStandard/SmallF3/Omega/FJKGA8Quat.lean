module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSimil
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Lin
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fj_polar_self_of_sq {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ x y, polar Q (g x) (g y) = polar Q x y) {x : V} (hx : g (g x) = -x) :
    polar Q x (g x) = 0 := by
  have h1 : polar Q (g x) (g (g x)) = polar Q x (g x) := hg x (g x)
  rw [hx, polar_neg_right, polar_comm Q (g x) x] at h1
  have h2 : (2 : ZMod 3) * polar Q x (g x) = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

private theorem fj_polar_adj_of_sq {g R : V ≃ₗ[ZMod 3] V}
    (hg : ∀ x y, polar Q (g x) (g y) = polar Q x y)
    (hR : ∀ x y, polar Q (R x) y = polar Q x (R y)) (hc : ∀ x, R (g x) = g (R x)) {x : V}
    (hx : g (g (R x)) = -R x) : polar Q (R x) (g x) = 0 := by
  have h1 : polar Q (R x) (g x) = polar Q x (g (R x)) := by rw [hR, hc]
  have h2 : polar Q x (g (R x)) = polar Q (g x) (g (g (R x))) := (hg x (g (R x))).symm
  rw [hx, polar_neg_right, polar_comm Q (g x) (R x)] at h2
  have h3 : (2 : ZMod 3) * polar Q (R x) (g x) = 0 := by linear_combination h1 + h2
  exact (mul_eq_zero.mp h3).resolve_left (by decide)

private theorem fj_exists_polar_self_ne_zero {W : Submodule (ZMod 3) V}
    (hW : (Q.restrict W).Nondegenerate) (hne : W ≠ ⊥) : ∃ u ∈ W, polar Q u u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hQ0 : ∀ x ∈ W, Q x = 0 := by
    intro x hx
    have h := hcon x hx
    rw [polar_self, two_smul] at h
    have h2 : (2 : ZMod 3) * Q x = 0 := by rw [two_mul]; exact h
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  have hrad : (⟨w, hw⟩ : W) ∈ (Q.restrict W).radical := by
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hQ0 w hw, fun y => ?_⟩
    change Q (w + (y : V)) = Q (y : V)
    rw [hQ0 _ (W.add_mem hw y.2), hQ0 _ y.2]
  rw [hW.radical_eq_bot, Submodule.mem_bot] at hrad
  exact hw0 (congrArg Subtype.val hrad)

private theorem fj_polar_coeff {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → V}
    {c : ι → ZMod 3} {x : V} (h0 : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0)
    (hx : x = ∑ i, c i • v i) (j : ι) : polar Q x (v j) = c j * polar Q (v j) (v j) := by
  have hsum : polar Q x (v j) = ∑ i, c i * polar Q (v i) (v j) := by
    simp only [hx, ← QuadraticMap.polarBilin_apply_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  rw [hsum, Finset.sum_eq_single j (fun i _ hij => by rw [h0 i j hij, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]

private theorem fj_orth_four {x0 x1 x2 x3 : V}
    (h01 : polar Q x0 x1 = 0) (h02 : polar Q x0 x2 = 0) (h03 : polar Q x0 x3 = 0)
    (h12 : polar Q x1 x2 = 0) (h13 : polar Q x1 x3 = 0) (h23 : polar Q x2 x3 = 0) :
    ∀ i j : Fin 4, i ≠ j → polar Q (![x0, x1, x2, x3] i) (![x0, x1, x2, x3] j) = 0 := by
  have h10 : polar Q x1 x0 = 0 := by rw [polar_comm]; exact h01
  have h20 : polar Q x2 x0 = 0 := by rw [polar_comm]; exact h02
  have h30 : polar Q x3 x0 = 0 := by rw [polar_comm]; exact h03
  have h21 : polar Q x2 x1 = 0 := by rw [polar_comm]; exact h12
  have h31 : polar Q x3 x1 = 0 := by rw [polar_comm]; exact h13
  have h32 : polar Q x3 x2 = 0 := by rw [polar_comm]; exact h23
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simpa using h01 | simpa using h02 | simpa using h03
    | simpa using h12 | simpa using h13 | simpa using h23
    | simpa using h10 | simpa using h20 | simpa using h30
    | simpa using h21 | simpa using h31 | simpa using h32

private theorem fj_core {a b R : V ≃ₗ[ZMod 3] V} {W : Submodule (ZMod 3) V}
    (hWnd : (Q.restrict W).Nondegenerate) (hdimW : Module.finrank (ZMod 3) W = 4)
    (hpa : ∀ x y, polar Q (a x) (a y) = polar Q x y)
    (hpb : ∀ x y, polar Q (b x) (b y) = polar Q x y)
    (hR : ∀ x y, polar Q (R x) y = polar Q x (R y))
    (haa : ∀ w ∈ W, a (a w) = -w) (hbb : ∀ w ∈ W, b (b w) = -w)
    (hba : ∀ z, a (b (a z)) = b z)
    (haW : ∀ w ∈ W, a w ∈ W) (hbW : ∀ w ∈ W, b w ∈ W) (hRW : ∀ w ∈ W, R w ∈ W)
    (hRa : ∀ x, R (a x) = a (R x)) (hRb : ∀ x, R (b x) = b (R x))
    (hRR : ∀ w ∈ W, R (R w) = -w) : False := by
  obtain ⟨u, huW, hu⟩ := fj_exists_polar_self_ne_zero hWnd (by
    intro h
    have := Submodule.finrank_eq_zero.mpr h
    omega)
  obtain ⟨c, hc⟩ : ∃ c : V ≃ₗ[ZMod 3] V, ∀ x, c x = a (b x) := ⟨a * b, fun x => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : V ≃ₗ[ZMod 3] V, ∀ x, d x = b (a x) := ⟨b * a, fun x => rfl⟩
  have hcc : ∀ w ∈ W, c (c w) = -w := fun w hw => by
    simp only [hc]
    rw [hba (b w)]
    exact hbb w hw
  have hdd : ∀ w ∈ W, d (d w) = -w := fun w hw => by
    simp only [hd]
    rw [hba w]
    exact hbb w hw
  have hpc : ∀ x y, polar Q (c x) (c y) = polar Q x y := fun x y => by
    rw [hc, hc, hpa, hpb]
  have hpd : ∀ x y, polar Q (d x) (d y) = polar Q x y := fun x y => by
    rw [hd, hd, hpb, hpa]
  have hRc : ∀ x, R (c x) = c (R x) := fun x => by rw [hc, hc, hRa, hRb]
  have hau : a u ∈ W := haW u huW
  have hbu : b u ∈ W := hbW u huW
  have hab : a (b u) ∈ W := haW _ hbu
  have o01 : polar Q u (a u) = 0 := fj_polar_self_of_sq hpa (haa u huW)
  have o02 : polar Q u (b u) = 0 := fj_polar_self_of_sq hpb (hbb u huW)
  have o03 : polar Q u (a (b u)) = 0 := by
    have h := fj_polar_self_of_sq hpc (hcc u huW)
    rwa [hc] at h
  have o12 : polar Q (a u) (b u) = 0 := by
    have h := fj_polar_self_of_sq hpd (hdd u huW)
    rw [hd] at h
    rw [← hba u, hpa]
    exact h
  have o13 : polar Q (a u) (a (b u)) = 0 := by rw [hpa]; exact o02
  have o23 : polar Q (b u) (a (b u)) = 0 := fj_polar_self_of_sq hpa (haa _ hbu)
  have n0 : polar Q u u ≠ 0 := hu
  have n1 : polar Q (a u) (a u) ≠ 0 := by rw [hpa]; exact hu
  have n2 : polar Q (b u) (b u) ≠ 0 := by rw [hpb]; exact hu
  have n3 : polar Q (a (b u)) (a (b u)) ≠ 0 := by rw [hpa, hpb]; exact hu
  obtain ⟨v, hv0, hv1, hv2, hv3⟩ : ∃ v : Fin 4 → V,
      v 0 = u ∧ v 1 = a u ∧ v 2 = b u ∧ v 3 = a (b u) :=
    ⟨![u, a u, b u, a (b u)], rfl, rfl, rfl, rfl⟩
  have hvdef : v = ![u, a u, b u, a (b u)] := by
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2, hv3]
  have horth : ∀ i j : Fin 4, i ≠ j → polar Q (v i) (v j) = 0 := by
    rw [hvdef]
    exact fj_orth_four o01 o02 o03 o12 o13 o23
  have hnorm : ∀ i : Fin 4, polar Q (v i) (v i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hv0] using n0
    · simpa [hv1] using n1
    · simpa [hv2] using n2
    · simpa [hv3] using n3
  have hli : LinearIndependent (ZMod 3) v :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := Q.polarBilin)
      (LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact horth i j hij)
      (fun i => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hnorm i)
  have hvW : ∀ i, v i ∈ W := by
    intro i
    fin_cases i
    · simpa [hv0] using huW
    · simpa [hv1] using hau
    · simpa [hv2] using hbu
    · simpa [hv3] using hab
  have hspan : Submodule.span (ZMod 3) (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hvW i
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hdimW]
  have hRuspan : R u ∈ Submodule.span (ZMod 3) (Set.range v) := by
    rw [hspan]
    exact hRW u huW
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hRuspan
  have hcoef : ∀ j, polar Q (R u) (v j) = cf j * polar Q (v j) (v j) :=
    fun j => fj_polar_coeff horth hcf.symm j
  have hRa' : polar Q (R u) (a u) = 0 :=
    fj_polar_adj_of_sq hpa hR hRa (haa _ (hRW u huW))
  have hRb' : polar Q (R u) (b u) = 0 :=
    fj_polar_adj_of_sq hpb hR hRb (hbb _ (hRW u huW))
  have hRc' : polar Q (R u) (a (b u)) = 0 := by
    have h := fj_polar_adj_of_sq hpc hR hRc (hcc _ (hRW u huW))
    rwa [hc] at h
  have e1 : cf 1 = 0 := by
    have h := hcoef 1
    rw [hv1, hRa'] at h
    exact (mul_eq_zero.mp h.symm).resolve_right n1
  have e2 : cf 2 = 0 := by
    have h := hcoef 2
    rw [hv2, hRb'] at h
    exact (mul_eq_zero.mp h.symm).resolve_right n2
  have e3 : cf 3 = 0 := by
    have h := hcoef 3
    rw [hv3, hRc'] at h
    exact (mul_eq_zero.mp h.symm).resolve_right n3
  have hRu : R u = cf 0 • u := by
    rw [← hcf, Fin.sum_univ_four, e1, e2, e3, hv0]
    simp
  have hu0 : u ≠ 0 := by
    intro h
    apply hu
    rw [h]
    exact polar_zero_left Q 0
  have h1 : R (R u) = (cf 0 * cf 0) • u := by
    rw [hRu, map_smul, hRu, smul_smul]
  have h2 : (cf 0 * cf 0 + 1) • u = 0 := by
    rw [add_smul, ← h1, hRR u huW, one_smul, neg_add_cancel]
  have h3 : cf 0 * cf 0 + 1 = 0 := (smul_eq_zero.mp h2).resolve_right hu0
  revert h3
  generalize cf 0 = t
  revert t
  decide

theorem fj_no_quaternion_comm_negsim (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {q r : OGroup Q} (hqr : q * q = r * r)
    (hyy : (q * q) * (q * q) = 1) (hrq : r * q = q⁻¹ * r) (hy1 : q * q ≠ 1)
    (hyπ : q * q ≠ piOrth Q) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v)
    (hqρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) v) =
      (q : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v))
    (hrρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) v) =
      (r : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v)) : False := by
  have hdimW : Module.finrank (ZMod 3) (commSp (q * q)) = 4 := by
    obtain ⟨h4, -⟩ := four_dvd_invDim_of_quaternion hQ hqr hyy hrq
    have hle := invDim_le (Q := Q) (q * q)
    have h0 : invDim (q * q) ≠ 0 := fun h => hy1 ((invDim_eq_zero_iff hyy).mp h)
    have h8 : invDim (q * q) ≠ Module.finrank (ZMod 3) V :=
      fun h => hyπ ((invDim_eq_finrank_iff hyy).mp h)
    unfold invDim at h4 h0 h8 hle
    omega
  have hmem : ∀ w : V, w ∈ commSp (q * q) ↔
      (q : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) w) = -w := fun w => by
    rw [mem_commSp_iff hyy]
    exact Iff.rfl
  have hmemb : ∀ w : V, w ∈ commSp (q * q) ↔
      (r : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) w) = -w := fun w => by
    rw [mem_commSp_iff hyy, hqr]
    exact Iff.rfl
  have haa : ∀ w ∈ commSp (q * q),
      (q : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) w) = -w := fun w hw => (hmem w).mp hw
  have hbb : ∀ w ∈ commSp (q * q),
      (r : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) w) = -w := fun w hw => (hmemb w).mp hw
  have hba : ∀ z : V, (q : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) z)) =
      (r : V ≃ₗ[ZMod 3] V) z := by
    intro z
    have h : q * r * q = r := by
      calc q * r * q = q * (r * q) := mul_assoc _ _ _
        _ = q * (q⁻¹ * r) := by rw [hrq]
        _ = r := mul_inv_cancel_left q r
    have h' := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) z) h
    exact h'
  have haW : ∀ w ∈ commSp (q * q), (q : V ≃ₗ[ZMod 3] V) w ∈ commSp (q * q) := fun w hw =>
    (hmem _).mpr (by rw [haa w hw, map_neg])
  have hbW : ∀ w ∈ commSp (q * q), (r : V ≃ₗ[ZMod 3] V) w ∈ commSp (q * q) := fun w hw =>
    (hmemb _).mpr (by rw [hbb w hw, map_neg])
  have hRW : ∀ w ∈ commSp (q * q), (ρ : V ≃ₗ[ZMod 3] V) w ∈ commSp (q * q) := fun w hw =>
    (hmem _).mpr (by rw [← hqρ w, ← hqρ _, haa w hw, map_neg])
  have hR : ∀ x y, polar Q ((ρ : V ≃ₗ[ZMod 3] V) x) y = polar Q x ((ρ : V ≃ₗ[ZMod 3] V) y) :=
    fun x y => by simpa only [QuadraticMap.polarBilin_apply_apply] using ff_aux_hadj hρ hρρ x y
  exact fj_core (a := (q : V ≃ₗ[ZMod 3] V)) (b := (r : V ≃ₗ[ZMod 3] V))
    (R := (ρ : V ≃ₗ[ZMod 3] V)) (W := commSp (q * q)) (nondegenerate_restrict_commSp hQ hyy)
    hdimW (fun x y => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup q.2 x y)
    (fun x y => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup r.2 x y) hR haa hbb hba
    haW hbW hRW hqρ hrρ (fun w _ => hρρ w)

end CFSG.OddStandard.SmallF3.Omega
