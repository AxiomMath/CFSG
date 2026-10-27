module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCent
public import Mathlib.RingTheory.AdjoinRoot

public noncomputable section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

@[expose] def quadPoly (t : K) : K[X] :=
  X ^ 2 - C t * X + 1

abbrev centPoly (u : SpecialLinearGroup (Fin 3) K) : K[X] :=
  quadPoly (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1)

@[expose] def quadElem (t a b : K) : AdjoinRoot (quadPoly t) :=
  AdjoinRoot.of (quadPoly t) a + AdjoinRoot.of (quadPoly t) b * AdjoinRoot.root (quadPoly t)

theorem quadPoly_monic (t : K) : (quadPoly t).Monic := by
  unfold quadPoly
  monicity!

theorem quadPoly_natDegree (t : K) : (quadPoly t).natDegree = 2 := by
  unfold quadPoly
  compute_degree!

theorem root_sq (t : K) :
    AdjoinRoot.root (quadPoly t) ^ 2 =
      AdjoinRoot.of (quadPoly t) t * AdjoinRoot.root (quadPoly t) - 1 := by
  have h : AdjoinRoot.mk (quadPoly t) (X ^ 2 - C t * X + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h
  linear_combination h

theorem quadElem_mul (t a b a' b' : K) :
    quadElem t a b * quadElem t a' b' =
      quadElem t (a * a' - b * b') (a * b' + b * a' + t * b * b') := by
  simp only [quadElem, map_add, map_sub, map_mul]
  linear_combination AdjoinRoot.of (quadPoly t) b * AdjoinRoot.of (quadPoly t) b' * root_sq t

theorem quadElem_eq_zero {t a b : K} (h : quadElem t a b = 0) : a = 0 ∧ b = 0 := by
  rw [quadElem, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X, ← map_mul, ← map_add,
    AdjoinRoot.mk_eq_zero] at h
  have hq : C a + C b * X = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h ?_
    have h2 : (quadPoly t).degree = 2 := by
      unfold quadPoly
      compute_degree!
    have h1 : (C a + C b * X).degree ≤ 1 := by compute_degree
    rw [h2]
    exact h1.trans_lt (by decide)
  have h0 := congrArg (fun q => Polynomial.coeff q 0) hq
  have h1 := congrArg (fun q => Polynomial.coeff q 1) hq
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem quadElem_injective {t a b a' b' : K} (h : quadElem t a b = quadElem t a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := quadElem_eq_zero (t := t) (a := a - a') (b := b - b') (by
    simp only [quadElem, map_sub] at h ⊢
    linear_combination h)
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem exists_quadElem_eq (t : K) (f : AdjoinRoot (quadPoly t)) :
    ∃ a b : K, f = quadElem t a b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective f
  have hne : quadPoly t ≠ 1 := fun h1 => by
    have := quadPoly_natDegree t
    rw [h1, natDegree_one] at this
    exact absurd this (by norm_num)
  have hdeg : (q %ₘ quadPoly t).degree ≤ 1 := by
    refine Polynomial.degree_le_of_natDegree_le ?_
    have := Polynomial.natDegree_modByMonic_lt q (quadPoly_monic t) hne
    rw [quadPoly_natDegree] at this
    exact Nat.le_of_lt_succ this
  refine ⟨(q %ₘ quadPoly t).coeff 0, (q %ₘ quadPoly t).coeff 1, ?_⟩
  have hqr : AdjoinRoot.mk (quadPoly t) q = AdjoinRoot.mk (quadPoly t) (q %ₘ quadPoly t) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨q /ₘ quadPoly t, by linear_combination -(Polynomial.modByMonic_add_div q (quadPoly t))⟩
  rw [hqr, quadElem]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]

theorem nontrivial_adjoinRoot (t : K) : Nontrivial (AdjoinRoot (quadPoly t)) :=
  AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_eq_natDegree (quadPoly_monic t).ne_zero, quadPoly_natDegree]
    decide)

theorem quadElem_mul_conj (t a b : K) :
    quadElem t a b * quadElem t (a + t * b) (-b) =
      AdjoinRoot.of (quadPoly t) (a ^ 2 + t * a * b + b ^ 2) := by
  simp only [quadElem, map_add, map_mul, map_pow, map_neg]
  linear_combination -(AdjoinRoot.of (quadPoly t) b) ^ 2 * root_sq t

theorem norm_ne_zero_of_isUnit {t a b : K} (h : IsUnit (quadElem t a b)) :
    a ^ 2 + t * a * b + b ^ 2 ≠ 0 := by
  intro hN
  have := nontrivial_adjoinRoot t
  have h0 := quadElem_mul_conj t a b
  rw [hN, map_zero] at h0
  obtain ⟨ha, hb⟩ := quadElem_eq_zero (h.mul_right_eq_zero.mp h0)
  rw [neg_eq_zero] at hb
  rw [hb, mul_zero, add_zero] at ha
  apply h.ne_zero
  rw [ha, hb, quadElem, map_zero, zero_mul, add_zero]

namespace IsFixedLine

variable {p : ℕ} {u : SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}

def nbVec (h : IsFixedLine p u x) : Fin 3 → K :=
  h.exists_normalBasis.choose

theorem nbVec_mem (h : IsFixedLine p u x) :
    h.nbVec ∈ LinearMap.range (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1)) :=
  h.exists_normalBasis.choose_spec.1

theorem nbVec_li (h : IsFixedLine p u x) :
    LinearIndependent K ![x, h.nbVec, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec] :=
  h.exists_normalBasis.choose_spec.2.1

theorem nbVec_sq (h : IsFixedLine p u x) :
    (u : Matrix (Fin 3) (Fin 3) K) *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) =
      (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) •
        ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) - h.nbVec :=
  h.exists_normalBasis.choose_spec.2.2.1

theorem trace_sub_one_ne_two (h : IsFixedLine p u x) :
    Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1 ≠ 2 :=
  h.exists_normalBasis.choose_spec.2.2.2

theorem exists_coord (h : IsFixedLine p u x)
    (g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :
    ∃ c : K × K, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec =
      c.1 • h.nbVec + c.2 • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) :=
  let ⟨_, α, β, hαβ⟩ := h.mulVec_eq_of_commute h.nbVec_mem h.nbVec_li
    (coe_mul_comm_of_mem_centralizer g.2)
  ⟨(α, β), hαβ⟩

def coord (h : IsFixedLine p u x)
    (g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) : K × K :=
  (h.exists_coord g).choose

theorem coord_spec (h : IsFixedLine p u x)
    (g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :
    ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec =
      (h.coord g).1 • h.nbVec + (h.coord g).2 • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) :=
  (h.exists_coord g).choose_spec

theorem coord_eq (h : IsFixedLine p u x)
    {g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))} {α β : K}
    (hg : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec =
      α • h.nbVec + β • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec)) :
    h.coord g = (α, β) := by
  have e := h.coord_spec g
  rw [hg] at e
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp (linearIndependent_tail_pair h.nbVec_li)
    ((h.coord g).1 - α) ((h.coord g).2 - β)
    (by rw [sub_smul, sub_smul, ← add_sub_add_comm, ← e, sub_self])
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

theorem det_eq (h : IsFixedLine p u x) {G : Matrix (Fin 3) (Fin 3) K}
    (hG : (u : Matrix (Fin 3) (Fin 3) K) * G = G * u) {l α β : K} (hx : G *ᵥ x = l • x)
    (hw : G *ᵥ h.nbVec = α • h.nbVec + β • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec)) :
    G.det = l * (α ^ 2 + (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) * α * β + β ^ 2) := by
  have hUw : G *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) = (-β) • h.nbVec +
      (α + (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) * β) •
        ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) := by
    rw [mulVec_mulVec_comm hG, hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      h.nbVec_sq]
    module
  rw [det_eq_of_mulVec_eq_sum h.nbVec_li (M := !![l, 0, 0; 0, α, -β; 0, β,
    α + (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) * β])
    (fun j => by fin_cases j <;> simp [Fin.sum_univ_three, hx, hw, hUw]), Matrix.det_fin_three]
  simp
  ring

@[expose] def centralizerHom (h : IsFixedLine p u x) :
    Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) →* AdjoinRoot (centPoly u)
    where
  toFun g := quadElem _ (h.coord g).1 (h.coord g).2
  map_one' := by
    rw [h.coord_eq (g := 1) (α := 1) (β := 0) (by simp), quadElem]
    simp
  map_mul' g k := by
    have hg := h.coord_spec g
    have hk := h.coord_spec k
    have hgU := mulVec_mulVec_comm (coe_mul_comm_of_mem_centralizer g.2) h.nbVec
    rw [h.coord_eq (g := g * k) (α := (h.coord g).1 * (h.coord k).1 - (h.coord g).2 * (h.coord k).2)
      (β := (h.coord g).1 * (h.coord k).2 + (h.coord g).2 * (h.coord k).1 +
        (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) * (h.coord g).2 * (h.coord k).2) ?_]
    · exact (quadElem_mul _ _ _ _ _).symm
    · rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hk,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgU, hg, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, h.nbVec_sq]
      module

theorem centralizerHom_apply (h : IsFixedLine p u x)
    (g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :
    h.centralizerHom g = quadElem _ (h.coord g).1 (h.coord g).2 :=
  rfl

theorem centralizerHom_injective (h : IsFixedLine p u x) :
    Function.Injective h.centralizerHom := by
  intro g k hgk
  rw [centralizerHom_apply, centralizerHom_apply] at hgk
  have hc : h.coord g = h.coord k := by
    obtain ⟨h1, h2⟩ := quadElem_injective hgk
    exact Prod.ext h1 h2
  have hg := h.coord_spec g
  have hk := h.coord_spec k
  rw [hc] at hg
  obtain ⟨⟨lg, hlg⟩, -⟩ := h.mulVec_eq_of_commute h.nbVec_mem h.nbVec_li
    (coe_mul_comm_of_mem_centralizer g.2)
  obtain ⟨⟨lk, hlk⟩, -⟩ := h.mulVec_eq_of_commute h.nbVec_mem h.nbVec_li
    (coe_mul_comm_of_mem_centralizer k.2)
  have hdg := h.det_eq (coe_mul_comm_of_mem_centralizer g.2) hlg hg
  have hdk := h.det_eq (coe_mul_comm_of_mem_centralizer k.2) hlk hk
  rw [(g : SpecialLinearGroup (Fin 3) K).prop] at hdg
  rw [(k : SpecialLinearGroup (Fin 3) K).prop] at hdk
  have hl : lg = lk := by
    have hN : (h.coord k).1 ^ 2 + (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) *
        (h.coord k).1 * (h.coord k).2 + (h.coord k).2 ^ 2 ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hdk
      exact one_ne_zero hdk
    exact mul_right_cancel₀ hN (hdg.symm.trans hdk)
  refine Subtype.ext (Subtype.ext (eq_of_mulVec_eq h.nbVec_li (forall_fin_three ?_ ?_ ?_)))
  · change _ *ᵥ x = _ *ᵥ x
    rw [hlg, hlk, hl]
  · change _ *ᵥ h.nbVec = _ *ᵥ h.nbVec
    rw [hg, hk]
  · change _ *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec) =
      _ *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ h.nbVec)
    rw [mulVec_mulVec_comm (coe_mul_comm_of_mem_centralizer g.2),
      mulVec_mulVec_comm (coe_mul_comm_of_mem_centralizer k.2), hg, hk]

theorem exists_centralizerHom_eq (h : IsFixedLine p u x) (f : (AdjoinRoot (centPoly u))ˣ) :
    ∃ g, h.centralizerHom g = f := by
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hUdef
  set t := Matrix.trace U - 1 with ht
  obtain ⟨a, b, hab⟩ := exists_quadElem_eq t (f : AdjoinRoot (quadPoly t))
  have hN := norm_ne_zero_of_isUnit (hab ▸ f.isUnit)
  set N := a ^ 2 + t * a * b + b ^ 2 with hNdef
  set w := h.nbVec with hwdef
  have hsq : U *ᵥ (U *ᵥ w) = t • (U *ᵥ w) - w := h.nbVec_sq
  have hfx : U *ᵥ x = x := h.fixed
  obtain ⟨G, hG⟩ := exists_mulVec_eq_sum h.nbVec_li !![N⁻¹, 0, 0; 0, a, -b; 0, b, a + t * b]
  have hG0 : G *ᵥ x = N⁻¹ • x := by simpa [Fin.sum_univ_three] using hG 0
  have hG1 : G *ᵥ w = a • w + b • (U *ᵥ w) := by simpa [Fin.sum_univ_three] using hG 1
  have hG2 : G *ᵥ (U *ᵥ w) = (-b) • w + (a + t * b) • (U *ᵥ w) := by
    simpa [Fin.sum_univ_three] using hG 2
  have hdet : G.det = 1 := by
    rw [det_eq_of_mulVec_eq_sum h.nbVec_li hG, Matrix.det_fin_three]
    simp
    field_simp
    ring
  have hcomm : U * G = G * U := by
    refine eq_of_mulVec_eq h.nbVec_li (forall_fin_three ?_ ?_ ?_)
    · change (U * G) *ᵥ x = (G * U) *ᵥ x
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfx, hG0, Matrix.mulVec_smul, hfx]
    · change (U * G) *ᵥ w = (G * U) *ᵥ w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG1, hG2, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hsq]
      module
    · change (U * G) *ᵥ (U *ᵥ w) = (G * U) *ᵥ (U *ᵥ w)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG2, hsq, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hsq, Matrix.mulVec_sub, Matrix.mulVec_smul,
        hG1, hG2]
      module
  refine ⟨⟨⟨G, hdet⟩, mem_centralizer_of_coe_mul_comm hcomm⟩, ?_⟩
  rw [centralizerHom_apply, h.coord_eq hG1, hab]

@[expose] def centralizerEquiv (h : IsFixedLine p u x) :
    Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) ≃*
      (AdjoinRoot (centPoly u))ˣ :=
  MulEquiv.ofBijective h.centralizerHom.toHomUnits
    ⟨fun _ _ e => h.centralizerHom_injective (congrArg Units.val e), fun f =>
      let ⟨g, hg⟩ := h.exists_centralizerHom_eq f
      ⟨g, Units.ext hg⟩⟩

theorem coe_centralizerEquiv (h : IsFixedLine p u x)
    (g : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :
    (h.centralizerEquiv g : AdjoinRoot (centPoly u)) = h.centralizerHom g :=
  rfl

theorem self_mem_centralizer (u : SpecialLinearGroup (Fin 3) K) :
    u ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) :=
  mem_centralizer_of_coe_mul_comm rfl

theorem centralizerEquiv_self (h : IsFixedLine p u x) :
    (h.centralizerEquiv ⟨u, self_mem_centralizer u⟩ : AdjoinRoot (centPoly u)) =
      AdjoinRoot.root _ := by
  rw [coe_centralizerEquiv, centralizerHom_apply, h.coord_eq (α := 0) (β := 1) (by simp), quadElem]
  simp

end IsFixedLine

end CFSG.AGLEmbedding.LinearThreeKit
