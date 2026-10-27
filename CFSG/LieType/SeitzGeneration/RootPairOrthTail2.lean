module

public import CFSG.LieType.SeitzGeneration.RootPairOrthGen
public import CFSG.LieType.SeitzGeneration.RootPairOrthTailCenter

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace RootPairOrth

section Xi

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)

@[expose] def xi (a : Fin d) (w : Fin d → K) : Fin d → K :=
  (Pi.single a 1 : Fin d → K) + w - Q w • Pi.single (S.star a) 1

@[expose] def IsTailVec (w : Fin d → K) : Prop := ∀ a ∈ S.hyp, w a = 0

theorem HypCoord.Q_xi {a : Fin d} (ha : a ∈ S.hyp) {w : Fin d → K} (hw : IsTailVec S w) :
    Q (xi S a w) = 0 :=
  S.Q_tail ha (hw _ (S.star_mem a ha)) (hw a ha)

theorem HypCoord.polar_xi_xi {a j : Fin d} (ha : a ∈ S.hyp) (hj : j ∈ S.hyp) (hja : j ≠ a)
    (hjs : j ≠ S.star a) {w w' : Fin d → K} (hw : IsTailVec S w) (hw' : IsTailVec S w') :
    polar Q (xi S a w) (xi S j w') = polar Q w w' := by
  have has := S.star_mem a ha
  have hjst := S.star_mem j hj
  have h1 : polar Q (Pi.single a 1 : Fin d → K) (Pi.single j 1) = 0 := by
    rw [S.polar_single_single ha]; simp [Ne.symm hjs]
  have h2 : polar Q (Pi.single a 1 : Fin d → K) w' = 0 := by
    rw [S.polar_single a ha]; exact hw' _ has
  have h3 : polar Q (Pi.single a 1 : Fin d → K) (Pi.single (S.star j) 1) = 0 := by
    rw [S.polar_single_single ha]
    have : S.star a ≠ S.star j := fun h => hja (S.star_injective hj ha h.symm)
    simp [this]
  have h4 : polar Q w (Pi.single j 1 : Fin d → K) = 0 := by
    rw [S.polar_single_right hj]; exact hw _ hjst
  have h5 : polar Q w (Pi.single (S.star j) 1 : Fin d → K) = 0 := by
    rw [S.polar_single_right hjst, S.star_star j hj]; exact hw _ hj
  have h6 : polar Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single j 1) = 0 := by
    rw [S.polar_single _ has, S.star_star a ha]; exact single_apply_ne hja.symm
  have h7 : polar Q (Pi.single (S.star a) 1 : Fin d → K) w' = 0 := by
    rw [S.polar_single _ has, S.star_star a ha]; exact hw' _ ha
  have h8 : polar Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single (S.star j) 1) = 0 := by
    rw [S.polar_single _ has, S.star_star a ha]
    have : a ≠ S.star j := fun h => hjs (by rw [h, S.star_star j hj])
    exact single_apply_ne this
  simp only [xi, polar_add_left, polar_sub_left, polar_smul_left, polar_add_right,
    polar_sub_right, polar_smul_right, smul_eq_mul, h1, h2, h3, h4, h5, h6, h7, h8]
  ring

@[expose] def wT (Q : QuadraticForm K (Fin d → K)) (t t' : Fin d) : Fin d → K :=
  polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) • (Pi.single t 1 : Fin d → K) -
    polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) • (Pi.single t' 1 : Fin d → K)

theorem isTailVec_single {t : Fin d} (ht : t ∉ S.hyp) : IsTailVec S (Pi.single t 1 : Fin d → K) :=
  fun _ ha => single_apply_ne (fun h => ht (h ▸ ha))

theorem isTailVec_wT {t t' : Fin d} (ht : t ∉ S.hyp) (ht' : t' ∉ S.hyp) :
    IsTailVec S (wT Q t t') := by
  intro a ha
  simp [wT, isTailVec_single S ht a ha, isTailVec_single S ht' a ha]

theorem polar_wT {t t' : Fin d} :
    polar Q (Pi.single t 1 : Fin d → K) (wT Q t t') = 0 := by
  simp only [wT, polar_sub_right, polar_smul_right, smul_eq_mul]
  ring

variable (Q) in
inductive IsTail2 (S : HypCoord Q) : (Fin d → K) → (Fin d → K) → Prop
  | mk {a j t t' : Fin d} : a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a → t ∉ S.hyp →
      t' ∉ S.hyp → IsTail2 S (xi S a (Pi.single t 1)) (xi S j (wT Q t t'))

theorem IsTail2.isTS {S : HypCoord Q} {x y : Fin d → K} (h : IsTail2 Q S x y) : IsTS Q x y := by
  cases h with
  | mk ha hj hja hjs ht ht' =>
    exact ⟨S.Q_xi ha (isTailVec_single S ht), S.Q_xi hj (isTailVec_wT S ht ht'), by
      rw [S.polar_xi_xi ha hj hja hjs (isTailVec_single S ht) (isTailVec_wT S ht ht')]
      exact polar_wT⟩

theorem IsTail2.isRat {S : HypCoord Q} {k : Subfield K}
    (hQrat : ∀ w : Fin d → K, IsRat k w → Q w ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) {x y : Fin d → K}
    (h : IsTail2 Q S x y) : IsRat k x ∧ IsRat k y := by
  cases h with
  | mk ha hj hja hjs ht ht' =>
    rename_i a j t t'
    have hwT : IsRat k (wT Q t t') := fun i => by
      simp only [wT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.mul_mem (hPk t t') (isRat_single k t i))
        (k.mul_mem (hPk t t) (isRat_single k t' i))
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [xi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.add_mem (isRat_single k a i) (isRat_single k t i))
        (k.mul_mem (hQrat _ (isRat_single k t)) (isRat_single k _ i))
    · simp only [xi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.add_mem (isRat_single k j i) (hwT i))
        (k.mul_mem (hQrat _ hwT) (isRat_single k _ i))

variable {k : Subfield K} {g : Matrix (Fin d) (Fin d) K} {μ : K}

theorem HypCoord.phi_tail_tail (h2 : (2 : K) ≠ 0) (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k)
    (hQrat : ∀ w : Fin d → K, IsRat k w → Q w ∈ k)
    (hQT : ∀ t, t ∉ S.hyp → Q (Pi.single t 1 : Fin d → K) ≠ 0) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k)
    (hcol2 : ∀ x y : Fin d → K, IsTail2 Q S x y → Phi Q g μ x y x₀ y₀ ∈ k) {t t' : Fin d}
    (ht : t ∉ S.hyp) (ht' : t' ∉ S.hyp) :
    Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀ ∈ k := by
  obtain ⟨a, ha⟩ : ∃ a, a ∈ S.hyp := by
    have := S.card_hyp
    exact Finset.card_pos.mp (by omega)
  obtain ⟨j, -, hj, -, hja, hjs, -, -, -, -⟩ := S.exists_three_T ha
  have has := S.star_mem a ha
  have hjst := S.star_mem j hj
  have kat : ∀ r s, (r ∈ S.hyp ∨ s ∈ S.hyp) →
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := fun r s hrs =>
    S.phi_row_ext h2 hQk hcol hrs
  have hc2 : polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 (hQT t ht)
  have hxy := hcol2 _ _ (IsTail2.mk ha hj hja hjs ht ht')
  have hpw : ∀ u : Fin d → K, polar Q (wT Q t t') u =
      polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) * polar Q (Pi.single t 1 : Fin d → K) u -
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) * polar Q (Pi.single t' 1 : Fin d → K) u
        := fun u => by simp only [wT, polar_sub_left, polar_smul_left, smul_eq_mul]
  have hmaster : polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) *
        Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀ =
      (Phi Q g μ (Pi.single a 1) (Pi.single j 1) x₀ y₀ +
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) *
          Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ -
        polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) *
          Phi Q g μ (Pi.single a 1) (Pi.single t' 1) x₀ y₀ -
        Q (wT Q t t') * Phi Q g μ (Pi.single a 1) (Pi.single (S.star j) 1) x₀ y₀ +
        Phi Q g μ (Pi.single t 1) (Pi.single j 1) x₀ y₀ -
        Q (wT Q t t') * Phi Q g μ (Pi.single t 1) (Pi.single (S.star j) 1) x₀ y₀ -
        Q (Pi.single t 1 : Fin d → K) *
          (Phi Q g μ (Pi.single (S.star a) 1) (Pi.single j 1) x₀ y₀ +
            polar Q (Pi.single t 1 : Fin d → K) (Pi.single t' 1) *
              Phi Q g μ (Pi.single (S.star a) 1) (Pi.single t 1) x₀ y₀ -
            polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) *
              Phi Q g μ (Pi.single (S.star a) 1) (Pi.single t' 1) x₀ y₀ -
            Q (wT Q t t') *
              Phi Q g μ (Pi.single (S.star a) 1) (Pi.single (S.star j) 1) x₀ y₀)) -
        Phi Q g μ (xi S a (Pi.single t 1)) (xi S j (wT Q t t')) x₀ y₀ := by
    simp only [Phi, xi, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, hpw]
    ring
  have hw : IsRat k (wT Q t t') := fun i => by
    simp only [wT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact k.sub_mem (k.mul_mem (hPk t t') (isRat_single k t i))
      (k.mul_mem (hPk t t) (isRat_single k t' i))
  have hmem : polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) *
        Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀ ∈ k := by
    rw [hmaster]
    refine k.sub_mem ?_ hxy
    have m1 := kat a j (Or.inl ha)
    have m2 := kat a t (Or.inl ha)
    have m3 := kat a t' (Or.inl ha)
    have m4 := kat a (S.star j) (Or.inl ha)
    have m5 := kat t j (Or.inr hj)
    have m6 := kat t (S.star j) (Or.inr hjst)
    have m7 := kat (S.star a) j (Or.inl has)
    have m8 := kat (S.star a) t (Or.inl has)
    have m9 := kat (S.star a) t' (Or.inl has)
    have m10 := kat (S.star a) (S.star j) (Or.inl has)
    have hqw := hQrat _ hw
    exact k.sub_mem (k.sub_mem (k.add_mem (k.sub_mem (k.sub_mem (k.add_mem m1
      (k.mul_mem (hPk t t') m2)) (k.mul_mem (hPk t t) m3)) (k.mul_mem hqw m4)) m5)
      (k.mul_mem hqw m6)) (k.mul_mem (hQk t) (k.sub_mem (k.sub_mem (k.add_mem m7
      (k.mul_mem (hPk t t') m8)) (k.mul_mem (hPk t t) m9)) (k.mul_mem hqw m10)))
  have hinv : Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀ =
      (polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1))⁻¹ *
        (polar Q (Pi.single t 1 : Fin d → K) (Pi.single t 1) *
          Phi Q g μ (Pi.single t 1) (Pi.single t' 1) x₀ y₀) := by
    field_simp
  rw [hinv]
  exact k.mul_mem (k.inv_mem (hPk t t)) hmem

@[expose] def IsBasicM (S : HypCoord Q) (x y : Fin d → K) : Prop :=
  IsBasicT S x y ∨ IsTail2 Q S x y

include S in
theorem HypCoord.phi_coord_mem_M (h2 : (2 : K) ≠ 0)
    (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k)
    (hQrat : ∀ w : Fin d → K, IsRat k w → Q w ∈ k)
    (hQT : ∀ t, t ∉ S.hyp → Q (Pi.single t 1 : Fin d → K) ≠ 0) (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (hdet : IsUnit g.det)
    (hP : ∀ x y x₀ y₀ : Fin d → K, IsBasicM S x y → IsBasicM S x₀ y₀ →
      Phi Q g μ x y x₀ y₀ ∈ k) (r s c c' : Fin d) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) (Pi.single c 1) (Pi.single c' 1) ∈ k := by
  have full : ∀ (g' : Matrix (Fin d) (Fin d) K) (μ' : K) (x₀ y₀ : Fin d → K),
      (∀ x y : Fin d → K, IsBasicM S x y → Phi Q g' μ' x y x₀ y₀ ∈ k) →
      ∀ r s : Fin d, Phi Q g' μ' (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := by
    intro g' μ' x₀ y₀ hcol r s
    by_cases hrs : r ∈ S.hyp ∨ s ∈ S.hyp
    · exact S.phi_row_ext h2 hQk (fun x y hxy => hcol x y (Or.inl hxy)) hrs
    · push Not at hrs
      exact S.phi_tail_tail h2 hQk hPk hQrat hQT (fun x y hxy => hcol x y (Or.inl hxy))
        (fun x y hxy => hcol x y (Or.inr hxy)) hrs.1 hrs.2
  have stepA : ∀ x₀ y₀ : Fin d → K, IsBasicM S x₀ y₀ → ∀ r s : Fin d,
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := fun x₀ y₀ hb r s =>
    full g μ x₀ y₀ (fun x y hxy => hP x y x₀ y₀ hxy hb) r s
  rw [phi_symm hμ hg hdet]
  refine full g⁻¹ μ⁻¹ (Pi.single r 1) (Pi.single s 1) (fun x y hxy => ?_) c c'
  rw [← phi_symm hμ hg hdet]
  exact stepA x y hxy r s

end Xi

section Rational

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K}

include S in
theorem HypCoord.rational_of_pairs_M (h2 : (2 : K) ≠ 0)
    (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k)
    (hQrat : ∀ w : Fin d → K, IsRat k w → Q w ∈ k)
    (hQT : ∀ t, t ∉ S.hyp → Q (Pi.single t 1 : Fin d → K) ≠ 0)
    (hnd : (polarBilin Q).Nondegenerate) {σ : K →+* K} (hσ : ∀ x, σ x = x ↔ x ∈ k)
    {g : Matrix (Fin d) (Fin d) K} {μ : K} (hμ : μ ≠ 0) (hg : ∀ v, Q (g *ᵥ v) = μ * Q v)
    (hdet : g.det ≠ 0)
    (hP : ∀ x y x₀ y₀ : Fin d → K, IsBasicM S x y → IsBasicM S x₀ y₀ →
      Phi Q g μ x y x₀ y₀ ∈ k) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  set G := gramMat Q with hGdef
  have hGdet : G.det ≠ 0 := gramMat_det_ne hnd
  have hG' : ∀ r c, (G * g) r c = polar Q (Pi.single r 1) (g *ᵥ Pi.single c 1) := by
    intro r c
    rw [← gramMat_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hdetG' : (G * g).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hGdet hdet
  have hmin : ∀ r s c c', μ⁻¹ * ((G * g) r c * (G * g) s c' - (G * g) r c' * (G * g) s c) ∈ k := by
    intro r s c c'
    have h := S.phi_coord_mem_M h2 hQk hPk hQrat hQT hμ hg (isUnit_iff_ne_zero.mpr hdet) hP r s c c'
    simp only [Phi] at h
    simpa only [hG'] using h
  have hcard : 3 ≤ Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    have h1 := S.card_hyp
    have h2' := S.hyp.card_le_univ
    rw [Fintype.card_fin] at h2'
    omega
  obtain ⟨a, ha, heig⟩ := rational_of_minors hcard hσ hμ hdetG' hmin
  refine ⟨a, ha, fun r c => ?_⟩
  have hGfix : ∀ r e, σ (G r e) = G r e := fun r e => (hσ _).mpr (hPk r e)
  have key : ∀ c, G *ᵥ (fun e => σ (g e c) - a * g e c) = 0 := by
    intro c
    funext r
    have h1 := heig r c
    rw [Matrix.mul_apply, map_sum] at h1
    simp only [map_mul, hGfix] at h1
    show ∑ e, G r e * (σ (g e c) - a * g e c) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [h1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun e _ => by ring
  have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGdet (key c)) r
  exact sub_eq_zero.mp this

end Rational

section Generation

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} (H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)))

theorem inv_apply_of_apply_eq (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) {v w : Fin d → K}
    (h : E v = w) : E⁻¹ w = v := by
  calc E⁻¹ w = E⁻¹ (E v) := by rw [h]
    _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem HypCoord.eichler_fix {c : Fin d} (hc : c ∈ S.hyp) {w v : Fin d → K}
    (hcw : polar Q (Pi.single c 1 : Fin d → K) w = 0) (hv : v (S.star c) = 0)
    (hvw : polar Q v w = 0) : eichler Q (Pi.single c 1 : Fin d → K) w v = v := by
  rw [eichler_apply (S.Q_single c hc) hcw, S.polar_single_right hc, hv, hvw]
  simp

include S in
theorem HypCoord.elementaryGroup_le_of_tail2_line (hnd : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k)
    (hrat : ∀ u w : Fin d → K, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ H)
    {x y : Fin d → K} (hxy : IsTail2 Q S x y) (hline : ∀ t : K, eichler Q x (t • y) ∈ H) :
    elementaryGroup Q ≤ H := by
  have hb : CoordEichlerT H S := fun u hu v hv => hrat _ _ (isRat_single k u) (isRat_single k v)
    (S.Q_single u hu) (by rw [S.polar_single_single hu]; simp [hv])
  cases hxy with
  | mk ha hj hja hjs ht ht' =>
    rename_i a j t t'
    have has := S.star_mem a ha
    have hjst := S.star_mem j hj
    have htv := isTailVec_single S ht
    have hwv := isTailVec_wT S ht ht'
    have hwr : IsRat k (wT Q t t') := fun i => by
      simp only [wT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (k.mul_mem (hPk t t') (isRat_single k t i))
        (k.mul_mem (hPk t t) (isRat_single k t' i))
    have hE1pol : polar Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) = 0 := by
      rw [S.polar_single _ has, S.star_star a ha]; exact htv a ha
    have hE2pol : polar Q (Pi.single (S.star j) 1 : Fin d → K) (wT Q t t') = 0 := by
      rw [S.polar_single _ hjst, S.star_star j hj]; exact hwv j hj
    have hE1 : eichler Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) ∈ H :=
      hrat _ _ (isRat_single k _) (isRat_single k _) (S.Q_single _ has) hE1pol
    have hE2 : eichler Q (Pi.single (S.star j) 1 : Fin d → K) (wT Q t t') ∈ H :=
      hrat _ _ (isRat_single k _) hwr (S.Q_single _ hjst) hE2pol
    set E1 := eichler Q (Pi.single (S.star a) 1 : Fin d → K) (Pi.single t 1) with hE1def
    set E2 := eichler Q (Pi.single (S.star j) 1 : Fin d → K) (wT Q t t') with hE2def
    have e1a : E1 (Pi.single a 1) = xi S a (Pi.single t 1) := by
      rw [hE1def, eichler_apply (S.Q_single _ has) hE1pol, S.polar_single_right has,
        S.star_star a ha, S.polar_single a ha, htv _ has]
      simp [xi]
    have haj : a ≠ S.star j := fun h => hjs (by rw [h, S.star_star j hj])
    have hxia : (xi S j (wT Q t t')) a = 0 := by
      simp only [xi, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [single_apply_ne hja.symm, hwv a ha, single_apply_ne haj]
      ring
    have hxit : polar Q (xi S j (wT Q t t')) (Pi.single t 1 : Fin d → K) = 0 := by
      have hwt : polar Q (wT Q t t') (Pi.single t 1 : Fin d → K) = 0 := by
        rw [polar_comm]; exact polar_wT
      have h1 : polar Q (Pi.single j 1 : Fin d → K) (Pi.single t 1) = 0 := by
        rw [S.polar_single j hj]; exact htv _ hjst
      have h2 : polar Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) = 0 := by
        rw [S.polar_single _ hjst]; exact htv _ (by rw [S.star_star j hj]; exact hj)
      simp only [xi, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, h1, h2, hwt]
      ring
    have e1y : E1 (xi S j (wT Q t t')) = xi S j (wT Q t t') :=
      S.eichler_fix has hE1pol (by rw [S.star_star a ha]; exact hxia) hxit
    have e2j : E2 (Pi.single j 1) = xi S j (wT Q t t') := by
      rw [hE2def, eichler_apply (S.Q_single _ hjst) hE2pol, S.polar_single_right hjst,
        S.star_star j hj, S.polar_single j hj, hwv _ hjst]
      simp [xi]
    have hpa : polar Q (Pi.single a 1 : Fin d → K) (wT Q t t') = 0 := by
      rw [S.polar_single a ha]; exact hwv _ has
    have e2a : E2 (Pi.single a 1) = Pi.single a 1 :=
      S.eichler_fix hjst hE2pol (by rw [S.star_star j hj]; exact single_apply_ne hja) hpa
    have hline1 : ∀ r : K, eichler Q (Pi.single a 1 : Fin d → K) (r • xi S j (wT Q t t')) ∈ H := by
      intro r
      have h3 := eichler_conj (hH (H.inv_mem hE1)) (xi S a (Pi.single t 1))
        (r • xi S j (wT Q t t'))
      rw [map_smul, inv_apply_of_apply_eq E1 e1y, inv_apply_of_apply_eq E1 e1a] at h3
      rw [← h3]
      exact H.mul_mem (H.mul_mem (H.inv_mem hE1) (hline r)) (H.inv_mem (H.inv_mem hE1))
    have hline2 : ∀ r : K, eichler Q (Pi.single a 1 : Fin d → K) (r • Pi.single j 1) ∈ H := by
      intro r
      have h3 := eichler_conj (hH (H.inv_mem hE2)) (Pi.single a 1 : Fin d → K)
        (r • xi S j (wT Q t t'))
      rw [map_smul, inv_apply_of_apply_eq E2 e2j, inv_apply_of_apply_eq E2 e2a] at h3
      rw [← h3]
      exact H.mul_mem (H.mul_mem (H.inv_mem hE2) (hline1 r)) (H.inv_mem (H.inv_mem hE2))
    refine S.elementaryGroup_le_of_rootLine_T H hnd hH hb ha hj hja ⟨?_, fun r => hline2 r⟩
    rw [S.polar_single_single ha]
    simp [Ne.symm hjs]

end Generation

section Pair

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_hypCoord_M (S : HypCoord Q)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    (hQT : ∀ t, t ∉ S.hyp → Q (Pi.single t 1 : Fin d → K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  have hQrat : ∀ w : Fin d → K, IsRat k w → Q w ∈ k := fun w hw => Q_isRat_mem hext hw
  have hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k := fun a => hQrat _ (isRat_single k a)
  have hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k := fun a b =>
    polar_isRat_mem hext (isRat_single k a) (isRat_single k b)
  refine orthPair_of_basic (IsBasicM S) ?_ ?_ ?_ hext hder hp hp2 hdeg hK hk3 hsetup gp hgp hne
  · intro x y h
    rcases h with h | h
    · exact ⟨(h.isRat k hQk).1, (h.isRat k hQk).2, h.isTS⟩
    · exact ⟨(h.isRat hQrat hPk).1, (h.isRat hQrat hPk).2, h.isTS⟩
  · intro σ hσk g μ hμ hdet hgμ hP
    exact S.rational_of_pairs_M h2 hQk hPk hQrat hQT hnd (σ := σ.toRingHom)
      (fun x => (hσk x).symm) hμ hgμ hdet hP
  · intro H hH hrat x y hxy hne' hline
    rcases hxy with hxy | hxy
    · exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat hxy hne' hline
    · exact S.elementaryGroup_le_of_tail2_line H hnd hH hPk hrat hxy hline

end Pair

end RootPairOrth

end CFSG.LieType.SeitzGeneration
