module

public import CFSG.CGT.Stroth77.TypePredicates
public import CFSG.LocalAnalysis.OddStandard.ONan76Defs
public import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76

@[expose] def alpS : IntMat := ofCols ![0, 1, 0] ![0, 0, 1] ![1, -1, 1]

@[expose] def alpT : IntMat := ofCols ![0, 0, -1] ![0, -1, 0] ![-1, 0, 0]

variable {k : Fin 3 → ℕ} {n : ℕ}

theorem compat_of_const (hk : ∀ i, k i = n) (M : IntMat) : Compat k M := by
  intro i j
  rw [hk i, hk j]
  exact dvd_mul_right _ _

theorem two_pow_nsmul_torus (hk : ∀ i, k i = n) (x : Torus k) : (2 ^ n) • x = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
  have h : ((2 ^ n : ℕ) : ZMod (2 ^ k i)) = 0 := by
    rw [← hk i]
    exact ZMod.natCast_self _
  rw [h, zero_mul]

@[expose] def actC (hk : ∀ i, k i = n) (M : IntMat) : Torus k →+ Torus k :=
  matAct k M (compat_of_const hk M)

theorem actC_mul (hk : ∀ i, k i = n) (M N : IntMat) :
    actC hk (M * N) = (actC hk M).comp (actC hk N) :=
  matAct_mul M N _ _

theorem actC_congr (hk : ∀ i, k i = n) {M N : IntMat} (h : MatEq k M N) :
    actC hk M = actC hk N :=
  matAct_congr _ _ h

theorem actC_one (hk : ∀ i, k i = n) : actC hk 1 = AddMonoidHom.id (Torus k) :=
  matAct_one

theorem actC_gen (hk : ∀ i, k i = n) (M : IntMat) (j : Fin 3) :
    actC hk M (gen k j) = M 0 j • gen k 0 + M 1 j • gen k 1 + M 2 j • gen k 2 :=
  matAct_gen_eq M _ j

theorem exists_int_combination (x : Torus k) :
    ∃ z : Fin 3 → ℤ, x = z 0 • gen k 0 + z 1 • gen k 1 + z 2 • gen k 2 := by
  choose z hz using fun i => ZMod.intCast_surjective (x i)
  refine ⟨z, funext fun i => ?_⟩
  fin_cases i <;> simp [gen, Pi.single_apply, hz]

theorem exists_mul_modEq_one_of_odd {d : ℤ} (hd : Odd d) (n : ℕ) :
    ∃ d' : ℤ, d * d' ≡ 1 [ZMOD 2 ^ n] := by
  obtain ⟨q, rfl⟩ := hd
  have h2 : IsCoprime (2 * q + 1) 2 := ⟨1, -q, by ring⟩
  obtain ⟨a, b, hab⟩ := h2.pow_right (n := n)
  refine ⟨a, Int.modEq_iff_dvd.2 ⟨b, by linear_combination (-1 : ℤ) * hab⟩⟩

theorem exists_matEq_mul_one_of_odd (hk : ∀ i, k i = n) {P : IntMat} (hdet : Odd (Matrix.det P)) :
    ∃ Q : IntMat, MatEq k (P * Q) 1 := by
  obtain ⟨d', hd'⟩ := exists_mul_modEq_one_of_odd hdet n
  refine ⟨d' • Matrix.adjugate P, fun i j => ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hk i]
  by_cases hij : i = j
  · subst hij
    simpa [mul_comm] using hd'
  · simp [Matrix.one_apply_ne hij]

section Bridge

variable {G : Type} [Group G] {D : Subgroup G}

@[expose] def torusElt (e : Additive D ≃+ Torus k) (w : Torus k) : G :=
  ((Additive.toMul (e.symm w) : D) : G)

theorem torusElt_mem (e : Additive D ≃+ Torus k) (w : Torus k) : torusElt e w ∈ D :=
  (Additive.toMul (e.symm w)).2

theorem torusElt_add (e : Additive D ≃+ Torus k) (w w' : Torus k) :
    torusElt e (w + w') = torusElt e w * torusElt e w' := by
  simp [torusElt, map_add, toMul_add]

theorem torusElt_neg (e : Additive D ≃+ Torus k) (w : Torus k) :
    torusElt e (-w) = (torusElt e w)⁻¹ := by
  simp [torusElt, map_neg, toMul_neg]

theorem torusElt_zero (e : Additive D ≃+ Torus k) : torusElt e 0 = 1 := by
  simp [torusElt]

theorem torusElt_zsmul (e : Additive D ≃+ Torus k) (z : ℤ) (w : Torus k) :
    torusElt e (z • w) = torusElt e w ^ z := by
  rw [torusElt, torusElt, map_zsmul, toMul_zsmul, Subgroup.coe_zpow]

theorem torusElt_nsmul (e : Additive D ≃+ Torus k) (z : ℕ) (w : Torus k) :
    torusElt e (z • w) = torusElt e w ^ z := by
  rw [torusElt, torusElt, map_nsmul, toMul_nsmul, Subgroup.coe_pow]

theorem exists_torusElt_eq (e : Additive D ≃+ Torus k) {x : G} (hx : x ∈ D) :
    ∃ w, torusElt e w = x :=
  ⟨e (Additive.ofMul ⟨x, hx⟩), by simp [torusElt]⟩

theorem inv_mul_torusElt_mul (e : Additive D ≃+ Torus k) {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) {f : Torus k →+ Torus k}
    (hconj : ∀ x : D, e (Additive.ofMul (conjBy hg x)) = f (e (Additive.ofMul x)))
    (w : Torus k) : g⁻¹ * torusElt e w * g = torusElt e (f w) := by
  have h := hconj (Additive.toMul (e.symm w))
  rw [ofMul_toMul, AddEquiv.apply_symm_apply] at h
  have h' : conjBy hg (Additive.toMul (e.symm w)) = Additive.toMul (e.symm (f w)) := by
    rw [← h, AddEquiv.symm_apply_apply, toMul_ofMul]
  exact congrArg Subtype.val h'

theorem closure_torusElt_eq (hk : ∀ i, k i = n) (e : Additive D ≃+ Torus k) {P : IntMat}
    (hdet : Odd (Matrix.det P)) :
    Subgroup.closure ({torusElt e (actC hk P (gen k 0)), torusElt e (actC hk P (gen k 1)),
      torusElt e (actC hk P (gen k 2))} : Set G) = D := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact torusElt_mem e _
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_torusElt_eq e hx
    obtain ⟨Q, hQ⟩ := exists_matEq_mul_one_of_odd hk hdet
    obtain ⟨z, hz⟩ := exists_int_combination (actC hk Q y)
    have hy : y = actC hk P (actC hk Q y) := by
      rw [← AddMonoidHom.comp_apply, ← actC_mul, actC_congr hk hQ, actC_one]
      rfl
    rw [hy, hz, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, torusElt_add, torusElt_add,
      torusElt_zsmul, torusElt_zsmul, torusElt_zsmul]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _

end Bridge

section Frame

variable {G : Type} [Group G] {D : Subgroup G}

theorem exists_alperinFrame_of_matEq (hk : ∀ i, k i = n) (e : Additive D ≃+ Torus k)
    {Mt Mu : IntMat} {uv t u : G} (ht : t ∈ Subgroup.normalizer (D : Set G))
    (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D, e (Additive.ofMul (conjBy ht x)) = actC hk Mt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D, e (Additive.ofMul (conjBy hu x)) = actC hk Mu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t)
    {P : IntMat} (hs : MatEq k (Mu * Mt * P) (P * alpS)) (hr : MatEq k (Mu * P) (P * alpT))
    (hdet : Odd (Matrix.det P)) :
    ∃ v₁ v₂ v₃ s r : G, AlperinFrame n v₁ v₂ v₃ s r ∧ s ^ 4 = 1 ∧
      Subgroup.closure ({v₁, v₂, v₃, s, r} : Set G) = D ⊔ Subgroup.closure {uv, t, u} := by
  set w : Fin 3 → Torus k := fun j => actC hk P (gen k j) with hw
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hcs : ∀ x : Torus k,
      (t * u)⁻¹ * torusElt e x * (t * u) = torusElt e (actC hk (Mu * Mt) x) := by
    intro x
    rw [show (t * u)⁻¹ * torusElt e x * (t * u) = u⁻¹ * (t⁻¹ * torusElt e x * t) * u by group,
      inv_mul_torusElt_mul e ht ht_conj, inv_mul_torusElt_mul e hu hu_conj, actC_mul]
    rfl
  have hcu : ∀ x : Torus k, u⁻¹ * torusElt e x * u = torusElt e (actC hk Mu x) :=
    inv_mul_torusElt_mul e hu hu_conj
  have hS : ∀ j, actC hk (Mu * Mt) (w j) = actC hk P (actC hk alpS (gen k j)) := by
    intro j
    simp only [hw]
    rw [← AddMonoidHom.comp_apply, ← actC_mul, ← AddMonoidHom.comp_apply, ← actC_mul,
      actC_congr hk hs]
  have hT : ∀ j, actC hk Mu (w j) = actC hk P (actC hk alpT (gen k j)) := by
    intro j
    simp only [hw]
    rw [← AddMonoidHom.comp_apply, ← actC_mul, ← AddMonoidHom.comp_apply, ← actC_mul,
      actC_congr hk hr]
  have hcomm : ∀ x y : Torus k, torusElt e x * torusElt e y = torusElt e y * torusElt e x :=
    fun x y => by rw [← torusElt_add, ← torusElt_add, add_comm]
  have hpow : ∀ x : Torus k, torusElt e x ^ 2 ^ n = 1 := fun x => by
    rw [← torusElt_nsmul, two_pow_nsmul_torus hk, torusElt_zero]
  have hs2 : (t * u) * (t * u) = u * uv * u := by
    rw [show (t * u) * (t * u) = (t * u) * t * u by group, htu,
      show u * uv * t * t * u = u * uv * (t * t) * u by group, ht2, mul_one]
  have hs4 : (t * u) ^ 4 = 1 := by
    rw [show (t * u) ^ 4 = ((t * u) * (t * u)) * ((t * u) * (t * u)) by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq], hs2,
      show u * uv * u * (u * uv * u) = u * uv * (u * u) * uv * u by group, hu2, mul_one,
      show u * uv * uv * u = u * (uv * uv) * u by group, huv2, mul_one, hu2]
  refine ⟨torusElt e (w 0), torusElt e (w 1), torusElt e (w 2), t * u, u,
    { comm₁₂ := hcomm _ _
      comm₁₃ := hcomm _ _
      comm₂₃ := hcomm _ _
      pow₁ := hpow _
      pow₂ := hpow _
      pow₃ := hpow _
      card_V := ?_
      s_v₁ := ?_
      s_v₂ := ?_
      s_v₃ := ?_
      t_v₁ := ?_
      t_v₂ := ?_
      t_v₃ := ?_
      t_sq := hu2
      t_s := ?_
      s_four := Or.inl hs4 }, hs4, ?_⟩
  · rw [closure_torusElt_eq hk e hdet, Nat.card_congr (Additive.ofMul : D ≃ Additive D),
      Nat.card_congr e.toEquiv, natCard_torus, hk 0, hk 1, hk 2]
    ring_nf
  · rw [hcs, hS, actC_gen]
    simp [alpS, ofCols_apply, hw]
  · rw [hcs, hS, actC_gen]
    simp [alpS, ofCols_apply, hw]
  · rw [hcs, hS, actC_gen]
    simp [alpS, ofCols_apply, map_add, map_neg, torusElt_add, torusElt_neg, hw]
  · rw [hcu, hT, actC_gen]
    simp [alpT, ofCols_apply, map_neg, torusElt_neg, hw]
  · rw [hcu, hT, actC_gen]
    simp [alpT, ofCols_apply, map_neg, torusElt_neg, hw]
  · rw [hcu, hT, actC_gen]
    simp [alpT, ofCols_apply, map_neg, torusElt_neg, hw]
  · rw [hu', mul_inv_rev, hu', ht', show u * (t * u) * u = u * t * (u * u) by group, hu2,
      mul_one]
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left (torusElt_mem e _)
      · exact Subgroup.mem_sup_left (torusElt_mem e _)
      · exact Subgroup.mem_sup_left (torusElt_mem e _)
      · exact Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · refine sup_le ?_ ?_
      · refine le_trans (le_of_eq (closure_torusElt_eq hk e hdet).symm) ?_
        exact Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢; tauto)
      · rw [Subgroup.closure_le]
        have hs : t * u ∈ Subgroup.closure ({torusElt e (w 0), torusElt e (w 1),
            torusElt e (w 2), t * u, u} : Set G) := Subgroup.subset_closure (by simp)
        have hu₀ : u ∈ Subgroup.closure ({torusElt e (w 0), torusElt e (w 1),
            torusElt e (w 2), t * u, u} : Set G) := Subgroup.subset_closure (by simp)
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx <;> rw [hx]
        · have h : uv = u * ((t * u) * (t * u)) * u := by
            rw [hs2, show u * (u * uv * u) * u = (u * u) * uv * (u * u) by group, hu2, one_mul,
              mul_one]
          rw [h]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu₀ (Subgroup.mul_mem _ hs hs)) hu₀
        · have h := Subgroup.mul_mem _ hs hu₀
          rwa [mul_assoc, hu2, mul_one] at h
        · exact hu₀

end Frame

end CFSG.CGT.Stroth77
