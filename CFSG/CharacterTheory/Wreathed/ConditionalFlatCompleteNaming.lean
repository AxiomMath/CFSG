module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteExclusion

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

theorem sign_pos_eq {γ γ' x x' : ℤ} (hγ : γ = 1 ∨ γ = -1) (hγ' : γ' = 1 ∨ γ' = -1)
    (hx : 0 < x) (hx' : 0 < x') (h : γ * x = γ' * x') : γ = γ' ∧ x = x' := by
  rcases hγ with rfl | rfl <;> rcases hγ' with rfl | rfl <;> constructor <;> linarith

theorem exists_pair (l : Fin 4) : ∃ f : Fin 2, l = pairA f ∨ l = pairB f := by
  revert l
  decide

theorem pair_unique {l : Fin 4} {f f' : Fin 2} (h : l = pairA f ∨ l = pairB f)
    (h' : l = pairA f' ∨ l = pairB f') : f = f' := by
  revert l f f'
  decide

theorem pairA_ne_pairB (f : Fin 2) : pairA f ≠ pairB f := by
  revert f
  decide

theorem eq_one_sub_of_ne {e f : Fin 2} (h : f ≠ e) : f = 1 - e := by
  revert e f
  decide

theorem one_sub_ne (e : Fin 2) : 1 - e ≠ e := by
  revert e
  decide

theorem sum_fin_four_pairs {β : Type*} [AddCommMonoid β] (g : Fin 4 → β) :
    ∑ l, g l = (g (pairA 0) + g (pairB 0)) + (g (pairA 1) + g (pairB 1)) := by
  rw [Fin.sum_univ_four]
  simp only [pairA, pairB, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype K]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

section Naming

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype K] in
theorem degree_diag {k : K} {v : I → ℤ} {ξ : I} {f : Fin 2} {sg : ℤ}
    (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v 1 ξ 0)
    (hpair : PairAt (q k) (η k) v f sg) :
    v ⬝ᵥ d = δ₀ * d i₀ - δ₁ * d i₁ + 2 * δ₄ * d i₄ +
      sg * (η k (pairA f) * d (q k (pairA f)) - η k (pairB f) * d (q k (pairB f))) := by
  obtain ⟨⟨v0, v1, v2, v3, v4⟩, vp, vout, -⟩ := hv
  obtain ⟨pa, pb, pa', pb'⟩ := hpair
  have hsplit := F.sum_split k fun i => v i * d i
  have hvd : v ⬝ᵥ d = ∑ i, v i * d i := rfl
  have hodd : ∑ h, v (p h) * d (p h) = 0 := Finset.sum_eq_zero fun h _ => by rw [vp h, zero_mul]
  have hrest : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i * d i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [vout i hi, ite_self, zero_mul]
  have hq : ∑ l, v (q k l) * d (q k l) =
      sg * (η k (pairA f) * d (q k (pairA f)) - η k (pairB f) * d (q k (pairB f))) := by
    rw [sum_fin_four_pairs]
    fin_cases f
    · simp only [Fin.zero_eta, Fin.isValue, sub_zero] at pa pb pa' pb' ⊢
      rw [pa, pb, pa', pb']
      ring
    · simp only [Fin.mk_one, Fin.isValue, sub_self] at pa pb pa' pb' ⊢
      rw [pa, pb, pa', pb']
      ring
  rw [hvd, hsplit, hodd, hq, hrest, v0, v1, v2, v3, v4]
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

omit [Fintype I] [Fintype H] [Fintype K] in
theorem pair_naming (hd : ∀ i, 0 < d i) (k : K) (f : Fin 2) {v : I → ℤ} {sg : ℤ}
    (hsg : sg = 1 ∨ sg = -1) (hpair : PairAt (q k) (η k) v f sg)
    (hdeg : δ₀ * d i₀ - δ₁ * d i₁ + 2 * δ₄ * d i₄ +
      sg * (η k (pairA f) * d (q k (pairA f)) - η k (pairB f) * d (q k (pairB f))) = 0)
    (hdYs : δ₀ * d i₀ + δ₁ * d i₁ - δ₂ * d i₂ - δ₃ * d i₃ = 0)
    (hdC : δ₀ * d i₀ - δ₁ * d i₁ + δ₂ * d i₂ - δ₃ * d i₃ + 2 * δ₄ * d i₄ = 0) :
    ∃ lP lQ : Fin 4, ((lP = pairA f ∧ lQ = pairB f) ∨ (lP = pairB f ∧ lQ = pairA f)) ∧
      η k lP = -δ₂ ∧ η k lQ = -δ₃ ∧ d (q k lP) = d i₂ ∧ d (q k lQ) = d i₃ ∧
      v (q k lP) = δ₂ ∧ v (q k lQ) = -δ₃ := by
  obtain ⟨pa, pb, -, -⟩ := hpair
  have hpd : η k (pairA f) * d (q k (pairA f)) + η k (pairB f) * d (q k (pairB f)) = α * D := by
    fin_cases f
    · exact (F.dpair k).1
    · exact (F.dpair k).2
  have hcore := F.dcore
  have hs2 : -δ₂ = 1 ∨ -δ₂ = -1 := by rcases F.sδ₂ with h | h <;> rw [h] <;> norm_num
  have hs3 : -δ₃ = 1 ∨ -δ₃ = -1 := by rcases F.sδ₃ with h | h <;> rw [h] <;> norm_num
  have hηA := F.sη k (pairA f)
  have hηB := F.sη k (pairB f)
  rcases hsg with rfl | rfl
  ·
    have hB : η k (pairB f) * d (q k (pairB f)) = -δ₂ * d i₂ := by linarith
    have hA : η k (pairA f) * d (q k (pairA f)) = -δ₃ * d i₃ := by linarith
    obtain ⟨eB, dB⟩ := sign_pos_eq hηB hs2 (hd _) (hd _) hB
    obtain ⟨eA, dA⟩ := sign_pos_eq hηA hs3 (hd _) (hd _) hA
    refine ⟨pairB f, pairA f, Or.inr ⟨rfl, rfl⟩, eB, eA, dB, dA, ?_, ?_⟩
    · rw [pb, eB]
      ring
    · rw [pa, eA]
      ring
  ·
    have hA : η k (pairA f) * d (q k (pairA f)) = -δ₂ * d i₂ := by linarith
    have hB : η k (pairB f) * d (q k (pairB f)) = -δ₃ * d i₃ := by linarith
    obtain ⟨eA, dA⟩ := sign_pos_eq hηA hs2 (hd _) (hd _) hA
    obtain ⟨eB, dB⟩ := sign_pos_eq hηB hs3 (hd _) (hd _) hB
    refine ⟨pairA f, pairB f, Or.inl ⟨rfl, rfl⟩, eA, eB, dA, dB, ?_, ?_⟩
    · rw [pa, eA]
      ring
    · rw [pb, eB]
      ring

omit [Fintype K] in
theorem diag_explicit {k : K} {v : I → ℤ} {ξ : I} {f : Fin 2} {sg : ℤ} {lP lQ : Fin 4}
    (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v 1 ξ 0)
    (hpair : PairAt (q k) (η k) v f sg)
    (hl : (lP = pairA f ∧ lQ = pairB f) ∨ (lP = pairB f ∧ lQ = pairA f))
    (hvP : v (q k lP) = δ₂) (hvQ : v (q k lQ) = -δ₃) :
    v = Pi.single i₀ δ₀ - Pi.single i₁ δ₁ + Pi.single i₄ (2 * δ₄) + Pi.single (q k lP) δ₂ -
      Pi.single (q k lQ) δ₃ := by
  obtain ⟨⟨v0, v1, v2, v3, v4⟩, vp, vout, -⟩ := hv
  obtain ⟨-, -, pa', pb'⟩ := hpair
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ := F.core_ne
  have hqi : ∀ l t, q k l ≠ ![i₀, i₁, i₂, i₃, i₄] t := fun l t => F.q_ne_core k l t
  have hq0 : ∀ l, q k l ≠ i₀ := fun l => hqi l 0
  have hq1 : ∀ l, q k l ≠ i₁ := fun l => hqi l 1
  have hq2 : ∀ l, q k l ≠ i₂ := fun l => hqi l 2
  have hq3 : ∀ l, q k l ≠ i₃ := fun l => hqi l 3
  have hq4 : ∀ l, q k l ≠ i₄ := fun l => hqi l 4
  have hqq : ∀ l l', q k l = q k l' ↔ l = l' := fun l l' =>
    ⟨fun h => (F.q_inj h).2, fun h => by rw [h]⟩
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_one, mul_zero, neg_zero] at v0 v1 v2 v3 v4
  refine F.eq_of_agree k ?_ ?_ ?_ ?_ ?_ (fun h => ?_) (fun l => ?_) (fun i hi => ?_)
  · rw [v0]
    simp [h01, h04, (hq0 lP).symm, (hq0 lQ).symm]
  · rw [v1]
    simp [h01.symm, h14, (hq1 lP).symm, (hq1 lQ).symm]
  · rw [v2]
    simp [h02.symm, h12.symm, h24, (hq2 lP).symm, (hq2 lQ).symm]
  · rw [v3]
    simp [h03.symm, h13.symm, h34, (hq3 lP).symm, (hq3 lQ).symm]
  · rw [v4]
    simp [h04.symm, h14.symm, (hq4 lP).symm, (hq4 lQ).symm]
    ring
  · have hp := F.p_notMem_core h
    obtain ⟨g0, g1, g2, g3, g4⟩ := ne_core_of_notMem hp
    rw [vp h]
    simp [g0, g1, g4, (F.q_ne_p k lP h).symm, (F.q_ne_p k lQ h).symm]
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, hqq, ite_eq_right (hq0 l),
      ite_eq_right (hq1 l), ite_eq_right (hq4 l)]
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases f <;> fin_cases l <;>
      simp_all [pairA, pairB]
  · obtain ⟨hic, hip, hiq⟩ := mem_outK.mp hi
    obtain ⟨g0, g1, g2, g3, g4⟩ := ne_core_of_notMem hic
    rw [vout i hi, ite_self]
    simp [g0, g1, g4, (hiq lP).symm, (hiq lQ).symm]

omit [Fintype K] in
theorem generic_explicit {k : K} {w : I → ℤ} {ψ : I} {γ : ℤ}
    (hw : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 w) (hwp : ∀ h, w (p h) = 0)
    (hwq : ∀ l, w (q k l) = 0) (hψ : ψ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k))
    (hwv : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i = if i = ψ then γ else 0) :
    w = Pi.single i₀ δ₀ - Pi.single i₁ δ₁ + Pi.single i₄ (2 * δ₄) + Pi.single ψ γ := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := hw
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ := F.core_ne
  obtain ⟨hψc, hψp, hψq⟩ := mem_outK.mp hψ
  obtain ⟨g0, g1, g2, g3, g4⟩ := ne_core_of_notMem hψc
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_one, mul_zero, neg_zero] at v0 v1 v2 v3 v4
  refine F.eq_of_agree k ?_ ?_ ?_ ?_ ?_ (fun h => ?_) (fun l => ?_) (fun i hi => ?_)
  · rw [v0]
    simp [h01, h04, g0.symm]
  · rw [v1]
    simp [h01.symm, h14, g1.symm]
  · rw [v2]
    simp [h02.symm, h12.symm, h24, g2.symm]
  · rw [v3]
    simp [h03.symm, h13.symm, h34, g3.symm]
  · rw [v4]
    simp [h04.symm, h14.symm, g4.symm]
    ring
  · have hp := F.p_notMem_core h
    obtain ⟨u0, u1, u2, u3, u4⟩ := ne_core_of_notMem hp
    rw [hwp h]
    simp [u0, u1, u4, hψp h]
  · have hqc := F.q_notMem_core k l
    obtain ⟨u0, u1, u2, u3, u4⟩ := ne_core_of_notMem hqc
    rw [hwq l]
    simp [u0, u1, u4, hψq l]
  · obtain ⟨hic, -, -⟩ := mem_outK.mp hi
    obtain ⟨u0, u1, u2, u3, u4⟩ := ne_core_of_notMem hic
    rw [hwv i hi]
    simp [Pi.single_apply, u0, u1, u4]

omit [Fintype I] [Fintype H] [Fintype K] in
theorem E_explicit (k : K) {lP lQ : Fin 2 → Fin 4}
    (hl : ∀ f, (lP f = pairA f ∧ lQ f = pairB f) ∨ (lP f = pairB f ∧ lQ f = pairA f))
    (hηP : ∀ f, η k (lP f) = -δ₂) (hηQ : ∀ f, η k (lQ f) = -δ₃) :
    E k = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ -
      Pi.single (q k (lP 0)) δ₂ - Pi.single (q k (lP 1)) δ₂ - Pi.single (q k (lQ 0)) δ₃ -
      Pi.single (q k (lQ 1)) δ₃ := by
  have hpair : ∀ f, (Pi.single (q k (pairA f)) (η k (pairA f)) : I → ℤ) +
      Pi.single (q k (pairB f)) (η k (pairB f)) =
      -Pi.single (q k (lP f)) δ₂ - Pi.single (q k (lQ f)) δ₃ := by
    intro f
    rcases hl f with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP, ← hQ, hηP, hηQ, Pi.single_neg, Pi.single_neg]
      abel
    · rw [← hP, ← hQ, hηP, hηQ, Pi.single_neg, Pi.single_neg]
      abel
  have hsum : (∑ r, Pi.single (q k r) (η k r) : I → ℤ) =
      ((Pi.single (q k (pairA 0)) (η k (pairA 0)) : I → ℤ) +
        Pi.single (q k (pairB 0)) (η k (pairB 0))) +
      ((Pi.single (q k (pairA 1)) (η k (pairA 1)) : I → ℤ) +
        Pi.single (q k (pairB 1)) (η k (pairB 1))) :=
    sum_fin_four_pairs fun r => (Pi.single (q k r) (η k r) : I → ℤ)
  rw [F.formE k, hsum, hpair 0, hpair 1]
  abel

omit [Fintype I] [Fintype H] [Fintype K] in
theorem Y_explicit (k : K) {lP lQ : Fin 2 → Fin 4}
    (hl : ∀ f, (lP f = pairA f ∧ lQ f = pairB f) ∨ (lP f = pairB f ∧ lQ f = pairA f))
    (hηP : ∀ f, η k (lP f) = -δ₂) (hηQ : ∀ f, η k (lQ f) = -δ₃) :
    Y k = -Pi.single (q k (lP 0)) δ₂ + Pi.single (q k (lP 1)) δ₂ - Pi.single (q k (lQ 0)) δ₃ +
      Pi.single (q k (lQ 1)) δ₃ := by
  have hpair : ∀ f, (Pi.single (q k (pairA f)) (η k (pairA f)) : I → ℤ) +
      Pi.single (q k (pairB f)) (η k (pairB f)) =
      -Pi.single (q k (lP f)) δ₂ - Pi.single (q k (lQ f)) δ₃ := by
    intro f
    rcases hl f with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP, ← hQ, hηP, hηQ, Pi.single_neg, Pi.single_neg]
      abel
    · rw [← hP, ← hQ, hηP, hηQ, Pi.single_neg, Pi.single_neg]
      abel
  have h0 := hpair 0
  have h1 := hpair 1
  simp only [pairA, pairB, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [F.formY k]
  have e : (Pi.single (q k 0) (η k 0) + Pi.single (q k 1) (η k 1) - Pi.single (q k 2) (η k 2) -
      Pi.single (q k 3) (η k 3) : I → ℤ) =
      ((Pi.single (q k 0) (η k 0) : I → ℤ) + Pi.single (q k 1) (η k 1)) -
        ((Pi.single (q k 2) (η k 2) : I → ℤ) + Pi.single (q k 3) (η k 3)) := by abel
  rw [e, h0, h1]
  abel

end Naming

end Frame

end CFSG.Wreathed.FlatComplete
