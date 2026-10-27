module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Gen

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

section

variable {Q V : Type*} [Group Q] [AddCommGroup V]

theorem exists_fixed_of_gl4 (ρ : Q → V → V) (hρ1 : ∀ v, ρ 1 v = v)
    (hρm : ∀ q q' v, ρ (q * q') v = ρ q (ρ q' v)) (hρa : ∀ q v w, ρ q (v + w) = ρ q v + ρ q w)
    (m : Q →* Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hker : ∀ q q', m q = m q' → ∀ v, ρ q v = ρ q' v)
    (ev : V →+ ZMod 2) (hev : ∀ q v, ev (ρ q v) = ev v) {v₀ : V} (hv₀ : ev v₀ = 1)
    (kS qT qn : Q) (hodd : Odd (orderOf kS))
    (hS : m kS = singerMat) (hT : m qT = gl4T) (hn : m qn = gl4N)
    (hunique : ∀ v : V, ev v = 0 → ρ (kS ^ 5) v = v → v = 0) :
    ∃ v : V, ev v = 1 ∧ ∀ q : Q, ρ q v = v := by
  classical
  let ρa : Q → V →+ V := fun q => AddMonoidHom.mk' (ρ q) (hρa q)
  have hρsub : ∀ q v w, ρ q (v - w) = ρ q v - ρ q w := fun q v w => map_sub (ρa q) v w
  have hfixpow : ∀ (q : Q) (v : V), ρ q v = v → ∀ j : ℕ, ρ (q ^ j) v = v := by
    intro q v hq j
    induction j with
    | zero => rw [pow_zero, hρ1]
    | succ j ih => rw [pow_succ', hρm, ih, hq]
  set n := orderOf kS with hnn
  set vK : V := ∑ i ∈ Finset.range n, ρ (kS ^ i) v₀ with hvK
  have hevK : ev vK = 1 := by
    simp only [hvK, map_sum, hev, hv₀, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    exact ZMod.natCast_eq_one_iff_odd.2 hodd
  have hfixK : ρ kS vK = vK := by
    have h1 : ρ kS vK = ∑ i ∈ Finset.range n, ρ (kS ^ (i + 1)) v₀ := by
      rw [hvK]
      show ρa kS (∑ i ∈ Finset.range n, ρ (kS ^ i) v₀) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show ρ kS (ρ (kS ^ i) v₀) = _
      rw [← hρm, ← pow_succ']
    rw [h1]
    have e1 := Finset.sum_range_succ' (fun i => ρ (kS ^ i) v₀) n
    have e2 := Finset.sum_range_succ (fun i => ρ (kS ^ i) v₀) n
    have hn0 : ρ (kS ^ n) v₀ = ρ (kS ^ 0) v₀ := by rw [hnn, pow_orderOf_eq_one, pow_zero]
    rw [hn0] at e2
    exact add_right_cancel (e1.symm.trans e2)
  let pe : Fin 3 → Fin 3 → Q := fun a b => kS ^ (5 * (a : ℕ)) * qT ^ (b : ℕ)
  have hmpe : ∀ a b : Fin 3,
      m (pe a b) = singerMat ^ (5 * (a : ℕ)) * gl4T ^ (b : ℕ) := fun a b => by
    simp only [pe, map_mul, map_pow, hS, hT]
  set w : V := ∑ p : Fin 3 × Fin 3, ρ (pe p.1 p.2) vK with hw
  have hevw : ev w = 1 := by
    simp only [hw, map_sum, hev, hevK, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    decide
  have hw5 : ρ (kS ^ 5) w = w := by
    have h1 : ρ (kS ^ 5) w = ∑ p : Fin 3 × Fin 3, ρ (pe (p.1 + 1) p.2) vK := by
      rw [hw]
      show ρa (kS ^ 5) (∑ p : Fin 3 × Fin 3, ρ (pe p.1 p.2) vK) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      show ρ (kS ^ 5) (ρ (pe p.1 p.2) vK) = _
      rw [← hρm]
      refine hker _ _ ?_ vK
      have hm1 : m (kS ^ 5 * pe p.1 p.2) =
          singerMat ^ 5 * (singerMat ^ (5 * (p.1 : ℕ)) * gl4T ^ (p.2 : ℕ)) := by
        rw [map_mul, map_pow, hS, hmpe]
      rw [hm1, hmpe]
      exact singer_mul_pe p.1 p.2
    rw [h1, hw]
    exact Equiv.sum_comp (Equiv.prodCongr (Equiv.addRight (1 : Fin 3)) (Equiv.refl (Fin 3)))
      (fun p : Fin 3 × Fin 3 => ρ (pe p.1 p.2) vK)
  have hwT : ρ qT w = w := by
    have h1 : ρ qT w = ∑ p : Fin 3 × Fin 3, ρ (pe p.1 (p.2 + 1)) vK := by
      rw [hw]
      show ρa qT (∑ p : Fin 3 × Fin 3, ρ (pe p.1 p.2) vK) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      show ρ qT (ρ (pe p.1 p.2) vK) = _
      rw [← hρm]
      refine hker _ _ ?_ vK
      have hm1 : m (qT * pe p.1 p.2) =
          gl4T * (singerMat ^ (5 * (p.1 : ℕ)) * gl4T ^ (p.2 : ℕ)) := by
        rw [map_mul, hT, hmpe]
      rw [hm1, hmpe]
      exact gl4T_mul_pe p.1 p.2
    rw [h1, hw]
    exact Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.addRight (1 : Fin 3)))
      (fun p : Fin 3 × Fin 3 => ρ (pe p.1 p.2) vK)
  have hwK : w = vK := by
    have h0 := hunique (w - vK) (by rw [map_sub, hevw, hevK, sub_self]) (by
      rw [hρsub, hw5, hfixpow kS vK hfixK 5])
    exact sub_eq_zero.1 h0
  have hTK : ρ qT vK = vK := by rw [← hwK, hwT]
  have hpe : ∀ a b : Fin 3, ρ (pe a b) vK = vK := fun a b => by
    show ρ (kS ^ (5 * (a : ℕ)) * qT ^ (b : ℕ)) vK = vK
    rw [hρm, hfixpow qT vK hTK, hfixpow kS vK hfixK]
  have hnK : ρ qn vK = vK := by
    have h0 := hunique (ρ qn vK - vK) (by rw [map_sub, hev, hevK, sub_self]) (by
      rw [hρsub, ← hρm]
      have h2 : ρ (kS ^ 5 * qn) vK = ρ (qn * pe 1 2) vK := by
        refine hker _ _ ?_ vK
        have hm1 : m (qn * pe 1 2) = gl4N * (singerMat ^ (5 * (1 : ℕ)) * gl4T ^ (2 : ℕ)) := by
          rw [map_mul, hn, hmpe]
          rfl
        rw [map_mul, map_pow, hS, hn, hm1]
        exact singer_pow_five_mul_gl4N
      rw [h2, hρm, hpe, hfixpow kS vK hfixK 5])
    exact sub_eq_zero.1 h0
  let X : Submonoid (Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    { carrier := {M | ∃ q : Q, ρ q vK = vK ∧ m q = M}
      mul_mem' := by
        rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩
        exact ⟨q₁ * q₂, by rw [hρm, h₂, h₁], map_mul m q₁ q₂⟩
      one_mem' := ⟨1, hρ1 vK, map_one m⟩ }
  have hclos : gl4Sub ≤ X := by
    refine Submonoid.closure_le.2 ?_
    rintro M (rfl | rfl)
    · exact ⟨kS, hfixK, hS⟩
    · exact ⟨qn, hnK, hn⟩
  refine ⟨vK, hevK, fun q => ?_⟩
  have hdet : (m q).det ≠ 0 := by
    have h := congrArg Matrix.det (map_mul m q q⁻¹)
    rw [mul_inv_cancel, map_one, det_one, det_mul] at h
    intro h0
    rw [h0, zero_mul] at h
    exact one_ne_zero h
  obtain ⟨q', hq', hmq'⟩ := hclos (mem_closure_singer_gl4N _ hdet)
  rw [hker q q' hmq'.symm vK, hq']

end

end CFSG.EvenSporadicStandard.ThStd
