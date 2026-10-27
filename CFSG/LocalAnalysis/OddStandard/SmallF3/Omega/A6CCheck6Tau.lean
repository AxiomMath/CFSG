module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CCheck
public import Certificates.Data.A6CMat6

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

theorem a6c_check6_tau {Γ : Type} [Group Γ] (m : A6CModel 6 Γ) (hΓ : Nat.card Γ = 26127360)
    {rT rCT : Rec} (h : part62 rT rCT = true) :
    A6CSimArr 6 (g0M6 ()) ∧ A6CElt m (g0M6 ()) ^ 5 = 1 ∧ A6CElt m (g0M6 ()) ≠ 1 ∧
      (rCT.L.toList.map (A6CElt m)).Nodup ∧ (∀ y ∈ rCT.L.toList, A6CSimArr 6 y) ∧
      (∀ c : Γ, c * A6CElt m (g0M6 ()) = A6CElt m (g0M6 ()) * c ↔
        ∃ y ∈ k0Of 6 (g0M6 ()) rCT, A6CElt m y = c) ∧
      (k0Of 6 (g0M6 ()) rCT).length = 40 := by
  classical
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (by omega)
  have h' := h
  unfold part62 at h'
  dsimp at h'
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨hsimOKg0, hneg⟩, hpowbeq⟩, hsimOKtau⟩, htau2⟩, hclass⟩, hcent⟩,
    hlenbeq⟩ := h'
  have hsimG0 : A6CSimArr 6 (g0M6 ()) := A6CSimArr.of_simOK hsimOKg0
  have hsimT : A6CSimArr 6 (tauM 6 (g0M6 ())) := A6CSimArr.of_simOK hsimOKtau
  have hne : eqP (g0M6 ()) (idN 6) = false := by
    have h'' := hneg
    rw [Bool.not_eq_true'] at h''
    exact h''
  have hg0ne : A6CElt m (g0M6 ()) ≠ 1 := by
    intro hcon
    have h1 : eqP (g0M6 ()) (idN 6) = true := by
      rw [a6cElt_eq_iff m hsimG0 (A6CSimArr.idN 6)]
      rw [hcon, a6cElt_idN m]
    rw [h1] at hne
    exact Bool.false_ne_true hne.symm
  have hg0pow : A6CElt m (g0M6 ()) ^ 5 = 1 := by
    have h2 := a6cElt_powM m hsimG0 5
    rw [beq_iff_eq.mp hpowbeq, a6cElt_idN m] at h2
    exact h2.symm
  have hlen : (k0Of 6 (g0M6 ()) rCT).length = 40 := beq_iff_eq.mp hlenbeq
  obtain ⟨-, hcentnd, hcentspec⟩ := a6c_centOK_sound m hcent hsimOKtau
  have hcard : 4536 * 5760 = Nat.card Γ := by rw [hΓ]
  have hcomplete : ∀ c : Γ,
      c * A6CElt m (tauM 6 (g0M6 ())) = A6CElt m (tauM 6 (g0M6 ())) * c →
        c ∈ rCT.L.toList.map (A6CElt m) :=
    (a6c_complete m hclass hcent hcard).2
  have key : ∀ c : Γ, c * A6CElt m (g0M6 ()) = A6CElt m (g0M6 ()) * c →
      c * A6CElt m (tauM 6 (g0M6 ())) = A6CElt m (tauM 6 (g0M6 ())) * c := by
    intro c hc
    obtain ⟨C, hC, rfl⟩ := m.ofMat_surj c
    let G : Matrix (Fin 6) (Fin 6) (ZMod 3) := A6CToMat 6 (g0M6 ())
    let T : Matrix (Fin 6) (Fin 6) (ZMod 3) := A6CToMat 6 (tauM 6 (g0M6 ()))
    have hGsim : A6CSimMat G := hsimG0.2
    have hTsim : A6CSimMat T := hsimT.2
    have hcG : m.ofMat C * m.ofMat G = m.ofMat G * m.ofMat C := hc
    have hCGmul : m.ofMat (C * G) = m.ofMat (G * C) := by
      rw [m.ofMat_mul C G hC hGsim, m.ofMat_mul G C hGsim hC]
      exact hcG
    have hG5 : G ^ 5 = 1 := by
      have h2 := congrArg (A6CToMat 6) (beq_iff_eq.mp hpowbeq)
      rw [a6c_toMat_powM, a6c_toMat_idN] at h2
      exact h2
    have hT' : T = -((G + G ^ 2) + (G ^ 3 + G ^ 4)) := by
      have hs : (g0M6 ()).size = 6 * 6 := hsimG0.1.1
      have hsp : ∀ k : ℕ, (powM 6 (g0M6 ()) k).size = 6 * 6 :=
        fun k => (a6c_wf_powM 6 (g0M6 ()) k).1
      have hpa : (addM (g0M6 ()) (powM 6 (g0M6 ()) 2)).size = 6 * 6 := by
        simp [addM, Array.size_ofFn, hs]
      simp only [T, tauM, a6c_toMat_negM]
      congr 1
      rw [a6c_toMat_addM 6 (addM (g0M6 ()) (powM 6 (g0M6 ()) 2))
            (addM (powM 6 (g0M6 ()) 3) (powM 6 (g0M6 ()) 4)) (by simp [hpa]),
          a6c_toMat_addM 6 (g0M6 ()) (powM 6 (g0M6 ()) 2) (by simp [hs]),
          a6c_toMat_addM 6 (powM 6 (g0M6 ()) 3) (powM 6 (g0M6 ()) 4) (by simp [hsp 3]),
          a6c_toMat_powM, a6c_toMat_powM, a6c_toMat_powM]
    rcases (m.ofMat_eq (C * G) (G * C) (hC.mul hGsim) (hGsim.mul hC)).mp hCGmul with
      hCG | hCGneg
    · have hCT : C * T = T * C := by
        rw [hT']
        have h1 : Commute C G := hCG
        have h12 : Commute C (G + G ^ 2) := h1.add_right (h1.pow_right 2)
        have h34 : Commute C (G ^ 3 + G ^ 4) :=
          (h1.pow_right 3).add_right (h1.pow_right 4)
        exact (h12.add_right h34).neg_right
      change m.ofMat C * m.ofMat T = m.ofMat T * m.ofMat C
      rw [← m.ofMat_mul C T hC hTsim, ← m.ofMat_mul T C hTsim hC, hCT]
    · exfalso
      have h2 : C * G ^ 2 = G ^ 2 * C := by
        calc C * G ^ 2 = C * (G * G) := by rw [pow_two]
          _ = (C * G) * G := by rw [Matrix.mul_assoc]
          _ = (-(G * C)) * G := by rw [hCGneg]
          _ = -(G * C * G) := by rw [Matrix.neg_mul]
          _ = -(G * (C * G)) := by rw [Matrix.mul_assoc]
          _ = -(G * (-(G * C))) := by rw [hCGneg]
          _ = -(-(G * (G * C))) := by rw [Matrix.mul_neg]
          _ = G * (G * C) := by rw [neg_neg]
          _ = (G * G) * C := by rw [Matrix.mul_assoc]
          _ = G ^ 2 * C := by rw [pow_two]
      have hg4 : G ^ 4 = G ^ 2 * G ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two]
      have h4 : C * G ^ 4 = G ^ 4 * C := by
        rw [hg4]
        calc C * (G ^ 2 * G ^ 2) = (C * G ^ 2) * G ^ 2 := by rw [Matrix.mul_assoc]
          _ = (G ^ 2 * C) * G ^ 2 := by rw [h2]
          _ = G ^ 2 * (C * G ^ 2) := by rw [Matrix.mul_assoc]
          _ = G ^ 2 * (G ^ 2 * C) := by rw [h2]
          _ = G ^ 2 * G ^ 2 * C := by rw [Matrix.mul_assoc]
      have hCeq : C = -C := by
        calc C = C * G ^ 5 := by rw [hG5, Matrix.mul_one]
          _ = C * G ^ 4 * G := by rw [pow_succ, Matrix.mul_assoc]
          _ = G ^ 4 * C * G := by rw [h4]
          _ = G ^ 4 * (C * G) := by rw [Matrix.mul_assoc]
          _ = G ^ 4 * (-(G * C)) := by rw [hCGneg]
          _ = -(G ^ 4 * (G * C)) := by rw [Matrix.mul_neg]
          _ = -(G ^ 4 * G * C) := by rw [Matrix.mul_assoc]
          _ = -(G ^ 5 * C) := by rw [← pow_succ]
          _ = -(1 * C) := by rw [hG5]
          _ = -C := by rw [Matrix.one_mul]
      have hCzero : C = 0 := by
        ext i j
        have hij : C i j = -(C i j) := by
          simpa [Matrix.neg_apply] using congrFun (congrFun hCeq i) j
        have hsum : C i j + C i j = 0 := by
          have h := neg_add_cancel (C i j)
          rwa [← hij] at h
        have h2m : (2 : ZMod 3) * C i j = 0 := by rw [two_mul]; exact hsum
        have h22 : (2 : ZMod 3) * 2 = 1 := by decide
        calc C i j = 1 * C i j := by rw [one_mul]
          _ = ((2 : ZMod 3) * 2) * C i j := by rw [h22]
          _ = 2 * ((2 : ZMod 3) * C i j) := by rw [mul_assoc]
          _ = 2 * 0 := by rw [h2m]
          _ = 0 := by rw [mul_zero]
      have hCne : C ≠ 0 := by
        intro h0
        rcases hC with h1 | h1
        · rw [h0, Matrix.zero_mul] at h1
          exact zero_ne_one h1
        · rw [h0, Matrix.zero_mul] at h1
          exact one_ne_zero (neg_eq_zero.mp h1.symm)
      exact hCne hCzero
  refine ⟨hsimG0, hg0pow, hg0ne, hcentnd, ?_, ?_, hlen⟩
  · intro y hy
    exact (hcentspec y hy).1
  · intro c
    constructor
    · intro hc
      obtain ⟨y, hy, hyc⟩ := List.mem_map.mp (hcomplete c (key c hc))
      refine ⟨y, ?_, hyc⟩
      rw [k0Of]
      exact List.mem_filter.mpr ⟨hy,
        (a6cElt_commP m (hcentspec y hy).1 hsimG0).mpr (by rw [hyc]; exact hc)⟩
    · rintro ⟨y, hy, hyc⟩
      rw [k0Of, List.mem_filter] at hy
      obtain ⟨hyL, hycomm⟩ := hy
      rw [← hyc]
      exact (a6cElt_commP m (hcentspec y hyL).1 hsimG0).mp hycomm

end CFSG.OddStandard.SmallF3.Omega
