module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDCode

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.S8DFin

theorem s8d_mk_col_lt {x y : ℕ} (hx : x < 256) (hy : y < 256) (k : Fin 8) :
    s8dCol (mk x y) k < 256 := by
  fin_cases k <;> simp [s8dCol, mk]
  · exact hx
  · exact s8d_cmul_lt hx
  · exact s8d_cmul_lt (s8d_cmul_lt hx)
  · exact s8d_cmul_lt (s8d_cmul_lt (s8d_cmul_lt hx))
  · exact hy
  · exact s8d_cmul_lt hy
  · exact s8d_cmul_lt (s8d_cmul_lt hy)
  · exact s8d_cmul_lt (s8d_cmul_lt (s8d_cmul_lt hy))

private theorem s8dDec_cmul {n : ℕ} (hn : n < 256) :
    s8dAp (s8dDiag (finRotate 5)) (s8dDec n) = s8dDec (cmul n) := by
  rw [s8dDec_cM, s8d_cM_ap hn]

private theorem s8d_bas1 (h : (1 : ℕ) < 8) :
    s8dBas (⟨1, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas 0) := by
  rw [show (⟨1, h⟩ : Fin 8) = 1 from Fin.ext rfl]
  decide +kernel

private theorem s8d_bas2 (h : (2 : ℕ) < 8) :
    s8dBas (⟨2, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas ⟨1, by norm_num⟩) := by
  rw [show (⟨2, h⟩ : Fin 8) = 2 from Fin.ext rfl]
  rw [show (⟨1, by norm_num⟩ : Fin 8) = 1 from Fin.ext rfl]
  decide +kernel

private theorem s8d_bas3 (h : (3 : ℕ) < 8) :
    s8dBas (⟨3, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas ⟨2, by norm_num⟩) := by
  rw [show (⟨3, h⟩ : Fin 8) = 3 from Fin.ext rfl]
  rw [show (⟨2, by norm_num⟩ : Fin 8) = 2 from Fin.ext rfl]
  decide +kernel

private theorem s8d_bas5 (h : (5 : ℕ) < 8) :
    s8dBas (⟨5, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas ⟨4, by norm_num⟩) := by
  rw [show (⟨5, h⟩ : Fin 8) = 5 from Fin.ext rfl]
  rw [show (⟨4, by norm_num⟩ : Fin 8) = 4 from Fin.ext rfl]
  decide +kernel

private theorem s8d_bas6 (h : (6 : ℕ) < 8) :
    s8dBas (⟨6, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas ⟨5, by norm_num⟩) := by
  rw [show (⟨6, h⟩ : Fin 8) = 6 from Fin.ext rfl]
  rw [show (⟨5, by norm_num⟩ : Fin 8) = 5 from Fin.ext rfl]
  decide +kernel

private theorem s8d_bas7 (h : (7 : ℕ) < 8) :
    s8dBas (⟨7, h⟩ : Fin 8) = s8dAp (s8dDiag (finRotate 5)) (s8dBas ⟨6, by norm_num⟩) := by
  rw [show (⟨7, h⟩ : Fin 8) = 7 from Fin.ext rfl]
  rw [show (⟨6, by norm_num⟩ : Fin 8) = 6 from Fin.ext rfl]
  decide +kernel

private theorem s8d_mk_basis {f : S8A}
    (hc : f * s8dDiag (finRotate 5) = s8dDiag (finRotate 5) * f) {x y : ℕ}
    (hxlt : x < 256) (hylt : y < 256) (hx : s8dDec x = s8dAp f (s8dBas 0))
    (hy : s8dDec y = s8dAp f (s8dBas 4)) :
    ∀ k : Fin 8, s8dAp f (s8dBas k) = s8dDec (s8dCol (mk x y) k) := by
  have hc' : ∀ p, s8dAp f (s8dAp (s8dDiag (finRotate 5)) p) =
      s8dAp (s8dDiag (finRotate 5)) (s8dAp f p) := by
    intro p
    have h := congrArg (fun e : S8A => s8dAp e p) hc
    simpa [s8dAp_mul] using h
  have hx' : s8dAp f (s8dBas 0) = s8dDec x := hx.symm
  have hy' : s8dAp f (s8dBas 4) = s8dDec y := hy.symm
  have hy4 : ∀ h : (4 : ℕ) < 8, s8dAp f (s8dBas (⟨4, h⟩ : Fin 8)) = s8dDec y := by
    intro h
    rw [show (⟨4, h⟩ : Fin 8) = 4 from Fin.ext rfl]
    exact hy'
  intro k
  fin_cases k <;> dsimp only
  · simpa [s8dCol, mk] using hx'
  · rw [s8d_bas1, hc', hx', s8dDec_cmul hxlt]
    simp [s8dCol, mk]
  · rw [s8d_bas2, s8d_bas1, hc', hc', hx', s8dDec_cmul hxlt,
      s8dDec_cmul (s8d_cmul_lt hxlt)]
    simp [s8dCol, mk]
  · rw [s8d_bas3, s8d_bas2, s8d_bas1, hc', hc', hc', hx', s8dDec_cmul hxlt,
      s8dDec_cmul (s8d_cmul_lt hxlt), s8dDec_cmul (s8d_cmul_lt (s8d_cmul_lt hxlt))]
    simp [s8dCol, mk]
  · simpa [s8dCol, mk] using hy'
  · rw [s8d_bas5, hc', hy4, s8dDec_cmul hylt]
    simp [s8dCol, mk]
  · rw [s8d_bas6, s8d_bas5, hc', hc', hy4, s8dDec_cmul hylt,
      s8dDec_cmul (s8d_cmul_lt hylt)]
    simp [s8dCol, mk]
  · rw [s8d_bas7, s8d_bas6, s8d_bas5, hc', hc', hc', hy4, s8dDec_cmul hylt,
      s8dDec_cmul (s8d_cmul_lt hylt), s8dDec_cmul (s8d_cmul_lt (s8d_cmul_lt hylt))]
    simp [s8dCol, mk]

theorem s8d_mk_of_comm {f : S8A}
    (hc : f * s8dDiag (finRotate 5) = s8dDiag (finRotate 5) * f) :
    ∃ x < 256, ∃ y < 256, ∀ n, s8dAp f (s8dDec n) = s8dDec ((mk x y).ap n) := by
  obtain ⟨x, hxlt, hx⟩ := s8dDec_surj (s8dAp f (s8dBas 0))
  obtain ⟨y, hylt, hy⟩ := s8dDec_surj (s8dAp f (s8dBas 4))
  refine ⟨x, hxlt, y, hylt, fun n => ?_⟩
  exact s8dDec_ap (f := fun p => s8dAp f p) (m := mk x y)
    (fun p q => s8dAp_add f p q) (s8d_mk_basis hc hxlt hylt hx hy) n

end CFSG.OddStandard.SmallF3.Omega
