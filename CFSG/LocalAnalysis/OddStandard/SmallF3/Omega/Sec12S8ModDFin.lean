module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDCodeMk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDOmData
public import Certificates.Certificate442331

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.S8DFin CFSG.HardMathSupport.RichardWeiss.Proving

private theorem s8d_eq_of_codes {f g : S8A} {m : M8}
    (hf : ∀ n, s8dAp f (s8dDec n) = s8dDec (m.ap n))
    (hg : ∀ k : Fin 8, s8dAp g (s8dBas k) = s8dDec (m.ap (2 ^ (k : ℕ)))) : f = g :=
  s8d_ext8 fun k => by
    have h := hf (2 ^ (k : ℕ))
    rw [s8dDec_bas k] at h
    rw [h, hg k]

private theorem s8d_rV_col : ∀ k : Fin 8, s8dCol rV k < 256 := by decide

private theorem s8d_cM_col : ∀ k : Fin 8, s8dCol cM k < 256 := by decide

private theorem s8d_iter_lt {m : M8} (hm : ∀ k : Fin 8, s8dCol m k < 256) {n : ℕ}
    (hn : n < 256) : ∀ k, m.iter k n < 256
  | 0 => hn
  | k + 1 => show m.ap (m.iter k n) < 256 from s8d_ap_lt hm _

private def s8dT1 : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide +kernel, by decide +kernel⟩

private def s8dT2 : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ :=
  ⟨!![0, 1; 1, 1], !![1, 1; 1, 0], by decide +kernel, by decide +kernel⟩

private def s8dT3 : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ :=
  ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide +kernel, by decide +kernel⟩

private def s8dT4 : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ :=
  ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide +kernel, by decide +kernel⟩

private def s8dT5 : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ :=
  ⟨!![1, 1; 1, 0], !![0, 1; 1, 1], by decide +kernel, by decide +kernel⟩

private theorem s8d_codes_one :
    ∀ k : Fin 8, s8dAp 1 (s8dBas k) = s8dDec ((mk 1 16).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_c0 : ∀ k : Fin 8,
    s8dAp (s8dDiag (finRotate 5)) (s8dBas k) = s8dDec ((mk 2 32).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S1 :
    ∀ k : Fin 8, s8dAp (s8dSplit s8dT1) (s8dBas k) = s8dDec ((mk 1 32).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S2 :
    ∀ k : Fin 8, s8dAp (s8dSplit s8dT2) (s8dBas k) = s8dDec ((mk 49 32).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S0 :
    ∀ k : Fin 8, s8dAp (s8dSplit 1) (s8dBas k) = s8dDec ((mk 2 16).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S3 :
    ∀ k : Fin 8, s8dAp (s8dSplit s8dT3) (s8dBas k) = s8dDec ((mk 50 16).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S4 :
    ∀ k : Fin 8, s8dAp (s8dSplit s8dT4) (s8dBas k) = s8dDec ((mk 2 19).ap (2 ^ (k : ℕ))) := by
  decide +kernel

private theorem s8d_codes_S5 :
    ∀ k : Fin 8, s8dAp (s8dSplit s8dT5) (s8dBas k) = s8dDec ((mk 1 35).ap (2 ^ (k : ℕ))) := by
  decide +kernel

theorem s8d_fin (f : S8A)
    (hc : f * s8dDiag (finRotate 5) = s8dDiag (finRotate 5) * f) (h5 : f ^ 5 = 1) (h1 : f ≠ 1)
    (hc0 : f ≠ s8dDiag (finRotate 5))
    (hb : s8dDiag altFiveVPerm * f * (s8dDiag altFiveVPerm)⁻¹ * (f⁻¹ * s8dDiag (finRotate 5)) =
      f⁻¹ * s8dDiag (finRotate 5) * (s8dDiag altFiveVPerm * f * (s8dDiag altFiveVPerm)⁻¹)) :
    (∃ T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ, f = s8dSplit T) ∨ f = s8dOm1 ∨ f = s8dOm2 := by
  obtain ⟨x, hx, y, hy, hf⟩ := s8d_mk_of_comm hc
  have hcol := s8d_mk_col_lt hx hy
  have hp5 : ∀ n < 256, (mk x y).iter 5 n = n := by
    intro n hn
    refine s8dDec_inj (s8d_iter_lt hcol hn 5) hn ?_
    rw [← s8dDec_iter hf, h5, s8dAp_one]
  have hinv : f⁻¹ = f ^ 4 := by
    have h54 : f ^ 4 * f = 1 := by
      rw [← pow_succ]
      exact h5
    exact (eq_inv_of_mul_eq_one_left h54).symm
  have hcomm : ∀ n < 256, commAt (mk x y) n = true := by
    intro n _
    have e := congrArg (fun e : S8A => s8dAp e (s8dDec n)) hb
    simp only [s8dAp_mul, hinv] at e
    simp only [s8dDec_cM, s8dDec_iter hf, s8dDec_rVi, hf, s8dDec_rV] at e
    have he := s8dDec_inj (s8d_ap_lt s8d_rV_col _)
      (s8d_iter_lt hcol (s8d_ap_lt s8d_cM_col _) 4) e
    unfold commAt
    rw [he]
    exact beq_self_eq_true _
  have hall : [1, 2, 4, 8, 16, 32, 64, 128].all (commAt (mk x y)) = true :=
    List.all_eq_true.mpr fun n hn => hcomm n (by simp at hn; omega)
  have hok : okXY x y = true := by
    have hcheck : check () = true := Certificates.certificate442331
    unfold check at hcheck
    exact List.all_eq_true.mp (List.all_eq_true.mp hcheck x (List.mem_range.mpr hx)) y
      (List.mem_range.mpr hy)
  have hmem : (x, y) ∈ sols := by
    unfold okXY at hok
    simp only [hp5 1 (by norm_num), hp5 16 (by norm_num), hall, beq_self_eq_true,
      Bool.and_self, Bool.not_true, Bool.false_or] at hok
    exact List.contains_iff.mp hok
  simp only [sols, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (s8d_eq_of_codes hf s8d_codes_one) h1
  · exact Or.inl ⟨s8dT1, s8d_eq_of_codes hf s8d_codes_S1⟩
  · exact Or.inl ⟨s8dT5, s8d_eq_of_codes hf s8d_codes_S5⟩
  · exact Or.inl ⟨1, s8d_eq_of_codes hf s8d_codes_S0⟩
  · exact Or.inl ⟨s8dT4, s8d_eq_of_codes hf s8d_codes_S4⟩
  · exact absurd (s8d_eq_of_codes hf s8d_codes_c0) hc0
  · exact Or.inl ⟨s8dT2, s8d_eq_of_codes hf s8d_codes_S2⟩
  · exact Or.inl ⟨s8dT3, s8d_eq_of_codes hf s8d_codes_S3⟩
  · exact Or.inr (Or.inl (s8d_om1_of hf))
  · exact Or.inr (Or.inr (s8d_om2_of hf))

end CFSG.OddStandard.SmallF3.Omega
