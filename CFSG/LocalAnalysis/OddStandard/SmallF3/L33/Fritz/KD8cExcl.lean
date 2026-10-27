module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cW2b
public import Certificates.Certificate22800
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cChk

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem pcx_0 : MC.PcX (vB 0 0) (vB 0 1) (vB 0 2) (vB 0 3) (vB 0 4) (vB 0 5) (vB 0 6)
    (vB 0 7) := by
  constructor <;> decide

theorem pcx_10 : MC.PcX (vB 10 0) (vB 10 1) (vB 10 2) (vB 10 3) (vB 10 4) (vB 10 5) (vB 10 6)
    (vB 10 7) := by
  constructor <;> decide

theorem nf_0 : ∀ a : MC, nfProd [vB 0 0, vB 0 1, vB 0 2, vB 0 3, vB 0 4, vB 0 5, vB 0 6,
    vB 0 7] (MC.nfBits a) = if chi0B 0 a then Multiplicative.ofAdd 1 else 1 := by
  decide +kernel

theorem nf_10 : ∀ a : MC, nfProd [vB 10 0, vB 10 1, vB 10 2, vB 10 3, vB 10 4, vB 10 5,
    vB 10 6, vB 10 7] (MC.nfBits a) = if chi0B 10 a then Multiplicative.ofAdd 1 else 1 := by
  decide +kernel

theorem pcx_1 : MC.PcX (vB 1 0) (vB 1 1) (vB 1 2) (vB 1 3) (vB 1 4) (vB 1 5) (vB 1 6)
    (vB 1 7) := by
  constructor <;> decide

theorem nf_1 : ∀ a : MC, nfProd [vB 1 0, vB 1 1, vB 1 2, vB 1 3, vB 1 4, vB 1 5, vB 1 6,
    vB 1 7] (MC.nfBits a) = if chi0B 1 a then Multiplicative.ofAdd 1 else 1 := by
  decide +kernel

theorem phi_1_1 : ∀ a : MC, chi0B 1 (phiR 1 a) = chi0B 1 a := by decide +kernel

theorem s_1 : chi0B 1 (sR 1 0) = false := by decide +kernel

theorem chi0B_zero : ∀ a : MC, chi0B 0 a = false := by decide +kernel

theorem phi_10_5 : ∀ a : MC, chi0B 10 (phiR 5 a) = chi0B 10 a := by decide +kernel

theorem phi_10_6 : ∀ a : MC, chi0B 10 (phiR 6 a) = chi0B 10 a := by decide +kernel

theorem s_10 : chi0B 10 (sR 5 0) = false ∧ chi0B 10 (sR 5 1) = false ∧
    chi0B 10 (sR 6 1) = false := by
  decide +kernel

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2}

theorem false_A_of [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (W : T.Lift)
    {bs : ℕ} {qb : Bool} {reps : List ℕ} {tab g cg : ℕ}
    (hpc : MC.PcX (vB bs 0) (vB bs 1) (vB bs 2) (vB bs 3) (vB bs 4) (vB bs 5) (vB bs 6)
      (vB bs 7))
    (hnf : ∀ a : MC, nfProd [vB bs 0, vB bs 1, vB bs 2, vB bs 3, vB bs 4, vB bs 5, vB bs 6,
      vB bs 7] (MC.nfBits a) = if chi0B bs a then Multiplicative.ofAdd 1 else 1)
    (hφ : ∀ a : MC, chi0B bs (phiR W.j a) = chi0B bs a) (hs : chi0B bs (sR W.j W.i) = false)
    {q0 : Bool} (hq0 : q0 = true → ¬ ConjTo t (K.ι MC.w₂))
    (hc : checkA W.D' bs qb q0 reps tab g cg = true) : False := by
  obtain ⟨χ₀, hχ₀⟩ := exists_chi0 bs hpc hnf
  obtain ⟨χ, hχ⟩ := exists_chi W.hj3 W.hj4 W.i bs qb hχ₀ hφ hs
  exact W.false_of_checkA hnonab hχ hq0 hc

theorem false_E_of [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (W : T.Lift)
    {bs : ℕ} {qb : Bool} {reps : List ℕ} {tab : ℕ}
    (hpc : MC.PcX (vB bs 0) (vB bs 1) (vB bs 2) (vB bs 3) (vB bs 4) (vB bs 5) (vB bs 6)
      (vB bs 7))
    (hnf : ∀ a : MC, nfProd [vB bs 0, vB bs 1, vB bs 2, vB bs 3, vB bs 4, vB bs 5, vB bs 6,
      vB bs 7] (MC.nfBits a) = if chi0B bs a then Multiplicative.ofAdd 1 else 1)
    (hφ : ∀ a : MC, chi0B bs (phiR W.j a) = chi0B bs a) (hs : chi0B bs (sR W.j W.i) = false)
    (hc : checkE W.D' bs qb reps tab = true) : False := by
  obtain ⟨χ₀, hχ₀⟩ := exists_chi0 bs hpc hnf
  obtain ⟨χ, hχ⟩ := exists_chi W.hj3 W.hj4 W.i bs qb hχ₀ hφ hs
  exact W.false_of_checkE hnonab hχ hc


theorem false_of_cert [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (W : T.Lift)
    (h : (W.j = 1 ∧ W.i = 0) ∨ (W.j = 1 ∧ W.i = 1) ∨ (W.j = 2 ∧ W.i = 0) ∨
      (W.j = 2 ∧ W.i = 1) ∨
      (W.j = 7 ∧ W.i = 0) ∨ (W.j = 7 ∧ W.i = 1) ∨ (W.j = 5 ∧ W.i = 0) ∨
      (W.j = 5 ∧ W.i = 1) ∨ (W.j = 6 ∧ W.i = 1)) : False := by
  have hc := Certificates.certificate22800
  obtain ⟨j, i, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ := W
  simp only at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact false_A_of hnonab ⟨1, 0, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_1 nf_1
      phi_1_1 s_1 (fun _ => K.not_conjTo_w₂) hc.1
  · exact false_A_of hnonab ⟨1, 1, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_0 nf_0
      (fun a => by rw [chi0B_zero, chi0B_zero]) (chi0B_zero _) (q0 := false)
      (fun h => absurd h (by decide)) hc.2.1
  · exact false_A_of hnonab ⟨2, 0, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_0 nf_0
      (fun a => by rw [chi0B_zero, chi0B_zero]) (chi0B_zero _) (q0 := false)
      (fun h => absurd h (by decide)) hc.2.2.1
  · exact false_A_of hnonab ⟨2, 1, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_0 nf_0
      (fun a => by rw [chi0B_zero, chi0B_zero]) (chi0B_zero _) (q0 := false)
      (fun h => absurd h (by decide)) hc.2.2.2.1
  · exact false_A_of hnonab ⟨7, 0, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_0 nf_0
      (fun a => by rw [chi0B_zero, chi0B_zero]) (chi0B_zero _) (q0 := false)
      (fun h => absurd h (by decide)) hc.2.2.2.2.1
  · exact false_A_of hnonab ⟨7, 1, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_0 nf_0
      (fun a => by rw [chi0B_zero, chi0B_zero]) (chi0B_zero _) (q0 := false)
      (fun h => absurd h (by decide)) hc.2.2.2.2.2.1
  · exact false_E_of hnonab ⟨5, 0, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_10 nf_10
      phi_10_5 s_10.1 hc.2.2.2.2.2.2.1
  · exact false_E_of hnonab ⟨5, 1, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_10 nf_10
      phi_10_5 s_10.2.1 hc.2.2.2.2.2.2.2.1
  · exact false_E_of hnonab ⟨6, 1, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ pcx_10 nf_10
      phi_10_6 s_10.2.2 hc.2.2.2.2.2.2.2.2

end Lift

end T2

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
