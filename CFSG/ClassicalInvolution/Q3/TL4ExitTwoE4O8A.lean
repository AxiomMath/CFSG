module

public import Certificates.Certificate127
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.E4QuatArr
public import Certificates.Data.E4QuatCheck
public import Certificates.Data.E4QuatO8
public import Certificates.Data.O8p2NoDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem rels : gen 8 * (gen 8 * gen 8) = 1 ∧ gen 9 * gen 9 = 1 ∧
    gen 9 * gen 8 * gen 9 = gen 8 * gen 8 :=
  Certificates.certificate127.1

@[expose] noncomputable def sig : List (Equiv.Perm (Fin 360)) :=
  [1, gen 8, gen 8 * gen 8, gen 9, gen 9 * gen 8, gen 9 * (gen 8 * gen 8)]

theorem rho_tau : gen 8 * gen 9 = gen 9 * (gen 8 * gen 8) := by
  obtain ⟨-, h2, h3⟩ := rels
  calc gen 8 * gen 9 = gen 9 * gen 9 * (gen 8 * gen 9) := by rw [h2, one_mul]
    _ = gen 9 * (gen 9 * gen 8 * gen 9) := by group
    _ = gen 9 * (gen 8 * gen 8) := by rw [h3]

theorem rho_mul_mem {s : Equiv.Perm (Fin 360)} (hs : s ∈ sig) : gen 8 * s ∈ sig := by
  obtain ⟨h1, -, -⟩ := rels
  have hrt := rho_tau
  simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · left
    rw [← mul_assoc] at h1
    rw [mul_assoc] at h1
    exact h1
  · right; right; right; right; right
    exact hrt
  · right; right; right
    left
    calc gen 8 * (gen 9 * gen 8) = gen 8 * gen 9 * gen 8 := by group
      _ = gen 9 * (gen 8 * (gen 8 * gen 8)) := by rw [hrt]; group
      _ = gen 9 := by rw [h1, mul_one]
  · right; right; right; right
    left
    calc gen 8 * (gen 9 * (gen 8 * gen 8)) = gen 8 * gen 9 * (gen 8 * gen 8) := by group
      _ = gen 9 * (gen 8 * (gen 8 * gen 8)) * gen 8 := by rw [hrt]; group
      _ = gen 9 * gen 8 := by rw [h1, mul_one]

theorem tau_mul_mem {s : Equiv.Perm (Fin 360)} (hs : s ∈ sig) : gen 9 * s ∈ sig := by
  obtain ⟨-, h2, -⟩ := rels
  simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · left
    exact h2
  · right
    left
    rw [← mul_assoc, h2, one_mul]
  · right; right
    left
    rw [← mul_assoc, h2, one_mul]

theorem mul_mem_sig {s s' : Equiv.Perm (Fin 360)} (hs : s ∈ sig) (hs' : s' ∈ sig) :
    s * s' ∈ sig := by
  simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rwa [one_mul]
  · exact rho_mul_mem hs'
  · rw [mul_assoc]
    exact rho_mul_mem (rho_mul_mem hs')
  · exact tau_mul_mem hs'
  · rw [mul_assoc]
    exact tau_mul_mem (rho_mul_mem hs')
  · rw [mul_assoc, mul_assoc]
    exact tau_mul_mem (rho_mul_mem (rho_mul_mem hs'))

theorem inv_mem_sig {s : Equiv.Perm (Fin 360)} (hs : s ∈ sig) : s⁻¹ ∈ sig := by
  have hfin : ∀ s ∈ sig, ∃ s' ∈ sig, s * s' = 1 := by
    intro s hs
    obtain ⟨h1, h2, -⟩ := rels
    have hrt := rho_tau
    simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by simp [sig], one_mul 1⟩
    · exact ⟨gen 8 * gen 8, by simp [sig], h1⟩
    · exact ⟨gen 8, by simp [sig], by rw [mul_assoc]; exact h1⟩
    · exact ⟨gen 9, by simp [sig], h2⟩
    · refine ⟨gen 9 * gen 8, by simp [sig], ?_⟩
      calc gen 9 * gen 8 * (gen 9 * gen 8) = gen 9 * (gen 8 * gen 9) * gen 8 := by group
        _ = gen 9 * gen 9 * (gen 8 * (gen 8 * gen 8)) := by rw [hrt]; group
        _ = 1 := by rw [h1, h2, one_mul]
    · refine ⟨gen 9 * (gen 8 * gen 8), by simp [sig], ?_⟩
      calc gen 9 * (gen 8 * gen 8) * (gen 9 * (gen 8 * gen 8))
          = gen 9 * gen 8 * (gen 8 * gen 9) * (gen 8 * gen 8) := by group
        _ = gen 9 * gen 8 * (gen 9 * (gen 8 * gen 8)) * (gen 8 * gen 8) := by rw [hrt]
        _ = gen 9 * (gen 8 * gen 9) * ((gen 8 * gen 8) * (gen 8 * gen 8)) := by group
        _ = gen 9 * (gen 9 * (gen 8 * gen 8)) * ((gen 8 * gen 8) * (gen 8 * gen 8)) := by
          rw [hrt]
        _ = gen 9 * gen 9 * ((gen 8 * (gen 8 * gen 8)) * (gen 8 * (gen 8 * gen 8))) := by group
        _ = 1 := by rw [h1, h2, one_mul, one_mul]
  obtain ⟨s', hs', he⟩ := hfin s hs
  rwa [inv_eq_of_mul_eq_one_right he]

theorem exists_sig {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) :
    ∃ ω ∈ omegaT, ∃ s ∈ sig, a = ω * s := by
  rw [autT_eq] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    by_cases h8 : i < 8
    · exact ⟨gen i, gen_mem_omegaT h8, 1, by simp [sig], (mul_one _).symm⟩
    · obtain rfl | rfl : i = 8 ∨ i = 9 := by omega
      · exact ⟨1, omegaT.one_mem, gen 8, by simp [sig], (one_mul _).symm⟩
      · exact ⟨1, omegaT.one_mem, gen 9, by simp [sig], (one_mul _).symm⟩
  | one => exact ⟨1, omegaT.one_mem, 1, by simp [sig], (one_mul 1).symm⟩
  | mul x y hx' hy' hx hy =>
    obtain ⟨ω, hω, s, hs, rfl⟩ := hx
    obtain ⟨ω', hω', s', hs', rfl⟩ := hy
    have hsA : s ∈ autT := by
      simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact autT.one_mem
        | exact autT.mul_mem (gen_mem_autT (by norm_num)) (gen_mem_autT (by norm_num))
        | exact gen_mem_autT (by norm_num)
        | exact autT.mul_mem (gen_mem_autT (by norm_num))
            (autT.mul_mem (gen_mem_autT (by norm_num)) (gen_mem_autT (by norm_num)))
    refine ⟨ω * (s * ω' * s⁻¹), omegaT.mul_mem hω ((conj_mem_omegaT hsA).1 hω'), s * s',
      mul_mem_sig hs hs', by group⟩
  | inv x hx' hx =>
    obtain ⟨ω, hω, s, hs, rfl⟩ := hx
    have hsA : s⁻¹ ∈ autT := by
      have := inv_mem_sig hs
      simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h | h | h <;> rw [h] <;>
        first
        | exact autT.one_mem
        | exact autT.mul_mem (gen_mem_autT (by norm_num)) (gen_mem_autT (by norm_num))
        | exact gen_mem_autT (by norm_num)
        | exact autT.mul_mem (gen_mem_autT (by norm_num))
            (autT.mul_mem (gen_mem_autT (by norm_num)) (gen_mem_autT (by norm_num)))
    refine ⟨s⁻¹ * ω⁻¹ * s⁻¹⁻¹, (conj_mem_omegaT hsA).1 (omegaT.inv_mem hω), s⁻¹,
      inv_mem_sig hs, by group⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
