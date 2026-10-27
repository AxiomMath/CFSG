module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem y7c_odd_splits {G : Type} [Group G] (M K J F Q : Subgroup G) (t : G)
    (hMK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) (hMle : M ≤ K)
    (ht2 : t ^ 2 = 1) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hFM : F ≤ M) (hFJ : F ≤ J) (hJK : J ≤ K) (hJt : ∀ j ∈ J, j * t = t * j)
    (hcent : ∀ m ∈ M, t * m * t⁻¹ = m → m ∈ F)
    (hQK : Q ≤ K) (hQ1 : ∀ x ∈ Q, x ∈ M → x = 1) (hQc : ∀ q ∈ Q, ∀ k ∈ K, ⁅k, q⁆ ∈ M)
    (hQt : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hQM : ∀ m ∈ M, (∀ q ∈ Q, q * m * q⁻¹ = m) → m = 1)
    (hFr : ∀ k ∈ K, ∃ m ∈ M, ∃ n ∈ K, (∀ q ∈ Q, n * q * n⁻¹ ∈ Q) ∧ k = m * n) :
    SplitsOver J F := by
  classical
  let B : Subgroup G := K ⊓ Subgroup.centralizer (Q : Set G)
  let C : Subgroup G := J ⊓ B ⊓ Subgroup.centralizer ({t} : Set G)
  have hBmem : ∀ x : G, x ∈ B ↔ x ∈ K ∧ ∀ q ∈ Q, q * x = x * q := by
    intro x
    simp [B, Subgroup.mem_centralizer_iff]
  have hCmem : ∀ x : G, x ∈ C ↔ (x ∈ J ∧ x ∈ B) ∧ t * x = x * t := by
    intro x
    simp [C, Subgroup.mem_centralizer_iff]
  have htinv : t⁻¹ = t := by
    have htt : t * t = 1 := by simpa only [pow_two] using ht2
    exact inv_eq_of_mul_eq_one_right htt
  have hN_le_B : ∀ n ∈ K, (∀ q ∈ Q, n * q * n⁻¹ ∈ Q) → n ∈ B := by
    intro n hnK hnN
    rw [hBmem n]
    refine ⟨hnK, ?_⟩
    intro q hq
    have hcQ : ⁅n, q⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (hnN q hq) (Q.inv_mem hq)
    have hcM : ⁅n, q⁆ ∈ M := hQc q hq n hnK
    have hc1 : ⁅n, q⁆ = 1 := hQ1 ⁅n, q⁆ hcQ hcM
    rw [commutatorElement_def] at hc1
    have h1 : n * q * n⁻¹ = q := by
      simpa [mul_assoc] using congrArg (· * q) hc1
    have h2 : n * q = q * n := by
      simpa [mul_assoc] using congrArg (· * n) h1
    exact h2.symm
  have hMB1 : ∀ x ∈ M ⊓ B, x = 1 := by
    intro x hx
    obtain ⟨hxM, hxB⟩ := Subgroup.mem_inf.mp hx
    exact hQM x hxM fun q hq => by
      have hqx : q * x = x * q := ((hBmem x).mp hxB).2 q hq
      rw [hqx, mul_inv_cancel_right]
  have hB_t : ∀ b ∈ B, t * b * t⁻¹ ∈ B := by
    intro b hb
    obtain ⟨hbK, hbQ⟩ := (hBmem b).mp hb
    rw [hBmem (t * b * t⁻¹)]
    refine ⟨htK b hbK, ?_⟩
    intro q hq
    have hq' : t⁻¹ * q * t ∈ Q := by
      simpa [htinv] using hQt q hq
    have hcomm : (t⁻¹ * q * t) * b = b * (t⁻¹ * q * t) := hbQ (t⁻¹ * q * t) hq'
    calc
      q * (t * b * t⁻¹) = t * ((t⁻¹ * q * t) * b) * t⁻¹ := by group
      _ = t * (b * (t⁻¹ * q * t)) * t⁻¹ := by rw [hcomm]
      _ = (t * b * t⁻¹) * q := by group
  have hJ_cent : ∀ j ∈ J, t * j * t⁻¹ = j := by
    intro j hj
    have hjt : j * t = t * j := hJt j hj
    have h1 : t⁻¹ * j * t = j := by
      rw [mul_assoc, hjt, ← mul_assoc, inv_mul_cancel, one_mul]
    simpa [htinv] using h1
  have hfactor : ∀ j ∈ J, ∃ m ∈ F, ∃ n ∈ C, j = m * n := by
    intro j hj
    obtain ⟨m, hmM, n, hnK, hnN, hjm⟩ := hFr j (hJK hj)
    have hnB : n ∈ B := hN_le_B n hnK hnN
    have htmM : t * m * t⁻¹ ∈ M := htM m hmM
    have htnB : t * n * t⁻¹ ∈ B := hB_t n hnB
    have heq : m * n = (t * m * t⁻¹) * (t * n * t⁻¹) := by
      rw [← hjm, ← hJ_cent j hj, hjm]
      group
    have huniq : m⁻¹ * (t * m * t⁻¹) = n * (t * n * t⁻¹)⁻¹ := by
      have h := congrArg (fun x => m⁻¹ * x * (t * n * t⁻¹)⁻¹) heq
      simpa [mul_assoc] using h.symm
    have hMpart : m⁻¹ * (t * m * t⁻¹) ∈ M := M.mul_mem (M.inv_mem hmM) htmM
    have hBpart : m⁻¹ * (t * m * t⁻¹) ∈ B := by
      rw [huniq]
      exact B.mul_mem hnB (B.inv_mem htnB)
    have hx1 : m⁻¹ * (t * m * t⁻¹) = 1 := hMB1 _ ⟨hMpart, hBpart⟩
    have htm : t * m * t⁻¹ = m := by
      have h := congrArg (fun x => m * x) hx1
      simpa [mul_assoc] using h
    have hx1' : n * (t * n * t⁻¹)⁻¹ = 1 := huniq ▸ hx1
    have htn : t * n * t⁻¹ = n := by
      have h := congrArg (fun x => x * (t * n * t⁻¹)) hx1'
      have h' : n = t * n * t⁻¹ := by simpa [mul_assoc] using h
      exact h'.symm
    have hmF : m ∈ F := hcent m hmM htm
    have hnJ : n ∈ J := by
      have hmj : m⁻¹ * j = n := by rw [hjm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← hmj]
      exact J.mul_mem (J.inv_mem (hFJ hmF)) hj
    have hnC : n ∈ C := by
      rw [hCmem n]
      refine ⟨⟨hnJ, hnB⟩, ?_⟩
      have hnt : t * n = n * t := by
        have h := congrArg (fun x => x * t) htn
        simpa [mul_assoc] using h
      exact hnt
    exact ⟨m, hmF, n, hnC, hjm⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x hx
    exact ((hCmem x).mp hx).1.1
  · apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨⟨-, hxB⟩, -⟩ := (hCmem x).mp hxC
    exact hMB1 x ⟨hFM hxF, hxB⟩
  · apply le_antisymm
    · refine sup_le hFJ ?_
      intro x hx
      exact ((hCmem x).mp hx).1.1
    · intro j hj
      obtain ⟨m, hmF, n, hnC, rfl⟩ := hfactor j hj
      exact Subgroup.mul_mem_sup hmF hnC

end CFSG.OddStandard.HigherRank.YamadaG23
