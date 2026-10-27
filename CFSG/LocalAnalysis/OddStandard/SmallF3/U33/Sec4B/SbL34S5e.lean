module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem omega_one_cases (B V : Subgroup G) (ρ : G) (hρ3 : ρ * ρ * ρ = 1)
    (hVB : V ≤ B) (hV4 : Nat.card V = 4) (hB16 : Nat.card B = 16)
    (hVsq : ∀ v ∈ V, v * v = 1) (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hρB : ∀ b ∈ B, ρ * b * ρ⁻¹ ∈ B) (hfix : ∀ b ∈ B, ρ * b = b * ρ → b = 1) :
    (∀ b ∈ B, b * b = 1) ∨ ∀ b ∈ B, b * b = 1 → b ∈ V := by
  classical
  let K : Subgroup G :=
    { carrier := {b | b ∈ B ∧ b * b = 1}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨haB, ha⟩ := ha
        obtain ⟨hbB, hb⟩ := hb
        refine ⟨B.mul_mem haB hbB, ?_⟩
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hBcomm b hbB a haB]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha, hb, mul_one]
      one_mem' := ⟨B.one_mem, by group⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨haB, ha⟩ := ha
        refine ⟨B.inv_mem haB, ?_⟩
        rw [← mul_inv_rev, ha, inv_one] }
  have hKB : K ≤ B := fun x hx => hx.1
  have hVK : V ≤ K := fun v hv => ⟨hVB hv, hVsq v hv⟩
  have hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K := by
    intro k hk
    refine ⟨hρB k hk.1, ?_⟩
    calc (ρ * k * ρ⁻¹) * (ρ * k * ρ⁻¹) = ρ * (k * k) * ρ⁻¹ := by group
      _ = 1 := by rw [hk.2]; group
  have hfixK : ∀ k ∈ K, ρ * k = k * ρ → k = 1 := fun k hk => hfix k hk.1
  have hdvdK : Nat.card K ∣ 2 ^ 6 := by
    have h : Nat.card K ∣ Nat.card B := Subgroup.card_dvd_of_le hKB
    rw [hB16] at h
    exact dvd_trans h ⟨4, by norm_num⟩
  have h4le : 4 ≤ Nat.card K := by
    have h : Nat.card V ≤ Nat.card K := Subgroup.card_le_of_le hVK
    rwa [hV4] at h
  have hKle16 : Nat.card K ≤ 16 := by
    have h : Nat.card K ≤ Nat.card B := Subgroup.card_le_of_le hKB
    rwa [hB16] at h
  rcases card_cases_of_conj_fpf K ρ hρ3 hρK hfixK hdvdK with h1 | h4 | h16 | h64
  · exfalso
    rw [h1] at h4le
    exact absurd h4le (by norm_num)
  · right
    have hVeq : V = K := Subgroup.eq_of_le_of_card_ge hVK (by simp [h4, hV4])
    intro b hb hbb
    rw [hVeq]
    exact ⟨hb, hbb⟩
  · left
    have hKeq : K = B := Subgroup.eq_of_le_of_card_ge hKB (by simp [h16, hB16])
    intro b hb
    have hbK : b ∈ K := by rw [hKeq]; exact hb
    exact hbK.2
  · exfalso
    rw [h64] at hKle16
    exact absurd hKle16 (by norm_num)

theorem cent_eq_of_fpf (Q B V : Subgroup G) (ρ : G) (hρ3 : ρ * ρ * ρ = 1)
    (hQ64 : Nat.card Q = 2 ^ 6) (hBQ : B ≤ Q) (hB16 : Nat.card B = 16) (hV4 : Nat.card V = 4)
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hρB : ∀ b ∈ B, ρ * b * ρ⁻¹ ∈ B)
    (hfix : ∀ q ∈ Q, ρ * q = q * ρ → q = 1)
    (hZ : ∀ b ∈ B, (∀ q ∈ Q, q * b = b * q) → b ∈ V) :
    ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → q ∈ B := by
  classical
  have hρ2 : ρ * ρ = ρ⁻¹ :=
    (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hρ3)).symm
  have hρinv2 : ρ⁻¹ * ρ⁻¹ = ρ := by
    rw [← mul_inv_rev, hρ2, inv_inv]
  set C : Subgroup G := Q ⊓ centralizer (B : Set G) with hCdef
  have hBC : B ≤ C := by
    intro b hb
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨hBQ hb, fun b' hb' => hBcomm b' hb' b hb⟩
  have hCρ : ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C := by
    intro c hc
    rw [hCdef, Subgroup.mem_inf] at hc
    obtain ⟨hcQ, hcB⟩ := hc
    have hcB' : ∀ b ∈ B, b * c = c * b := Subgroup.mem_centralizer_iff.mp hcB
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨hρQ c hcQ, ?_⟩
    intro b hb
    have hb' : ρ⁻¹ * b * ρ ∈ B := by
      have h := hρB (ρ * b * ρ⁻¹) (hρB b hb)
      have key : ρ * (ρ * b * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * b * ρ := by
        calc ρ * (ρ * b * ρ⁻¹) * ρ⁻¹
            = (ρ * ρ) * b * (ρ⁻¹ * ρ⁻¹) := by group
          _ = ρ⁻¹ * b * (ρ⁻¹ * ρ⁻¹) := by rw [hρ2]
          _ = ρ⁻¹ * b * ρ := by rw [hρinv2]
      rwa [key] at h
    have hcomm' : c * (ρ⁻¹ * b * ρ) = (ρ⁻¹ * b * ρ) * c := (hcB' (ρ⁻¹ * b * ρ) hb').symm
    symm
    calc (ρ * c * ρ⁻¹) * b = ρ * c * (ρ⁻¹ * b * ρ) * ρ⁻¹ := by group
      _ = ρ * (c * (ρ⁻¹ * b * ρ)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * b * ρ) * c) * ρ⁻¹ := by rw [hcomm']
      _ = b * (ρ * c * ρ⁻¹) := by group
  have hfixC : ∀ c ∈ C, ρ * c = c * ρ → c = 1 := by
    intro c hc hcomm
    have hcQ : c ∈ Q := by rw [hCdef] at hc; exact hc.1
    exact hfix c hcQ hcomm
  have hdvd : Nat.card C ∣ 2 ^ 6 := by
    have h : Nat.card C ∣ Nat.card Q :=
      Subgroup.card_dvd_of_le (by rw [hCdef]; exact inf_le_left)
    rwa [hQ64] at h
  have h16le : 16 ≤ Nat.card C := by
    have h : Nat.card B ≤ Nat.card C := Subgroup.card_le_of_le hBC
    rwa [hB16] at h
  rcases card_cases_of_conj_fpf C ρ hρ3 hCρ hfixC hdvd with h1 | h4 | h16 | h64
  · exfalso
    rw [h1] at h16le
    exact absurd h16le (by norm_num)
  · exfalso
    rw [h4] at h16le
    exact absurd h16le (by norm_num)
  · intro q hqQ hqB
    have hqC : q ∈ C := by
      rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact ⟨hqQ, fun b hb => (hqB b hb).symm⟩
    have hCB : C = B :=
      (Subgroup.eq_of_le_of_card_ge hBC (by simp [h16, hB16])).symm
    rwa [hCB] at hqC
  · exfalso
    have hCleQ : C ≤ Q := by rw [hCdef]; exact inf_le_left
    have hCeqQ : C = Q :=
      Subgroup.eq_of_le_of_card_ge hCleQ (by rw [hQ64, h64]; norm_num)
    have hBV : ∀ b ∈ B, b ∈ V := by
      intro b hb
      apply hZ b hb
      intro q hq
      have hqC : q ∈ C := by rw [hCeqQ]; exact hq
      have hqcent : q ∈ centralizer (B : Set G) := by
        rw [hCdef] at hqC
        exact hqC.2
      exact ((Subgroup.mem_centralizer_iff.mp hqcent) b hb).symm
    have hcardle : Nat.card B ≤ Nat.card V := Subgroup.card_le_of_le hBV
    rw [hB16, hV4] at hcardle
    exact absurd hcardle (by norm_num)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
