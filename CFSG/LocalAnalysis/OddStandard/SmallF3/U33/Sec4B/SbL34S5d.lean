module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

private lemma V_comm {B V : Subgroup G}
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hVB : V ≤ B) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
  fun a ha b hb => hBcomm a (hVB ha) b (hVB hb)

private lemma sigma_comm_mem {B V : Subgroup G} {σ : G}
    (hσB : ∀ b ∈ B, σ * b * σ⁻¹ ∈ B)
    (hσ2 : ∀ b ∈ B, (σ * σ) * b * (σ * σ)⁻¹ * b⁻¹ ∈ V)
    (hBsq : ∀ b ∈ B, b * b ∈ V)
    (b : G) (hb : b ∈ B) :
    σ * (σ * b * σ⁻¹ * b⁻¹) * σ⁻¹ * (σ * b * σ⁻¹ * b⁻¹)⁻¹ ∈ V := by
  have hx : σ * b * σ⁻¹ ∈ B := hσB b hb
  have hyb : (σ * (σ * b * σ⁻¹) * σ⁻¹) * b⁻¹ ∈ V := by
    have h := hσ2 b hb
    simpa [show σ * (σ * b * σ⁻¹) * σ⁻¹ = (σ * σ) * b * (σ * σ)⁻¹ by group] using h
  have hbb : b * (σ * b * σ⁻¹)⁻¹ ∈ B := B.mul_mem hb (B.inv_mem hx)
  have hsq : (b * (σ * b * σ⁻¹)⁻¹) * (b * (σ * b * σ⁻¹)⁻¹) ∈ V := hBsq _ hbb
  have key : σ * ((σ * b * σ⁻¹) * b⁻¹) * σ⁻¹ * ((σ * b * σ⁻¹) * b⁻¹)⁻¹
      = ((σ * (σ * b * σ⁻¹) * σ⁻¹) * b⁻¹)
        * ((b * (σ * b * σ⁻¹)⁻¹) * (b * (σ * b * σ⁻¹)⁻¹)) := by
    group
  rw [key]
  exact V.mul_mem hyb hsq

private lemma comm_mul_left {B V D : Subgroup G} {b₀ : G}
    (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ * b⁻¹ ∈ V)
    (hb₀ : b₀ ∈ B) (x : G) (hx : x ∈ D) (y : G) (hy : y ∈ D) :
    ⁅x * y, b₀⁆ = ⁅y, b₀⁆ * ⁅x, b₀⁆ := by
  have hyV : ⁅y, b₀⁆ ∈ V := by
    have h := hDB y hy b₀ hb₀
    simpa [commutatorElement_def] using h
  have hcomm : Commute x ⁅y, b₀⁆ := hDV x hx ⁅y, b₀⁆ hyV
  rw [commutatorElement_mul_left_eq_conj_mul, hcomm.mul_inv_cancel]

private lemma comm_sigma_fixed {B V D : Subgroup G} {σ b₀ : G}
    (hVBc : ∀ v ∈ V, ∀ b ∈ B, v * b = b * v)
    (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ * b⁻¹ ∈ V)
    (hσD : ∀ d ∈ D, ∃ v ∈ V, σ * d * σ⁻¹ = d * v)
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hb₀ : b₀ ∈ B) (hbc₀ : σ * b₀ * σ⁻¹ * b₀⁻¹ ∈ V)
    (x : G) (hx : x ∈ D) :
    σ * ⁅x, b₀⁆ * σ⁻¹ = ⁅x, b₀⁆ := by
  obtain ⟨v, hv, hv_eq⟩ := hσD x hx
  set c := σ * b₀ * σ⁻¹ * b₀⁻¹ with hc_def
  have hcV : c ∈ V := by rw [hc_def]; exact hbc₀
  have hvb : Commute v b₀ := hVBc v hv b₀ hb₀
  have hvc : Commute v c := hVcomm v hv c hcV
  have hdc : Commute x c := hDV x hx c hcV
  have hxbV : ⁅x, b₀⁆ ∈ V := by
    have h := hDB x hx b₀ hb₀
    simpa [commutatorElement_def] using h
  have hvc0 : Commute v (c * b₀) := hvc.mul_right hvb
  have h1 : ⁅v, c * b₀⁆ = 1 := hvc0.commutator_eq
  have h2 : ⁅x, c * b₀⁆ = c * ⁅x, b₀⁆ * c⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hdc.commutator_eq, one_mul]
  have hc_comm : Commute c ⁅x, b₀⁆ := hVcomm c hcV ⁅x, b₀⁆ hxbV
  have h3 : c * ⁅x, b₀⁆ * c⁻¹ = ⁅x, b₀⁆ := hc_comm.mul_inv_cancel
  have h4 : ⁅x * v, c * b₀⁆ = ⁅x, b₀⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, h1, h2, h3]
    simp
  have hsb : σ * b₀ * σ⁻¹ = c * b₀ := by
    rw [hc_def]; group
  calc σ * ⁅x, b₀⁆ * σ⁻¹ = ⁅x * v, c * b₀⁆ := by
        rw [conjugate_commutatorElement, hv_eq, hsb]
    _ = ⁅x, b₀⁆ := h4

private lemma Vf_ne {V : Subgroup G} {ρ σ : G}
    (hρ3 : ρ * ρ * ρ = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hρV : ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V)
    (hρnt : ∃ v ∈ V, ρ * v ≠ v * ρ) :
    V ⊓ Subgroup.centralizer ({σ} : Set G) ≠ V := by
  intro hEq
  have hfixV : ∀ v ∈ V, σ * v = v * σ := by
    intro v hv
    have hv' : v ∈ V ⊓ Subgroup.centralizer ({σ} : Set G) := by rw [hEq]; exact hv
    exact Subgroup.mem_centralizer_iff.mp hv'.2 σ (Set.mem_singleton σ)
  have hsigma_inv : ∀ v ∈ V, σ⁻¹ * v * σ = v := by
    intro v hv
    calc σ⁻¹ * v * σ = σ⁻¹ * (v * σ) := by group
      _ = σ⁻¹ * (σ * v) := by rw [← hfixV v hv]
      _ = v := by group
  have hρv : ∀ v ∈ V, ρ * v = v * ρ := by
    intro v hv
    have hwV : ρ * v * ρ⁻¹ ∈ V := hρV v hv
    have hwfix : σ * (ρ * v * ρ⁻¹) = (ρ * v * ρ⁻¹) * σ := hfixV _ hwV
    have hwσ : σ * (ρ * v * ρ⁻¹) * σ⁻¹ = ρ * v * ρ⁻¹ := by
      rw [hwfix, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : ρ⁻¹ * v * ρ = ρ * v * ρ⁻¹ := by
      calc ρ⁻¹ * v * ρ = (σ * ρ * σ⁻¹) * v * (σ * ρ * σ⁻¹)⁻¹ := by rw [hσρ]; group
        _ = σ * (ρ * (σ⁻¹ * v * σ) * ρ⁻¹) * σ⁻¹ := by group
        _ = σ * (ρ * v * ρ⁻¹) * σ⁻¹ := by rw [hsigma_inv v hv]
        _ = ρ * v * ρ⁻¹ := hwσ
    have hρ2' : v * (ρ * ρ) = (ρ * ρ) * v := by
      calc v * (ρ * ρ) = ρ * (ρ⁻¹ * v * ρ) * ρ := by group
        _ = ρ * (ρ * v * ρ⁻¹) * ρ := by rw [h1]
        _ = (ρ * ρ) * v := by group
    have hρ2 : (ρ * ρ) * v = v * (ρ * ρ) := hρ2'.symm
    have hρsq : ρ * ρ = ρ⁻¹ := mul_eq_one_iff_eq_inv.mp hρ3
    have hinv : ρ⁻¹ * v = v * ρ⁻¹ := by rw [← hρsq]; exact hρ2
    exact Commute.inv_left_iff.mp hinv
  obtain ⟨v, hv, hne⟩ := hρnt
  exact hne (hρv v hv)

theorem exists_cent_elem (B V D : Subgroup G) (ρ σ : G)
    (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (hVB : V ≤ B) (hB16 : Nat.card B = 16)
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBsq : ∀ b ∈ B, b * b ∈ V)
    (hVBc : ∀ v ∈ V, ∀ b ∈ B, v * b = b * v)
    (hD4 : Nat.card D = 4) (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ * b⁻¹ ∈ V)
    (hρ3 : ρ * ρ * ρ = 1) (hρB : ∀ b ∈ B, ρ * b * ρ⁻¹ ∈ B)
    (hρV : ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V) (hρD : ∀ d ∈ D, ρ * d = d * ρ)
    (hρfix : ∀ b ∈ B, ρ * b = b * ρ → b = 1) (hρnt : ∃ v ∈ V, ρ * v ≠ v * ρ)
    (hσB : ∀ b ∈ B, σ * b * σ⁻¹ ∈ B) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hσ2 : ∀ b ∈ B, (σ * σ) * b * (σ * σ)⁻¹ * b⁻¹ ∈ V)
    (hσD : ∀ d ∈ D, ∃ v ∈ V, σ * d * σ⁻¹ = d * v) :
    ∃ d ∈ D, d ≠ 1 ∧ ∀ b ∈ B, d * b = b * d := by
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := V_comm hBcomm hVB
  have hb₀_exists : ∃ b₀ ∈ B, b₀ ∉ V ∧ σ * b₀ * σ⁻¹ * b₀⁻¹ ∈ V := by
    by_contra hcon
    rw [not_exists] at hcon
    have hBleV : B ≤ V := by
      intro b hb
      have hcB : σ * b * σ⁻¹ * b⁻¹ ∈ B := B.mul_mem (hσB b hb) (B.inv_mem hb)
      have hcP : σ * (σ * b * σ⁻¹ * b⁻¹) * σ⁻¹ * (σ * b * σ⁻¹ * b⁻¹)⁻¹ ∈ V :=
        sigma_comm_mem hσB hσ2 hBsq b hb
      have hcV : σ * b * σ⁻¹ * b⁻¹ ∈ V := by
        by_contra hcV
        exact hcon (σ * b * σ⁻¹ * b⁻¹) ⟨hcB, hcV, hcP⟩
      by_contra hbV
      exact hcon b ⟨hb, hbV, hcV⟩
    have hcard : Nat.card B ≤ Nat.card V := Subgroup.card_le_of_le hBleV
    rw [hB16, hV4] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨b₀, hb₀, hb₀_notV, hb₀_comm⟩ := hb₀_exists
  let Vf : Subgroup G := V ⊓ Subgroup.centralizer ({σ} : Set G)
  have hVf_ne : Vf ≠ V := Vf_ne hρ3 hσρ hρV hρnt
  have hVf_le : Vf ≤ V := inf_le_left
  have hVf_lt : Vf < V := lt_of_le_of_ne hVf_le hVf_ne
  have hVf_card_lt : Nat.card Vf < 4 := by
    have h := Subgroup.card_lt_of_lt hVf_lt
    rwa [hV4] at h
  let f : ↥D → ↥Vf := fun x =>
    ⟨⁅(x : G)⁻¹, b₀⁆, by
      have hV : ⁅(x : G)⁻¹, b₀⁆ ∈ V := by
        have h := hDB (x : G)⁻¹ (D.inv_mem x.2) b₀ hb₀
        simpa [commutatorElement_def] using h
      have hC : ⁅(x : G)⁻¹, b₀⁆ ∈ Subgroup.centralizer ({σ} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]
          have hfix :=
            comm_sigma_fixed hVBc hDV hDB hσD hVcomm hb₀ hb₀_comm (x : G)⁻¹ (D.inv_mem x.2)
          exact mul_inv_eq_iff_eq_mul.mp hfix)
      exact ⟨hV, hC⟩⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hle : Nat.card D ≤ Nat.card Vf := Nat.card_le_card_of_injective f hinj
    rw [hD4] at hle
    exact absurd hle (not_le.mpr hVf_card_lt)
  obtain ⟨d₁, d₂, heq, hne⟩ := Function.not_injective_iff.mp hnotinj
  have heqG : ⁅(d₁ : G)⁻¹, b₀⁆ = ⁅(d₂ : G)⁻¹, b₀⁆ := congrArg Subtype.val heq
  let d : G := (d₁ : G)⁻¹ * (d₂ : G)
  have hdD : d ∈ D := D.mul_mem (D.inv_mem d₁.2) d₂.2
  have hdne : d ≠ 1 := by
    intro hd1
    apply hne
    have h : (d₂ : G) = (d₁ : G) := by
      have := congrArg (fun z => (d₁ : G) * z) hd1
      simpa [d] using this
    exact (Subtype.ext h).symm
  have hcomm_b₀ : d * b₀ = b₀ * d := by
    have hφd : ⁅d⁻¹, b₀⁆ = 1 := by
      have hd1inv : ⁅(d₁ : G)⁻¹, b₀⁆ = (⁅(d₁ : G), b₀⁆)⁻¹ := by
        have h := comm_mul_left hDV hDB hb₀ (d₁ : G) d₁.2 (d₁ : G)⁻¹ (D.inv_mem d₁.2)
        rw [mul_inv_cancel, commutatorElement_one_left] at h
        exact eq_inv_of_mul_eq_one_left h.symm
      have hd_inv : d⁻¹ = (d₂ : G)⁻¹ * (d₁ : G) := by simp [d]
      rw [hd_inv,
        comm_mul_left hDV hDB hb₀ (d₂ : G)⁻¹ (D.inv_mem d₂.2) (d₁ : G) d₁.2,
        ← heqG, hd1inv, mul_inv_cancel]
    have h : d⁻¹ * b₀ * d * b₀⁻¹ = 1 := by
      rw [commutatorElement_def] at hφd
      simpa using hφd
    have h3 : b₀ * d * b₀⁻¹ = d := by
      have := congrArg (fun z => d * z) h
      simpa [mul_assoc] using this
    have h4 : b₀ * d = d * b₀ := by
      have := congrArg (fun z => z * b₀) h3
      simpa [mul_assoc] using this
    exact h4.symm
  refine ⟨d, hdD, hdne, ?_⟩
  let K : Subgroup G := B ⊓ Subgroup.centralizer ({d} : Set G)
  have hKB : K ≤ B := inf_le_left
  have hVK : V ≤ K := by
    intro v hv
    exact ⟨hVB hv, Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hDV d hdD v hv)⟩
  have hb₀K : b₀ ∈ K := ⟨hb₀, Subgroup.mem_centralizer_iff.mpr (fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hcomm_b₀)⟩
  have hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K := by
    intro k hk
    have hkd : d * k = k * d := Subgroup.mem_centralizer_iff.mp hk.2 d (Set.mem_singleton d)
    have hρd : ρ * d = d * ρ := hρD d hdD
    have hdρinv : d * ρ⁻¹ = ρ⁻¹ * d := by
      calc d * ρ⁻¹ = ρ⁻¹ * (ρ * d) * ρ⁻¹ := by group
        _ = ρ⁻¹ * (d * ρ) * ρ⁻¹ := by rw [hρd]
        _ = ρ⁻¹ * d := by group
    refine ⟨hρB k hk.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    calc d * (ρ * k * ρ⁻¹) = (d * ρ) * k * ρ⁻¹ := by group
      _ = (ρ * d) * k * ρ⁻¹ := by rw [← hρd]
      _ = ρ * (d * k) * ρ⁻¹ := by group
      _ = ρ * (k * d) * ρ⁻¹ := by rw [hkd]
      _ = ρ * k * (d * ρ⁻¹) := by group
      _ = ρ * k * (ρ⁻¹ * d) := by rw [hdρinv]
      _ = (ρ * k * ρ⁻¹) * d := by group
  have hfixK : ∀ k ∈ K, ρ * k = k * ρ → k = 1 := fun k hk h => hρfix k hk.1 h
  have hdvd : Nat.card K ∣ 2 ^ 6 := by
    have h1 : Nat.card K ∣ Nat.card B := Subgroup.card_dvd_of_le hKB
    rw [hB16] at h1
    exact dvd_trans h1 (by norm_num)
  have hcases := card_cases_of_conj_fpf K ρ hρ3 hρK hfixK hdvd
  have hVKcard : 4 ≤ Nat.card K := by
    have h := Subgroup.card_le_of_le hVK
    rwa [hV4] at h
  have hKcard : Nat.card K = 16 := by
    rcases hcases with h | h | h | h
    · rw [h] at hVKcard
      exact absurd hVKcard (by norm_num)
    · have hVeqK : V = K := Subgroup.eq_of_le_of_card_ge hVK (by simp [h, hV4])
      exact absurd (by rw [hVeqK]; exact hb₀K) hb₀_notV
    · exact h
    · have hle : Nat.card K ≤ Nat.card B := Subgroup.card_le_of_le hKB
      rw [h, hB16] at hle
      exact absurd hle (by norm_num)
  have hK_eq_B : K = B := by
    apply Subgroup.eq_of_le_of_card_ge hKB
    simp [hB16, hKcard]
  intro b hb
  have hbK : b ∈ K := by rw [hK_eq_B]; exact hb
  exact Subgroup.mem_centralizer_iff.mp hbK.2 d (Set.mem_singleton d)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
