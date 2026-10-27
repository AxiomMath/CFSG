module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1r
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section GroupHelpers

private theorem conj_conj_of_comm {q x m : G} (hmq : m * q = q * m) :
    q * (m * x * m⁻¹) * q⁻¹ = m * (q * x * q⁻¹) * m⁻¹ := by
  have h1 : q * m = m * q := hmq.symm
  have h2 : m⁻¹ * q⁻¹ = q⁻¹ * m⁻¹ := by
    rw [← mul_inv_rev q m, ← mul_inv_rev m q, hmq]
  calc q * (m * x * m⁻¹) * q⁻¹
      = (q * m) * x * (m⁻¹ * q⁻¹) := by group
    _ = (m * q) * x * (q⁻¹ * m⁻¹) := by rw [h1, h2]
    _ = m * (q * x * q⁻¹) * m⁻¹ := by group

private theorem comm_of_conj_eq {a b : G} (h : a * b * a⁻¹ = b) : a * b = b * a := by
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [h]

end GroupHelpers

section Adjust

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

private theorem comm_fourGrp_of {v : G} (hvy : v * x₁ ^ 2 = x₁ ^ 2 * v)
    (hvz : v * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * v) :
    ∀ a ∈ fourGrp x₁ x₂, v * a = a * v := by
  intro a ha
  rcases (mem_fourGrp_iff hc.toCtx4Q a).mp ha with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact hvy
  · exact hvz
  · calc v * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = (v * x₁ ^ 2) * (x₁ * x₂) ^ 2 := by group
      _ = (x₁ ^ 2 * v) * (x₁ * x₂) ^ 2 := by rw [hvy]
      _ = x₁ ^ 2 * (v * (x₁ * x₂) ^ 2) := by group
      _ = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * v) := by rw [hvz]
      _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * v := by group

theorem y_conj_q : x₁ ^ 2 * (t * lam) * (x₁ ^ 2)⁻¹ = (t * lam) * (x₁ * x₂) ^ 2 := by
  have hqy := q_conj_y hc.toCtx4Q
  have hqz := q_conj_z hc.toCtx4Q
  have hqinv : (t * lam)⁻¹ = t * lam :=
    inv_eq_of_mul_eq_one_right (q_mul_self hc.toCtx4Q)
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := y_mul_self hc.toCtx4Q
  have hyinv : (x₁ ^ 2)⁻¹ = x₁ ^ 2 := inv_eq_of_mul_eq_one_right hy2
  have hA : (t * lam) * x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 * (t * lam) := by
    have h : (t * lam) * x₁ ^ 2 * (t * lam) = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
      simpa [hqinv] using hqy
    calc (t * lam) * x₁ ^ 2 = ((t * lam) * x₁ ^ 2) * ((t * lam) * (t * lam)) := by
          rw [q_mul_self hc.toCtx4Q, mul_one]
      _ = (((t * lam) * x₁ ^ 2) * (t * lam)) * (t * lam) := by group
      _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (t * lam) := by rw [h]
  have hB : (t * lam) * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * (t * lam) := by
    have h : (t * lam) * (x₁ * x₂) ^ 2 * (t * lam) = (x₁ * x₂) ^ 2 := by
      simpa [hqinv] using hqz
    calc (t * lam) * (x₁ * x₂) ^ 2 =
        ((t * lam) * (x₁ * x₂) ^ 2) * ((t * lam) * (t * lam)) := by
          rw [q_mul_self hc.toCtx4Q, mul_one]
      _ = (((t * lam) * (x₁ * x₂) ^ 2) * (t * lam)) * (t * lam) := by group
      _ = (x₁ * x₂) ^ 2 * (t * lam) := by rw [h]
  calc x₁ ^ 2 * (t * lam) * (x₁ ^ 2)⁻¹
      = x₁ ^ 2 * ((t * lam) * x₁ ^ 2) := by rw [hyinv]; group
    _ = x₁ ^ 2 * (x₁ ^ 2 * (x₁ * x₂) ^ 2 * (t * lam)) := by rw [hA]
    _ = (x₁ ^ 2 * x₁ ^ 2) * (x₁ * x₂) ^ 2 * (t * lam) := by group
    _ = (x₁ * x₂) ^ 2 * (t * lam) := by rw [hy2, one_mul]
    _ = (t * lam) * (x₁ * x₂) ^ 2 := hB.symm

theorem cent_of_conj_qz {g : G} (hg : g * (t * lam) * g⁻¹ = (t * lam) * (x₁ * x₂) ^ 2) :
    ((x₁ ^ 2)⁻¹ * g) * (t * lam) * ((x₁ ^ 2)⁻¹ * g)⁻¹ = t * lam := by
  have hy := y_conj_q hc
  have h2 : (x₁ ^ 2)⁻¹ * ((t * lam) * (x₁ * x₂) ^ 2) * x₁ ^ 2 = t * lam := by
    have h := congrArg (fun u => (x₁ ^ 2)⁻¹ * u * x₁ ^ 2) hy
    rw [show (x₁ ^ 2)⁻¹ * (x₁ ^ 2 * (t * lam) * (x₁ ^ 2)⁻¹) * x₁ ^ 2 = t * lam by group] at h
    exact h.symm
  calc ((x₁ ^ 2)⁻¹ * g) * (t * lam) * ((x₁ ^ 2)⁻¹ * g)⁻¹
      = (x₁ ^ 2)⁻¹ * (g * (t * lam) * g⁻¹) * x₁ ^ 2 := by group
    _ = (x₁ ^ 2)⁻¹ * ((t * lam) * (x₁ * x₂) ^ 2) * x₁ ^ 2 := by rw [hg]
    _ = t * lam := h2

theorem exists_u_cent {n : G} (hnN : n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G)) :
    ∃ u ∈ ctxU t tau x₁ x₂ lam, (u * n) * (t * lam) * (u * n)⁻¹ = t * lam := by
  have hnO : n ∈ normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) :=
    norm_U_le_LO hc hnN
  set q' : G := n * (t * lam) * n⁻¹ with hq'_def
  have hq'U : q' ∈ ctxU t tau x₁ x₂ lam := by
    rw [hq'_def]
    exact (Subgroup.mem_normalizer_iff.mp hnN (t * lam)).mp (q_mem_U hc)
  have hq'O : q' ∉ ctxO t tau x₁ x₂ := by
    intro h
    apply q_not_mem_O hc
    rw [hq'_def] at h
    exact (Subgroup.mem_normalizer_iff.mp hnO (t * lam)).mpr h
  set w : G := (t * lam)⁻¹ * q' with hw_def
  have hw : w ∈ ctxO t tau x₁ x₂ := by
    rw [hw_def]
    exact inv_mul_mem_O hc (q_mem_U hc) hq'U (q_not_mem_O hc) hq'O
  have hq'w : (t * lam) * w = q' := by
    rw [hw_def]; group
  have hq'2 : q' * q' = 1 := by
    rw [hq'_def]
    calc (n * (t * lam) * n⁻¹) * (n * (t * lam) * n⁻¹)
        = n * ((t * lam) * (t * lam)) * n⁻¹ := by group
      _ = 1 := by rw [q_mul_self hc.toCtx4Q]; group
  have hqw : (t * lam * w) * (t * lam * w) = 1 := by
    have h : t * lam * w = q' := hq'w
    rw [h]; exact hq'2
  obtain ⟨b, hb, hxX⟩ := claim1 hc hw hqw
  set x : G := (t * lam)⁻¹ * (b⁻¹ * (t * lam * w) * b) with hx_def
  have hbx : b⁻¹ * q' * b = (t * lam) * x := by
    rw [hx_def, hq'w]
    group
  have hinv : (t * lam * x) * (t * lam * x) = 1 := by
    rw [hbx.symm]
    calc (b⁻¹ * q' * b) * (b⁻¹ * q' * b) = b⁻¹ * (q' * q') * b := by group
      _ = 1 := by rw [hq'2]; group
  have hcl : ∃ g : G, g * t * g⁻¹ = t * lam * x := by
    obtain ⟨g₀, hg₀⟩ := hc.inv_tl 1 (one_mem _) (by simpa using q_mul_self hc.toCtx4Q)
    have hg₀' : g₀ * t * g₀⁻¹ = t * lam := by
      simpa using hg₀
    refine ⟨b⁻¹ * n * g₀, ?_⟩
    calc (b⁻¹ * n * g₀) * t * (b⁻¹ * n * g₀)⁻¹
        = b⁻¹ * (n * (g₀ * t * g₀⁻¹) * n⁻¹) * b := by group
      _ = b⁻¹ * (n * (t * lam) * n⁻¹) * b := by rw [hg₀']
      _ = b⁻¹ * q' * b := by rw [hq'_def]
      _ = (t * lam) * x := hbx
  rcases x_one_or_z hc hxX hinv hcl with hx1 | hxz
  · refine ⟨b⁻¹, O_le_U hc (inv_mem hb), ?_⟩
    calc (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹
        = b⁻¹ * q' * b := by rw [hq'_def]; group
      _ = (t * lam) * x := hbx
      _ = t * lam := by rw [hx1, mul_one]
  · refine ⟨(x₁ ^ 2)⁻¹ * b⁻¹, ?_, ?_⟩
    · exact mul_mem
        (inv_mem (O_le_U hc (hc.toCtx4Q.Q_le_O
          (hc.toCtx4Q.V_le_Q (subset_closure (by simp))))))
        (inv_mem (O_le_U hc hb))
    · have hgt : (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹ = (t * lam) * (x₁ * x₂) ^ 2 := by
        calc (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹
            = b⁻¹ * q' * b := by rw [hq'_def]; group
          _ = (t * lam) * x := hbx
          _ = (t * lam) * (x₁ * x₂) ^ 2 := by rw [hxz]
      have hcent := cent_of_conj_qz hc hgt
      rw [show (x₁ ^ 2)⁻¹ * (b⁻¹ * n) = ((x₁ ^ 2)⁻¹ * b⁻¹) * n from
        (mul_assoc (x₁ ^ 2)⁻¹ b⁻¹ n).symm] at hcent
      exact hcent

theorem exists_cent {W : Subgroup G} {n : G} (hUW : ctxU t tau x₁ x₂ lam ≤ W) (hnW : n ∈ W)
    (hnN : n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G))
    (hnU : n ∉ ctxU t tau x₁ x₂ lam) (hn2 : n ^ 2 ∈ ctxU t tau x₁ x₂ lam) :
    ∃ g : G, g ∈ W ∧ g ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) ∧
      g ∉ ctxU t tau x₁ x₂ lam ∧ g ^ 2 ∈ ctxU t tau x₁ x₂ lam ∧
      g * (t * lam) = (t * lam) * g := by
  obtain ⟨u, hu, hq⟩ := exists_u_cent hc hnN
  set g : G := u * n with hg_def
  have hgW : g ∈ W := by rw [hg_def]; exact mul_mem (hUW hu) hnW
  have hgN : g ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) := by
    rw [hg_def]
    exact mul_mem (Subgroup.le_normalizer hu) hnN
  have hgU : g ∉ ctxU t tau x₁ x₂ lam := by
    intro hg
    apply hnU
    have h := mul_mem (inv_mem hu) hg
    rwa [show u⁻¹ * g = n from by rw [hg_def]; group] at h
  have hnu : n * u * n⁻¹ ∈ ctxU t tau x₁ x₂ lam :=
    (Subgroup.mem_normalizer_iff.mp hnN u).mp hu
  have hg2U : g ^ 2 ∈ ctxU t tau x₁ x₂ lam := by
    rw [hg_def, pow_two]
    have hEq : (u * n) * (u * n) = u * (n * u * n⁻¹) * n ^ 2 := by group
    rw [hEq]
    exact mul_mem (mul_mem hu hnu) hn2
  have hgq : g * (t * lam) = (t * lam) * g := by
    have h : g * (t * lam) * g⁻¹ = t * lam := by
      rw [hg_def]; exact hq
    calc g * (t * lam) = (g * (t * lam) * g⁻¹) * g := by group
      _ = (t * lam) * g := by rw [h]
  exact ⟨g, hgW, hgN, hgU, hg2U, hgq⟩

theorem conj_V_cases {g : G}
    (hgN : g ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G))
    (hgq : g * (t * lam) = (t * lam) * g) :
    g * (x₁ * x₂) ^ 2 * g⁻¹ = (x₁ * x₂) ^ 2 ∧
      (g * x₁ ^ 2 * g⁻¹ = x₁ ^ 2 ∨ g * x₁ ^ 2 * g⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2) := by
  have hgV : g ∈ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    normalizer_le_of_charIn hc.char_V hgN
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hmemV : ∀ {a : G}, a ∈ fourGrp x₁ x₂ → g * a * g⁻¹ ∈ fourGrp x₁ x₂ :=
    fun ha => (Subgroup.mem_normalizer_iff.mp hgV _).mp ha
  have hzg : g * (x₁ * x₂) ^ 2 * g⁻¹ = (x₁ * x₂) ^ 2 := by
    have hconj : (t * lam) * (g * (x₁ * x₂) ^ 2 * g⁻¹) * (t * lam)⁻¹ =
        g * (x₁ * x₂) ^ 2 * g⁻¹ := by
      rw [conj_conj_of_comm hgq, q_conj_z hc.toCtx4Q]
    rcases CV_q hc.toCtx4Q (hmemV hzV) hconj with h1 | hz
    · exfalso
      have hz1 : (x₁ * x₂) ^ 2 = 1 := by
        have h := congrArg (fun u => g⁻¹ * u * g) h1
        rw [show g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g = (x₁ * x₂) ^ 2 by group,
          show g⁻¹ * 1 * g = 1 by group] at h
        exact h
      exact z_ne_one hc.toCtx4Q hz1
    · exact hz
  refine ⟨hzg, ?_⟩
  have hconj : (t * lam) * (g * x₁ ^ 2 * g⁻¹) * (t * lam)⁻¹ =
      (g * x₁ ^ 2 * g⁻¹) * (x₁ * x₂) ^ 2 := by
    rw [conj_conj_of_comm hgq, q_conj_y hc.toCtx4Q]
    rw [show g * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * g⁻¹ =
        (g * x₁ ^ 2 * g⁻¹) * (g * (x₁ * x₂) ^ 2 * g⁻¹) by group, hzg]
  rcases (mem_fourGrp_iff hc.toCtx4Q (g * x₁ ^ 2 * g⁻¹)).mp (hmemV hyV) with
    h1 | h2 | h3 | h4
  · exfalso
    have hy1 : x₁ ^ 2 = 1 := by
      have h := congrArg (fun u => g⁻¹ * u * g) h1
      rw [show g⁻¹ * (g * x₁ ^ 2 * g⁻¹) * g = x₁ ^ 2 by group,
        show g⁻¹ * 1 * g = 1 by group] at h
      exact h
    exact hc.toCtx4Q.y_ne_one hy1
  · exact Or.inl h2
  · exfalso
    have hyz : x₁ ^ 2 = (x₁ * x₂) ^ 2 := by
      have h := h3.trans hzg.symm
      have h' := congrArg (fun u => g⁻¹ * u * g) h
      rw [show g⁻¹ * (g * x₁ ^ 2 * g⁻¹) * g = x₁ ^ 2 by group,
        show g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g = (x₁ * x₂) ^ 2 by group] at h'
      exact h'
    exact y_ne_z hc.toCtx4Q hyz
  · exact Or.inr h4

theorem exists_v_of_cent {W : Subgroup G} {g : G} (hUW : ctxU t tau x₁ x₂ lam ≤ W) (hgW : g ∈ W)
    (hgN : g ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G))
    (hgU : g ∉ ctxU t tau x₁ x₂ lam) (hg2 : g ^ 2 ∈ ctxU t tau x₁ x₂ lam)
    (hgq : g * (t * lam) = (t * lam) * g) :
    ∃ v : G, v ∈ W ∧ v ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) ∧
      v ∉ ctxU t tau x₁ x₂ lam ∧ v ^ 2 ∈ ctxU t tau x₁ x₂ lam ∧
      v * (t * lam) = (t * lam) * v ∧ ∀ a ∈ fourGrp x₁ x₂, v * a = a * v := by
  obtain ⟨hzg, hycase⟩ := conj_V_cases hc hgN hgq
  rcases hycase with hgy | hgyz
  · refine ⟨g, hgW, hgN, hgU, hg2, hgq, ?_⟩
    apply comm_fourGrp_of hc
    · exact comm_of_conj_eq hgy
    · exact comm_of_conj_eq hzg
  · have hvz : (g * (t * lam)) * (x₁ * x₂) ^ 2 * (g * (t * lam))⁻¹ = (x₁ * x₂) ^ 2 := by
      calc (g * (t * lam)) * (x₁ * x₂) ^ 2 * (g * (t * lam))⁻¹
          = g * ((t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹) * g⁻¹ := by group
        _ = g * (x₁ * x₂) ^ 2 * g⁻¹ := by rw [q_conj_z hc.toCtx4Q]
        _ = (x₁ * x₂) ^ 2 := hzg
    have hvy : (g * (t * lam)) * x₁ ^ 2 * (g * (t * lam))⁻¹ = x₁ ^ 2 := by
      calc (g * (t * lam)) * x₁ ^ 2 * (g * (t * lam))⁻¹
          = g * ((t * lam) * x₁ ^ 2 * (t * lam)⁻¹) * g⁻¹ := by group
        _ = g * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * g⁻¹ := by rw [q_conj_y hc.toCtx4Q]
        _ = (g * x₁ ^ 2 * g⁻¹) * (g * (x₁ * x₂) ^ 2 * g⁻¹) := by group
        _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hgyz, hzg]
        _ = x₁ ^ 2 := by rw [mul_assoc, z_mul_self hc.toCtx4Q, mul_one]
    have hvq : (g * (t * lam)) * (t * lam) = (t * lam) * (g * (t * lam)) := by
      calc (g * (t * lam)) * (t * lam)
          = g * ((t * lam) * (t * lam)) := by group
        _ = g := by rw [q_mul_self hc.toCtx4Q, mul_one]
        _ = ((t * lam) * (t * lam)) * g := by rw [q_mul_self hc.toCtx4Q, one_mul]
        _ = (t * lam) * ((t * lam) * g) := by group
        _ = (t * lam) * (g * (t * lam)) := by rw [← hgq]
    refine ⟨g * (t * lam), mul_mem hgW (hUW (q_mem_U hc)),
      mul_mem hgN (Subgroup.le_normalizer (q_mem_U hc)), ?_, ?_, hvq,
      comm_fourGrp_of hc (comm_of_conj_eq hvy) (comm_of_conj_eq hvz)⟩
    · intro hvU
      apply hgU
      have hqinvU : (t * lam)⁻¹ ∈ ctxU t tau x₁ x₂ lam :=
        inv_mem (q_mem_U hc)
      have h := mul_mem hvU hqinvU
      rwa [show (g * (t * lam)) * (t * lam)⁻¹ = g from by group] at h
    · have hEq : (g * (t * lam)) ^ 2 = g ^ 2 := by
        rw [pow_two]
        calc (g * (t * lam)) * (g * (t * lam))
            = (g * g) * ((t * lam) * (t * lam)) := by
              calc (g * (t * lam)) * (g * (t * lam))
                  = g * ((t * lam) * g) * (t * lam) := by group
                _ = g * (g * (t * lam)) * (t * lam) := by rw [← hgq]
                _ = (g * g) * ((t * lam) * (t * lam)) := by group
          _ = g ^ 2 := by rw [q_mul_self hc.toCtx4Q, mul_one, pow_two]
      rw [hEq]; exact hg2

end Adjust

end CFSG.OddStandard.SmallF3.HarrisU33.L34

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l34_s1 : L34S1Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hB hc
  obtain ⟨W, n, hWsyl, hUW, hnW, hnN, hnU, hn2⟩ := L34.exists_n_W hc
  obtain ⟨g, hgW, hgN, hgU, hg2, hgq⟩ := L34.exists_cent hc hUW hnW hnN hnU hn2
  obtain ⟨v, hvW, hvN, hvU, hv2, hvq, hvV⟩ :=
    L34.exists_v_of_cent hc hUW hgW hgN hgU hg2 hgq
  exact ⟨W, v, ⟨hWsyl, hUW, hvW, hvN, hvU, hv2, hvq, hvV⟩⟩

end CFSG.OddStandard.SmallF3.HarrisU33
