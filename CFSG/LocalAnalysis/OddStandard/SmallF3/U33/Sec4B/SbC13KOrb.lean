module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_t_inv (hc : Ctx13M t L S x₁ x₂ lam rho tau om) : t⁻¹ = t := by
  have h : t * t = 1 := by
    have h2 := (c13K_rel hc).1
    rwa [pow_two] at h2
  exact inv_eq_of_mul_eq_one_right h

private lemma c13K_comm_eq_commutatorElement (hc : Ctx13M t L S x₁ x₂ lam rho tau om) (q : G) :
    t * q * t * q⁻¹ = ⁅t, q⁆ := by
  rw [commutatorElement_def, c13K_t_inv hc]

private lemma c13K_commutatorElement_mem_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : ⁅t, q⁆ ∈ ctxQ t tau x₁ x₂ rho := by
  rw [← c13K_comm_eq_commutatorElement hc q]
  refine (ctxQ t tau x₁ x₂ rho).mul_mem ?_ ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
  have h := hc.normal_Q.2 t (c13K_mem_M hc).1 q hq
  rwa [c13K_t_inv hc] at h

private lemma c13K_comm_t_one (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = 1 := by
  refine ⟨1, (ctxQ t tau x₁ x₂ rho).one_mem, ?_⟩
  have h : t * t = 1 := by
    have h2 := (c13K_rel hc).1
    rwa [pow_two] at h2
  simpa using h

private lemma c13K_comm_t_mul (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {a b : G}
    (ha : ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = a)
    (hb : ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = b) :
    ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = a * b := by
  obtain ⟨q1, hq1, rfl⟩ := ha
  obtain ⟨q2, hq2, rfl⟩ := hb
  refine ⟨q1 * q2, (ctxQ t tau x₁ x₂ rho).mul_mem hq1 hq2, ?_⟩
  rw [c13K_comm_eq_commutatorElement hc (q1 * q2),
    c13K_comm_eq_commutatorElement hc q1, c13K_comm_eq_commutatorElement hc q2,
    commutatorElement_mul_right_eq_mul_conj]
  have hmem2 : ⁅t, q2⁆ ∈ ctxQ t tau x₁ x₂ rho := c13K_commutatorElement_mem_Q hc hq2
  have hcomm2 : q1 * ⁅t, q2⁆ = ⁅t, q2⁆ * q1 := hc.Q_comm q1 hq1 ⁅t, q2⁆ hmem2
  calc ⁅t, q1⁆ * q1 * ⁅t, q2⁆ * q1⁻¹
      = ⁅t, q1⁆ * (q1 * ⁅t, q2⁆) * q1⁻¹ := by group
    _ = ⁅t, q1⁆ * (⁅t, q2⁆ * q1) * q1⁻¹ := by rw [hcomm2]
    _ = ⁅t, q1⁆ * ⁅t, q2⁆ := by group

private lemma c13K_comm_t_inv (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = a) :
    ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = a⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := ha
  refine ⟨q⁻¹, (ctxQ t tau x₁ x₂ rho).inv_mem hq, ?_⟩
  rw [c13K_comm_eq_commutatorElement hc (q⁻¹), c13K_comm_eq_commutatorElement hc q,
    commutatorElement_inv_right, commutatorElement_inv]
  have hmem : ⁅q, t⁆ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← commutatorElement_inv]
    exact (ctxQ t tau x₁ x₂ rho).inv_mem (c13K_commutatorElement_mem_Q hc hq)
  have hcomm : q * ⁅q, t⁆ = ⁅q, t⁆ * q := hc.Q_comm q hq ⁅q, t⁆ hmem
  rw [mul_assoc, ← hcomm]
  group

theorem c13K_comm_t_surj (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = v := by
  intro v hv
  obtain ⟨V', v₁, v₂, hEAb, _hcard, hQ, _hinf, _hrho, _hlamt, _hY, _hv1C, hv1mem, _hv1ne,
    ht_v1, hv2mem, _hv2not, _hV'cl, ht_v2, _hlamt_v2, _hCttau, _homx1, _homx2⟩ := hc.data_V
  have hV'le : V' ≤ ctxQ t tau x₁ x₂ rho := by
    rw [hQ]
    exact le_sup_right
  have hv1Q : v₁ ∈ ctxQ t tau x₁ x₂ rho := hV'le hv1mem
  have hv2Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := hV'le hv2mem
  have hx1sqQ : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q ((baseGrp x₁ x₂).pow_mem (Subgroup.subset_closure (by simp)) 2)
  have hx1x2Q : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q ((baseGrp x₁ x₂).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hx1x2sqQ : (x₁ * x₂) ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).pow_mem hx1x2Q 2
  refine Subgroup.closure_induction (k := ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    (p := fun v _ => ∃ q ∈ ctxQ t tau x₁ x₂ rho, t * q * t * q⁻¹ = v) ?_ ?_ ?_ ?_ hv
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨v₂, hv2Q, ?_⟩
      have h1 : t * v₂ * t = v₂ * x₁ ^ 2 := by
        have h := ht_v2
        rwa [c13K_t_inv hc] at h
      calc t * v₂ * t * v₂⁻¹
          = (v₂ * x₁ ^ 2) * v₂⁻¹ := by rw [h1]
        _ = x₁ ^ 2 := by rw [hc.Q_comm v₂ hv2Q (x₁ ^ 2) hx1sqQ]; group
    · refine ⟨v₁, hv1Q, ?_⟩
      have h1 : t * v₁ * t = v₁ * (x₁ * x₂) ^ 2 := by
        have h := ht_v1
        rwa [c13K_t_inv hc] at h
      calc t * v₁ * t * v₁⁻¹
          = (v₁ * (x₁ * x₂) ^ 2) * v₁⁻¹ := by rw [h1]
        _ = (x₁ * x₂) ^ 2 := by rw [hc.Q_comm v₁ hv1Q ((x₁ * x₂) ^ 2) hx1x2sqQ]; group
  · exact c13K_comm_t_one hc
  · intro x y _hx _hy ihx ihy
    exact c13K_comm_t_mul hc ihx ihy
  · intro x _hx ihx
    exact c13K_comm_t_inv hc ihx

theorem c13K_C_inf_Y (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {c : G}
    (hcC : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
    (hcY : c ∈ ctxYq t tau x₁ x₂ rho) : c ∈ fourGrp x₁ x₂ := by
  have hmem : c ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := ⟨hcY, hcC.2⟩
  rwa [hc.Y_cent.2] at hmem

private lemma c13K_rho_comm_tt (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Commute rho (t * tau) := by
  obtain ⟨hrt, hrtau, _⟩ := c13K_rho_comm hc
  show rho * (t * tau) = (t * tau) * rho
  calc rho * (t * tau) = (rho * t) * tau := by group
    _ = (t * rho) * tau := by rw [hrt]
    _ = t * (rho * tau) := by group
    _ = t * (tau * rho) := by rw [hrtau]
    _ = (t * tau) * rho := by group

private lemma c13K_rho_conj_mem_C (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {c : G}
    (hcC : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) :
    rho * c * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact hc.normal_Q.2 rho (c13K_mem_M hc).2.2.2.1 c hcC.1
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((c13K_rho_comm_tt hc).mul_left
        (Subgroup.mem_centralizer_singleton_iff.mp hcC.2)).mul_left
          (c13K_rho_comm_tt hc).inv_left)

theorem c13K_rho_norm_C (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {c : G}
    (hcC : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) :
    rho * c * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) ∧
      rho ^ 2 * c * (rho ^ 2)⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
  have h1 := c13K_rho_conj_mem_C hc hcC
  refine ⟨h1, ?_⟩
  have h2 := c13K_rho_conj_mem_C hc h1
  have heq : rho * (rho * c * rho⁻¹) * rho⁻¹ = rho ^ 2 * c * (rho ^ 2)⁻¹ := by
    simp only [pow_two]
    group
  rwa [heq] at h2

private lemma c13K_om_conj_tau (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om * tau * om⁻¹ = tau := by
  obtain ⟨_, _, _, _, _, _, htauom, _⟩ := c13K_rel hc
  calc om * tau * om⁻¹ = tau * om * om⁻¹ := by rw [htauom.symm]
    _ = tau := by group

private lemma c13K_om_conj_tt (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om * (t * tau) * om⁻¹ = t := by
  obtain ⟨_, _, _, htau2, _, _, _, homt⟩ := c13K_rel hc
  calc om * (t * tau) * om⁻¹
      = (om * t * om⁻¹) * (om * tau * om⁻¹) := by group
    _ = (t * tau) * tau := by rw [homt, c13K_om_conj_tau hc]
    _ = t := by rw [mul_assoc, ← pow_two, htau2, mul_one]

theorem c13K_orbit_swap (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {d : G}
    (hd : d ∈ baseGrp x₁ x₂) (hdV : d ∉ fourGrp x₁ x₂) :
    ∃ m ∈ ctxM t tau x₁ x₂, ∃ c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G),
      c ∉ fourGrp x₁ x₂ ∧ m * (t * tau * d) * m⁻¹ = t * c := by
  obtain ⟨_, _, _, _, _, _, _, homt⟩ := c13K_rel hc
  have hdt : t * d = d * t := by
    have hdC : d ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
      rw [(c13K_lemma4_12a hc).2.2.1]
      exact hd
    exact (Subgroup.mem_centralizer_singleton_iff.mp hdC.2).symm
  refine ⟨om, (c13K_mem_M hc).2.2.1, om * d * om⁻¹, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hc.normal_Q.2 om (c13K_mem_M hc).2.2.1 d (hc.base_le_Q hd)
    · rw [Subgroup.mem_centralizer_singleton_iff, eq_comm]
      calc (t * tau) * (om * d * om⁻¹)
          = (om * t * om⁻¹) * (om * d * om⁻¹) := by rw [← homt]
        _ = om * t * d * om⁻¹ := by group
        _ = om * (t * d) * om⁻¹ := by group
        _ = om * (d * t) * om⁻¹ := by rw [hdt]
        _ = om * d * t * om⁻¹ := by group
        _ = (om * d * om⁻¹) * (om * t * om⁻¹) := by group
        _ = (om * d * om⁻¹) * (t * tau) := by rw [homt]
  · intro hcV
    have hmem : om⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem (c13K_mem_M hc).2.2.1
    have h := hc.normal_V.2 om⁻¹ hmem (om * d * om⁻¹) hcV
    have hd_eq : om⁻¹ * (om * d * om⁻¹) * (om⁻¹)⁻¹ = d := by group
    rw [hd_eq] at h
    exact hdV h
  · calc om * (t * tau * d) * om⁻¹
        = (om * (t * tau) * om⁻¹) * (om * d * om⁻¹) := by group
      _ = t * (om * d * om⁻¹) := by rw [c13K_om_conj_tt hc]

private lemma c13K_conj_rho_pow (hc : Ctx13M t L S x₁ x₂ lam rho tau om) (i : ℕ) (x : G) :
    rho ^ i * (t * x) * (rho ^ i)⁻¹ = t * (rho ^ i * x * (rho ^ i)⁻¹) := by
  have hrt : Commute rho t := (c13K_rho_comm hc).1
  have hpow : Commute (rho ^ i) t := hrt.pow_left i
  calc rho ^ i * (t * x) * (rho ^ i)⁻¹
      = (rho ^ i * t * (rho ^ i)⁻¹) * (rho ^ i * x * (rho ^ i)⁻¹) := by group
    _ = t * (rho ^ i * x * (rho ^ i)⁻¹) := by rw [hpow.eq]; group

private lemma c13K_conj_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {q d v : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hdQ : d ∈ ctxQ t tau x₁ x₂ rho)
    (hcomm : t * q * t * q⁻¹ = v) : q * (t * d) * q⁻¹ = t * (d * v) := by
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← hcomm, c13K_comm_eq_commutatorElement hc q]
    exact c13K_commutatorElement_mem_Q hc hq
  have hdqi : d * q⁻¹ = q⁻¹ * d := hc.Q_comm d hdQ q⁻¹ ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
  have ht2 : t * t = 1 := by
    have h := (c13K_rel hc).1
    rwa [pow_two] at h
  have htq' : q * t * q⁻¹ = t * v := by
    rw [← hcomm]
    rw [show t * (t * q * t * q⁻¹) = q * t * q⁻¹ by
      calc t * (t * q * t * q⁻¹) = (t * t) * (q * t * q⁻¹) := by group
        _ = q * t * q⁻¹ := by rw [ht2, one_mul]]
  calc q * (t * d) * q⁻¹
      = q * t * d * q⁻¹ := by group
    _ = q * t * (d * q⁻¹) := by group
    _ = q * t * (q⁻¹ * d) := by rw [hdqi]
    _ = (q * t * q⁻¹) * d := by group
    _ = (t * v) * d := by rw [htq']
    _ = t * (d * v) := by
          rw [show (t * v) * d = t * (v * d) by group, hc.Q_comm v hvQ d hdQ]

private lemma c13K_orbit_C_aux (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {c c' d v : G}
    (hdC : d ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
    (hvV : v ∈ fourGrp x₁ x₂) (hdv : c' = d * v) (i : ℕ)
    (hd : d = rho ^ i * c * (rho ^ i)⁻¹) :
    ∃ m ∈ ctxM t tau x₁ x₂, m * (t * c) * m⁻¹ = t * c' := by
  obtain ⟨q, hqQ, hqeq⟩ := c13K_comm_t_surj hc v hvV
  have hdQ : rho ^ i * c * (rho ^ i)⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← hd]
    exact hdC.1
  refine ⟨q * rho ^ i, (ctxM t tau x₁ x₂).mul_mem (hc.normal_Q.1 hqQ)
    ((ctxM t tau x₁ x₂).pow_mem (c13K_mem_M hc).2.2.2.1 i), ?_⟩
  calc (q * rho ^ i) * (t * c) * (q * rho ^ i)⁻¹
      = q * (rho ^ i * (t * c) * (rho ^ i)⁻¹) * q⁻¹ := by group
    _ = q * (t * (rho ^ i * c * (rho ^ i)⁻¹)) * q⁻¹ := by rw [c13K_conj_rho_pow hc i c]
    _ = t * ((rho ^ i * c * (rho ^ i)⁻¹) * v) := c13K_conj_Q hc hqQ hdQ hqeq
    _ = t * c' := by rw [← hd, ← hdv]

theorem c13K_orbit_C (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {c c' : G}
    (hc1 : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
    (hc2 : c' ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
    (hcV : c ∉ fourGrp x₁ x₂) (hc'V : c' ∉ fourGrp x₁ x₂) :
    ∃ m ∈ ctxM t tau x₁ x₂, m * (t * c) * m⁻¹ = t * c' := by
  let C : Subgroup G := ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)
  have hcYnot : c ∉ ctxYq t tau x₁ x₂ rho := fun hcY => hcV (c13K_C_inf_Y hc hc1 hcY)
  rcases hc.fpf_QY.cover hc1.1 hcYnot hc2.1 with h | h | h | h
  · exact absurd (c13K_C_inf_Y hc hc2 h) hc'V
  · refine c13K_orbit_C_aux hc (c := c) (c' := c') (d := c) (v := c⁻¹ * c') hc1 ?_ ?_ 0 ?_
    · exact c13K_C_inf_Y hc (C.mul_mem (C.inv_mem hc1) hc2) h
    · group
    · group
  · refine c13K_orbit_C_aux hc (c := c) (c' := c') (d := rho * c * rho⁻¹)
      (v := (rho * c * rho⁻¹)⁻¹ * c') (c13K_rho_conj_mem_C hc hc1) ?_ ?_ 1 ?_
    · exact c13K_C_inf_Y hc
        (C.mul_mem (C.inv_mem (c13K_rho_conj_mem_C hc hc1)) hc2) h
    · group
    · group
  · refine c13K_orbit_C_aux hc (c := c) (c' := c') (d := rho ^ 2 * c * (rho ^ 2)⁻¹)
      (v := (rho ^ 2 * c * (rho ^ 2)⁻¹)⁻¹ * c') (c13K_rho_norm_C hc hc1).2 ?_ ?_ 2 ?_
    · exact c13K_C_inf_Y hc
        (C.mul_mem (C.inv_mem (c13K_rho_norm_C hc hc1).2) hc2) h
    · group
    · group

private lemma c13K_Tp_to_C (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {s : G}
    (hs : s ∈ c13KTp t tau x₁ x₂ rho) (hn : s ∉ conjIn (ctxM t tau x₁ x₂) t) :
    ∃ m ∈ ctxM t tau x₁ x₂, ∃ c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G),
      c ∉ fourGrp x₁ x₂ ∧ m * s * m⁻¹ = t * c := by
  rw [c13K_mem_Tp_iff hc] at hs
  rcases hs with ⟨c, hcC, hs_eq⟩ | ⟨d, hd, hs_eq⟩
  · subst hs_eq
    refine ⟨1, (ctxM t tau x₁ x₂).one_mem, c, hcC, ?_, by group⟩
    intro hcV
    apply hn
    rw [hc.tM]
    exact Or.inl (Set.mem_smul_set.mpr ⟨c, hcV, by rw [smul_eq_mul]⟩)
  · subst hs_eq
    have hdV : d ∉ fourGrp x₁ x₂ := by
      intro hdV
      apply hn
      rw [hc.tM]
      exact Or.inr (Set.mem_smul_set.mpr ⟨d, hdV, by rw [smul_eq_mul]⟩)
    exact c13K_orbit_swap hc hd hdV

theorem c13K_orbit_trans (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {s s' : G}
    (hs : s ∈ c13KTp t tau x₁ x₂ rho) (hs' : s' ∈ c13KTp t tau x₁ x₂ rho)
    (hn : s ∉ conjIn (ctxM t tau x₁ x₂) t) (hn' : s' ∉ conjIn (ctxM t tau x₁ x₂) t) :
    ∃ m ∈ ctxM t tau x₁ x₂, m * s * m⁻¹ = s' := by
  obtain ⟨m₁, hm₁M, c₁, hc₁C, hc₁V, h₁⟩ := c13K_Tp_to_C hc hs hn
  obtain ⟨m₂, hm₂M, c₂, hc₂C, hc₂V, h₂⟩ := c13K_Tp_to_C hc hs' hn'
  obtain ⟨m', hm'M, h'⟩ := c13K_orbit_C hc hc₁C hc₂C hc₁V hc₂V
  refine ⟨m₂⁻¹ * m' * m₁, ?_, ?_⟩
  · exact (ctxM t tau x₁ x₂).mul_mem
      ((ctxM t tau x₁ x₂).mul_mem ((ctxM t tau x₁ x₂).inv_mem hm₂M) hm'M) hm₁M
  · calc (m₂⁻¹ * m' * m₁) * s * (m₂⁻¹ * m' * m₁)⁻¹
        = m₂⁻¹ * (m' * (m₁ * s * m₁⁻¹) * m'⁻¹) * m₂ := by group
      _ = m₂⁻¹ * (m' * (t * c₁) * m'⁻¹) * m₂ := by rw [h₁]
      _ = m₂⁻¹ * (t * c₂) * m₂ := by rw [h']
      _ = s' := by rw [← h₂]; group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
