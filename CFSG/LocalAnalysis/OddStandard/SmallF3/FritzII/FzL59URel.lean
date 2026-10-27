module


public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Dict

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

theorem fz59u_fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

theorem fz59u_mem_R (b : Fin 3 → Fin 2 → G) (i : Fin 3) (k : Fin 2) : b i k ∈ fz59R b :=
  subset_closure ⟨(i, k), rfl⟩

theorem fz59u_cell_mem (b : Fin 3 → Fin 2 → G) (c : Fz59Cell) : fz59CellElt b c ∈ fz59R b := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact fz59u_mem_R b i 0
  · exact fz59u_mem_R b i 1
  · exact mul_mem (fz59u_mem_R b i 0) (fz59u_mem_R b i 1)

theorem fz59u_sq_mem_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 ∈ fz59Z b := by
  have h0 : b 0 0 ^ 2 ∈ fz59Z b := subset_closure (by simp)
  have h1 : b 1 0 ^ 2 ∈ fz59Z b := subset_closure (by simp)
  rcases fz59u_fin3 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · rw [hb.sq_eq]
    exact mul_mem h0 h1

theorem fz59u_Z_sq {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {z : G} (hz : z ∈ fz59Z b) :
    z ^ 2 = 1 := by
  rcases (fz59_mem_Z hb z).1 hz with rfl | rfl | rfl | rfl
  · exact one_pow 2
  all_goals rw [sq]; exact (hb.quat _).sq_mul_sq

theorem fz59u_sq_mul {p q : G} (h : IsQ8Pair p q) : (p * q) ^ 2 = p ^ 2 :=
  h.mul_left.2.1.symm

theorem fz59u_cell_sq {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (c : Fz59Cell) :
    fz59CellElt b c ^ 2 = b c.1 0 ^ 2 := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · rfl
  · exact (hb.quat i).2.1
  · exact fz59u_sq_mul (hb.quat i)

theorem fz59u_sq_mul_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {x z : G} (hx : x ∈ fz59R b)
    (hz : z ∈ fz59Z b) : (x * z) ^ 2 = x ^ 2 := by
  have hc : Commute z x := fz59_Z_central hb z hz x hx
  rw [hc.symm.mul_pow, fz59u_Z_sq hb hz, mul_one]

theorem fz59u_q8_inv {p q : G} (h : IsQ8Pair p q) : IsQ8Pair p q⁻¹ := by
  refine ⟨h.1, ?_, ?_, h.2.2.2⟩
  · rw [inv_pow, h.2.1, inv_eq_of_mul_eq_one_right h.sq_mul_sq]
  · have e : p = q⁻¹ * p⁻¹ * q := by
      rw [← h.2.2.1]
      group
    rw [inv_inv]
    calc q⁻¹ * p * q = (q⁻¹ * p⁻¹ * q)⁻¹ := by group
      _ = p⁻¹ := by rw [← e]

theorem fz59u_q8_mul {p q : G} (h : IsQ8Pair p q) : IsQ8Pair p (p * q) := by
  refine ⟨h.1, fz59u_sq_mul h, ?_, h.2.2.2⟩
  calc p * q * p * (p * q)⁻¹ = p * (q * p * q⁻¹) * p⁻¹ := by group
    _ = p⁻¹ := by rw [h.2.2.1]; group

theorem fz59u_diag_sq {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (k : Fin 2) :
    (b 0 k * b 1 k * b 2 k) ^ 2 = 1 := by
  have hk : ∀ i, b i k ^ 2 = b i 0 ^ 2 := by
    intro i
    fin_cases k
    · rfl
    · exact (hb.quat i).2.1
  rw [((hb.comm 0 2 (by decide) k k).mul_left (hb.comm 1 2 (by decide) k k)).mul_pow,
    (hb.comm 0 1 (by decide) k k).mul_pow, hk, hk, hk, ← hb.sq_eq]
  exact (hb.quat 2).sq_mul_sq

theorem fz59u_t_sq {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    t ^ 2 = 1 := by
  rw [h.t_eq]
  exact fz59u_diag_sq h.rows 0

theorem fz59u_s_sq {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    s ^ 2 = 1 := by
  rw [h.s_eq]
  exact fz59u_diag_sq h.rows 1

theorem fz59u_inv_eq {x : G} (h : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h)

theorem fz59u_t_mem {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    t ∈ fz59R b := by
  rw [h.t_eq]
  exact mul_mem (mul_mem (fz59u_mem_R b 0 0) (fz59u_mem_R b 1 0)) (fz59u_mem_R b 2 0)

theorem fz59u_s_mem {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    s ∈ fz59R b := by
  rw [h.s_eq]
  exact mul_mem (mul_mem (fz59u_mem_R b 0 1) (fz59u_mem_R b 1 1)) (fz59u_mem_R b 2 1)

theorem fz59u_rev {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    b 2 1 * (b 1 1 * b 0 1) = b 0 1 * b 1 1 * b 2 1 := by
  rw [← (hb.comm 0 1 (by decide) 1 1).eq]
  exact ((hb.comm 2 0 (by decide) 1 1).mul_right (hb.comm 2 1 (by decide) 1 1)).eq

theorem fz59u_s_b00 {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    s * b 0 0 * s⁻¹ = (b 0 0)⁻¹ := by
  have hb := h.rows
  have hc : Commute (b 1 1 * b 2 1) (b 0 0) :=
    (hb.comm 1 0 (by decide) 1 0).mul_left (hb.comm 2 0 (by decide) 1 0)
  rw [h.s_eq]
  calc b 0 1 * b 1 1 * b 2 1 * b 0 0 * (b 0 1 * b 1 1 * b 2 1)⁻¹ =
      b 0 1 * ((b 1 1 * b 2 1) * b 0 0 * (b 1 1 * b 2 1)⁻¹) * (b 0 1)⁻¹ := by group
    _ = b 0 1 * b 0 0 * (b 0 1)⁻¹ := by rw [hc.eq]; group
    _ = (b 0 0)⁻¹ := (hb.quat 0).2.2.1

theorem fz59u_s_b01 {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    s * b 0 1 * s⁻¹ = b 0 1 := by
  have hb := h.rows
  have hc : Commute s (b 0 1) := by
    rw [h.s_eq]
    exact ((Commute.refl _).mul_left (hb.comm 1 0 (by decide) 1 1)).mul_left
      (hb.comm 2 0 (by decide) 1 1)
  rw [hc.eq, mul_inv_cancel_right]

theorem fz59u_lam_1 {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b)
    (k : Fin 2) : lam * b 1 k * lam⁻¹ = b 0 k := by
  have hl : lam * lam = 1 := by rw [← sq]; exact h.lam_sq
  rw [← h.lam_01 k]
  calc lam * (lam * b 0 k * lam⁻¹) * lam⁻¹ = (lam * lam) * b 0 k * (lam * lam)⁻¹ := by group
    _ = b 0 k := by rw [hl]; group

theorem fz59u_z_mul {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 * b (i - 1) 0 ^ 2 = b (i + 1) 0 ^ 2 := by
  have h01 : Commute (b 0 0 ^ 2) (b 1 0 ^ 2) :=
    ((hb.comm 0 1 (by decide) 0 0).pow_left 2).pow_right 2
  rcases fz59u_fin3 i with rfl | rfl | rfl
  · show b 0 0 ^ 2 * b 2 0 ^ 2 = b 1 0 ^ 2
    rw [hb.sq_eq, ← mul_assoc, (hb.quat 0).sq_mul_sq, one_mul]
  · show b 1 0 ^ 2 * b 0 0 ^ 2 = b 2 0 ^ 2
    rw [hb.sq_eq, h01.eq]
  · show b 2 0 ^ 2 * b 1 0 ^ 2 = b 0 0 ^ 2
    rw [hb.sq_eq, mul_assoc, (hb.quat 1).sq_mul_sq, mul_one]

theorem fz59u_R_eq {b b' : Fin 3 → Fin 2 → G} (h1 : ∀ i k, b' i k ∈ fz59R b)
    (h2 : ∀ i k, b i k ∈ fz59R b') : fz59R b' = fz59R b := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact h1 i k
  · refine (closure_le _).mpr ?_
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact h2 i k

theorem fz59u_tr_inj {ω ω' : Fin 3 → Fin 3} (h : fz59Tr ω = fz59Tr ω') : ω = ω' := by
  funext i
  have hi : (i, ω i) ∈ fz59Tr ω' := by
    rw [← h]
    simp [fz59Tr]
  simp [fz59Tr] at hi
  exact hi.symm

@[expose] def fz59uInv (b : Fin 3 → Fin 2 → G) : Fin 3 → Fin 2 → G :=
  fun i => ![b i 0, (b i 1)⁻¹]

@[expose] def fz59uRel (b : Fin 3 → Fin 2 → G) : Fin 3 → Fin 2 → G :=
  fun i => ![b i 0, b i 0 * b i 1]

theorem fz59u_frame_inv {t tau lam rho x₁ x₂ s : G} {b : Fin 3 → Fin 2 → G}
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) : Fz59Frame t tau lam rho x₁ x₂ s (fz59uInv b) := by
  have hb := hF.grid.rows
  have hR : fz59R (fz59uInv b) = fz59R b := by
    refine fz59u_R_eq (fun i k => ?_) (fun i k => ?_)
    · fin_cases k
      · exact fz59u_mem_R b i 0
      · exact inv_mem (fz59u_mem_R b i 1)
    · fin_cases k
      · exact fz59u_mem_R (fz59uInv b) i 0
      · have := inv_mem (fz59u_mem_R (fz59uInv b) i 1)
        simpa [fz59uInv] using this
  refine ⟨⟨fun i => fz59u_q8_inv (hF.grid.quat i), hF.grid.sq_eq, ?_, hF.grid.t_eq, ?_,
    hF.grid.lam_sq, ?_, ?_, hF.grid.rho_ord, ?_, hF.grid.lam_rho⟩, hF.s_cases,
    hF.hR.trans hR.symm, hF.hZ, hF.z3, hF.hW, hF.hE⟩
  · intro i j hij k l
    have h := hF.grid.comm i j hij
    fin_cases k <;> fin_cases l
    · exact h 0 0
    · exact (h 0 1).inv_right
    · exact (h 1 0).inv_left
    · exact (h 1 1).inv_left.inv_right
  · show s = (b 0 1)⁻¹ * (b 1 1)⁻¹ * (b 2 1)⁻¹
    calc s = s⁻¹ := (fz59u_inv_eq (fz59u_s_sq hF.grid)).symm
      _ = (b 0 1 * b 1 1 * b 2 1)⁻¹ := by rw [hF.grid.s_eq]
      _ = (b 2 1 * (b 1 1 * b 0 1))⁻¹ := by rw [fz59u_rev hb]
      _ = (b 0 1)⁻¹ * (b 1 1)⁻¹ * (b 2 1)⁻¹ := by group
  · intro k
    fin_cases k
    · exact hF.grid.lam_01 0
    · show lam * (b 0 1)⁻¹ * lam⁻¹ = (b 1 1)⁻¹
      rw [← conj_inv, hF.grid.lam_01]
  · intro k
    fin_cases k
    · exact hF.grid.lam_2 0
    · show lam * (b 2 1)⁻¹ * lam⁻¹ = (b 2 1)⁻¹
      rw [← conj_inv, hF.grid.lam_2]
  · intro i k
    fin_cases k
    · exact hF.grid.rho_b i 0
    · show rho * (b i 1)⁻¹ * rho⁻¹ = (b (i + 1) 1)⁻¹
      rw [← conj_inv, hF.grid.rho_b]

theorem fz59u_R_rel (b : Fin 3 → Fin 2 → G) : fz59R (fz59uRel b) = fz59R b := by
  refine fz59u_R_eq (fun i k => ?_) (fun i k => ?_)
  · fin_cases k
    · exact fz59u_mem_R b i 0
    · exact mul_mem (fz59u_mem_R b i 0) (fz59u_mem_R b i 1)
  · fin_cases k
    · exact fz59u_mem_R (fz59uRel b) i 0
    · have := mul_mem (inv_mem (fz59u_mem_R (fz59uRel b) i 0)) (fz59u_mem_R (fz59uRel b) i 1)
      simpa [fz59uRel] using this

theorem fz59u_frame_rel {t tau lam rho x₁ x₂ s : G} {b : Fin 3 → Fin 2 → G}
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) :
    Fz59Frame t tau lam rho x₁ x₂ (t * s) (fz59uRel b) := by
  have hb := hF.grid.rows
  refine ⟨⟨fun i => fz59u_q8_mul (hF.grid.quat i), hF.grid.sq_eq, ?_, hF.grid.t_eq, ?_,
    hF.grid.lam_sq, ?_, ?_, hF.grid.rho_ord, ?_, hF.grid.lam_rho⟩, ?_,
    hF.hR.trans (fz59u_R_rel b).symm, hF.hZ, hF.z3, hF.hW, hF.hE⟩
  · intro i j hij k l
    have h := hF.grid.comm i j hij
    fin_cases k <;> fin_cases l
    · exact h 0 0
    · exact (h 0 0).mul_right (h 0 1)
    · exact (h 0 0).mul_left (h 1 0)
    · exact ((h 0 0).mul_right (h 0 1)).mul_left ((h 1 0).mul_right (h 1 1))
  · show t * s = b 0 0 * b 0 1 * (b 1 0 * b 1 1) * (b 2 0 * b 2 1)
    have c1 : Commute (b 1 0 * b 2 0) (b 0 1) :=
      (hb.comm 1 0 (by decide) 0 1).mul_left (hb.comm 2 0 (by decide) 0 1)
    have c2 : Commute (b 2 0) (b 1 1) := hb.comm 2 1 (by decide) 0 1
    rw [hF.grid.t_eq, hF.grid.s_eq]
    calc b 0 0 * b 1 0 * b 2 0 * (b 0 1 * b 1 1 * b 2 1) =
        b 0 0 * ((b 1 0 * b 2 0) * b 0 1) * b 1 1 * b 2 1 := by group
      _ = b 0 0 * (b 0 1 * (b 1 0 * b 2 0)) * b 1 1 * b 2 1 := by rw [c1.eq]
      _ = b 0 0 * b 0 1 * b 1 0 * (b 2 0 * b 1 1) * b 2 1 := by group
      _ = b 0 0 * b 0 1 * b 1 0 * (b 1 1 * b 2 0) * b 2 1 := by rw [c2.eq]
      _ = b 0 0 * b 0 1 * (b 1 0 * b 1 1) * (b 2 0 * b 2 1) := by group
  · intro k
    fin_cases k
    · exact hF.grid.lam_01 0
    · show lam * (b 0 0 * b 0 1) * lam⁻¹ = b 1 0 * b 1 1
      calc lam * (b 0 0 * b 0 1) * lam⁻¹ = (lam * b 0 0 * lam⁻¹) * (lam * b 0 1 * lam⁻¹) := by
            group
        _ = b 1 0 * b 1 1 := by rw [hF.grid.lam_01 0, hF.grid.lam_01 1]
  · intro k
    fin_cases k
    · exact hF.grid.lam_2 0
    · show lam * (b 2 0 * b 2 1) * lam⁻¹ = b 2 0 * b 2 1
      calc lam * (b 2 0 * b 2 1) * lam⁻¹ = (lam * b 2 0 * lam⁻¹) * (lam * b 2 1 * lam⁻¹) := by
            group
        _ = b 2 0 * b 2 1 := by rw [hF.grid.lam_2 0, hF.grid.lam_2 1]
  · intro i k
    fin_cases k
    · exact hF.grid.rho_b i 0
    · show rho * (b i 0 * b i 1) * rho⁻¹ = b (i + 1) 0 * b (i + 1) 1
      calc rho * (b i 0 * b i 1) * rho⁻¹ = (rho * b i 0 * rho⁻¹) * (rho * b i 1 * rho⁻¹) := by
            group
        _ = b (i + 1) 0 * b (i + 1) 1 := by rw [hF.grid.rho_b i 0, hF.grid.rho_b i 1]
  · have ht : t * t = 1 := by rw [← sq]; exact fz59u_t_sq hF.grid
    rcases hF.s_cases with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, ← mul_assoc, ht, one_mul])

theorem fz59u_nrm_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G)) :
    ∀ w ∈ fz59Z b, (n : G) * w * (n : G)⁻¹ ∈ fz59Z b := by
  have hz : ∀ i, (n : G) * b i 0 ^ 2 * (n : G)⁻¹ ∈ fz59Z b := by
    intro i
    obtain ⟨z, hz, he⟩ := hΦ.1 n (i, 0)
    rw [← conj_pow]
    change (n : G) * b i 0 * (n : G)⁻¹ = _ at he
    rw [he, fz59u_sq_mul_Z hb (fz59u_cell_mem b _) hz, fz59u_cell_sq hb]
    exact fz59u_sq_mem_Z hb _
  intro w hw
  rcases (fz59_mem_Z hb w).1 hw with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  all_goals exact hz _

theorem fz59u_cell_rel {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (c : Fz59Cell) :
    ∃ w ∈ fz59Z b, fz59CellElt (fz59uRel b) c =
      fz59CellElt b (fz59ColPerm (Equiv.swap 1 2) c) * w := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact ⟨1, one_mem _, (mul_one _).symm⟩
  · exact ⟨1, one_mem _, (mul_one _).symm⟩
  · refine ⟨b i 0 ^ 2, fz59u_sq_mem_Z hb i, ?_⟩
    show b i 0 * (b i 0 * b i 1) = b i 1 * b i 0 ^ 2
    rw [(hb.quat i).mul_comm_sq, ← mul_assoc, ← sq]

theorem fz59u_phi_rel {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b)
    (hg : fz59ColPerm (Equiv.swap 0 1) ∈ Φ.range) :
    ∃ Φ' : normalizer ((fz59R (fz59uRel b) : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell,
      Fz59CellAction (fz59uRel b) Φ' ∧ (∀ n, Φ' n = 1 ↔ (n : G) ∈ fz59R (fz59uRel b)) ∧
      fz59ColPerm (Equiv.swap 0 2) ∈ Φ'.range := by
  have hR := fz59u_R_rel b
  have hle : normalizer ((fz59R (fz59uRel b) : Subgroup G) : Set G) ≤
      normalizer ((fz59R b : Subgroup G) : Set G) := by rw [hR]
  set κ : Equiv.Perm Fz59Cell := fz59ColPerm (Equiv.swap 1 2) with hκ
  have hκκ : κ⁻¹ = κ := by rw [hκ]; decide
  have hκ2 : ∀ c, κ (κ c) = c := by rw [hκ]; decide
  have hκ1 : ∀ c : Fz59Cell, (κ c).1 = c.1 := fun c => rfl
  let Φ' := (MulAut.conj κ).toMonoidHom.comp (Φ.comp (Subgroup.inclusion hle))
  have hΦ' : ∀ n c, Φ' n c = κ (Φ (Subgroup.inclusion hle n) (κ c)) := by
    intro n c
    show (κ * Φ (Subgroup.inclusion hle n) * κ⁻¹) c = _
    rw [hκκ]
    rfl
  refine ⟨Φ', ⟨fun n c => ?_, fun n i k k' => ?_⟩, fun n => ?_, ?_⟩
  · obtain ⟨w, hw, hc⟩ := fz59u_cell_rel hb c
    obtain ⟨z, hz, he⟩ := hΦ.1 (Subgroup.inclusion hle n) (κ c)
    obtain ⟨w', hw', hc'⟩ := fz59u_cell_rel hb (Φ' n c)
    rw [← hκ] at hc hc'
    have hκd : κ (Φ' n c) = Φ (Subgroup.inclusion hle n) (κ c) := by
      rw [hΦ', hκ2]
    rw [hκd] at hc'
    have hn : ((Subgroup.inclusion hle n : normalizer ((fz59R b : Subgroup G) : Set G)) : G) =
        (n : G) := rfl
    rw [hn] at he
    refine ⟨w'⁻¹ * z * ((n : G) * w * (n : G)⁻¹),
      mul_mem (mul_mem (inv_mem hw') hz) (fz59u_nrm_Z hb hΦ (Subgroup.inclusion hle n) w hw), ?_⟩
    have e1 : fz59CellElt b (Φ (Subgroup.inclusion hle n) (κ c)) =
        fz59CellElt (fz59uRel b) (Φ' n c) * w'⁻¹ := by
      rw [hc', mul_inv_cancel_right]
    calc (n : G) * fz59CellElt (fz59uRel b) c * (n : G)⁻¹ =
        ((n : G) * fz59CellElt b (κ c) * (n : G)⁻¹) * ((n : G) * w * (n : G)⁻¹) := by
          rw [hc]; group
      _ = fz59CellElt (fz59uRel b) (Φ' n c) * (w'⁻¹ * z * ((n : G) * w * (n : G)⁻¹)) := by
          rw [he, e1]; group
  · rw [hΦ', hΦ', hκ1, hκ1]
    exact hΦ.2 _ i _ _
  · show κ * Φ (Subgroup.inclusion hle n) * κ⁻¹ = 1 ↔ _
    have hmem : ∀ x : G, x ∈ fz59R b ↔ x ∈ fz59R (fz59uRel b) := fun x => by rw [hR]
    rw [conj_eq_one_iff, hker]
    exact hmem _
  · obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hg
    refine MonoidHom.mem_range.mpr ⟨⟨n, by rw [hR]; exact n.2⟩, ?_⟩
    show κ * Φ (Subgroup.inclusion hle ⟨n, _⟩) * κ⁻¹ = _
    have : Subgroup.inclusion hle ⟨(n : G), by rw [hR]; exact n.2⟩ = n := rfl
    rw [this, hn, hκ]
    decide

end CFSG.OddStandard.SmallF3.FritzII
