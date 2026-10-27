module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59CB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Crit

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open scoped Pointwise

variable {G : Type} [Group G]

theorem fz59cls_nrm [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) {n : G} (hn : n ∈ fzN2 t x₁ x₂) :
    n ∈ normalizer ((fz59R b : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← hF.hR]
  constructor
  · exact hB.N2_nrm_R n hn h
  · intro hh
    have h2 := hB.N2_nrm_R n⁻¹ ((fzN2 t x₁ x₂).inv_mem hn) _ hh
    have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
    rwa [e] at h2

theorem fz59cls_cell_conj {b : Fin 3 → Fin 2 → G} {g : G} {f : Fin 3 → Fin 3}
    (hg : ∀ (i : Fin 3) (k : Fin 2), g * b i k * g⁻¹ = b (f i) k) (i k : Fin 3) :
    g * fz59CellElt b (i, k) * g⁻¹ = fz59CellElt b (f i, k) := by
  fin_cases k
  · exact hg i 0
  · exact hg i 1
  · show g * (b i 0 * b i 1) * g⁻¹ = b (f i) 0 * b (f i) 1
    rw [← hg i 0, ← hg i 1]
    group

theorem fz59cls_rho [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) :
    ∃ h : rho ∈ normalizer ((fz59R b : Subgroup G) : Set G), Φ ⟨rho, h⟩ = fz59RowRot := by
  have h : rho ∈ normalizer ((fz59R b : Subgroup G) : Set G) := fz59cls_nrm hB hF hB.rho_N2
  refine ⟨h, fz59_phi_unique hF.grid.rows hΦ ⟨rho, h⟩ fz59RowRot fun c => ⟨1, one_mem _, ?_⟩⟩
  obtain ⟨i, k⟩ := c
  rw [mul_one]
  exact fz59cls_cell_conj (f := fun i => i + 1) hF.grid.rho_b i k

theorem fz59cls_lam [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) :
    ∃ h : lam ∈ normalizer ((fz59R b : Subgroup G) : Set G), Φ ⟨lam, h⟩ = fz59RowSwap := by
  have hlam : lam ∈ fzN2 t x₁ x₂ := by
    apply hB.T2_le
    rw [hB.shape.gen]
    exact Subgroup.subset_closure (by simp)
  have h : lam ∈ normalizer ((fz59R b : Subgroup G) : Set G) := fz59cls_nrm hB hF hlam
  refine ⟨h, fz59_phi_unique hF.grid.rows hΦ ⟨lam, h⟩ fz59RowSwap fun c => ⟨1, one_mem _, ?_⟩⟩
  obtain ⟨i, k⟩ := c
  rw [mul_one]
  refine fz59cls_cell_conj (f := Equiv.swap (0 : Fin 3) 1) ?_ i k
  intro i k
  have hsq : lam * lam = 1 := by rw [← pow_two]; exact hF.grid.lam_sq
  have h1 : lam * b 0 k * lam⁻¹ = b 1 k := hF.grid.lam_01 k
  have h2 : lam * b 1 k * lam⁻¹ = b 0 k := by
    rw [← h1]
    calc lam * (lam * b 0 k * lam⁻¹) * lam⁻¹ = (lam * lam) * b 0 k * (lam * lam)⁻¹ := by group
      _ = b 0 k := by rw [hsq]; group
  have hs0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have hs1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have hs2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  fin_cases i
  · show lam * b 0 k * lam⁻¹ = b ((Equiv.swap (0 : Fin 3) 1) 0) k
    rw [hs0]
    exact h1
  · show lam * b 1 k * lam⁻¹ = b ((Equiv.swap (0 : Fin 3) 1) 1) k
    rw [hs1]
    exact h2
  · show lam * b 2 k * lam⁻¹ = b ((Equiv.swap (0 : Fin 3) 1) 2) k
    rw [hs2]
    exact hF.grid.lam_2 k

theorem fz59cls_col0 [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G))
    (hn : ∀ i, Φ n (i, 0) = (i, 0)) : (n : G) ∈ fz59R b := by
  have hb := hF.grid.rows
  have hZW : fz59Z b ≤ closure (Set.range fun i => b i 0) := by
    rw [fz59Z, Subgroup.closure_le]
    have h0 : b 0 0 ∈ closure (Set.range fun i => b i 0) := Subgroup.subset_closure ⟨0, rfl⟩
    have h1 : b 1 0 ∈ closure (Set.range fun i => b i 0) := Subgroup.subset_closure ⟨1, rfl⟩
    rintro _ (rfl | rfl)
    · exact pow_mem h0 2
    · exact pow_mem h1 2
  have hconjW : ∀ m : normalizer ((fz59R b : Subgroup G) : Set G), (∀ i, Φ m (i, 0) = (i, 0)) →
      ∀ x ∈ closure (Set.range fun i => b i 0),
        (m : G) * x * (m : G)⁻¹ ∈ closure (Set.range fun i => b i 0) := by
    intro m hm
    have hle : closure (Set.range fun i => b i 0) ≤
        (closure (Set.range fun i => b i 0)).comap (MulAut.conj (m : G)).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨w, hw, h⟩ := hΦ.1 m (i, 0)
      rw [hm i] at h
      have h' : (m : G) * b i 0 * (m : G)⁻¹ = b i 0 * w := h
      show (MulAut.conj (m : G)) (b i 0) ∈ closure (Set.range fun i => b i 0)
      rw [MulAut.conj_apply, h']
      exact mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) (hZW hw)
    intro x hx
    exact hle hx
  have hninv : ∀ i, Φ n⁻¹ (i, 0) = (i, 0) := by
    intro i
    rw [map_inv]
    exact Equiv.Perm.inv_eq_iff_eq.mpr (hn i).symm
  have hnN2 : (n : G) ∈ fzN2 t x₁ x₂ := by
    show (n : G) ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hF.hW]
    constructor
    · exact hconjW n hn x
    · intro hx
      have := hconjW n⁻¹ hninv _ hx
      have e : ((n⁻¹ : normalizer ((fz59R b : Subgroup G) : Set G)) : G) *
          ((n : G) * x * (n : G)⁻¹) * ((n⁻¹ : normalizer ((fz59R b : Subgroup G) : Set G)) : G)⁻¹
          = x := by
        simp [mul_assoc]
      rwa [e] at this
  have hcz : ∀ z ∈ fourGrp x₁ x₂, (n : G) * z * (n : G)⁻¹ = z := by
    intro z hz
    rw [hF.hZ, fz59_mem_Z hb] at hz
    have key : ∀ i, (n : G) * b i 0 ^ 2 * (n : G)⁻¹ = b i 0 ^ 2 := by
      intro i
      obtain ⟨w, hw, h⟩ := hΦ.1 n (i, 0)
      rw [hn i] at h
      have h' : (n : G) * b i 0 * (n : G)⁻¹ = b i 0 * w := h
      have hxw : Commute (b i 0) w :=
        (fz59_Z_central hb w hw _ (Subgroup.subset_closure ⟨(i, 0), rfl⟩)).symm
      rw [← conj_pow, h', hxw.mul_pow, fz59crit_Z_sq hb hw, mul_one]
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · exact key 0
    · exact key 1
    · exact key 2
  have hnR := hB.cz _ hnN2 hcz
  rw [hF.hR] at hnR
  exact hnR

theorem fz59cls_fus [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) (hs2 : s ^ 2 = 1)
    (hcases : s = tau ∨ s = t * tau) :
    ∀ e ∈ baseGrp x₁ x₂, IsConj s (e * s) ∧ IsConj (t * s) (e * (t * s)) := by
  have ht2 : t ^ 2 = 1 := hB.str.t_sq
  have hct : Commute tau t := mul_inv_eq_iff_eq_mul.mp hB.str.tau_t
  have htau2 : tau ^ 2 = 1 := by
    rcases hcases with rfl | rfl
    · exact hs2
    · rw [hct.symm.mul_pow, ht2, one_mul] at hs2
      exact hs2
  have hf := hB.fus htau2
  intro e he
  rcases hcases with rfl | rfl
  · exact hf e he
  · have h1 : t * (t * tau) = tau := by
      rw [← mul_assoc, ← pow_two, ht2, one_mul]
    rw [h1]
    exact ⟨(hf e he).2, (hf e he).1⟩

theorem fz59cls_prod_model {b : Fin 3 → Fin 2 → G} {π : Fz59Mod →* G}
    (hπg : ∀ i k, π (fz59Gen i k) = b i k) (ω : Fin 3 → Fin 3) :
    π (fz59Prod fz59Gen ω) = fz59Prod b ω := by
  have hc : ∀ c : Fz59Cell, π (fz59CellElt fz59Gen c) = fz59CellElt b c := by
    rintro ⟨i, k⟩
    fin_cases k <;> simp [fz59CellElt, hπg, map_mul]
  simp only [fz59Prod, map_mul, hc]

theorem fz59cls_ident {b : Fin 3 → Fin 2 → G} {π : Fz59Mod →* G}
    (hπg : ∀ i k, π (fz59Gen i k) = b i k)
    (hπk : ∀ q q' : Fz59Mod, π q = π q' ↔ (q' = q ∨ q' = q * fz59Zeta)) {t s : G}
    (ht : t = b 0 0 * b 1 0 * b 2 0) (hs : s = b 0 1 * b 1 1 * b 2 1) :
    s ^ 2 = 1 ∧ fz59Prod b ![1, 1, 1] = s ∧
    fz59Prod b ![1, 2, 2] = ((b 1 0 * t) * (b 2 0 * t)) * s ∧
    fz59Prod b ![2, 1, 2] = ((b 0 0 * t) * (b 2 0 * t)) * s ∧
    fz59Prod b ![2, 2, 1] = ((b 0 0 * t) * (b 1 0 * t)) * s ∧
    fz59Prod b ![2, 2, 2] = t * s ∧
    fz59Prod b ![2, 1, 1] = (b 0 0 * t) * (t * s) ∧
    fz59Prod b ![1, 2, 1] = (b 1 0 * t) * (t * s) ∧
    fz59Prod b ![1, 1, 2] = (b 2 0 * t) * (t * s) := by
  subst ht hs
  have hP := fz59cls_prod_model hπg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have key := (hπk ((fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1) *
      (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1)) 1).mpr (by decide +kernel)
    simp only [map_mul, hπg, map_one] at key
    rwa [pow_two]
  · simp [fz59Prod, fz59CellElt]
  · have key := (hπk (fz59Prod fz59Gen ![1, 2, 2])
      (((fz59Gen 1 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        (fz59Gen 2 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0))) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![2, 1, 2])
      (((fz59Gen 0 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        (fz59Gen 2 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0))) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![2, 2, 1])
      (((fz59Gen 0 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        (fz59Gen 1 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0))) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![2, 2, 2])
      ((fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![2, 1, 1])
      ((fz59Gen 0 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        ((fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1)))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![1, 2, 1])
      ((fz59Gen 1 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        ((fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1)))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key
  · have key := (hπk (fz59Prod fz59Gen ![1, 1, 2])
      ((fz59Gen 2 0 * (fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0)) *
        ((fz59Gen 0 0 * fz59Gen 1 0 * fz59Gen 2 0) *
        (fz59Gen 0 1 * fz59Gen 1 1 * fz59Gen 2 1)))).mpr (by decide +kernel)
    simpa only [map_mul, hπg, hP] using key

theorem fz59cls_fusion [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) :
    ∀ p ∈ fz59FusPairs, ((∃ z ∈ fz59Z b, IsConj t (fz59Prod b p.1 * z)) ↔
      ∃ z ∈ fz59Z b, IsConj t (fz59Prod b p.2 * z)) := by
  have hb := hF.grid.rows
  obtain ⟨π, hπg, -, hπk⟩ := fz59_dict hb
  obtain ⟨hs2, I1, I2, I3, I4, I5, I6, I7, I8⟩ :=
    fz59cls_ident hπg hπk hF.grid.t_eq hF.grid.s_eq
  have hfus := fz59cls_fus hB hs2 hF.s_cases
  have hc : ∀ i, b i 0 * t ∈ baseGrp x₁ x₂ := fun i => by
    rw [hF.hE]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hZE : fz59Z b ≤ baseGrp x₁ x₂ := by
    rw [← hF.hZ]
    exact hB.str.ZE
  have hPR : ∀ ω, fz59Prod b ω ∈ fz59R b := fun ω =>
    mul_mem (mul_mem (fz59crit_cell_mem_R b _) (fz59crit_cell_mem_R b _))
      (fz59crit_cell_mem_R b _)
  have hsR : s ∈ fz59R b := by
    rw [← I1]
    exact hPR _
  have htsR : t * s ∈ fz59R b := by
    rw [← I5]
    exact hPR _
  have hconj1 : ∀ ω, ∀ e ∈ baseGrp x₁ x₂, fz59Prod b ω = e * s →
      ∀ z ∈ fz59Z b, IsConj s (fz59Prod b ω * z) := by
    intro ω e he hP z hz
    have hsz : s * z = z * s := (fz59_Z_central hb z hz s hsR).symm
    have : fz59Prod b ω * z = (e * z) * s := by rw [hP, mul_assoc, hsz, ← mul_assoc]
    rw [this]
    exact (hfus (e * z) ((baseGrp x₁ x₂).mul_mem he (hZE hz))).1
  have hconj2 : ∀ ω, ∀ e ∈ baseGrp x₁ x₂, fz59Prod b ω = e * (t * s) →
      ∀ z ∈ fz59Z b, IsConj (t * s) (fz59Prod b ω * z) := by
    intro ω e he hP z hz
    have hsz : (t * s) * z = z * (t * s) := (fz59_Z_central hb z hz _ htsR).symm
    have : fz59Prod b ω * z = (e * z) * (t * s) := by rw [hP, mul_assoc, hsz, ← mul_assoc]
    rw [this]
    exact (hfus (e * z) ((baseGrp x₁ x₂).mul_mem he (hZE hz))).2
  have hC : ∀ (ω : Fin 3 → Fin 3) (a : G), (∀ z ∈ fz59Z b, IsConj a (fz59Prod b ω * z)) →
      ((∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)) ↔ IsConj t a) := by
    intro ω a h
    constructor
    · rintro ⟨z, hz, hzc⟩
      exact hzc.trans (h z hz).symm
    · intro hta
      refine ⟨1, one_mem _, ?_⟩
      rw [mul_one]
      exact hta.trans (by simpa using h 1 (one_mem _))
  have hsC : ∀ ω ∈ ({![1, 1, 1], ![1, 2, 2], ![2, 1, 2], ![2, 2, 1]} : Set (Fin 3 → Fin 3)),
      ((∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)) ↔ IsConj t s) := by
    intro ω hω
    refine hC ω s ?_
    rcases hω with rfl | rfl | rfl | rfl
    · exact hconj1 _ 1 (one_mem _) (by rw [I1, one_mul])
    · exact hconj1 _ _ ((baseGrp x₁ x₂).mul_mem (hc 1) (hc 2)) I2
    · exact hconj1 _ _ ((baseGrp x₁ x₂).mul_mem (hc 0) (hc 2)) I3
    · exact hconj1 _ _ ((baseGrp x₁ x₂).mul_mem (hc 0) (hc 1)) I4
  have htsC : ∀ ω ∈ ({![2, 2, 2], ![2, 1, 1], ![1, 2, 1], ![1, 1, 2]} : Set (Fin 3 → Fin 3)),
      ((∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)) ↔ IsConj t (t * s)) := by
    intro ω hω
    refine hC ω (t * s) ?_
    rcases hω with rfl | rfl | rfl | rfl
    · exact hconj2 _ 1 (one_mem _) (by rw [I5, one_mul])
    · exact hconj2 _ _ (hc 0) I6
    · exact hconj2 _ _ (hc 1) I7
    · exact hconj2 _ _ (hc 2) I8
  intro p hp
  simp only [fz59FusPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hsC _ (by simp)).trans (hsC _ (by simp)).symm
  · exact (hsC _ (by simp)).trans (hsC _ (by simp)).symm
  · exact (hsC _ (by simp)).trans (hsC _ (by simp)).symm
  · exact (htsC _ (by simp)).trans (htsC _ (by simp)).symm
  · exact (htsC _ (by simp)).trans (htsC _ (by simp)).symm
  · exact (htsC _ (by simp)).trans (htsC _ (by simp)).symm

theorem fz59_classify [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) :
    ∃ Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell,
      Fz59CellAction b Φ ∧ (∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b) ∧ Nat.card Φ.range = 12 ∧
      ∃ σ : Equiv.Perm (Fin 3), (σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 0 1) ∧
        fz59ColPerm σ ∈ Φ.range := by
  have hb : Fz59Rows b := hF.grid.rows
  obtain ⟨Φ, hΦ⟩ := fz59_phi hb
  have hkerΦ : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b := by
    intro n
    constructor
    · intro h
      exact fz59cls_col0 hB hF hΦ n (fun i => by rw [h]; rfl)
    · exact fz59_phi_one_of_mem hb hΦ n
  refine ⟨Φ, hΦ, hkerΦ, ?_⟩
  obtain ⟨hρ, hΦρ⟩ := fz59cls_rho hB hF hΦ
  obtain ⟨hlam, hΦlam⟩ := fz59cls_lam hB hF hΦ
  have hcardN3 : 2 ^ 8 * Nat.card Φ.range = Nat.card (fz59N3 t x₁ x₂) := by
    have h3 := Subgroup.card_ker_mul_card_range Φ
    have e : fz59N3 t x₁ x₂ = normalizer ((fz59R b : Subgroup G) : Set G) := by
      unfold fz59N3
      rw [hF.hR]
    rw [e, ← h3, fz59_card_ker hb hΦ (fun n hn => (hkerΦ n).mp hn)]
  have h4 : 4 ∣ Nat.card Φ.range := by
    have h := hB.even
    rw [← hcardN3, show (2 : ℕ) ^ 10 = 2 ^ 8 * 4 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have h8 : ¬ 8 ∣ Nat.card Φ.range := by
    intro h
    apply hB.bound
    have h1 : 2 ^ 11 ∣ Nat.card (fz59N3 t x₁ x₂) := by
      rw [← hcardN3, show (2 : ℕ) ^ 11 = 2 ^ 8 * 8 by norm_num]
      exact Nat.mul_dvd_mul_left _ h
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  have h0 : (fun _ => (0 : Fin 3)) ∈ {ω : Fin 3 → Fin 3 |
      ∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)} :=
    ⟨1, one_mem _, by
      rw [mul_one]
      have e : fz59Prod b (fun _ => (0 : Fin 3)) = t := hF.grid.t_eq.symm
      rw [e]⟩
  have hN : ∀ g ∈ Φ.range, ∀ ω ∈ {ω : Fin 3 → Fin 3 |
      ∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)}, ∀ ω' : Fin 3 → Fin 3,
      (fz59Tr ω).image g = fz59Tr ω' → ω' ∈ {ω : Fin 3 → Fin 3 |
      ∃ z ∈ fz59Z b, IsConj t (fz59Prod b ω * z)} := by
    rintro _ ⟨n, rfl⟩ ω ⟨z, hz, hconj⟩ ω' himg
    obtain ⟨ω₁, z₁, hz₁, hP, himg₁⟩ := fz59_phi_prod hb hΦ n ω
    have hω : ω₁ = ω' := fz59crit_tr_inj (himg₁.symm.trans himg)
    subst hω
    refine ⟨z₁ * ((n : G) * z * (n : G)⁻¹),
      (fz59Z b).mul_mem hz₁ (fz59_conj_mem_Z hb hΦ n hz), ?_⟩
    have e : (n : G) * (fz59Prod b ω * z) * (n : G)⁻¹ =
        fz59Prod b ω₁ * (z₁ * ((n : G) * z * (n : G)⁻¹)) := by
      calc (n : G) * (fz59Prod b ω * z) * (n : G)⁻¹
          = ((n : G) * fz59Prod b ω * (n : G)⁻¹) * ((n : G) * z * (n : G)⁻¹) := by group
        _ = (fz59Prod b ω₁ * z₁) * ((n : G) * z * (n : G)⁻¹) := by rw [hP]
        _ = fz59Prod b ω₁ * (z₁ * ((n : G) * z * (n : G)⁻¹)) := by rw [mul_assoc]
    rw [← e]
    exact hconj.trans (isConj_iff.mpr ⟨(n : G), rfl⟩)
  exact fz59_cb Φ.range (by rintro _ ⟨n, rfl⟩ i k k'; exact hΦ.2 n i k k')
    ⟨⟨rho, hρ⟩, hΦρ⟩ ⟨⟨lam, hlam⟩, hΦlam⟩
    (by rintro _ ⟨n, rfl⟩ h; exact (hkerΦ n).mpr (fz59cls_col0 hB hF hΦ n h)) h4 h8 _ h0 hN
    (fz59cls_fusion hB hF)
    (by
      rintro ω ⟨z, hz, hconj⟩
      exact fz59_crit hb hΦ (fun n hn => (hkerΦ n).mp hn) hB.cent2 ω hz hconj)

end CFSG.OddStandard.SmallF3.FritzII
