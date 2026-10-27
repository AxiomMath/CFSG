module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemX

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_ncard_V (hc : Ctx0 t L S x₁ x₂ lam rho) : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
  change Nat.card ↥(fourGrp x₁ x₂) = 4
  exact (hc.wreath.fourGrp_eq_omega).2.2

theorem w4_V_le_invCent (hc : Ctx4 t L S x₁ x₂ lam rho tau) : fourGrp x₁ x₂ ≤ invCent t := by
  rw [fourGrp]
  refine (Subgroup.closure_le _).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).1
  · exact S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).2

theorem w4_t_comm_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) {v : G} (hv : v ∈ fourGrp x₁ x₂) :
    t * v = v * t :=
  (S4A.mem_invCent_iff.mp (w4_V_le_invCent hc hv)).symm

theorem w4_tM_of_ncard (hc : Ctx10 t L S x₁ x₂ lam rho tau)
    (h4 : (conjIn (ctxM t tau x₁ x₂) t).ncard = 4) :
    conjIn (ctxM t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx4
  have hV : (fourGrp x₁ x₂ : Set G).ncard = 4 := w4_ncard_V hc4.toCtx0
  have htauN : tau ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  have hge : ∀ {c : G}, (∀ v ∈ fourGrp x₁ x₂, ∀ w ∈ fourGrp x₁ x₂, t * v ≠ c * w) →
      ∀ {T : Set G}, t • (fourGrp x₁ x₂ : Set G) ∪ c • (fourGrp x₁ x₂ : Set G) ⊆ T →
        8 ≤ T.ncard := by
    intro c hdisj T hT
    have hd : Disjoint (t • (fourGrp x₁ x₂ : Set G)) (c • (fourGrp x₁ x₂ : Set G)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hu
      obtain ⟨w, hw, hwe⟩ := Set.mem_smul_set.mp hu'
      exact hdisj v hv w hw (by simpa [smul_eq_mul] using hwe.symm)
    have hcard : (t • (fourGrp x₁ x₂ : Set G) ∪ c • (fourGrp x₁ x₂ : Set G)).ncard = 8 := by
      rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), Set.ncard_smul_set,
        Set.ncard_smul_set, hV]
    calc 8 = (t • (fourGrp x₁ x₂ : Set G) ∪ c • (fourGrp x₁ x₂ : Set G)).ncard := hcard.symm
      _ ≤ T.ncard := Set.ncard_le_ncard hT (Set.toFinite _)
  have hdisj_tau : ∀ v ∈ fourGrp x₁ x₂, ∀ w ∈ fourGrp x₁ x₂, t * v ≠ tau * w := by
    intro v hv w hw h
    apply l12_t_not_mem_N hc4
    have : t = tau * w * v⁻¹ := by rw [← h]; group
    rw [this]
    exact mul_mem (mul_mem htauN (hVN hw)) (inv_mem (hVN hv))
  have hdisj_ttau : ∀ v ∈ fourGrp x₁ x₂, ∀ w ∈ fourGrp x₁ x₂, t * v ≠ (t * tau) * w := by
    intro v hv w hw h
    apply l12_tau_not_mem_V hc4
    have h' : v = tau * w := by
      have : t * v = t * (tau * w) := by rw [h]; group
      exact mul_left_cancel this
    have : tau = v * w⁻¹ := by rw [h']; group
    rw [this]
    exact mul_mem hv (inv_mem hw)
  rcases hc.l49.2 with h | h | h | h
  · exact h
  · exfalso
    have := hge hdisj_tau (T := conjIn (ctxM t tau x₁ x₂) t) (by rw [h])
    omega
  · exfalso
    have := hge hdisj_ttau (T := conjIn (ctxM t tau x₁ x₂) t) (by rw [h])
    omega
  · exfalso
    have := hge hdisj_tau (T := conjIn (ctxM t tau x₁ x₂) t)
      (by rw [h]; exact Set.subset_union_left)
    omega

private theorem w4_conj_mem_closure_of_gens {T : Set G} {g : G}
    (hgen : ∀ x ∈ T, g * x * g⁻¹ ∈ Subgroup.closure T) :
    ∀ w ∈ Subgroup.closure T, g * w * g⁻¹ ∈ Subgroup.closure T := by
  intro w hw
  refine Subgroup.closure_induction (p := fun w _ => g * w * g⁻¹ ∈ Subgroup.closure T)
    ?_ ?_ ?_ ?_ hw
  · intro x hx; exact hgen x hx
  · simp
  · intro x y hx hy ihx ihy
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]; exact mul_mem ihx ihy
  · intro x hx ihx
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]; exact inv_mem ihx

theorem w4_tG_X
    (hc : W4Ctx0 t L S x₁ x₂ lam rho tau) (g : G)
    (hg : g * t * g⁻¹ ∈ ctxX t tau x₁ x₂) : g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
  have hmem : g * t * g⁻¹ ∈
      {u : G | (∃ g : G, g * t * g⁻¹ = u) ∧ u ∈ ctxX t tau x₁ x₂} := ⟨⟨g, rfl⟩, hg⟩
  rw [Ctx10.tG_inf_X hc.toCtx10, hc.tM] at hmem
  exact hmem

theorem w4_card_M
    (hc : W4Ctx0 t L S x₁ x₂ lam rho tau) :
    Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 9 := by
  have h := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) t
  rw [hc.tM, Set.ncard_smul_set, w4_ncard_V hc.toCtx10.toCtx4.toCtx0,
    p0_card_CMt hc.toCtx10.toCtx4] at h
  rw [h]
  norm_num

theorem w4_normal_V (hc : W4Ctx0 t L S x₁ x₂ lam rho tau) :
    NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ :=
    (p0_V_le_N_le_X t tau x₁ x₂).1.trans (p0_V_le_N_le_X t tau x₁ x₂).2
  have ht2 : t * t = 1 := S4A.t_mul_self hc4.hyp
  refine ⟨fun v hv => Subgroup.le_normalizer (hVX hv), fun g hg v hv => ?_⟩
  have h1 : g * t * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨g, hg, rfl⟩
  have htv : t * v ∈ conjIn (ctxM t tau x₁ x₂) t := by
    rw [hc.tM]; exact Set.mem_smul_set.mpr ⟨v, hv, rfl⟩
  obtain ⟨m, hm, hmt⟩ := htv
  have h2 : g * (t * v) * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t :=
    ⟨g * m, mul_mem hg hm, by rw [← hmt]; group⟩
  rw [hc.tM] at h1 h2
  obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp h1
  obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp h2
  simp only [smul_eq_mul] at hae hbe
  have hv_eq : v = t * (t * v) := by rw [← mul_assoc, ht2, one_mul]
  have key : g * v * g⁻¹ = (g * t * g⁻¹) * (g * (t * v) * g⁻¹) := by
    conv_lhs => rw [hv_eq]
    group
  rw [key, ← hae, ← hbe]
  have hta : t * a = a * t := w4_t_comm_V hc4 ha
  have hab : t * a * (t * b) = a * b := by
    calc t * a * (t * b) = a * t * (t * b) := by rw [hta]
      _ = a * (t * t) * b := by group
      _ = a * b := by rw [ht2, mul_one]
  rw [hab]
  exact mul_mem ha hb

theorem w4_normal_E (hc : W4Ctx0 t L S x₁ x₂ lam rho tau)
    (hV : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂)) :
    NormalIn (ctxE t x₁ x₂) (ctxM t tau x₁ x₂) := by
  have hVE : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
    rw [fourGrp, ctxE]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have htE : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨?_, fun g hg e he => ?_⟩
  · rw [ctxE]
    refine (Subgroup.closure_le (K := ctxM t tau x₁ x₂)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hXle : ctxX t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := Subgroup.le_normalizer
    rcases hx with rfl | rfl | rfl <;> exact hXle (Subgroup.subset_closure (by simp))
  · rw [ctxE] at he ⊢
    refine w4_conj_mem_closure_of_gens (g := g) ?_ e he
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 : g * x * g⁻¹ ∈ conjIn (ctxM x tau x₁ x₂) x := ⟨g, hg, rfl⟩
      rw [hc.tM] at h1
      obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp h1
      simp only [smul_eq_mul] at hae
      rw [← hae]
      exact mul_mem htE (hVE ha)
    · exact hVE (hV.2 g hg _ (Subgroup.subset_closure (by simp)))
    · exact hVE (hV.2 g hg _ (Subgroup.subset_closure (by simp)))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
