module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36Hom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59EModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzQuat

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

private theorem fz59e_gen_mem (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) {e : G}
    (he : e ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂} : Set G)) : e ∈ T₂ := by
  rw [hsh.gen]
  apply Subgroup.subset_closure
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he ⊢
  tauto

private theorem fz59e_R6_le (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ≤ T₂ := by
  rw [fzR6, closure_le]
  exact fun e he => fz59e_gen_mem hsh he

private theorem fz59e_q8_mem {p q : G} (hpq : IsQ8Pair p q) {s : Set G} (hp : p ∈ s)
    (hq : q ∈ s) (r : Q8) : q8Hom hpq r ∈ closure s := by
  have h : q8Hom hpq r ∈ closure ({p, q} : Set G) := by
    rw [← fz_q8_range hpq]
    exact ⟨r, rfl⟩
  exact closure_mono (Set.insert_subset hp (Set.singleton_subset_iff.mpr hq)) h

theorem fz59e_mem_R6_iff (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (x : G) :
    x ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ↔ x ∈ T₂ ∧ ∀ y ∈ T₂, y ^ 4 = 1 → x * y ^ 2 = y ^ 2 * x := by
  obtain ⟨π, hπ1, hπ2, hπ3, -, hπrange, hπker⟩ := fzl_model_hom hsh
  constructor
  · intro hx
    refine ⟨fz59e_R6_le hsh hx, fun y hy hy4 => ?_⟩
    rw [← hπrange] at hy
    obtain ⟨m, rfl⟩ := hy
    have hm4 : KEq (m * m * (m * m)) 1 :=
      (hπker _ _).mp (by
        rw [map_one, ← hy4]
        simp only [map_mul, pow_succ, pow_zero, one_mul, mul_assoc])
    have hgen : ∀ e ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂} : Set G),
        ∃ g ∈ fz59e_baseGens, π g = e := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨(QuaternionGroup.a 1, 1, 1), 1⟩, by simp [fz59e_baseGens],
          (hπ1 _).trans (fzl_q8Hom_a_one hsh.quat₁)⟩
      · exact ⟨⟨(QuaternionGroup.xa 0, 1, 1), 1⟩, by simp [fz59e_baseGens],
          (hπ1 _).trans (fzl_q8Hom_xa_zero hsh.quat₁)⟩
      · exact ⟨⟨(1, QuaternionGroup.a 1, 1), 1⟩, by simp [fz59e_baseGens],
          (hπ2 _).trans (fzl_q8Hom_a_one hsh.quat₂)⟩
      · exact ⟨⟨(1, QuaternionGroup.xa 0, 1), 1⟩, by simp [fz59e_baseGens],
          (hπ2 _).trans (fzl_q8Hom_xa_zero hsh.quat₂)⟩
      · exact ⟨⟨(1, 1, QuaternionGroup.a 1), 1⟩, by simp [fz59e_baseGens],
          (hπ3 _).trans (fzl_q8Hom_a_one hsh.quat₃)⟩
      · exact ⟨⟨(1, 1, QuaternionGroup.xa 0), 1⟩, by simp [fz59e_baseGens],
          (hπ3 _).trans (fzl_q8Hom_xa_zero hsh.quat₃)⟩
    have hle : fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ≤ centralizer {π m ^ 2} := by
      rw [fzR6, closure_le]
      intro e he
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      obtain ⟨g, hg, rfl⟩ := hgen e he
      have h := (hπker _ _).mpr (fz59e_sq_comm m hm4 g hg)
      simpa only [map_mul, pow_two] using h
    exact mem_centralizer_singleton_iff.mp (hle hx)
  · rintro ⟨hxT, hx⟩
    have h₁ := hx (x₁ * t) (fz59e_gen_mem hsh (by simp)) hsh.quat₁.1
    have h₂ := hx (x₂ * t) (fz59e_gen_mem hsh (by simp)) hsh.quat₂.1
    rw [← hπrange] at hxT
    obtain ⟨m, rfl⟩ := hxT
    have e₁ : π ⟨(QuaternionGroup.a 2, 1, 1), 1⟩ = (x₁ * t) ^ 2 :=
      (hπ1 _).trans (fzl_q8Hom_a_two hsh.quat₁)
    have e₂ : π ⟨(1, QuaternionGroup.a 2, 1), 1⟩ = (x₂ * t) ^ 2 :=
      (hπ2 _).trans (fzl_q8Hom_a_two hsh.quat₂)
    have hk₁ := (hπker (m * ⟨(QuaternionGroup.a 2, 1, 1), 1⟩)
      (⟨(QuaternionGroup.a 2, 1, 1), 1⟩ * m)).mp (by rw [map_mul, map_mul, e₁]; exact h₁)
    have hk₂ := (hπker (m * ⟨(1, QuaternionGroup.a 2, 1), 1⟩)
      (⟨(1, QuaternionGroup.a 2, 1), 1⟩ * m)).mp (by rw [map_mul, map_mul, e₂]; exact h₂)
    have hr := fz59e_base_of_comm m hk₁ hk₂
    obtain ⟨⟨a, b, c⟩, e⟩ := m
    change e = 1 at hr
    subst hr
    have hsplit : (⟨(a, b, c), 1⟩ : Model) =
        (⟨(a, 1, 1), 1⟩ : Model) * ⟨(1, b, 1), 1⟩ * ⟨(1, 1, c), 1⟩ := by
      ext <;> simp
    rw [hsplit, map_mul, map_mul, hπ1, hπ2, hπ3, fzR6]
    exact mul_mem (mul_mem (fz59e_q8_mem hsh.quat₁ (by simp) (by simp) a)
      (fz59e_q8_mem hsh.quat₂ (by simp) (by simp) b))
      (fz59e_q8_mem hsh.quat₃ (by simp) (by simp) c)

theorem fz59e_canon (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    FzCanon T₂ (fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂) := by
  intro α hα g
  rw [fz59e_mem_R6_iff hsh, fz59e_mem_R6_iff hsh]
  constructor
  · rintro ⟨hgT, hg⟩
    refine ⟨(hα g).mp hgT, fun y hy hy4 => ?_⟩
    have hy' : α.symm y ∈ T₂ := (hα _).mpr (by rwa [MulEquiv.apply_symm_apply])
    have hy4' : α.symm y ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    have h := congrArg α (hg _ hy' hy4')
    simpa only [map_mul, map_pow, MulEquiv.apply_symm_apply] using h
  · rintro ⟨hgT, hg⟩
    refine ⟨(hα g).mpr hgT, fun y hy hy4 => ?_⟩
    have h := hg (α y) ((hα y).mp hy) (by rw [← map_pow, hy4, map_one])
    apply α.injective
    simpa only [map_mul, map_pow] using h

theorem fz59e_le_normalizer_of_canon {T W : Subgroup G} (hW : FzCanon T W) :
    T ≤ normalizer (W : Set G) := by
  intro x hx
  have hα : ∀ g, g ∈ T ↔ MulAut.conj x g ∈ T := by
    intro g
    rw [MulAut.conj_apply]
    exact (mem_normalizer_iff.mp (le_normalizer hx)) g
  rw [mem_normalizer_iff]
  intro w
  have h := hW (MulAut.conj x) hα w
  rwa [MulAut.conj_apply] at h

end CFSG.OddStandard.SmallF3.FritzII
