module

public import CFSG.ClassicalInvolution.Q3.TL4D1ML32
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

theorem fanoVec_castLE : ∀ k : Fin 3, fanoVec (Fin.castLE (by norm_num) k) = Pi.single k 1 := by
  decide

theorem lpermHom_injective : Function.Injective lpermHom := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hcol : ∀ k : Fin 3, A.1 *ᵥ Pi.single k 1 = Pi.single k 1 := by
    intro k
    have h1 : lapply A (Fin.castLE (by norm_num) k) = Fin.castLE (by norm_num) k := by
      rw [← lpermHom_apply, hA]
      rfl
    have h2 := fanoVec_lapply A (Fin.castLE (by norm_num) k)
    rw [h1, fanoVec_castLE] at h2
    exact h2.symm
  refine Subtype.ext (Matrix.ext fun r k => ?_)
  have := congrFun (hcol k) r
  rw [mulVec_single_one] at this
  show A.1 r k = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) r k
  exact this.trans (by rw [Pi.single_apply, one_apply])

theorem exists_lpermHom_eq {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ l32) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), lpermHom A = σ := by
  set A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    Matrix.of fun r k => fanoVec (σ (Fin.castLE (by norm_num) k)) r with hA₀
  have hline : ∀ a b c : Fin 7, ({a, b, c} : Finset (Fin 7)) ∈ fanoLines →
      fanoVec (σ a) + fanoVec (σ b) = fanoVec (σ c) := by
    intro a b c habc
    have h1 := (hσ _ habc).1
    simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] at h1
    exact ((mem_fanoLines_iff _ _ _).mp h1).2
  have hbase : ∀ k : Fin 3, A₀ *ᵥ fanoVec (Fin.castLE (by norm_num) k) =
      fanoVec (σ (Fin.castLE (by norm_num) k)) := by
    intro k
    rw [fanoVec_castLE, mulVec_single_one]
    rfl
  have h0 := hbase 0
  have h1 := hbase 1
  have h2 := hbase 2
  have hv3 : fanoVec 3 = fanoVec 0 + fanoVec 1 := by decide
  have hv4 : fanoVec 4 = fanoVec 1 + fanoVec 2 := by decide
  have hv5 : fanoVec 5 = fanoVec 2 + fanoVec 3 := by decide
  have hv6 : fanoVec 6 = fanoVec 3 + fanoVec 4 := by decide
  have h3 : A₀ *ᵥ fanoVec 3 = fanoVec (σ 3) := by
    rw [hv3, mulVec_add]
    exact (congrArg₂ (· + ·) h0 h1).trans (hline 0 1 3 (by decide))
  have h4 : A₀ *ᵥ fanoVec 4 = fanoVec (σ 4) := by
    rw [hv4, mulVec_add]
    exact (congrArg₂ (· + ·) h1 h2).trans (hline 1 2 4 (by decide))
  have h5 : A₀ *ᵥ fanoVec 5 = fanoVec (σ 5) := by
    rw [hv5, mulVec_add, h3]
    exact (congrArg (· + fanoVec (σ 3)) h2).trans (hline 2 3 5 (by decide))
  have h6 : A₀ *ᵥ fanoVec 6 = fanoVec (σ 6) := by
    rw [hv6, mulVec_add, h3, h4]
    exact hline 3 4 6 (by decide)
  have hall : ∀ x : Fin 7, A₀ *ᵥ fanoVec x = fanoVec (σ x) := by
    intro x
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  have hdet : A₀.det = 1 := by
    have hne : A₀.det ≠ 0 := by
      intro h0'
      obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0'
      rw [← fanoVec_fanoIdx v hv, hall] at hAv
      exact fanoVec_ne_zero _ hAv
    generalize A₀.det = d at hne
    revert d
    decide
  let A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨A₀, hdet⟩
  have hA : A.1 = A₀ := rfl
  refine ⟨A, Equiv.ext fun x => ?_⟩
  rw [lpermHom_apply]
  unfold lapply
  rw [hA, hall, fanoIdx_fanoVec]

noncomputable def sl3TwoEquivL32 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥l32 :=
  (MonoidHom.ofInjective lpermHom_injective).trans (MulEquiv.subgroupCongr (by
    ext σ
    constructor
    · rintro ⟨A, rfl⟩
      exact lpermHom_mem_l32 A
    · intro hσ
      exact exists_lpermHom_eq hσ))

theorem isSimpleGroup_sl3Two : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r hr
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)).mp hPSL

theorem isSimpleGroup_l32 : IsSimpleGroup ↥l32 :=
  (MulEquiv.isSimpleGroup_congr sl3TwoEquivL32).mp isSimpleGroup_sl3Two

end CFSG.ClassicalInvolution.Q3.TL4
