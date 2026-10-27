module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NMisc
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NConj

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable {I : S.Inst} {H : S.Sec6Hyp T₁}

namespace Data6

variable (D : I.Data6 H) (R : D.Rel)

theorem Q0_le : S.Q0 I.yi I.ki D.w₁ D.w₂ ≤ D.Q₁ :=
  sup_le (sup_le (I.E0_le_E.trans D.E_le_Q₁) (zpowers_le.mpr D.w₁_Q₁)) (zpowers_le.mpr D.w₂_Q₁)

theorem D₁₁_le : zpowers D.d ≤ normalizer (S.E I.yi : Set X) ⊓ normalizer (D.Q₁ : Set X) ⊓
    centralizer ({S.t} : Set X) :=
  zpowers_le.mpr (mem_inf.mpr ⟨mem_inf.mpr ⟨D.d_mat.mem, D.d_Q₁⟩, D.d_mem_C_t⟩)

theorem w₁_comm_t : D.w₁ * S.t * D.w₁⁻¹ * S.t⁻¹ ≠ 1 := by
  rw [D.w₁_mat.conj_t, M1C_two, I.wV_t, I.wV_inv, ← I.wV_add, ← I.wV_zero]
  intro h
  have := I.wV_injective h
  simp [addV] at this

theorem w₁_comm_C' : ∀ c ∈ D.Q₁ ⊓ centralizer (zpowers D.d : Set X), D.w₁ * c * D.w₁⁻¹ * c⁻¹ ∈
    (match actOf D.ε with
      | .one => closure {S.z}
      | .two => closure {S.z * I.ki}) := by
  intro c hc
  have h := D.w₁_comm_C c hc
  rcases Fin.exists_fin_two.mp ⟨D.ε, rfl⟩ with he | he
  · rw [he] at h ⊢
    simpa [actOf, wV] using h
  · rw [he] at h ⊢
    simpa [actOf, wV] using h

noncomputable def toSec6 : S.Sec6 T₁ I.yi I.ki I.ui where
  S₁ := D.S₁
  Q₁ := D.Q₁
  D₁₁ := zpowers D.d
  C₁ := D.C₁
  v := D.v
  w₁ := D.w₁
  w₂ := D.w₂
  u := D.u
  d := D.d
  act := actOf D.ε
  q0 := q0Of D.ε R.s1 R.s4
  automizer := I.automizer H
  controls := controls I H
  card_conj := card_conj I H
  isPGroup_S₁ := D.isPGroup
  S₁_le := D.le
  S₁_maximal := D.maximal
  S₁_eq := D.S₁_eq R
  v_central := D.v_central
  d_mem := mem_inf.mpr ⟨D.d_mat.mem, D.d_mem_C_t⟩
  d_cube := D.d_cube_mem
  d_not_mem := D.d_not_mem
  u_inv_d := by rw [D.u_inv_d, inv_mul_cancel]; exact one_mem _
  u_comm_w₁ := D.u_comm_w₁
  normalizer_inf_centralizer := D.normalizer_inf_centralizer
  act_holds := D.act_holds
  k_fixed := fun _ hn => I.k_fixed H hn
  T₁_eq := D.T₁_eq R
  T₁_le := D.T₁_le
  Q₁_eq := rfl
  Q0_le := D.Q0_le
  Q0_invariant := fun _ hn => D.Q0_invariant R hn
  q0_holds := D.q0_holds R
  isPGroup_D₁₁ := D.isPGroup_D₁₁
  D₁₁_le := D.D₁₁_le
  C_eq := D.C_eq
  w₁_comm_C := D.w₁_comm_C'
  w₁_comm_t := D.w₁_comm_t
  C₁_le := D.C₁_le
  C₁_sup := D.C₁_sup
  card_C₁ := D.card_C₁
  card_C := D.card_C
  C₁_comm := D.C₁_comm R
  u_eq := D.u_eq
  u_comm_C := D.u_comm_C
  u_inv_D₁₁ := D.u_inv_D₁₁
  S₁_commutator_mem := D.S₁_commutator_mem R
  Q₁_char := fun h _ hn => by
    rcases q0Of_cases D.ε R.s1 R.s4 with ⟨hq, -⟩ | ⟨hq, hε, h1, -⟩ | ⟨hq, hε, -, h4⟩ |
        ⟨hq, hε, h1, -⟩ | ⟨hq, -⟩ <;> rw [hq] at h
    · simp at h
    · exact D.Q₁_char R hε (Or.inl h1) hn
    · exact D.Q₁_char R hε (Or.inr h4) hn
    · exact D.Q₁_char R hε (Or.inl h1) hn
    · simp at h
  no_conj_extraspecial := fun h => by
    rcases q0Of_cases D.ε R.s1 R.s4 with ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, hε⟩ <;>
      rw [hq] at h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · exact D.no_conj_two R hε
  no_conj_of := fun h => by
    rcases q0Of_cases D.ε R.s1 R.s4 with ⟨hq, hε, -, h4⟩ | ⟨hq, hε, -, h4⟩ | ⟨hq, -⟩ |
        ⟨hq, -⟩ | ⟨hq, -⟩ <;> rw [hq] at h
    · exact D.no_conj_one R hε h4
    · exact D.no_conj_one R hε h4
    · simp at h
    · simp at h
    · simp at h

end Data6

theorem exists_sec6 (I : S.Inst) (H : S.Sec6Hyp T₁) : Nonempty (S.Sec6 T₁ I.yi I.ki I.ui) := by
  obtain ⟨D⟩ := I.exists_data6 H
  obtain ⟨R⟩ := D.nonempty_rel
  exact ⟨D.toSec6 R⟩

end Inst

end A7Base

theorem fritzA7Section6 : FritzA7Section6 := by
  intro _ X _ _ _ _ _ S F T₁ h4 hF hnc
  have H := A7Base.Sec6Hyp.of_sec4 h4 hF hnc
  obtain ⟨hx, hy, hk⟩ := hF
  have e1 : F.xF * F.yF = S.y := by rw [hx, hy, inv_mul_cancel_left]
  rw [e1, hy, hk]
  exact ⟨S.inst₁.exists_sec6 H, S.inst₂.exists_sec6 H⟩

end CFSG.ComponentClassification.HSFLit
