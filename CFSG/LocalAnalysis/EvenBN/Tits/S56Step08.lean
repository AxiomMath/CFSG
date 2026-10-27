module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P08
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P517

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace S56

theorem coe_sup_eq_mul_of_comm {Γ : Type*} [Group Γ] {H K : Subgroup Γ}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    ((H ⊔ K : Subgroup Γ) : Set Γ) = (H : Set Γ) * (K : Set Γ) := by
  let S : Subgroup Γ :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', mul_mem hh hh', k * k', mul_mem hk hk', ?_⟩
        calc h * k * (h' * k') = h * (k * h') * k' := by group
          _ = h * (h' * k) * k' := by rw [← hc h' hh' k hk]
          _ = h * h' * (k * k') := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        have h1 : h⁻¹ * k⁻¹ = k⁻¹ * h⁻¹ := by
          have := hc h⁻¹ (inv_mem hh) k⁻¹ (inv_mem hk)
          exact this
        calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
          _ = h⁻¹ * k⁻¹ := h1.symm }
  ext g
  constructor
  · intro hg
    have hle : H ⊔ K ≤ S :=
      sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
        (fun k hk => ⟨1, one_mem _, k, hk, by simp⟩)
    obtain ⟨h, hh, k, hk, rfl⟩ := hle hg
    exact Set.mul_mem_mul hh hk
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (mem_sup_left hh) (mem_sup_right hk)

end S56

namespace N

section Step08

variable {G : Type} [Group G] [Finite G]


theorem P11_eq_s56P11 (d : Data G) : P11 d = d.s56P11 := Subgroup.ext fun _ => Iff.rfl

theorem Pe11_eq_s56Pe11 (d : Data G) : Pe11 d = d.s56Pe11 := by
  rw [Pe11, P11_eq_s56P11]
  rfl

theorem IsY.facts {d : Data G} {y : G} (hy : IsY d y) : y ∈ d.N ∧ y ^ 3 = 1 ∧ y ≠ 1 := by
  obtain ⟨hyNL, hord, -⟩ := hy
  refine ⟨(mem_inf.1 hyNL).1, ?_, ?_⟩
  · rw [← hord]
    exact pow_orderOf_eq_one y
  · rintro rfl
    rw [orderOf_one] at hord
    exact absurd hord (by norm_num)

theorem step08_of_KV
    (hKV : ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}, d.Thm49Statement → d.Hyp →
      d.S56Z0 z₀ → ∀ x ∈ d.s56V, d.s56Eps x ∈ d.s56U11 →
        x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ zpowers d.z) : Step08 := by
  intro G _ _ d z₀ h49 hd hz hinv h05 h06 h07
  have hsq : z₀ * z₀ = 1 := hinv z₀ hz
  obtain ⟨⟨y₁, hy₁⟩, -⟩ := h07
  obtain ⟨hy₁N, hy₁3, hy₁1⟩ := hy₁.facts
  have hstruct : ∀ y, IsY d y → d.B ≤ d.s56P11 ∧ d.F ≤ d.s56Pe11 ∧
      d.s56P11 = d.s56Pe11 ⊔ zpowers d.t ∧
      d.s56Pe11 = d.F ⊔ Subgroup.closure ({z₀, y * z₀ * y⁻¹} : Set G) ∧
      CFSG.Open.IsElemAbelian 2 d.s56Pe11 ∧ Nat.card d.s56Pe11 = 2 ^ 7 ∧ d.t ∉ d.s56Pe11 :=
    fun y hy => by
      obtain ⟨hyN, hy3, hy1⟩ := hy.facts
      exact hd.s56_P11_structure h49 hz hsq hyN hy3 hy1
  obtain ⟨hB, hF, hP11, -, hel, hcard, ht⟩ := hstruct y₁ hy₁
  refine ⟨by rw [P11_eq_s56P11]; exact hB, by rw [Pe11_eq_s56Pe11]; exact hF,
    by rw [P11_eq_s56P11, Pe11_eq_s56Pe11]; exact hP11,
    fun y hy => by rw [Pe11_eq_s56Pe11]; exact (hstruct y hy).2.2.2.1,
    by rw [Pe11_eq_s56Pe11]; exact hel, by rw [Pe11_eq_s56Pe11]; exact hcard,
    by rw [Pe11_eq_s56Pe11]; exact ht, ?_⟩
  rw [Pe11_eq_s56Pe11]
  obtain ⟨hQD, hQA, -⟩ := h05
  obtain ⟨f, hf, hfV⟩ := hd.s56_c1_mem_FV h49 hz hsq hy₁N hy₁3 hy₁1 hQD hQA (hKV h49 hd hz)
  have hE := hd.s56_Pe11_eq_R1 h49 hz hsq hy₁N hy₁3 hy₁1
  have hz0 : z₀ ∈ d.s56Pe11 := by rw [hE]; exact Data.s56_z0_mem_R1 d
  have hc1 : y₁ * z₀ * y₁⁻¹ ∈ d.s56Pe11 := by rw [hE]; exact Data.s56_c1_mem_R1 d
  have hFle : d.F ≤ d.s56Pe11 := hF
  have hxW : f * (y₁ * z₀ * y₁⁻¹) ∈ d.s56Pe11 ⊓ d.s56V :=
    mem_inf.2 ⟨mul_mem (hFle hf) hc1, hfV⟩
  have hz0W : z₀ ∈ d.s56Pe11 ⊓ d.s56V := mem_inf.2 ⟨hz0, hz.mem_V⟩
  have hle : d.s56Pe11 ≤ d.F ⊔ (d.s56Pe11 ⊓ d.s56V) := by
    refine hE.le.trans ?_
    rw [Data.s56R1]
    refine sup_le le_sup_left ((Subgroup.closure_le _).2 ?_)
    intro x hx
    rcases hx with rfl | hx
    · exact mem_sup_right hz0W
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have e : y₁ * z₀ * y₁⁻¹ = f⁻¹ * (f * (y₁ * z₀ * y₁⁻¹)) := by group
      rw [e]
      exact mul_mem (mem_sup_left (inv_mem hf)) (mem_sup_right hxW)
  have hcomm : ∀ a ∈ d.F, ∀ b ∈ d.s56Pe11 ⊓ d.s56V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, hFle ha⟩ ⟨b, (mem_inf.1 hb).1⟩)
  have hsup : d.F ⊔ (d.s56Pe11 ⊓ d.s56V) ≤ d.s56Pe11 := sup_le hFle inf_le_left
  rw [← S56.coe_sup_eq_mul_of_comm hcomm]
  exact congrArg (fun K : Subgroup G => (K : Set G)) (le_antisymm hle hsup)

theorem step08_holds : Step08 :=
  step08_of_KV fun h49 hd hz _ hx hε => hd.s56_V_comm_pv7_mem_zpowers h49 hz hx hε

end Step08

end N

end CFSG.LocalAnalysis.EvenBN.Tits
