module

public import CFSG.GroupActions.PrimitiveNormalTransitive
public import CFSG.GroupActions.StabilizerFactorization
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupActions

open scoped commutatorElement

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem equivalence_normal_orbit (N : Subgroup G) :
    Equivalence fun x y : Ω => ∃ n ∈ N, n • x = y where
  refl x := ⟨1, one_mem N, one_smul G x⟩
  symm := by
    rintro x y ⟨n, hn, rfl⟩
    exact ⟨n⁻¹, inv_mem hn, inv_smul_smul n x⟩
  trans := by
    rintro x y z ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨m * n, mul_mem hm hn, mul_smul m n x⟩

theorem exists_mem_smul_eq_iff (N : Subgroup G) [hN : N.Normal] (g : G) (x y : Ω) :
    (∃ n ∈ N, n • x = y) ↔ ∃ n ∈ N, n • (g • x) = g • y := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨g * n * g⁻¹, hN.conj_mem n hn g, ?_⟩
    rw [smul_smul, smul_smul, inv_mul_cancel_right]
  · rintro ⟨n, hn, h⟩
    refine ⟨g⁻¹ * n * g, ?_, ?_⟩
    · simpa using hN.conj_mem n hn g⁻¹
    · rw [← smul_smul, ← smul_smul, h, inv_smul_smul]

theorem exists_mul_of_normalClosure_eq_top (N : Subgroup G) [hN : N.Normal] {H A : Subgroup G}
    (hAH : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hNH : ∀ g : G, ∃ n ∈ N, ∃ h ∈ H, n * h = g)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) (g : G) :
    ∃ n ∈ N, ∃ a ∈ A, n * a = g := by
  have hconj : ∀ x : G, ∀ a ∈ A, x * a * x⁻¹ ∈ N ⊔ A := by
    intro x a ha
    obtain ⟨n, hn, h, hh, rfl⟩ := hNH x
    have ha' : h * a * h⁻¹ ∈ A := hAH h hh a ha
    have e : n * h * a * (n * h)⁻¹ =
        (n * ((h * a * h⁻¹) * n⁻¹ * (h * a * h⁻¹)⁻¹)) * (h * a * h⁻¹) := by group
    rw [e]
    refine mul_mem (Subgroup.mem_sup_left (mul_mem hn ?_)) (Subgroup.mem_sup_right ha')
    have := hN.conj_mem n⁻¹ (inv_mem hn) (h * a * h⁻¹)
    simpa [mul_assoc] using this
  have hle : Subgroup.normalClosure (A : Set G) ≤ N ⊔ A := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    exact hconj c a ha
  have hg : g ∈ N ⊔ A := hle (hgen ▸ Subgroup.mem_top g)
  exact Subgroup.mem_sup_of_normal_left.1 hg

theorem commutator_le_of_normal_ne_bot [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (α : Ω) {A : Subgroup G} (hAn : ∀ h ∈ MulAction.stabilizer G α, ∀ a ∈ A, h * a * h⁻¹ ∈ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) (N : Subgroup G) [hN : N.Normal]
    (hN1 : N ≠ ⊥) : commutator G ≤ N := by
  have : Nonempty Ω := ⟨α⟩
  have : MulAction.IsPretransitive N Ω := isPretransitive_of_normal_ne_bot N hN1
  have hNH : ∀ g : G, ∃ n ∈ N, ∃ h ∈ MulAction.stabilizer G α, n * h = g := by
    intro g
    obtain ⟨n, h, hnh⟩ := exists_mul_stabilizer_eq N α g
    exact ⟨n, n.2, h, h.2, hnh⟩
  have hNA := exists_mul_of_normalClosure_eq_top N hAn hNH hgen
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨n₁, hn₁, a₁, ha₁, rfl⟩ := hNA x
  obtain ⟨n₂, hn₂, a₂, ha₂, rfl⟩ := hNA y
  refine (QuotientGroup.eq_one_iff _).1 ?_
  have e₁ : ((n₁ * a₁ : G) : G ⧸ N) = (a₁ : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hn₁, one_mul]
  have e₂ : ((n₂ * a₂ : G) : G ⧸ N) = (a₂ : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hn₂, one_mul]
  have hc : ⁅a₁, a₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hAc a₁ ha₁ a₂ ha₂)
  calc ((⁅n₁ * a₁, n₂ * a₂⁆ : G) : G ⧸ N)
      = ⁅((n₁ * a₁ : G) : G ⧸ N), ((n₂ * a₂ : G) : G ⧸ N)⁆ :=
        map_commutatorElement (QuotientGroup.mk' N) _ _
    _ = ⁅(a₁ : G ⧸ N), (a₂ : G ⧸ N)⁆ := by rw [e₁, e₂]
    _ = ((⁅a₁, a₂⁆ : G) : G ⧸ N) := (map_commutatorElement (QuotientGroup.mk' N) _ _).symm
    _ = 1 := by rw [hc, QuotientGroup.mk_one]

theorem isSimpleGroup_of_iwasawa [Nontrivial G] (hperf : commutator G = ⊤) [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω] (α : Ω) {A : Subgroup G}
    (hAn : ∀ h ∈ MulAction.stabilizer G α, ∀ a ∈ A, h * a * h⁻¹ ∈ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) : IsSimpleGroup G := by
  refine ⟨fun N hN => ?_⟩
  rcases eq_or_ne N ⊥ with h | h
  · exact .inl h
  · exact .inr (eq_top_iff.2 (hperf ▸ commutator_le_of_normal_ne_bot α hAn hAc hgen N h))

end CFSG.GroupActions
