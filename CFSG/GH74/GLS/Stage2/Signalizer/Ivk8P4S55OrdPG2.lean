module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPL
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Main
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts

namespace OrdPG2

theorem pow_apply_eq_self {G : Type*} [Group G] {φ : MulAut G} {v : G} (h : φ v = v) (j : ℕ) :
    (φ ^ j) v = v := by
  induction j with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

end OrdPG2


namespace OrdPG2

theorem ordP_g2 {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut ↥(adjointGroup Tag.G2 K)) (hα : orderOf α = p) :
    OrdPConcl r ↥(adjointGroup Tag.G2 K) α := by
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hr hf hK
  by_cases hinn : IsInnerAut α
  · exact Or.inr hinn
  left
  obtain ⟨-, i, δ, τ, -, hτord, hδ⟩ :=
    Stage2.Bender.Thm1.g2_field_descent hr hr2 hf K hK hp (hp.odd_of_ne_two hp2) hα hinn
  have hi : ¬ p ∣ i := by
    rintro ⟨m, rfl⟩
    have h1 : g2FieldHom K τ = 1 := by
      rw [← hδ, pow_mul, ← hα, pow_orderOf_eq_one, one_pow, mul_one, mul_inv_cancel]
    have hτ1 : τ = 1 :=
      Stage2.Bender.Thm1.g2FieldHom_faithful hr hr2 hf K hK τ ⟨1, by rw [h1, map_one]⟩
    rw [hτ1, orderOf_one] at hτord
    exact hp.one_lt.ne hτord
  set v : ↥(adjointGroup Tag.G2 K) := δ⁻¹ (StepH3G2.rootElt K) with hvdef
  have hfix_i : (α ^ i) v = v := by
    have h1 : (δ * α ^ i * δ⁻¹) (StepH3G2.rootElt K) = StepH3G2.rootElt K := by
      rw [hδ]
      exact StepH3G2.g2FieldHom_xUnit_one τ
    rw [MulAut.mul_apply, MulAut.mul_apply] at h1
    rw [hvdef]
    apply δ.injective
    rw [h1, MulAut.apply_inv_self]
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime (x := α) (n := i)
    (by rw [hα]; exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi)))
  have hfix : α v = v := by
    have h1 := pow_apply_eq_self hfix_i j
    rwa [hj] at h1
  have hvo : orderOf v = r := by
    rw [hvdef, MulEquiv.orderOf_eq, StepH3G2.orderOf_rootElt]
  refine ⟨zpowers v, ?_, ?_, ?_⟩
  · intro h
    have h1 : v = 1 := by
      have : v ∈ zpowers v := mem_zpowers v
      rwa [h, mem_bot] at this
    rw [h1, orderOf_one] at hvo
    exact hr.one_lt.ne hvo
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvo, pow_one])
  · intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow, hfix]
    exact zpow_mem (mem_zpowers v) n

end OrdPG2

theorem ordPInner_fg2d : OrdPInner FG2d := by
  intro r p Y _ _ hr hr2 hp hp5 _ hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Stage2.Bender.Thm1.exists_mulEquiv_adjoint_of_lieModel hLM
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPG2.ordP_g2 hr hr2 hf hK hp (by omega) _
    ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
