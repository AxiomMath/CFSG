module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag

variable {r f : ℕ} {K : Type} [Field K]

theorem finite_mulAut_hypPSU (h : UnitaryFieldData r f K) (a ε : ℕ) :
    Finite (MulAut (hypPSU h a ε)) := by
  have := h.finite
  exact Finite.of_injective (fun α : MulAut (hypPSU h a ε) => (α : hypPSU h a ε → hypPSU h a ε))
    fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)

theorem unitary_nonabelian_projective_plane_overgroup_rank_three (h : UnitaryFieldData r f K)
    {p a : ℕ} (hp : p.Prime) (hpa : p = 2 * a + 1) (ha : 1 ≤ a) (hq : p = 3 → 2 < r ^ f)
    (D : Subgroup (MulAut (hypPSU h a 1))) (hDI : D ≤ linearSimAutGroup h ha le_rfl)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (linearSimAut h ha le_rfl), ∀ B ∈ D.comap (linearSimAut h ha le_rfl),
      A * B = B * A)
    (E : Subgroup (MulAut (hypPSU h a 1))) (hDE : D ≤ E)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1) :
    E ⊓ linearSimAutGroup h ha le_rfl = D ∧ ∃ k ≤ 3, Nat.card E = p ^ k := by
  have := finite_mulAut_hypPSU h a 1
  have hn : 3 ≤ 2 * a + 1 := by omega
  have hqa : ¬(2 * a + 1 = 3 ∧ r ^ f = 2) := fun ⟨h3, h2⟩ => by
    have := hq (by omega)
    omega
  obtain ⟨-, hcentI, -⟩ :=
    linearSimAut_plane h ha le_rfl hn hp hpa.symm D hDI hDab hDp hcard hna
  have hEI : E ⊓ linearSimAutGroup h ha le_rfl = D := by
    apply le_antisymm
    · rintro x ⟨hxE, hxI⟩
      exact hcentI x hxI fun d hd => hEab d (hDE hd) x hxE
    · exact le_inf hDE hDI
  refine ⟨hEI, ?_⟩
  have hker := ker_autFieldPart h ha le_rfl hn hqa
  let ψ : E →* (K ≃+* K) := (autFieldPart h ha le_rfl hn hqa).comp E.subtype
  have hkerψ : ψ.ker = D.subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, ← hEI]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hkercard : Nat.card ψ.ker = p ^ 2 := by
    rw [hkerψ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hcard]
  have := unitaryFieldAut_isCyclic h
  have hrangecard : Nat.card ψ.range ≤ p := by
    have hexp : Monoid.exponent ψ.range ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => by
        obtain ⟨_, x, rfl⟩ := y
        ext1
        rw [SubmonoidClass.coe_pow, ← map_pow, show x ^ p = 1 from Subtype.ext (by
          rw [SubmonoidClass.coe_pow]; exact hEp x x.2), map_one]
        rfl
    have := h.finite
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  have hEcard : Nat.card E ≤ p ^ 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard]
    calc Nat.card ψ.range * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hrangecard
      _ = p ^ 3 := by ring
  have hpg : IsPGroup p E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hEp x x.2)⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  refine ⟨k, ?_, hk⟩
  rw [hk] at hEcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hEcard

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
