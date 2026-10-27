module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryOvergroup
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag LinearFlag UnitaryHigher

section Linear

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem finite_mulAut_projectiveSL (n : ℕ) : Finite (MulAut (projectiveSL n F)) :=
  Finite.of_injective (fun α : MulAut (projectiveSL n F) => (α : projectiveSL n F → _))
    fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)

theorem conjAut_eq_one_iff {n : ℕ} (hn : 3 ≤ n) (A : GL (Fin n) F) :
    conjAut n F A = 1 ↔ ∃ u : Fˣ, A = GeneralLinearGroup.scalar (Fin n) u := by
  constructor
  · intro h
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h])
    exact ⟨c, hc.symm⟩
  · rintro ⟨u, rfl⟩
    exact conjAut_scalar u

theorem linearAutGroup_plane (hp : p.Prime) (hp3 : 3 ≤ p) (D : Subgroup (MulAut (projectiveSL p F)))
    (hDI : D ≤ linearAutGroup p F) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (conjAut p F), ∀ B ∈ D.comap (conjAut p F), A * B = B * A) :
    ringChar F ≠ p ∧ (∀ x ∈ linearAutGroup p F, (∀ d ∈ D, d * x = x * d) → x ∈ D) ∧
      ∀ A B : GL (Fin p) F, Subgroup.closure {conjAut p F A, conjAut p F B} = D →
        ∃ ζ : F, IsPrimitiveRoot ζ p ∧
          (A : Matrix (Fin p) (Fin p) F) * B = ζ • ((B : Matrix (Fin p) (Fin p) F) * A) := by
  rw [linearAutGroup_eq_range] at hDI ⊢
  exact plane_transport hp (conjAut p F) (MonoidHom.id _) Function.injective_id
    (conjAut_eq_one_iff hp3) D hDI hDab hDp hcard hna

theorem linear_projective_nonabelian_plane_coprime_centralizer_central (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (projectiveSL p F))) (hDI : D ≤ linearAutGroup p F)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (conjAut p F), ∀ B ∈ D.comap (conjAut p F), A * B = B * A) :
    (linearAutGroup p F).Normal ∧
      (∀ a b : MulAut (projectiveSL p F), a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup p F) ∧
      Subgroup.centralizer (D : Set (MulAut (projectiveSL p F))) ⊓ linearAutGroup p F = D ∧
      D ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (projectiveSL p F)))) ∧
      (∀ a ∈ Subgroup.centralizer (D : Set (MulAut (projectiveSL p F))),
        ∀ b ∈ Subgroup.centralizer (D : Set (MulAut (projectiveSL p F))),
          a * b * a⁻¹ * b⁻¹ ∈ D) ∧
      (∀ Y : Subgroup (MulAut (projectiveSL p F)),
        Y ≤ Subgroup.centralizer (D : Set (MulAut (projectiveSL p F))) →
          Nat.Coprime p (Nat.card Y) →
            Y ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (projectiveSL p F))))) ∧
      ∀ H : Subgroup (MulAut (projectiveSL p F)), D ≤ H →
        localDelta p H D ≤
          centerOf (Subgroup.centralizer (D : Set (MulAut (projectiveSL p F)))) := by
  have := finite_mulAut_projectiveSL (F := F) p
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcomm := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
    (K := F) hp3
  obtain ⟨-, hcent, -⟩ := linearAutGroup_plane hp hp3 D hDI hDab hDp hcard hna
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    coprime_centralizer_central hp (linearAutGroup p F) D hcomm hDI hDab hDp hcent
  have hD : D ≠ ⊥ := fun hD => by
    rw [hD, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  exact ⟨normal_of_commutator_mem hcomm, hcomm, h1, h2, h3, h4, h5 hD⟩

end Linear

section Unitary

variable {r f : ℕ} {K : Type} [Field K]

theorem unitary_projective_nonabelian_plane_coprime_centralizer_central
    (h : UnitaryFieldData r f K) {p a : ℕ} (hp : p.Prime) (hpa : p = 2 * a + 1) (ha : 1 ≤ a)
    (hq : p = 3 → 2 < r ^ f) (D : Subgroup (MulAut (hypPSU h a 1)))
    (hDI : D ≤ linearSimAutGroup h ha le_rfl) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (linearSimAut h ha le_rfl), ∀ B ∈ D.comap (linearSimAut h ha le_rfl),
      A * B = B * A) :
    (linearSimAutGroup h ha le_rfl).Normal ∧
      (∀ x y : MulAut (hypPSU h a 1), x * y * x⁻¹ * y⁻¹ ∈ linearSimAutGroup h ha le_rfl) ∧
      Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))) ⊓ linearSimAutGroup h ha le_rfl =
        D ∧
      D ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1)))) ∧
      (∀ x ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
        ∀ y ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
          x * y * x⁻¹ * y⁻¹ ∈ D) ∧
      (∀ Y : Subgroup (MulAut (hypPSU h a 1)),
        Y ≤ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))) →
          Nat.Coprime p (Nat.card Y) →
            Y ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))))) ∧
      ∀ H : Subgroup (MulAut (hypPSU h a 1)), D ≤ H →
        localDelta p H D ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1)))) := by
  have := finite_mulAut_hypPSU h a 1
  have hn : 3 ≤ 2 * a + 1 := by omega
  have hqa : ¬(2 * a + 1 = 3 ∧ r ^ f = 2) := fun ⟨h3, h2⟩ => by
    have := hq (by omega)
    omega
  have hcomm := commutator_mem_linearSimAutGroup h ha le_rfl hn hqa
  obtain ⟨-, hcent, -⟩ := linearSimAut_plane h ha le_rfl hn hp hpa.symm D hDI hDab hDp hcard hna
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    coprime_centralizer_central hp (linearSimAutGroup h ha le_rfl) D hcomm hDI hDab hDp hcent
  have hD : D ≠ ⊥ := fun hD => by
    rw [hD, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  exact ⟨normal_of_commutator_mem hcomm, hcomm, h1, h2, h3, h4, h5 hD⟩

end Unitary

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
