module

public import CFSG.GH74.AS16.E2.Outer4
public import CFSG.GH74.AS16.E2.OuterChecks
public import CFSG.GH74.AS16.E2.Local3Models
public import CFSG.GH74.AS16.E2.Tables
public import CFSG.GH74.KGroups.L33Tables
public meta import CFSG.GH74.AS16.E2.OuterChecks
public meta import CFSG.GH74.KGroups.L33Tables
public import Certificates.Certificate5000
public import Certificates.Certificate5001
public import Certificates.Certificate5120
public import Certificates.Certificate5121
public import CFSG.GH74.AS16.E2.Data3
public meta import CFSG.GH74.AS16.E2.Delta3

public section

namespace CFSG.GH74.AS16.E2

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74.KGroups
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.Uniqueness (S_CorZD)

theorem l33_outCent3 :
    ∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ L33.QP.originalSubgroup →
      ∀ ψ ∈ L33.QA.originalSubgroup, (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * τ = τ * c →
        ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ :=
  Certificates.certificate5001.1

theorem l33_bang :
    ∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ L33.QP.originalSubgroup →
      ∃ l ∈ L33.QP.originalSubgroup, ∃ c₁ ∈ L33.QP.originalSubgroup,
        ∃ c₂ ∈ L33.QP.originalSubgroup, c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧
        c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧
        τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂ :=
  Certificates.certificate5001.2.1

theorem l33_innerSq :
    ∀ v ∈ L33.QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ L33.QA.originalSubgroup,
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ L33.QP.originalSubgroup → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v) :=
  Certificates.certificate5001.2.2.1

theorem l33_cyc :
    ∀ v ∈ L33.QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∃ φ ∈ L33.QA.originalSubgroup,
      ∀ ψ ∈ L33.QA.originalSubgroup, (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 →
        c * v = v * c → ψ * c = c * ψ) → ∃ k : ℕ, ψ = φ ^ k :=
  Certificates.certificate5001.2.2.2.1

theorem l33_sylCent :
    ∀ ψ ∈ L33.QA.originalSubgroup, (∀ q ∈ L33.QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ L33.QS.originalSubgroup :=
  Certificates.certificate5001.2.2.2.2.1

theorem l33_word :
    ∃ a ∈ L33.QP.originalSubgroup, ∃ b ∈ L33.QP.originalSubgroup, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a * L33.s0 = L33.s0 * a ∧ b * L33.s0 = L33.s0 * b ∧
      (a * b) ^ 3 = L33.s0 :=
  Certificates.certificate5001.2.2.2.2.2.1

theorem l33_sylSq :
    ∀ ψ ∈ L33.QA.originalSubgroup, ψ ∉ L33.QP.originalSubgroup →
      (∀ q ∈ L33.QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ L33.QS.originalSubgroup) →
      ∀ v ∈ L33.QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ L33.QS.originalSubgroup, q * v = v * q :=
  Certificates.certificate5001.2.2.2.2.2.2.1

theorem l33_conj4 :
    ∀ a ∈ L33.QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ L33.QP.originalSubgroup, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ L33.QP.originalSubgroup, k⁻¹ * a * k ∈ L33.QS.originalSubgroup ∧
        ∀ y ∈ L33.QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y :=
  Certificates.certificate5001.2.2.2.2.2.2.2

theorem l33_le : L33.QP.originalSubgroup ≤ L33.QA.originalSubgroup := by
  have hA : L33.QA.originalSubgroup =
      Subgroup.closure {g | g ∈ [L33.PA, L33.PB, L33.sg0]} := by
    rw [L33.QA, certificate_originalSubgroup]
  rw [L33.QP_closure, Subgroup.closure_le, hA]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp

theorem l33_model
    {K : Type} [Group K] (hK : ShapeL33 K) :
    ∃ M : AutModel K (Equiv.Perm (Fin 26)), M.P = L33.QP.originalSubgroup ∧
      M.A = L33.QA.originalSubgroup ∧ M.P ≤ M.A ∧ Nonempty (K ≃* L33.QP.originalSubgroup) := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  refine ⟨M, hP, hA, ?_, ⟨e⟩⟩
  rw [hP, hA]
  exact l33_le

theorem outerTable_L33
    {K : Type} [Group K] (hK : ShapeL33 K) : OuterTable K := by
  obtain ⟨M, hP, hA, hPA, -⟩ := l33_model hK
  refine outerTable_of_model M hPA ?_ ?_ ?_
  · rw [hA, hP]
    exact l33_outCent3
  · rw [hA, hP]
    exact l33_bang
  · rw [hA, hP]
    exact l33_innerSq

theorem outerCycTable_L33
    {K : Type} [Group K] (hK : ShapeL33 K) : OuterCycTable K := by
  obtain ⟨M, hP, hA, hPA, -⟩ := l33_model hK
  refine outerCycTable_of_model M hPA ?_
  rw [hA, hP]
  exact l33_cyc

theorem outerSylowTable_L33
    {K : Type} [Group K] (hK : ShapeL33 K) (Q : Subgroup K)
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) : OuterSylowTable K Q := by
  obtain ⟨M, hP, hA, hPA, ⟨e⟩⟩ := l33_model hK
  have : Finite K := L33.finite_K' e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP : L33.QS.originalSubgroup ≤ M.P := by
    rw [hP]
    exact L33.QS_le
  obtain ⟨e', he'⟩ := exists_iso_of_sylow M.P M.e L33.QS.originalSubgroup hSP L33.card_S
    (L33.card_K e) (by decide) (hQ.toSylow hQi)
  have hs := smallCheck_sound L33.QS L33.QS_ok L33.small_ok
  have hcent : ∀ ψ ∈ M.A, (∀ q ∈ L33.QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ L33.QS.originalSubgroup := by
    rw [hA]
    exact l33_sylCent
  have hword : ∃ a ∈ M.P, ∃ b ∈ M.P, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a * L33.s0 = L33.s0 * a ∧ b * L33.s0 = L33.s0 * b ∧ (a * b) ^ 3 = L33.s0 := by
    rw [hP]
    exact l33_word
  have hsq : ∀ ψ ∈ M.A, ψ ∉ M.P →
      (∀ q ∈ L33.QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ L33.QS.originalSubgroup) →
      ∀ v ∈ L33.QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ M.P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ L33.QS.originalSubgroup, q * v = v * q := by
    rw [hA, hP]
    exact l33_sylSq
  have hconj4 : ∀ a ∈ L33.QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ M.P, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ M.P, k⁻¹ * a * k ∈ L33.QS.originalSubgroup ∧
        ∀ y ∈ L33.QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y := by
    rw [hP]
    exact l33_conj4
  exact outerSylowTable_of_model (AM.twist M e') hPA hSP he'
    ⟨L33.s0, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2, hcent, hword⟩ hsq hconj4

theorem rank3Data_L33 :
    Rank3Data ShapeL33 := by
  intro K _ _ hK
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  exact ⟨⟨(local3Data_L33 K hK).elemAb9, (local3Data_L33 K hK).exists3⟩, L33.inner3 e⟩

theorem noPairL33Outer_of
    (hZD : S_CorZD) (hD3 : K0Data3) (hS : SmallData ShapeL33) :
    NoPairL33Outer := by
  intro G _ _ T z L hcfg hterm hsh _
  have hZ : Subgroup.center ↥L = ⊥ := hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inl hsh))))
  have hR3 : Rank3Sub L := Rank3Sub.of_table (rank3Data_L33 ↥L hsh).1 (rank3Data_L33 ↥L hsh).2
  have hO : OuterSub L := OuterSub.of_table (outerTable_L33 hsh)
  have hSyl : OuterSylow L ((T : Subgroup G) ⊓ L) := by
    have hsyl := hcfg.isSylowOf_inf
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
    exact OuterSylow.of_table inf_le_right
      (outerSylowTable_L33 hsh _ hsyl.2.1.comap_subtype hsyl.2.2)
  exact hcfg.false_of_outer hZD hterm hZ hR3 hO (hcfg.smallTable hS hsh) hSyl
    (Or.inr (OuterCyc.of_table (outerCycTable_L33 hsh)))

end CFSG.GH74.AS16.E2
