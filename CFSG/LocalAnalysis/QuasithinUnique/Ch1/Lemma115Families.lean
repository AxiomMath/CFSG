module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def AltList (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def OddList (X : Type) [Group X] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f) ∨
      StatedClassicalModel X .PSL 3 p 1 ∨ StatedClassicalModel X .PSU 3 p 1)

@[expose] def IsSQTKSporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
    s = .HS ∨ s = .He ∨ s = .Ru

@[expose] def SporadicList (X : Type) [Group X] : Prop :=
  ∃ s : TauCeti.SporadicName, IsSQTKSporadicName s ∧ Nonempty (X ≃* NativeSporadic.Carrier s)

@[expose] def EvenLieAutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SQTKCharTwoLie K → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
    (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

section Simple

variable {K : Type} [Group K] [Finite K] {β : K ≃* K}

theorem InvDatum.isSimpleGroup (h : InvDatum K β) (hz : Subgroup.center K = ⊥) : IsSimpleGroup K :=
  (mulEquivQuotientOfCenterEqBot hz).isSimpleGroup_congr.mpr h.simple_quotient

end Simple

theorem simpleInspection_charTwoList (hE : EvenLieAutInner) : SimpleInspection SQTKCharTwoLie := by
  intro K _ _ β h hz hK
  exact Or.inl ⟨h.isSimpleGroup hz, Or.inl hK, hE K hK β h.involutory h.sylow⟩

section Centralizer

variable {K : Type} [Group K] [Finite K] {β : K ≃* K}

omit [Finite K] in
theorem fixedSubgroup_eq_centralizer {l : K} (hl : ∀ x, β x = l⁻¹ * x * l) :
    fixedSubgroup β = Subgroup.centralizer ({l} : Set K) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_centralizer_singleton_iff, hl x]
  constructor
  · intro h
    calc x * l = l * (l⁻¹ * x * l) := by group
      _ = l * x := by rw [h]
  · intro h
    calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
      _ = l⁻¹ * (l * x) := by rw [h]
      _ = x := by group

theorem InvDatum.pCore_eq_bot (h : InvDatum K β) (hz : Subgroup.center K = ⊥) :
    CFSG.pCore 2 K = ⊥ := by
  rw [pCore_eq_center_of_isPGroup_center h.quasisimple (by rw [hz]; exact IsPGroup.of_bot), hz]

theorem InvDatum.involution_of_inner (h : InvDatum K β) (hz : Subgroup.center K = ⊥) {l : K}
    (hl : ∀ x, β x = l⁻¹ * x * l) : l ≠ 1 ∧ l * l = 1 := by
  obtain ⟨x, hx⟩ := h.nontrivial
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hx
    simp [hl x]
  refine ⟨hl1, ?_⟩
  have hcen : l * l ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h.involutory g
    rw [hl, hl] at h1
    calc g * (l * l) = l * l * (l⁻¹ * l⁻¹ * g * l * l) := by group
      _ = l * l * g := by
        rw [show l⁻¹ * l⁻¹ * g * l * l = l⁻¹ * (l⁻¹ * g * l) * l by group, h1]
  rw [hz, Subgroup.mem_bot] at hcen
  exact hcen

end Centralizer

end CFSG.QuasithinUnique.Ch1
