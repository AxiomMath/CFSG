module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TightEnd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Member

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

@[expose] def TwinExclusion : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ClassicalCommuteBelow F → ClassicalQuasisimple F →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z →
      ¬ (Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) → False

@[expose] def TwinPairExclusion : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ClassicalCommuteBelow F → ClassicalQuasisimple F →
    ∀ (K K' : Subgroup F) (z : F), IsClassical2A7 ⊤ K z → IsClassical2A7 ⊤ K' z → K' ≠ K →
      (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) → False

section Assembly

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem center_trivial_of_simple [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) :
    ∀ x : F, (∀ y : F, x * y = y * x) → x = 1 := by
  intro x hx
  have hnormal : (Subgroup.center F).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · have : x ∈ Subgroup.center F := Subgroup.mem_center_iff.mpr fun y => (hx y).symm
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center F := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

omit [Finite F] in
theorem exists_twin_of_not_tight [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (ht : ¬ Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) :
    ∃ K' : Subgroup F, IsClassical2A7 ⊤ K' z ∧ K' ≠ K ∧ ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
  obtain ⟨g, hg, hgK⟩ := Set.not_subset.mp ht
  have hgz : g * z * g⁻¹ = z := by
    have h1 : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z rfl
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h1]
      _ = z := mul_inv_cancel_right z g
  have hK' : IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) z := by
    have h1 := hK.conj g
    have htop : (⊤ : Subgroup F).map (MulAut.conj g).toMonoidHom = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
    rwa [htop, hgz] at h1
  have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := by
    intro h
    apply (show g ∉ Subgroup.normalizer (K : Set F) from hgK)
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h] at this
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have : y = x := by simpa using hyx'
      rwa [← this]
  have hY : Subgroup.centralizer ({z} : Set F) ≠ ⊤ := by
    intro h
    have hz1 : z = 1 := center_trivial_of_simple hnab z (fun y => by
      have hy : y ∈ Subgroup.centralizer ({z} : Set F) := h ▸ Subgroup.mem_top y
      exact Subgroup.mem_centralizer_iff.mp hy z rfl)
    have := hK.orderOf_eq_two
    rw [hz1, orderOf_one] at this
    omega
  refine ⟨K.map (MulAut.conj g).toMonoidHom, hK', hne, ?_⟩
  rcases IH z hK.orderOf_eq_two hY K _ z z (hK.mono hK.le_centralizer le_top)
      (hK'.mono hK'.le_centralizer le_top) with h | h
  · exact absurd h.symm hne
  · exact h

omit [Finite F] in
theorem twinExclusion_of_pair (h : TwinPairExclusion) : TwinExclusion := by
  intro F _ _ _ hnab IH P1 K z hK ht
  obtain ⟨K', hK', hne, hcomm⟩ := exists_twin_of_not_tight hnab IH hK ht
  exact h F hnab IH P1 K K' z hK hK' hne hcomm

theorem false_of_classical2A7 [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)
    (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) : False := by
  by_cases ht : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)
  · exact TightSetting.false_of_goldschmidt hnab GS
      ⟨⟨hK, ht⟩, center_trivial_of_simple hnab, IH, P1⟩
  · exact TW F hnab IH P1 K z hK ht

theorem false_of_witness [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)
    (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion) {z : F} (hz : orderOf z = 2)
    {K : Subgroup F} (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer ({z} : Set F)))
    (hw : A7Witness K) : False := by
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK hw
  exact false_of_classical2A7 hnab IH P1 GS TW hL

theorem cit2A7_of_inputs (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion)
    (IHP : ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
      (∃ (L : Subgroup F) (u : F), IsClassical2A7 ⊤ L u) →
      ClassicalCommuteBelow F ∧ ClassicalQuasisimple F) : CIT2A7 := by
  intro F _ _ _ hnab z hz K hzK hK _ _ h
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK h.2
  obtain ⟨IH, P1⟩ := IHP F hnab ⟨L, z, hL⟩
  exact (false_of_classical2A7 hnab IH P1 GS TW hL).elim

end Assembly

end CFSG.ClassicalInvolution.Hat2A7
