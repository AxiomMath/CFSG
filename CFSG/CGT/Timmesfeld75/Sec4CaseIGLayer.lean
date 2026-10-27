module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGCenter
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGold

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open CFSG.Goldschmidt

@[expose] def Sec4I5NoLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SimpleCaseUpTo (Nat.card G) →
    ∀ (T T₁ T₂ : Subgroup G) (a : G), Sec4Hyp T T₁ a T₂ →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      Sec4FourHolds T T₁ T₂ → Sec4PlusHolds T T₁ T₂ →
        goldschmidtLayer (↥(Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T))) ⧸
          goldschmidtOddCore ↥(Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)))) = ⊥

section Normal

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.conjSubgroup_sec4R_eq_of_normal_sec4A (_h : Sec4Hyp T T₁ a T₂)
    (hA : (sec4A T T₁ T₂).Normal) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup g (sec4R T T₁ T₂) = sec4R T T₁ T₂ := by
  have hle : ∀ x ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup x (sec4R T T₁ T₂) ≤ sec4R T T₁ T₂ := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ sec4R T T₁ T₂, y = x * r * x⁻¹ :=
      ⟨x⁻¹ * y * x, mem_conjSubgroup.1 hy, by group⟩
    have hrN := sec4R_le_normalizer_left hr
    have hyN : x * r * x⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hx hrN)
        ((Subgroup.normalizer (T : Set G)).inv_mem hx)
    have hrA : barElt T hrN ∈ sec4A T T₁ T₂ := barElt_mem_barSub hrN hr
    have hyA : barElt T hyN ∈ sec4A T T₁ T₂ := by
      have e : barElt T hyN = barElt T hx * barElt T hrN * (barElt T hx)⁻¹ := rfl
      rw [e]
      exact hA.conj_mem _ hrA (barElt T hx)
    obtain ⟨u, huN, huR, hut⟩ := (barElt_mem_barSub_iff hyN).1 hyA
    have e : x * r * x⁻¹ = u * (u⁻¹ * (x * r * x⁻¹)) := by group
    rw [e]
    exact (sec4R T T₁ T₂).mul_mem huR (left_le_sec4R hut)
  have hNle := le_normalizer_of_conjSubgroup_le (K := Subgroup.normalizer (T : Set G))
    (N := sec4R T T₁ T₂) hle
  exact mem_normalizer_iff_conjSubgroup_eq.1 (hNle hg)

end Normal

theorem sec4I5Goldschmidt_of_noLayer (hG : Goldschmidt1974) (hL : Sec4I5NoLayer) :
    Sec4I5Goldschmidt := by
  intro G _ _ _ hnab hind T T₁ T₂ a h hq h16 h4 hP g hg
  have hAab : IsElemAbelian 2 (sec4A T T₁ T₂) := h.isElemAbelian_sec4A
  obtain ⟨S, hAS⟩ := (isPGroup_two_of_isElemAbelian hAab).exists_le_sylow
  have hcl : ∀ x ∈ sec4A T T₁ T₂, ∀ k : NQuot T,
      k⁻¹ * x * k ∈ (S : Subgroup (NQuot T)) → k⁻¹ * x * k ∈ sec4A T T₁ T₂ :=
    fun x hx k hk => h.sec4A_stronglyClosed hP S.isPGroup' hAS hx k hk
  have hlayer := hL G hnab hind T T₁ T₂ a h hq h16 h4 hP
  have hcent : ∀ n ∈ oddCoreOf (Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T))),
      ∀ m ∈ Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)), m * n = n * m := by
    intro n hn m hm
    have hMn : (Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T))).Normal :=
      Subgroup.normalClosure_normal
    have : (oddCoreOf (Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)))).Normal :=
      oddCoreOf_normal hMn
    exact h.oddNormal_comm_normalClosure hq _
      (odd_card_oddCoreOf (Subgroup.normalClosure (sec4A T T₁ T₂ : Set (NQuot T)))) n hn m hm
  have hAn : (sec4A T T₁ T₂).Normal :=
    normal_of_goldschmidt_of_no_layer hG S (sec4A T T₁ T₂) hAS hAab.1 hcl hlayer hcent
  have hgR : g ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.2 (h.conjSubgroup_sec4R_eq_of_normal_sec4A hAn hg)
  exact h.conjSubgroup_normIn_eq hg hgR

end CFSG.CGT.Timmesfeld75
