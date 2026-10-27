module

public import CFSG.CGT.PushingUp.CampbellPair
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {P Q : Subgroup G} (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q)
    (hne : P ≠ Q) : ∃ x ∈ Q, x ∈ Subgroup.normalizer (P : Set G) ∧ x ∉ P := by
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hPQ ?_)
    intro x hx
    have : (⟨x, hx⟩ : ↥Q) ∈ P.subgroupOf Q := by
      rw [h]
      trivial
    exact this
  obtain ⟨x, hxn, hxnot⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨x, x.2, ?_, fun hx => hxnot hx⟩
  have : x ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ]
    exact hxn
  exact this

omit [Finite G] in
theorem le_centralizer_of_le_omegaOneCenterIn {T T₂ : Subgroup G}
    (hT₂ : T₂ ≤ omegaOneCenterIn T) : T ≤ Subgroup.centralizer (T₂ : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨-, hc, -⟩ := mem_omegaOneCenterIn_iff.mp (hT₂ hx)
  exact (hc t ht).symm

theorem even_card_of_isPGroup_le {T M : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTM : T ≤ M) : Even (Nat.card M) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hT1
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hk
  have h2 : 2 ∣ Nat.card T := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hTM))

omit [Finite G] in
theorem not_map_conj_le {M H : Subgroup G} (hHM : ¬ H ≤ M) {m : G} (hm : m ∈ M) :
    ¬ H.map (MulAut.conj m).toMonoidHom ≤ M := by
  intro h
  apply hHM
  intro x hx
  have h1 : m * x * m⁻¹ ∈ M := h ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm

omit [Finite G] in
theorem mem_map_conj_iff {R : Subgroup G} {m y : G} :
    y ∈ R.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * y * m ∈ R := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    show m⁻¹ * (m * x * m⁻¹) * m ∈ R
    rw [e]
    exact hx
  · intro h
    exact ⟨m⁻¹ * y * m, h, by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.CGT.PushingUp
