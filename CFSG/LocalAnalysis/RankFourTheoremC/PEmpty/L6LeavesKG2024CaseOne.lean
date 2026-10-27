module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Cycle

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Equiv Equiv.Perm Subgroup CFSG.Open

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem three_dvd_factorial_div_two {m : ℕ} (hm : 5 ≤ m) : 3 ∣ m.factorial / 2 := by
  have h3 : 3 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have e : m.factorial = 2 * (m.factorial / 2) := (Nat.mul_div_cancel' h2).symm
  rw [e] at h3
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3

theorem case_one {p : ℕ} {z : Perm Ω} (hp : p.Prime) (hp5 : 5 ≤ p) (hz : orderOf z = p)
    (hn : Fintype.card Ω < 2 * p) (T : Subgroup (Perm Ω))
    (hfix : ∀ x, z x ≠ x → ∀ t ∈ T, t x = x) :
    ∃ Y : Subgroup (Perm Ω), Y ≤ alternatingGroup Ω ∧ Y ≤ normalizer (T : Set (Perm Ω)) ∧
      z ∈ Y ∧ S622IsSimpleSection Y ⊥ ∧ 3 ∣ Nat.card ↥Y := by
  classical
  set F : Set Ω := {x | ∀ t ∈ T, t x = x} with hF
  have hsupp := card_support_eq hp hz hn
  have hSF : ∀ x, z x ≠ x → x ∈ F := fun x hx t ht => hfix x hx t ht
  have hzF : ∀ x, z x ∈ F ↔ x ∈ F := by
    intro x
    constructor
    · intro hx
      by_cases h : z x = x
      · rwa [h] at hx
      · exact hSF x h
    · intro hx
      by_cases h : z x = x
      · rwa [h]
      · exact hSF (z x) (fun h' => h (z.injective h'))
  have hFcard : 5 ≤ Nat.card ↥F := by
    have hsub : (z.support : Set Ω) ⊆ F := fun x hx =>
      hSF x (Equiv.Perm.mem_support.1 (Finset.mem_coe.1 hx))
    have := Set.ncard_le_ncard hsub (Set.toFinite F)
    rw [Set.ncard_coe_finset, hsupp] at this
    rw [Nat.card_coe_set_eq]
    omega
  haveI : Nontrivial ↥F := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  haveI hsimpleF : IsSimpleGroup ↥(alternatingGroup ↥F) := alternatingGroup.isSimpleGroup hFcard
  have hinj : Function.Injective (Equiv.Perm.ofSubtype (p := fun x => x ∈ F)) :=
    Equiv.Perm.ofSubtype_injective
  let Y : Subgroup (Perm Ω) := (alternatingGroup ↥F).map Equiv.Perm.ofSubtype
  let e : ↥(alternatingGroup ↥F) ≃* ↥Y := (alternatingGroup ↥F).equivMapOfInjective _ hinj
  have hYsimple : IsSimpleGroup ↥Y := e.symm.isSimpleGroup
  have hYalt : Y ≤ alternatingGroup Ω := by
    rintro _ ⟨σ, hσ, rfl⟩
    have hσ' : σ ∈ alternatingGroup ↥F := hσ
    rw [mem_alternatingGroup] at hσ' ⊢
    rw [Equiv.Perm.sign_ofSubtype]
    exact hσ'
  have hYcomm : ∀ y ∈ Y, ∀ t ∈ T, y * t = t * y := by
    rintro _ ⟨σ, -, rfl⟩ t ht
    refine (Equiv.Perm.Disjoint.commute fun x => ?_)
    by_cases hx : x ∈ F
    · exact Or.inr (hx t ht)
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem σ hx)
  have hsignz : Perm.sign z = 1 :=
    sign_eq_one_of_pow_eq_one (hp.odd_of_ne_two (by omega)) (hz ▸ pow_orderOf_eq_one z)
  have hzY : z ∈ Y := by
    have hz' : ∀ x, (fun x => x ∈ F) (z x) ↔ (fun x => x ∈ F) x := hzF
    refine ⟨z.subtypePerm hz', ?_, Equiv.Perm.ofSubtype_subtypePerm hz' hSF⟩
    show z.subtypePerm hz' ∈ alternatingGroup ↥F
    rw [mem_alternatingGroup]
    have := Equiv.Perm.sign_ofSubtype (z.subtypePerm hz')
    rw [Equiv.Perm.ofSubtype_subtypePerm hz' hSF, hsignz] at this
    exact this.symm
  have hcardY : Nat.card ↥Y = (Nat.card ↥F).factorial / 2 := by
    rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  have h3Y : 3 ∣ Nat.card ↥Y := by
    rw [hcardY]
    exact three_dvd_factorial_div_two hFcard
  have hpY : p ∣ Nat.card ↥Y := by
    have := Subgroup.orderOf_dvd_natCard Y hzY
    rwa [hz] at this
  exact ⟨Y, hYalt, fun y hy => mem_normalizer_of_commute (fun t ht => hYcomm y hy t ht), hzY,
    isSimpleSection_bot hYsimple hp5 hpY h3Y, h3Y⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
