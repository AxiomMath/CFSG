module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

@[expose] def InvolutionsCommute (Y : Type) [Group Y] : Prop :=
  ∀ u a : Y, orderOf u = 2 → orderOf a = 2 →
    ∃ h : Y, (h * u * h⁻¹) * a = a * (h * u * h⁻¹)

variable {Y : Type} [Group Y]

omit [Group Y] in
theorem isPGroup_zpowers_of_mul_self_eq_one {Y : Type} [Group Y] {z : Y} (hz : z * z = 1) :
    IsPGroup 2 (zpowers z) := by
  by_cases h1 : z = 1
  · exact IsPGroup.of_card (n := 0) (by simp [h1])
  · have h2 : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) h1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])

variable [Finite Y]

theorem mem_sylow_of_forall_comm (P : Sylow 2 Y) {z : Y} (hz : z * z = 1)
    (hc : ∀ p ∈ (P : Subgroup Y), p * z = z * p) : z ∈ (P : Subgroup Y) := by
  have hnorm : zpowers z ≤ normalizer (P : Subgroup Y) := by
    rw [zpowers_le]
    have hz' : z ∈ centralizer ((P : Subgroup Y) : Set Y) := mem_centralizer_iff.2 hc
    exact centralizer_le_normalizer (P : Subgroup Y) hz'
  have hsup := (isPGroup_zpowers_of_mul_self_eq_one hz).to_sup_of_normal_right'
    (P.isPGroup' : IsPGroup 2 (P : Subgroup Y)) hnorm
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have hPQ : (P : Subgroup Y) ≤ Q := le_trans le_sup_right hQ
  have hcard : Nat.card (Q : Subgroup Y) ≤ Nat.card (P : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have heq : (P : Subgroup Y) = Q := Subgroup.eq_of_le_of_card_ge hPQ hcard
  rw [heq]
  exact le_trans (le_sup_left : zpowers z ≤ zpowers z ⊔ P) hQ (mem_zpowers z)

theorem exists_mem_sylow_conj (P : Sylow 2 Y) {a : Y} (ha : a * a = 1) :
    ∃ g : Y, ∃ p ∈ (P : Subgroup Y), g * p * g⁻¹ = a := by
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_mul_self_eq_one ha).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P Q
  have haQ : a ∈ (Q : Subgroup Y) := hQ (mem_zpowers a)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at haQ
  obtain ⟨p, hp, hpa⟩ := haQ
  exact ⟨g, p, hp, by simpa [MulAut.smul_def, MulAut.conj_apply] using hpa⟩

theorem exists_conj_commute_of_mem_sylow (P : Sylow 2 Y) {z : Y}
    (hz : ∀ p ∈ (P : Subgroup Y), p * z = z * p) {a : Y} (ha : a * a = 1) :
    ∃ h : Y, (h * z * h⁻¹) * a = a * (h * z * h⁻¹) := by
  obtain ⟨g, p, hp, rfl⟩ := exists_mem_sylow_conj P ha
  refine ⟨g, ?_⟩
  have := hz p hp
  calc g * z * g⁻¹ * (g * p * g⁻¹) = g * (z * p) * g⁻¹ := by group
    _ = g * (p * z) * g⁻¹ := by rw [this]
    _ = g * p * g⁻¹ * (g * z * g⁻¹) := by group

theorem exists_conj_commute_of_le_centralizer (P : Sylow 2 Y) {a : Y}
    (hP : ∀ p ∈ (P : Subgroup Y), p * a = a * p) {u : Y} (hu : u * u = 1) :
    ∃ h : Y, (h * u * h⁻¹) * a = a * (h * u * h⁻¹) := by
  obtain ⟨g, p, hp, rfl⟩ := exists_mem_sylow_conj P hu
  refine ⟨g⁻¹, ?_⟩
  have e : g⁻¹ * (g * p * g⁻¹) * g⁻¹⁻¹ = p := by group
  rw [e]
  exact hP p hp

theorem exists_involution_mem_center_sylow (P : Sylow 2 Y) (hY : 2 ∣ Nat.card Y) :
    ∃ z : Y, z ∈ (P : Subgroup Y) ∧ (∀ p ∈ (P : Subgroup Y), p * z = z * p) ∧ orderOf z = 2 := by
  have hP : IsPGroup 2 (P : Subgroup Y) := P.isPGroup'
  have hntP : Nontrivial (P : Subgroup Y) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
    have hc : Nat.card (P : Subgroup Y) = 2 ^ (Nat.card Y).factorization 2 :=
      Sylow.card_eq_multiplicity P
    have h1 : Nat.card (P : Subgroup Y) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h1] at hc
    have hpos : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have : 1 ≤ (Nat.card Y).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos).1 hY
    have h3 : 2 ^ 1 ≤ 2 ^ (Nat.card Y).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) this
    omega
  have hcn : Nontrivial (center (P : Subgroup Y)) := hP.center_nontrivial
  have hc : IsPGroup 2 (center (P : Subgroup Y)) := hP.to_subgroup _
  have hdvd : 2 ∣ Nat.card (center (P : Subgroup Y)) := by
    rcases hc.card_eq_or_dvd with h | h
    · exfalso
      exact not_subsingleton _ (Nat.card_eq_one_iff_unique.1 h).1
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center (P : Subgroup Y)) 2 hdvd
  refine ⟨(((x : (P : Subgroup Y))) : Y), (x : (P : Subgroup Y)).2, fun p hp => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 x.2 ⟨p, hp⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx

omit [Finite Y] in
theorem mul_self_eq_one_of_orderOf_eq_two' {x : Y} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

theorem involutionsCommute_aux (P : Sylow 2 Y) {z r r' : Y}
    (hzc : ∀ p ∈ (P : Subgroup Y), p * z = z * p) (hzr : IsConj z r)
    (hcov : ∀ x : Y, orderOf x = 2 → IsConj x r ∨ IsConj x r') {u a : Y}
    (hu : orderOf u = 2) (ha : orderOf a = 2) :
    ∃ h : Y, (h * u * h⁻¹) * a = a * (h * u * h⁻¹) := by
  by_cases hu' : IsConj u z
  · obtain ⟨c, hc⟩ := isConj_iff.1 hu'
    obtain ⟨h₁, hh₁⟩ :=
      exists_conj_commute_of_mem_sylow P hzc (mul_self_eq_one_of_orderOf_eq_two' ha)
    refine ⟨h₁ * c, ?_⟩
    have e : h₁ * c * u * (h₁ * c)⁻¹ = h₁ * z * h₁⁻¹ := by
      rw [← hc]; group
    rw [e]
    exact hh₁
  by_cases ha' : IsConj a z
  · obtain ⟨c, hc⟩ := isConj_iff.1 ha'
    obtain ⟨h₂, hh₂⟩ := exists_conj_commute_of_le_centralizer P (a := z) hzc
      (mul_self_eq_one_of_orderOf_eq_two' hu)
    refine ⟨c⁻¹ * h₂, ?_⟩
    have ea : a = c⁻¹ * z * c := by rw [← hc]; group
    have e : c⁻¹ * h₂ * u * (c⁻¹ * h₂)⁻¹ = c⁻¹ * (h₂ * u * h₂⁻¹) * c := by group
    rw [e, ea]
    calc c⁻¹ * (h₂ * u * h₂⁻¹) * c * (c⁻¹ * z * c) = c⁻¹ * ((h₂ * u * h₂⁻¹) * z) * c := by group
      _ = c⁻¹ * (z * (h₂ * u * h₂⁻¹)) * c := by rw [hh₂]
      _ = c⁻¹ * z * c * (c⁻¹ * (h₂ * u * h₂⁻¹) * c) := by group
  · have hu'' : IsConj u r' := (hcov u hu).resolve_left fun h => hu' (h.trans hzr.symm)
    have ha'' : IsConj a r' := (hcov a ha).resolve_left fun h => ha' (h.trans hzr.symm)
    obtain ⟨c, hc⟩ := isConj_iff.1 (hu''.trans ha''.symm)
    exact ⟨c, by rw [hc]⟩

theorem involutionsCommute_of_two_classes {r₁ r₂ : Y}
    (hcov : ∀ x : Y, orderOf x = 2 → IsConj x r₁ ∨ IsConj x r₂) (h1 : orderOf r₁ = 2) :
    InvolutionsCommute Y := by
  intro u a hu ha
  obtain P : Sylow 2 Y := default
  have hY : 2 ∣ Nat.card Y := h1 ▸ orderOf_dvd_natCard r₁
  obtain ⟨z, -, hzc, hz2⟩ := exists_involution_mem_center_sylow P hY
  rcases hcov z hz2 with hz | hz
  · exact involutionsCommute_aux P hzc hz hcov hu ha
  · exact involutionsCommute_aux P hzc hz (fun x hx => (hcov x hx).symm) hu ha

theorem centerInvolutionsAt_of_sylow (P : Sylow 2 Y) {a : Y}
    (hP : ∀ p ∈ (P : Subgroup Y), p * a = a * p)
    (hZ : ∀ z ∈ (P : Subgroup Y), (∀ p ∈ (P : Subgroup Y), p * z = z * p) → z = 1 ∨ z = a)
    {z : Y} (hzz : z * z = 1) (hzc : ∀ y : Y, y * a = a * y → z * y = y * z) :
    z = 1 ∨ z = a := by
  have hc : ∀ p ∈ (P : Subgroup Y), p * z = z * p := fun p hp => (hzc p (hP p hp)).symm
  exact hZ z (mem_sylow_of_forall_comm P hzz hc) hc

end CFSG.EvenSporadicStandard.Solomon78
