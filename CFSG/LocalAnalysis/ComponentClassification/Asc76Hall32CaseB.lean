module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Basic
public import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Defs

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

theorem eq_or_of_card_four {T : Subgroup G} (hT4 : Nat.card T = 4) (hTsq : ∀ x ∈ T, x ^ 2 = 1)
    {z a : G} (hz : z ∈ T) (ha : a ∈ T) (hz1 : z ≠ 1) (ha1 : a ≠ 1) (haz : a ≠ z) {x : G}
    (hx : x ∈ T) : x = 1 ∨ x = z ∨ x = a ∨ x = a * z := by
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hTsq z hz)
  have h1 : a * z ≠ 1 := fun h => haz (by rw [← hzz]; exact eq_inv_of_mul_eq_one_left h)
  have h2 : a * z ≠ z := fun h => ha1 (by simpa using h)
  have h3 : a * z ≠ a := fun h => hz1 (by simpa using h)
  by_contra hne
  push Not at hne
  obtain ⟨hx1, hxz, hxa, hxaz⟩ := hne
  have hsub : ({x, 1, z, a, a * z} : Set G) ⊆ T := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact one_mem T
    · exact hz
    · exact ha
    · exact mul_mem ha hz
  have hx' : x ∉ ({1, z, a, a * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1, hxz, hxa, hxaz⟩
  have h1' : (1 : G) ∉ ({z, a, a * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, ha1.symm, h1.symm⟩
  have hz' : z ∉ ({a, a * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨haz.symm, h2.symm⟩
  have h5 : ({x, 1, z, a, a * z} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem hx', Set.ncard_insert_of_notMem h1',
      Set.ncard_insert_of_notMem hz', Set.ncard_pair h3.symm]
  have h7 : (T : Set G).ncard = 4 := hT4
  have h6 := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero (by rw [h7]; norm_num))
  omega

theorem mem_centralizer_of_comm {T : Subgroup G} (hT4 : Nat.card T = 4)
    (hTsq : ∀ x ∈ T, x ^ 2 = 1) {z a : G} (hz : z ∈ T) (ha : a ∈ T) (hz1 : z ≠ 1) (ha1 : a ≠ 1)
    (haz : a ≠ z) {q : G} (hqz : z * q = q * z) (hqa : a * q = q * a) :
    q ∈ centralizer (T : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  rcases eq_or_of_card_four hT4 hTsq hz ha hz1 ha1 haz hx with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hqz
  · exact hqa
  · rw [mul_assoc, hqz, ← mul_assoc, hqa, mul_assoc]

variable [Finite G]

theorem nonempty_mulEquiv_dihedral {P T : Subgroup G} (hP : IsPGroup 2 P) (hTP : T ≤ P)
    (hPN : P ≤ normalizer (T : Set G)) (hT4 : Nat.card T = 4) (hTsq : ∀ x ∈ T, x ^ 2 = 1)
    (hC : P ⊓ centralizer (T : Set G) ≤ T) {u : G} (huP : u ∈ P)
    (huC : u ∉ centralizer (T : Set G)) (hu2 : u ^ 2 = 1) : Nonempty (P ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 : T ≠ ⊥ := fun h => by
    rw [h, card_bot] at hT4
    norm_num at hT4
  obtain ⟨⟨z, hzmem⟩, hz1⟩ :=
    ne_bot_iff_exists_ne_one.mp (CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hP hTP hPN hT1)
  rw [mem_inf, mem_inf] at hzmem
  obtain ⟨hzT, -, hzC⟩ := hzmem
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzc : ∀ p ∈ P, p * z = z * p := fun p hp => mem_centralizer_iff.mp hzC p hp
  obtain ⟨a, haT, hau⟩ : ∃ a ∈ T, a * u ≠ u * a := by
    by_contra h
    push Not at h
    exact huC (mem_centralizer_iff.mpr h)
  have ha1 : a ≠ 1 := fun h => hau (by rw [h, one_mul, mul_one])
  have huz : u * z = z * u := hzc u huP
  have haz : a ≠ z := fun h => hau (by rw [h]; exact huz.symm)
  have hbT : u * a * u⁻¹ ∈ T := (mem_normalizer_iff.mp (hPN huP) a).mp haT
  have hb : u * a * u⁻¹ = a * z := by
    rcases eq_or_of_card_four hT4 hTsq hzT haT hz1' ha1 haz hbT with h | h | h | h
    · exact absurd (conj_eq_one_iff.mp h) ha1
    · refine absurd ?_ haz
      calc a = u⁻¹ * (u * a * u⁻¹) * u := by group
        _ = u⁻¹ * (u * z) := by rw [h, huz, mul_assoc]
        _ = z := by group
    · refine absurd ?_ hau
      calc a * u = u * a * u⁻¹ * u := by rw [h]
        _ = u * a := by group
    · exact h
  have e1 : u * z * u⁻¹ = z := by rw [huz]; group
  have hzz : z * z = 1 := by rw [← sq]; exact hTsq z hzT
  have hsplit : ∀ p ∈ P, p ∈ centralizer (T : Set G) ∨ u * p ∈ centralizer (T : Set G) := by
    intro p hp
    have hpz : p * z = z * p := hzc p hp
    have hcT : p * a * p⁻¹ ∈ T := (mem_normalizer_iff.mp (hPN hp) a).mp haT
    rcases eq_or_of_card_four hT4 hTsq hzT haT hz1' ha1 haz hcT with h | h | h | h
    · exact absurd (conj_eq_one_iff.mp h) ha1
    · refine absurd ?_ haz
      calc a = p⁻¹ * (p * a * p⁻¹) * p := by group
        _ = p⁻¹ * (p * z) := by rw [h, hpz, mul_assoc]
        _ = z := by group
    · left
      refine mem_centralizer_of_comm hT4 hTsq hzT haT hz1' ha1 haz hpz.symm ?_
      calc a * p = p * a * p⁻¹ * p := by rw [h]
        _ = p * a := by group
    · right
      have e2 : (u * p) * a * (u * p)⁻¹ = a := by
        calc (u * p) * a * (u * p)⁻¹ = u * (p * a * p⁻¹) * u⁻¹ := by group
          _ = u * (a * z) * u⁻¹ := by rw [h]
          _ = (u * a * u⁻¹) * (u * z * u⁻¹) := by group
          _ = a * (z * z) := by rw [hb, e1, mul_assoc]
          _ = a := by rw [hzz, mul_one]
      refine mem_centralizer_of_comm hT4 hTsq hzT haT hz1' ha1 haz ?_ ?_
      · calc z * (u * p) = (u * z) * p := by rw [huz, mul_assoc]
          _ = u * p * z := by rw [mul_assoc, ← hpz, ← mul_assoc]
      · calc a * (u * p) = (u * p) * a * (u * p)⁻¹ * (u * p) := by rw [e2]
          _ = (u * p) * a := by group
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hu2)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hTsq a haT)
  have hρP : a * u ∈ P := mul_mem (hTP haT) huP
  have hρ2 : (a * u) ^ 2 = z := by
    calc (a * u) ^ 2 = a * (u * a * u⁻¹) * (u * u) := by rw [sq]; group
      _ = a * (a * z) * (u ^ 2) := by rw [hb, ← sq]
      _ = z := by rw [hu2, mul_one, ← mul_assoc, ← sq, hTsq a haT, one_mul]
  have hρord : orderOf (a * u) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a * u)
      (by rw [pow_one, hρ2]; exact hz1') (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul,
        hρ2, sq, hzz])
    rw [h]
    norm_num
  have hrel : u * (a * u) * u⁻¹ = (a * u)⁻¹ := by
    calc u * (a * u) * u⁻¹ = u * a := by group
      _ = u⁻¹ * a⁻¹ := by rw [hui, hai]
      _ = (a * u)⁻¹ := (mul_inv_rev a u).symm
  have hσρ : u ∉ zpowers (a * u) := by
    intro hu
    have ha' : a ∈ zpowers (a * u) := by
      have h := mul_mem (mem_zpowers (a * u)) (inv_mem hu)
      rwa [mul_inv_cancel_right] at h
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp ha'
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hu
    have hc : Commute ((a * u) ^ i) ((a * u) ^ j) := Commute.zpow_zpow_self (a * u) i j
    rw [hi, hj] at hc
    exact hau hc.eq
  have hgenG : P ≤ zpowers (a * u) ⊔ zpowers u := by
    set H := zpowers (a * u) ⊔ zpowers u with hHdef
    have huH : u ∈ H := mem_sup_right (mem_zpowers u)
    have haH : a ∈ H := by
      have h := mul_mem (mem_sup_left (mem_zpowers (a * u)) : a * u ∈ H) (inv_mem huH)
      rwa [mul_inv_cancel_right] at h
    have hzH : z ∈ H := by
      rw [← hρ2]
      exact pow_mem (mem_sup_left (mem_zpowers (a * u))) 2
    have hTH : T ≤ H := fun x hx => by
      rcases eq_or_of_card_four hT4 hTsq hzT haT hz1' ha1 haz hx with rfl | rfl | rfl | rfl
      · exact one_mem H
      · exact hzH
      · exact haH
      · exact mul_mem haH hzH
    intro p hp
    rcases hsplit p hp with h | h
    · exact hTH (hC (mem_inf.mpr ⟨hp, h⟩))
    · have h1 : u * p ∈ H := hTH (hC (mem_inf.mpr ⟨mul_mem huP hp, h⟩))
      have h2 := mul_mem (inv_mem huH) h1
      rwa [inv_mul_cancel_left] at h2
  have hgen : ⊤ = zpowers (⟨a * u, hρP⟩ : P) ⊔ zpowers (⟨u, huP⟩ : P) := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    rw [← mem_map_iff_mem P.subtype_injective, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    exact hgenG x.2
  have hσ2 : (⟨u, huP⟩ : P) ^ 2 = 1 := Subtype.ext hu2
  have hrel' : (⟨u, huP⟩ : P) * ⟨a * u, hρP⟩ * (⟨u, huP⟩ : P)⁻¹ = (⟨a * u, hρP⟩ : P)⁻¹ :=
    Subtype.ext hrel
  have hσρ' : (⟨u, huP⟩ : P) ∉ zpowers (⟨a * u, hρP⟩ : P) := fun h => hσρ (by
    have h1 := (mem_map_iff_mem P.subtype_injective).mpr h
    rwa [MonoidHom.map_zpowers] at h1)
  have hord : orderOf (⟨a * u, hρP⟩ : P) = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact hρord
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem _ _ hgen hσ2 hrel' hσρ'
  rw [hord] at e
  exact ⟨e⟩

theorem forall_dihedral_of_core (hcore : Hall32Core)
    (IH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → Hall32For H)
    {S T : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hT4 : Nat.card T = 4)
    (hTel : IsElemAbelian 2 T) (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hns : ∃ t ∈ T, ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ∉ T) :
    ∀ P : Subgroup G, IsSylowOf 2 P (normalClosure (T : Set G)) →
      Nonempty (P ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalClosure (T : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hTM : T ≤ M := subset_normalClosure
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 : (⟨a, ha⟩ : ↥T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hTel.1.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  have hTsq : ∀ x ∈ T, x ^ 2 = 1 := hTel.2
  obtain ⟨t₀, ht₀, m₀, hm₀, hm₀S, hm₀T⟩ :=
    exists_conj_of_not_stronglyClosed hS hTS hwc hMn hTM hns
  have hcardM : Nat.card (BarGroup M) ≤ Nat.card G :=
    (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)).trans (card_le_card_group M)
  have hcore' := hcore (BarGroup M) (fun H _ _ hH => IH H (hH.trans_le hcardM)) (bar M S)
    (bar M T) (isSylowOf_bar hMn hS) (bar_mono hTS) (by rw [card_bar_of_pGroup hTM hT2, hT4])
    (isElemAbelian_of_mulEquiv (barEquiv hTM hT2) hTel) (bar_weaklyClosed hS2 hMn hTM hT2 hwc)
    (bar_not_stronglyClosed hS2 hTS hTM ht₀ hm₀ hm₀S hm₀T)
    (normalClosure_bar_eq_top (normalClosure_subgroupOf_eq_top hS hTS hwc))
    (eq_bot_of_normal_of_odd_bar M)
  have hC : S ⊓ M ⊓ centralizer (T : Set G) ≤ T := inf_centralizer_le_of_bar hS2 hTS hcore'
  obtain ⟨t, ht, g, hgS, hgT⟩ := hns
  have hgM : g⁻¹ * t * g ∈ M := by
    have h1 := hMn.conj_mem t (hTM ht) g⁻¹
    rwa [inv_inv] at h1
  have huC : g⁻¹ * t * g ∉ centralizer (T : Set G) := fun h =>
    hgT (conj_mem_of_mem_centralizer hS hTS hTab hwc ht h)
  have hu2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    have e := conj_pow (a := g⁻¹) (b := t) (i := 2)
    rw [inv_inv] at e
    rw [e, hTsq t ht, mul_one, inv_mul_cancel]
  have hSM : IsSylowOf 2 (S ⊓ M) M :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hMn]) hS
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedral hSM.isPGroup (le_inf hTS hTM)
    (inf_le_left.trans (le_normalizer_of_weaklyClosed hTS hwc)) hT4 hTsq hC
    (mem_inf.mpr ⟨hgS, hgM⟩) huC hu2
  intro P hP
  obtain ⟨m, -, rfl⟩ := exists_conj_of_isSylowOf hSM hP
  exact ⟨((S ⊓ M).equivMapOfInjective (MulAut.conj m⁻¹).toMonoidHom
    (MulAut.conj m⁻¹).injective).symm.trans e⟩

end CFSG.ComponentClassification.Asc76X.Hall32
