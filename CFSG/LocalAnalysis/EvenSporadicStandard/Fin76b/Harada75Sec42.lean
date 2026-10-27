module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Lin

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Sec42

theorem sec42_comm {S : Type} [Group S] {H : Subgroup S} (hH : IsElemAbelian 2 H)
    {x y : S} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sec42_sq {S : Type} [Group S] {H : Subgroup S} (hH : IsElemAbelian 2 H)
    {x : S} (hx : x ∈ H) : x * x = 1 := by
  rw [← pow_two]
  exact hH.2 x hx

theorem sec42_dvd_eight {n : ℕ} (h : n ∣ 8) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> first | omega | (norm_num at h)

theorem sec42_exists_centralizer_ne_one {S : Type} [Group S] [Finite S] {A E : Subgroup S}
    (hA8 : Nat.card A = 8) (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hE8 : Nat.card E = 8)
    (hEn : E.Normal) : ∃ e ∈ E, e ≠ 1 ∧ ∀ a ∈ A, a * e = e * a := by
  letI : MulAction S E := conjMulAction hEn
  letI : MulAction A E := MulAction.compHom E A.subtype
  have hG : IsPGroup 2 A := IsPGroup.of_card (p := 2) (n := 3) (by norm_num [hA8])
  have hα : Nat.card E % 2 = 0 := by rw [hE8]
  obtain ⟨x, hx1, hxfix⟩ := exists_fixed_ne_of_even hG hα (1 : E) (fun g => cj_one_elem hEn _)
  have hx1' : (x : S) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcomm : ∀ a ∈ A, a * (x : S) = (x : S) * a := by
    intro a ha
    have h := congrArg Subtype.val (hxfix ⟨a, ha⟩)
    have h' : a * (x : S) * a⁻¹ = (x : S) := h
    exact mul_inv_eq_iff_eq_mul.mp h'
  exact ⟨(x : S), x.2, hx1', hcomm⟩

theorem sec42_coset_rep {S : Type} [Group S] [Finite S] {A H : Subgroup S}
    (hA8 : Nat.card A = 8) (hHA : H ≤ A) (hH4 : Nat.card H = 4) :
    ∃ c ∈ A, ∀ b ∈ A, (c * b ∈ H ↔ b ∉ H) := by
  have hcard : Nat.card (H.subgroupOf A) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv, hH4]
  have hmul := Subgroup.card_mul_index (H := H.subgroupOf A)
  rw [hcard, hA8] at hmul
  have hidx : (H.subgroupOf A).index = 2 := by omega
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff'.mp hidx
  refine ⟨(c : S), c.2, fun b hb => ?_⟩
  have hbc := hc ⟨b, hb⟩
  have e1 : (c * (⟨b, hb⟩ : A) ∈ H.subgroupOf A) ↔ ((c : S) * b ∈ H) := Iff.rfl
  have e2 : ((⟨b, hb⟩ : A) ∈ H.subgroupOf A) ↔ (b ∈ H) := Iff.rfl
  rw [e1, e2] at hbc
  rcases hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto

theorem inter_card_two_or_four {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {A E : Subgroup S} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hEn : E.Normal) (hne : A ≠ E) :
    Nat.card (A ⊓ E : Subgroup S) = 2 ∨ Nat.card (A ⊓ E : Subgroup S) = 4 := by
  obtain ⟨e, heE, he1, hfix⟩ := sec42_exists_centralizer_ne_one hA8 hCA hE8 hEn
  have heA : e ∈ A := hCA (Subgroup.mem_centralizer_iff.mpr fun h hh => hfix h hh)
  have hne1 : Nat.card (A ⊓ E : Subgroup S) ≠ 1 := by
    intro h1
    have hbot : A ⊓ E = ⊥ := Subgroup.eq_bot_of_card_eq (A ⊓ E : Subgroup S) h1
    have heZ : e ∈ A ⊓ E := Subgroup.mem_inf.mpr ⟨heA, heE⟩
    rw [hbot, Subgroup.mem_bot] at heZ
    exact he1 heZ
  have hne8 : Nat.card (A ⊓ E : Subgroup S) ≠ 8 := by
    intro h8
    have hAeq : A ⊓ E = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hEeq : A ⊓ E = E := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    exact hne (hAeq.symm.trans hEeq)
  have hdvd : Nat.card (A ⊓ E : Subgroup S) ∣ 8 := by
    rw [← hA8]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases sec42_dvd_eight hdvd with h | h | h | h <;> omega

theorem mem_of_centralizes_of_card_two {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {A E : Subgroup S} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hEn : E.Normal) (hAE2 : Nat.card (A ⊓ E : Subgroup S) = 2) :
    ∀ a ∈ A, (∀ e ∈ E, a * e = e * a) → a ∈ E := by
  intro a ha hac
  by_contra haE
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup S, H = A ⊓ Subgroup.centralizer (E : Set S) := ⟨_, rfl⟩
  have hmemH : ∀ x, x ∈ H ↔ x ∈ A ∧ x ∈ Subgroup.centralizer (E : Set S) := by
    intro x
    rw [hHdef, Subgroup.mem_inf]
  have hHA : H ≤ A := fun x hx => ((hmemH x).mp hx).1
  have hZH : A ⊓ E ≤ H := by
    intro z hz
    obtain ⟨hzA, hzE⟩ := Subgroup.mem_inf.mp hz
    refine (hmemH z).mpr ⟨hzA, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact sec42_comm hE hh hzE
  have haH : a ∈ H :=
    (hmemH a).mpr ⟨ha, Subgroup.mem_centralizer_iff.mpr fun h hh => (hac h hh).symm⟩
  have hcardH : 2 ≤ Nat.card H := by
    have := Subgroup.card_le_of_le hZH
    omega
  have hdvdH : Nat.card H ∣ 8 := by
    rw [← hA8]
    exact Subgroup.card_dvd_of_le hHA
  obtain ⟨b, hbA, hb⟩ : ∃ b ∈ A, ∀ x ∈ A, x ∈ H ∨ b * x ∈ H := by
    by_cases hall : ∀ x ∈ A, x ∈ H
    · exact ⟨1, Subgroup.one_mem A, fun x hx => Or.inl (hall x hx)⟩
    · push Not at hall
      obtain ⟨x₀, hx₀A, hx₀H⟩ := hall
      have hH8 : Nat.card H ≠ 8 := by
        intro h8
        have heq : H = A := Subgroup.eq_of_le_of_card_ge hHA (by omega)
        exact hx₀H (by rw [heq]; exact hx₀A)
      have hH2 : Nat.card H ≠ 2 := by
        intro h2
        have heq : A ⊓ E = H := Subgroup.eq_of_le_of_card_ge hZH (by omega)
        have haZ : a ∈ A ⊓ E := by rw [heq]; exact haH
        exact haE (Subgroup.mem_inf.mp haZ).2
      have hH4 : Nat.card H = 4 := by
        rcases sec42_dvd_eight hdvdH with h | h | h | h <;> omega
      obtain ⟨c, hcA, hc⟩ := sec42_coset_rep hA8 hHA hH4
      refine ⟨c, hcA, fun x hx => ?_⟩
      by_cases hxH : x ∈ H
      · exact Or.inl hxH
      · exact Or.inr ((hc x hx).mpr hxH)
  have hbb : b * b = 1 := sec42_sq hA hbA
  have hC : E ⊓ Subgroup.centralizer ({b} : Set S) ≤ A ⊓ E := by
    intro e he
    obtain ⟨heE, hec⟩ := Subgroup.mem_inf.mp he
    have hbe : b * e = e * b := (Subgroup.mem_centralizer_singleton_iff.mp hec).symm
    have hAe : ∀ x ∈ A, x * e = e * x := by
      intro x hx
      rcases hb x hx with hxH | hbxH
      · have hxc : x ∈ Subgroup.centralizer (E : Set S) := ((hmemH x).mp hxH).2
        exact ((Subgroup.mem_centralizer_iff.mp hxc) e heE).symm
      · have hbxc : b * x ∈ Subgroup.centralizer (E : Set S) := ((hmemH _).mp hbxH).2
        have h1 : (b * x) * e = e * (b * x) := ((Subgroup.mem_centralizer_iff.mp hbxc) e heE).symm
        calc x * e = (b * b) * x * e := by rw [hbb, one_mul]
          _ = b * ((b * x) * e) := by simp only [mul_assoc]
          _ = b * (e * (b * x)) := by rw [h1]
          _ = (b * e) * (b * x) := by simp only [mul_assoc]
          _ = (e * b) * (b * x) := by rw [hbe]
          _ = e * (b * (b * x)) := by simp only [mul_assoc]
          _ = e * x := by rw [← mul_assoc b b x, hbb, one_mul]
    have heA : e ∈ A := hCA (Subgroup.mem_centralizer_iff.mpr fun h hh => hAe h hh)
    exact Subgroup.mem_inf.mpr ⟨heA, heE⟩
  have hEb := card_le_card_fix_sq E (fun x hx y hy => sec42_comm hE hx hy)
    (fun x hx => sec42_sq hE hx) b (fun y hy => hEn.conj_mem y hy b)
    (fun y _ => by rw [hbb, one_mul, mul_one])
  have hle := Subgroup.card_le_of_le hC
  rw [hAE2] at hle
  have hsq : Nat.card (E ⊓ Subgroup.centralizer ({b} : Set S) : Subgroup S) ^ 2 ≤ 2 ^ 2 :=
    Nat.pow_le_pow_left hle 2
  have h8le : 8 ≤ 2 ^ 2 := by
    calc (8 : ℕ) = Nat.card E := hE8.symm
      _ ≤ _ := hEb
      _ ≤ 2 ^ 2 := hsq
  norm_num at h8le

end Sec42

end CFSG.EvenSporadicStandard.Fin76b
