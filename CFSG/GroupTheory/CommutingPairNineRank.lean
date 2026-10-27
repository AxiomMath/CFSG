module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {H : Type*} [Group H] [Finite H]

theorem exists_elemAbelian_card_eightyOne_of_commuting_pair
    {C₁ C₂ E₁ E₂ : Subgroup H} {x₁ x₂ : H}
    (hcomm : ∀ a ∈ C₁, ∀ b ∈ C₂, a * b = b * a)
    (hE₁ : E₁ ≤ C₁) (hE₂ : E₂ ≤ C₂)
    (hE₁el : CFSG.Open.IsElemAbelian 3 E₁) (hE₂el : CFSG.Open.IsElemAbelian 3 E₂)
    (hE₁c : Nat.card E₁ = 9) (hE₂c : Nat.card E₂ = 9)
    (hx₁ : x₁ ∈ C₁) (hx₂ : x₂ ∈ C₂) (hx₁o : orderOf x₁ = 9) (hx₂o : orderOf x₂ = 9)
    (hx₁E : ∀ e ∈ E₁, e * x₁ = x₁ * e) (hx₂E : ∀ e ∈ E₂, e * x₂ = x₂ * e)
    (hinter : C₁ ⊓ C₂ = ⊥ ∨
      (Nat.card ↥(C₁ ⊓ C₂) = 3 ∧ x₁ ^ 3 ∈ C₁ ⊓ C₂ ∧ x₂ ^ 3 ∈ C₁ ⊓ C₂)) :
    ∃ F : Subgroup H, CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 4 := by
  rcases hinter with hbot | ⟨hDcard, hx₁D, hx₂D⟩
  · refine ⟨E₁ ⊔ E₂, hE₁el.sup_of_commute hE₂el ?_, ?_⟩
    · intro a ha b hb
      exact hcomm a (hE₁ ha) b (hE₂ hb)
    · have hcent : E₂ ≤ Subgroup.centralizer (E₁ : Set H) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hcomm a (hE₁ ha) b (hE₂ hb)
      have hnorm : E₂ ≤ Subgroup.normalizer (E₁ : Set H) :=
        hcent.trans (Subgroup.centralizer_le_normalizer (E₁ : Set H))
      have hdisj : E₁ ⊓ E₂ = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        have hmem : a ∈ C₁ ⊓ C₂ := ⟨hE₁ ha.1, hE₂ ha.2⟩
        rw [hbot] at hmem
        exact hmem
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        E₁ E₂ hnorm (disjoint_iff.mpr hdisj)
      rw [hcard, hE₁c, hE₂c]
      norm_num
  · let D : Subgroup H := C₁ ⊓ C₂
    have hDcard' : Nat.card ↥D = 3 := hDcard
    have hx₁D' : x₁ ^ 3 ∈ D := hx₁D
    have hx₂D' : x₂ ^ 3 ∈ D := hx₂D
    have hx₁3ne : x₁ ^ 3 ≠ 1 := by
      intro h
      have hdvd : orderOf x₁ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hx₁o] at hdvd
      norm_num at hdvd
    have hx₂3ne : x₂ ^ 3 ≠ 1 := by
      intro h
      have hdvd : orderOf x₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hx₂o] at hdvd
      norm_num at hdvd
    have hx₁3o : orderOf (x₁ ^ 3) = 3 := by
      rw [orderOf_pow, hx₁o]
      norm_num
    have hzDle : Subgroup.zpowers (x₁ ^ 3) ≤ D := Subgroup.zpowers_le.mpr hx₁D'
    have hzDcard : Nat.card ↥(Subgroup.zpowers (x₁ ^ 3)) = 3 := by
      rw [Nat.card_zpowers, hx₁3o]
    have hzD : Subgroup.zpowers (x₁ ^ 3) = D :=
      Subgroup.eq_of_le_of_card_ge hzDle (by rw [hDcard', hzDcard])
    have hx₂zp : x₂ ^ 3 ∈ Subgroup.zpowers (x₁ ^ 3) := by
      rw [hzD]
      exact hx₂D'
    have hx₂3cases :=
      eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hx₁3o hx₂zp hx₂3ne
    obtain ⟨z, hzC₂, hzE₂, hz3⟩ : ∃ z : H, z ∈ C₂ ∧
        (∀ a ∈ E₂, a * z = z * a) ∧ z ^ 3 = (x₁ ^ 3)⁻¹ := by
      rcases hx₂3cases with h | h
      · refine ⟨x₂⁻¹, C₂.inv_mem hx₂, ?_, ?_⟩
        · intro a ha
          exact Commute.inv_right (hx₂E a ha)
        · rw [inv_pow, h]
      · exact ⟨x₂, hx₂, hx₂E, h⟩
    let y : H := x₁ * z
    have hydef : y = x₁ * z := rfl
    have hcz : Commute x₁ z := hcomm x₁ hx₁ z hzC₂
    have hy3 : y ^ 3 = 1 := by
      rw [hydef, Commute.mul_pow hcz, hz3, mul_inv_cancel]
    have hyC₂ : y ∉ C₂ := by
      intro hy
      have hx₁C₂ : x₁ ∈ C₂ := by
        have hmem : y * z⁻¹ ∈ C₂ := C₂.mul_mem hy (C₂.inv_mem hzC₂)
        have hyz : y * z⁻¹ = x₁ := by
          rw [hydef]
          group
        rwa [hyz] at hmem
      have hx₁Dmem : x₁ ∈ D := ⟨hx₁, hx₁C₂⟩
      have hdvd := Subgroup.orderOf_dvd_natCard D hx₁Dmem
      rw [hDcard', hx₁o] at hdvd
      norm_num at hdvd
    have hy1 : y ≠ 1 := fun h => hyC₂ (h ▸ C₂.one_mem)
    have hyo : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h
    have hE₂notle : ¬ E₂ ≤ D := by
      intro hle
      have hcard : Nat.card ↥E₂ ≤ Nat.card ↥D :=
        Nat.card_le_card_of_injective (fun e : ↥E₂ => (⟨e.1, hle e.2⟩ : ↥D))
          (fun e f hef => Subtype.ext (congrArg (fun z : ↥D => (z : H)) hef))
      rw [hE₂c, hDcard'] at hcard
      norm_num at hcard
    obtain ⟨e₂, he₂E, he₂D⟩ := SetLike.not_le_iff_exists.mp hE₂notle
    have he₂3 : e₂ ^ 3 = 1 := hE₂el.2 e₂ he₂E
    have he₂1 : e₂ ≠ 1 := fun h => he₂D (h ▸ D.one_mem)
    have he₂o : orderOf e₂ = 3 := by
      have hdvd : orderOf e₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr he₂3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) he₂1
      · exact h
    have he₂card : Nat.card ↥(Subgroup.zpowers e₂) = 3 := by
      rw [Nat.card_zpowers, he₂o]
    have hycard : Nat.card ↥(Subgroup.zpowers y) = 3 := by
      rw [Nat.card_zpowers, hyo]
    have he₂x₁ : e₂ * x₁ = x₁ * e₂ := (hcomm x₁ hx₁ e₂ (hE₂ he₂E)).symm
    have he₂z : e₂ * z = z * e₂ := hzE₂ e₂ he₂E
    have he₂y : e₂ * y = y * e₂ := by
      rw [hydef]
      calc e₂ * (x₁ * z) = e₂ * x₁ * z := by group
        _ = x₁ * e₂ * z := by rw [he₂x₁]
        _ = x₁ * (e₂ * z) := by group
        _ = x₁ * (z * e₂) := by rw [he₂z]
        _ = x₁ * z * e₂ := by group
    have hcomm_zp : ∀ u ∈ Subgroup.zpowers e₂, ∀ v ∈ Subgroup.zpowers y,
        u * v = v * u := by
      intro u hu v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact Commute.zpow_zpow he₂y m n
    have hdisj_zy : Subgroup.zpowers e₂ ⊓ Subgroup.zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      by_contra hu1
      have hu_e := eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three he₂o hu.1 hu1
      have hu_y := eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hyo hu.2 hu1
      rcases hu_e with h | h <;> rcases hu_y with h' | h'
      · exact hyC₂ (h' ▸ h ▸ hE₂ he₂E)
      · have hyinv : y⁻¹ ∈ C₂ := h' ▸ h ▸ hE₂ he₂E
        exact hyC₂ (by rw [← inv_inv y]; exact C₂.inv_mem hyinv)
      · exact hyC₂ (h' ▸ h ▸ C₂.inv_mem (hE₂ he₂E))
      · have hyinv : y⁻¹ ∈ C₂ := h' ▸ h ▸ C₂.inv_mem (hE₂ he₂E)
        exact hyC₂ (by rw [← inv_inv y]; exact C₂.inv_mem hyinv)
    have hF₂ea : IsElemAbelian 3 (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) :=
      (CFSG.Open.isElemAbelian_zpowers he₂3).sup_of_commute
        (CFSG.Open.isElemAbelian_zpowers hy3) hcomm_zp
    have hF₂card : Nat.card ↥(Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) = 9 := by
      have hcent : Subgroup.zpowers y ≤ Subgroup.centralizer (Subgroup.zpowers e₂ : Set H) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hcomm_zp a ha b hb
      have hnorm : Subgroup.zpowers y ≤
          Subgroup.normalizer (Subgroup.zpowers e₂ : Set H) :=
        hcent.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers e₂ : Set H))
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (Subgroup.zpowers e₂) (Subgroup.zpowers y) hnorm (disjoint_iff.mpr hdisj_zy),
        he₂card, hycard]
    have hF₂C₁ : (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) ⊓ C₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm_zp hxF
      have haE : a ∈ E₂ := (Subgroup.zpowers_le.mpr he₂E) ha
      by_cases hb1 : b = 1
      · rw [hb1, mul_one] at hxC ⊢
        have haD : a ∈ D := ⟨hxC, hE₂ haE⟩
        by_contra ha1
        have ha3 : a ^ 3 = 1 := by
          rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three he₂o ha ha1 with h | h
          · rw [h, he₂3]
          · rw [h, inv_pow, he₂3]
            simp
        have hao : orderOf a = 3 := by
          have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha3
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) ha1
          · exact h
        have hacard : Nat.card ↥(Subgroup.zpowers a) = 3 := by
          rw [Nat.card_zpowers, hao]
        have hZaD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.mpr haD
        have hZaD' : Subgroup.zpowers a = D :=
          Subgroup.eq_of_le_of_card_ge hZaD (by rw [hDcard', hacard])
        have hZae : Subgroup.zpowers a ≤ Subgroup.zpowers e₂ := Subgroup.zpowers_le.mpr ha
        have hZae' : Subgroup.zpowers a = Subgroup.zpowers e₂ :=
          Subgroup.eq_of_le_of_card_ge hZae (by rw [he₂card, hacard])
        exact he₂D (hZaD' ▸ hZae' ▸ Subgroup.mem_zpowers e₂)
      · have hb_cases := eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hyo hb hb1
        rcases hb_cases with hby | hby
        · rw [hby] at hxC
          have hzx : z * x₁⁻¹ = x₁⁻¹ * z := Commute.inv_right hcz.symm
          have hxy : a * y * x₁⁻¹ = a * z := by
            rw [hydef]
            calc a * (x₁ * z) * x₁⁻¹ = a * x₁ * z * x₁⁻¹ := by group
              _ = a * x₁ * (z * x₁⁻¹) := by group
              _ = a * x₁ * (x₁⁻¹ * z) := by rw [hzx]
              _ = a * z := by group
          have huC₂ : a * z ∈ C₂ := C₂.mul_mem (hE₂ haE) hzC₂
          have huD : a * z ∈ D := by
            refine ⟨?_, huC₂⟩
            rw [← hxy]
            exact C₁.mul_mem hxC (C₁.inv_mem hx₁)
          have hu3 : (a * z) ^ 3 = 1 := by
            have hdvd := Subgroup.orderOf_dvd_natCard D huD
            rw [hDcard'] at hdvd
            exact orderOf_dvd_iff_pow_eq_one.mp hdvd
          have hu3' : (a * z) ^ 3 = (x₁ ^ 3)⁻¹ := by
            rw [Commute.mul_pow (hzE₂ a haE), hE₂el.2 a haE, one_mul, hz3]
          rw [hu3'] at hu3
          exfalso
          exact hx₁3ne (inv_eq_one.mp hu3)
        · rw [hby] at hxC
          have hxy : a * y⁻¹ * x₁ = a * z⁻¹ := by
            rw [hydef]
            group
          have huC₂ : a * z⁻¹ ∈ C₂ := C₂.mul_mem (hE₂ haE) (C₂.inv_mem hzC₂)
          have huD : a * z⁻¹ ∈ D := by
            refine ⟨?_, huC₂⟩
            rw [← hxy]
            exact C₁.mul_mem hxC hx₁
          have hu3 : (a * z⁻¹) ^ 3 = 1 := by
            have hdvd := Subgroup.orderOf_dvd_natCard D huD
            rw [hDcard'] at hdvd
            exact orderOf_dvd_iff_pow_eq_one.mp hdvd
          have hu3' : (a * z⁻¹) ^ 3 = x₁ ^ 3 := by
            rw [Commute.mul_pow (Commute.inv_right (hzE₂ a haE)), hE₂el.2 a haE, one_mul,
              inv_pow, hz3, inv_inv]
          rw [hu3'] at hu3
          exfalso
          exact hx₁3ne hu3
    have hE₁z : ∀ a ∈ E₁, a * z = z * a := fun a ha => hcomm a (hE₁ ha) z hzC₂
    have hE₁y : ∀ a ∈ E₁, a * y = y * a := by
      intro a ha
      rw [hydef]
      calc a * (x₁ * z) = a * x₁ * z := by group
        _ = x₁ * a * z := by rw [hx₁E a ha]
        _ = x₁ * (a * z) := by group
        _ = x₁ * (z * a) := by rw [hE₁z a ha]
        _ = x₁ * z * a := by group
    have hE₁F₂comm : ∀ a ∈ E₁, ∀ b ∈ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y),
        a * b = b * a := by
      intro a ha b hb
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm_zp hb
      have hau : a * u = u * a := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact Commute.zpow_right (hcomm a (hE₁ ha) e₂ (hE₂ he₂E)) m
      have hav : a * v = v * a := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact Commute.zpow_right (hE₁y a ha) n
      calc a * (u * v) = a * u * v := by group
        _ = u * a * v := by rw [hau]
        _ = u * (a * v) := by group
        _ = u * (v * a) := by rw [hav]
        _ = u * v * a := by group
    have hE₁F₂ea : IsElemAbelian 3 (E₁ ⊔ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y)) :=
      hE₁el.sup_of_commute hF₂ea hE₁F₂comm
    have hE₁disj : E₁ ⊓ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      have hamin : a ∈ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) ⊓ C₁ :=
        ⟨ha.2, hE₁ ha.1⟩
      rw [hF₂C₁] at hamin
      simpa using hamin
    refine ⟨E₁ ⊔ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y), hE₁F₂ea, ?_⟩
    have hcent : (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) ≤
        Subgroup.centralizer (E₁ : Set H) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hE₁F₂comm a ha b hb
    have hnorm : (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) ≤
        Subgroup.normalizer (E₁ : Set H) :=
      hcent.trans (Subgroup.centralizer_le_normalizer (E₁ : Set H))
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      E₁ (Subgroup.zpowers e₂ ⊔ Subgroup.zpowers y) hnorm (disjoint_iff.mpr hE₁disj)
    rw [hcard, hE₁c, hF₂card]
    norm_num

end CFSG.GroupTheory
