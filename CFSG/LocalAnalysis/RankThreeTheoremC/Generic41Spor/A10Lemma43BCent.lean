module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BCP
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123

open CFSG.Open Subgroup

variable {Y : Type} [Group Y]

theorem coprime_trick {d w : Y} {W : Subgroup Y} (hW : IsPGroup 2 W) (hd5 : d ^ 5 = 1)
    (hdW : d ∈ normalizer (W : Set Y)) (hw : w ∈ W)
    (h : (d * w * d⁻¹ * w⁻¹) * d = d * (d * w * d⁻¹ * w⁻¹)) : d * w = w * d := by
  have hdw : d * w * d⁻¹ ∈ W := (mem_normalizer_iff.1 hdW w).1 hw
  have huW : d * w * d⁻¹ * w⁻¹ ∈ W := W.mul_mem hdw (W.inv_mem hw)
  generalize hu : d * w * d⁻¹ * w⁻¹ = u at h huW
  have hdwu : d * w * d⁻¹ = u * w := by rw [← hu]; group
  have hdu : d * u * d⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]; exact h.symm
  have key : ∀ k : ℕ, d ^ k * w * (d ^ k)⁻¹ = u ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : d ^ (k + 1) * w * (d ^ (k + 1))⁻¹ = d * (d ^ k * w * (d ^ k)⁻¹) * d⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e, ih]
      have e2 : d * (u ^ k * w) * d⁻¹ = (d * u ^ k * d⁻¹) * (d * w * d⁻¹) := by group
      rw [e2, ← conj_pow, hdu, hdwu, pow_succ]
      group
  have hu5 : u ^ 5 = 1 := by
    have h5 := key 5
    rw [hd5] at h5
    simpa using h5.symm
  obtain ⟨n, hn⟩ := hW ⟨u, huW⟩
  have hn' : u ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hu1 : u = 1 := by
    have h1 : orderOf u ∣ 5 := orderOf_dvd_of_pow_eq_one hu5
    have h2 : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h3 : Nat.Coprime 5 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have h4 : orderOf u ∣ Nat.gcd 5 (2 ^ n) := Nat.dvd_gcd h1 h2
    rw [h3.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  rw [hu1] at hu
  calc d * w = (d * w * d⁻¹ * w⁻¹) * (w * d) := by group
    _ = w * d := by rw [hu, one_mul]

variable [Finite Y] {J₁ J₂ : Subgroup Y} {t₁ t₂ : Y}

theorem W_centralizes (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (Q₁ : A5Quot J₁) (Q₂ : A5Quot J₂) (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5)
    (ho₂ : orderOf t₂ = 5) {W : Subgroup Y} (hW : IsPGroup 2 W)
    (hd : t₁ * t₂ ∈ normalizer (W : Set Y)) : ∀ y ∈ W, y * (t₁ * t₂) = (t₁ * t₂) * y := by
  have hc := comp_commute hJ₁ hJ₂ hne
  have hcomm12 : Commute t₁ t₂ := hc t₁ ht₁ t₂ ht₂
  have h51 : t₁ ^ 5 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one t₁
  have h52 : t₂ ^ 5 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one t₂
  have hd5 : (t₁ * t₂) ^ 5 = 1 := by rw [hcomm12.mul_pow, h51, h52, one_mul]
  intro y hy
  have hdy : (t₁ * t₂) * y * (t₁ * t₂)⁻¹ ∈ W := (mem_normalizer_iff.1 hd y).1 hy
  have huW : (t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹ ∈ W := W.mul_mem hdy (W.inv_mem hy)
  have hK₁ := comp_conj hJ₁ y
  have hK₂ := comp_conj hJ₂ y
  have hy₁ : y * t₁ * y⁻¹ ∈ J₁.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.2 ⟨t₁, ht₁, by simp [MulAut.conj_apply]⟩
  have hy₂ : y * t₂ * y⁻¹ ∈ J₂.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.2 ⟨t₂, ht₂, by simp [MulAut.conj_apply]⟩
  have hun : ∀ J : Subgroup Y, IsComponentOf J ⊤ →
      (t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹ ∈ normalizer (J : Set Y) := by
    intro J hJ
    have a1 : t₁ ∈ normalizer (J : Set Y) := mem_normalizer_of_comp hJ₁ hJ ht₁
    have a2 : t₂ ∈ normalizer (J : Set Y) := mem_normalizer_of_comp hJ₂ hJ ht₂
    have b1 : y * t₁ * y⁻¹ ∈ normalizer (J : Set Y) := mem_normalizer_of_comp hK₁ hJ hy₁
    have b2 : y * t₂ * y⁻¹ ∈ normalizer (J : Set Y) := mem_normalizer_of_comp hK₂ hJ hy₂
    have e : (t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹ =
        (t₁ * t₂) * ((y * t₁ * y⁻¹) * (y * t₂ * y⁻¹))⁻¹ := by group
    rw [e]
    exact (normalizer (J : Set Y)).mul_mem ((normalizer (J : Set Y)).mul_mem a1 a2)
      ((normalizer (J : Set Y)).inv_mem ((normalizer (J : Set Y)).mul_mem b1 b2))
  have hu₁ := hun J₁ hJ₁
  have hu₂ := hun J₂ hJ₂
  have hvJ : (t₁ * t₂) * ((t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹) * (t₁ * t₂)⁻¹ *
      ((t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹)⁻¹ ∈ J₁ ⊔ J₂ := by
    generalize (t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹ = u at hu₁ hu₂ ⊢
    have m1 : u * t₁⁻¹ * u⁻¹ ∈ J₁ := (mem_normalizer_iff.1 hu₁ _).1 (J₁.inv_mem ht₁)
    have m2 : u * t₂⁻¹ * u⁻¹ ∈ J₂ := (mem_normalizer_iff.1 hu₂ _).1 (J₂.inv_mem ht₂)
    have e : (t₁ * t₂) * u * (t₁ * t₂)⁻¹ * u⁻¹ =
        (t₁ * t₂) * ((u * t₂⁻¹ * u⁻¹) * (u * t₁⁻¹ * u⁻¹)) := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left ht₁) (mem_sup_right ht₂))
      (mul_mem (mem_sup_right m2) (mem_sup_left m1))
  have hvW : (t₁ * t₂) * ((t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹) * (t₁ * t₂)⁻¹ *
      ((t₁ * t₂) * y * (t₁ * t₂)⁻¹ * y⁻¹)⁻¹ ∈ W :=
    W.mul_mem ((mem_normalizer_iff.1 hd _).1 huW) (W.inv_mem huW)
  have hvc := commutes_d_of_mem_W hc Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ hW hd hvW hvJ
  have hdu := coprime_trick hW hd5 hd huW hvc
  have hdy' := coprime_trick hW hd5 hd hy hdu.symm
  exact hdy'.symm

theorem tbaux_conj_mem_sup_aux {Ja Jb : Subgroup Y} (hJa : IsComponentOf Ja ⊤)
    (hJb : IsComponentOf Jb ⊤) (hne : Ja ≠ Jb) {ta tb : Y} (hta : ta ∈ Ja) (htb : tb ∈ Jb)
    {y : Y} (hy : y * (ta * tb) = (ta * tb) * y)
    (hnc : ∃ a ∈ Ja, a * (ta * tb) ≠ (ta * tb) * a) :
    y * ta * y⁻¹ ∈ Ja ⊔ Jb := by
  have hKc : IsComponentOf (Ja.map (MulAut.conj y).toMonoidHom) ⊤ := comp_conj hJa y
  have hmapmem : ∀ x ∈ Ja, y * x * y⁻¹ ∈ Ja.map (MulAut.conj y).toMonoidHom := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    simp [MulAut.conj_apply]
  by_cases h1 : Ja.map (MulAut.conj y).toMonoidHom = Ja
  · have hm := hmapmem ta hta
    rw [h1] at hm
    exact Subgroup.mem_sup_left hm
  by_cases h2 : Ja.map (MulAut.conj y).toMonoidHom = Jb
  · have hm := hmapmem ta hta
    rw [h2] at hm
    exact Subgroup.mem_sup_right hm
  exfalso
  obtain ⟨a, ha, hne'⟩ := hnc
  apply hne'
  have hyaK := hmapmem a ha
  have h3 : (y * a * y⁻¹) * ta = ta * (y * a * y⁻¹) :=
    comp_commute hKc hJa h1 _ hyaK ta hta
  have h4 : (y * a * y⁻¹) * tb = tb * (y * a * y⁻¹) :=
    comp_commute hKc hJb h2 _ hyaK tb htb
  have h5 : (y * a * y⁻¹) * (ta * tb) = (ta * tb) * (y * a * y⁻¹) := by
    rw [← mul_assoc, h3, mul_assoc, h4, ← mul_assoc]
  have hyd : y⁻¹ * (ta * tb) * y = ta * tb := by
    rw [mul_assoc, ← hy, ← mul_assoc, inv_mul_cancel, one_mul]
  calc a * (ta * tb) = y⁻¹ * ((y * a * y⁻¹) * (y * (ta * tb))) := by group
    _ = y⁻¹ * ((y * a * y⁻¹) * ((ta * tb) * y)) := by rw [hy]
    _ = y⁻¹ * (((y * a * y⁻¹) * (ta * tb)) * y) := by group
    _ = y⁻¹ * (((ta * tb) * (y * a * y⁻¹)) * y) := by rw [h5]
    _ = (y⁻¹ * (ta * tb) * y) * a := by group
    _ = (ta * tb) * a := by rw [hyd]

theorem conj_mem_sup (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (Q₁ : A5Quot J₁) (Q₂ : A5Quot J₂) (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5)
    (ho₂ : orderOf t₂ = 5) {y : Y} (hy : y * (t₁ * t₂) = (t₁ * t₂) * y) :
    y * t₁ * y⁻¹ ∈ J₁ ⊔ J₂ ∧ y * t₂ * y⁻¹ ∈ J₁ ⊔ J₂ := by
  have hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := comp_commute hJ₁ hJ₂ hne
  refine ⟨?_, ?_⟩
  · exact tbaux_conj_mem_sup_aux hJ₁ hJ₂ hne ht₁ ht₂ hy (not_centralizes hc Q₁ ht₁ ht₂ ho₁)
  · have hc' : ∀ a ∈ J₂, ∀ b ∈ J₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hy' : y * (t₂ * t₁) = (t₂ * t₁) * y := by
      rw [← hc t₁ ht₁ t₂ ht₂]
      exact hy
    have := tbaux_conj_mem_sup_aux hJ₂ hJ₁ hne.symm ht₂ ht₁ hy'
      (not_centralizes hc' Q₂ ht₂ ht₁ ho₂)
    rwa [sup_comm] at this

theorem conj_mem_P (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (Q₁ : A5Quot J₁) (Q₂ : A5Quot J₂) (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5)
    (ho₂ : orderOf t₂ = 5) {y : Y} (hy : y * (t₁ * t₂) = (t₁ * t₂) * y) :
    y * t₁ * y⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂ ∧ y * t₂ * y⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂ := by
  obtain ⟨hz1, hz2⟩ := conj_mem_sup hJ₁ hJ₂ hne Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ hy
  have hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := comp_commute hJ₁ hJ₂ hne
  have hcomm : t₁ * t₂ = t₂ * t₁ := hc t₁ ht₁ t₂ ht₂
  have hd1 : t₁ * (t₁ * t₂) = (t₁ * t₂) * t₁ := by
    rw [mul_assoc, ← hcomm]
  have hd2 : t₂ * (t₁ * t₂) = (t₁ * t₂) * t₂ := by
    rw [← mul_assoc, ← hcomm]
  have hyinv : y⁻¹ * (t₁ * t₂) = (t₁ * t₂) * y⁻¹ :=
    Commute.inv_left (show Commute y (t₁ * t₂) from hy)
  have hz1d : (y * t₁ * y⁻¹) * (t₁ * t₂) = (t₁ * t₂) * (y * t₁ * y⁻¹) := by
    calc (y * t₁ * y⁻¹) * (t₁ * t₂) = y * t₁ * (y⁻¹ * (t₁ * t₂)) := by group
      _ = y * t₁ * ((t₁ * t₂) * y⁻¹) := by rw [hyinv]
      _ = y * (t₁ * (t₁ * t₂)) * y⁻¹ := by group
      _ = y * ((t₁ * t₂) * t₁) * y⁻¹ := by rw [hd1]
      _ = (y * (t₁ * t₂)) * t₁ * y⁻¹ := by group
      _ = ((t₁ * t₂) * y) * t₁ * y⁻¹ := by rw [hy]
      _ = (t₁ * t₂) * (y * t₁ * y⁻¹) := by group
  have hz2d : (y * t₂ * y⁻¹) * (t₁ * t₂) = (t₁ * t₂) * (y * t₂ * y⁻¹) := by
    calc (y * t₂ * y⁻¹) * (t₁ * t₂) = y * t₂ * (y⁻¹ * (t₁ * t₂)) := by group
      _ = y * t₂ * ((t₁ * t₂) * y⁻¹) := by rw [hyinv]
      _ = y * (t₂ * (t₁ * t₂)) * y⁻¹ := by group
      _ = y * ((t₁ * t₂) * t₂) * y⁻¹ := by rw [hd2]
      _ = (y * (t₁ * t₂)) * t₂ * y⁻¹ := by group
      _ = ((t₁ * t₂) * y) * t₂ * y⁻¹ := by rw [hy]
      _ = (t₁ * t₂) * (y * t₂ * y⁻¹) := by group
  have ht5₁ : t₁ ^ 5 = 1 := by
    have := pow_orderOf_eq_one t₁
    rwa [ho₁] at this
  have ht5₂ : t₂ ^ 5 = 1 := by
    have := pow_orderOf_eq_one t₂
    rwa [ho₂] at this
  have hz1_5 : (y * t₁ * y⁻¹) ^ 5 = 1 := by
    rw [conj_pow, ht5₁]; group
  have hz2_5 : (y * t₂ * y⁻¹) ^ 5 = 1 := by
    rw [conj_pow, ht5₂]; group
  exact ⟨five_elem_mem hc Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ hz1 hz1d hz1_5,
    five_elem_mem hc Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ hz2 hz2d hz2_5⟩

theorem conj_mem_P_of_gens {y : Y} (h₁ : y * t₁ * y⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂)
    (h₂ : y * t₂ * y⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂) :
    ∀ k ∈ zpowers t₁ ⊔ zpowers t₂, y * k * y⁻¹ ∈ zpowers t₁ ⊔ zpowers t₂ := by
  intro k hk
  have hle : zpowers t₁ ⊔ zpowers t₂ ≤
      (zpowers t₁ ⊔ zpowers t₂).comap (MulAut.conj y).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact h₁
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact h₂
  exact Subgroup.mem_comap.mp (hle hk)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123
