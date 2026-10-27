module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Basic
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

section Abstract

variable {X Y : Type} [Group X] [Group Y] [Finite X]

theorem exists_conj_of_pow_four_mod (f : X →* Y) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {a b : X} (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hfab : f a = f b)
    (hb2 : f b ^ 2 ≠ 1) : ∃ h : X, h * a * h⁻¹ = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite Y := Finite.of_surjective f hf
  set Y₀ : Subgroup Y := zpowers (f b) with hY₀
  set H₀ : Subgroup X := Y₀.comap f with hH₀
  have hfb4 : f b ^ 4 = 1 := by rw [← map_pow, hb, map_one]
  have hfbo : orderOf (f b) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := f b) (by simpa using hb2)
      (by simpa using hfb4)
    simpa using h
  have haH : a ∈ H₀ := by
    show f a ∈ Y₀
    rw [hfab]
    exact mem_zpowers _
  have hbH : b ∈ H₀ := mem_zpowers _
  have hkerH : f.ker ≤ H₀ := fun x hx => by
    show f x ∈ Y₀
    rw [MonoidHom.mem_ker.1 hx]
    exact one_mem _
  have hcardH : Nat.card ↥H₀ = 4 * Nat.card f.ker := by
    have h1 : H₀.index = Y₀.index := Subgroup.index_comap_of_surjective Y₀ hf
    have h2 := Subgroup.index_mul_card H₀
    have h3 := Subgroup.index_mul_card Y₀
    have h4 := Subgroup.card_ker_mul_card_of_surjective hf
    have hY₀card : Nat.card ↥Y₀ = 4 := by rw [hY₀, Nat.card_zpowers, hfbo]
    have hidx : 0 < Y₀.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    rw [h1] at h2
    rw [hY₀card] at h3
    have : Y₀.index * Nat.card ↥H₀ = Y₀.index * (4 * Nat.card f.ker) := by
      rw [h2, ← h4, ← h3]
      ring
    exact Nat.eq_of_mul_eq_mul_left hidx this
  have hfac : (Nat.card ↥H₀).factorization 2 = 2 := by
    have hker0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
    rw [hcardH, Nat.factorization_mul (by norm_num) hker0]
    simp only [Finsupp.add_apply]
    have : (Nat.card f.ker).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h))
    rw [this]
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [h4]
  have hao : orderOf a = 4 := by
    have h1 : orderOf a ∣ 4 := orderOf_dvd_of_pow_eq_one ha
    have h2 : orderOf (f a) ∣ orderOf a := orderOf_map_dvd f a
    rw [hfab, hfbo] at h2
    exact Nat.dvd_antisymm h1 h2
  have hbo : orderOf b = 4 := by
    have h1 : orderOf b ∣ 4 := orderOf_dvd_of_pow_eq_one hb
    have h2 : orderOf (f b) ∣ orderOf b := orderOf_map_dvd f b
    rw [hfbo] at h2
    exact Nat.dvd_antisymm h1 h2
  let aH : ↥H₀ := ⟨a, haH⟩
  let bH : ↥H₀ := ⟨b, hbH⟩
  have haHo : orderOf aH = 4 := by
    rw [show orderOf aH = orderOf a from Subgroup.orderOf_mk a haH, hao]
  have hbHo : orderOf bH = 4 := by
    rw [show orderOf bH = orderOf b from Subgroup.orderOf_mk b hbH, hbo]
  have hA : Nat.card ↥(zpowers aH) = 2 ^ (Nat.card ↥H₀).factorization 2 := by
    rw [Nat.card_zpowers, haHo, hfac]
    norm_num
  have hB : Nat.card ↥(zpowers bH) = 2 ^ (Nat.card ↥H₀).factorization 2 := by
    rw [Nat.card_zpowers, hbHo, hfac]
    norm_num
  let SA : Sylow 2 ↥H₀ := Sylow.ofCard (zpowers aH) hA
  let SB : Sylow 2 ↥H₀ := Sylow.ofCard (zpowers bH) hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H₀ SB SA
  have hconj : ∀ y : ↥H₀, y ∈ zpowers aH ↔ g⁻¹ * y * g ∈ zpowers bH := by
    intro y
    have h := congrArg (fun S : Sylow 2 ↥H₀ => (S : Subgroup ↥H₀)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    show y ∈ (SA : Subgroup ↥H₀) ↔ g⁻¹ * y * g ∈ (SB : Subgroup ↥H₀)
    rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hmem : g⁻¹ * aH * g ∈ zpowers bH := (hconj aH).1 (mem_zpowers aH)
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
  have hgY : f (g : X) ∈ Y₀ := g.2
  have hcommY : f (g : X) * f a = f a * f (g : X) := by
    rw [hfab]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hgY
    rw [← hj]
    exact ((Commute.refl (f b)).zpow_left j).eq
  have hfx : f ((g : X)⁻¹ * a * (g : X)) = f b := by
    rw [map_mul, map_mul, map_inv]
    calc (f (g : X))⁻¹ * f a * f (g : X) = (f (g : X))⁻¹ * (f (g : X) * f a) := by
          rw [hcommY]
          group
      _ = f a := by group
      _ = f b := hfab
  have hxb : (g : X)⁻¹ * a * (g : X) = b ^ i := by
    have := congrArg Subtype.val hi
    simpa using this.symm
  have hbi : (g : X)⁻¹ * a * (g : X) = b := by
    have h1 : f b ^ i = f b := by
      have := hfx
      rw [hxb, map_zpow] at this
      exact this
    have h2 : f b ^ (i - 1) = 1 := by
      rw [zpow_sub_one, h1, mul_inv_cancel]
    have h3 : (4 : ℤ) ∣ i - 1 := by
      have h := orderOf_dvd_iff_zpow_eq_one.2 h2
      rw [hfbo] at h
      simpa using h
    obtain ⟨m, hm⟩ := h3
    have h4 : b ^ i = b := by
      have : i = 4 * m + 1 := by omega
      rw [this, zpow_add, zpow_one, zpow_mul]
      have : b ^ (4 : ℤ) = 1 := by
        have h5 : b ^ (4 : ℕ) = 1 := hb
        exact_mod_cast h5
      rw [this, one_zpow, one_mul]
    rw [hxb, h4]
  refine ⟨(g : X)⁻¹, ?_⟩
  rw [inv_inv]
  exact hbi

end Abstract

section Main

variable {G : Type} [Group G] [Finite G]

theorem ii4_ord4_lift_of_II4 (h44 : II4_44) (hAut : II4_Aut) : II4_ord4_lift := by
  intro G _ _ hG z hz K hKc hrk hzs a ha b hb haz hbz
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL := h44 G hG z hz K hKc hrk
  have hconj := (hAut (Hat K) hSL).2.1
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have hzK : z ∈ K := haz ▸ K.mul_mem ha ha
  have hz1 : hatMk K ⟨z, hzK⟩ ≠ 1 := by
    intro h1
    have hzO : z ∈ pPrimeCoreOf 2 K := (hatMk_eq_one_iff K ⟨z, hzK⟩).1 h1
    have h2 := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 K) hzO
    rw [hz] at h2
    exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd K)) (even_iff_two_dvd.2 h2)
  let a' : ↥K := ⟨a, ha⟩
  let b' : ↥K := ⟨b, hb⟩
  have ha2 : a' ^ 2 = ⟨z, hzK⟩ := Subtype.ext (by simpa [sq] using haz)
  have hb2 : b' ^ 2 = ⟨z, hzK⟩ := Subtype.ext (by simpa [sq] using hbz)
  have hz'2 : (⟨z, hzK⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hz2)
  have ha4 : a' ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, ha2, hz'2]
  have hb4 : b' ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hb2, hz'2]
  have hfa2 : hatMk K a' ^ 2 ≠ 1 := by
    rw [← map_pow, ha2]
    exact hz1
  have hfb2 : hatMk K b' ^ 2 ≠ 1 := by
    rw [← map_pow, hb2]
    exact hz1
  have hfo : ∀ x : ↥K, x ^ 4 = 1 → hatMk K x ^ 2 ≠ 1 → orderOf (hatMk K x) = 4 := by
    intro x hx4 hx2
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := hatMk K x) (by simpa using hx2)
      (by rw [← map_pow]; simpa using (congrArg (hatMk K) hx4).trans (map_one _))
    simpa using h
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj _ _ (hfo a' ha4 hfa2) (hfo b' hb4 hfb2))
  obtain ⟨k₀, rfl⟩ := hatMk_surjective K c
  have ha''4 : (k₀ * a' * k₀⁻¹) ^ 4 = 1 := by
    rw [conj_pow, ha4]
    group
  obtain ⟨h, hh⟩ := exists_conj_of_pow_four_mod (hatMk K) (hatMk_surjective K)
    (odd_card_ker_hatMk K) ha''4 hb4 (by rw [map_mul, map_mul, map_inv]; exact hc) hfb2
  refine ⟨((h * k₀ : ↥K) : G), (h * k₀).2, ?_⟩
  have := congrArg Subtype.val hh
  simpa [mul_assoc] using this

end Main


end CFSG.GH74.GLS.IVK.Lifted
