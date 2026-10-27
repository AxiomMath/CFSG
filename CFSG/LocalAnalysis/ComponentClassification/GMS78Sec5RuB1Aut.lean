module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSzAut
public import CFSG.Quasithin.Recognition.F112TitsFrob
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.PerfectAutomorphisms

theorem eq_one_of_odd_of_fix_four {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Sz 1) (β : MulAut Q) (hβ : Odd (orderOf β)) {B : Subgroup Q}
    (hB2 : ∀ b ∈ B, b * b = 1) (hB4 : 4 ≤ Nat.card B) (hfix : ∀ b ∈ B, β b = b) : β = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβin : β ∈ inner Q := by
    by_contra hβin
    have h3 : Nat.card (Outer Q) = 3 := card_outer_eq_three e
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    set b := (QuotientGroup.mk β : Outer Q) with hb
    have hb1 : b ≠ 1 := fun h => hβin ((QuotientGroup.eq_one_iff _).mp h)
    have hbo : orderOf b = 3 := by
      have hdvd : orderOf b ∣ 3 := h3 ▸ _root_.orderOf_dvd_natCard b
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hb1
      · exact h
    have hβ0 : orderOf β ≠ 0 := (orderOf_pos β).ne'
    obtain ⟨k, m, hm3, hβm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hβ0 3 (by norm_num)
    set β' := β ^ m with hβ'
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hβm
      exact hβ0 hβm
    have hβ'o : orderOf β' = 3 ^ k := by
      rw [hβ', orderOf_pow_of_dvd hm0 (by rw [hβm]; exact dvd_mul_left m _), hβm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hb' : (QuotientGroup.mk β' : Outer Q) ≠ 1 := by
      intro h
      rw [hβ', QuotientGroup.mk_pow, ← hb] at h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hbo] at this
      exact hm3 this
    have hβ'1 : β' ≠ 1 := fun h => hb' (by rw [h]; rfl)
    set f := MulAut.congr e β' with hf
    have hfo : orderOf f = 3 ^ k := by
      rw [hf, MulEquiv.orderOf_eq, hβ'o]
    have hcop : Nat.Coprime (2 * 1 + 1) (Nat.card (Sz 1)) := by
      rw [card_Sz_one]
      norm_num
    have hP : IsPGroup 3 (zpowers f) := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, hfo]
    have hdvd := CFSG.SignalizerFunctorTheorem.NearModels.sz_card_pSubgroup_dvd 1 (by norm_num)
      hcop (zpowers f) hP
    rw [Nat.card_zpowers] at hdvd
    have hfo3 : orderOf f = 2 * 1 + 1 := by
      rcases (Nat.dvd_prime (by norm_num : (2 * 1 + 1).Prime)).mp hdvd with h | h
      · exfalso
        apply hβ'1
        have hf1 : f = 1 := orderOf_eq_one_iff.mp h
        rw [hf] at hf1
        exact (MulAut.congr e).injective (by rw [hf1, map_one])
      · exact h
    obtain ⟨φ⟩ := CFSG.SignalizerFunctorTheorem.NearModels.sz_fixedSubgroup_mulEquiv 1
      (by norm_num) hcop f hfo3
    have hle : B.map e.toMonoidHom ≤ signalizerFixedSubgroup f := by
      rintro _ ⟨a, ha, rfl⟩
      change f (e a) = e a
      have hpow : ∀ j : ℕ, (β ^ j) a = a := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ, MulAut.mul_apply, hfix a ha, ih]
      rw [hf, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hβ', hpow m]
    set E := (B.map e.toMonoidHom).subgroupOf (signalizerFixedSubgroup f) with hE
    have hE2 : ∀ x ∈ E, x * x = 1 := by
      intro x hx
      obtain ⟨a, ha, hax⟩ := mem_subgroupOf.mp hx
      apply Subtype.ext
      rw [coe_mul, ← hax]
      change e a * e a = 1
      rw [← map_mul, hB2 a ha, map_one]
    have hEc : Nat.card E = Nat.card B := by
      rw [hE, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
        card_map_of_injective e.injective]
    have h2 := CFSG.Quasithin.F112T.ElemAbSmall.of_sz φ E hE2
    omega
  obtain ⟨q, rfl⟩ := hβin
  obtain ⟨⟨b, hbB⟩, hb1⟩ : ∃ b : B, b ≠ 1 := by
    have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hB2 b hbB) hb1'
  have hqb : q ∈ centralizer ({b} : Set Q) := by
    rw [mem_centralizer_singleton_iff]
    have h := hfix b hbB
    rw [MulAut.conj_apply] at h
    calc q * b = q * b * q⁻¹ * q := by group
      _ = b * q := by rw [h]
  obtain ⟨n, hn⟩ := isPGroup_centralizer_of_sz_one e hbo ⟨q, hqb⟩
  have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : orderOf (MulAut.conj q) ∣ 2 ^ n :=
    (orderOf_map_dvd MulAut.conj q).trans (orderOf_dvd_of_pow_eq_one hqn)
  have hcop : Nat.Coprime (orderOf (MulAut.conj q)) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hβ)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_odd_of_fix_four {L : Subgroup G}
    (hLp : commutator L = ⊤) (e : rankTwoQuot L ≃* Sz 1) (hZ : Odd (Nat.card (center L)))
    {B : Subgroup G} (hBL : B ≤ L) (hB2 : ∀ b ∈ B, b * b = 1) (hB4 : 4 ≤ Nat.card B) {y : G}
    (hyN : y ∈ normalizer (L : Set G)) (hy : Odd (orderOf y))
    (hyB : ∀ b ∈ B, y * b * y⁻¹ = b) : y ∈ centralizer (L : Set G) := by
  have : Group.IsPerfect L := ⟨hLp⟩
  set π := QuotientGroup.mk' (center L) with hπ
  set B' : Subgroup (rankTwoQuot L) := (B.subgroupOf L).map π with hB'
  set α := quotAutHom L ⟨y, hyN⟩ with hα
  have hBZ : ∀ x : L, (x : G) ∈ B → x ∈ center L → x = 1 := by
    intro x hxB hxZ
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hB2 x hxB)
    have hxodd : Odd (orderOf x) := by
      have := Subgroup.orderOf_dvd_natCard (center L) hxZ
      exact hZ.of_dvd_nat this
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have h2 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at hxodd
        exact absurd hxodd (by decide)
    exact orderOf_eq_one_iff.mp h2
  have hinj : Set.InjOn π (B.subgroupOf L) := by
    intro x hx x' hx' hxx
    have h1 : x⁻¹ * x' ∈ center L := by
      rw [← QuotientGroup.ker_mk' (center L), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hxx, inv_mul_cancel]
    have h2 := hBZ _ (B.mul_mem (B.inv_mem (mem_subgroupOf.mp hx)) (mem_subgroupOf.mp hx')) h1
    rw [inv_mul_eq_one] at h2
    exact h2
  have hB'c : Nat.card B' = Nat.card B := by
    rw [hB', ← Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv]
    exact Nat.card_image_of_injOn hinj
  have hB'2 : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, show b * b = 1 from Subtype.ext (by simpa using hB2 b hb), map_one]
  have hαo : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf (⟨y, hyN⟩ : normalizer (L : Set G)) :=
      orderOf_map_dvd (quotAutHom L) _
    rw [Subgroup.orderOf_mk] at h1
    exact hy.of_dvd_nat h1
  have hαB : ∀ x ∈ B', α x = x := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hα, hπ, quotAutHom_apply_mk]
    congr 1
    apply Subtype.ext
    simp only [normalizerMonoidHom_apply_apply_coe]
    exact hyB _ (mem_subgroupOf.mp hb)
  have hα1 : α = 1 := eq_one_of_odd_of_fix_four e α hαo hB'2 (by omega) hαB
  have hσ : L.normalizerMonoidHom ⟨y, hyN⟩ = 1 := by
    apply centerQuotientHom_injective L
    rw [map_one]
    exact hα1
  rw [mem_centralizer_iff]
  intro z hz
  have h1 := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : G)) hσ
  simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
  calc z * y = y * z * y⁻¹ * y := by rw [h1]
    _ = y * z := by group

end CFSG.ComponentClassification.GMS78
