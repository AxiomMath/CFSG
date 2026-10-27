module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRankL
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BRank

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_elem_lift {J D : Subgroup Ω} (hD : IsElemAbelian 3 D)
    (hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d) {Eb : Subgroup (PQuot 3 J)}
    (hEb : IsElemAbelian 3 Eb) {k : ℕ}
    (hk : 3 ^ k * Nat.card (Subgroup.center (PQuot 3 J)) ≤ Nat.card Eb) :
    ∃ E : Subgroup Ω, E ≤ D ⊔ J ∧ IsElemAbelian 3 E ∧ 3 ^ k * Nat.card D ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥J →* PQuot 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hπ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)) h
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
  obtain ⟨W, -, hWmap, hWinj⟩ := CatB.exists_pSubgroup_lift Nat.prime_three π hk3 hEb.isPGroup
    (by rw [hrange]; exact le_top)
  obtain ⟨hW', hW'c⟩ := CatB.map_subtype_isElemAbelian_card π hWmap hWinj hEb
  have hW'J : W.map J.subtype ≤ J := Subgroup.map_subtype_le W
  have hc : ∀ a ∈ D, ∀ b ∈ W.map J.subtype, a * b = b * a := fun a ha b hb =>
    hDJ a ha b (hW'J hb)
  refine ⟨D ⊔ W.map J.subtype, sup_le_sup_left hW'J D, hD.sup_of_commute hW' hc, ?_⟩
  have hinf : Nat.card ↥(D ⊓ W.map J.subtype) ≤ Nat.card (Subgroup.center (PQuot 3 J)) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨π ⟨x.1, hW'J x.2.2⟩, ?_⟩) ?_
    · refine Subgroup.mem_center_iff.2 fun y => ?_
      obtain ⟨j, rfl⟩ : ∃ j, π j = y := QuotientGroup.mk'_surjective _ y
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (hDJ x.1 x.2.1 j j.2).symm)
    · intro x y hxy
      have h : π ⟨x.1, hW'J x.2.2⟩ = π ⟨y.1, hW'J y.2.2⟩ := congrArg Subtype.val hxy
      obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 x.2.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.1 y.2.2
      have hu' : u = ⟨x.1, hW'J x.2.2⟩ := Subtype.ext hux
      have hv' : v = ⟨y.1, hW'J y.2.2⟩ := Subtype.ext hvy
      have h' : π u = π v := by rw [hu', hv']; exact h
      have huv : (⟨u, hu⟩ : W) = ⟨v, hv⟩ :=
        hWinj (show (π.comp W.subtype) ⟨u, hu⟩ = (π.comp W.subtype) ⟨v, hv⟩ from h')
      exact Subtype.ext (by rw [← hux, ← hvy, show u = v from congrArg Subtype.val huv])
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D (W.map J.subtype) hc).1
  rw [hW'c] at hprod
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := Subgroup.center (PQuot 3 J)))
  calc 3 ^ k * Nat.card D * Nat.card (Subgroup.center (PQuot 3 J))
      = Nat.card D * (3 ^ k * Nat.card (Subgroup.center (PQuot 3 J))) := by ring
    _ ≤ Nat.card D * Nat.card Eb := Nat.mul_le_mul_left _ hk
    _ = Nat.card ↥(D ⊔ W.map J.subtype) * Nat.card ↥(D ⊓ W.map J.subtype) := hprod.symm
    _ ≤ Nat.card ↥(D ⊔ W.map J.subtype) * Nat.card (Subgroup.center (PQuot 3 J)) :=
      Nat.mul_le_mul_left _ hinf


theorem le_twoLocalRank_add_one {J D : Subgroup Ω} (hD : IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d)
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) {n : ℕ} (hn5 : 5 ≤ n)
    (hcat : catalogIs (PSimple 3 J) (tyUnTwo n)) :
    n ≤ GLATwoLocalRank 3 Ω + 1 ∧ (¬ 3 ∣ n → n ≤ GLATwoLocalRank 3 Ω) := by
  obtain ⟨r, hw, h1, h2⟩ :=
    exists_twoLocal_of_cover hq (I2611.isPGroup_center_pQuot' Nat.prime_three J) hn5 hcat
  have hl := S8.L84.two_local_lift hD hD9 hDJ hw
  exact ⟨by omega, fun h3 => by have := h2 h3; omega⟩

theorem exists_elem_six {J D : Subgroup Ω} (hD : IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d) (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≤ 6) (hcat : catalogIs (PSimple 3 J) (tyUnTwo n)) :
    ∃ E : Subgroup Ω, E ≤ D ⊔ J ∧ IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E := by
  obtain ⟨Eb, hEb, hk⟩ :=
    exists_elem_of_cover hq (I2611.isPGroup_center_pQuot' Nat.prime_three J) hn5 hn6 hcat
  obtain ⟨E, hEDJ, hE, hEc⟩ := exists_elem_lift hD hDJ hEb hk
  exact ⟨E, hEDJ, hE, le_trans (by norm_num [hD9]) hEc⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.BRank

end
