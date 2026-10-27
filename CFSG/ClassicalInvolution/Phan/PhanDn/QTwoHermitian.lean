module

public import CFSG.ClassicalGroups.Unitary.SmallOrbit
public import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

theorem qTwo_fixed_eq_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {x : K} (hfix : σ x = x) (hx : x ≠ 0) : x = 1 := by
  classical
  let H := fixedFieldAdd σ
  have hcard : Nat.card H = 2 := by
    simpa using natCard_fixedFieldAdd hσ (CharP.cast_eq_zero K 2) (m := 1)
      (show Nat.card K = (2 ^ 1) ^ 2 by simpa using hK)
  obtain ⟨y, _, hu⟩ := (Nat.card_eq_two_iff' (0 : H)).mp hcard
  let x' : H := ⟨x, hfix⟩
  let one' : H := ⟨1, map_one σ⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hone' : one' ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  exact congrArg Subtype.val ((hu x' hx').trans (hu one' hone').symm)

theorem qTwo_norm_eq_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {x : K} (hx : x ≠ 0) : σ x * x = 1 := by
  have hs : σ x ≠ 0 := fun h => hx (σ.injective (h.trans (map_zero σ).symm))
  exact qTwo_fixed_eq_one hσ hK (hσ.norm_fixed x) (mul_ne_zero hs hx)

omit [Finite K] [CharP K 2] in
private theorem point_eq_span {n : ℕ}
    {p : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p)
    {x : Fin n ⊕ Fin n → K} (hx : x ∈ p) (hx0 : x ≠ 0) : p = K ∙ x := by
  obtain ⟨v, hpv, _, hvh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h]; simp)
  have hpdim : Module.finrank K p = 1 := by
    rw [hpv, finrank_span_singleton hv0]
  symm
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x p).2 hx)
  rw [finrank_span_singleton hx0, hpdim]

private theorem point_diag_eq_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {n : ℕ} {p : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p)
    {x : Fin n ⊕ Fin n → K} (hx : x ∈ p) (hx0 : x ≠ 0) : flipHerm σ x x = 1 := by
  have hp' : IsFlipflopPt σ (K ∙ x) := point_eq_span hp hx hx0 ▸ hp
  exact qTwo_fixed_eq_one hσ hK (flipHerm_conj hσ.invol x x)
    ((isFlipflopPt_span_singleton_iff hx0).1 hp').2

theorem FlipColl.flipHerm_eq_zero_of_card_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {n : ℕ} {p q : Submodule K (Fin n ⊕ Fin n → K)}
    (hcoll : FlipColl σ p q) (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q)
    {x y : Fin n ⊕ Fin n → K} (hx : x ∈ p) (hy : y ∈ q) : flipHerm σ x y = 0 := by
  classical
  by_contra hxy
  have hx0 : x ≠ 0 := by intro h; subst x; simp at hxy
  have hy0 : y ≠ 0 := by intro h; subst y; simp at hxy
  have hxx := point_diag_eq_one hσ hK hp hx hx0
  have hyy := point_diag_eq_one hσ hK hq hy hy0
  have hnorm := qTwo_norm_eq_one hσ hK hxy
  let c := flipHerm σ x y
  let z := x - c • y
  have hzx : flipHerm σ z x = 0 := by
    change flipHerm σ (x - c • y) x = 0
    rw [flipHerm_sub_left, flipHerm_smul_left, hxx, ← flipHerm_conj hσ.invol x y]
    change 1 - c * σ c = 0
    rw [mul_comm c (σ c), hnorm, sub_self]
  have hzy : flipHerm σ z y = 0 := by
    change flipHerm σ (x - c • y) y = 0
    rw [flipHerm_sub_left, flipHerm_smul_left, hyy, mul_one]
    exact sub_self c
  have hz : z ∈ p ⊔ q := Submodule.sub_mem _ (Submodule.mem_sup_left hx)
    (Submodule.mem_sup_right (q.smul_mem c hy))
  have hpx := point_eq_span hp hx hx0
  have hqy := point_eq_span hq hy hy0
  have hz0 : z = 0 := hcoll.2.nondeg z hz fun v hv => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hpx] at ha
    rw [hqy] at hb
    obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨w, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [flipHerm_add_right, flipHerm_smul_right, flipHerm_smul_right, hzx, hzy,
      mul_zero, mul_zero, add_zero]
  have hxq : x ∈ q := by
    have heq : x = c • y := sub_eq_zero.mp hz0
    rw [heq]
    exact q.smul_mem c hy
  have hpq : p ≤ q := by
    rw [hpx]
    exact (Submodule.span_singleton_le_iff_mem x q).2 hxq
  exact hcoll.1 (Submodule.eq_of_le_of_finrank_eq hpq
    (by rw [hpx, hqy, finrank_span_singleton hx0, finrank_span_singleton hy0]))

theorem FlipColl.le_flipOrth_of_card_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {n : ℕ} {p q : Submodule K (Fin n ⊕ Fin n → K)}
    (hcoll : FlipColl σ p q) (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) :
    p ≤ flipOrth σ q := by
  intro x hx
  apply mem_flipOrth.mpr
  intro y hy
  exact (flipHerm_eq_zero_iff hσ.invol).mp
    (hcoll.flipHerm_eq_zero_of_card_four hσ hK hp hq hx hy)

end CFSG.ClassicalInvolution.PhanDn

end
