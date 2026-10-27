module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Ex
public import CFSG.ClassicalInvolution.Q3.TL4MF163PGL

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.GorensteinWalter Matrix QuaternionGroup
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem eight_dvd_pow_sub_one {p f : ℕ} (hp : Odd p) (hf : Even f) : 8 ∣ p ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  obtain ⟨m, hm⟩ := hp.pow (n := k)
  have h1 : p ^ (k + k) = (2 * m + 1) ^ 2 := by rw [← hm, ← pow_mul, mul_two]
  have h2 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  rw [h1, h2, hj]
  omega

omit [Finite K] in
theorem torus_sq_mem_range (d : Kˣ) :
    pGammaL2FullSplitTorus K (d ^ 2) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  let g : SL(2, K) := ⟨!![(d : K), 0; 0, ((d⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_fin_two_of]
    simp⟩
  refine ⟨QuotientGroup.mk' _ g, ?_⟩
  rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  change Matrix.ProjGenLinGroup.mk _ =
    Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K (d ^ 2))
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨d, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = !![(d : K), 0; 0, ((d⁻¹ : Kˣ) : K)] := rfl
  rw [hg]
  fin_cases a <;> fin_cases b <;>
    simp [pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar, sq]

theorem exists_right_ne_one (hK : IsOddPrimePower (Nat.card K))
    {ψ : QuaternionGroup 2 →* PGammaL2 K} (hψ : Function.Injective ψ) :
    ∃ q : QuaternionGroup 2, (ψ q).right ≠ 1 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p, n, -, hp, -, hn⟩ := hK
    rw [hn]
    exact hp.pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card K hodd
  have key : ∀ q, ψ q = SemidirectProduct.inl (ψ q).left := fun q =>
    SemidirectProduct.ext (by rw [SemidirectProduct.left_inl])
      (by rw [SemidirectProduct.right_inl, hall q])
  have hinl : Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) :=
    SemidirectProduct.inl_injective
  have hrel : ∀ q₁ q₂ : QuaternionGroup 2,
      (ψ (q₁ * q₂)).left = (ψ q₁).left * (ψ q₂).left := by
    intro q₁ q₂
    apply hinl
    rw [← key (q₁ * q₂), map_mul, map_mul, ← key q₁, ← key q₂]
  have hone : (ψ 1).left = 1 := by rw [map_one, SemidirectProduct.one_left]
  let ψ' : QuaternionGroup 2 →* PGL2 K :=
    { toFun := fun q => (ψ q).left
      map_one' := hone
      map_mul' := hrel }
  have hψ' : Function.Injective ψ' := fun x y h =>
    hψ (by rw [key x, key y]; exact congrArg SemidirectProduct.inl h)
  have hc2 : ψ' (a 1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    exact (by decide : (a 1 ^ 2 : QuaternionGroup 2) ≠ 1) (hψ' (by rw [h, map_one]))
  have hc4 : ψ' (a 1) ^ 4 = 1 := by
    rw [← map_pow, show (a 1 ^ 4 : QuaternionGroup 2) = 1 by decide, map_one]
  have hwc : ψ' (xa 0) * ψ' (a 1) * (ψ' (xa 0))⁻¹ = (ψ' (a 1))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      show (xa 0 * a 1 * (xa 0)⁻¹ : QuaternionGroup 2) = (a 1)⁻¹ by decide]
  have hww := MF163.pgl2_mul_self_of_inv h2 hc2 hc4 hwc
  rw [← map_mul, show (xa 0 * xa 0 : QuaternionGroup 2) = a 2 by decide] at hww
  exact (by decide : (a 2 : QuaternionGroup 2) ≠ 1) (hψ' (by rw [hww, map_one]))

theorem mem_range_of_pow_four (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (h8 : 8 ∣ Nat.card K - 1) {v : PGL2 K} (hv2 : v ^ 2 ≠ 1) (hv4 : v ^ 4 = 1)
    (hvr : v ^ 2 ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    v ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  obtain ⟨i, hi⟩ : ∃ i : K, i * i = -1 := by
    obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr (by rw [hcardF]; omega)
    exact ⟨i, hi.symm⟩
  set L := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hL
  have ha2 : v ^ 2 * v ^ 2 = 1 := by rw [← pow_add]; exact hv4
  obtain ⟨c, hc, hca⟩ := MF164.exists_conj_s0 hK hcard hi hvr hv2 ha2
  set w := c * v * c⁻¹ with hw
  have hw2 : w * w = pGammaL2FullSplitTorus K (-1) := by
    rw [← hca, hw, sq]
    group
  have hws : w * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * w := by
    rw [← hw2]
    group
  have hwU : w ∈ (pGammaL2FullSplitTorus K).range := by
    by_contra hU
    exact MF164.s0_ne_one hK (hw2.symm.trans (MF164.sq_eq_one_of_not_mem_torus hK hws hU))
  obtain ⟨b, hb⟩ := hwU
  have hb2 : b ^ 2 = -1 := by
    apply pGammaL2FullSplitTorus_injective K
    rw [map_pow, hb, sq, hw2]
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, hcardF]
    intro hev
    obtain ⟨p, n, -, hp, -, hn⟩ := hK
    rw [hn] at hev
    have := Nat.odd_iff.mp (hp.pow (n := n))
    omega
  obtain ⟨d, hd⟩ : IsSquare b := by
    rw [FiniteField.unit_isSquare_iff hchar]
    obtain ⟨m, hm⟩ := h8
    have hhalf : Fintype.card K / 2 = 2 * (2 * m) := by rw [hcardF]; omega
    rw [hhalf, pow_mul, pow_mul, hb2]
    simp
  have hwL : w ∈ L := by
    rw [← hb, hd, ← sq]
    exact torus_sq_mem_range d
  have hv : v = c⁻¹ * w * c := by
    rw [hw]
    group
  rw [hv]
  exact L.mul_mem (L.mul_mem (L.inv_mem hc) hwL) hc

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
