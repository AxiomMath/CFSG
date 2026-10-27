module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Br
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Q3.TL4MF164PG

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.GorensteinWalter Matrix QuaternionGroup
open scoped MatrixGroups

theorem q8_inv_eq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 → x = 1 ∨ x = a 2 := by decide

theorem q8_sq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 ∨ x ^ 2 = a 2 := by decide

theorem q8_exists_inv : ∀ y : QuaternionGroup 2, y ≠ 1 → y ≠ a 2 → ∃ j : QuaternionGroup 2,
    y * j * y⁻¹ = j⁻¹ ∧ y * (y * j) * y⁻¹ = (y * j)⁻¹ ∧ j ^ 2 ≠ 1 ∧ (y * j) ^ 2 ≠ 1 := by
  decide

theorem q8_nonabelian : ∃ x y : QuaternionGroup 2, x * y ≠ y * x := by decide

theorem pow_half_mod_eight {p f : ℕ} (hp : Odd p) (h4f : 4 ∣ f) : p ^ (f / 2) % 8 = 1 := by
  obtain ⟨k, hk⟩ := h4f
  have hq' : p ^ (f / 2) = (p ^ k) ^ 2 := by rw [hk, ← pow_mul]; congr 1; omega
  obtain ⟨m, hm⟩ := hp.pow (n := k)
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  rw [hq', hm]
  have h1 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
  rw [h1, ht]
  omega

section Ex

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem left_commute_s0 {x : PGammaL2 K}
    (hx : x * SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) * x) :
    x.left * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * x.left := by
  have h := congrArg SemidirectProduct.left hx
  simpa [SemidirectProduct.mul_left, pgl2FieldAut_s0] using h

omit [Finite K] in
theorem conj_inl (y : PGammaL2 K) (t : PGL2 K) :
    y * SemidirectProduct.inl t * y⁻¹ =
      SemidirectProduct.inl (y.left * pgl2FieldAut K y.right t * y.left⁻¹) := by
  have hy := SemidirectProduct.inl_left_mul_inr_right y
  calc y * SemidirectProduct.inl t * y⁻¹
      = SemidirectProduct.inl y.left * (SemidirectProduct.inr y.right * SemidirectProduct.inl t *
          (SemidirectProduct.inr y.right)⁻¹) * (SemidirectProduct.inl y.left)⁻¹ := by
        conv_lhs => rw [← hy]
        group
    _ = _ := by
        rw [← map_inv SemidirectProduct.inr y.right, ← SemidirectProduct.inl_aut,
          ← map_inv SemidirectProduct.inl, ← map_mul, ← map_mul]

omit [Finite K] in
theorem fieldAut_torus_pow {φ : K ≃+* K} {q : ℕ} (hφ : ∀ x, φ x = x ^ q) (c : Kˣ) :
    pgl2FieldAut K φ (pGammaL2FullSplitTorus K c) = pGammaL2FullSplitTorus K (c ^ q) := by
  rw [pGammaL2FullSplitTorus_map_field]
  congr 1
  ext
  simp [hφ]

theorem sq_eq_one_of_not_mem_torus (hK : IsOddPrimePower (Nat.card K)) {h : PGL2 K}
    (hh : h * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * h)
    (hU : h ∉ (pGammaL2FullSplitTorus K).range) : h * h = 1 := by
  obtain ⟨b, hb⟩ := (mem_torus_or_mul_weyl hK hh).resolve_left hU
  have hh' : h = pGammaL2FullSplitTorus K b * weylPGL K := by
    rw [hb, mul_assoc, weylPGL_mul_self, mul_one]
  rw [hh']
  calc pGammaL2FullSplitTorus K b * weylPGL K * (pGammaL2FullSplitTorus K b * weylPGL K)
      = pGammaL2FullSplitTorus K b * (weylPGL K * pGammaL2FullSplitTorus K b *
          (weylPGL K)⁻¹) * (weylPGL K * weylPGL K) := by group
    _ = 1 := by rw [weylPGL_conj_torus, weylPGL_mul_self]; group

theorem q8_sq_mem (hK : IsOddPrimePower (Nat.card K)) {S : Subgroup (PGammaL2 K)}
    (eS : S ≃* QuaternionGroup 2)
    (hs₀ : SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) ∈ S) :
    eS ⟨_, hs₀⟩ = a 2 ∧ ∀ x : S, x ^ 2 = 1 ∨ x ^ 2 = ⟨_, hs₀⟩ := by
  have hs02 : pGammaL2FullSplitTorus K (-1) * pGammaL2FullSplitTorus K (-1) = 1 := by
    rw [← map_mul, show (-1 : Kˣ) * -1 = 1 by simp, map_one]
  have hz8sq : (⟨_, hs₀⟩ : S) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    change SemidirectProduct.inl _ * SemidirectProduct.inl _ = (1 : PGammaL2 K)
    rw [← map_mul, hs02, map_one])
  have hz8 : eS ⟨_, hs₀⟩ = a 2 := by
    refine (q8_inv_eq _ (by rw [← map_pow, hz8sq, map_one])).resolve_left fun h =>
      s0_ne_one hK ?_
    have h1 : (⟨_, hs₀⟩ : S) = 1 := eS.injective (by rw [h, map_one])
    have h2 := congrArg (fun x : S => SemidirectProduct.left (x : PGammaL2 K)) h1
    simpa using h2
  refine ⟨hz8, fun x => ?_⟩
  rcases q8_sq (eS x) with h | h
  · exact Or.inl (eS.injective (by rw [map_pow, h, map_one]))
  · exact Or.inr (eS.injective (by rw [map_pow, h, hz8]))

end Ex

end CFSG.ClassicalInvolution.Q3.TL4.MF164
