module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUKernel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEight

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section Eight

variable {K : Type*} [Field K] [Finite K]

theorem pow_fifteen_eq_self (hK : Nat.card K = 8) (a : K) : a ^ 15 = a := by
  have : Fintype K := Fintype.ofFinite K
  have h8 : a ^ 8 = a := by
    have := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hK] at this
  calc a ^ 15 = a ^ 8 * a ^ 7 := by ring
    _ = a * a ^ 7 := by rw [h8]
    _ = a ^ 8 := by ring
    _ = a := h8

theorem pow_five_injective (hK : Nat.card K = 8) {a b : K} (h : a ^ 5 = b ^ 5) : a = b := by
  calc a = (a ^ 5) ^ 3 := by rw [← pow_mul, pow_fifteen_eq_self hK]
    _ = (b ^ 5) ^ 3 := by rw [h]
    _ = b := by rw [← pow_mul, pow_fifteen_eq_self hK]

theorem eq_mul_of_map_mul_eq (hK : Nat.card K = 8) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (h : K →+ K) (hh : ∀ w, h (c * w) = c * h w) : ∀ w, h w = h 1 * w := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hne : Units.mk0 c hc0 ≠ 1 := by
    intro h1
    apply hc1
    have := congrArg Units.val h1
    simpa using this
  have htop := zpowers_eq_top_of_prime_card hcard hne
  have hpow : ∀ n : ℕ, ∀ w, h (c ^ n * w) = c ^ n * h w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', mul_assoc, hh, ih, mul_assoc]
  intro w
  by_cases hw : w = 0
  · rw [hw, map_zero, mul_zero]
  have hmem : Units.mk0 w hw ∈ zpowers (Units.mk0 c hc0) := by
    rw [htop]
    exact mem_top _
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have hn' : c ^ n = w := by
    have := congrArg Units.val hn
    simpa using this
  rw [← hn', ← mul_one (c ^ n), hpow, mul_comm, mul_one]

theorem false_of_affine_card_eq_168_of_sq_equivariant' (hK : Nat.card K = 8)
    (N : Subgroup (Equiv.Perm K)) (haff : ∀ x ∈ N, ∀ v w, x (v + w) + x 0 = x v + x w)
    (hN : Nat.card N = 168) (hs : IsSimpleGroup N)
    (hsq : ∀ x ∈ N, ∃ φ : AddAut K, ∀ a, (x a - x 0) ^ 5 = φ (a ^ 5)) : False := by
  classical
  have hinj := affineLinearPartHom_injective N haff hs (by omega)
  choose H hH using hsq
  let F : N → SzEight.equivariantAddAut (fun a : K => a ^ 5) := fun x =>
    ⟨Multiplicative.ofAdd (H x x.2), SzEight.mem_equivariantAddAut.mpr
      ⟨affineLinearPart (x : Equiv.Perm K) (haff x x.2), fun a => by
        rw [toAdd_ofAdd, ← hH x x.2 a, affineLinearPart_apply]⟩⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hinj
    apply Multiplicative.toAdd.injective
    ext a
    rw [affineLinearPartHom_apply, affineLinearPartHom_apply]
    have h1 := congrArg (fun z : SzEight.equivariantAddAut (fun a : K => a ^ 5) =>
      Multiplicative.toAdd (z : Multiplicative (AddAut K)) (a ^ 5)) hxy
    simp only [F, toAdd_ofAdd] at h1
    rw [← hH x x.2 a, ← hH y y.2 a] at h1
    exact pow_five_injective hK h1
  have h1 := Nat.card_le_card_of_injective F hFinj
  rw [hN, SzEight.card_equivariantAddAut_pow_five hK] at h1
  omega

end Eight

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem sq_eq_one_of_mem_szCand (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hγ : γ = 0) {x : G}
    (hx : x ∈ szR T₁ R₂ t) (hxC : φ x ∈ szCand a c) : x ^ 2 = 1 := by
  refine h.v_inj _ (h.sq_mem x hx) ?_
  rw [h.sq x hx, szSqMap, hγ, hxC.1]
  have h2 := hxC.2
  linear_combination h2

theorem conj_mem_szCand (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) {y : G}
    (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) {x : G} (hx : x ∈ szR T₁ R₂ t)
    (hxC : φ x ∈ szCand a c) : y * x * y⁻¹ ∈ szR T₁ R₂ t ∧ φ (y * x * y⁻¹) ∈ szCand a c := by
  have hyx : y * x * y⁻¹ ∈ szR T₁ R₂ t := (mem_normalizer_iff.mp hy x).mp hx
  refine ⟨hyx, h.mem_szCand_of_sq_eq_one hγ hyx ?_ ?_⟩
  · rw [show (y * x * y⁻¹) ^ 2 = y * x ^ 2 * y⁻¹ by simp only [_root_.sq]; group,
      h.sq_eq_one_of_mem_szCand hγ hx hxC]
    group
  · intro hmem
    have hxH : x ∈ T₁ ⊔ R₂ := by
      have h1 := (mem_normalizer_iff''.mp (h.normalizer_le_normalizer_sup ha hK hγ hy) _).mp hmem
      simpa [mul_assoc] using h1
    have h0 := (h.thd_eq_zero_iff x hx).mpr hxH
    rw [hxC.1] at h0
    exact one_ne_zero h0

theorem exists_equiv_coord (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (cd : K × K × K → K)
    (hinj : ∀ z ∈ szCand a c, ∀ z' ∈ szCand a c, cd z = cd z' → z = z')
    (hsurj : ∀ w, ∃ z ∈ szCand a c, cd z = w) :
    ∃ e : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) ≃ K,
      ∀ (S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) (x : G),
        x ∈ szR T₁ R₂ t → φ x ∈ szCand a c → (S : Subgroup G) = szA₁ T₁ ⊔ zpowers x →
          e S = cd (φ x) := by
  classical
  choose xs hxsR hxsC hxsS using fun S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) =>
    h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt S.2
  let f : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) → K := fun S => cd (φ (xs S))
  have hf : ∀ (S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) (x : G),
      x ∈ szR T₁ R₂ t → φ x ∈ szCand a c → (S : Subgroup G) = szA₁ T₁ ⊔ zpowers x →
        f S = cd (φ x) := by
    intro S x hx hxC hSx
    have h1 := h.map_eq_of_szA₁_sup_zpowers_eq (hxsR S) (map_ne_zero_of_thd_eq_one hxC.1)
      ((hxsS S).symm.trans hSx)
    show cd (φ (xs S)) = cd (φ x)
    rw [h1]
  have hbij : Function.Bijective f := by
    refine ⟨fun S S' hSS => Subtype.ext ?_, fun w => ?_⟩
    · have h1 := hinj _ (hxsC S) _ (hxsC S') hSS
      rw [hxsS S, hxsS S']
      exact h.szA₁_sup_zpowers_eq_of_map_eq (hxsR S) (hxsR S') h1
    · obtain ⟨z, hzC, hzw⟩ := hsurj w
      obtain ⟨x, hx, hxz⟩ := h.surj z (Or.inr hzC.1)
      have hxC : φ x ∈ szCand a c := hxz ▸ hzC
      refine ⟨⟨_, h.mem_gmsRootConjugates_of_mem_szCand hG hS hc ha hK hμ hCt hx hxC⟩, ?_⟩
      rw [hf _ x hx hxC rfl, hxz, hzw]
  exact ⟨Equiv.ofBijective f hbij, fun S x hx hxC hSx => hf S x hx hxC hSx⟩

theorem equiv_coord_action (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) (cd : K × K × K → K)
    {e : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) ≃ K}
    (he : ∀ (S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) (x : G),
        x ∈ szR T₁ R₂ t → φ x ∈ szCand a c → (S : Subgroup G) = szA₁ T₁ ⊔ zpowers x →
          e S = cd (φ x))
    (y : normalizer (szR T₁ R₂ t : Set G))
    (S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) {x : G}
    (hx : x ∈ szR T₁ R₂ t) (hxC : φ x ∈ szCand a c) (hSx : (S : Subgroup G) = szA₁ T₁ ⊔ zpowers x) :
    e (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) y S) =
      cd (φ ((y : G) * x * (y : G)⁻¹)) := by
  obtain ⟨hyx, hyxC⟩ := h.conj_mem_szCand ha hK hγ y.2 hx hxC
  refine he _ _ hyx hyxC ?_
  have hy' : (y : G)⁻¹ ∈ normalizer (szA₁ T₁ : Set G) :=
    h.normalizer_szR_le_normalizer_szA₁ ha hK (inv_mem y.2)
  have h1 := map_conj_szA₁_sup_zpowers hy' x
  simp only [inv_inv] at h1
  show (S : Subgroup G).map (MulAut.conj (y : G)).toMonoidHom = _
  rw [hSx, h1]

end SzRCoords2

end CFSG.SeitzReduction.RankOne
