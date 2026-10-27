module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Module
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section SL2

theorem sl2_sq_eq_one_of_fixed {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} {v : Fin 2 → F} (hv : v ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : g ^ 2 = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have htr : a + d = 0 := by
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h => hv (by ext i; fin_cases i <;> simp [hv0, h])
      rw [hv0] at h0 h1
      have hb0 : b = 0 := by
        have : b * v 1 = 0 := by linear_combination h0
        exact (mul_eq_zero.1 this).resolve_right hv1
      have hd1 : d = 1 := by
        have : (d - 1) * v 1 = 0 := by linear_combination h1
        have := (mul_eq_zero.1 this).resolve_right hv1
        linear_combination this
      have : a = 1 := by
        rw [hb0, hd1] at hdet
        linear_combination hdet
      rw [this, hd1]; linear_combination h2
    · have e : ((a - 1) * (d - 1) - b * c) * v 0 = 0 := by
        linear_combination (d - 1) * h0 - b * h1
      have := (mul_eq_zero.1 e).resolve_right hv0
      linear_combination h2 - this + hdet
  have hmat : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination a * htr - hdet - h2
    · linear_combination b * htr
    · linear_combination c * htr
    · linear_combination d * htr - hdet - h2
  apply Subtype.ext
  simpa [pow_two] using hmat

end SL2

theorem exists_two_fixedPoints_of_pow_three (σ : Equiv.Perm (Fin 5)) (h3 : σ ^ 3 = 1) :
    ∃ p q : Fin 5, p ≠ q ∧ σ p = p ∧ σ q = q := by
  classical
  have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f : Function.End (Fin 5) := (⇑σ : Fin 5 → Fin 5)
  have hf : f ^ 3 ^ 1 = 1 := by
    funext x
    have h := congrArg (fun τ : Equiv.Perm (Fin 5) => τ x) h3
    simp [pow_succ, Equiv.Perm.mul_apply] at h
    show (f ^ 3) x = x
    simp [f]
    exact h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have h2 : 1 < Fintype.card (Function.fixedPoints f) := by
    rw [Fintype.card_fin] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  exact ⟨a.1, b.1, fun h => hab (Subtype.ext h), a.2, b.2⟩

theorem q_eq_four_of_card (q : ℕ) (hq : 4 ≤ q) (h : q * (q ^ 2 - 1) = 60) : q = 4 := by
  by_contra hne
  have h5 : 5 ≤ q := by omega
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have h24 : 24 ≤ q ^ 2 - 1 := by omega
  have := Nat.mul_le_mul h5 h24
  omega

section Normal

variable {G : Type*} [Group G]

theorem le_normalizer_blockU (L : Subgroup G) : L ≤ Subgroup.normalizer (blockU L : Set G) := by
  intro g hg
  rw [← conjR_eq_self_iff]
  have hQ : conjR (blockQ L) g = blockQ L := by
    apply conjR_eq_of_mem_normalizer
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L hg
  have hL : conjR L g = L := conjR_eq_of_mem hg
  have : conjR (⁅blockQ L, L⁆) g = ⁅conjR (blockQ L) g, conjR L g⁆ := by
    simp only [conjR_def]
    exact Subgroup.map_commutator _ _ _
  unfold blockU
  rw [this, hQ, hL]

end Normal

theorem lin2_not_alt {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} (hn : 1 < n)
    (h : IsLin2Type L n) {m : ℕ} (hm : m = 3 ∨ m = 5) : ¬ IsAltType L m := by
  rintro ⟨α', hα', hker', β', hβ', hβker', hβeq'⟩
  obtain ⟨F, hF, hFin, hcard, α, hα, hker, β, hβ, hβker, hβeq⟩ := h
  have hK : α.ker = α'.ker := hker.trans hker'.symm
  have c1 := Subgroup.card_ker_mul_card_of_surjective hα
  have c2 := Subgroup.card_ker_mul_card_of_surjective hα'
  rw [hK] at c1
  have hpos : 0 < Nat.card α'.ker := Nat.card_pos
  have hcardeq : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card (alternatingGroup (Fin m)) := Nat.eq_of_mul_eq_mul_left hpos (c1.trans c2.symm)
  have hSLcard := card_sl2 F
  rw [hcard] at hSLcard
  rw [hSLcard] at hcardeq
  have hq4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq60 : 60 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h15 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have := Nat.mul_le_mul hq4 h15
    omega
  rcases hm with rfl | rfl
  · have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega
  · have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hA] at hcardeq
    have hq : 2 ^ n = 4 := q_eq_four_of_card _ hq4 hcardeq
    have h2 : (2 : F) = 0 := by
      have h0 := FiniteField.cast_card_eq_zero F
      rw [hcard] at h0
      push_cast at h0
      exact pow_eq_zero_iff (by omega : n ≠ 0) |>.1 h0
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
      rw [hSLcard, hcardeq]
    have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) F) 3
      (by rw [hSL]; norm_num)
    obtain ⟨ℓ, hℓ⟩ := hα g
    have hℓ3 : α (ℓ ^ 3) = 1 := by
      rw [map_pow, hℓ, ← hg]; exact pow_orderOf_eq_one g
    have hℓK : ℓ ^ 3 ∈ α'.ker := hK ▸ hℓ3
    set σ : Equiv.Perm (Fin 5) := ((α' ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) with hσ
    have hσ3 : σ ^ 3 = 1 := by
      have : α' (ℓ ^ 3) = 1 := hℓK
      rw [map_pow] at this
      have := congrArg (fun τ : alternatingGroup (Fin 5) => (τ : Equiv.Perm (Fin 5))) this
      simpa [hσ] using this
    obtain ⟨p, q, hpq, hσp, hσq⟩ := exists_two_fixedPoints_of_pow_three σ hσ3
    let w : Fin 5 → ZMod 2 := Pi.single p 1 + Pi.single q 1
    have hw : w ∈ evenWeight 5 := by
      show (∑ i, w i) = 0
      simp only [w, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
        ite_true]
      decide
    have hwp : w p = 1 := by simp [w, hpq]
    obtain ⟨u, hu⟩ := hβ' (Multiplicative.ofAdd (⟨w, hw⟩ : evenWeight 5))
    have hUℓ : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_blockU L ℓ.2) (u : G)).1 u.2
    have hfix : β' ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hUℓ⟩ = β' u := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      have := hβeq' ℓ u ⟨_, hUℓ⟩ rfl i
      rw [this, hu]
      change w (σ⁻¹ i) = w i
      have hip : σ⁻¹ i = p ↔ i = p := by rw [Equiv.Perm.inv_eq_iff_eq, hσp]
      have hiq : σ⁻¹ i = q ↔ i = q := by rw [Equiv.Perm.inv_eq_iff_eq, hσq]
      simp only [w, Pi.add_apply, Pi.single_apply, hip, hiq]
    have hu0' : β' u ≠ 1 := by
      rw [hu]
      intro h1
      have h2 := congrArg Multiplicative.toAdd h1
      have h3 : (⟨w, hw⟩ : evenWeight 5) = 0 := h2
      have h4 := congrArg (fun z : evenWeight 5 => (z : Fin 5 → ZMod 2) p) h3
      simp at h4
      rw [hwp] at h4
      exact one_ne_zero h4
    have hu0 : β u ≠ 1 := by
      intro h
      apply hu0'
      have : u ∈ β.ker := h
      rw [hβker, ← hβker'] at this
      exact this
    have hvu : β ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hUℓ⟩ = β u := by
      have hk1 : (⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hUℓ⟩ : blockU L) * u⁻¹ ∈ β'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, mul_inv_cancel]
      have hk2 : (⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hUℓ⟩ : blockU L) * u⁻¹ ∈ β.ker := by
        rw [hβker]; rw [hβker'] at hk1; exact hk1
      rw [MonoidHom.mem_ker, map_mul, map_inv] at hk2
      exact mul_inv_eq_one.1 hk2
    have hfixed : (g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) =
        Multiplicative.toAdd (β u) := by
      have := hβeq ℓ u ⟨_, hUℓ⟩ rfl
      rw [hvu, hℓ] at this
      exact this.symm
    have hx : Multiplicative.toAdd (β u) ≠ 0 := fun h => hu0 (by
      have : β u = Multiplicative.ofAdd 0 := by rw [← h]; rfl
      rw [this]; rfl)
    have hg2 := sl2_sq_eq_one_of_fixed h2 hx hfixed
    have := orderOf_dvd_of_pow_eq_one hg2
    rw [hg] at this
    omega
