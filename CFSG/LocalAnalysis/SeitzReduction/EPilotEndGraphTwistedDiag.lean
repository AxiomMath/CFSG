module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.SeitzReduction.EPilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K]

theorem cartanChar_E6_zero (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨0, by decide⟩ = c 0 ^ 2 * (c 2)⁻¹ := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 0 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem cartanChar_E6_one (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨1, by decide⟩ = c 1 ^ 2 * (c 3)⁻¹ := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 1 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem cartanChar_E6_two (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨2, by decide⟩ = (c 0)⁻¹ * c 2 ^ 2 * (c 3)⁻¹ := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 2 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem cartanChar_E6_three (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨3, by decide⟩ =
      (c 1)⁻¹ * (c 2)⁻¹ * c 3 ^ 2 * (c 4)⁻¹ := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 3 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem cartanChar_E6_four (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨4, by decide⟩ = (c 3)⁻¹ * c 4 ^ 2 * (c 5)⁻¹ := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 4 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem cartanChar_E6_five (c : Fin 6 → Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) c ⟨5, by decide⟩ = (c 4)⁻¹ * c 5 ^ 2 := by
  show ∏ j : Fin 6, c j ^ Tag.cartanE 6 j 5 = _
  rw [Fin.prod_univ_six]
  simp [Tag.cartanE]

theorem perm_E6_zero : TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide

theorem perm_E6_one : TwistTag.E6.perm ⟨1, by decide⟩ = ⟨1, by decide⟩ := by decide

theorem perm_E6_two : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide

theorem perm_E6_three : TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide

theorem perm_E6_four : TwistTag.E6.perm ⟨4, by decide⟩ = ⟨2, by decide⟩ := by decide

theorem perm_E6_five : TwistTag.E6.perm ⟨5, by decide⟩ = ⟨0, by decide⟩ := by decide

theorem exists_compat_cartanChar_eq_of_mod_three [Finite K] {q : ℕ} (hq : q % 3 = 1)
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) :
    ∃ c : Fin TwistTag.E6.tag.rank → Kˣ,
      (∀ i, c (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (c i)) ∧
      cartanChar c = b := by
  have : Fintype K := Fintype.ofFinite K
  set s : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hs
  have hsv : ∀ v : Kˣ, ((s v : Kˣ) : K) = σ (v : K) := fun v => rfl
  have hsq : ∀ v : Kˣ, s v = v ^ q := fun v =>
    Units.ext (by rw [hsv, hσ, Units.val_pow_eq_pow_val])
  have hss : ∀ v : Kˣ, s (s v) = v := fun v => Units.ext (by
    rw [hsv, hsv, hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card])
  have hb1 : s (b ⟨1, by decide⟩) = b ⟨1, by decide⟩ := by
    have h := hb ⟨1, by decide⟩
    rw [perm_E6_one] at h
    exact h.symm
  have hb3 : s (b ⟨3, by decide⟩) = b ⟨3, by decide⟩ := by
    have h := hb ⟨3, by decide⟩
    rw [perm_E6_three] at h
    exact h.symm
  have hb4 : b ⟨4, by decide⟩ = s (b ⟨2, by decide⟩) := by
    have h := hb ⟨2, by decide⟩
    rw [perm_E6_two] at h
    exact h
  have hb5 : b ⟨5, by decide⟩ = s (b ⟨0, by decide⟩) := by
    have h := hb ⟨0, by decide⟩
    rw [perm_E6_zero] at h
    exact h
  set b0 := b ⟨0, by decide⟩ with hb0d
  set b1 := b ⟨1, by decide⟩ with hb1d
  set b2 := b ⟨2, by decide⟩ with hb2d
  set b3 := b ⟨3, by decide⟩ with hb3d
  set m := (q + 2) / 3 with hm
  have hm3 : m * 3 = q + 2 := by omega
  set A : Kˣ := b2 * b0 ^ 2 * b1⁻¹ with hA
  set B : Kˣ := b3 * b1 ^ 2 * (b0 * s b0)⁻¹ with hB
  set NA : Kˣ := A * s A with hNA
  set z : Kˣ := B ^ 3 * NA ^ 2 with hz
  set n : Kˣ := NA ^ 3 * B ^ 4 with hn
  set cc : Kˣ := A * z ^ 2 with hcc
  set x : Kˣ := cc ^ m * n⁻¹ with hx
  set y : Kˣ := x ^ 2 * b0⁻¹ with hy
  set w : Kˣ := z ^ 2 * b1⁻¹ with hw
  clear_value w y x cc n z NA B A m
  have hsB : s B = B := by
    rw [hB, map_mul, map_mul, map_inv, map_mul, map_pow, hb1, hb3, hss, mul_comm (s b0) b0]
  have hsNA : s NA = NA := by rw [hNA, map_mul, hss, mul_comm]
  have hsz : s z = z := by rw [hz, map_mul, map_pow, map_pow, hsB, hsNA]
  have hsw : s w = w := by rw [hw, map_mul, map_pow, map_inv, hsz, hb1]
  have hccq : cc ^ (q + 1) = n ^ 3 := by
    rw [pow_succ, ← hsq, hcc, map_mul, map_pow, hsz, hn, hz, hNA]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have hx3 : x ^ 3 = cc := by
    rw [hx, mul_pow, ← pow_mul, hm3, show q + 2 = (q + 1) + 1 by ring, pow_succ, hccq, inv_pow,
      mul_comm (n ^ 3) cc, mul_inv_cancel_right]
  have hxN : x * s x = n := by
    rw [hsq x, ← pow_succ', hx, mul_pow, ← pow_mul, mul_comm m (q + 1), pow_mul, hccq,
      ← pow_mul, mul_comm 3 m, hm3, inv_pow, show q + 2 = (q + 1) + 1 by ring, pow_succ,
      mul_comm (n ^ (q + 1)) n, mul_inv_cancel_right]
  have hz3 : z ^ 3 = B * n ^ 2 := by
    rw [hz, hn]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have h0 : x ^ 2 * y⁻¹ = b0 := by
    rw [hy, mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have h1 : z ^ 2 * w⁻¹ = b1 := by
    rw [hw, mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have h2 : x⁻¹ * y ^ 2 * w⁻¹ = b2 := by
    have e : x⁻¹ * y ^ 2 * w⁻¹ = x ^ 3 * (b0 ^ 2)⁻¹ * (z ^ 2)⁻¹ * b1 := by
      rw [hy, hw]
      ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
    rw [e, hx3, hcc, hA]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  have h3 : z⁻¹ * y⁻¹ * w ^ 2 * (s y)⁻¹ = b3 := by
    have e : z⁻¹ * y⁻¹ * w ^ 2 * (s y)⁻¹ =
        z ^ 3 * (b1 ^ 2)⁻¹ * (b0 * s b0) * ((x * s x) ^ 2)⁻¹ := by
      rw [hy, hw, map_mul, map_pow, map_inv]
      ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
    rw [e, hxN, hz3, hB]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨![x, z, y, w, s y, s x], fun i => ?_, ?_⟩
  · fin_cases i
    · rw [perm_E6_zero]
      rfl
    · rw [perm_E6_one]
      exact hsz.symm
    · rw [perm_E6_two]
      rfl
    · rw [perm_E6_three]
      exact hsw.symm
    · rw [perm_E6_four]
      exact (hss y).symm
    · rw [perm_E6_five]
      exact (hss x).symm
  · funext l
    fin_cases l
    · exact (cartanChar_E6_zero _).trans h0
    · exact (cartanChar_E6_one _).trans h1
    · exact (cartanChar_E6_two _).trans h2
    · exact (cartanChar_E6_three _).trans h3
    · refine (cartanChar_E6_four _).trans ?_
      show w⁻¹ * s y ^ 2 * (s x)⁻¹ = b ⟨4, by decide⟩
      rw [hb4, ← h2, map_mul, map_mul, map_inv, map_pow, map_inv, hsw]
      ac_rfl
    · refine (cartanChar_E6_five _).trans ?_
      show (s y)⁻¹ * s x ^ 2 = b ⟨5, by decide⟩
      rw [hb5, ← h0, map_mul, map_inv, map_pow]
      ac_rfl

theorem twistedE6_compatDiagAutHom_mem_inner [Finite K] {q : ℕ} (hq : q % 3 = 1)
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨c, hc, hcb⟩ :=
    exists_compat_cartanChar_eq_of_mod_three hq hK σ hσ _ (compatDiag_perm u)
  obtain ⟨w, hw⟩ := exists_compatDiag_eq hc
  have hmem : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rw [pow_one, ← hcb, ← hw, ← list_prod_orbitH_eq_rootDiagUnit]
    exact Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
      exact orbitH_mem_graphFixedRootGroup _ _ _ _
  exact ⟨⟨_, hmem⟩, (compatDiagAutHom_pow_eq_conj u 1 hmem).symm.trans (pow_one _)⟩

theorem twistedE6_exists_eq_conj_mul_fieldActor [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (δ : K ≃+* K),
      α = MulAut.conj g * fieldActor σ δ := by
  obtain ⟨-, -, -, -, -, -, -, hNF, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  obtain ⟨g, u, δ, rfl⟩ := hNF α
  obtain ⟨h, hh⟩ := twistedE6_compatDiagAutHom_mem_inner hq hK σ hσ u
  refine ⟨g * h, δ, ?_⟩
  rw [← hh, map_mul]

end CFSG.SeitzReduction.EPilot
