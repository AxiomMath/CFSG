module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Heis
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeightsSwap

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix Module CFSG.LieType.Universal.Unitary

section Excl

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

include h hodd

theorem lineProj_ne_zero_of_trans_excl (hfaith : ∀ x, ρ x = 1 → x = 0)
    (htrans : ∀ u : K × K, u.1 ≠ 0 → ∃ (γ : K × K → K × K) (g : E ≃ₗ[ZMod 2] E),
      Function.Bijective γ ∧ (∀ (k : K) (x : K × K), γ (k • x) = k • γ x) ∧ γ (1, 0) = u ∧
        ∀ x, g * ρ x * g⁻¹ = ρ (γ x)) :
    ∀ u : K × K, u.1 ≠ 0 → lineProj ρ u ≠ 0 := by
  classical
  have h10 : lineProj ρ (1, 0) ≠ 0 := by
    intro h0
    have hm : ∀ m : K, lineProj ρ (1, m) = 0 := by
      intro m
      obtain ⟨γ, g, hb, hk, hγ, hg⟩ := htrans (1, m) one_ne_zero
      rw [← hγ, ← lineProj_conj hb hk hg, h0]
      simp
    have hsum := sum_lineProj_rep h hodd
    rw [Fintype.sum_option] at hsum
    simp only [lineRep] at hsum
    rw [Finset.sum_eq_zero fun m _ => hm m, add_zero] at hsum
    have e1 : opE ρ (0, 1) * lineProj ρ (0, 1) = lineProj ρ (0, 1) := by
      simpa using opE_mul_lineProj h (1 : K) (0, 1)
    rw [hsum, mul_add, opE_mul_fullSum h, mul_one] at e1
    have e2 : opE ρ (0, 1) = 1 := add_left_cancel e1
    have e3 : ρ (0, 1) = 1 := by
      ext x
      have := LinearMap.congr_fun e2 x
      simpa [opE] using this
    have := hfaith _ e3
    exact one_ne_zero (congrArg Prod.snd this)
  intro u hu
  obtain ⟨γ, g, hb, hk, hγ, hg⟩ := htrans u hu
  rw [← hγ, ← lineProj_conj hb hk hg]
  exact conj_ne_zero h10

end Excl

section Rank

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def negT : SU σ 3 :=
  ⟨torGL (neg_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0)),
    torGL_mem_SU σ (neg_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0)) (by rw [map_neg, map_one])⟩

theorem negT_mul_self : negT σ * negT σ = (1 : SU σ 3) :=
  Subtype.ext torGL_neg_one_mul_self

variable {σ}

theorem negT_mul_vH {F : Type} [Field F] {ι : F →+* K} {ω : K} (x y : F) :
    (negT σ : GL (Fin 3) K) * vH σ ι ω x y = vH σ ι ω (-x) y * negT σ :=
  torGL_mul_vH (neg_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0)) (by rw [map_neg, map_one]) x y (-x) y
    (by rw [map_neg, neg_one_mul]) (by rw [neg_one_sq, one_mul])

theorem natCast_ne_zero_of_lt {F : Type} [Field F] {p : ℕ} [CharP F p] {a : ℕ} (h0 : 0 < a)
    (hp : a < p) : (a : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  exact absurd (Nat.le_of_dvd h0 h) (not_le.2 hp)

theorem natCast_inj_of_lt {F : Type} [Field F] {p : ℕ} [CharP F p] {a b : ℕ} (ha : a < p)
    (hb : b < p) (h : (a : F) = b) : a = b := by
  have := (CharP.natCast_eq_natCast F p).1 h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem negT_rank_ge_four {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E] {p : ℕ} [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    {F : Type} [Field F] [Fintype F] [CharP F p] (hFcard : Fintype.card F = p)
    (hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k) (ι : F →+* K) (hι : ∀ x : F, σ (ι x) = ι x)
    (hσ : ∀ x, σ (σ x) = x) {ω : K} (hω : σ ω = -ω) (hω0 : ω ≠ 0)
    (ρ : SU σ 3 →* (E ≃ₗ[ZMod 2] E))
    (hρ : ∀ g : SU σ 3, ρ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ (negT σ)))) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  let vS : F → F → SU σ 3 := fun x y => ⟨vH σ ι ω x y, vH_mem h2 hσ hι hω x y⟩
  have hvS_mul : ∀ x y x' y', vS x y * vS x' y' = vS (x + x') (y + y') := fun x y x' y' =>
    Subtype.ext (vH_mul h2 hι x y x' y')
  have hvS_zero : vS 0 0 = 1 := Subtype.ext vH_zero
  let ρ' : F × F → (E ≃ₗ[ZMod 2] E) := fun z => ρ (vS z.1 z.2)
  have hV : IsVAct ρ' :=
    ⟨by simp [ρ', hvS_zero], fun a b => by
      show ρ (vS (a.1 + b.1) (a.2 + b.2)) = ρ (vS a.1 a.2) * ρ (vS b.1 b.2)
      rw [← map_mul, hvS_mul]⟩
  have hodd : Odd (Fintype.card F) := by rw [hFcard]; exact hpodd
  have hfaith : ∀ z, ρ' z = 1 → z = 0 := by
    intro z hz
    obtain ⟨r, hr⟩ := hρ _ hz
    obtain ⟨hx, hy⟩ := vH_not_scalar hω0 hr
    exact Prod.ext hx hy
  let τ : F × F → F × F := fun z => (-z.1, z.2)
  have hτ2 : ∀ z, τ (τ z) = z := fun z => by simp [τ]
  have hτk : ∀ (k : F) (z : F × F), τ (k • z) = k • τ z := by
    intro k z
    simp [τ, Prod.smul_mk]
  have hs : ρ (negT σ) * ρ (negT σ) = 1 := by rw [← map_mul, negT_mul_self, map_one]
  have hsρ : ∀ z, ρ (negT σ) * ρ' z * ρ (negT σ) = ρ' (τ z) := by
    intro z
    have h1 : negT σ * vS z.1 z.2 = vS (-z.1) z.2 * negT σ := Subtype.ext (negT_mul_vH z.1 z.2)
    calc ρ (negT σ) * ρ' z * ρ (negT σ) = ρ (negT σ * vS z.1 z.2 * negT σ) := by
          simp only [ρ', map_mul]
      _ = ρ (vS (-z.1) z.2 * (negT σ * negT σ)) := by rw [h1, mul_assoc]
      _ = ρ' (τ z) := by rw [negT_mul_self, mul_one]
  have htrans : ∀ u : F × F, u.1 ≠ 0 → ∃ (γ : F × F → F × F)
      (g : E ≃ₗ[ZMod 2] E), Function.Bijective γ ∧
      (∀ (k : F) (x : F × F), γ (k • x) = k • γ x) ∧ γ (1, 0) = u ∧
        ∀ x, g * ρ' x * g⁻¹ = ρ' (γ x) := by
    intro u hu
    obtain ⟨u1, u2⟩ := u
    simp only at hu
    have hdK : ι u1 ≠ 0 := fun h0 => hu (ι.injective (by rw [map_zero]; exact h0))
    let tS : SU σ 3 := ⟨torGL hdK, torGL_mem_SU σ hdK (hι u1)⟩
    let sS : SU σ 3 := ⟨shearGL σ ι ω (u2 / u1), shearGL_mem h2 hσ hι hω (u2 / u1)⟩
    refine ⟨fun z => (u1 * z.1, u1 ^ 2 * z.2 + (u2 / u1) * (u1 * z.1)), ρ sS * ρ tS, ?_, ?_, ?_,
      ?_⟩
    · rw [Function.bijective_iff_has_inverse]
      refine ⟨fun w => (w.1 / u1, (w.2 - (u2 / u1) * w.1) / u1 ^ 2), fun z => ?_, fun w => ?_⟩
      · refine Prod.ext ?_ ?_
        · simp only; field_simp
        · simp only; field_simp; ring
      · refine Prod.ext ?_ ?_
        · simp only; field_simp
        · simp only; field_simp; ring
    · rintro k ⟨a, b⟩
      simp only [Prod.smul_mk, smul_eq_mul]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    · refine Prod.ext (by simp) ?_
      simp only [mul_zero, zero_add, mul_one]
      field_simp
    · intro x
      have h1 : tS * vS x.1 x.2 = vS (u1 * x.1) (u1 ^ 2 * x.2) * tS :=
        Subtype.ext (torGL_mul_vH hdK (hι u1) x.1 x.2 (u1 * x.1) (u1 ^ 2 * x.2)
          (by rw [map_mul]) (by rw [map_mul, map_pow]))
      have h2' : sS * vS (u1 * x.1) (u1 ^ 2 * x.2) =
          vS (u1 * x.1) (u1 ^ 2 * x.2 + (u2 / u1) * (u1 * x.1)) * sS :=
        Subtype.ext (shearGL_mul_vH h2 hι hω (u2 / u1) _ _)
      rw [mul_inv_eq_iff_eq_mul]
      show ρ sS * ρ tS * ρ (vS x.1 x.2) =
        ρ (vS (u1 * x.1) (u1 ^ 2 * x.2 + (u2 / u1) * (u1 * x.1))) * (ρ sS * ρ tS)
      rw [← map_mul, ← map_mul, ← map_mul, mul_assoc, h1, ← mul_assoc, h2', mul_assoc]
  have hne := lineProj_ne_zero_of_trans_excl hV hodd hfaith htrans
  let U : Finset (F × F) :=
    (Finset.Icc 1 ((p - 1) / 2)).image (fun n : ℕ => ((1 : F), (n : F)))
  have hmem : ∀ u ∈ U, ∃ n : ℕ, 1 ≤ n ∧ n ≤ (p - 1) / 2 ∧ u = ((1 : F), (n : F)) := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨n, (Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2, rfl⟩
  have hself : ∀ u ∈ U, det2 u (τ u) ≠ 0 := by
    intro u hu
    obtain ⟨n, hn1, hn2, rfl⟩ := hmem u hu
    have : det2 ((1 : F), (n : F)) (τ ((1 : F), (n : F))) = ((2 * n : ℕ) : F) := by
      simp only [det2, τ]
      push_cast
      ring
    rw [this]
    exact natCast_ne_zero_of_lt (by omega) (by omega)
  have hpair : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 ∧ det2 u (τ v) ≠ 0 ∧
      det2 (τ u) v ≠ 0 ∧ det2 (τ u) (τ v) ≠ 0 := by
    intro u hu v hv huv
    obtain ⟨n, hn1, hn2, rfl⟩ := hmem u hu
    obtain ⟨n', hn1', hn2', rfl⟩ := hmem v hv
    have hnn : n ≠ n' := fun h => huv (by rw [h])
    have hsum : ((n + n' : ℕ) : F) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
    have hdiff : (n' : F) - n ≠ 0 := by
      intro h0
      exact hnn (natCast_inj_of_lt (F := F) (p := p) (by omega) (by omega) (sub_eq_zero.1 h0).symm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [det2]
      intro h0
      apply hdiff
      linear_combination h0
    · simp only [det2, τ]
      intro h0
      apply hsum
      push_cast
      linear_combination h0
    · simp only [det2, τ]
      intro h0
      apply hsum
      push_cast
      linear_combination -h0
    · simp only [det2, τ]
      intro h0
      apply hdiff
      linear_combination -h0
  have hUne : ∀ u ∈ U, lineProj ρ' u ≠ 0 := by
    intro u hu
    obtain ⟨n, -, -, rfl⟩ := hmem u hu
    exact hne _ one_ne_zero
  have hUcard : U.card = (p - 1) / 2 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro n hn n' hn' h
      have h' : (n : F) = n' := congrArg Prod.snd h
      have := (Finset.mem_Icc.1 hn).2
      have := (Finset.mem_Icc.1 hn').2
      exact natCast_inj_of_lt (F := F) (p := p) (by omega) (by omega) h'
  have := card_le_finrank_range_sub1_swap hV hodd hFK hs hτ2 hτk hsρ U hself hpair hUne
  rw [hUcard] at this
  omega

end Rank

end CFSG.QuasithinUnique.Setup.Family
