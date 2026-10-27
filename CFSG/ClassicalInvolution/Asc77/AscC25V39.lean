module

public import CFSG.ClassicalInvolution.Asc77.AscC25V36
public import CFSG.ClassicalInvolution.Asc77.AscC25V38

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_comm_z_of_isFAut {R : Subgroup G} {z a : G} (hR : IsQuatSub R)
    (hz : IsUniqueInvolution R z) (hF : IsFAut R a) (ha2 : a * a = 1) :
    ∃ k ∈ R, a * k * a⁻¹ = z * k := by
  classical
  obtain ⟨x, hxR, -, hxa, hxne, -⟩ :=
    T7T.exists_cyclic_of_isFAut hR hz hF (isPGroup_two_zpowers_of_sq ha2)
  obtain ⟨k₀, hk₀, hRk⟩ := hR.natCard_eq
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := k₀ + 2) hRk
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hxa
  have hwx : a * x * a⁻¹ * x⁻¹ = x ^ (t - 1) := by
    rw [← ht, zpow_sub, zpow_one]
  have hxcomm : Commute (a * x * a⁻¹ * x⁻¹) x := by
    rw [hwx]
    exact (Commute.self_zpow x _).symm
  have hw1 : a * x * a⁻¹ * x⁻¹ ≠ 1 := by
    intro h
    apply hxne
    calc a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
      _ = x := by rw [h, one_mul]
  have hwR : a * x * a⁻¹ * x⁻¹ ∈ R := by
    rw [hwx]
    exact R.zpow_mem hxR _
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hR2 ⟨_, hwR⟩
  have hj' : orderOf (a * x * a⁻¹ * x⁻¹) = 2 ^ j := by
    rw [← hj, ← Subgroup.orderOf_coe]
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero] at hj'
      exact absurd (orderOf_eq_one_iff.mp hj') hw1
    · exact h0
  have hw' : (a * x * a⁻¹ * x⁻¹) ^ 2 ^ (j - 1) = z := by
    have hsq : (a * x * a⁻¹ * x⁻¹) ^ 2 ^ (j - 1) * (a * x * a⁻¹ * x⁻¹) ^ 2 ^ (j - 1) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hj1, ← hj']
      exact pow_orderOf_eq_one _
    have hne : (a * x * a⁻¹ * x⁻¹) ^ 2 ^ (j - 1) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf
      · positivity
      · rw [hj']
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rcases hz.unique _ (R.pow_mem hwR _) hsq with h | h
    · exact absurd h hne
    · exact h
  refine ⟨x ^ 2 ^ (j - 1), R.pow_mem hxR _, ?_⟩
  have hconj : a * x ^ 2 ^ (j - 1) * a⁻¹ = (a * x * a⁻¹) ^ 2 ^ (j - 1) := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
  have hdecomp : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
  rw [hconj, hdecomp, hxcomm.mul_pow, hw']

end Basic

section K'

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fieldChar_eq_one_of_mem_K' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {x : G} (hx : x ∈ K') :
    ∃ hxN : x ∈ Subgroup.normalizer (K : Set G), fieldChar hp hq e ⟨x, hxN⟩ = 1 := by
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz
  have hcomm := h.hΩ.comm_le_oddCore_of_twin h.hK h.hK' h.hs.hne.symm h.hz h.hz'
  refine ⟨hK'N hx, fieldChar_eq_one_of_comm_mod_odd hp hq e (hK'N hx) (fun l hl => ?_)⟩
  have h1 : ⁅l, x⁆ ∈ oddCoreOf K := (hcomm (Subgroup.commutator_mem_commutator hl hx)).1
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h1

end K'

section Defs

variable (p f : ℕ) [Fact p.Prime]



@[expose] def G1Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G),
    T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → p ^ f = 9 → ∀ a : G, a ∈ (S : Subgroup G) →
      a * a = 1 → IsFAut R' a → a * t' = t' * a →
      z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
          (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (d : G)
          (hdK : d ∈ Subgroup.normalizer (K : Set G)), d * z = z * d → d * a = a * d →
          ∀ (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)),
            Odd (orderOf (fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹))

@[expose] def DIAGS25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
          ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
            (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (n : G),
            n ∈ (S : Subgroup G) → ∀ (hn : n ∈ Subgroup.normalizer (K : Set G))
            (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
              ¬ (n * a = a * n ∨ n * a = a * n * z) →
              diagChar hp hq e ⟨t' * n * t', hn'⟩ = diagChar hp hq e ⟨n, hn⟩ →
                fieldChar hp hq e ⟨t' * n * t', hn'⟩ = fieldChar hp hq e ⟨n, hn⟩

@[expose] def Ident25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
          ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
            (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (n : G),
            n ∈ (S : Subgroup G) → ∀ (hn : n ∈ Subgroup.normalizer (K : Set G))
            (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
              diagChar hp hq e ⟨n, hn⟩ = 1 → diagChar hp hq e ⟨t' * n * t', hn'⟩ = 1 →
                (n * a = a * n ∨ n * a = a * n * z)

end Defs

section Proof

variable {p f : ℕ} [Fact p.Prime]



theorem res25_of_g1 (hG1 : G1_25 p f) (hG9 : G1Nine p f) (hD : DIAGS25 p f) : RES25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hδ
  classical
  by_cases hc : n * a = a * n ∨ n * a = a * n * z
  swap
  · exact hD G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' hc hδ
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  have hG : ∀ (d : G) (hdK : d ∈ Subgroup.normalizer (K : Set G)), d * z = z * d → d * a = a * d →
      ∀ (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)),
        Odd (orderOf (fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹)) := by
    intro d hdK hdz hda hd'
    by_cases h9 : p ^ f = 9
    · exact hG9 G Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hFa' hat hZ hp hq e d hdK hdz hda
        hd'
    · exact hG1 G Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hFa' hat hZ hp hq e d hdK hdz hda
        hd'
  have hnz : n * z = z * n := hyp.hzS n hnS
  have hzz : z * z = 1 := h.hz.sq
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have key : Odd (orderOf (fieldChar hp hq e ⟨n, hn⟩ *
      (fieldChar hp hq e ⟨t' * n * t', hn'⟩)⁻¹)) := by
    rcases hc with hc | hc
    · exact hG n hn hnz hc hn'
    · obtain ⟨k, hkR, hk⟩ := exists_mem_comm_z_of_isFAut h.hqR h.hzR hFa ha2
      have hkK : k ∈ K := h.hRsyl.1 hkR
      have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
      have hkz : k * z = z * k := comm_z_of_mem h.hzR hkR
      have hk' : t' * k * t' ∈ K' := by
        have := conj_mem_conjSub (n := t') hkR
        rw [h.ht'R, h.ht'inv] at this
        exact h.hR'syl.1 this
      obtain ⟨hk'N, hk'χ⟩ := fieldChar_eq_one_of_mem_K' h hp hq e hk'
      have hdK : n * k ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hn hkN
      have hdz : n * k * z = z * (n * k) := by
        calc n * k * z = n * (k * z) := by rw [mul_assoc]
          _ = n * (z * k) := by rw [hkz]
          _ = (n * z) * k := by rw [mul_assoc]
          _ = z * n * k := by rw [hnz]
          _ = z * (n * k) := by rw [mul_assoc]
      have hda : n * k * a = a * (n * k) := by
        have h1 : a * n = n * a * z := by
          calc a * n = (a * n * z) * z := by rw [mul_assoc, hzz, mul_one]
            _ = (n * a) * z := by rw [← hc]
        have h2 : a * k = z * k * a := by
          calc a * k = (a * k * a⁻¹) * a := by group
            _ = z * k * a := by rw [hk]
        calc n * k * a = n * (k * a) := by rw [mul_assoc]
          _ = n * (a * a * (k * a)) := by rw [ha2, one_mul]
          _ = n * a * (a * k) * a := by group
          _ = n * a * (z * k * a) * a := by rw [h2]
          _ = (n * a * z) * k * (a * a) := by group
          _ = (a * n) * k := by rw [ha2, mul_one, ← h1]
          _ = a * (n * k) := by rw [mul_assoc]
      have hd' : t' * (n * k) * t' ∈ Subgroup.normalizer (K : Set G) := by
        have e1 : t' * (n * k) * t' = (t' * n * t') * (t' * k * t') := by
          calc t' * (n * k) * t' = t' * n * (t' * t') * k * t' := by rw [h.ht'2]; group
            _ = (t' * n * t') * (t' * k * t') := by group
        rw [e1]
        exact Subgroup.mul_mem _ hn' hk'N
      have hodd := hG (n * k) hdK hdz hda hd'
      have e1 : (⟨n * k, hdK⟩ : Subgroup.normalizer (K : Set G)) = ⟨n, hn⟩ * ⟨k, hkN⟩ := rfl
      have e2 : (⟨t' * (n * k) * t', hd'⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨t' * n * t', hn'⟩ * ⟨t' * k * t', hk'N⟩ :=
        Subtype.ext (by
          show t' * (n * k) * t' = (t' * n * t') * (t' * k * t')
          calc t' * (n * k) * t' = t' * n * (t' * t') * k * t' := by rw [h.ht'2]; group
            _ = (t' * n * t') * (t' * k * t') := by group)
      rw [e1, e2, map_mul, map_mul, fieldChar_eq_one_of_mem hp hq e hkK hkN, hk'χ, mul_one,
        mul_one] at hodd
      exact hodd
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (⟨n, hnS⟩ : (S : Subgroup G))
  have hi' : n ^ 2 ^ i = 1 := by
    have := pow_orderOf_eq_one (⟨n, hnS⟩ : (S : Subgroup G))
    rw [hi] at this
    exact congrArg Subtype.val this
  have hpow : (fieldChar hp hq e ⟨n, hn⟩ *
      (fieldChar hp hq e ⟨t' * n * t', hn'⟩)⁻¹) ^ 2 ^ i = 1 := by
    have h1 : fieldChar hp hq e ⟨n, hn⟩ ^ 2 ^ i = 1 := by
      rw [← map_pow]
      have : (⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ i = 1 := Subtype.ext hi'
      rw [this, map_one]
    have h2 : fieldChar hp hq e ⟨t' * n * t', hn'⟩ ^ 2 ^ i = 1 := by
      rw [← map_pow]
      have : (⟨t' * n * t', hn'⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ i = 1 := by
        apply Subtype.ext
        change (t' * n * t') ^ 2 ^ i = 1
        have e3 : t' * n * t' = t' * n * t'⁻¹ := by rw [h.ht'inv]
        rw [e3, ← MulAut.conj_apply, ← map_pow]
        simp [hi']
      rw [this, map_one]
    rw [mul_pow, inv_pow, h1, h2]
    simp
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf (fieldChar hp hq e ⟨n, hn⟩ *
      (fieldChar hp hq e ⟨t' * n * t', hn'⟩)⁻¹) = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨j, -, hj⟩
    rw [hj] at key ⊢
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; rfl
    · exfalso
      have : Even (2 ^ j) := (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩)
      exact (Nat.not_even_iff_odd.mpr key) this
  have h1 := orderOf_eq_one_iff.mp hord
  exact (mul_inv_eq_one.mp h1).symm

theorem diags25_of_diag25 (hI : Ident25 p f) (hD : DIAG25 p f) : DIAGS25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hc hδ
  rcases Int.units_eq_one_or (diagChar hp hq e ⟨n, hn⟩) with h1 | h1
  · exact absurd (hI G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e
      n hnS hn hn' h1 (hδ.trans h1)) hc
  · exact hD G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' h1 (hδ.trans h1)

end Proof

end CFSG.ClassicalInvolution.Asc77.C25V
