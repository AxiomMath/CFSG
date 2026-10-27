module

public import CFSG.ClassicalInvolution.Asc77.AscC25V30
public import CFSG.ClassicalInvolution.Asc77.AscC25V35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type} [Group G]

@[expose] def swapDiff {N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hconj : ∀ n ∈ N, t * n * t ∈ N) {Γ : Type*} [CommGroup Γ] (φ : N →* Γ) : N →* Γ :=
  MonoidHom.mk' (fun n => φ n * (φ ⟨t * n * t, hconj n n.2⟩)⁻¹) (by
    intro n m
    have e2 : (⟨t * ((n * m : N) : G) * t, hconj _ (n * m).2⟩ : N) =
        ⟨t * n * t, hconj n n.2⟩ * ⟨t * m * t, hconj m m.2⟩ := by
      apply Subtype.ext
      show t * ((n : G) * m) * t = (t * n * t) * (t * m * t)
      calc t * ((n : G) * m) * t = t * n * (t * t) * m * t := by rw [ht2]; group
        _ = (t * n * t) * (t * m * t) := by group
    rw [map_mul, e2, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

variable {N : Subgroup G} {t : G} (ht2 : t * t = 1) (hconj : ∀ n ∈ N, t * n * t ∈ N)
  {Γ : Type*} [CommGroup Γ] (φ : N →* Γ)

include ht2 in
theorem swapDiff_apply (n : G) (hn : n ∈ N) :
    swapDiff ht2 hconj φ ⟨n, hn⟩ = φ ⟨n, hn⟩ * (φ ⟨t * n * t, hconj n hn⟩)⁻¹ := rfl

include ht2 in
theorem swapDiff_swap (n : G) (hn : n ∈ N) :
    swapDiff ht2 hconj φ ⟨t * n * t, hconj n hn⟩ = (swapDiff ht2 hconj φ ⟨n, hn⟩)⁻¹ := by
  have e3 : (⟨t * (t * n * t) * t, hconj _ (hconj n hn)⟩ : N) = ⟨n, hn⟩ := by
    apply Subtype.ext
    show t * (t * n * t) * t = n
    calc t * (t * n * t) * t = (t * t) * n * (t * t) := by group
      _ = n := by rw [ht2]; group
  rw [swapDiff_apply ht2 hconj φ _ (hconj n hn), e3, swapDiff_apply ht2 hconj φ n hn, mul_inv,
    inv_inv, mul_comm]

theorem exists_swapDiff_eq_of_hT {C : Subgroup G} (hNC : N ≤ C)
    (hcov : ∀ c ∈ C, c ∈ N ∨ c * t ∈ N) {Γ : Type} [CommGroup Γ] (χ : N →* Γ) (δ : N →* ℤˣ)
    {a : G} (haN : a ∈ N)
    (hT : ∀ (B : Type) [CommGroup B] (π : ↥C →* B), π ⟨a, hNC haN⟩ = 1) :
    ∃ n : N, swapDiff ht2 hconj δ n = δ ⟨a, haN⟩ ∧ swapDiff ht2 hconj χ n = χ ⟨a, haN⟩ := by
  classical
  let ε : N →* ℤˣ × Γ := (swapDiff ht2 hconj δ).prod (swapDiff ht2 hconj χ)
  let E : Subgroup (ℤˣ × Γ) := ε.range
  have : E.Normal := Subgroup.normal_of_isMulCommutative E
  let ϕ₀ : N →* ((ℤˣ × Γ) ⧸ E) := (QuotientGroup.mk' E).comp (δ.prod χ)
  have hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t * n * t, hconj n hn⟩ = ϕ₀ ⟨n, hn⟩ := by
    intro n hn
    change (QuotientGroup.mk (δ ⟨t * n * t, hconj n hn⟩, χ ⟨t * n * t, hconj n hn⟩) :
      (ℤˣ × Γ) ⧸ E) = QuotientGroup.mk (δ ⟨n, hn⟩, χ ⟨n, hn⟩)
    rw [QuotientGroup.eq]
    refine ⟨⟨n, hn⟩, ?_⟩
    change (swapDiff ht2 hconj δ ⟨n, hn⟩, swapDiff ht2 hconj χ ⟨n, hn⟩) = _
    rw [swapDiff_apply ht2 hconj δ n hn, swapDiff_apply ht2 hconj χ n hn]
    ext
    · simp [mul_comm]
    · simp [mul_comm]
  obtain ⟨ϕ, hϕ⟩ := exists_hom_extension_of_index_two C N hNC t ht2 hcov hconj ϕ₀ hinv
  have h1 := hT ((ℤˣ × Γ) ⧸ E) ϕ
  rw [hϕ a haN] at h1
  change (QuotientGroup.mk (δ ⟨a, haN⟩, χ ⟨a, haN⟩) : (ℤˣ × Γ) ⧸ E) = 1 at h1
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  exact ⟨n, congrArg Prod.fst hn, congrArg Prod.snd hn⟩

include ht2 in
theorem swapDiff_conj_mem {Λ : Type*} [CommGroup Λ] (φ : N →* Λ) (c n : N) :
    swapDiff ht2 hconj φ (c * n * c⁻¹) = swapDiff ht2 hconj φ n := by
  rw [map_mul, map_mul, map_inv, mul_comm (swapDiff ht2 hconj φ c) _, mul_assoc, mul_inv_cancel,
    mul_one]

theorem odd_orderOf_swapDiff_of_corr [Finite G] {C : Subgroup G} (S : Sylow 2 G)
    (hSC : (S : Subgroup G) ≤ C) (hNC : N ≤ C) (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hcov : ∀ c ∈ C, c ∈ N ∨ c * t ∈ N) {Γ : Type*} [CommGroup Γ] (χ : N →* Γ) {Λ : Type*}
    [CommGroup Λ] (δ : N →* Λ)
    (hcorr : ∀ (m : G) (hm : m ∈ N), m ∈ (S : Subgroup G) →
      swapDiff ht2 hconj δ ⟨m, hm⟩ = 1 → swapDiff ht2 hconj χ ⟨m, hm⟩ = 1)
    (n : G) (hn : n ∈ N) (hnδ : swapDiff ht2 hconj δ ⟨n, hn⟩ = 1) :
    Odd (orderOf (swapDiff ht2 hconj χ ⟨n, hn⟩)) := by
  classical
  have hA : ∀ (x : N) (i : ℕ), orderOf (x : G) = 2 ^ i → swapDiff ht2 hconj δ x = 1 →
      swapDiff ht2 hconj χ x = 1 := by
    intro x i hx hxδ
    obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_sylow S hSC (hNC x.2) hx
    have hmN : c * (x : G) * c⁻¹ ∈ N := hnorm c hcC x x.2
    rcases hcov c hcC with hcN | hct
    · have e : (⟨c * (x : G) * c⁻¹, hmN⟩ : N) = ⟨c, hcN⟩ * x * ⟨c, hcN⟩⁻¹ := rfl
      have h1 := hcorr _ hmN hcS (by rw [e, swapDiff_conj_mem ht2 hconj δ]; exact hxδ)
      rwa [e, swapDiff_conj_mem ht2 hconj χ] at h1
    · have hc0 : c * t ∈ N := hct
      have e : (⟨c * (x : G) * c⁻¹, hmN⟩ : N) =
          ⟨c * t, hc0⟩ * ⟨t * (x : G) * t, hconj x x.2⟩ * ⟨c * t, hc0⟩⁻¹ := by
        apply Subtype.ext
        show c * (x : G) * c⁻¹ = (c * t) * (t * (x : G) * t) * (c * t)⁻¹
        have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
        rw [mul_inv_rev, hti]
        calc c * (x : G) * c⁻¹ = c * (t * t) * (x : G) * (t * t) * c⁻¹ := by rw [ht2]; group
          _ = (c * t) * (t * (x : G) * t) * (t * c⁻¹) := by group
      have hxs : swapDiff ht2 hconj δ ⟨t * (x : G) * t, hconj x x.2⟩ = 1 := by
        rw [swapDiff_swap ht2 hconj δ x x.2]
        have : swapDiff ht2 hconj δ x = 1 := hxδ
        simp [this]
      have h1 := hcorr _ hmN hcS (by rw [e, swapDiff_conj_mem ht2 hconj δ]; exact hxs)
      rw [e, swapDiff_conj_mem ht2 hconj χ, swapDiff_swap ht2 hconj χ x x.2] at h1
      exact inv_eq_one.mp h1
  have hord0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  have hno : orderOf (n ^ o) = 2 ^ k := by
    have h1 : o ∣ orderOf n := ⟨2 ^ k, by rw [hko, mul_comm]⟩
    rw [orderOf_pow_of_dvd ho.pos.ne' h1, hko, Nat.mul_div_cancel _ ho.pos]
  let nN : N := ⟨n, hn⟩
  have h2 : swapDiff ht2 hconj χ (nN ^ o) = 1 := by
    apply hA (nN ^ o) k
    · rw [Subgroup.coe_pow]
      exact hno
    · rw [map_pow]
      have : swapDiff ht2 hconj δ nN = 1 := hnδ
      rw [this, one_pow]
  rw [map_pow] at h2
  have h3 : orderOf (swapDiff ht2 hconj χ nN) ∣ o := orderOf_dvd_of_pow_eq_one h2
  exact Odd.of_dvd_nat ho h3

theorem false_of_corr_of_hT [Finite G] {C : Subgroup G} (S : Sylow 2 G)
    (hSC : (S : Subgroup G) ≤ C) (hNC : N ≤ C) (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hcov : ∀ c ∈ C, c ∈ N ∨ c * t ∈ N) {Γ : Type} [CommGroup Γ] (χ : N →* Γ) (δ : N →* ℤˣ)
    (hcorr : ∀ (m : G) (hm : m ∈ N), m ∈ (S : Subgroup G) →
      swapDiff ht2 hconj δ ⟨m, hm⟩ = 1 → swapDiff ht2 hconj χ ⟨m, hm⟩ = 1)
    {a : G} (haN : a ∈ N) (hδa : δ ⟨a, haN⟩ = 1) (hχa : orderOf (χ ⟨a, haN⟩) = 2)
    (hT : ∀ (B : Type) [CommGroup B] (π : ↥C →* B), π ⟨a, hNC haN⟩ = 1) : False := by
  obtain ⟨n, hn1, hn2⟩ := exists_swapDiff_eq_of_hT ht2 hconj hNC hcov χ δ haN hT
  have hodd := odd_orderOf_swapDiff_of_corr ht2 hconj S hSC hNC hnorm hcov χ δ hcorr n n.2
    (by rw [hn1, hδa])
  have hn2' : swapDiff ht2 hconj χ ⟨n, n.2⟩ = χ ⟨a, haN⟩ := hn2
  rw [hn2', hχa] at hodd
  exact absurd hodd (by decide)

end Abstract

section Main

variable (p f : ℕ) [Fact p.Prime]


@[expose] def RES25 : Prop :=
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
              diagChar hp hq e ⟨t' * n * t', hn'⟩ = diagChar hp hq e ⟨n, hn⟩ →
                fieldChar hp hq e ⟨t' * n * t', hn'⟩ = fieldChar hp hq e ⟨n, hn⟩

@[expose] def ResAt25 (ε : ℤˣ) : Prop :=
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
              diagChar hp hq e ⟨n, hn⟩ = ε → diagChar hp hq e ⟨t' * n * t', hn'⟩ = ε →
                fieldChar hp hq e ⟨t' * n * t', hn'⟩ = fieldChar hp hq e ⟨n, hn⟩

@[expose] def GCS25Z : Prop := ResAt25 p f 1

@[expose] def DIAG25 : Prop := ResAt25 p f (-1)

end Main

section Proof

variable {p f : ℕ} [Fact p.Prime]


theorem false_of_ff_res (h11 : C25_11 p f) (hres : RES25 p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ : G} (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hFa' : IsFAut R' a) :
    False := by
  classical
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
  · exact false_of_zStar_ff h11 hyp haS ha2 hFa hFa' hZ
  obtain ⟨t', g, h, hg, hnf, hat⟩ := exists_comm_swap_of_ff h11 hyp haS ha2 hFa hFa'
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  have hfix := fix_of_isFAut h haS hFa'
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hσ : fieldChar hp hq e ⟨a, haK⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2 haK
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (hyp.hzS s hs)
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN
  have hconjN : ∀ m ∈ N, t' * m * t' ∈ N := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    have hmK' : conjSub m K' = K' := (cz_fix_iff h hmz).mp hmK
    have hK2 : conjSub (t' * m * t') K = K := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hmK', conjSub_t'_K' h]
    exact ⟨C.mul_mem (C.mul_mem ht'C hm.1) ht'C, mem_normalizer_iff_conjSub_eq.mpr hK2⟩
  have hnormN : ∀ c ∈ C, ∀ m ∈ N, c * m * c⁻¹ ∈ N := by
    intro c hc m hm
    have hcz : c * z = z * c := (hmemC c).mp hc
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    have hcmK : conjSub (c * m * c⁻¹) K = K :=
      (twinCtx_of_hyp25 h).conj_normalizer hcz hmz hmK
    exact ⟨C.mul_mem (C.mul_mem hc hm.1) (C.inv_mem hc), mem_normalizer_iff_conjSub_eq.mpr hcmK⟩
  have hcov : ∀ c ∈ C, c ∈ N ∨ c * t' ∈ N := by
    intro c hc
    have hcz : c * z = z * c := (hmemC c).mp hc
    rcases cz_cover h hcz with h1 | h1
    · exact Or.inl ⟨hc, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hc ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    (fieldChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  let δ : N →* ℤˣ := (diagChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  have haz : a * z = z * a := hyp.hzS a haS
  have haC : a ∈ C := (hmemC a).mpr haz
  have haN : a ∈ N := ⟨haC, haK⟩
  have hδa : δ ⟨a, haN⟩ = 1 := diagChar_eq_one_of_involution hp hq e haK ha2 hσ
  have hχa : orderOf (χ ⟨a, haN⟩) = 2 := by
    have hsq : χ ⟨a, haN⟩ ^ 2 = 1 := by
      have h3 : (⟨a, haN⟩ : N) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact ha2)
      rw [← map_pow, h3, map_one]
    exact orderOf_eq_prime hsq hσ
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hFa'
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := comm_z_of_mem h.hzR' hyR'
  have hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y)
      (by rw [conjSub_one]; exact h.hyp.hR'.2.1 hyR') hy4 hg
    simpa using this
  refine false_of_corr_of_hT h.ht'2 hconjN S hSC inf_le_left hnormN hcov χ δ ?_ haN hδa hχa ?_
  · intro m hm hmS hδm
    have hδ' : δ ⟨t' * m * t', hconjN m hm⟩ = δ ⟨m, hm⟩ := by
      rw [swapDiff_apply h.ht'2 hconjN δ m hm] at hδm
      exact (mul_inv_eq_one.mp hδm).symm
    have hχ' := hres G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h ⟨g, hg⟩ hnf hat
      hp hq e m hmS hm.2 (hconjN m hm).2 hδ'
    rw [swapDiff_apply h.ht'2 hconjN χ m hm]
    exact mul_inv_eq_one.mpr hχ'.symm
  · intro B _ π
    exact hom_centralizer_apply_eq_one (exists_noncomm_of_swap h) ha2 haz hya hyz hy4' hnc4 π

theorem c25_16inv_of_res (h11 : C25_11 p f) (hmix : Mix25 p f) (hres : RES25 p f) :
    T7U.C25_16inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  rcases hmix G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' with hin | ⟨r, hrR, ha'2, hFa'⟩
  · obtain ⟨e, heS, he2, hFe, hFe'⟩ := exists_ff_of_inner h11 hyp haS ha2 hF' hin
    exact (false_of_ff_res h11 hres hyp heS he2 hFe hFe').elim
  · obtain ⟨t₀, h₀⟩ := T7T.exists_hyp25T hyp
    have ha'S : a * r ∈ (S : Subgroup G) := S.mul_mem haS (h₀.hRS hrR)
    have hF'a' : IsFAut R' (a * r) :=
      T7U.isFAut_mul_of_centralizes (fun x hx => h₀.hcomm r hrR x hx) hF'
    exact (false_of_ff_res h11 hres hyp ha'S ha'2 hFa' hF'a').elim

theorem c25_16invEven_of_res (h11 : C25_11 p f) (hmix : Mix25 p f) (hres : RES25 p f) :
    Even f → T7U.C25_16inv p f :=
  fun _ => c25_16inv_of_res h11 hmix hres

theorem res25_of_parts (h0 : GCS25Z p f) (hd : DIAG25 p f) : RES25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hδ
  rcases Int.units_eq_one_or (diagChar hp hq e ⟨n, hn⟩) with h1 | h1
  · exact h0 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' h1 (hδ.trans h1)
  · exact hd G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' h1 (hδ.trans h1)

theorem res25_of_gcs25 (hgcs : GCS25 p f) : RES25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' _
  exact hgcs G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn'

theorem c25_16inv_of_zero_diag (h11 : C25_11 p f) (hmix : Mix25 p f) (h0 : GCS25Z p f)
    (hd : DIAG25 p f) : T7U.C25_16inv p f :=
  c25_16inv_of_res h11 hmix (res25_of_parts h0 hd)

end Proof

end CFSG.ClassicalInvolution.Asc77.C25V
