module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups Pointwise

section Generic

theorem le_of_isPGroup_of_normalizes {A : Type*} [Group A] [Finite A] (hA : Nat.card A ∣ 24)
    {H T : Subgroup A} (hT2 : IsPGroup 2 T) (hTH : T ≤ Subgroup.normalizer (H : Set A))
    (h8 : 8 ∣ Nat.card H) : T ≤ H := by
  set B : Subgroup A := H ⊔ T with hB
  have hHB : H ≤ B := le_sup_left
  have hTB : T ≤ B := le_sup_right
  have hN : (H.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHB).mpr
      (sup_le Subgroup.le_normalizer hTH)
  let φ : T →* B ⧸ H.subgroupOf B :=
    (QuotientGroup.mk' (H.subgroupOf B)).comp (Subgroup.inclusion hTB)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hb' : b ∈ ((T ⊔ H : Subgroup A) : Set A) := by rw [sup_comm]; exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T H hTH] at hb'
    obtain ⟨t, ht, h, hh, rfl⟩ := Set.mem_mul.mp hb'
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    have : (t : A)⁻¹ * (t * h) = h := by group
    rw [this]
    exact hh
  have hdvd : Nat.card (B ⧸ H.subgroupOf B) ∣ Nat.card T := Subgroup.card_dvd_of_surjective hφ
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  rw [hm] at hdvd
  have hdvd2 : Nat.card (B ⧸ H.subgroupOf B) ∣ 2 ^ m := hdvd
  have hBcard : Nat.card B = Nat.card (H.subgroupOf B) * Nat.card (B ⧸ H.subgroupOf B) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf B)).trans (mul_comm _ _)
  have hHcard : Nat.card (H.subgroupOf B) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv
  have hBdvd : Nat.card B ∣ 24 := (Subgroup.card_subgroup_dvd_card B).trans hA
  rw [hBcard, hHcard] at hBdvd
  obtain ⟨c, hc⟩ := h8
  rw [hc] at hBdvd
  have h3 : Nat.card (B ⧸ H.subgroupOf B) ∣ 3 := by
    have : 8 * (c * Nat.card (B ⧸ H.subgroupOf B)) ∣ 8 * 3 := by
      calc 8 * (c * Nat.card (B ⧸ H.subgroupOf B)) = 8 * c * Nat.card (B ⧸ H.subgroupOf B) := by
            ring
        _ ∣ 24 := hBdvd
        _ = 8 * 3 := by norm_num
    have h' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    exact (Dvd.intro_left c rfl).trans h'
  have hone : Nat.card (B ⧸ H.subgroupOf B) = 1 := by
    have h2 : Nat.card (B ⧸ H.subgroupOf B) ∣ Nat.gcd 3 (2 ^ m) := Nat.dvd_gcd h3 hdvd2
    have : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
    rw [this] at h2
    exact Nat.dvd_one.mp h2
  have hidx : (H.subgroupOf B).index = 1 := by
    rw [Subgroup.index, hone]
  have : B ≤ H := Subgroup.relIndex_eq_one.mp (show H.relIndex B = 1 from hidx)
  exact hTB.trans this

end Generic

section Action

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))

omit [Finite G] in
theorem le_sup_cStar_of_eight_dvd {X S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (K : Set G)) (hS2 : IsPGroup 2 S)
    (hSX : S ≤ Subgroup.normalizer (X : Set G))
    (h8 : 8 ∣ Nat.card ((X.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (normalizerToAutSL3 e))) : S ≤ X ⊔ centralizerModOdd ⊤ K := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToAutSL3 e with hΨ
  set H := (X.subgroupOf N).map Ψ with hH
  set T := (S.subgroupOf N).map Ψ with hT
  have hT2 : IsPGroup 2 T := hS2.comap_subtype.map Ψ
  have key : ∀ σ ∈ T, ∀ h ∈ H, σ * h * σ⁻¹ ∈ H := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨s * x * s⁻¹, ?_, by simp⟩
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hSX hs') _).mp hx')
  have hTH : T ≤ Subgroup.normalizer (H : Set (MulAut SL(2, ZMod 3))) := fun σ hσ =>
    Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => key σ hσ h hh, fun hh => by
      have := key σ⁻¹ (T.inv_mem hσ) _ hh
      simpa [mul_assoc] using this⟩
  have hTleH : T ≤ H :=
    le_of_isPGroup_of_normalizes (by rw [sl2Three_card_mulAut]) hT2 hTH h8
  intro s hs
  obtain ⟨x, hx, hxs⟩ := hTleH (Subgroup.mem_map_of_mem Ψ
    (Subgroup.mem_subgroupOf.mpr hs : (⟨s, hSN hs⟩ : N) ∈ S.subgroupOf N))
  have h1 : Ψ (x⁻¹ * ⟨s, hSN hs⟩) = 1 := by
    rw [map_mul, map_inv, hxs, inv_mul_cancel]
  have e1 : s = (x : G) * ((x⁻¹ * ⟨s, hSN hs⟩ : N) : G) := by simp
  rw [e1]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx)
    ((normalizerToAutSL3_eq_one_iff_mem_centralizerModOdd e _).mp h1)

end Action

section Counting

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem natCard_sylow_eq_eight (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {R : Subgroup G} (hR : IsSylow2In R K) : Nat.card R = 8 := by
  have hK : Nat.card K = 24 * Nat.card (classicalInvolutionOddCore K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore K),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hodd : Odd (Nat.card (classicalInvolutionOddCore K)) :=
    CFSG.ComponentClassification.OddCore.odd_card K
  have h2 : ¬ 2 ∣ Nat.card (classicalInvolutionOddCore K) := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [natCard_eq_pow_of_isSylow2In hR, hK,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2]
  have : (24 : ℕ).factorization 2 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
    simp
  rw [this]
  norm_num

theorem eight_dvd_card_map_of_sylow_outer (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {X V R : Subgroup G} (hR : IsSylow2In R K) (hRX : R ≤ X)
    (hV : ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3)
    (hVX : V ≤ X) :
    8 ∣ Nat.card ((X.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e)) := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToAutSL3 e with hΨ
  set H := (X.subgroupOf N).map Ψ with hH
  have hRK : R ≤ K := hR.1
  have hRN : R ≤ N := hRK.trans Subgroup.le_normalizer
  let ρ : ↥R →* MulAut SL(2, ZMod 3) := Ψ.comp (Subgroup.inclusion hRN)
  have hρ : ∀ r : R, ρ r = MulAut.conj (e (QuotientGroup.mk ⟨(r : G), hRK r.2⟩)) := fun r =>
    normalizerToAutSL3_of_mem e (hRK r.2)
  have hrange : ρ.range ≤ H ⊓ inn3 := by
    rintro _ ⟨r, rfl⟩
    refine ⟨⟨⟨r, hRN r.2⟩, Subgroup.mem_subgroupOf.mpr (hRX r.2), rfl⟩, ?_⟩
    rw [hρ]
    exact conj_mem_inn3 _
  have hinj : ∀ a b : R, e (QuotientGroup.mk ⟨(a : G), hRK a.2⟩) =
      e (QuotientGroup.mk ⟨(b : G), hRK b.2⟩) → a = b := by
    intro a b hab
    have h1 : (QuotientGroup.mk ⟨(a : G), hRK a.2⟩ : K ⧸ classicalInvolutionOddCore K) =
        QuotientGroup.mk ⟨(b : G), hRK b.2⟩ := e.injective hab
    rw [QuotientGroup.eq] at h1
    have hmem : ((a : G)⁻¹ * (b : G)) ∈ oddCoreOf K := ⟨_, h1, rfl⟩
    have hxR : (a : G)⁻¹ * (b : G) ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    have h2 : (a : G)⁻¹ * (b : G) = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
        (hR.2.1.to_le (Subgroup.zpowers_le.mpr hxR))
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have hker : Nat.card ρ.ker ≤ 2 := by
    let f : ρ.ker → Subgroup.center SL(2, ZMod 3) := fun r => ⟨e (QuotientGroup.mk
      ⟨((r : R) : G), hRK (r : R).2⟩), by
        have h1 : ρ (r : R) = 1 := r.2
        rw [hρ] at h1
        exact Aut.ker_conj_sl2Three ▸ h1⟩
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (hinj _ _ (congrArg Subtype.val hab))
    calc Nat.card ρ.ker ≤ Nat.card (Subgroup.center SL(2, ZMod 3)) :=
          Nat.card_le_card_of_injective f hf
      _ = 2 := Aut.natCard_center_sl2Three
  have hR8 : Nat.card R = 8 := natCard_sylow_eq_eight e hR
  have hmul := Subgroup.card_ker_mul_card_range ρ
  rw [hR8] at hmul
  have hker1 : 0 < Nat.card ρ.ker := Nat.card_pos
  have hrange4 : 4 ≤ Nat.card ρ.range := by
    interval_cases h : Nat.card ρ.ker <;> omega
  have hr2 : IsPGroup 2 ρ.range := hR.2.1.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨m, hm⟩ := hr2.exists_card_eq
  have h4 : 4 ∣ Nat.card ρ.range := by
    rw [hm] at hrange4 ⊢
    have : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m <;> omega
    exact (pow_dvd_pow 2 this)
  have h4' : 4 ∣ Nat.card ↥(H ⊓ inn3) := h4.trans (Subgroup.card_dvd_of_le hrange)
  have hVH : (V.subgroupOf N).map Ψ ≤ H := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hVX (Subgroup.mem_subgroupOf.mp hx))
  have hHnot : ¬ H ≤ inn3 := fun h => hV (hVH.trans h)
  have hidx2 : inn3.relIndex H = 2 := by
    have hd : inn3.relIndex H ∣ 2 := by
      have := Subgroup.relIndex_dvd_index_of_normal (H := inn3) (K := H)
      rwa [inn3_index] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hHnot
    · exact h
  have hcard := Subgroup.relIndex_mul_card (H := inn3) (K := H)
  rw [hidx2, inf_comm] at hcard
  rw [← hcard]
  obtain ⟨c, hc⟩ := h4'
  exact ⟨c, by rw [hc]; ring⟩

theorem le_sup_cStar_of_sylow_outer (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {X S V R : Subgroup G} (hR : IsSylow2In R K) (hRX : R ≤ X)
    (hV : ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3)
    (hVX : V ≤ X) (hSN : S ≤ Subgroup.normalizer (K : Set G)) (hS2 : IsPGroup 2 S)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) : S ≤ X ⊔ centralizerModOdd ⊤ K :=
  le_sup_cStar_of_eight_dvd e hSN hS2 hSX (eight_dvd_card_map_of_sylow_outer e hR hRX hV hVX)

theorem false_of_not_mem_sup_cStar (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {X S V R : Subgroup G} (hR : IsSylow2In R K) (hRX : R ≤ X)
    (hV : ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3)
    (hVX : V ≤ X) (hSN : S ≤ Subgroup.normalizer (K : Set G)) (hS2 : IsPGroup 2 S)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) {a : G} (haS : a ∈ S)
    (ha : a ∉ X ⊔ centralizerModOdd ⊤ K) : False :=
  ha (le_sup_cStar_of_sylow_outer e hR hRX hV hVX hSN hS2 hSX haS)

end Counting

end CFSG.ClassicalInvolution.Q3.Q3T6
