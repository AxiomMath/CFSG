module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bB
public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped IsMulCommutative
open scoped Pointwise

private lemma fzl21b_K6_data (N : Type) [Group N] (φ : N →* MulAut fz21b_X) (N₀ : Subgroup N)
    [N₀.Normal] (e : N ⧸ N₀ ≃* FzSigma4) (ρ lam : N) (hφ : Function.Injective φ)
    (hInv : ∀ n ∈ N₀, n ≠ 1 → ∀ x : fz21b_X, φ n x = x⁻¹) (hρ : orderOf ρ = 3)
    (hlam : orderOf lam = 2) (hrel : lam * ρ * lam⁻¹ = ρ⁻¹)
    (V' : Subgroup N) (hV'card : Nat.card V' = 4)
    (hV'le : V' ≤ fz21b_V.comap (e.toMonoidHom.comp (QuotientGroup.mk' N₀)))
    (hV'disj : V' ⊓ N₀ = ⊥)
    (hρnorm : ρ ∈ Subgroup.normalizer (V' : Set N))
    (hlamnorm : lam ∈ Subgroup.normalizer (V' : Set N)) :
    ∃ K6 : Subgroup N, K6 ≤ Subgroup.normalizer (V' : Set N) ∧
      K6 ⊓ fz21b_V.comap (e.toMonoidHom.comp (QuotientGroup.mk' N₀)) = ⊥ ∧ K6 ⊓ N₀ = ⊥ ∧
      V'.map (e.toMonoidHom.comp (QuotientGroup.mk' N₀)) = fz21b_V ∧
      Nat.card (K6.map (e.toMonoidHom.comp (QuotientGroup.mk' N₀))) = 6 ∧
      fz21b_V ⊓ K6.map (e.toMonoidHom.comp (QuotientGroup.mk' N₀)) = ⊥ := by
  classical
  let π : N →* FzSigma4 := e.toMonoidHom.comp (QuotientGroup.mk' N₀)
  have hπker : π.ker = N₀ := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' N₀)).ker = N₀
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N₀) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N₀)
  obtain ⟨N₁, hN₁normal, hN₁sq, hN₀N₁, hN₁eq, K, hKnormal, hN₀K, hN₁K, hKfix⟩ :=
    fzl21b_stage1_strong N φ N₀ e hφ hInv
  have hN₁mem : ∀ x : N, x ∈ N₁ → π x ∈ fz21b_V := by
    intro x hx
    rw [hN₁eq] at hx
    exact Subgroup.mem_comap.mp hx
  have hcardSigma : Nat.card FzSigma4 = 24 := by rw [Nat.card_eq_fintype_card]; decide
  have hV'leN₁ : V' ≤ N₁ := hN₁eq ▸ hV'le
  have hρ3 : ρ ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hlam2 : lam ^ 2 = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hπρ3 : (π ρ) ^ 3 = 1 := by rw [← map_pow, hρ3, map_one]
  have hπρne : π ρ ≠ 1 := by
    intro h
    have hmem : ρ ∈ N₀ := by rw [← hπker, MonoidHom.mem_ker]; exact h
    have hρ2 : ρ ^ 2 = 1 := by
      have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ
      have hphi : φ ρ = fz21b_invAut fz21b_X := MulEquiv.ext (fun x => hInv ρ hmem hρ1 x)
      have h1 : φ (ρ ^ 2) = 1 := by
        have hsq : fz21b_invAut fz21b_X * fz21b_invAut fz21b_X = 1 := by
          apply MulEquiv.ext
          intro x
          show x⁻¹⁻¹ = x
          exact inv_inv x
        rw [map_pow, hphi]
        change fz21b_invAut fz21b_X * fz21b_invAut fz21b_X = 1
        exact hsq
      exact hφ (by rw [h1, map_one])
    have hdv : orderOf ρ ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact hρ2
    rw [hρ] at hdv
    norm_num at hdv
  have hπlam2 : (π lam) ^ 2 = 1 := by rw [← map_pow, hlam2, map_one]
  have hπrel : π lam * π ρ * (π lam)⁻¹ = (π ρ)⁻¹ := by
    have h := congrArg π hrel
    simpa only [map_mul, map_inv] using h
  let K6 : Subgroup N := Subgroup.zpowers ρ ⊔ Subgroup.zpowers lam
  have hK6normV' : K6 ≤ Subgroup.normalizer (V' : Set N) := by
    rw [show K6 = Subgroup.zpowers ρ ⊔ Subgroup.zpowers lam from rfl, sup_le_iff]
    exact ⟨Subgroup.zpowers_le.mpr hρnorm, Subgroup.zpowers_le.mpr hlamnorm⟩
  have hK6N₁ : K6 ⊓ N₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxK6, hxN₁⟩ := hx
    rw [Subgroup.mem_bot]
    obtain ⟨j, i, hxji⟩ := fz21b_zpowers_sup_fin (N := N) ρ lam hρ hlam hrel x hxK6
    have hword : (π lam) ^ (j : ℕ) * (π ρ) ^ (i : ℕ) ∈ fz21b_V := by
      have h := hN₁mem x hxN₁
      rw [hxji] at h
      simpa only [map_mul, map_pow] using h
    obtain ⟨hi, hj⟩ := fz21b_hword_V (π ρ) (π lam) hπρ3 hπlam2 hπrel hπρne i j hword
    rw [hxji, hi, hj]
    simp
  have hK6N₀ : K6 ⊓ N₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxK6, hxN₀⟩ := hx
    have : x ∈ K6 ⊓ N₁ := Subgroup.mem_inf.mpr ⟨hxK6, hN₀N₁ hxN₀⟩
    rwa [hK6N₁] at this
  have hcardπV' : Nat.card (V'.map π) = 4 := by
    rw [fz21b_card_map_of_disjoint π V' (by rw [hπker]; exact hV'disj), hV'card]
  have hπV' : V'.map π = fz21b_V := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hN₁mem x (hV'leN₁ hx)
    · rw [fz21b_V_card, hcardπV']
  have hπK6card : Nat.card (K6.map π) = 6 := by
    let g : Fin 2 × Fin 3 → K6.map π := fun p =>
      ⟨(π lam) ^ (p.1 : ℕ) * (π ρ) ^ (p.2 : ℕ), by
        refine Subgroup.mem_map.mpr ⟨lam ^ (p.1 : ℕ) * ρ ^ (p.2 : ℕ), ?_, ?_⟩
        · exact K6.mul_mem (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers lam _))
            (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers ρ _))
        · simp only [map_mul, map_pow]⟩
    have hg : Function.Bijective g := by
      constructor
      · rintro ⟨j1, i1⟩ ⟨j2, i2⟩ heq
        have hval : (π lam) ^ (j1 : ℕ) * (π ρ) ^ (i1 : ℕ) =
            (π lam) ^ (j2 : ℕ) * (π ρ) ^ (i2 : ℕ) := by
          have := congrArg (Subtype.val) heq
          simpa [g] using this
        obtain ⟨hi, hj⟩ := fz21b_hword_ne' (π ρ) (π lam) hπρ3 hπlam2 hπrel hπρne i1 j1 i2 j2 hval
        exact Prod.ext hj hi
      · intro y
        obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp y.2
        obtain ⟨j, i, hkji⟩ := fz21b_zpowers_sup_fin (N := N) ρ lam hρ hlam hrel k hk
        refine ⟨(j, i), ?_⟩
        apply Subtype.ext
        have hgv : (g (j, i) : FzSigma4) = (π lam) ^ (j : ℕ) * (π ρ) ^ (i : ℕ) := rfl
        rw [hgv, ← hkπ, hkji]
        simp only [map_mul, map_pow]
    have hcard6 : Nat.card (Fin 2 × Fin 3) = 6 := by
      rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
    rw [← Nat.card_congr (Equiv.ofBijective g hg)]
    exact hcard6
  have hK6disjV : fz21b_V ⊓ K6.map π = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hvV, hvK6⟩ := hv
    rw [Subgroup.mem_bot]
    obtain ⟨k, hkK6, hkπ⟩ := Subgroup.mem_map.mp hvK6
    obtain ⟨j, i, hkji⟩ := fz21b_zpowers_sup_fin (N := N) ρ lam hρ hlam hrel k hkK6
    have hword : (π lam) ^ (j : ℕ) * (π ρ) ^ (i : ℕ) ∈ fz21b_V := by
      have h := hvV
      rw [← hkπ, hkji] at h
      simpa only [map_mul, map_pow] using h
    obtain ⟨hi, hj⟩ := fz21b_hword_V (π ρ) (π lam) hπρ3 hπlam2 hπrel hπρne i j hword
    rw [← hkπ, hkji, hi, hj]
    simp
  refine ⟨K6, hK6normV', ?_, hK6N₀, hπV', hπK6card, hK6disjV⟩
  rw [← hN₁eq]; exact hK6N₁


private theorem fzl_21b_concrete (N : Type) [Group N] (φ : N →* MulAut fz21b_X) (N₀ : Subgroup N)
    [N₀.Normal] (ρ lam : N) (hφ : Function.Injective φ) (hN₀ : Nat.card N₀ = 2)
    (hInv : ∀ n ∈ N₀, n ≠ 1 → ∀ x : fz21b_X, φ n x = x⁻¹)
    (hq : Nonempty (N ⧸ N₀ ≃* FzSigma4)) (hρ : orderOf ρ = 3) (hlam : orderOf lam = 2)
    (hrel : lam * ρ * lam⁻¹ = ρ⁻¹) :
    Nonempty (N ≃* FzZ2xSigma4) := by
  classical
  obtain ⟨e⟩ := hq
  let π : N →* FzSigma4 := e.toMonoidHom.comp (QuotientGroup.mk' N₀)
  have hπker : π.ker = N₀ := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' N₀)).ker = N₀
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N₀) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  obtain ⟨N₁, hN₁normal, hN₁sq, hN₀N₁, hN₁eq, K, hKnormal, hN₀K, hN₁K, hKfix⟩ :=
    fzl21b_stage1_strong N φ N₀ e hφ hInv
  have hN₁mem : ∀ x : N, x ∈ N₁ → π x ∈ fz21b_V := by
    intro x hx
    rw [hN₁eq] at hx
    exact Subgroup.mem_comap.mp hx
  have hcardSigma : Nat.card FzSigma4 = 24 := by rw [Nat.card_eq_fintype_card]; decide
  have hNq : Nat.card (N ⧸ N₀) = 24 := by rw [Nat.card_congr e.toEquiv, hcardSigma]
  have hcardN : Nat.card N = 48 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N₀
    rw [hNq, hN₀] at h
    omega
  haveI : Finite N := Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  have hcenter : N₀ ≤ Subgroup.center N := by
    intro n hn
    by_cases hn1 : n = 1
    · rw [hn1]; exact Subgroup.one_mem _
    rw [Subgroup.mem_center_iff]
    intro g
    have hphin : φ n = fz21b_invAut fz21b_X :=
      MulEquiv.ext (fun x => hInv n hn hn1 x)
    have hcomm : φ n * φ g = φ g * φ n := by
      rw [hphin]
      exact (Subgroup.mem_center_iff.mp (fz21b_invAut_mem_center fz21b_X) (φ g)).symm
    have hconj : φ (g * n) = φ (n * g) := by rw [map_mul, map_mul]; exact hcomm.symm
    exact hφ hconj
  obtain ⟨V', hcardV', hV'le, hV'disj, hρnorm, hlamnorm⟩ :=
    fzl21b_V'_data N φ N₀ e ρ lam hφ hInv hN₀ hρ hlam hrel
  have hV'leN₁ : V' ≤ N₁ := hN₁eq ▸ hV'le
  obtain ⟨K6, hK6normV', hK6N₁', hK6N₀, hπV', hπK6card, hK6disjV⟩ :=
    fzl21b_K6_data N φ N₀ e ρ lam hφ hInv hρ hlam hrel V' hcardV' hV'le hV'disj hρnorm hlamnorm
  have hK6N₁ : K6 ⊓ N₁ = ⊥ := by rw [hN₁eq]; exact hK6N₁'

  let A : Subgroup N := V' ⊔ K6
  have hAinfN₁ : A ⊓ N₁ = V' := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxN₁⟩ := hx
      have hset : (↑A : Set N) = (↑V' : Set N) * (↑K6 : Set N) := by
        change (↑(V' ⊔ K6) : Set N) = (↑V' : Set N) * (↑K6 : Set N)
        exact Subgroup.coe_mul_of_right_le_normalizer_left V' K6 hK6normV'
      have hxA' : x ∈ (↑A : Set N) := hxA
      rw [hset] at hxA'
      obtain ⟨v, hv, k, hk, hvk⟩ := Set.mem_mul.mp hxA'
      have hkN₁ : k ∈ N₁ := by
        have hk_eq : k = v⁻¹ * x := by rw [← hvk]; group
        rw [hk_eq]
        exact N₁.mul_mem (N₁.inv_mem (hV'leN₁ hv)) hxN₁
      have hk1 : k = 1 := by
        have hkm : k ∈ K6 ⊓ N₁ := Subgroup.mem_inf.mpr ⟨hk, hkN₁⟩
        rw [hK6N₁] at hkm
        exact Subgroup.mem_bot.mp hkm
      rw [← hvk, hk1, mul_one]
      exact hv
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(le_sup_left : V' ≤ A) hx, hV'leN₁ hx⟩
  have hAinfN₀ : A ⊓ N₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxN₀⟩ := hx
    have hxN₁ : x ∈ N₁ := hN₀N₁ hxN₀
    have hxV : x ∈ V' := by
      have : x ∈ A ⊓ N₁ := Subgroup.mem_inf.mpr ⟨hxA, hxN₁⟩
      rwa [hAinfN₁] at this
    have : x ∈ V' ⊓ N₀ := Subgroup.mem_inf.mpr ⟨hxV, hxN₀⟩
    rwa [hV'disj] at this
  have hπA : A.map π = ⊤ := by
    have hsup : A.map π = fz21b_V ⊔ K6.map π := by
      rw [show A = V' ⊔ K6 from rfl, Subgroup.map_sup, hπV']
    rw [hsup]
    apply Subgroup.eq_top_of_card_eq
    haveI : fz21b_V.Normal := fz21b_V_normal
    rw [fz21b_card_sup fz21b_V (K6.map π)
      (Subgroup.le_normalizer_of_normal (H := fz21b_V) (K := K6.map π)) hK6disjV,
      fz21b_V_card, hπK6card, hcardSigma]
  let eA : A ≃* FzSigma4 := by
    have hπAker : (π.domRestrict A).ker = ⊥ := by
      rw [MonoidHom.ker_domRestrict, hπker]
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hxm : (x : N) ∈ A ⊓ N₀ := Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [hAinfN₀] at hxm
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxm))
    have hπAinj : Function.Injective (π.domRestrict A) :=
      (MonoidHom.ker_eq_bot_iff (π.domRestrict A)).mp hπAker
    have hπArange : (π.domRestrict A).range = ⊤ := by
      rw [MonoidHom.domRestrict_range, hπA]
    have hπAsurj : Function.Surjective (π.domRestrict A) := by
      rw [← MonoidHom.range_eq_top]; exact hπArange
    exact MulEquiv.ofBijective (π.domRestrict A) ⟨hπAinj, hπAsurj⟩
  have hcomm : ∀ {c p : N}, c ∈ N₀ → p ∈ A → Commute c p := by
    intro c p hc hp
    exact (Subgroup.mem_center_iff.mp (hcenter hc) p).symm
  have hdecomp : ∀ {h : N}, h ∈ (⊤ : Subgroup N) → ∃ c ∈ N₀, ∃ p ∈ A, c * p = h := by
    intro h _
    have hh : π h ∈ A.map π := by rw [hπA]; exact Subgroup.mem_top h
    obtain ⟨p, hp, hpp⟩ := Subgroup.mem_map.mp hh
    refine ⟨h * p⁻¹, ?_, p, hp, ?_⟩
    · rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hpp, mul_inv_cancel]
    · group
  let eN₀ : N₀ ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) hN₀ (by rw [Nat.card_eq_fintype_card]; decide)
  have eN : N ≃* Multiplicative (ZMod 2) × FzSigma4 :=
    Subgroup.topEquiv.symm.trans
      ((Subgroup.mulEquivProdOfInternalDirect N₀ A ⊤ le_top le_top hcomm
        (by rw [inf_comm]; exact hAinfN₀)
        hdecomp).symm.trans (MulEquiv.prodCongr eN₀ eA))
  exact ⟨eN⟩


theorem fzl_21b : Fz21bFix := by
  intro X N _ _ φ N₀ _ ρ lam hX hφ hN₀ hInv hq hρ hlam hrel
  obtain ⟨eX⟩ := hX
  exact fzl_21b_concrete N ((MulAut.congr eX).toMonoidHom.comp φ) N₀ ρ lam
    (fun a b hab => hφ ((MulAut.congr eX).injective hab)) hN₀
    (by
      intro n hn hn1 x
      show eX ((φ n) (eX.symm x)) = x⁻¹
      rw [hInv n hn hn1 (eX.symm x), map_inv, MulEquiv.apply_symm_apply])
    hq hρ hlam hrel

end CFSG.OddStandard.SmallF3.FritzII
