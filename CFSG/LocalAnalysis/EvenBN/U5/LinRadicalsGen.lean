module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelThreeTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open CFSG.Open (IsElemAbelian)

theorem linrad_normal_of_map {H G : Type*} [Group H] [Group G] {φ : H →* G}
    (hφ : Function.Injective φ) {W V : Subgroup H} (hWV : W ≤ V)
    (h : ((W.map φ).subgroupOf (V.map φ)).Normal) : (W.subgroupOf V).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWV]
  have hWV' : W.map φ ≤ V.map φ := Subgroup.map_mono hWV
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWV'] at h
  intro v hv
  exact (LinearThree.mem_normalizer_map_iff hφ v W).1 (h (Subgroup.mem_map_of_mem φ hv))

theorem radicals_of_map {H G : Type*} [Group H] [Group G] {φ : H →* G}
    (hφ : Function.Injective φ) {V V₁ V₂ : Subgroup H} {q : ℕ}
    (hR : LinearThree.Radicals (V.map φ) (V₁.map φ) (V₂.map φ) q) :
    LinearThree.Radicals V V₁ V₂ q := by
  have hle₁ : V₁ ≤ V := (Subgroup.map_le_map_iff_of_injective hφ).1 hR.le₁
  have hle₂ : V₂ ≤ V := (Subgroup.map_le_map_iff_of_injective hφ).1 hR.le₂
  have hcardmap : ∀ W : Subgroup H, Nat.card (W.map φ) = Nat.card W := fun W =>
    Subgroup.card_map_of_injective hφ
  refine
    { le₁ := hle₁
      le₂ := hle₂
      normal₁ := linrad_normal_of_map hφ hle₁ hR.normal₁
      normal₂ := linrad_normal_of_map hφ hle₂ hR.normal₂
      elem₁ := ?_
      elem₂ := ?_
      card₁ := (hcardmap V₁).symm.trans hR.card₁
      card₂ := (hcardmap V₂).symm.trans hR.card₂
      card := (hcardmap V).symm.trans hR.card
      inf_eq := ?_
      sup_eq := ?_
      card_center := ?_
      le_of_elem := ?_
      eq_of_card := ?_
      le_of_sq := ?_ }
  · have h := LinearThree.isElemAbelian_comap hφ hR.elem₁
    rwa [Subgroup.comap_map_eq_self_of_injective hφ] at h
  · have h := LinearThree.isElemAbelian_comap hφ hR.elem₂
    rwa [Subgroup.comap_map_eq_self_of_injective hφ] at h
  · refine Subgroup.map_injective hφ ?_
    rw [Subgroup.map_inf V₁ V₂ φ hφ, hR.inf_eq, LinearThree.map_inf_centralizer hφ V]
  · refine Subgroup.map_injective hφ ?_
    rw [Subgroup.map_sup V₁ V₂ φ, hR.sup_eq]
  · have h := hcardmap (V ⊓ Subgroup.centralizer (V : Set H))
    rw [LinearThree.map_inf_centralizer hφ V, hR.card_center] at h
    exact h.symm
  · intro E hEV hEl
    rcases hR.le_of_elem (E.map φ) (Subgroup.map_mono hEV)
      (LinearThree.isElemAbelian_map φ hEl) with h | h
    · exact Or.inl ((Subgroup.map_le_map_iff_of_injective hφ).1 h)
    · exact Or.inr ((Subgroup.map_le_map_iff_of_injective hφ).1 h)
  · intro E hEV hEl hc
    have hc' : Nat.card (E.map φ) = q ^ 2 := (hcardmap E).trans hc
    rcases hR.eq_of_card (E.map φ) (Subgroup.map_mono hEV)
      (LinearThree.isElemAbelian_map φ hEl) hc' with h | h
    · exact Or.inl (Subgroup.map_injective hφ h)
    · exact Or.inr (Subgroup.map_injective hφ h)
  · intro x hx hx2
    have hpx : φ x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rcases hR.le_of_sq (φ x) (Subgroup.mem_map_of_mem φ hx) hpx with h | h
    · exact Or.inl ((Subgroup.mem_map_iff_mem hφ).1 h)
    · exact Or.inr ((Subgroup.mem_map_iff_mem hφ).1 h)

theorem radicals_of_surjective_odd_ker {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ]
    {f : ℕ} (hf : 1 ≤ f) (hΛ : CFSG.Blueprint.LieModel Λ .PSL 3 2 (2 * f)) (π : M →* Λ)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {R : Subgroup M}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R ⊤) :
    ∃ R₁ R₂ : Subgroup M, LinearThree.Radicals R R₁ R₂ ((2 ^ f) ^ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcard : Nat.card R = 2 ^ (Nat.card M).factorization 2 := by
    have h := hR.card_eq
    rwa [Subgroup.card_top] at h
  have hK : π.ker ⊓ R = ⊥ := by
    have hKdvd : Nat.card (π.ker ⊓ R : Subgroup M) ∣ 2 ^ (Nat.card M).factorization 2 := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card (π.ker ⊓ R : Subgroup M) := by
        rw [hk]
        exact dvd_pow_self 2 hk0
      exact hker.not_two_dvd_nat (h2.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact Subgroup.card_eq_one.1 (by rw [hk, hk0, pow_zero])
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : (g : M) ∈ π.ker ⊓ R := Subgroup.mem_inf.2 ⟨(MonoidHom.mem_ker).2 hg, g.2⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨φ, hφdef⟩ : ∃ φ : R →* Λ, φ = π.comp R.subtype := ⟨_, rfl⟩
  have hφinj : Function.Injective φ := by
    rw [hφdef]
    exact hinj
  have hRtop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hRmap : R.map π = (⊤ : Subgroup R).map φ := by
    rw [hφdef, ← Subgroup.map_map, hRtop]
  have hcardφ : ∀ W : Subgroup R, Nat.card (W.map φ) = Nat.card W := fun W =>
    Subgroup.card_map_of_injective hφinj
  have hcardRmap : Nat.card (R.map π) = Nat.card R := by
    rw [hRmap, hcardφ, Subgroup.card_top]
  have hMfac : Nat.card M = Nat.card π.ker * Nat.card Λ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, mul_comm]
  have hne₁ : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hne₂ : Nat.card Λ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card M).factorization 2 = (Nat.card Λ).factorization 2 := by
    rw [hMfac, Nat.factorization_mul hne₁ hne₂, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker.not_two_dvd_nat, zero_add]
  have hcardΛ : Nat.card (R.map π) = 2 ^ (Nat.card Λ).factorization 2 := by
    rw [hcardRmap, hRcard, hfac]
  have hA : CFSG.Blueprint.LieModel (↥(⊤ : Subgroup Λ)) .PSL 3 2 (2 * f) :=
    CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv.symm hΛ
  have hV : CFSG.ABGLocalTools.IsSylowOf 2 (R.map π) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [Subgroup.card_top]; exact hcardΛ)
  obtain ⟨W₁, W₂, hW⟩ := exists_radicals_of_lieModel_sq hf hA hV
  have hW' : LinearThree.Radicals ((⊤ : Subgroup R).map φ) W₁ W₂ ((2 ^ f) ^ 2) := by
    rw [← hRmap]
    exact hW
  have e₁ : W₁ = (W₁.comap φ).map φ := LinearThree.eq_map_comap_of_le hW'.le₁
  have e₂ : W₂ = (W₂.comap φ).map φ := LinearThree.eq_map_comap_of_le hW'.le₂
  have hR' : LinearThree.Radicals (⊤ : Subgroup R) (W₁.comap φ) (W₂.comap φ) ((2 ^ f) ^ 2) := by
    apply radicals_of_map hφinj
    rw [← e₁, ← e₂]
    exact hW'
  have hRR := LinearThree.Radicals.map (φ := R.subtype) R.subtype_injective hR'
  rw [hRtop] at hRR
  exact ⟨_, _, hRR⟩

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
