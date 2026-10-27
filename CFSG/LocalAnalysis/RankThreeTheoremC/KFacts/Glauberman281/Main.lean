module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

theorem three_dvd_card_of_actsAsNaturalL2 {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (h : ActsAsNaturalL2 L U) : 3 ∣ Nat.card L := by
  obtain ⟨e, -, -⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [this]
  norm_num

theorem glaubermanFactorization_holds :
    ∀ (G : Type) [Group G] [Finite G] (H Y : Subgroup G), Group.IsSolvable ↥H → ¬ 3 ∣ Nat.card H →
      CharTwo H → IsSylowTwoOf Y H → ∀ h ∈ H,
        ∃ n ∈ H ⊓ normalizer (thompsonJ Y : Set G),
          ∃ c ∈ H ⊓ centralizer (quasithinOmegaOneCenter Y : Set G), h = n * c := by
  intro G _ _ H Y hsolv h3 hF hY h hh
  obtain ⟨hU, -, hcase, -⟩ := B2_16 (G := G) (H := H) (T := Y)
    (V := conjClosure (quasithinOmegaOneCenter Y) H) hsolv hF hY rfl
  rcases hcase with ⟨-, hfac⟩ | ⟨hJ, I, hSyl, hEq, -, -, hNat, -⟩
  · exact hfac h hh
  · exfalso
    set V : Subgroup G := conjClosure (quasithinOmegaOneCenter Y) H with hV
    have hHN : H ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
    have hYH : Y ≤ H := hY.1
    have hJY : thompsonJ Y ≤ Y := iSup₂_le fun _ hA => hA.1
    have hJH : thompsonJ H ≤ H := iSup₂_le fun _ hA => hA.1
    have hJYN : thompsonJ Y ≤ Subgroup.normalizer (V : Set G) := hJY.trans (hYH.trans hHN)
    have hJHN : thompsonJ H ≤ Subgroup.normalizer (V : Set G) := hJH.trans hHN
    have hI : I.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      have hbot : autI hU (thompsonJ H) = ⊥ := by simpa using hEq
      have hle : autI hU (thompsonJ Y) ≤ ⊥ :=
        hbot ▸ autI_mono hU (thompsonJ_le_thompsonJ_of_isSylowTwoOf hY)
      exact hJ ((autI_eq_bot_iff hU hJYN).1 (le_bot_iff.1 hle))
    obtain ⟨L, hL⟩ := hI
    have h3L : 3 ∣ Nat.card L := three_dvd_card_of_actsAsNaturalL2 (hNat L hL)
    have hLle : L ≤ autI hU (thompsonJ H) := hEq ▸ le_iSup₂ (f := fun L' _ => L') L hL
    have h3a : 3 ∣ Nat.card (autI hU (thompsonJ H)) :=
      h3L.trans (Subgroup.card_dvd_of_le hLle)
    have hcard := card_autI_mul_card_inf hU hJHN
    have h3J : 3 ∣ Nat.card (thompsonJ H) := hcard ▸ h3a.mul_right _
    exact h3 (h3J.trans (Subgroup.card_dvd_of_le hJH))

theorem card_eq_two_pow_mul_pow {n p : ℕ} (hn : n ≠ 0) (hp : p ≠ 2)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = p) :
    n = 2 ^ n.factorization 2 * p ^ n.factorization p := by
  have hsub : n.factorization.support ⊆ {2, p} := by
    intro r hr
    rw [Nat.support_factorization] at hr
    have hr' := Nat.prime_of_mem_primeFactors hr
    rcases h r hr' (Nat.dvd_of_mem_primeFactors hr) with rfl | rfl <;> simp
  have h1 := Nat.factorization_prod_pow_eq_self hn
  rw [Finsupp.prod_of_support_subset _ hsub _ (fun r _ => pow_zero r)] at h1
  rw [Finset.prod_pair (Ne.symm hp)] at h1
  exact h1.symm

theorem glaubermanTwoP_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ H Y : Subgroup G,
      (∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p) → CharTwo H → IsSylowTwoOf Y H →
      ∀ h ∈ H, ∃ a ∈ H ⊓ normalizer (thompsonJ Y : Set G),
        ∃ b ∈ H ⊓ normalizer (quasithinOmegaOneCenter Y : Set G), h = a * b := by
  intro G _ _ p hp h5 H Y hpr hF hY h hh
  have hp2 : p ≠ 2 := by omega
  have hcard := card_eq_two_pow_mul_pow (Nat.card_pos (α := H)).ne' hp2 hpr
  have hsolv : Group.IsSolvable ↥H := by
    haveI : Fintype H := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two hp
      (Ne.symm hp2) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have h3 : ¬ 3 ∣ Nat.card H := fun hd => by
    rcases hpr 3 Nat.prime_three hd with h' | h' <;> omega
  obtain ⟨n, hn, c, hc, hnc⟩ := glaubermanFactorization_holds G H Y hsolv h3 hF hY h hh
  exact ⟨n, hn, c, ⟨hc.1, Subgroup.centralizer_le_normalizer _ hc.2⟩, hnc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281
