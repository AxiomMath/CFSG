module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarChain

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter

section Pair

variable {N : ℕ}

theorem swap_conj_eq (c : Perm (Fin N)) (p q : Fin N) :
    c * swap p q * c⁻¹ = swap (c p) (c q) := by
  rw [mul_swap_eq_swap_mul, mul_assoc, mul_inv_cancel, mul_one]

theorem swap_comm_of_apply {π : Perm (Fin N)} (h2 : π * π = 1) {p : Fin N} :
    swap p (π p) * π = π * swap p (π p) := by
  rw [mul_swap_eq_swap_mul π, apply_apply_of_mul_self h2, swap_comm]

theorem mem_of_mul_swap_apply_ne {p q r s x : Fin N} (h : (swap p q * swap r s) x ≠ x) :
    x = p ∨ x = q ∨ x = r ∨ x = s := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcon.2.2.1 hcon.2.2.2,
    swap_apply_of_ne_of_ne hcon.1 hcon.2.1]

theorem exists_swap_pair (hN : 7 ≤ N) {π : Perm (Fin N)} (h2 : π * π = 1) (h1 : π ≠ 1)
    (hns : ¬ π.IsSwap) :
    ∃ e e' : Perm (Fin N), e.IsSwap ∧ e'.IsSwap ∧ e * π = π * e ∧ e' * π = π * e' ∧ e ≠ e' ∧
      e * e' = e' * e ∧ e * e' ≠ π ∧
      ∀ c : Perm (Fin N), c * π = π * c → c * (e * e') = (e * e') * c →
        c * e * c⁻¹ = e ∨ c * e * c⁻¹ = e' := by
  classical
  have hπ := apply_apply_of_mul_self h2
  have hs := card_support_eq_two_mul_card_cycleType h2
  have hpos : 0 < π.support.card := by
    rw [Finset.card_pos, Finset.nonempty_iff_ne_empty, Ne, support_eq_empty_iff]
    exact h1
  have hne2 : π.support.card ≠ 2 := fun h => hns (card_support_eq_two.1 h)
  obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
  rw [mem_support] at hp
  set q := π p with hq
  have hpq : p ≠ q := fun h => hp h.symm
  have hπq : π q = p := hπ p
  have hcommute : ∀ c : Perm (Fin N), c * π = π * c → ∀ x, π (c x) = c (π x) := by
    intro c hc x
    have := DFunLike.congr_fun hc x
    simpa using this.symm
  by_cases h6 : 6 ≤ π.support.card
  ·
    obtain ⟨r, hr, hr'⟩ : ∃ r ∈ π.support, r ≠ p ∧ r ≠ q := by
      by_contra hcon
      push Not at hcon
      have : π.support ⊆ {p, q} := fun r hr => by
        rcases eq_or_ne r p with h | h
        · simp [h]
        · simp [hcon r hr h]
      have := (Finset.card_le_card this).trans (Finset.card_le_two)
      omega
    rw [mem_support] at hr
    set s := π r with hsdef
    have hrs : r ≠ s := fun h => hr h.symm
    have hsp : s ≠ p := fun h => hr'.2 (by rw [← hπ r, ← hsdef, h])
    have hsq : s ≠ q := fun h => hr'.1 (by rw [← hπ r, ← hsdef, h, hπq])
    refine ⟨swap p q, swap r s, ⟨p, q, hpq, rfl⟩, ⟨r, s, hrs, rfl⟩, swap_comm_of_apply h2,
      swap_comm_of_apply h2, ?_, ?_, ?_, ?_⟩
    · intro h
      have := DFunLike.congr_fun h p
      rw [swap_apply_left, swap_apply_of_ne_of_ne hr'.1.symm hsp.symm] at this
      exact hpq this.symm
    · exact swap_mul_swap_comm_of_ne hr'.1.symm hsp.symm hr'.2.symm hsq.symm
    ·
      obtain ⟨t, ht, ht'⟩ : ∃ t ∈ π.support, t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s := by
        by_contra hcon
        push Not at hcon
        have : π.support ⊆ {p, q, r, s} := fun t ht => by
          by_cases h1 : t = p; · simp [h1]
          by_cases h2 : t = q; · simp [h2]
          by_cases h3 : t = r; · simp [h3]
          simp [hcon t ht h1 h2 h3]
        have := (Finset.card_le_card this).trans Finset.card_le_four
        omega
      rw [mem_support] at ht
      intro h
      apply ht
      rw [← h, Perm.mul_apply, swap_apply_of_ne_of_ne ht'.2.2.1 ht'.2.2.2,
        swap_apply_of_ne_of_ne ht'.1 ht'.2.1]
    · intro c hc hcw
      rw [swap_conj_eq]
      have hwp : (swap p q * swap r s) p = q := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hr'.1.symm hsp.symm, swap_apply_left]
      have hcp : (swap p q * swap r s) (c p) ≠ c p := by
        have h1 : (swap p q * swap r s) (c p) = c q := by
          rw [← Perm.mul_apply (swap p q * swap r s) c p, ← hcw, Perm.mul_apply, hwp]
        rw [h1]
        exact fun h => hpq (c.injective h).symm
      have hcq : c q = π (c p) := by rw [hcommute c hc p]
      rcases mem_of_mul_swap_apply_ne hcp with h | h | h | h
      · left; rw [hcq, h, ← hq]
      · left; rw [hcq, h, hπq, swap_comm]
      · right; rw [hcq, h, ← hsdef]
      · right; rw [hcq, h, hπ r, swap_comm]
  ·
    have h4 : π.support.card = 4 := by omega
    have hfix : 3 ≤ (Finset.univ \ π.support).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨r, hr, s, hs', hrs⟩ := Finset.one_lt_card.1 (show 1 < (Finset.univ \ π.support).card
      by omega)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_support, not_not] at hr hs'
    have hrp : r ≠ p := fun h => hp (by rw [hq, ← h]; exact hr)
    have hrq : r ≠ q := fun h => hpq (by
      have := hr
      rw [h, hπq] at this
      exact this)
    have hsp : s ≠ p := fun h => hp (by rw [hq, ← h]; exact hs')
    have hsq : s ≠ q := fun h => hpq (by
      have := hs'
      rw [h, hπq] at this
      exact this)
    refine ⟨swap p q, swap r s, ⟨p, q, hpq, rfl⟩, ⟨r, s, hrs, rfl⟩, swap_comm_of_apply h2,
      (swap_comm_of_fixed hr hs').symm.symm, ?_, ?_, ?_, ?_⟩
    · intro h
      have := DFunLike.congr_fun h p
      rw [swap_apply_left, swap_apply_of_ne_of_ne hrp.symm hsp.symm] at this
      exact hpq this.symm
    · exact swap_mul_swap_comm_of_ne hrp.symm hsp.symm hrq.symm hsq.symm
    · intro h
      have := DFunLike.congr_fun h r
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hsp hsq, hr] at this
      exact hrs this.symm
    · intro c hc hcw
      rw [swap_conj_eq]
      have hwp : (swap p q * swap r s) p = q := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hrp.symm hsp.symm, swap_apply_left]
      have hcp : (swap p q * swap r s) (c p) ≠ c p := by
        have h1 : (swap p q * swap r s) (c p) = c q := by
          rw [← Perm.mul_apply (swap p q * swap r s) c p, ← hcw, Perm.mul_apply, hwp]
        rw [h1]
        exact fun h => hpq (c.injective h).symm
      have hcpm : π (c p) ≠ c p := by
        rw [hcommute c hc p]
        exact fun h => hpq (c.injective h).symm
      have hcq : c q = π (c p) := by rw [hcommute c hc p]
      left
      rcases mem_of_mul_swap_apply_ne hcp with h | h | h | h
      · rw [hcq, h, ← hq]
      · rw [hcq, h, hπq, swap_comm]
      · exact absurd (by rw [h]; exact hr) hcpm
      · exact absurd (by rw [h]; exact hs') hcpm

end Pair

section Excl

variable {G : Type*} [Group G] {z : G} {m : ℕ}

theorem coe_eM_mul {M : Subgroup G} (eM : Perm (Fin (m + 3)) ≃* M) (x y : Perm (Fin (m + 3))) :
    (eM (x * y) : G) = eM x * eM y := by
  rw [map_mul]; rfl

theorem eM_comm {M : Subgroup G} (eM : Perm (Fin (m + 3)) ≃* M) {x y : Perm (Fin (m + 3))}
    (hxy : x * y = y * x) : (eM x : G) * eM y = eM y * eM x := by
  rw [← coe_eM_mul, ← coe_eM_mul, hxy]

theorem eM_comm_iff {M : Subgroup G} (eM : Perm (Fin (m + 3)) ≃* M) {x y : Perm (Fin (m + 3))}
    (hxy : (eM x : G) * eM y = eM y * eM x) : x * y = y * x := by
  apply eM.injective
  apply Subtype.ext
  rw [coe_eM_mul, coe_eM_mul]
  exact hxy

theorem isSwap_of_swap_partner_compat (hm : 10 ≤ m) (D : NearData z (m + 1)) {M : Subgroup G}
    (eM : Perm (Fin (m + 3)) ≃* M) (hz : (eM (adjSwap (m + 2) (m + 1)) : G) = z)
    (hcompat : ∀ σ : Perm (Fin (m + 1)), (eM (inclPerm m σ) : G) = D.ι σ)
    {e π : Perm (Fin (m + 3))} (he : e.IsSwap) (Da : NearData (eM π : G) (m + 1))
    (hpe : (eM e : G) ∈ Partners (eM π : G))
    (hsw : (Da.π ⟨eM e, NearData.mem_centralizer_of_partner hpe⟩).IsSwap) : π.IsSwap := by
  obtain ⟨γ, hγ⟩ : ∃ γ : Perm (Fin (m + 3)), γ * adjSwap (m + 2) (m + 1) * γ⁻¹ = e := by
    have h1 : IsConj (adjSwap (m + 2) (m + 1)) e := by
      rw [adjSwap_of_lt (by omega)]
      obtain ⟨p, q, hpq, rfl⟩ := he
      exact isConj_swap (by simp [Fin.ext_iff]) hpq
    obtain ⟨γ, hγ⟩ := isConj_iff.1 h1
    exact ⟨γ, hγ⟩
  set g : G := (eM γ : G) with hgdef
  have hg : g * z * g⁻¹ = eM e := by
    rw [← hz, hgdef, ← hγ, coe_eM_mul, coe_eM_mul, map_inv]
    rfl
  set De := D.conj g with hDe
  have hpe' : g * z * g⁻¹ ∈ Partners (eM π : G) := by rw [hg]; exact hpe
  have hsw' : (Da.π ⟨g * z * g⁻¹, NearData.mem_centralizer_of_partner hpe'⟩).IsSwap := by
    rw [Da.π_congr hg _ (NearData.mem_centralizer_of_partner hpe)]
    exact hsw
  have hsym := NearData.isSwap_symm (by omega) Da De hpe' hsw'
  obtain ⟨-, heq⟩ := De.near ⟨(eM π : G), NearData.mem_centralizer_of_partner (Partners.symm hpe')⟩
    (Partners.symm hpe') (NearData.isNearPerm_of_isSwap (by omega) hsym)
  set τ := De.π ⟨eM π, NearData.mem_centralizer_of_partner (Partners.symm hpe')⟩ with hτ
  have heq' : (eM π : G) = g * D.ι τ * g⁻¹ := by
    rw [← NearData.conj_ι_apply]
    exact heq
  rw [← hcompat, hgdef] at heq'
  have hπ : π = γ * inclPerm m τ * γ⁻¹ := by
    apply eM.injective
    apply Subtype.ext
    rw [coe_eM_mul, coe_eM_mul, heq', map_inv]
    rfl
  rw [hπ]
  obtain ⟨p, q, hpq, hτe⟩ := inclPerm_isSwap hsym
  rw [hτe, swap_conj_eq]
  exact ⟨_, _, fun h => hpq (γ.injective h), rfl⟩

theorem isSwap_of_isConj_of_cent (hm : 10 ≤ m) (D : NearData z (m + 1)) {M : Subgroup G}
    (eM : Perm (Fin (m + 3)) ≃* M) (hz : (eM (adjSwap (m + 2) (m + 1)) : G) = z)
    (hcompat : ∀ σ : Perm (Fin (m + 1)), (eM (inclPerm m σ) : G) = D.ι σ)
    (hconj : ∀ ρ : Perm (Fin (m + 3)), ρ.IsSwap → IsConj z (eM ρ : G))
    (h47 : ∀ e e' : Perm (Fin (m + 3)), e.IsSwap → e'.IsSwap → e ≠ e' → e * e' = e' * e →
      centralizer ({(eM (e * e') : G)} : Set G) ≤ M)
    {π : Perm (Fin (m + 3))} (ha : IsConj z (eM π : G)) : π.IsSwap := by
  classical
  by_contra hns
  have hz2 : z * z = 1 := D.sq
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 ha
  have ha2 : (eM π : G) * eM π = 1 := by
    rw [← hg₀]
    calc g₀ * z * g₀⁻¹ * (g₀ * z * g₀⁻¹) = g₀ * (z * z) * g₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hπ2 : π * π = 1 := by
    apply eM.injective
    apply Subtype.ext
    rw [coe_eM_mul, map_one]
    exact ha2
  have ha1 : (eM π : G) ≠ 1 := fun h => D.ne_one (by
    calc z = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [hg₀, h]; group)
  have hπ1 : π ≠ 1 := fun h => ha1 (by rw [h, map_one]; rfl)
  obtain ⟨e, e', he, he', hec, he'c, hee', hcomm, heeπ, hnorm⟩ :=
    exists_swap_pair (by omega) hπ2 hπ1 hns
  have hpart : ∀ f : Perm (Fin (m + 3)), f.IsSwap → f * π = π * f →
      (eM f : G) ∈ Partners (eM π : G) := by
    intro f hf hfc
    refine ⟨ha.symm.trans (hconj f hf), fun h => hns ?_, eM_comm eM hfc⟩
    have : f = π := eM.injective (Subtype.ext h)
    rw [← this]; exact hf
  have hpe := hpart e he hec
  have hpe' := hpart e' he' he'c
  obtain ⟨Da⟩ := D.nonempty_of_isConj ha
  set σe := Da.π ⟨eM e, NearData.mem_centralizer_of_partner hpe⟩ with hσe
  set σe' := Da.π ⟨eM e', NearData.mem_centralizer_of_partner hpe'⟩ with hσe'
  have hwC : (eM (e * e') : G) ∈ centralizer ({(eM π : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact eM_comm eM (by
      calc e * e' * π = e * (π * e') := by rw [mul_assoc, he'c]
        _ = π * (e * e') := by rw [← mul_assoc, hec, mul_assoc])
  have hπw : Da.π ⟨eM (e * e'), hwC⟩ = σe * σe' := by
    rw [hσe, hσe', ← map_mul]
    exact Da.π_congr (coe_eM_mul eM e e') _ _
  have hN : ∀ c : Perm (Fin (m + 1)), c * (σe * σe') = (σe * σe') * c →
      c * σe * c⁻¹ = σe ∨ c * σe * c⁻¹ = σe' := by
    intro σ hσ
    set x : G := (Da.ι σ : G) with hx
    have hxa : x * eM π = eM π * x := Da.ι_comm σ
    have hxw : x * eM (e * e') = eM (e * e') * x := by
      rcases Da.eq_or ⟨eM (e * e'), hwC⟩ with h | h
      · have h' : (eM (e * e') : G) = Da.ι (σe * σe') := by rw [← hπw]; exact h
        rw [h', hx, ← Da.ι_mul, ← Da.ι_mul, hσ]
      · have h' : (eM (e * e') : G) = eM π * Da.ι (σe * σe') := by rw [← hπw]; exact h
        rw [h', ← mul_assoc, hxa, mul_assoc, hx, ← Da.ι_mul, hσ, Da.ι_mul, ← mul_assoc]
    have hxM : x ∈ M := h47 e e' he he' hee' hcomm (mem_centralizer_singleton_iff.2 hxw)
    set c := eM.symm ⟨x, hxM⟩ with hc
    have hcx : (eM c : G) = x := by rw [hc, MulEquiv.apply_symm_apply]
    have hcπ : c * π = π * c := eM_comm_iff eM (by rw [hcx]; exact hxa)
    have hcw : c * (e * e') = (e * e') * c := eM_comm_iff eM (by rw [hcx]; exact hxw)
    have hσx : Da.π ⟨x, Da.ι_mem σ⟩ = σ := Da.π_ι σ
    rcases hnorm c hcπ hcw with h | h
    · left
      have h1 : x * eM e * x⁻¹ = eM e := by
        rw [← hcx, ← coe_eM_mul, ← Subgroup.coe_inv, ← map_inv, ← coe_eM_mul, h]
      have h2 := congrArg Da.π (show (⟨x, Da.ι_mem σ⟩ : centralizer ({(eM π : G)} : Set G)) *
          ⟨eM e, NearData.mem_centralizer_of_partner hpe⟩ * (⟨x, Da.ι_mem σ⟩)⁻¹ =
          ⟨eM e, NearData.mem_centralizer_of_partner hpe⟩ from Subtype.ext h1)
      rwa [map_mul, map_mul, map_inv, hσx] at h2
    · right
      have h1 : x * eM e * x⁻¹ = eM e' := by
        rw [← hcx, ← coe_eM_mul, ← Subgroup.coe_inv, ← map_inv, ← coe_eM_mul, h]
      have h2 := congrArg Da.π (show (⟨x, Da.ι_mem σ⟩ : centralizer ({(eM π : G)} : Set G)) *
          ⟨eM e, NearData.mem_centralizer_of_partner hpe⟩ * (⟨x, Da.ι_mem σ⟩)⁻¹ =
          ⟨eM e', NearData.mem_centralizer_of_partner hpe'⟩ from Subtype.ext h1)
      rwa [map_mul, map_mul, map_inv, hσx] at h2
  have hinv : ∀ f : Perm (Fin (m + 3)), f.IsSwap → (eM f : G) * eM f = 1 := by
    intro f hf
    obtain ⟨p, q, -, rfl⟩ := hf
    rw [← coe_eM_mul, swap_mul_self, map_one]; rfl
  have hσe2 : σe * σe = 1 := Da.π_mul_self (hinv e he)
  have hσe'2 : σe' * σe' = 1 := Da.π_mul_self (hinv e' he')
  have hσc : σe * σe' = σe' * σe := by
    rw [hσe, hσe', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (eM_comm eM hcomm)
  have hne1 : ∀ f : Perm (Fin (m + 3)), f.IsSwap → (hf : (eM f : G) ∈ Partners (eM π : G)) →
      Da.π ⟨eM f, NearData.mem_centralizer_of_partner hf⟩ ≠ 1 := by
    intro f hf hfp
    refine Da.π_ne_one (fun h => ?_) hfp.2.1
    apply D.ne_one
    have := (hconj f hf)
    rw [h] at this
    exact isConj_one_right.1 this.symm
  rcases card_support_le_four_of_normalizes (by simp; omega) hσe2 hσe'2 hσc
      (hne1 e he hpe) (hne1 e' he' hpe') hN with h | h
  · have hnear : IsNearPerm σe := by
      have := NearData.fixFin_card_add_support_card σe
      constructor <;> omega
    exact hns (isSwap_of_swap_partner_compat hm D eM hz hcompat he Da hpe
      (Da.near _ hpe hnear).1)
  · have hnear : IsNearPerm σe' := by
      have := NearData.fixFin_card_add_support_card σe'
      constructor <;> omega
    exact hns (isSwap_of_swap_partner_compat hm D eM hz hcompat he' Da hpe'
      (Da.near _ hpe' hnear).1)

theorem isSwap_π_of_partner (hm : 10 ≤ m) (D : NearData z (m + 1)) {M : Subgroup G}
    (eM : Perm (Fin (m + 3)) ≃* M) (hC : centralizer ({z} : Set G) ≤ M)
    (hz : (eM (adjSwap (m + 2) (m + 1)) : G) = z)
    (hcompat : ∀ σ : Perm (Fin (m + 1)), (eM (inclPerm m σ) : G) = D.ι σ)
    (hconj : ∀ ρ : Perm (Fin (m + 3)), ρ.IsSwap → IsConj z (eM ρ : G))
    (h47 : ∀ e e' : Perm (Fin (m + 3)), e.IsSwap → e'.IsSwap → e ≠ e' → e * e' = e' * e →
      centralizer ({(eM (e * e') : G)} : Set G) ≤ M)
    {a : G} (ha : a ∈ Partners z) :
    (D.π ⟨a, NearData.mem_centralizer_of_partner ha⟩).IsSwap := by
  classical
  have haM : a ∈ M := hC (NearData.mem_centralizer_of_partner ha)
  set π := eM.symm ⟨a, haM⟩ with hπdef
  have hπa : (eM π : G) = a := by rw [hπdef, MulEquiv.apply_symm_apply]
  have hsw : π.IsSwap := isSwap_of_isConj_of_cent hm D eM hz hcompat hconj h47 (hπa ▸ ha.1)
  set τz := adjSwap (m + 2) (m + 1) with hτz
  have hτzs : τz.IsSwap := adjSwap_isSwap (by omega)
  have hcπ : π * τz = τz * π := eM_comm_iff eM (by rw [hπa, hz]; exact ha.2.2)
  have hne : π ≠ τz := fun h => ha.2.1 (by rw [← hπa, h, hz])
  have hfix : ∀ x, τz x ≠ x → π x = x := fun x hx => fixes_of_comm_swap hτzs hsw hcπ hne hx
  obtain ⟨p, q, hpq, hπe⟩ := hsw
  have hlt : ∀ x : Fin (m + 3), π x ≠ x → (x : ℕ) < m + 1 := by
    intro x hx
    by_contra hcon
    apply hx
    apply hfix
    rw [hτz, adjSwap_of_lt (by omega)]
    rcases (by omega : (x : ℕ) = m + 1 ∨ (x : ℕ) = m + 2) with h | h
    · have : x = ⟨m + 1, by omega⟩ := Fin.ext h
      rw [this, swap_apply_left]
      simp [Fin.ext_iff]
    · have : x = ⟨m + 1 + 1, by omega⟩ := Fin.ext h
      rw [this, swap_apply_right]
      simp [Fin.ext_iff]
  have hp : (p : ℕ) < m + 1 := hlt p (by rw [hπe, swap_apply_left]; exact hpq.symm)
  have hq : (q : ℕ) < m + 1 := hlt q (by rw [hπe, swap_apply_right]; exact hpq)
  set p' : Fin (m + 1) := ⟨p, hp⟩
  set q' : Fin (m + 1) := ⟨q, hq⟩
  have hincl : inclPerm m (swap p' q') = π := by
    rw [inclPerm_swap, hπe]
  have ha' : a = D.ι (swap p' q') := by rw [← hcompat, hincl, hπa]
  have : D.π ⟨a, NearData.mem_centralizer_of_partner ha⟩ = swap p' q' := by
    rw [← D.π_ι (swap p' q')]
    exact D.π_congr ha' _ _
  rw [this]
  exact ⟨p', q', fun h => hpq (Fin.ext (by simpa [p', q'] using congrArg Fin.val h)), rfl⟩

end Excl

end CFSG.OddStandard.AltStdSec
