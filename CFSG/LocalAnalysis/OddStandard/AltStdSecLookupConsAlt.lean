module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSym

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

theorem lookup_zpow_eq_one_or_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

theorem lookup_exists_of_mem_alt {X : Type} [Group X] {W : Subgroup X} {N : ℕ}
    (eW : W ≃* alternatingGroup (Fin N)) (ι : X →* Perm (Fin N))
    (hιW : ∀ w : W, ι (w : X) = ((eW w : alternatingGroup (Fin N)) : Perm (Fin N)))
    {g : Perm (Fin N)} (hg : g ∈ alternatingGroup (Fin N)) : ∃ w : W, ι (w : X) = g :=
  ⟨eW.symm ⟨g, hg⟩, by rw [hιW]; simp⟩

theorem symOutcome_of_alt {X : Type} [Group X] [Finite X] {t : X} {A W : Subgroup X} [W.Normal]
    {m N : ℕ} (h : ExactShape t A m) (hm : 7 ≤ m) (hAW : A ≤ W)
    (hCW : centralizer (W : Set X) = ⊥)
    (hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)))
    (eW : W ≃* alternatingGroup (Fin N)) :
    SymOutcome t m ∧ t ∉ W ∧ ∃ x ∈ W, x ∈ centralizer ({t} : Set X) ∧ x ∉ A := by
  classical
  obtain ⟨eA⟩ := h.iso
  have hcA : Nat.card A = m.factorial / 2 := card_eq_of_equiv_alt (by omega) eA
  have hNm : m ≤ N := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : Nat.card A ≤ Nat.card (Perm (Fin N)) :=
      (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hAW)).trans
        ((Nat.card_congr eW.toEquiv ▸ Subgroup.card_le_card_group (alternatingGroup (Fin N))))
    rw [hcA, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    have h2 : N.factorial ≤ (m - 1).factorial := Nat.factorial_le (by omega)
    have h3 : 2 * (m - 1).factorial + 2 ≤ m.factorial := by
      have := Nat.mul_factorial_pred (show m ≠ 0 by omega)
      have h5 := Nat.factorial_pos (m - 1)
      nlinarith
    have h4 : (m - 1).factorial < m.factorial / 2 := by omega
    omega
  have hN5 : 5 ≤ N := by omega
  have hN6 : N ≠ 6 := by omega
  obtain ⟨ι, hι, hιW⟩ := lookup_exists_perm_embedding W hCW hN5 hN6 eW
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.order, sq] at this
    exact this
  have hτ2 : ι t * ι t = 1 := by rw [← map_mul, ht2, map_one]
  have hτ1 : ι t ≠ 1 := by
    intro h1
    have : t = 1 := hι (by rw [h1, map_one])
    have h2 := h.order
    rw [this, orderOf_one] at h2
    omega
  set τ := ι t with hτdef
  have hmemA : ∀ a ∈ A, ι a ∈ alternatingGroup (Fin N) := by
    intro a ha
    rw [show ι a = _ from hιW ⟨a, hAW ha⟩]
    exact (eW ⟨a, hAW ha⟩).2
  have hcommA : ∀ a ∈ A, ι a * τ = τ * ι a := by
    intro a ha
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (h.le_cent ha)]
  have hA'A : A.map ι ≤ alternatingGroup (Fin N) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hmemA a ha
  have hA'c : A.map ι ≤ centralizer ({τ} : Set (Perm (Fin N))) := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hcommA a ha)
  have hCWt : (W ⊓ centralizer ({t} : Set X)).map ι =
      alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · rw [show ι y = _ from hιW ⟨y, hy.1⟩]
        exact (eW ⟨y, hy.1⟩).2
      · rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy.2]
    · rintro ⟨hx, hxc⟩
      obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hx
      refine ⟨w, ⟨w.2, mem_centralizer_singleton_iff.2 ?_⟩, hw⟩
      apply hι
      rw [map_mul, map_mul, hw]
      exact mem_centralizer_singleton_iff.1 hxc
  have hAcomp : CFSG.IsComponent
      ((A.map ι).subgroupOf
        (alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))))) := by
    have h1 : CFSG.Assembly.IsComponentOf A (W ⊓ centralizer ({t} : Set X)) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp
        (le_inf hAW h.le_cent) inf_le_right
    have h2 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hι).2 h1
    rw [hCWt] at h2
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (le_inf hA'A hA'c)).1 h2
  obtain ⟨hF5, hsupp, ⟨eP⟩⟩ := component_eq_alt_fixed hτ2 hA'A hA'c hAcomp
  have hFcard : m = Fintype.card {x : Fin N // τ x = x} := by
    have hk2 : 2 ≤ Fintype.card {x : Fin N // τ x = x} := by omega
    have : Nontrivial {x : Fin N // τ x = x} := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have h1 : Nat.card A = Nat.card (alternatingGroup {x : Fin N // τ x = x}) :=
      Nat.card_congr ((A.equivMapOfInjective ι hι).trans eP).toEquiv
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := {x : Fin N // τ x = x}),
      hcA] at h1
    have h2 : m.factorial = (Fintype.card {x : Fin N // τ x = x}).factorial :=
      (Nat.div_left_inj (Nat.dvd_factorial (by norm_num) (by omega))
        (Nat.dvd_factorial (by norm_num) hk2)).1 h1
    exact (Nat.factorial_inj (by omega)).1 h2
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    simpa using congrArg (fun p : Perm (Fin N) => p x) hτ2
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra hcon
    exact hτ1 (Equiv.ext fun x => by_contra fun hx => hcon ⟨x, hx⟩)
  have hcyc : ∀ c, τ c ≠ c → c = a ∨ c = τ a := by
    intro c hc
    by_contra hne
    rw [not_or] at hne
    obtain ⟨g, hgA, hgτ, hg1, hgτ', hgsupp⟩ := exists_even_commuting_swap hτ2 ha hc hne.1 hne.2
    obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hgA
    have hwt : (w : X) * t = t * w := hι (by rw [map_mul, map_mul, hw]; exact hgτ)
    have hwA : (w : X) ∈ centralizer (A : Set X) := by
      rw [mem_centralizer_iff]
      intro a' ha'
      apply hι
      rw [map_mul, map_mul, hw]
      have hd : Perm.Disjoint (ι a') g := by
        intro x
        by_cases hgx : g x = x
        · exact Or.inr hgx
        · exact Or.inl (hsupp (ι a') ⟨a', ha', rfl⟩ x (hgsupp x hgx))
      exact hd.commute.eq
    have hmem : (w : X) ∈ zpowers t := by
      rw [← h.cent_cent]
      exact ⟨hwA, mem_centralizer_singleton_iff.2 hwt⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hgk : g = τ ^ k := by rw [← hw, ← hk, map_zpow]
    rcases lookup_zpow_eq_one_or_self hτ2 k with h1 | h1
    · exact hg1 (hgk.trans h1)
    · exact hgτ' (hgk.trans h1)
  have hswap : τ = swap a (τ a) := eq_swap_of_unique_cycle hτ2 ha hcyc
  have hcardF : Fintype.card {x : Fin N // τ x = x} + 2 = N := by
    have h1 := Fintype.card_subtype_compl (fun x : Fin N => τ x = x)
    have h2 : Fintype.card {x : Fin N // ¬ τ x = x} = 2 := by
      rw [Fintype.card_subtype]
      have : (Finset.univ.filter fun x : Fin N => ¬ τ x = x) = {a, τ a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · exact hcyc x
        · rintro (hx | hx)
          · rw [hx]
            exact ha
          · rw [hx, hττ a]
            exact fun h' => ha h'.symm
      rw [this, Finset.card_pair]
      exact fun h => ha h.symm
    rw [Fintype.card_fin] at h1
    have h3 := Fintype.card_subtype_le (fun x : Fin N => τ x = x)
    rw [Fintype.card_fin] at h3
    omega
  have hτsgn : Perm.sign τ = -1 := by rw [hswap, Perm.sign_swap (Ne.symm ha)]
  have hsurj : Function.Surjective ι := by
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin N)
    · obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hσ
      exact ⟨w, hw⟩
    · have hsgn : Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
        · exact absurd (Perm.mem_alternatingGroup.2 h1) hσ
        · exact h1
      have hστ : σ * τ ∈ alternatingGroup (Fin N) := by
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, hsgn, hτsgn]
        decide
      obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hστ
      refine ⟨w * t, ?_⟩
      rw [map_mul, hw, mul_assoc, hτ2, mul_one]
  have htW : t ∉ W := by
    intro htW
    have h1 := (eW ⟨t, htW⟩).2
    rw [show ((eW ⟨t, htW⟩ : alternatingGroup (Fin N)) : Perm (Fin N)) = τ from
      (hιW ⟨t, htW⟩).symm, Perm.mem_alternatingGroup, hτsgn] at h1
    exact absurd h1 (by decide)
  have hex : ∃ x ∈ W, x ∈ centralizer ({t} : Set X) ∧ x ∉ A := by
    have hF1 : 1 < Fintype.card {x : Fin N // τ x = x} := by omega
    obtain ⟨c₁⟩ : Nonempty {x : Fin N // τ x = x} := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨d₁, hd₁⟩ := Fintype.exists_ne_of_one_lt_card hF1 c₁
    have hcτ : τ c₁.1 = c₁.1 := c₁.2
    have hdτ : τ d₁.1 = d₁.1 := d₁.2
    have hcd : d₁.1 ≠ c₁.1 := fun h' => hd₁ (Subtype.ext h')
    have hgA : swap c₁.1 d₁.1 * τ ∈ alternatingGroup (Fin N) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hcd.symm, hτsgn]
      decide
    have hcomm : τ * swap c₁.1 d₁.1 = swap c₁.1 d₁.1 * τ := by
      rw [mul_swap_eq_swap_mul, hcτ, hdτ]
    have hgτ : (swap c₁.1 d₁.1 * τ) * τ = τ * (swap c₁.1 d₁.1 * τ) := by
      rw [mul_assoc, hτ2, mul_one, ← mul_assoc, hcomm, mul_assoc, hτ2, mul_one]
    obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hgA
    refine ⟨(w : X), w.2, mem_centralizer_singleton_iff.2 ?_, fun hwA => ?_⟩
    · apply hι
      rw [map_mul, map_mul, hw]
      exact hgτ
    · have h1 := hsupp _ ⟨(w : X), hwA, hw⟩ a ha
      have hac : τ a ≠ c₁.1 := fun h' => ha (by
        have : a = c₁.1 := by rw [← hττ a, h', hcτ]
        rw [this, hcτ])
      have had : τ a ≠ d₁.1 := fun h' => ha (by
        have : a = d₁.1 := by rw [← hττ a, h', hdτ]
        rw [this, hdτ])
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had] at h1
      exact ha h1
  obtain rfl : N = m + 2 := by omega
  let e : Perm (Fin (m + 2)) ≃* X := (MulEquiv.ofBijective ι ⟨hι, hsurj⟩).symm
  exact ⟨⟨e, ⟨a, τ a, Ne.symm ha, hswap⟩⟩, htW, hex⟩

end CFSG.OddStandard.AltStdSec
