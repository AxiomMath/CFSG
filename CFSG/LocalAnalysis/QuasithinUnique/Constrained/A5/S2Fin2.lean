module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Subs5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

@[expose] def zv : evenWeight 5 := ⟨z0, (mem_evenWeight_iff z0).2 (by decide +kernel)⟩

theorem zv_ne_zero : zv ≠ 0 := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  simp [zv, z0] at this

theorem vact_zv {σ : Perm (Fin 5)} (hσ : σ 4 = 4) : vact σ zv = zv :=
  Subtype.ext (z0_fixed σ hσ)

theorem fix_of_D (w : evenWeight 5) (h : ∀ σ ∈ Dset, vact σ w = w) : w = 0 ∨ w = zv := by
  rcases fixed_Dset w.1 ((mem_evenWeight_iff _).1 w.2) (fun σ hσ => congrArg Subtype.val (h σ hσ))
    with h0 | h0
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr (Subtype.ext h0)

theorem zv_comm : ∃ w : evenWeight 5,
    zv = (vact (swap 0 1) w + w) + (vact (swap 2 3) w + w) := by
  refine ⟨⟨g2, (mem_evenWeight_iff g2).2 g2_even⟩, Subtype.ext ?_⟩
  show z0 = (pact (swap 0 1) g2 + g2) + (pact (swap 2 3) g2 + g2)
  decide +kernel

theorem eSigma_ne : ∀ σ : Perm (Fin 5), σ 4 ≠ 4 → ∃ e ∈ Eset, (e * σ) ^ 4 ≠ 1 := by
  decide +kernel

theorem pow8_pow4 : ∀ g : Perm (Fin 5), g ^ 8 = 1 → g ^ 4 = 1 := by decide +kernel

theorem pow4_of_two_group {g : Perm (Fin 5)} (h : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf g ∣ 120 := by
    have := orderOf_dvd_card (G := Perm (Fin 5)) (x := g)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    have h120 : Nat.factorial 5 = 120 := by decide
    rwa [h120] at this
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hjo] at h16
    have := h16.trans h2
    omega
  have h8 : orderOf g ∣ 8 := by
    rw [hjo]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact pow8_pow4 g (orderOf_dvd_iff_pow_eq_one.1 h8)

theorem fix4_of_two_group {P : Subgroup (Perm (Fin 5))} (hP : ∀ σ ∈ P, ∃ k : ℕ, σ ^ 2 ^ k = 1)
    (hE : Estd ≤ P) : ∀ σ ∈ P, σ 4 = 4 := by
  intro σ hσ
  by_contra hne
  obtain ⟨e, he, hne'⟩ := eSigma_ne σ hne
  exact hne' (pow4_of_two_group (hP (e * σ) (P.mul_mem (hE he) hσ)))

theorem V_sub : ∀ σ : Perm (Fin 5), σ ∈ A4set → σ ^ 4 = 1 → σ ∈ Vset := by decide +kernel

theorem Vset_card : Vset.card = 4 := by decide +kernel

theorem Vstd_card : Nat.card Vstd = 4 := (mkSub_card _ _ _ _).trans Vset_card

theorem V_le_Vstd {V : Subgroup (Perm (Fin 5))} (h2 : ∀ σ ∈ V, ∃ k : ℕ, σ ^ 2 ^ k = 1)
    (h4 : ∀ σ ∈ V, σ 4 = 4) (hs : ∀ σ ∈ V, Perm.sign σ = 1) : V ≤ Vstd := fun σ hσ =>
  V_sub σ ((mem_A4set σ).2 ⟨h4 σ hσ, hs σ hσ⟩) (pow4_of_two_group (h2 σ hσ))

theorem V_eq_Vstd {V : Subgroup (Perm (Fin 5))} (h2 : ∀ σ ∈ V, ∃ k : ℕ, σ ^ 2 ^ k = 1)
    (h4 : ∀ σ ∈ V, σ 4 = 4) (hs : ∀ σ ∈ V, Perm.sign σ = 1) (hcard : Nat.card V = 4) :
    V = Vstd :=
  Subgroup.eq_of_le_of_card_ge (V_le_Vstd h2 h4 hs) (by rw [Vstd_card, hcard])

theorem Dset_le_of {P : Subgroup (Perm (Fin 5))} (hE : Estd ≤ P) (hV : Vstd ≤ P) :
    ∀ τ ∈ Dset, τ ∈ P := by
  intro τ hτ
  obtain ⟨v, hv, e, he, rfl⟩ := D_eq_VE τ hτ
  exact P.mul_mem (hV hv) (hE he)

theorem swap01_mem : (swap (0 : Fin 5) 1) ∈ Estd := by
  show swap (0 : Fin 5) 1 ∈ Eset
  decide +kernel

theorem swap23_mem : (swap (2 : Fin 5) 3) ∈ Estd := by
  show swap (2 : Fin 5) 3 ∈ Eset
  decide +kernel

theorem ew_add_self (w : evenWeight 5) : w + w = 0 := by
  ext i
  show w.1 i + w.1 i = 0
  generalize w.1 i = a
  revert a
  decide

theorem sylow_card_alt_five (P : Sylow 2 (alternatingGroup (Fin 5))) : Nat.card P = 4 := by
  rw [Sylow.card_eq_multiplicity, a5_card]
  have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h60, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

@[expose] def a234 : Perm (Fin 5) := swap 2 3 * swap 3 4

theorem a234_even : Perm.sign a234 = 1 := by decide +kernel

theorem a234_conj : a234 * (swap 0 1 * swap 2 3) * a234⁻¹ = swap 0 1 * swap 3 4 := by
  decide +kernel

theorem sigma_moves : (swap (0 : Fin 5) 1 * swap (3 : Fin 5) 4) 4 ≠ 4 := by decide +kernel

theorem sigma_even : Perm.sign (swap (0 : Fin 5) 1 * swap (3 : Fin 5) 4) = 1 := by decide +kernel

theorem vV_mem : (swap (0 : Fin 5) 1 * swap (2 : Fin 5) 3) ∈ Vset := by decide +kernel

theorem vact_zero (σ : Perm (Fin 5)) : vact σ 0 = 0 := Subtype.ext rfl

end CFSG.QuasithinUnique.A5.S2
