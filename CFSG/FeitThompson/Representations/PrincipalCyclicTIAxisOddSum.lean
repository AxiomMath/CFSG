module

public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
import CFSG.FeitThompson.Representations.CyclicTILinearCharIntegralCoprime
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

theorem even_sum_of_involutive_of_ne {ι : Type*} {s : Finset ι} {n : ι → ℤ} {τ : ι → ι}
    (hmem : ∀ a ∈ s, τ a ∈ s) (hinv : ∀ a ∈ s, τ (τ a) = a) (hne : ∀ a ∈ s, τ a ≠ a)
    (hval : ∀ a ∈ s, n (τ a) = n a) : Even (∑ a ∈ s, n a) := by
  have key : ((∑ a ∈ s, n a : ℤ) : ZMod 2) = 0 := by
    push_cast
    refine Finset.sum_involution (fun a _ => τ a) (fun a ha => ?_) (fun a ha _ => hne a ha)
      hmem hinv
    rw [hval a ha, ← two_mul, show ((2 : ZMod 2)) = 0 from by decide, zero_mul]
  exact even_iff_two_dvd.mpr (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp key)

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

namespace IsCyclicTIPair

theorem prodCharHom_val (hW : IsCyclicTIPair W W1 W2) (ψ₁ : ↥W1 →* ℂˣ) (ψ₂ : ↥W2 →* ℂˣ)
    (x : ↥W) : ((hW.prodCharHom ψ₁ ψ₂ x : ℂ)) =
      (ψ₁ (hW.mulEquivProd.symm x).1 : ℂ) * (ψ₂ (hW.mulEquivProd.symm x).2 : ℂ) :=
  (congrFun (hW.prodChar_coe_coe ψ₁ ψ₂) x).symm.trans (hW.prodChar_apply _ _ x)

variable [Fintype G] [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem exists_int_prodCharEta_row (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {g : G}
    (hg : (orderOf g).Coprime (Nat.card ↥W1)) (i : Irr ↥W1) :
    ∃ n : ℤ, hW.prodCharEta σ i (principalIrr ↥W2) g = (n : ℂ) := by
  have hfin := hW.finite_left
  have hcomm := hW.isMulCommutative_left
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_coe_eq_of_mem_Irr i.2
  have hbasis : linearCharClassFun (hW.prodCharHom ψ 1)
      = hW.basisProdIrr (i, principalIrr ↥W2) := by
    refine Subtype.ext ?_
    rw [coe_linearCharClassFun, coe_basisProdIrr_apply, coe_principalIrr, ← hψ]
    funext x
    rw [hW.prodCharHom_val ψ 1 x, hW.prodChar_apply]
    simp
  have hw : ∀ x : ↥W, (hW.prodCharHom ψ 1) x ^ Nat.card ↥W1 = 1 := by
    intro x
    have hp : (ψ ((hW.mulEquivProd.symm x).1)) ^ Nat.card ↥W1 = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine Units.val_eq_one.mp ?_
    rw [Units.val_pow_eq_pow_val, hW.prodCharHom_val ψ 1 x]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one, ← Units.val_pow_eq_pow_val, hp]
  obtain ⟨n, hn⟩ := exists_int_apply_linearCharClassFun hW hσ (hW.prodCharHom ψ 1)
    hW.odd_natCard_left.pos hw hg
  refine ⟨n, ?_⟩
  have he : hW.prodCharEta σ i (principalIrr ↥W2) g
      = (σ (linearCharClassFun (hW.prodCharHom ψ 1)) : G → ℂ) g := by
    rw [hbasis, prodCharEta_eq_coe_apply]
  rw [he, hn]

theorem exists_odd_int_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W1)) :
    ∃ m : ℤ, Odd m ∧ hW.prodCharEtaColSum σ (principalIrr ↥W2) g = (m : ℂ) := by
  classical
  have hfin := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  choose n hn using hW.exists_int_prodCharEta_row hσ hg
  have h0 : n (principalIrr ↥W1) = 1 := by
    have h1 := hn (principalIrr ↥W1)
    rw [hW.prodCharEta_principal hσ, Pi.one_apply] at h1
    exact_mod_cast h1.symm
  have hstar : ∀ i : Irr ↥W1, n (starIrr i) = n i := by
    intro i
    have hc := congrFun (hW.conj_prodCharEta_row hσ (k := starIrr i) (coe_starIrr_eq i)) g
    rw [hn i, hn (starIrr i)] at hc
    simp only [map_intCast] at hc
    exact_mod_cast hc.symm
  refine ⟨∑ i : Irr ↥W1, n i, ?_, ?_⟩
  ·
    have hsplit : ∑ i : Irr ↥W1, n i
        = n (principalIrr ↥W1) + ∑ i ∈ Finset.univ.erase (principalIrr ↥W1), n i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    have heven : Even (∑ i ∈ Finset.univ.erase (principalIrr ↥W1), n i) := by
      refine even_sum_of_involutive_of_ne (τ := starIrr) (fun a ha => ?_) (fun a _ => ?_)
        (fun a ha => ?_) fun a _ => hstar a
      · exact Finset.mem_erase.2
          ⟨starIrr_ne_principalIrr (Finset.mem_erase.1 ha).1, Finset.mem_univ _⟩
      · exact starIrr_starIrr a
      · exact starIrr_ne_self hW.odd_natCard_left (Finset.mem_erase.1 ha).1
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by rw [hsplit, h0, hk]; ring⟩
  · rw [hW.prodCharEtaColSum_eq_sum, Finset.sum_apply]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hn i

theorem exists_odd_int_sum_prodCharEta_row [Fintype (Irr ↥W1)] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W1)) :
    ∃ m : ℤ, Odd m ∧ ∑ i : Irr ↥W1, hW.prodCharEta σ i (principalIrr ↥W2) g = (m : ℂ) := by
  obtain ⟨m, hodd, hm⟩ := hW.exists_odd_int_prodCharEtaColSum hσ hg
  refine ⟨m, hodd, ?_⟩
  rwa [hW.prodCharEtaColSum_eq_sum, Finset.sum_apply] at hm

theorem one_le_norm_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W1)) :
    1 ≤ ‖hW.prodCharEtaColSum σ (principalIrr ↥W2) g‖ := by
  obtain ⟨m, hodd, hm⟩ := hW.exists_odd_int_prodCharEtaColSum hσ hg
  have hm0 : m ≠ 0 := by rintro rfl; simp at hodd
  rw [hm, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem prodCharEtaColSum_ne_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W1)) :
    hW.prodCharEtaColSum σ (principalIrr ↥W2) g ≠ 0 := by
  intro he
  have h := hW.one_le_norm_prodCharEtaColSum hσ hg
  rw [he, norm_zero] at h
  exact absurd h (by norm_num)

end IsCyclicTIPair

end CFSG.FeitThompson
