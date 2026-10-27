module

public import CFSG.HardMathSupport.U4FF.Model
public import CFSG.HardMathSupport.U4FF.Singer
public import CFSG.HardMathSupport.U4FF.SmallGL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

variable {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}

@[expose] def actOn (S₁ : Subgroup S) (hS₁ : ∀ l ∈ L, ∀ s ∈ S₁, l s ∈ S₁) :
    ↥L →* MulAut ↥S₁ where
  toFun l :=
    { toFun := fun s => ⟨(l : MulAut S) s, hS₁ l l.2 s s.2⟩
      invFun := fun s => ⟨((l : MulAut S)⁻¹) s, hS₁ _ (L.inv_mem l.2) s s.2⟩
      left_inv := fun s => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun s => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun s => Subtype.ext rfl
  map_mul' := fun a b => MulEquiv.ext fun s => Subtype.ext rfl

variable {n : ℕ}

theorem isSimpleGroup_of_isU4Group (hL : IsU4Group n L) : IsSimpleGroup ↥L := by
  obtain ⟨F, _, hFfin, hcardF, ⟨e⟩⟩ := exists_equiv_statedProj hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hcardF 4
    (by norm_num) (fun h => absurd (Prod.mk.inj h).1 (by norm_num))
  haveI := h
  exact e.isSimpleGroup

theorem actOn_injective (hL : IsU4Group n L) (S₁ : Subgroup S)
    (hS₁ : ∀ l ∈ L, ∀ s ∈ S₁, l s ∈ S₁) (hnt : ∃ l ∈ L, ∃ s ∈ S₁, l s ≠ s) :
    Function.Injective (actOn S₁ hS₁) := by
  have hsimple := isSimpleGroup_of_isU4Group hL
  have hker : (actOn S₁ hS₁).ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (actOn S₁ hS₁).ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, s, hs, hne⟩ := hnt
      have h0 : (⟨l, hl⟩ : ↥L) ∈ (actOn S₁ hS₁).ker := by rw [h]; trivial
      have h1 : actOn S₁ hS₁ ⟨l, hl⟩ = 1 := h0
      apply hne
      have h2 := congrArg (fun φ : MulAut ↥S₁ => ((φ ⟨s, hs⟩ : S₁) : S)) h1
      simp only [MulAut.one_apply] at h2
      exact h2
  exact (MonoidHom.ker_eq_bot_iff _).1 hker

theorem two_pow_le_card_of_nontrivial_action [Finite S] (hS : ∀ s : S, s * s = 1)
    (hL : IsU4Group n L) (S₁ : Subgroup S) (hS₁ : ∀ l ∈ L, ∀ s ∈ S₁, l s ∈ S₁)
    (hnt : ∃ l ∈ L, ∃ s ∈ S₁, l s ≠ s) : 2 ^ (4 * n + 1) ≤ Nat.card S₁ := by
  classical
  haveI : Fact (∀ s : ↥S₁, s * s = 1) := ⟨fun s => Subtype.ext (hS s)⟩
  have hinj := actOn_injective hL S₁ hS₁ hnt
  let ρ : ↥L →* (Additive ↥S₁ ≃ₗ[ZMod 2] Additive ↥S₁) := binaryLin.comp (actOn S₁ hS₁)
  have hρ : Function.Injective ρ := binaryLin_injective.comp hinj
  have hcard : Nat.card S₁ = 2 ^ Module.finrank (ZMod 2) (Additive ↥S₁) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥S₁)
    rwa [Nat.card_zmod] at this
  suffices h : 4 * n + 1 ≤ Module.finrank (ZMod 2) (Additive ↥S₁) by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : CharP K 2 := h.charP
  haveI := finite_gramSU_miyamotoJ4 h
  haveI : Finite ↥L := Finite.of_equiv _ η.symm.toEquiv
  have hcardL : (Nat.card ↥L : ℤ) = ((2 ^ n : ℕ) : ℤ) ^ 6 *
      ((((2 ^ n : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ n : ℕ) : ℤ) ^ 3 + 1) * (((2 ^ n : ℕ) : ℤ) ^ 4 - 1)) := by
    rw [Nat.card_congr η.toEquiv]
    exact (card_gramSU_miyamotoJ4 h).1
  by_cases hn2 : 2 ≤ n
  · obtain ⟨ℓ, hℓ, hℓ2, hord, -, hdvd, -⟩ :=
      CFSG.QuasithinUnique.Setup.X5.binary_multiple_six_exponents_have_primitive_prime_divisors
        hn2
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hdvdL : ℓ ∣ Nat.card ↥L := by
      have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hqq : 2 ^ n ≤ (2 ^ n) ^ 2 := by nlinarith
      obtain ⟨c, hc⟩ := hdvd
      set q : ℤ := ((2 ^ n : ℕ) : ℤ) with hq
      have hcz : q ^ 2 - q + 1 = (ℓ : ℤ) * c := by
        have h1 := congrArg (fun m : ℕ => (m : ℤ)) hc
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
        rw [Nat.cast_sub hqq] at h1
        push_cast at h1
        rw [hq]
        push_cast
        linarith
      have hdvdZ : (ℓ : ℤ) ∣ (Nat.card ↥L : ℤ) := by
        rw [hcardL]
        have hq3 : q ^ 3 + 1 = (q + 1) * ((ℓ : ℤ) * c) := by rw [← hcz]; ring
        rw [hq3]
        exact ⟨q ^ 6 * ((q ^ 2 - 1) * ((q + 1) * c) * (q ^ 4 - 1)), by ring⟩
      exact_mod_cast hdvdZ
    haveI := Fintype.ofFinite ↥L
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card ℓ (by rwa [Fintype.card_eq_nat_card])
    have hox : orderOf (ρ x) = ℓ := by rw [orderOf_injective ρ hρ x]; exact hx
    have h6 := orderOf_two_le_finrank_of_orderOf_eq (ρ x) hℓ hℓ2 hox
    rw [hord] at h6
    omega
  · have hn1 : n = 1 := by
      have := one_le_of_isU4Group hL
      omega
    subst hn1
    by_contra hlt
    have h4 : Module.finrank (ZMod 2) (Additive ↥S₁) ≤ 4 := by omega
    have hle := card_le_of_faithful_finrank_le_four ρ hρ h4
    have h25 : (Nat.card ↥L : ℤ) = 25920 := by
      rw [hcardL]
      norm_num
    have : Nat.card ↥L = 25920 := by exact_mod_cast h25
    omega

end CFSG.HardMathSupport.U4FF
