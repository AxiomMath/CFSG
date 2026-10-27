module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Base
public import CFSG.GH74.GLS.Stage2.Local.P27.P1Main

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local.P27

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem card_L₁ (hP : Stage1Pair G z S q L₁ L₂) : Nat.card ↥L₁ = q * (q ^ 2 - 1) := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := hP.sl₁
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]

theorem card_L2_mul_two {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (IVK.L2 F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hop : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    LinearGroups.isOddPrimePower_card_of_ringChar_ne_two (p1_ringChar_ne_two_of_odd_card hodd)
  rw [Nat.card_congr (IVK.L2.equivPSL F).toEquiv, GorensteinWalter.psl2_card_formula F hop]
  apply Nat.div_mul_cancel
  obtain ⟨k, hk⟩ := hodd
  rw [hk]
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [h1]
  exact ⟨(2 * k + 1) * (2 * (k * (k + 1))), by ring⟩

theorem card_CL (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) : Nat.card ↥(CL z t) = q * (q ^ 2 - 1) := by
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := Stage1.Main.exists_CL_iso hP hsw ht2
  have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  have h4 := card_L2_mul_two (F := F) (by rw [hFq]; exact hP.odd)
  rw [hFq] at h4
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, h3, h4]

theorem card_CL_eq_card_L₁ (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) : Nat.card ↥(CL z t) = Nat.card ↥L₁ := by
  rw [card_CL hP hsw ht2, card_L₁ hP]

theorem card_P_eq (hS : IsSylowOf 2 S (Cen z)) (L : Subgroup (CentralizerBar z)) :
    Nat.card ↥((L.comap (rhoS hS)).map S.subtype) = Nat.card ↥(barOf z S ⊓ L) := by
  have hρ := rhoS_injective hS
  have hbar : ∀ s : ↥S, rhoS hS s ∈ barOf z S := fun s => (mem_barOf_S_iff hS _).2 ⟨s, rfl⟩
  let f : ↥(L.comap (rhoS hS)) →* ↥(barOf z S ⊓ L) :=
    ((rhoS hS).comp (L.comap (rhoS hS)).subtype).codRestrict (barOf z S ⊓ L)
      (fun s => ⟨hbar s.1, s.2⟩)
  have hfinj : Function.Injective f := fun x y h => Subtype.ext (hρ (congrArg Subtype.val h))
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨s, hs⟩ := (mem_barOf_S_iff hS x).1 hx1
    exact ⟨⟨s, by show rhoS hS s ∈ L; rw [hs]; exact hx2⟩, Subtype.ext hs⟩
  rw [← Nat.card_congr ((L.comap (rhoS hS)).equivMapOfInjective S.subtype S.subtype_injective).toEquiv]
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)

theorem factorization_card_L₁ (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    {P₁ : Subgroup G} {a : ℕ} (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype)
    (hPc : Nat.card ↥P₁ = 2 ^ a) : (Nat.card ↥L₁).factorization 2 = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h1, -⟩ := bar_sylow_structure hS hP
  have hc := h1.card_eq
  rw [← card_P_eq hS L₁, ← hP₁, hPc] at hc
  exact (Nat.pow_right_injective (le_refl 2) (by show 2 ^ a = 2 ^ _; exact hc)).symm

theorem factorization_card_CL (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    {t : G} (hsw : Swaps z t L₁ L₂) (ht2 : t * t = 1) {P₁ : Subgroup G} {a : ℕ}
    (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype) (hPc : Nat.card ↥P₁ = 2 ^ a) :
    (Nat.card ↥(CL z t)).factorization 2 = a := by
  rw [card_CL_eq_card_L₁ hP hsw ht2]
  exact factorization_card_L₁ hS hP hP₁ hPc

theorem factorization_card_A {t : G} {A : Subgroup (CentralizerBar z)} {a : ℕ}
    (hA : Nat.card ↥A * 2 = Nat.card ↥(CL z t))
    (hfac : (Nat.card ↥(CL z t)).factorization 2 = a) :
    (Nat.card ↥A).factorization 2 + 1 = a := by
  have hA0 : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
  rw [← hfac, ← hA, Nat.factorization_mul hA0 (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
