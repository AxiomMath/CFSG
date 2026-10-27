module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclComp
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclR

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N

section


theorem layer_eq_bot (hTop : TopStatement) {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    {A : Subgroup X} (hAS : A ≤ S) (hab : IsElemAbelian 2 A) (hA : Nat.card A = 256)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    {x t : X} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (ht2 : t * t = 1) (htx : t * x = x * t)
    (hxA : x ∈ normalizer (A : Set X)) (htA : t ∈ normalizer (A : Set X))
    (hfpf : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1)
    {U : Subgroup X} (hUA : U ≤ A) (hU : Nat.card U = 16)
    (hCt : ∀ a ∈ A, t * a * t⁻¹ = a ↔ a ∈ U)
    {s : X} (hs : ∃ h : X, s = h * t * h⁻¹) (hsA : s ∈ normalizer (A : Set X))
    (hv : (t * s) * x * (t * s)⁻¹ = x⁻¹)
    (hsolv : Group.IsSolvable ↥(centralizer ({t} : Set X)))
    (hIα : Nat.card (imgIn A (normalizer (A : Set X))) ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2) :
    goldschmidtLayer (Mbar A) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hU1, hU2, hU3⟩ := unpack hTop S hAS hab.1 hcl
  have hφ5 : rhoHom A x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hψ2 : rhoHom A t ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 by rw [sq]; exact ht2, map_one]
  have hφψ : rhoHom A x * rhoHom A t = rhoHom A t * rhoHom A x := by
    rw [← map_mul, ← map_mul, htx]
  have hcardAbar : Nat.card (Abar A) = 256 := by rw [card_Abar hab]; exact hA
  have hfpfbar := rhoHom_fpf hab hxA hfpf
  have hRA : pCore 2 (Mbar A) ≤ Abar A := R_le_Abar hTop S hAS hab.1 hcl
  have hφA : ∀ a ∈ Abar A, rhoHom A x a ∈ Abar A := fun a ha => rhoHom_mem_Abar A hxA ha
  have hψA : ∀ a ∈ Abar A, rhoHom A t a ∈ Abar A := fun a ha => rhoHom_mem_Abar A htA ha
  have hUfix : ∀ a ∈ Abar A, rhoHom A t a = a ↔ a ∈ Ubar A U :=
    fun a ha => rhoHom_fixed_iff hab htA hCt ha
  have hUcard : Nat.card (Ubar A U) = 16 := by rw [card_Ubar hab hUA]; exact hU
  by_cases hR1 : pCore 2 (Mbar A) = ⊥
  ·
    exfalso
    obtain ⟨Sb, hSb⟩ := exists_sylow_Mbar S A
    have hAb : Abar A = pCore 2 (Mbar A) ⊔ closure {t | t ∈ (Sb : Subgroup (Mbar A)) ⊓
        goldschmidtLayer (Mbar A) ∧ t ^ 2 = 1} := by
      rw [hSb]
      exact hU2
    have htrans := comp_transitive (oddCore_Mbar A) hR1 hU1 hU3 Sb hAb (isElemAbelian_Abar hab)
      hcardAbar hφ5 hψ2 hφψ hφA hψA hfpfbar (Ubar_le_Abar A U) hUfix hUcard
      (isSolvable_fixSub_rhoHom A ht2 hsolv)
    have hXtrans := normalizer_transitive_of_bar hab htrans
    have hAbot : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hA
      omega
    have hdvd := Lift.card_sub_one_dvd_card_imgIn A hAbot hXtrans
    rw [hA] at hdvd
    have h255 : 255 ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 := hdvd.trans hIα
    norm_num at h255
  ·
    have hinvφ : ∀ r ∈ pCore 2 (Mbar A), rhoHom A x r ∈ pCore 2 (Mbar A) :=
      fun r hr => rhoHom_mem_pCore A x hr
    have hinvψ : ∀ r ∈ pCore 2 (Mbar A), rhoHom A t r ∈ pCore 2 (Mbar A) :=
      fun r hr => rhoHom_mem_pCore A t hr
    have hUR : Ubar A U ≤ pCore 2 (Mbar A) :=
      Comp.le_of_invariant hcardAbar hφ5 hψ2 hφψ hφA hψA hfpfbar (Ubar_le_Abar A U) hUfix hUcard
        hRA hinvφ hinvψ hR1
    rcases Comp.card_eq_of_invariant hcardAbar hφ5 hφA hfpfbar hRA hinvφ with h1 | h16 | h256
    · exact absurd (Subgroup.card_eq_one.1 h1) hR1
    · exfalso
      have hRU : pCore 2 (Mbar A) = Ubar A U :=
        (Subgroup.eq_of_le_of_card_ge hUR (by rw [h16, hUcard])).symm
      obtain ⟨h, hsh⟩ := hs
      exact false_of_pCore_eq_Ubar hab hUA hU hx5 htx hxA htA hfpf hCt hsh hsA hv hRU
    · have hRAbar : pCore 2 (Mbar A) = Abar A :=
        Subgroup.eq_of_le_of_card_ge hRA (by rw [h256, hcardAbar])
      exact layer_eq_bot_of_pCore_eq_Abar hab hRAbar

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
