module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm7
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.ClassicalInvolution.Balance.Delta
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Diagonal
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open CFSG.ClassicalInvolution.Balance (deltaCore)

section Theta

variable {G : Type} [Group G]

@[expose] def thetaGA (A : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), pPrimeCoreOf 2 (centralizer ({a} : Set G))

theorem pPrimeCoreOf_le_thetaGA {A : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≤ thetaGA A :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem thetaGA_ne_bot {A : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (h : pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) : thetaGA A ≠ ⊥ := fun hbot =>
  h (le_bot_iff.mp (hbot ▸ pPrimeCoreOf_le_thetaGA ha ha1))

end Theta

section Completion

variable {G : Type} [Group G] [Finite G]

theorem exists_zpowers_of_card_two {S : Subgroup G} (hS : Nat.card ↥S = 2) :
    ∃ a ∈ S, a ≠ 1 ∧ S = zpowers a := by
  have hnt : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnt
  have haS : (a : G) ∈ S := a.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hle : zpowers (a : G) ≤ S := zpowers_le.mpr haS
  have hdvd : Nat.card ↥(zpowers (a : G)) ∣ 2 := hS ▸ Subgroup.card_dvd_of_le hle
  have hne1 : Nat.card ↥(zpowers (a : G)) ≠ 1 := by
    rw [Nat.card_zpowers]
    intro h
    exact ha1' (orderOf_eq_one_iff.mp h)
  have h2 : Nat.card ↥(zpowers (a : G)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  exact ⟨a, haS, ha1', (Subgroup.eq_of_le_of_card_ge hle (by rw [hS, h2])).symm⟩

omit [Finite G] in
theorem centralizer_zpowers_eq (a : G) :
    centralizer ((zpowers a : Subgroup G) : Set G) = centralizer ({a} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem hypB_two_of_coprime (H : Subgroup G) (h : Nat.Coprime 2 (Nat.card ↥H)) :
    CFSG.Open.signalizerMcBrideHypothesisB 2 H := by
  refine ⟨Nat.prime_two, h, fun K L hKH hLK _ hS hnc => ?_⟩
  exfalso
  have hdvd : Nat.card (↥K ⧸ L.subgroupOf K) ∣ Nat.card ↥H :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hKH)
  have hodd : Odd (Nat.card (↥K ⧸ L.subgroupOf K)) :=
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hdvd h)
  have hsolv : Group.IsSolvable (↥K ⧸ L.subgroupOf K) := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem thetaGA_spec_of_elementary {A : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (h8 : 8 ≤ Nat.card ↥A)
    (hbal : IsBalancedWrt A) :
    Nat.Coprime 2 (Nat.card ↥(thetaGA A)) ∧ A ≤ normalizer (thetaGA A : Set G) ∧
      ∀ a ∈ A, a ≠ 1 → thetaGA A ⊓ centralizer ({a} : Set G) =
        pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hAe
  have hAe' : CFSG.Open.IsElemAbelian 2 A :=
    ⟨hAe.toIsMulCommutative,
      fun x hx => by
        simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx⟩
  have hrank : 2 ^ (1 + 2) ≤ Nat.card ↥A := by
    simpa using h8
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hAe' hx hy
  have horder : ∀ a ∈ A, a ≠ 1 → orderOf a = 2 := by
    intro a ha ha1
    exact orderOf_eq_prime (by
      have h := hAe'.2 a ha
      simpa [pow_two] using h) ha1
  have hEk : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 1 A, ∃ a ∈ A, a ≠ 1 ∧ S = zpowers a := by
    intro S hS
    obtain ⟨a, haS, ha1, hSa⟩ := exists_zpowers_of_card_two (by simpa using hS.2)
    exact ⟨a, hS.1 haS, ha1, hSa⟩
  have hEk' : ∀ a ∈ A, a ≠ 1 → zpowers a ∈ CFSG.Open.signalizerFunctorEk 2 1 A := by
    intro a ha ha1
    refine ⟨zpowers_le.mpr ha, ?_⟩
    rw [Nat.card_zpowers, horder a ha ha1, pow_one]
  set Θ : Subgroup G → Subgroup G := fun S => pPrimeCoreOf 2 (centralizer (S : Set G)) with hΘ
  have hΘz : ∀ a : G, Θ (zpowers a) = pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
    intro a
    simp only [hΘ, centralizer_zpowers_eq]
  have hinv : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 1 A, A ≤ normalizer (Θ S : Set G) := by
    intro S hS c hc
    have hcC : c ∈ centralizer (S : Set G) := by
      rw [mem_centralizer_iff]
      intro s hs
      exact (hcomm c hc s (hS.1 hs)).symm
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · exact CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore hcC hg
    · have h1 := CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore
        (Subgroup.inv_mem _ hcC) hg
      rwa [show c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g by group] at h1
  have hbal' : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 1 A, ∀ S' ∈ CFSG.Open.signalizerFunctorEk 2 1 A,
      Θ S ⊓ centralizer (S' : Set G) ≤ Θ S' := by
    intro S hS S' hS'
    obtain ⟨a, ha, ha1, rfl⟩ := hEk S hS
    obtain ⟨b, hb, hb1, rfl⟩ := hEk S' hS'
    rw [hΘz, hΘz, centralizer_zpowers_eq]
    exact (hbal a ha ha1 b hb hb1).le.trans inf_le_right
  have h := CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_two G 1 le_rfl A hAe' hrank Θ
    (fun S _ => pPrimeCoreOf_le_self _) (fun S _ => coprime_card_pPrimeCoreOf _) hinv hbal'
    (fun S _ => hypB_two_of_coprime _ (coprime_card_pPrimeCoreOf _))
  obtain ⟨⟨hcopW, hnormW⟩, hcentW, -, -⟩ := h
  have hW : (⨆ (S : Subgroup G) (_ : S ∈ CFSG.Open.signalizerFunctorEk 2 1 A), Θ S) = thetaGA A := by
    apply le_antisymm
    · refine iSup₂_le fun S hS => ?_
      obtain ⟨a, ha, ha1, rfl⟩ := hEk S hS
      rw [hΘz]
      exact pPrimeCoreOf_le_thetaGA ha ha1
    · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      refine le_iSup₂_of_le (zpowers a) (hEk' a ha ha1) ?_
      rw [hΘz]
  rw [hW] at hcopW hnormW hcentW
  refine ⟨hcopW, hnormW, fun a ha ha1 => ?_⟩
  have := hcentW (zpowers a) (hEk' a ha ha1)
  rwa [hΘz, centralizer_zpowers_eq] at this

theorem thetaGA_spec {A : Subgroup G} (hA : IsEStar A) (hr : 3 ≤ pRank 2 G) (hbal : IsBalancedWrt A) :
    Nat.Coprime 2 (Nat.card ↥(thetaGA A)) ∧ A ≤ normalizer (thetaGA A : Set G) ∧
      ∀ a ∈ A, a ≠ 1 → thetaGA A ⊓ centralizer ({a} : Set G) =
        pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
  have h8 : 8 ≤ Nat.card ↥A := by
    rw [hA.2]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ pRank 2 G := Nat.pow_le_pow_right (by norm_num) hr
  exact thetaGA_spec_of_elementary (A := A) hA.1 h8 hbal

theorem exists_elemAbelian_card_pRank (H : Subgroup G) :
    ∃ A : Subgroup G, A ≤ H ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : CFSG.pRank 2 ↥H ∈
      {r : ℕ | ∃ B : Subgroup ↥H, CFSG.IsElementaryAbelian 2 ↥B ∧ Nat.card ↥B = 2 ^ r} := by
    apply Nat.sSup_mem
    · exact ⟨0, ⊥, isElementaryAbelian_bot, by simp⟩
    · refine ⟨Nat.card ↥H, ?_⟩
      rintro r ⟨B, -, hB⟩
      have h1 : r < 2 ^ r := Nat.lt_pow_self (by norm_num)
      have h2 : Nat.card ↥B ≤ Nat.card ↥H := Subgroup.card_le_card_group B
      omega
  obtain ⟨B, hBe, hBcard⟩ := hmem
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hequiv : ↥B ≃* ↥(B.map H.subtype) := Subgroup.equivMapOfInjective B H.subtype hinj
  refine ⟨B.map H.subtype, Subgroup.map_subtype_le B, ?_, ?_⟩
  · exact isElementaryAbelian_two_of_mulEquiv hequiv hBe
  · rw [← hBcard]
    exact (Nat.card_congr hequiv.toEquiv).symm

theorem exists_isEStar_le {T : Subgroup G} (hT : pRank 2 ↥T = pRank 2 G) :
    ∃ A : Subgroup G, A ≤ T ∧ IsEStar A := by
  obtain ⟨A, hAT, hAe, hAcard⟩ := exists_elemAbelian_card_pRank T
  exact ⟨A, hAT, hAe, by rw [hAcard, hT]⟩

theorem exists_isEStar_of_isStar2 {t : G} (ht : IsStar2 t) : ∃ A : Subgroup G, IsEStar A ∧ t ∈ A := by
  obtain ⟨A, hAT, hA⟩ := exists_isEStar_le (T := centralizer ({t} : Set G)) ht.2
  refine ⟨A, hA, hA.mem_of_commute ht.1 fun a ha => ?_⟩
  exact (mem_centralizer_singleton_iff.mp (hAT ha)).symm

theorem exists_coatom_of_thetaGA {A : Subgroup G} (hG : IsSimpleGroup G) (h2 : 2 ∣ Nat.card G)
    (hcop : Nat.Coprime 2 (Nat.card ↥(thetaGA A))) (hne : thetaGA A ≠ ⊥) :
    ∃ M : Subgroup G, IsCoatom M ∧ normalizer (thetaGA A : Set G) ≤ M := by
  rcases eq_top_or_exists_le_coatom (normalizer (thetaGA A : Set G)) with htop | h
  · exfalso
    have hN : (thetaGA A).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (thetaGA A) with hb | ht
    · exact hne hb
    · rw [ht, Subgroup.card_top] at hcop
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)
  · obtain ⟨M, hM, hle⟩ := h
    exact ⟨M, hM, hle⟩

theorem exists_config_of_thetaGA {A : Subgroup G} (hG : IsSimpleGroup G) (hA : IsEStar A)
    (hr : 3 ≤ pRank 2 G) (hbal : IsBalancedWrt A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hne : pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) :
    ∃ M S : Subgroup G, IsCoatom M ∧ normalizer (thetaGA A : Set G) ≤ M ∧ IsSylowOf 2 S M ∧ A ≤ S := by
  obtain ⟨hcop, hnorm, -⟩ := thetaGA_spec hA hr hbal
  have h2 : 2 ∣ Nat.card G := by
    have h1 : 2 ∣ Nat.card ↥A := by
      rw [hA.2]
      exact dvd_pow_self 2 (by omega)
    exact h1.trans (Subgroup.card_subgroup_dvd_card A)
  obtain ⟨M, hM, hle⟩ := exists_coatom_of_thetaGA hG h2 hcop (thetaGA_ne_bot ha ha1 hne)
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_ge (N := M) (K := A) (hnorm.trans hle) hA.isPGroup
  exact ⟨M, S, hM, hle, hS, hAS⟩

end Completion

end CFSG.GH74.GLS
