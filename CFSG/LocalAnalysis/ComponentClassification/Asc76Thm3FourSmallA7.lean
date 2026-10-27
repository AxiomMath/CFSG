module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsA7Core
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourSmallL2
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

theorem eq_one_of_card_support_le_two {ρ : Perm (Fin 7)} (hρ : Perm.sign ρ = 1)
    (h : ρ.support.card ≤ 2) : ρ = 1 := by
  have h1 := ρ.card_support_ne_one
  rcases (by omega : ρ.support.card = 0 ∨ ρ.support.card = 2) with h0 | h2
  · exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)
  · rw [(Perm.card_support_eq_two.mp h2).sign_eq] at hρ
    exact absurd hρ (by decide)

theorem eq_one_of_fixed {O : Finset (Fin 7)} (hO : O.card = 3) {τ : Perm (Fin 7)}
    (hτ2 : τ * τ = 1) (hτ : Perm.sign τ = 1) (hτO : ∀ o ∈ O, τ o = o) {q : Fin 7} (hq : q ∉ O)
    (hτq : τ q = q) : τ = 1 := by
  by_contra hτ1
  have h4 := card_support_of_even_involution ((pow_two τ).trans hτ2) hτ1 hτ
  have hsub : τ.support ⊆ (insert q O)ᶜ := fun x hx => by
    rw [Perm.mem_support] at hx
    rw [Finset.mem_compl, Finset.mem_insert, not_or]
    exact ⟨fun h => hx (by rw [h]; exact hτq), fun h => hx (hτO x h)⟩
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hq, hO, h4] at h5
  omega

theorem perm_eq_of_apply_eq {O : Finset (Fin 7)} (hO : O.card = 3) {τ τ' : Perm (Fin 7)}
    (hτ2 : τ * τ = 1) (hτ'2 : τ' * τ' = 1) (hτ : Perm.sign τ = 1) (hτ' : Perm.sign τ' = 1)
    (hτO : ∀ o ∈ O, τ o = o) (hτ'O : ∀ o ∈ O, τ' o = o) {q : Fin 7} (hq : q ∉ O)
    (h : τ q = τ' q) : τ = τ' := by
  by_cases hτq : τ q = q
  · rw [eq_one_of_fixed hO hτ2 hτ hτO hq hτq,
      eq_one_of_fixed hO hτ'2 hτ' hτ'O hq (h.symm.trans hτq)]
  have hτa : τ (τ q) = q := by rw [← Perm.mul_apply, hτ2, Perm.one_apply]
  have haO : τ q ∉ O := fun haO => hτq (by
    calc τ q = τ (τ q) := (hτO _ haO).symm
      _ = q := hτa)
  have hρq : (τ' * τ) q = q := by rw [Perm.mul_apply, h, ← Perm.mul_apply, hτ'2, Perm.one_apply]
  have hρa : (τ' * τ) (τ q) = τ q := by rw [Perm.mul_apply, hτa, h]
  have hsub : (τ' * τ).support ⊆ (insert (τ q) (insert q O))ᶜ := fun x hx => by
    rw [Perm.mem_support] at hx
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_insert, not_or, not_or]
    refine ⟨fun e => hx (by rw [e]; exact hρa), fun e => hx (by rw [e]; exact hρq),
      fun hxO => hx ?_⟩
    rw [Perm.mul_apply, hτO x hxO, hτ'O x hxO]
  have hcard := Finset.card_le_card hsub
  have hnot : τ q ∉ insert q O := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hτq, haO⟩
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hnot,
    Finset.card_insert_of_notMem hq, hO] at hcard
  have hρ := eq_one_of_card_support_le_two (ρ := τ' * τ) (by rw [map_mul, hτ, hτ', one_mul])
    (by omega)
  rw [eq_inv_of_mul_eq_one_left hρ, inv_eq_of_mul_eq_one_right hτ2]

variable {X : Type} [Group X] [Finite X]

theorem local_of_alt7 (e : X ≃* alternatingGroup (Fin 7)) (K R : Subgroup X)
    (hK : TightlyEmbedded K) (hKn : ¬ K.Normal) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (h4 : Nat.card R = 4) :
    (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (K : Set X) with hHdef
  have hHtop : H ≠ ⊤ := fun h => hKn (normalizer_eq_top_iff.mp h)
  have hRK : R ≤ K := hR.le
  have hKH : K ≤ H := le_normalizer
  have hRH : R ≤ H := hRK.trans hKH
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hsq : ∀ r ∈ R, r * r = 1 := fun r hr => by
    rw [← pow_two]
    exact hRe.2 r hr
  set σ : X →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom with hσdef
  have hσinj : Function.Injective σ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp e.injective
  have hσsign : ∀ x, Perm.sign (σ x) = 1 := fun x => Perm.mem_alternatingGroup.mp (e x).2
  have hσsurj : ∀ g : Perm (Fin 7), Perm.sign g = 1 → ∃ x, σ x = g := fun g hg =>
    ⟨e.symm ⟨g, Perm.mem_alternatingGroup.mpr hg⟩, by simp [hσdef]⟩
  have hσsq : ∀ x : X, x * x = 1 → σ x * σ x = 1 := fun x hx => by
    rw [← map_mul, hx, map_one]
  have hCH : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set X) ≤ H := fun r hr hr1 =>
    CFSG.ComponentClassification.Asc75T4.centralizer_le_of_involution hK (hRK hr)
      (orderOf_eq_prime (hRe.2 r hr) hr1)
  have hFixCard : ∀ r ∈ R, r ≠ 1 → (σ r).supportᶜ.card = 3 := fun r hr hr1 => by
    have h1 : σ r ≠ 1 := fun h => hr1 (hσinj (h.trans (map_one σ).symm))
    rw [Finset.card_compl, Fintype.card_fin,
      card_support_of_even_involution ((pow_two _).trans (hσsq r (hsq r hr))) h1 (hσsign r)]
  have hmemFix : ∀ (g : Perm (Fin 7)) (a : Fin 7), a ∈ g.supportᶜ ↔ g a = a := fun g a => by
    rw [Finset.mem_compl, Perm.notMem_support]
  obtain ⟨p, hp⟩ : ∃ p : Fin 7, ∀ r ∈ R, σ r p = p := by
    let inst : MulAction R (Fin 7) := MulAction.compHom (Fin 7) (σ.comp R.subtype)
    have hmod := hR2.card_modEq_card_fixedPoints (Fin 7)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hmod
    have hpos : Nat.card (MulAction.fixedPoints R (Fin 7)) ≠ 0 := by
      intro h0
      rw [h0] at hmod
      exact absurd hmod (by decide)
    obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp hpos).1
    exact ⟨p, fun r hr => hp ⟨r, hr⟩⟩
  have h3c : ∀ r ∈ R, r ≠ 1 → ∀ a, σ r a = a → a ≠ p →
      ∃ y ∈ H, σ y p = a ∧ (σ y).IsThreeCycle := by
    intro r hr hr1 a ha hap
    obtain ⟨b, hb, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {p, a}) (t := (σ r).supportᶜ)
      (by rw [hFixCard r hr hr1]; exact Finset.card_le_two.trans_lt (by norm_num))
    rw [hmemFix] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb'
    have hc3 : (swap p b * swap p a).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hb'.1) (Ne.symm hap) hb'.2
    obtain ⟨y, hy⟩ := hσsurj _ (Perm.mem_alternatingGroup.mp (threeCycle_mem_alternating hc3))
    have hyC : y ∈ centralizer ({r} : Set X) := by
      rw [mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm]
      apply hσinj
      rw [map_mul, map_mul, hy]
      exact commute_threeCycle_of_fixed (hp r hr) hb ha
    refine ⟨y, hCH r hr hr1 hyC, ?_, by rw [hy]; exact hc3⟩
    rw [hy, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hap (Ne.symm hb'.2)]
  set O : Finset (Fin 7) := Finset.univ.filter fun z => ∃ h ∈ H, σ h p = z with hOdef
  have hmemO : ∀ z, z ∈ O ↔ ∃ h ∈ H, σ h p = z := fun z => by
    rw [hOdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ z, h⟩⟩
  have hOinv : ∀ g ∈ H, ∀ z, σ g z ∈ O ↔ z ∈ O := by
    intro g hg z
    rw [hmemO, hmemO]
    constructor
    · rintro ⟨h, hh, hz⟩
      refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_⟩
      rw [map_mul, Perm.mul_apply, hz, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Perm.one_apply]
    · rintro ⟨h, hh, rfl⟩
      exact ⟨g * h, mul_mem hg hh, by rw [map_mul, Perm.mul_apply]⟩
  have hFixO : ∀ r ∈ R, r ≠ 1 → ∀ a, σ r a = a → a ∈ O := by
    intro r hr hr1 a ha
    rw [hmemO]
    by_cases hap : a = p
    · exact ⟨1, one_mem H, by rw [map_one, Perm.one_apply, hap]⟩
    · obtain ⟨y, hyH, hya, -⟩ := h3c r hr hr1 a ha hap
      exact ⟨y, hyH, hya⟩
  obtain ⟨r₁, hr₁, hr₁1, -⟩ := exists_mem_ne_ne' (T := R) (by omega) 1 1
  obtain ⟨a, ha, hap⟩ : ∃ a, σ r₁ a = a ∧ a ≠ p := by
    obtain ⟨a, ha, ha'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {p}) (t := (σ r₁).supportᶜ)
      (by rw [hFixCard r₁ hr₁ hr₁1, Finset.card_singleton]; norm_num)
    exact ⟨a, (hmemFix _ a).mp ha, Finset.notMem_singleton.mp ha'⟩
  obtain ⟨y, hyH, -, hy3⟩ := h3c r₁ hr₁ hr₁1 a ha hap
  obtain ⟨q, hq⟩ : ∃ q, q ∉ O := by
    by_contra hall
    have hall' : ∀ z, z ∈ O := fun z => by
      by_contra hz
      exact hall ⟨z, hz⟩
    apply hHtop
    have hA : alternatingGroup (Fin 7) ≤ H.map σ :=
      alternating_le_of_transitive_of_threeCycle (H.map σ) p (fun z => by
        obtain ⟨h, hh, hz⟩ := (hmemO z).mp (hall' z)
        exact ⟨σ h, ⟨h, hh, rfl⟩, hz⟩) hy3 ⟨y, hyH, rfl⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh, hhx⟩ := hA (Perm.mem_alternatingGroup.mpr (hσsign x))
    rw [← hσinj hhx]
    exact hh
  have hfix1 : ∀ r ∈ R, ∀ z, z ∉ O → σ r z = z → r = 1 := fun r hr z hz hrz => by
    by_contra hr1
    exact hz (hFixO r hr hr1 z hrz)
  let f : R → (Oᶜ : Finset (Fin 7)) := fun r =>
    ⟨σ r q, Finset.mem_compl.mpr fun h => hq ((hOinv r (hRH r.2) q).mp h)⟩
  have hf : Function.Injective f := by
    intro r r' hrr
    have h1 : σ r q = σ r' q := congrArg Subtype.val hrr
    have h2 : (r' : X)⁻¹ * r = 1 := hfix1 _ (mul_mem (inv_mem r'.2) r.2) q hq (by
      rw [map_mul, map_inv, Perm.mul_apply, h1, ← Perm.mul_apply, inv_mul_cancel,
        Perm.one_apply])
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  have hcardOc : Nat.card (Oᶜ : Finset (Fin 7)) = 7 - O.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hO3 : O.card ≤ 3 := by
    have h1 := Nat.card_le_card_of_injective f hf
    rw [h4, hcardOc] at h1
    omega
  have hOeq : ∀ r ∈ R, r ≠ 1 → (σ r).supportᶜ = O := fun r hr hr1 =>
    Finset.eq_of_subset_of_card_le (fun a ha => hFixO r hr hr1 a ((hmemFix _ a).mp ha))
      (by rw [hFixCard r hr hr1]; exact hO3)
  have hOcard : O.card = 3 := by rw [← hOeq r₁ hr₁ hr₁1, hFixCard r₁ hr₁ hr₁1]
  have hRO : ∀ r ∈ R, ∀ o ∈ O, σ r o = o := fun r hr o ho => by
    by_cases hr1 : r = 1
    · rw [hr1, map_one, Perm.one_apply]
    · rw [← hOeq r hr hr1, hmemFix] at ho
      exact ho
  have hbij := hf.bijective_of_nat_card_le (by rw [h4, hcardOc, hOcard])
  have hRn : H ≤ normalizer (R : Set X) := le_normalizer_of_conj fun h hh r hr => by
    have hr'H : h * r * h⁻¹ ∈ H := mul_mem (mul_mem hh (hRH hr)) (inv_mem hh)
    have hr'O : ∀ o ∈ O, σ (h * r * h⁻¹) o = o := fun o ho => by
      have h1 : σ h⁻¹ o ∈ O := (hOinv h⁻¹ (inv_mem hh) o).mpr ho
      rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, hRO r hr _ h1, ← Perm.mul_apply,
        ← map_mul, mul_inv_cancel, map_one, Perm.one_apply]
    have hr'2 : h * r * h⁻¹ * (h * r * h⁻¹) = 1 := by
      calc h * r * h⁻¹ * (h * r * h⁻¹) = h * (r * r) * h⁻¹ := by group
        _ = 1 := by rw [hsq r hr]; group
    obtain ⟨s, hs⟩ := hbij.2 ⟨σ (h * r * h⁻¹) q,
      Finset.mem_compl.mpr fun h' => hq ((hOinv _ hr'H q).mp h')⟩
    have hs' : σ s q = σ (h * r * h⁻¹) q := congrArg Subtype.val hs
    have heq := perm_eq_of_apply_eq hOcard (hσsq s (hsq s s.2)) (hσsq _ hr'2) (hσsign s)
      (hσsign _) (hRO s s.2) hr'O hq hs'
    rw [← hσinj heq]
    exact s.2
  refine ⟨(normal_subgroupOf_iff_le_normalizer hRK).mpr (hKH.trans hRn), ?_⟩
  have hnot : ∀ h ∈ H, ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → orderOf h ≠ ℓ := by
    intro h hh ℓ hℓ hℓ5 hord
    have hord' : orderOf (σ h) = ℓ := by rw [orderOf_injective σ hσinj h, hord]
    have hcyc : (σ h).IsCycle := Perm.isCycle_of_prime_order' (by rw [hord']; exact hℓ)
      (by rw [Fintype.card_fin, hord']; omega)
    have hsupp : (σ h).support.card = ℓ := by rw [← hcyc.orderOf, hord']
    obtain ⟨x, hx⟩ : (σ h).support.Nonempty := Finset.card_pos.mp (by omega)
    have hall : ∀ y ∈ (σ h).support, y ∈ O ↔ x ∈ O := by
      intro y hy
      obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Perm.mem_support.mp hx) (Perm.mem_support.mp hy)
      rw [← hi, ← map_pow]
      exact hOinv _ (pow_mem hh i) x
    by_cases hxO : x ∈ O
    · have h1 := Finset.card_le_card (s := (σ h).support) (t := O) fun y hy =>
        (hall y hy).mpr hxO
      omega
    · have h1 := Finset.card_le_card (s := (σ h).support) (t := Oᶜ) fun y hy =>
        Finset.mem_compl.mpr fun hyO => hxO ((hall y hy).mp hyO)
      rw [Finset.card_compl, Fintype.card_fin, hOcard] at h1
      omega
  have hdvd5 : ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ¬ ℓ ∣ Nat.card H := fun ℓ hℓ hℓ5 hdvd => by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
    exact hnot x x.2 ℓ hℓ hℓ5 (by rw [Subgroup.orderOf_coe, hx])
  have hX : Nat.card X = 2 ^ 3 * 3 ^ 2 * (5 * 7) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hcop : Nat.Coprime (Nat.card H) (5 * 7) :=
    Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (hdvd5 5 (by norm_num) le_rfl)).symm
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
        (hdvd5 7 (by norm_num) (by norm_num))).symm
  have hdvdX : Nat.card H ∣ 2 ^ 3 * 3 ^ 2 * (5 * 7) := by
    rw [← hX]
    exact card_subgroup_dvd_card H
  obtain ⟨k₁, k₂, h1, h2, hk⟩ := Nat.dvd_mul.mp (hcop.dvd_of_dvd_mul_right hdvdX)
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨n, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  exact isSolvable_of_card_two_three hk.symm

end CFSG.ComponentClassification.Asc76X.Thm3Four
