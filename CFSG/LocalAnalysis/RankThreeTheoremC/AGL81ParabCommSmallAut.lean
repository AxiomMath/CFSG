module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Quasithin.Background.FFC2Core
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
public import CFSG.GH74.KGroups.L27
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding
open scoped commutatorElement

@[expose] noncomputable def quotAut {A : Type} [Group A] {Y B : Subgroup A}
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) : ↥B →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Y).comp
    (Y.normalizerMonoidHom.comp (Subgroup.inclusion hBY))

theorem quotAut_apply_mk {A : Type} [Group A] {Y B : Subgroup A}
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) (b : ↥B) (y : ↥Y) :
    quotAut hBY b (QuotientGroup.mk' (Subgroup.center ↥Y) y) =
      QuotientGroup.mk' (Subgroup.center ↥Y) (Y.normalizerMonoidHom (Subgroup.inclusion hBY b) y) :=
  CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ _

theorem commutator_centralizes_of_quotAut_comm {A : Type} [Group A] {Y B : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hcomm : ∀ a b : ↥B, quotAut hBY a * quotAut hBY b = quotAut hBY b * quotAut hBY a) :
    ∀ c ∈ ⁅B, B⁆, ∀ y ∈ Y, c * y = y * c := by
  haveI : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.1
  let φ : ↥B →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hBY)
  have hle : ⁅B, B⁆ ≤ (quotAut hBY).ker.map B.subtype := by
    rw [Subgroup.commutator_le]
    intro b₁ h₁ b₂ h₂
    refine ⟨⁅(⟨b₁, h₁⟩ : ↥B), (⟨b₂, h₂⟩ : ↥B)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  intro c hc y hy
  obtain ⟨k, hk, rfl⟩ := hle hc
  have hφ : φ k = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥Y
      (by rw [map_one]; exact hk)
  have h1 := Y.normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hBY k) ⟨y, hy⟩
  change ((φ k ⟨y, hy⟩ : ↥Y) : A) = _ at h1
  rw [hφ] at h1
  change y = (k : A) * y * (k : A)⁻¹ at h1
  calc (k : A) * y = (k : A) * y * (k : A)⁻¹ * k := by group
    _ = y * k := by rw [← h1]

theorem parabCommGroupOn_of_aut {𝔉 : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], 𝔉 X → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ S : Subgroup (MulAut X), IsPGroup p ↥S → ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ParabCommGroupOn 𝔉 := by
  intro A _ _ Y P B p hp hp2 hY _ hF _ _ _ hB hBY _ _
  left
  have hS : IsPGroup p ↥(quotAut hBY).range :=
    hB.of_surjective (quotAut hBY).rangeRestrict (quotAut hBY).rangeRestrict_surjective
  have hcomm := h _ hF p hp hp2 _ hS
  exact commutator_centralizes_of_quotAut_comm hY hBY fun a b =>
    hcomm _ ⟨a, rfl⟩ _ ⟨b, rfl⟩

theorem isPGroup_commutative_of_dvd {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {S : Subgroup G} (hS : IsPGroup p ↥S) (h3 : ¬ p ^ 3 ∣ Nat.card G) :
    ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card S
  have hk2 : k ≤ 2 := by
    by_contra hk3
    exact h3 ((pow_dvd_pow p (by omega)).trans hdvd)
  have hcomm : ∀ x y : ↥S, x * y = y * x := by
    interval_cases k
    · intro x y
      haveI : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact Subsingleton.elim _ _
    · haveI : IsCyclic ↥S := isCyclic_of_prime_card (by simpa using hk)
      exact fun x y => mul_comm' x y
    · exact IsPGroup.commutative_of_card_eq_prime_sq hk
  intro a ha b hb
  exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)

theorem card_mulAut_alternatingGroup {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Nat.card (MulAut ↥(alternatingGroup (Fin n))) = Nat.factorial n := by
  have hle := CFSG.Quasithin.FFC.card_mulAut_alternating_le hn
  have hn4 : 4 ≤ n := by omega
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hdvd := Subgroup.card_dvd_of_injective _
    (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn4)
  rw [Nat.card_perm, Nat.card_fin] at hdvd
  have hA : 2 * Nat.card ↥(alternatingGroup (Fin n)) = Nat.factorial n := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    have h2 : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  rw [hA] at hle
  have hpos : 0 < Nat.card (MulAut ↥(alternatingGroup (Fin n))) := Nat.card_pos
  exact le_antisymm hle (Nat.le_of_dvd hpos hdvd)

theorem false_of_pow_three_dvd {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm0 : 0 < m)
    (hm : ∀ q : ℕ, 3 ≤ q → q ^ 3 ≤ m → ¬ q ^ 3 ∣ m) (h : p ^ 3 ∣ 2 ^ k * m) : False := by
  have hcop : Nat.Coprime (p ^ 3) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h' : p ^ 3 ∣ m := hcop.dvd_of_dvd_mul_left h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  exact hm p hp3 (Nat.le_of_dvd hm0 h') h'

theorem not_cube_dvd_small {m : ℕ} (hm : m = 15 ∨ m = 45 ∨ m = 315 ∨ m = 21) :
    ∀ q : ℕ, 3 ≤ q → q ^ 3 ≤ m → ¬ q ^ 3 ∣ m := by
  intro q hq hqm hdvd
  have hq6 : q ≤ 6 := by
    by_contra h
    have : 7 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  rcases hm with rfl | rfl | rfl | rfl <;> interval_cases q <;> omega

theorem parabCommGroupOn_alternating :
    ParabCommGroupOn fun X _ => ∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
      Nonempty (X ≃* alternatingGroup (Fin n)) := by
  refine parabCommGroupOn_of_aut fun X _ _ ⟨n, hn, ⟨e⟩⟩ p hp hp2 S hS => ?_
  refine isPGroup_commutative_of_dvd hp hS ?_
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  intro h3
  rcases hn with rfl | rfl | rfl
  · rw [card_mulAut_alternatingGroup (Or.inl rfl),
      show Nat.factorial 5 = 2 ^ 3 * 15 by decide] at h3
    exact false_of_pow_three_dvd hp hp2 (by norm_num) (not_cube_dvd_small (Or.inl rfl)) h3
  · rcases CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.card_mulAut_six with h | h <;>
      rw [h] at h3
    · rw [show (720 : ℕ) = 2 ^ 4 * 45 by norm_num] at h3
      exact false_of_pow_three_dvd hp hp2 (by norm_num)
        (not_cube_dvd_small (Or.inr (Or.inl rfl))) h3
    · rw [show (1440 : ℕ) = 2 ^ 5 * 45 by norm_num] at h3
      exact false_of_pow_three_dvd hp hp2 (by norm_num)
        (not_cube_dvd_small (Or.inr (Or.inl rfl))) h3
  · rw [card_mulAut_alternatingGroup (Or.inr (by norm_num : 7 ≤ 8)),
      show Nat.factorial 8 = 2 ^ 7 * 315 by decide] at h3
    exact false_of_pow_three_dvd hp hp2 (by norm_num)
      (not_cube_dvd_small (Or.inr (Or.inr (Or.inl rfl)))) h3

theorem parabCommGroupOn_psl27 :
    ParabCommGroupOn fun X _ => ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  refine parabCommGroupOn_of_aut fun X _ _ ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ p hp hp2 S hS => ?_
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hpq, hf] at h
  obtain ⟨e₇⟩ := CFSG.GH74.KGroups.L27.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  refine isPGroup_commutative_of_dvd hp hS ?_
  rw [CFSG.GH74.KGroups.L27.card_mulAut e₇, show (336 : ℕ) = 2 ^ 4 * 21 by norm_num]
  exact false_of_pow_three_dvd hp hp2 (by norm_num)
    (not_cube_dvd_small (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
