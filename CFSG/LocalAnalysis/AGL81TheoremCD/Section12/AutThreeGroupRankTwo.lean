module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.AutThreeGroupSmall
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup

private theorem mulAut_eq_one_of_card_frattini_le_nine {D : Type} [Group D] [Finite D]
    (hD : IsPGroup 3 D) (hsmall : Nat.card (D ⧸ frattini D) ≤ 9) {d : ℕ} (hd : d.Prime)
    (hd5 : 5 ≤ d) {β : MulAut D} {k : ℕ} (hβ : β ^ d ^ k = 1) : β = 1 := by
  by_contra hne
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hd).1 (orderOf_dvd_of_pow_eq_one hβ)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hi
    exact hne (orderOf_eq_one_iff.1 hi)
  have hdvd : d ∣ orderOf β := by
    rw [hi]
    exact dvd_pow_self d hi0
  exact (not_dvd_card_mulAut_of_five_le hD hsmall hd hd5) (hdvd.trans (orderOf_dvd_natCard β))

theorem mulAut_eq_one_of_pRank_le_two {P : Type} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup P) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    {α : MulAut P} {k : ℕ} (hα : α ^ d ^ k = 1) : α = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hnt : Nontrivial P
  · have := hnt
    obtain ⟨D, hDc, -, -, hDexp, hDfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by norm_num) hP
    have := hDc
    have hDp : IsPGroup 3 D := hP.to_subgroup D
    have hDexp' : ∀ x : D, x ^ 3 = 1 := fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
    have hDrank : CFSG.Open.pRank 3 (⊤ : Subgroup D) ≤ 2 :=
      (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) D.subtype
        D.subtype_injective).trans h2
    have hDsmall : Nat.card (D ⧸ frattini D) ≤ 9 := by
      have h := (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDp hDexp'
        hDrank).2
      simpa using h
    let β : MulAut D := MulAut.characteristic D α
    have hβ : β ^ d ^ k = 1 := by
      change (MulAut.characteristic D α) ^ d ^ k = 1
      rw [← map_pow, hα, map_one]
    have hβ1 : β = 1 := mulAut_eq_one_of_card_frattini_le_nine hDp hDsmall hd hd5 hβ
    have hmem : α ∈ fixingSubgroup (MulAut P) (D : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      have h := congrArg (fun γ : MulAut D => ((γ ⟨x, hx⟩ : D) : P)) hβ1
      simpa [β, MulAut.characteristic_apply_apply_coe] using h
    obtain ⟨n, hn⟩ := hDfix ⟨α, hmem⟩
    have hα3 : α ^ 3 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have h2dvd : orderOf α ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hα3
    have h1dvd : orderOf α ∣ d ^ k := orderOf_dvd_of_pow_eq_one hα
    have h3d : Nat.Coprime 3 d :=
      (Nat.coprime_primes Nat.prime_three hd).2 (by omega)
    have hcop : Nat.gcd (3 ^ n) (d ^ k) = 1 :=
      (h3d.pow_left n).pow_right k
    have hdiv : orderOf α ∣ Nat.gcd (3 ^ n) (d ^ k) := Nat.dvd_gcd h2dvd h1dvd
    rw [hcop] at hdiv
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdiv)
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact MulEquiv.ext fun x => Subsingleton.elim _ _

theorem le_centralizer_of_le_normalizer_of_pRank_le_two {X : Type} [Group X] [Finite X]
    {W B : Subgroup X} (hW : IsPGroup 3 W) (h2 : CFSG.Open.pRank 3 W ≤ 2) {d : ℕ}
    (hd : d.Prime) (hd5 : 5 ≤ d) (hB : IsPGroup d B)
    (hBW : B ≤ Subgroup.normalizer (W : Set X)) :
    B ≤ Subgroup.centralizer (W : Set X) := by
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (W : Set X) := hBW hb
  let g : ↥(Subgroup.normalizer (W : Set X)) := ⟨b, hbN⟩
  obtain ⟨n, hn⟩ := hB (⟨b, hb⟩ : ↥B)
  have hgpow : g ^ d ^ n = 1 := by
    apply Subtype.ext
    simpa [g] using congrArg Subtype.val hn
  have hαpow : W.normalizerMonoidHom g ^ d ^ n = 1 := by
    rw [← map_pow, hgpow, map_one]
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) W]
    exact h2
  have hα1 : W.normalizerMonoidHom g = 1 :=
    mulAut_eq_one_of_pRank_le_two hW hrk hd hd5 hαpow
  have hker : g ∈ W.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact hα1
  rw [W.normalizerMonoidHom_ker] at hker
  rw [Subgroup.mem_subgroupOf] at hker
  simpa [g] using hker

theorem exists_map_conj_le_normalizer_of_isSylowOf {X : Type} [Group X] [Finite X]
    {K B W : Subgroup X} {d : ℕ} (hd : d.Prime) (hB : IsPGroup d B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hK : ¬ d ∣ Nat.card K)
    (hW : CFSG.ABGLocalTools.IsSylowOf 3 W K) :
    ∃ k ∈ K, B.map (MulAut.conj k).toMonoidHom ≤ Subgroup.normalizer (W : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hBR⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime hd Nat.prime_three hB hBK hK
  obtain ⟨k, hkK, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hW hR
  refine ⟨k⁻¹, K.inv_mem hkK, ?_⟩
  have hmap : R.map (MulAut.conj k⁻¹).toMonoidHom = W := by
    ext x
    rw [Subgroup.mem_map_equiv]
    have h := hconj (k * x * k⁻¹)
    rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h
    simpa [MulAut.conj_symm_apply] using h
  have hnorm : (Subgroup.normalizer (R : Set X)).map (MulAut.conj k⁻¹).toMonoidHom =
      Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq, hmap]
  calc B.map (MulAut.conj k⁻¹).toMonoidHom
      ≤ (Subgroup.normalizer (R : Set X)).map (MulAut.conj k⁻¹).toMonoidHom :=
        Subgroup.map_mono hBR
    _ = Subgroup.normalizer (W : Set X) := hnorm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
