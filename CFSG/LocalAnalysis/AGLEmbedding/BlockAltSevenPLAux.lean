module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7PrimeOrderCentralizer
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.AGLEmbedding.BlockAltSevenPL

open Equiv

theorem card_map_eq_card_map_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C]
    {f : A →* B} {g : A →* C} (h : f.ker = g.ker) (X : Subgroup A) :
    Nat.card (X.map f) = Nat.card (X.map g) := by
  rw [← MonoidHom.domRestrict_range, ← MonoidHom.domRestrict_range,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.domRestrict X)).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (g.domRestrict X)).toEquiv,
    MonoidHom.ker_domRestrict, MonoidHom.ker_domRestrict, h]

theorem nonempty_mulEquiv_range_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C]
    {f : A →* B} {g : A →* C} (h : f.ker = g.ker) : Nonempty (f.range ≃* g.range) :=
  ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange g))⟩

theorem card_mulAut_eq_and_isSimpleGroup {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4) :
    Nat.card (MulAut W) = 20160 ∧ IsSimpleGroup (MulAut W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq hcard
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (GL (Fin 4) (ZMod 2)) :=
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm.isSimpleGroup
  exact ⟨by rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.GH74.Exceptional.card_GL_four_two],
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).isSimpleGroup⟩

theorem mem_of_mem_normalizer_of_index_eight {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (hΓ : Nat.card Γ = 20160) {H : Subgroup Γ} (hH : Nat.card H = 2520) {γ : Γ}
    (hγ : γ ∈ Subgroup.normalizer (H : Set Γ)) : γ ∈ H := by
  set N := Subgroup.normalizer (H : Set Γ)
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hNi := N.card_mul_index
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hHN
  rw [hH] at hr
  rw [hΓ, hr] at hNi
  have hk : N.index * r = 8 := by nlinarith
  obtain ⟨m, hm, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (⟨r, hk.symm⟩ : N.index ∣ 2 ^ 3)
  have hsmall : N ≠ ⊤ → N.index ≤ 4 → False := fun hne h4 => by
    have : N.normalCore.Normal := N.normalCore_normal
    have hcore : N.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with h | h
      · exact h
      · exact absurd (eq_top_iff.mpr (h ▸ N.normalCore_le)) hne
    have h1 := N.index_normalCore_dvd_factorial_index
    rw [hcore, Subgroup.index_bot, hΓ] at h1
    have h2 : N.index.factorial ≤ 24 := (Nat.factorial_le h4).trans (by decide)
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos _) h1) (by omega)
  interval_cases m
  · exfalso
    have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp hi)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · rw [h, Subgroup.card_bot] at hH
      omega
    · rw [h, Subgroup.card_top, hΓ] at hH
      omega
  · exact (hsmall (fun h => by rw [h, Subgroup.index_top] at hi; omega) (by omega)).elim
  · exact (hsmall (fun h => by rw [h, Subgroup.index_top] at hi; omega) (by omega)).elim
  · have hr1 : r = 1 := by
      rw [hi] at hk
      omega
    have hcard : Nat.card N ≤ Nat.card H := by rw [hr, hr1, hH]
    rw [Subgroup.eq_of_le_of_card_ge hHN hcard]
    exact hγ

theorem eq_bot_of_orderOf_eq_five {T : Subgroup (alternatingGroup (Fin 7))} (hT : IsPGroup 2 T)
    {x : alternatingGroup (Fin 7)} (hx : orderOf x = 5)
    (hxT : x ∈ Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) : T = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hC : T ⊓ Subgroup.centralizer {x} = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.mp (hT.to_le (inf_le_left (b := Subgroup.centralizer {x})))
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne ((Subgroup.eq_bot_iff_card _).mpr (by simpa using hn))
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T ⊓ Subgroup.centralizer {x})) 2
      (by rw [hn]; exact dvd_pow_self 2 hn0)
    rw [← Subgroup.orderOf_coe] at hy
    have hy1 : (y : alternatingGroup (Fin 7)) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hy
      exact absurd hy (by decide)
    refine CFSG.GorensteinWalter.aSeven_no_involution_centralizes_oddP_five_seven (p := 5)
      (by decide) (Or.inl rfl) (Subgroup.zpowers x)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])) (fun h => ?_)
      (t := (y : alternatingGroup (Fin 7))) ⟨hy1, by rw [← hy]; exact pow_orderOf_eq_one _⟩ ?_
    · rw [Subgroup.zpowers_eq_bot] at h
      rw [h, orderOf_one] at hx
      exact absurd hx (by decide)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp y.2.2).symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  have hn3 : n ≤ 3 := by
    have h := Subgroup.card_subgroup_dvd_card T
    rw [hn, nat_card_alternatingGroup, Nat.card_fin] at h
    by_contra hlt
    exact absurd ((pow_dvd_pow 2 (by omega : 4 ≤ n)).trans h) (by decide)
  by_contra hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne ((Subgroup.eq_bot_iff_card _).mpr (by simpa using hn))
  let f : Perm ↥T := MulAut.toPerm _ (T.normalizerMonoidHom ⟨x, hxT⟩)
  have hf : ∀ t : ↥T, f t ≠ 1 ↔ t ≠ 1 := fun t => by
    show ¬ (T.normalizerMonoidHom ⟨x, hxT⟩) t = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
  have hf5 : f ^ 5 = 1 := by
    have h5 : (⟨x, hxT⟩ : ↥(Subgroup.normalizer (T : Set (alternatingGroup (Fin 7))))) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]; rfl)
    simp only [f, ← map_pow, h5, map_one]
  have hσ : f.subtypePerm (p := fun t : ↥T => t ≠ 1) hf ^ 5 ^ 1 = 1 := by
    rw [pow_one, Perm.subtypePerm_pow]
    simp only [hf5]
    exact Perm.subtypePerm_one _ _
  have hcard : ¬ 5 ∣ Fintype.card {t : ↥T // t ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hn]
    rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl <;> decide
  obtain ⟨⟨t, ht⟩, hfix⟩ := Perm.exists_fixed_point_of_prime hcard hσ
  have htx : (t : alternatingGroup (Fin 7)) ∈ T ⊓ Subgroup.centralizer {x} := by
    refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg (fun s : {t : ↥T // t ≠ 1} => ((s : ↥T) : alternatingGroup (Fin 7))) hfix
    change x * (t : alternatingGroup (Fin 7)) * x⁻¹ = t at h1
    conv_lhs => rw [← h1]
    group
  rw [hC] at htx
  exact ht (Subtype.ext htx)

theorem eq_bot_of_orderOf_eq_seven {T : Subgroup (alternatingGroup (Fin 7))} (hT : IsPGroup 2 T)
    {x : alternatingGroup (Fin 7)} (hx : orderOf x = 7)
    (hxT : x ∈ Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) : T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : Perm (Fin 7) := (x : Perm (Fin 7)) with hσdef
  have hσ : orderOf σ = 7 := by rw [hσdef, Subgroup.orderOf_coe, hx]
  have hcyc : σ.IsCycle := Perm.isCycle_of_prime_order (by rw [hσ]; decide)
    (by rw [hσ]; exact lt_of_le_of_lt (Finset.card_le_univ _) (by simp))
  have hsupp : ∀ j : Fin 7, σ j ≠ j := by
    intro j
    rw [← Perm.mem_support]
    have h7 : σ.support.card = Fintype.card (Fin 7) := by
      rw [← hcyc.orderOf, hσ, Fintype.card_fin]
    rw [Finset.eq_univ_of_card σ.support h7]
    exact Finset.mem_univ j
  obtain ⟨i, hi⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card (Fin 7) (by simp)
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Equiv.ext
  intro j
  obtain ⟨k, hk⟩ := hcyc.exists_pow_eq (hsupp i) (hsupp j)
  have hkT : (x ^ k)⁻¹ * t * ((x ^ k)⁻¹)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxT k)) t).mp ht
  have hfix := hi ⟨_, hkT⟩
  rw [Subgroup.smul_def, Subgroup.smul_def] at hfix
  change ((((x ^ k)⁻¹ * t * ((x ^ k)⁻¹)⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))) i = i
    at hfix
  simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Perm.mul_apply,
    ← hσdef] at hfix
  rw [← hk]
  simpa using congrArg (σ ^ k) hfix

theorem card_dvd_seventyTwo_of_le_normalizer {T P : Subgroup (alternatingGroup (Fin 7))}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hP : P ≤ Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) : Nat.card P ∣ 72 := by
  have hp : ∀ p : ℕ, p.Prime → (p = 5 ∨ p = 7) → ¬ p ∣ Nat.card P := by
    intro p hp hp57 hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p hdvd
    rw [← Subgroup.orderOf_coe] at hx
    rcases hp57 with rfl | rfl
    · exact hT1 (eq_bot_of_orderOf_eq_five hT hx (hP x.2))
    · exact hT1 (eq_bot_of_orderOf_eq_seven hT hx (hP x.2))
  have hdvd : Nat.card P ∣ 72 * 35 := by
    have h := Subgroup.card_subgroup_dvd_card P
    rwa [nat_card_alternatingGroup, Nat.card_fin] at h
  refine Nat.Coprime.dvd_of_dvd_mul_right ?_ hdvd
  rw [show (35 : ℕ) = 5 * 7 by norm_num]
  exact Nat.Coprime.mul_right
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (hp 5 (by norm_num) (Or.inl rfl))).symm
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (hp 7 (by norm_num) (Or.inr rfl))).symm

theorem card_dvd_seventyTwo_of_mulEquiv {A : Type*} [Group A] (θ : A ≃* alternatingGroup (Fin 7))
    {T P : Subgroup A} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hP : P ≤ Subgroup.normalizer (T : Set A)) : Nat.card P ∣ 72 := by
  have h := card_dvd_seventyTwo_of_le_normalizer (T := T.map θ.toMonoidHom)
    (P := P.map θ.toMonoidHom) (hT.map _)
    (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ θ.injective).mp h))
    ((Subgroup.map_mono hP).trans (Subgroup.map_equiv_normalizer_eq T θ).le)
  rwa [Subgroup.card_map_of_injective θ.injective] at h

end CFSG.AGLEmbedding.BlockAltSevenPL
