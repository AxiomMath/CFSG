module

import CFSG.GroupTheory.SteinbergCBHHBTheoremB
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs

public section

open Subgroup Polynomial Module
open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

section HHCore

variable {p : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [Finite (LinearMap.GeneralLinearGroup F W)]

theorem hh_centralizes (hd : Module.finrank F W + 2 ≤ p)
    (N : Subgroup (LinearMap.GeneralLinearGroup F W))
    (hN : Nat.Coprime p (Nat.card N))
    (x : LinearMap.GeneralLinearGroup F W) (hx : x ^ p = 1)
    (hxN : x ∈ normalizer (N : Set (LinearMap.GeneralLinearGroup F W))) :
    ∀ g ∈ N, x * g = g * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, hg₀N, hg₀⟩ := hcon
  have hx1 : x ≠ 1 := fun h => hg₀ (by simp [h])
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  set G : Subgroup (LinearMap.GeneralLinearGroup F W) := N ⊔ zpowers x with hG
  have hzN : zpowers x ≤ normalizer (N : Set (LinearMap.GeneralLinearGroup F W)) :=
    zpowers_le.2 hxN
  have hGn : G ≤ normalizer (N : Set (LinearMap.GeneralLinearGroup F W)) :=
    sup_le le_normalizer hzN
  have hNG : N ≤ G := le_sup_left
  have hxG : x ∈ G := mem_sup_right (mem_zpowers x)
  have hzcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hord]
  have hzfin : Finite (zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [hzcard]; exact hp.out.ne_zero)
  have hGcoe : (G : Set (LinearMap.GeneralLinearGroup F W)) =
      (N : Set (LinearMap.GeneralLinearGroup F W)) * (zpowers x : Set (LinearMap.GeneralLinearGroup F W)) :=
    coe_mul_of_right_le_normalizer_left N (zpowers x) hzN
  haveI : Finite G := by
    have hfin : ((N : Set (LinearMap.GeneralLinearGroup F W)) *
        (zpowers x : Set (LinearMap.GeneralLinearGroup F W))).Finite :=
      Set.Finite.mul (Set.toFinite _) (Set.toFinite _)
    rw [← hGcoe] at hfin
    exact hfin.to_subtype
  set N' : Subgroup G := N.subgroupOf G with hN'
  haveI hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNG).2 hGn
  have hN'card : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNG).toEquiv
  set xG : G := ⟨x, hxG⟩ with hxG'
  haveI hcyc : IsCyclic (G ⧸ N') := by
    refine ⟨QuotientGroup.mk xG, fun y => ?_⟩
    induction y using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : LinearMap.GeneralLinearGroup F W) ∈ (G : Set (LinearMap.GeneralLinearGroup F W)) :=
        y.2
      rw [hGcoe] at hy
      obtain ⟨n, hn, z, hz, hnz⟩ := hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have hyeq : y = ⟨n, hNG hn⟩ * xG ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
        exact hnz.symm
      rw [hyeq, ← QuotientGroup.mk_zpow, QuotientGroup.mk_mul]
      have : (QuotientGroup.mk (⟨n, hNG hn⟩ : G) : G ⧸ N') = 1 :=
        (QuotientGroup.eq_one_iff _).2 (by simpa [hN', mem_subgroupOf] using hn)
      rw [this, one_mul]
  have hsol : Group.IsSolvable (G ⧸ N') := by
    refine Group.isSolvable_of_comm ?_
    obtain ⟨g, hg⟩ := hcyc
    intro a b
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (hg a)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (hg b)
    exact (Commute.zpow_zpow_self g i j).eq
  have hps : CFSG.HallHigman.IsPSolvable p G :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
      N' (by rw [hN'card]; exact hN) hsol
  have hNx : N ⊓ zpowers x = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (by rw [hzcard]; exact hN.symm))
  have hGcard : Nat.card G = Nat.card N * p := by
    have h := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hNx, card_bot, mul_one, hzcard] at h
    exact h
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (zpowers x) G := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨zpowers_le.2 hxG, IsPGroup.of_card (n := 1) (by rw [hzcard, pow_one]), ?_⟩
    intro hdvd
    have h1 := Subgroup.relIndex_mul_card (zpowers x) G
    rw [inf_eq_left.2 (zpowers_le.2 hxG), hzcard, hGcard] at h1
    have h2 : (zpowers x).relIndex G = Nat.card N := Nat.eq_of_mul_eq_mul_right hp.out.pos h1
    rw [h2] at hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hN) hdvd
  have hpi : CFSG.piCore {q : Nat.Primes | q.val = p} G = ⊥ := by
    refine le_antisymm (sSup_le ?_) bot_le
    rintro K ⟨hKn, hKπ⟩
    rw [le_bot_iff]
    by_contra hK
    have hKp : IsPGroup p K := by
      rw [IsPGroup.iff_orderOf]
      intro g
      have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      refine ⟨(orderOf g).primeFactorsList.length, ?_⟩
      exact Nat.eq_prime_pow_of_unique_prime_dvd hg0 (fun {d} hd hdvd => by
        have h1 : d ∣ Nat.card K := hdvd.trans (orderOf_dvd_natCard g)
        exact hKπ ⟨d, hd⟩ h1)
    set K₀ : Subgroup (LinearMap.GeneralLinearGroup F W) := K.map G.subtype with hK₀
    have hK₀G : K₀ ≤ G := map_subtype_le K
    have hK₀p : IsPGroup p K₀ := hKp.map G.subtype
    have hGK₀ : G ≤ normalizer (K₀ : Set (LinearMap.GeneralLinearGroup F W)) := by
      intro g hg
      have h1 : (⟨g, hg⟩ : G) ∈ normalizer (K : Set G) := by
        rw [normalizer_eq_top_iff.2 hKn]; exact mem_top _
      exact le_normalizer_map G.subtype (mem_map_of_mem G.subtype h1)
    have hK₀le : K₀ ≤ zpowers x := le_of_normal_isPGroup_of_isSylowOf hSyl hK₀G hGK₀ hK₀p
    have hK₀ne : K₀ ≠ ⊥ := by
      intro h
      apply hK
      exact (map_eq_bot_iff_of_injective K G.subtype_injective).1 h
    have hdvd : Nat.card K₀ ∣ p := by
      have := Subgroup.card_dvd_of_le hK₀le
      rwa [hzcard] at this
    have hKeq : K₀ = zpowers x := by
      rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq K₀ h1) hK₀ne
      · exact Subgroup.eq_of_le_of_card_ge hK₀le (by rw [h1, hzcard])
    have hg₀G : g₀ ∈ G := hNG hg₀N
    have hxK₀ : x ∈ K₀ := by rw [hKeq]; exact mem_zpowers x
    have h1 : g₀ * x * g₀⁻¹ ∈ zpowers x := by
      have := (mem_normalizer_iff.1 (hGK₀ hg₀G) x).1 hxK₀
      rw [hKeq] at this
      exact this
    have h2 : x * g₀⁻¹ * x⁻¹ ∈ N := (mem_normalizer_iff.1 hxN g₀⁻¹).1 (inv_mem hg₀N)
    have hcN : g₀ * x * g₀⁻¹ * x⁻¹ ∈ N := by
      have := mul_mem hg₀N h2
      have e : g₀ * (x * g₀⁻¹ * x⁻¹) = g₀ * x * g₀⁻¹ * x⁻¹ := by group
      rwa [e] at this
    have hcz : g₀ * x * g₀⁻¹ * x⁻¹ ∈ zpowers x := mul_mem h1 (inv_mem (mem_zpowers x))
    have hc1 : g₀ * x * g₀⁻¹ * x⁻¹ = 1 := by
      have : g₀ * x * g₀⁻¹ * x⁻¹ ∈ N ⊓ zpowers x := ⟨hcN, hcz⟩
      rwa [hNx, mem_bot] at this
    apply hg₀
    calc x * g₀ = (g₀ * x * g₀⁻¹ * x⁻¹)⁻¹ * (g₀ * x) := by group
      _ = g₀ * x := by rw [hc1]; simp
  obtain ⟨r, hr1, hrle, hmin, h2, -, -⟩ :=
    CFSG.GroupTheory.HallHigmanB.hall_higman_theorem_B_minimal_polynomial
      G hps hpi ⟨x, hxG⟩ (n := 1) le_rfl (by rw [Subgroup.orderOf_mk, hord, pow_one])
  have hrp : p - 1 ≤ r := by
    by_cases hlt : r < p ^ 1
    · obtain ⟨n₀, q, k, hn₀1, hn₀n, -, -, -, -, hbound⟩ := h2 hlt
      have hn0 : n₀ = 1 := by omega
      subst hn0
      simpa using hbound
    · have : r = p := by rw [pow_one] at hrle hlt; omega
      omega
  have hrd : r ≤ Module.finrank F W := by
    have hdvd := LinearMap.minpoly_dvd_charpoly
      (((⟨x, hxG⟩ : G) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W)
    rw [hmin] at hdvd
    have := natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic _).ne_zero
    rw [LinearMap.charpoly_natDegree] at this
    have h1 : (X - 1 : F[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : F)
    rw [natDegree_pow, h1, mul_one] at this
    exact this
  omega

theorem centralizes_of_faithful_lift (hd : Module.finrank F W + 2 ≤ p)
    {S P : Type} [Group S] [Group P]
    (ρ : S →* LinearMap.GeneralLinearGroup F W) (hρ : Function.Injective ρ)
    (π : S →* P) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    {u : P} (hu : orderOf u = p) {V : Subgroup P} (hV : ¬ p ∣ Nat.card V)
    (hnorm : u ∈ normalizer (V : Set P)) :
    ∀ v ∈ V, u * v = v * u := by
  haveI : Finite S := Finite.of_injective ρ hρ
  have hp' : p.Prime := hp.out
  have hker' : Nat.Coprime p (Nat.card π.ker) := (Nat.Prime.coprime_iff_not_dvd hp').2 hker
  have hup : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  obtain ⟨u₀, hu₀⟩ := hπ u
  have hker_mem : u₀ ^ p ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu₀, hup]
  obtain ⟨m, hm1, hm0⟩ := Nat.chineseRemainder hker' 1 0
  have hkm : Nat.card π.ker ∣ m := (Nat.modEq_zero_iff_dvd).1 hm0
  have hmod : m % p = 1 := by
    have : m % p = 1 % p := hm1
    rw [this]
    exact Nat.mod_eq_of_lt hp'.one_lt
  set ul : S := u₀ ^ m with hul
  have hπul : π ul = u := by
    rw [hul, map_pow, hu₀]
    conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hup, one_pow, one_mul, hmod, pow_one]
  have hulp : ul ^ p = 1 := by
    have h1 : (⟨u₀ ^ p, hker_mem⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    have h2 : (u₀ ^ p) ^ Nat.card π.ker = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    obtain ⟨t, ht⟩ := hkm
    calc (u₀ ^ m) ^ p = (u₀ ^ p) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((u₀ ^ p) ^ Nat.card π.ker) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [h2, one_pow]
  set Vl : Subgroup S := V.comap π with hVl
  have hulN : ul ∈ normalizer (Vl : Set S) := by
    rw [mem_normalizer_iff]
    intro h
    have hV' := (mem_normalizer_iff.1 hnorm) (π h)
    simp only [hVl, SetLike.mem_coe, mem_comap, map_mul, map_inv, hπul]
    exact hV'
  have hVlp : ¬ p ∣ Nat.card Vl := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Vl) p hdvd
    have hyp : ((y : Vl) : S) ^ p = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    have hyV : π ((y : Vl) : S) ∈ V := y.2
    by_cases hπy : π ((y : Vl) : S) = 1
    · have hmem : ((y : Vl) : S) ∈ π.ker := hπy
      have h1 : orderOf (⟨((y : Vl) : S), hmem⟩ : π.ker) = p := by
        rw [← Subgroup.orderOf_coe]
        simp only [Subgroup.coe_mk]
        rw [Subgroup.orderOf_coe, hy]
      exact hker (h1 ▸ orderOf_dvd_natCard _)
    · have hpow : (π ((y : Vl) : S)) ^ p = 1 := by rw [← map_pow, hyp, map_one]
      have hdvd' : orderOf (π ((y : Vl) : S)) ∣ p := orderOf_dvd_of_pow_eq_one hpow
      have hne : orderOf (π ((y : Vl) : S)) ≠ 1 := fun h => hπy (orderOf_eq_one_iff.1 h)
      have h2 : orderOf (π ((y : Vl) : S)) = p := (Nat.dvd_prime hp').1 hdvd' |>.resolve_left hne
      have h3 : orderOf (⟨π ((y : Vl) : S), hyV⟩ : V) = p := by
        rw [← Subgroup.orderOf_coe]
        exact h2
      exact hV (h3 ▸ orderOf_dvd_natCard _)
  haveI : Finite Vl := inferInstance
  have hNcop : Nat.Coprime p (Nat.card (Vl.map ρ)) := by
    rw [Subgroup.card_map_of_injective hρ]
    exact (Nat.Prime.coprime_iff_not_dvd hp').2 hVlp
  have hxN : ρ ul ∈ normalizer ((Vl.map ρ : Subgroup (LinearMap.GeneralLinearGroup F W)) :
      Set (LinearMap.GeneralLinearGroup F W)) :=
    le_normalizer_map ρ (mem_map_of_mem ρ hulN)
  have hcent := hh_centralizes hd (Vl.map ρ) hNcop (ρ ul) (by rw [← map_pow, hulp, map_one]) hxN
  intro v hv
  obtain ⟨g, hg⟩ := hπ v
  have hgVl : g ∈ Vl := by simpa [hVl, hg] using hv
  have h1 := hcent (ρ g) (mem_map_of_mem ρ hgVl)
  rw [← map_mul, ← map_mul] at h1
  have h2 : ul * g = g * ul := hρ h1
  have h3 := congrArg π h2
  rw [map_mul, map_mul, hπul, hg] at h3
  exact h3

end HHCore

open CFSG.BenderSuzuki.MatrixGroups in
theorem kFactU3UnipotentCentralizing :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsU3Pred p K →
      ∀ u : K, orderOf u = p → ∀ V : Subgroup K, ¬ p ∣ Nat.card V →
        u ∈ Subgroup.normalizer (V : Set K) → ∀ v ∈ V, u * v = v * u := by
  intro p _ hp5 K _ _ hK u hu V hV hnorm
  obtain ⟨d, hd, hfe, he⟩ := u3Sylow_index_of_isU3Pred hK
  obtain ⟨-, hf, hq, K', _, _, J, hJ, hK', hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
      (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hd he)
  haveI : Fintype K' := Fintype.ofFinite K'
  haveI : CharP K' p := charP_of_card_eq_prime_pow (p := p) (f := d.1.fieldExponent * 2)
    (by rw [Fintype.card_eq_nat_card, hK', ← pow_mul])
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 3) K') := inferInstance
  haveI : Finite (LinearMap.GeneralLinearGroup K' (Fin 3 → K')) :=
    Finite.of_equiv _ (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := K')).toEquiv
  set S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K') := J.specialSubgroup with hS
  let π₀ : ↥S →* ↥(ProjectiveSpecialUnitaryMatrixGroup J) :=
    (Matrix.ProjGenLinGroup.mk).subgroupMap S
  have hπ₀ : Function.Surjective π₀ := MonoidHom.subgroupMap_surjective _ _
  let π : ↥S →* K := e.symm.toMonoidHom.comp π₀
  have hπ : Function.Surjective π := e.symm.surjective.comp hπ₀
  let ρ : ↥S →* LinearMap.GeneralLinearGroup K' (Fin 3 → K') :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := K')).toMonoidHom.comp S.subtype
  have hρ : Function.Injective ρ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := K')).injective.comp S.subtype_injective
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p hdvd
    have hyker : π (y : ↥S) = 1 := y.2
    have h1 : π₀ (y : ↥S) = 1 := (e.symm.map_eq_one_iff).1 hyker
    have h2 : Matrix.ProjGenLinGroup.mk (((y : ↥S) : ↥S) : Matrix.GeneralLinearGroup (Fin 3) K') = 1 := by
      have := congrArg Subtype.val h1
      simpa [π₀] using this
    have h3 : (((y : ↥S)) : Matrix.GeneralLinearGroup (Fin 3) K') ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) K') :=
      Matrix.ProjGenLinGroup.mk_eq_one.1 h2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
    obtain ⟨a, ha⟩ := h3
    have hdet : Matrix.GeneralLinearGroup.det (((y : ↥S)) : Matrix.GeneralLinearGroup (Fin 3) K') = 1 :=
      ((J.mem_specialSubgroup_iff _).1 (y : ↥S).2).2
    rw [← ha, Matrix.GeneralLinearGroup.det_scalar] at hdet
    have h4 : (((y : ↥S)) : Matrix.GeneralLinearGroup (Fin 3) K') ^ 3 = 1 := by
      rw [← ha, ← map_pow]
      have : a ^ 3 = 1 := by simpa using hdet
      rw [this, map_one]
    have h5 : y ^ 3 = 1 := Subtype.ext (Subtype.ext h4)
    have h6 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h5
    rw [hy] at h6
    have h7 : p ≤ 3 := Nat.le_of_dvd (by norm_num) h6
    omega
  have hdim : Module.finrank K' (Fin 3 → K') + 2 ≤ p := by
    rw [Module.finrank_fin_fun]; omega
  exact centralizes_of_faithful_lift hdim ρ hρ π hπ hker hu hV hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
