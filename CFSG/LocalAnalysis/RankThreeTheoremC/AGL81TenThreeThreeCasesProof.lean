module

import CFSG.Quasithin.EmptyFaithful.S151TCA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenOneSixCenterCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    NineThreeFour M (pCoreOf 2 H) L →
    ∀ z ∈ Subgroup.center ↥(barM M L), (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (H ⊓ L)

variable {G}

namespace TenThreeThree

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_card_eight {P : Subgroup X} {m : ℕ} (hm : ¬ 2 ∣ m)
    (hP : Nat.card P = 8 * m) : ∃ T : Subgroup X, T ≤ P ∧ IsPGroup 2 T ∧ Nat.card T = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥P))
  refine ⟨(T₀ : Subgroup P).map P.subtype, Subgroup.map_subtype_le _, T₀.isPGroup'.map _, ?_⟩
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have hf : (Nat.card P).factorization 2 = 3 := by
    rw [hP, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm, show (8 : ℕ) = 2 ^ 3 by norm_num,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
    rfl
  rw [Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity, hf]
  norm_num

theorem isSylowTwoOf_of_card {T Y : Subgroup X} (hTY : T ≤ Y) (hT : IsPGroup 2 T)
    (hT8 : Nat.card T = 8) {m : ℕ} (hm : ¬ 2 ∣ m) (hY : Nat.card Y = 8 * m) :
    CFSG.QuasithinUnique.IsSylowTwoOf T Y := by
  refine ⟨hTY, hT, fun h2 => hm ?_⟩
  have h := (T.subgroupOf Y).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hT8, hY] at h
  have : (T.subgroupOf Y).index = m := by omega
  rwa [this] at h2

theorem isParabolicTwo_altSix {Y P : Subgroup X} (hPY : P ≤ Y)
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (eP : ↥P ≃* Equiv.Perm (Fin 4)) : IsParabolicTwo Y P := by
  have hP24 : Nat.card P = 8 * 3 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have hY360 : Nat.card Y = 8 * 45 := by
    rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; rfl
  obtain ⟨T, hTP, hT2, hT8⟩ := exists_sylow_card_eight (by norm_num) hP24
  refine ⟨hPY, T, isSylowTwoOf_of_card (hTP.trans hPY) hT2 hT8 (by norm_num) hY360, ?_⟩
  rintro y ⟨hyY, hyN⟩
  have hTY := hTP.trans hPY
  set T' := T.subgroupOf Y
  have hyN' : (⟨y, hyY⟩ : ↥Y) ∈ Subgroup.normalizer (T' : Set ↥Y) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTY]
    exact Subgroup.mem_subgroupOf.mpr hyN
  have hD : Nat.card (T'.map eY.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective eY.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hT8]
  have hnorm := CFSG.Quasithin.S151TC.alt6_normalizer_eq_of_card_eight _ hD
  have hmem : eY ⟨y, hyY⟩ ∈ Subgroup.normalizer ((T'.map eY.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨_, hyN', rfl⟩
  rw [hnorm] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have : t = ⟨y, hyY⟩ := eY.injective hte
  have hyT : (⟨y, hyY⟩ : ↥Y) ∈ T' := this ▸ ht
  exact hTP (Subgroup.mem_subgroupOf.mp hyT)

theorem isParabolicTwo_threeASix {Y P : Subgroup X} (hPY : P ≤ Y)
    (hZ : Nat.card (Subgroup.center ↥Y) = 3)
    (hA6 : Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 6)))
    (hS4 : Nonempty (↥((P.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) ≃*
      Equiv.Perm (Fin 4)))
    (hZP : ∀ z ∈ Subgroup.center ↥Y, (z : X) ∈ P) : IsParabolicTwo Y P := by
  classical
  obtain ⟨e6⟩ := hA6
  obtain ⟨e4⟩ := hS4
  set Z := Subgroup.center ↥Y
  set π : ↥Y →* ↥Y ⧸ Z := QuotientGroup.mk' Z
  set P' := P.subgroupOf Y
  have hZP' : Z ≤ P' := fun z hz => Subgroup.mem_subgroupOf.mpr (hZP z hz)
  have hYc : Nat.card Y = 8 * 135 := by
    have h := Z.card_mul_index
    have hi : Z.index = 360 := by
      rw [Subgroup.index, Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; rfl
    rw [hZ, hi] at h; omega
  have hPc : Nat.card P = 8 * 9 := by
    set g : ↥P' →* ↥Y ⧸ Z := π.comp P'.subtype
    have hr : g.range = P'.map π := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hk : g.ker = Z.subgroupOf P' := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have h1 : Nat.card (P'.map π) = 24 := by
      rw [Nat.card_congr e4.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have h2 := Subgroup.card_ker_mul_card_range g
    rw [hk, hr, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP').toEquiv, hZ] at h2
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv]
    change Nat.card P' = _
    omega
  obtain ⟨T, hTP, hT2, hT8⟩ := exists_sylow_card_eight (by norm_num) hPc
  have hTY := hTP.trans hPY
  refine ⟨hPY, T, isSylowTwoOf_of_card hTY hT2 hT8 (by norm_num) hYc, ?_⟩
  rintro y ⟨hyY, hyN⟩
  set T' := T.subgroupOf Y
  have hyN' : (⟨y, hyY⟩ : ↥Y) ∈ Subgroup.normalizer (T' : Set ↥Y) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTY]
    exact Subgroup.mem_subgroupOf.mpr hyN
  have hT'Z : ∀ t ∈ T', t ∈ Z → t = 1 := by
    intro t ht htZ
    have hT2' : IsPGroup 2 T' := hT2.comap_subtype
    have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
    obtain ⟨i, hi⟩ := hT2' ⟨t, ht⟩
    obtain ⟨j, hj⟩ := hZ3 ⟨t, htZ⟩
    have hdi : orderOf t ∣ 2 ^ i :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hi)
    have hdj : orderOf t ∣ 3 ^ j :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      ((Nat.Coprime.pow _ _ (by norm_num)).coprime_dvd_left hdi) hdj)
  have hD : Nat.card ((T'.map π).map e6.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e6.injective]
    have hinj : Function.Injective (π.comp T'.subtype) := by
      rw [injective_iff_map_eq_one]
      intro t ht
      exact Subtype.ext (hT'Z t t.2 ((QuotientGroup.eq_one_iff _).mp ht))
    have hr : (π.comp T'.subtype).range = T'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hT8]
  have hnorm := CFSG.Quasithin.S151TC.alt6_normalizer_eq_of_card_eight _ hD
  have hmem : e6 (π ⟨y, hyY⟩) ∈
      Subgroup.normalizer (((T'.map π).map e6.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨_, Subgroup.le_normalizer_map π ⟨_, hyN', rfl⟩, rfl⟩
  rw [hnorm] at hmem
  obtain ⟨w, ⟨t, ht, rfl⟩, hwe⟩ := hmem
  have hyt : π ⟨y, hyY⟩ = π t := (e6.injective hwe).symm
  have hz : t⁻¹ * ⟨y, hyY⟩ ∈ Z := by
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv]
    change (π t)⁻¹ * π ⟨y, hyY⟩ = 1
    rw [hyt, inv_mul_cancel]
  have : y = (t : X) * ((t⁻¹ * ⟨y, hyY⟩ : ↥Y) : X) := by simp
  rw [this]
  exact P.mul_mem (hTP (Subgroup.mem_subgroupOf.mp ht)) (hZP _ hz)

theorem isClassicalTwoOrG2_of_altSix {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 6)) : IsClassicalTwoOrG2 Y :=
  Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ⟨e⟩⟩)

end TenThreeThree

end CFSG.LocalAnalysis.RankThreeTheoremC
