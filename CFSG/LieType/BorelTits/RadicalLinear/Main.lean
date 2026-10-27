module

public import CFSG.LieType.BorelTits.RadicalLinear.Levi
public import CFSG.LieType.BorelTits.RadicalLinear.Centre
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalBasis
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSL

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
  {G : Type*} [Group G]

theorem exists_levels_of_radical [CharP K 2] (π : SpecialLinearGroup ι K →* G)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center (SpecialLinearGroup ι K))
    (U : Subgroup G) (hU : U ≠ ⊥)
    (hrad : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (U : Set G)) = U) :
    ∃ (ℓ : ι → ℕ) (hk : 2 ≤ levelsCard ℓ),
      Nat.card (Subgroup.center U) =
        Nat.card K ^ (levelCount ℓ ⟨0, by omega⟩ * levelCount ℓ ⟨levelsCard ℓ - 1, by omega⟩) ∧
      Nat.card U = Nat.card K ^ ((Fintype.card ι ^ 2 - ∑ i, levelCount ℓ i ^ 2) / 2) ∧
      ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set G)) ⧸
          U.subgroupOf (Subgroup.normalizer (U : Set G))),
        S.Normal → CFSG.IsQuasisimple S →
          ∃ i, 2 ≤ levelCount ℓ i ∧ ¬ (levelCount ℓ i = 2 ∧ Nat.card K = 2) ∧
            ∃ Z' ≤ Subgroup.center S, ∃ _ : Z'.Normal,
              Nonempty (S ⧸ Z' ≃* ProjectiveSpecialLinearGroup (Block ℓ (levels ℓ i)) K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G := Finite.of_surjective π hπ
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
  have hrad2 : GGRadicalTwo π.range U := by
    unfold GGRadicalTwo
    rw [hrange, top_inf_eq]
    exact hrad
  have hU2 : IsPGroup 2 U := hrad2.isPGroup
  have hker_le : π.ker ≤ Subgroup.center (SpecialLinearGroup ι K) := hker.le
  have hinv : ∀ z ∈ π.ker, z ^ 2 = 1 → z = 1 := by
    intro z hz h2
    rw [hker] at hz
    exact eq_one_of_mem_center_of_sq_eq_one hz h2
  have hU₀rad : GGRadicalTwo (⊤ : Subgroup (SpecialLinearGroup ι K)) (liftTwo π U) :=
    radicalTwo_liftTwo π hker_le hrad2
  have hU₀P2 : IsPGroup 2 (liftTwo π U) := isPGroup_liftTwo π U
  have hU₀map : (liftTwo π U).map π = U :=
    map_liftTwo π hker_le hU2 hrad2.le
  have hU₀ne : liftTwo π U ≠ ⊥ := fun h => hU (by rw [← hU₀map, h, Subgroup.map_bot])
  have hN : (⊤ : Subgroup (SpecialLinearGroup ι K)) ⊓
      Subgroup.normalizer (liftTwo π U : Set (SpecialLinearGroup ι K)) =
      Subgroup.comap π (Subgroup.normalizer (U : Set G)) := by
    rw [normalizer_liftTwo π hker_le hU2 hrad2.le, hrange, top_inf_eq]
  obtain ⟨hQeq, hQN⟩ := eq_flagKernel_of_radical (slRep (ι := ι) (K := K)) slRep_injective hU₀rad
  obtain ⟨g, ℓ, hF⟩ := exists_eq_flagMap_stdFlag (fixFlag_mono slRep (liftTwo π U))
    (fixFlag_zero slRep (liftTwo π U))
    (exists_fixFlag_eq_top (slRep (ι := ι) (K := K)) 2 (liftTwo π U) hU₀rad.isPGroup)
  have hU₀eq : liftTwo π U = (stdU (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [stdU, ← flagKernel_flagMap, ← hF]
    exact hQeq
  have hU₀P : (⊤ : Subgroup (SpecialLinearGroup ι K)) ⊓
      Subgroup.normalizer (liftTwo π U : Set (SpecialLinearGroup ι K)) =
      (stdP (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [hQN, hF, flagStab_flagMap]
    rfl
  have hP : Subgroup.comap π (Subgroup.normalizer (U : Set G)) =
      (stdP (K := K) ℓ).map (MulAut.conj g).toMonoidHom := hN.symm.trans hU₀P
  have hstdU_ne : stdU (K := K) ℓ ≠ ⊥ := fun h => hU₀ne (by rw [hU₀eq, h, Subgroup.map_bot])
  have hk : 2 ≤ levelsCard ℓ := two_le_levelsCard (exists_lt_of_stdU_ne_bot hstdU_ne)
  have hinj : Function.Injective (π.comp (liftTwo π U).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : SpecialLinearGroup ι K) ∈ π.ker ⊓ (liftTwo π U) := ⟨hx, x.2⟩
    rw [ker_inf_eq_bot π hinv hU₀P2, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange' : (π.comp (liftTwo π U).subtype).range = U := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hU₀map]
  let e1 : (liftTwo π U) ≃* U :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange')
  let e2 : (stdU (K := K) ℓ) ≃* (liftTwo π U) :=
    (Subgroup.equivMapOfInjective (stdU (K := K) ℓ) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hU₀eq.symm)
  have hc1 : Nat.card (Subgroup.center U) = Nat.card (Subgroup.center (liftTwo π U)) := by
    rw [← Subgroup.map_center_eq e1]
    exact Subgroup.card_map_of_injective e1.injective
  have hc2 : Nat.card (Subgroup.center (liftTwo π U)) =
      Nat.card (Subgroup.center (stdU (K := K) ℓ)) := by
    rw [← Subgroup.map_center_eq e2]
    exact Subgroup.card_map_of_injective e2.injective
  have hcenter : Nat.card (Subgroup.center U) =
      Nat.card (Subgroup.center (stdU (K := K) ℓ)) := hc1.trans hc2
  have hcardU : Nat.card U = Nat.card (stdU (K := K) ℓ) :=
    (Nat.card_congr (e2.trans e1).toEquiv).symm
  have hK3 : Nat.card K ≠ 3 := by
    let _ : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hn, hcard⟩ := FiniteField.card K 2
    have hcard' : Nat.card K = 2 ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hcard
    rintro h3
    have h23 : 2 ^ (n : ℕ) = 3 := hcard'.symm.trans h3
    have hdvd : 2 ∣ 3 := h23 ▸ dvd_pow_self 2 (PNat.ne_zero n)
    omega
  have hUeq : U = ((stdU (K := K) ℓ).map (MulAut.conj g).toMonoidHom).map π := by
    rw [← hU₀map, hU₀eq]
  refine ⟨ℓ, hk, ?_, ?_, fun S hSn hS => ?_⟩
  ·
    have h0 : 0 < levelsCard ℓ := by omega
    have hlast : levelsCard ℓ - 1 < levelsCard ℓ := Nat.sub_lt h0 Nat.one_pos
    have hlo : ∀ a, levels ℓ ⟨0, h0⟩ ≤ ℓ a := levels_zero_le h0
    have hhi : ∀ a, ℓ a ≤ levels ℓ ⟨levelsCard ℓ - 1, hlast⟩ := le_levels_last h0
    have hlo' : ∃ a, ℓ a = levels ℓ ⟨0, h0⟩ := exists_eq_levels ℓ ⟨0, h0⟩
    have hhi' : ∃ a, ℓ a = levels ℓ ⟨levelsCard ℓ - 1, hlast⟩ :=
      exists_eq_levels ℓ ⟨levelsCard ℓ - 1, hlast⟩
    have hlohi : levels ℓ ⟨0, h0⟩ < levels ℓ ⟨levelsCard ℓ - 1, hlast⟩ :=
      (levels ℓ).strictMono (by
        rw [Fin.lt_def]
        simp only [Fin.val_mk]
        omega)
    exact hcenter.trans (card_center_stdU (K := K) (ℓ := ℓ) hlo hhi hlo' hhi' hlohi)
  ·
    rw [hcardU, card_stdU (K := K) ℓ, card_filter_lt ℓ]
  ·
    exact exists_levi_of_isQuasisimple hK3 π hπ hker ℓ g U hUeq hP S hSn hS

end CFSG.LieType.BorelTits.RadicalLinear
