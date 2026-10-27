module

public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem eq_bot_of_twoFree {S : Type} [Group S] {σ : MulAut S} {D : Subgroup (fixedSubgroup σ)}
    (hfree : FixedCentralizerTwoFree σ D) {U : Subgroup (fixedSubgroup σ)} (hU : IsPGroup 2 U)
    (hUD : U ≤ centralizer (D : Set (fixedSubgroup σ))) : U = ⊥ := by
  have h := hfree (U.map (fixedSubgroup σ).subtype) (hU.map _) ?_ (map_subtype_le U)
  · exact (map_eq_bot_iff_of_injective U (fixedSubgroup σ).subtype_injective).mp h
  · rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hUD hu) d hd)

theorem inf_center_eq_bot_of_twoFree {S : Type} [Group S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} (hfree : FixedCentralizerTwoFree σ D) {K : Subgroup D}
    (hK : IsPGroup 2 K) : K ⊓ center D = ⊥ := by
  set U : Subgroup (fixedSubgroup σ) := (K ⊓ center D).map D.subtype with hU
  have hUp : IsPGroup 2 U := (hK.to_le inf_le_left).map _
  have hUD : U ≤ centralizer (D : Set (fixedSubgroup σ)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := mem_center_iff.mp (mem_inf.mp hk).2 ⟨d, hd⟩
    exact congrArg Subtype.val h1
  have hbot := eq_bot_of_twoFree hfree hUp hUD
  rw [hU] at hbot
  exact (map_eq_bot_iff_of_injective _ D.subtype_injective).mp hbot

theorem normal_of_isComponent_of_twoFree {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hfree : FixedCentralizerTwoFree σ D)
    (h2 : 2 ∣ Nat.card D) : D.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  intro d hd c
  set D' : Subgroup (fixedSubgroup σ) := D.map (MulAut.conj c).toMonoidHom with hD'
  have hD'c : IsComponent D' := LocalCores.isComponent_map_mulEquiv (MulAut.conj c) hD
  rcases LocalCores.distinct_components_commute hD hD'c with h | h
  · rw [h]
    exact ⟨d, hd, rfl⟩
  · exfalso
    have hle : D' ≤ centralizer (D : Set (fixedSubgroup σ)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm D' D).trans h)
    have hcard : Nat.card D' = Nat.card D :=
      card_map_of_injective (MulAut.conj c).injective
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := D') 2 (hcard ▸ h2)
    have hU : IsPGroup 2 (zpowers (u : fixedSubgroup σ)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hu, pow_one])
    have hbot := eq_bot_of_twoFree hfree hU (zpowers_le.mpr (hle u.2))
    have h1 : (u : fixedSubgroup σ) = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact mem_zpowers _
    have h1' : orderOf u = 1 := by rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [hu] at h1'
    exact absurd h1' (by norm_num)

theorem card_dvd_card_centralizer_mul_card_mulAut {H : Type*} [Group H] [Finite H]
    {D : Subgroup H} [D.Normal] [Group.IsPerfect D] :
    Nat.card H ∣ Nat.card (centralizer (D : Set H)) * Nat.card (MulAut (D ⧸ center D)) := by
  set φ : H →* MulAut (D ⧸ center D) :=
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom D).comp MulAut.conjNormal
    with hφ
  have hker : φ.ker = centralizer (D : Set H) := by
    ext h
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro hh d hd
      have h1 : (MulAut.conjNormal h : MulAut D) = 1 :=
        ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective D
          (by rw [map_one]; exact hh)
      have h2 := congrArg (fun β : MulAut D => ((β ⟨d, hd⟩ : D) : H)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc d * h = h * d * h⁻¹ * h := by rw [h2]
        _ = h * d := by group
    · intro hh
      have h1 : (MulAut.conjNormal h : MulAut D) = 1 := by
        refine MulEquiv.ext fun d => Subtype.ext ?_
        rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hh d d.2]
        group
      show ComponentClassification.PerfectAutomorphisms.centerQuotientHom D
        (MulAut.conjNormal h) = 1
      rw [h1, map_one]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker] at h
  rw [← h]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_subgroup_dvd_card _)

theorem card_mulAut_of_lieModel_psl_three_two {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) : Nat.card (MulAut X) = 241920 := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact RankThree.PartTwo.KFacts.L34.card_mulAut (by rw [hk]; norm_num)


section SuzFive

open CFSG.Sporadic.SuzOddCore CFSG.RankThree.Native
open scoped Pointwise


theorem suzM_card_dvd_of_le_centralizer {y : Equiv.Perm (Fin 1782)} (hy : y ∈ suzM)
    (hyo : orderOf y = 5) {K : Subgroup (Equiv.Perm (Fin 1782))} (hKM : K ≤ suzM)
    (hKy : K ≤ centralizer {y}) : Nat.card K ∣ 3600 ∨ Nat.card K ∣ 600 := by
  obtain ⟨⟨-, -, -, -, ⟨P, hP⟩⟩, ⟨hlines, -⟩, hC, h0, h1⟩ :=
    R3E_Suz_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set yM : suzM := ⟨y, hy⟩ with hyM
  have hyp : IsPGroup 5 (zpowers yM) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyo, pow_one])
  obtain ⟨P', hP'⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq suzM P' P
  set c : Equiv.Perm (Fin 1782) := (g : Equiv.Perm (Fin 1782)) with hc
  have hcM : c ∈ suzM := g.2
  have hyQ : c * y * c⁻¹ ∈ suzFiveQ := by
    have h1 : MulAut.conj g • yM ∈ MulAut.conj g • (P' : Subgroup suzM) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (mem_zpowers yM))
    rw [← Sylow.coe_subgroup_smul, hg, hP] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  set y₀ := c * y * c⁻¹ with hy₀
  have hy₀o : orderOf y₀ = 5 := by
    rw [hy₀, show c * y * c⁻¹ = MulAut.conj c y from rfl, MulEquiv.orderOf_eq, hyo]
  have hmem : zpowers y₀ ∈ {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧
      Nat.card H = 5} := ⟨zpowers_le.mpr hyQ, by rw [Nat.card_zpowers, hy₀o]⟩
  rw [hlines] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hxi : suzFiveLine i ∈ zpowers y₀ := by
    rw [← hi]
    exact mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxi
  set K₀ := K.map (MulAut.conj c).toMonoidHom with hK₀
  have hK₀C : K₀ ≤ suzFiveC i := by
    rw [(hC i).1]
    rintro _ ⟨z, hz, rfl⟩
    refine mem_inf.mpr ⟨?_, mem_suzT_of_mem_suzM ?_⟩
    · rw [mem_centralizer_singleton_iff, ← hk]
      have hzy : z * y = y * z := (mem_centralizer_singleton_iff.mp (hKy hz))
      have hcomm : Commute (MulAut.conj c z) y₀ := by
        show c * z * c⁻¹ * (c * y * c⁻¹) = c * y * c⁻¹ * (c * z * c⁻¹)
        calc c * z * c⁻¹ * (c * y * c⁻¹) = c * (z * y) * c⁻¹ := by group
          _ = c * (y * z) * c⁻¹ := by rw [hzy]
          _ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
      exact (hcomm.zpow_right k).eq
    · exact mul_mem (mul_mem hcM (hKM hz)) (inv_mem hcM)
  have hcard : Nat.card K₀ = Nat.card K := card_map_of_injective (MulAut.conj c).injective
  have hdvd := Subgroup.card_dvd_of_le hK₀C
  rw [hcard] at hdvd
  obtain ⟨v, hv⟩ := i
  have hv' : v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 1 ∨ v = 2 ∨ v = 5 := by omega
  rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (by rwa [(h0 ⟨0, hv⟩ (by simp)).1] at hdvd)
  · exact .inl (by rwa [(h0 ⟨3, hv⟩ (by simp)).1] at hdvd)
  · exact .inl (by rwa [(h0 ⟨4, hv⟩ (by simp)).1] at hdvd)
  · exact .inr (by rwa [(h1 ⟨1, hv⟩ (by simp)).1] at hdvd)
  · exact .inr (by rwa [(h1 ⟨2, hv⟩ (by simp)).1] at hdvd)
  · exact .inr (by rwa [(h1 ⟨5, hv⟩ (by simp)).1] at hdvd)

theorem suz_card_dvd_of_le_centralizer {S : Type} [Group S] (e : S ≃* NativeSporadic.Suz)
    {y : S} (hyo : orderOf y = 5) {K : Subgroup S} (hKy : K ≤ centralizer {y}) :
    Nat.card K ∣ 3600 ∨ Nat.card K ∣ 600 := by
  set f : S →* Equiv.Perm (Fin 1782) := suzM.subtype.comp (e.trans suzEquivM).toMonoidHom
    with hf
  have hinj : Function.Injective f := suzM.subtype_injective.comp (e.trans suzEquivM).injective
  have hfy : orderOf (f y) = 5 := by rw [orderOf_injective f hinj, hyo]
  have hK := suzM_card_dvd_of_le_centralizer (y := f y) (K := K.map f)
    ((e.trans suzEquivM) y).2 hfy
    (by rintro _ ⟨k, -, rfl⟩; exact ((e.trans suzEquivM) k).2)
    (by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.mp (hKy hk)])
  rwa [card_map_of_injective hinj] at hK

theorem suz_not_lieModel_psl_three_two {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Suz) {σ : MulAut S} (hcard : Nat.card (fixedSubgroup σ) = 1209600)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hfree : FixedCentralizerTwoFree σ D) :
    ¬ LieModel (D ⧸ center D) .PSL 3 2 2 := by
  intro hDm
  have hq : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hDcard : Nat.card D = 20160 * Nat.card (center D) := by
    rw [← hq]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hN : D.Normal := normal_of_isComponent_of_twoFree hD hfree h2
  have : Group.IsPerfect D := hD.1.1
  have hdvd := card_dvd_card_centralizer_mul_card_mulAut (H := fixedSubgroup σ) (D := D)
  rw [hcard, card_mulAut_of_lieModel_psl_three_two hDm,
    show (1209600 : ℕ) = 5 * 241920 by norm_num] at hdvd
  have h5 : 5 ∣ Nat.card (centralizer (D : Set (fixedSubgroup σ))) :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 241920) hdvd
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := centralizer (D : Set (fixedSubgroup σ))) 5 h5
  have hy' : orderOf ((y : fixedSubgroup σ) : S) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hK : D.map (fixedSubgroup σ).subtype ≤ centralizer {((y : fixedSubgroup σ) : S)} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_iff.mp y.2 d hd)
  have hKcard : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  have h20160 : 20160 ∣ Nat.card (D.map (fixedSubgroup σ).subtype) := by
    rw [hKcard, hDcard]
    exact Dvd.intro _ rfl
  rcases suz_card_dvd_of_le_centralizer e hy' hK with h | h
  · exact absurd (h20160.trans h) (by norm_num)
  · exact absurd (h20160.trans h) (by norm_num)

end SuzFive

end CFSG.SeitzReduction.SporadicRefine
