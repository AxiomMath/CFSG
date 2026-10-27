module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Kernel
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

section Aux

private theorem isPGroup_center_of_pPrimeCore_eq_bot {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (h : CFSG.pPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  intro z
  obtain ⟨a, m, hpm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (z : Y)).ne' p hp.ne_one
  refine ⟨a, Subtype.ext ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Y, y = (z : Y) ^ p ^ a := ⟨_, rfl⟩
  have hyc : y ∈ Subgroup.center Y := hy ▸ Subgroup.pow_mem _ z.2 _
  have hym : y ^ m = 1 := by rw [hy, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hym)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hN : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ Subgroup.center Y := (Subgroup.zpowers_le.2 hyc) hn
    rw [Subgroup.mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn
  have hle : Subgroup.zpowers y ≤ CFSG.pPrimeCore p Y := le_sSup ⟨hN, hcop⟩
  rw [h] at hle
  have h1 : y = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers y))
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, h1]

private theorem isPGroup_center_pQuot {p : ℕ} (hp : p.Prime) (J : Subgroup G) :
    IsPGroup p (Subgroup.center (PQuot p J)) :=
  isPGroup_center_of_pPrimeCore_eq_bot hp (CFSG.pPrimeCore_quotient_eq_bot hp)

private theorem exists_elemAbelian_center_pQuot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (J : Subgroup G) (hnc : ¬ IsCyclic (Subgroup.center (PQuot p J))) :
    ∃ U : Subgroup (PQuot p J), U ≤ Subgroup.center (PQuot p J) ∧ IsElemAbelian p U ∧
      Nat.card U = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p (Subgroup.center (PQuot p J))) := ⟨isPGroup_center_pQuot hp J⟩
  obtain ⟨E, -, hcard, hE⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hE
  haveI : CFSG.IsElementaryAbelian p (E.map (Subgroup.center (PQuot p J)).subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  refine ⟨E.map (Subgroup.center (PQuot p J)).subtype, Subgroup.map_subtype_le E,
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]

private theorem isPGroup_zpowers_of_pow_eq_one {M : Type*} [Group M] {p : ℕ} {φ : M}
    (h : φ ^ p = 1) : IsPGroup p (Subgroup.zpowers φ) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

end Aux

theorem i64UsedAt_of_tables
    (hGA : GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I64UsedAt G p := by
  intro B x J hB hx hJ hBJ hnc b hb
  have hbN : b ∈ Subgroup.normalizer (J : Set G) := hBJ hb
  have hC : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one inferInstance hnonab hx.2.1
  have hKC : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hKP hC
  have hKJ : CFSG.Open.IsKGroup ↥J := CFSG.Open.IsKGroup.of_le hKC hJ.1
  have hKq : CFSG.Open.IsKGroup (PQuot p J) := CFSG.Open.IsKGroup.quotient hKJ _
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hU := exists_elemAbelian_center_pQuot hp hp2 J hnc
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ with hγ
  have hbp : b ^ p = 1 := hB.1.2 b hb
  have hγp : γ ^ p = 1 := by
    apply Subtype.ext
    simp [hγ, inv_pow, hbp]
  have hφp : (barAut p J γ) ^ p = 1 := by rw [← map_pow, hγp, map_one]
  obtain ⟨u, hu⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.kernel11_6U_conj hGA hSpM hq
    hKq hp hp2 hU (barAut p J γ) (isPGroup_zpowers_of_pow_eq_one hφp)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = b⁻¹ * y * b := fun y => by
    change (b⁻¹ : G) * y * (b⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (b⁻¹ * y * b) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

private theorem sporadicMultipliers_of_census
    (h : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
  ⟨fun s => by rw [h.1 s]; cases s <;> rfl, h.2⟩

theorem i64UsedAt_holds
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I64UsedAt G p :=
  i64UsedAt_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    hnonab hKP hp hp2

end CFSG.LocalAnalysis.GLTheoremA
