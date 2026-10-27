module

public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]

theorem exists_sylow_normalized_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (H B : Subgroup G) (hB : IsPGroup p B) (hBH : B ≤ Subgroup.normalizer (H : Set G)) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup p S ∧
      (∀ n : ℕ, p ^ n ∣ Nat.card H → p ^ n ∣ Nat.card S) ∧ B ≤ Subgroup.normalizer (S : Set G) := by
  classical
  let φ : B →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hBH)
  let _ : MulDistribMulAction B H := MulDistribMulAction.compHom H φ
  let _ : MulAction B (Sylow p H) := Sylow.pointwiseMulAction
  have hmod := hB.card_modEq_card_fixedPoints (Sylow p H)
  have hone : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
  have hne : Nat.card (MulAction.fixedPoints B (Sylow p H)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h1 : 0 ≡ 1 [MOD p] := hmod.symm.trans hone
    have := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).1 h1
    have hp : p ∣ 1 := by simpa using this
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 hp)
  obtain ⟨⟨Q₀, hQ₀⟩⟩ : Nonempty (MulAction.fixedPoints B (Sylow p H)) := by
    have : Finite (MulAction.fixedPoints B (Sylow p H)) := inferInstance
    exact (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  refine ⟨(Q₀ : Subgroup H).map H.subtype, Subgroup.map_subtype_le _,
    Q₀.isPGroup'.map _, fun n hn => ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup H) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup H) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((H.normalizerMonoidHom) (Subgroup.inclusion hBH ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem exists_ne_one_mem_centralizer_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (S B : Subgroup G) (hS : IsPGroup p S) (hS1 : S ≠ ⊥) (hB : IsPGroup p B)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    ∃ w ∈ S, w ≠ 1 ∧ ∀ b ∈ B, b * w = w * b := by
  classical
  let φ : B →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hBS)
  let _ : MulDistribMulAction B S := MulDistribMulAction.compHom S φ
  have hmod := hB.card_modEq_card_fixedPoints S
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    apply hS1
    exact Subgroup.eq_bot_of_card_eq S (by simpa using hk)
  have hpS : p ∣ Nat.card S := by
    rw [hk]
    exact dvd_pow_self p hk1
  have hpF : p ∣ Nat.card (MulAction.fixedPoints B S) :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 hpS))
  have hpos : 0 < Nat.card (MulAction.fixedPoints B S) :=
    Nat.card_pos_iff.2 ⟨⟨(⟨1, MulAction.mem_fixedPoints.2 fun m => smul_one m⟩ :
      MulAction.fixedPoints B S)⟩, inferInstance⟩
  have hlt : 1 < Nat.card (MulAction.fixedPoints B S) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hpF)
  have := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨a, b, hab⟩ := exists_pair_ne (MulAction.fixedPoints B S)
  obtain ⟨w, hw⟩ : ∃ w : MulAction.fixedPoints B S, w.1 ≠ 1 := by
    by_cases ha : a.1 = 1
    · refine ⟨b, fun hb => hab ?_⟩
      exact Subtype.ext (ha.trans hb.symm)
    · exact ⟨a, ha⟩
  refine ⟨(w.1 : G), w.1.2, fun h => hw (Subtype.ext h), fun c hc => ?_⟩
  have hfix := MulAction.mem_fixedPoints.1 w.2 ⟨c, hc⟩
  have h1 : ((((⟨c, hc⟩ : B) • w.1 : S)) : G) = (w.1 : G) := congrArg Subtype.val hfix
  have h2 : ((((⟨c, hc⟩ : B) • w.1 : S)) : G) = c * (w.1 : G) * c⁻¹ := by
    change (((S.normalizerMonoidHom) (Subgroup.inclusion hBS ⟨c, hc⟩)) w.1 : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [h2] at h1
  calc c * (w.1 : G) = c * (w.1 : G) * c⁻¹ * c := by group
    _ = (w.1 : G) * c := by rw [h1]

theorem mem_of_pow_eq_one_of_isSCp {p : ℕ} {B : Subgroup G} (hB : IsSCp p ⊤ B) {c : G}
    (hc : c ∈ Subgroup.centralizer (B : Set G)) (hcp : c ^ p = 1) : c ∈ B := by
  have hz : IsElemAbelian p (Subgroup.zpowers c) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := a.2
      obtain ⟨n, hn⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  have hBc : B ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := hy
    have hbc : Commute b c := Subgroup.mem_centralizer_iff.1 hc b hb
    exact (Commute.zpow_right hbc m).symm.eq
  have hE := isElemAbelian_sup_of_commute hB.2.1 hz hBc
  have := hB.2.2 _ le_top hE le_sup_left
  rw [← this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C
