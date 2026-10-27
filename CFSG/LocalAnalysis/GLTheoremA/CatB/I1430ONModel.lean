module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.RankThree.Native.ONTripleRed
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.RankThree.PartTwo.Sec14.ONCoverProofModel
import CFSG.HardMathSupport.Solomon.Coordinator.ON25K0
import CFSG.HardMathSupport.Solomon.Coordinator.ON25Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

attribute [local irreducible] dotProduct

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Native.ONTriple (GM zG xG K0G wordN P0G P0Syl P0Syl_coe relG zG_central
  center_GM aut_fix_z_inner exists_word_conj_x0 conj_not_mem_zpowers centralizer_x0_eq
  K0G_le_centralizer)
open CFSG.HardMathSupport.Solomon.Coordinator (on25_K0_quasisimple on25_card_center_K0
  on25_glaPComponent_self on25_primeCore_eq_bot)

set_option linter.unusedSectionVars false


private theorem isPGroup_zpowers_nine {G : Type*} [Group G] {g : G} (hg : g ^ 9 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
  refine ⟨2, Subtype.ext ?_⟩
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, hg, one_zpow, Subgroup.coe_one]

theorem i1430ON_exists_conj_x0 (β : GM ≃* GM) (h3 : ∀ x, β (β (β x)) = x)
    (h1 : ∃ x, β x ≠ x) :
    ∃ m : GM, ∀ x, β x = m * (xG 0 * (m⁻¹ * x * m) * (xG 0)⁻¹) * m⁻¹ := by
  classical
  have hz3 : zG ^ 3 = 1 := relG.xcube
  have hz1 : zG ≠ 1 := relG.x1
  have hcen : ∀ a : GM, a ∈ Subgroup.zpowers zG ↔ ∀ g : GM, g * a = a * g := fun a => by
    rw [← center_GM, Subgroup.mem_center_iff]
  have hβc : β zG ∈ Subgroup.zpowers zG := (hcen _).2 fun g => by
    obtain ⟨n, rfl⟩ := β.surjective g
    rw [← map_mul β, ← map_mul β, zG_central n]
  have hβc' := (mem_zpowers_iff_mem_range_orderOf (x := zG) (y := β zG)).1 hβc
  rw [orderOf_eq_prime hz3 hz1, Finset.mem_image] at hβc'
  obtain ⟨i, hi, hiz⟩ := hβc'
  rw [Finset.mem_range] at hi
  have hβz : β zG = zG := by
    interval_cases i
    · exact absurd (β.injective (by rw [← hiz, pow_zero, map_one])) hz1
    · rw [← hiz, pow_one]
    · have e2 : β (zG ^ 2) = zG := by
        rw [map_pow, ← hiz, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul,
          pow_one]
      have h := h3 zG
      rw [← hiz, e2, ← hiz] at h
      exact absurd (mul_left_cancel (show zG * zG = zG * 1 by rw [mul_one, ← pow_two, h])) hz1
  obtain ⟨g, hg⟩ := aut_fix_z_inner β hβz
  have hgz : g ∉ Subgroup.zpowers zG := fun hgz => by
    obtain ⟨x, hx⟩ := h1
    exact hx (by rw [hg x, ← (hcen g).1 hgz x, mul_inv_cancel_right])
  have hg3 : g ^ 3 ∈ Subgroup.zpowers zG := (hcen _).2 fun x => by
    have e : β (β (β x)) = g ^ 3 * x * (g ^ 3)⁻¹ := by
      rw [hg, hg, hg, pow_three]
      group
    exact (mul_inv_eq_iff_eq_mul.1 (e.symm.trans (h3 x))).symm
  have hg9 : g ^ 9 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg3
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hz3, one_zpow]
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_nine hg9).exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hgP : (MulAut.conj n).toMonoidHom g ∈ P0G := by
    rw [← P0Syl_coe, ← hn, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map_of_mem _ (hP (Subgroup.mem_zpowers g))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hgP (conj_not_mem_zpowers hgz n)
  obtain ⟨m, hge⟩ : ∃ m : GM, g = m * (xG 0 * zG ^ c) * m⁻¹ :=
    ⟨n⁻¹ * wordN w, by rw [← hwc]; simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  refine ⟨m, fun x => ?_⟩
  have hzc : zG ^ c * (m⁻¹ * x * m) = m⁻¹ * x * m * zG ^ c :=
    (Commute.pow_left (show Commute zG (m⁻¹ * x * m) from zG_central _) c).eq
  rw [hg x, hge]
  calc _ = m * xG 0 * (zG ^ c * (m⁻¹ * x * m)) * (zG ^ c)⁻¹ * (xG 0)⁻¹ * m⁻¹ := by group
    _ = _ := by rw [hzc]; group

theorem i1430ON_card_center_pQuot {Q : Type} [Group Q] [Finite Q] {K I₀ : Subgroup Q} {y : Q}
    (ι : GM →* Q) (hι : Function.Injective ι) (hK : ι.range = K)
    (hy : ∀ x, y * ι x * y⁻¹ = ι (xG 0 * x * (xG 0)⁻¹))
    (hI : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Q)) I₀) :
    Nat.card (Subgroup.center (PQuot 3 I₀)) = 3 := by
  have hmem : ∀ x, ι x ∈ Subgroup.centralizer ({y} : Set Q) ↔
      x ∈ Subgroup.centralizer {xG 0} := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : xG 0 * x * (xG 0)⁻¹ = x := hι (by rw [← hy, ← h, mul_inv_cancel_right])
      calc x * xG 0 = xG 0 * x * (xG 0)⁻¹ * xG 0 := by rw [h']
        _ = xG 0 * x := by group
    · intro h
      have h' := hy x
      rw [← h, mul_inv_cancel_right] at h'
      calc ι x * y = y * ι x * y⁻¹ * y := by rw [h']
        _ = y * ι x := by group
  have hIK : I₀ ≤ ι.range := by rw [hK]; exact hI.1.trans inf_le_left
  have hmap : (I₀.comap ι).map ι = I₀ := Subgroup.map_comap_eq_self hIK
  have hperf : ⁅I₀.comap ι, I₀.comap ι⁆ = I₀.comap ι := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmap, glaPComponent_perfect hI]
  haveI : Group.IsPerfect ↥(I₀.comap ι) := Subgroup.isPerfect_iff.2 hperf
  have hI'K : I₀.comap ι ≤ K0G :=
    CFSG.RankThree.PartTwo.Sec15.ONCoverCent.le_K0_of_isPerfect fun x hx =>
      (hmem x).1 ((hI.1.trans inf_le_right) hx)
  have hIK₁ : I₀ ≤ K0G.map ι := by
    rw [← hmap]
    exact Subgroup.map_mono hI'K
  have hK₁C : K0G.map ι ≤ K ⊓ Subgroup.centralizer ({y} : Set Q) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨by rw [← hK]; exact ⟨x, rfl⟩, (hmem x).2 (K0G_le_centralizer hx)⟩
  have hI₁ : GLAPComponent 3 (K0G.map ι) I₀ := glaPComponent_of_le Nat.prime_three hI hIK₁ hK₁C
  let e₁ : ↥K0G ≃* ↥(K0G.map ι) := K0G.equivMapOfInjective ι hι
  have hq₁ : CFSG.Open.IsQuasisimple ↥(K0G.map ι) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₁ on25_K0_quasisimple
  have hc₁ : Nat.card (Subgroup.center ↥(K0G.map ι)) = 3 := by
    have hc : (Subgroup.center ↥K0G).map e₁.toMonoidHom = Subgroup.center ↥(K0G.map ι) :=
      Subgroup.map_center_eq e₁
    rw [← hc, Subgroup.card_map_of_injective e₁.injective]
    exact on25_card_center_K0
  have hZ₁ : IsPGroup 3 (Subgroup.center ↥(K0G.map ι)) :=
    IsPGroup.of_card (n := 1) (by rw [hc₁, pow_one])
  have h3₁ : 3 ∣ Nat.card (K0G.map ι) := by
    rw [← Nat.card_congr e₁.toEquiv, centralizer_x0_eq.2]
    norm_num
  have hcore := on25_primeCore_eq_bot hq₁ hZ₁ h3₁
  let e₂ : (↥(K0G.map ι) ⧸ GLAPPrimeCore 3 ↥(K0G.map ι)) ≃* ↥(K0G.map ι) :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hY : CFSG.Open.IsQuasisimple (↥(K0G.map ι) ⧸ GLAPPrimeCore 3 ↥(K0G.map ι)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂.symm hq₁
  have heq : I₀ = K0G.map ι :=
    glaPComponent_eq_of_isQuasisimple hY hI₁ (on25_glaPComponent_self hq₁ hZ₁ h3₁)
  rw [heq]
  have hc : (Subgroup.center (PQuot 3 (K0G.map ι))).map e₂.toMonoidHom =
      Subgroup.center ↥(K0G.map ι) := Subgroup.map_center_eq e₂
  calc Nat.card (Subgroup.center (PQuot 3 (K0G.map ι)))
      = Nat.card ((Subgroup.center (PQuot 3 (K0G.map ι))).map e₂.toMonoidHom) :=
        (Subgroup.card_map_of_injective e₂.injective).symm
    _ = 3 := by rw [hc]; exact hc₁

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
