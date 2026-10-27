module

public import CFSG.GH74.GLS.Stage1.Main.P49BarA
public import CFSG.GH74.GLS.Stage1.Main.P49Fus
public import CFSG.GH74.GLS.Stage1.Main.P49Lift
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement

section BarB

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem bar_normal49 (h : Ctx49 G z S K F U x y) : (imgBar z K).Normal := by
  have hn : (K.subgroupOf (Cz z)).Normal := by
    constructor
    intro n hn g
    have hg := (mem_normalizer_iff.1 (h.std.toStd6r1.normalizes_K g.2) (n : G)).1 hn
    exact hg
  exact hn.map (piC z) (QuotientGroup.mk'_surjective _)

theorem bar_quasi49 (h : Ctx49 G z S K F U x y) : IsQuasisimple ↥(imgBar z K) := by
  have hc1 := h.std.comp_isPCompIn
  obtain ⟨e⟩ := imgBar_equiv hc1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (TwoThin.isQuasisimple_hat hc1)

theorem bar_center49 (h44 : II4_44) (h : Ctx49 G z S K F U x y) :
    Nat.card ↥(center ↥(imgBar z K)) = 2 := by
  have hc1 := h.std.comp_isPCompIn
  have hsl := h44 G h.std.simple z h.std.orderOf_z K hc1 h.std.comp_pRank
  obtain ⟨e⟩ := imgBar_equiv hc1
  have := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hsl.2] at this
  exact this.symm

theorem bar_comp49 (hK1 : ∀ L : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) L → L = K) :
    ∀ L : Subgroup (CentralizerBar z), IsComponent L → L ≤ imgBar z K := by
  intro Lb hLb
  obtain ⟨L₀, hL₀, hmap⟩ := exists_pComponent_of_component hLb
  have hsub : (L₀.map (Cz z).subtype).subgroupOf (Cz z) = L₀ := by
    rw [Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective (Cz z).subtype_injective L₀
  have hcomp : IsPCompIn 2 (centralizer ({z} : Set G)) (L₀.map (Cz z).subtype) := by
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [hsub]
    exact hL₀
  have hKe := hK1 _ hcomp
  have hL₀eq : L₀ = K.subgroupOf (Cz z) := by
    rw [← hKe, hsub]
  rw [← hmap, hL₀eq]
  exact le_rfl

theorem bar_sylow49 (h : Ctx49 G z S K F U x y) : CFSG.ABGLocalTools.IsSylowOf 2 (imgBar z S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (piC z) := QuotientGroup.mk'_surjective _
  obtain ⟨Q, hQ⟩ := h.std.sylow.exists_sylow_eq_subgroupOf
  have hcoe : ((Q.mapSurjective hsurj : Sylow 2 (CentralizerBar z)) : Subgroup (CentralizerBar z)) =
      imgBar z S := by
    rw [Sylow.coe_mapSurjective, hQ]
    rfl
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hcoe]
    exact (Q.mapSurjective hsurj).isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hcoe]
    exact (Q.mapSurjective hsurj).not_dvd_index


theorem subgroupOf_normal49 (h : Ctx49 G z S K F U x y) : (K.subgroupOf (Cz z)).Normal := by
  constructor
  intro n hn g
  have hg := (mem_normalizer_iff.1 (h.std.toStd6r1.normalizes_K g.2) (n : G)).1 hn
  exact hg

theorem bar_P49 (h : Ctx49 G z S K F U x y) {n : ℕ} (hPn : IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n) :
    IVK.IsQuaternionTwoGroup ↥(imgBar z S ⊓ imgBar z K) n := by
  have hS := h.std.sylow.isPGroup
  rw [imgBar_inf_of_normal49 hS (subgroupOf_normal49 h)]
  obtain ⟨e⟩ := imgBar_equiv_of_isPGroup49 (hS.to_inf_left : IsPGroup 2 ↥(S ⊓ K))
    ((inf_le_left : S ⊓ K ≤ S).trans h.std.sylow.le)
  obtain ⟨hn3, ⟨e2⟩⟩ := hPn
  exact ⟨hn3, ⟨e.symm.trans e2⟩⟩

theorem bar_Q49 (h : Ctx49 G z S K F U x y) {n : ℕ}
    (hQn : IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n) :
    IVK.IsQuaternionTwoGroup ↥(imgBar z S ⊓ centralizer (imgBar z K : Set (CentralizerBar z))) n := by
  have hS := h.std.sylow.isPGroup
  rw [imgBar_inf_centralizer49 h.std.comp_isPCompIn (fun c hc => h.std.toStd6r1.normalizes_K hc)]
  obtain ⟨e⟩ := imgBar_equiv_of_isPGroup49 (hS.to_inf_left : IsPGroup 2 ↥(S ⊓ cSec K))
    ((inf_le_left : S ⊓ cSec K ≤ S).trans h.std.sylow.le)
  obtain ⟨hn3, ⟨e2⟩⟩ := hQn
  exact ⟨hn3, ⟨e.symm.trans e2⟩⟩

theorem bar_card49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {n : ℕ}
    (hPn : IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n) (hQn : IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n) :
    Nat.card ↥(imgBar z S) = 2 ^ (2 * n) := by
  obtain ⟨u₁, u₂, c⟩ := setup9_of_ctx49 hc h
  obtain ⟨e⟩ := imgBar_equiv_of_isPGroup49 h.std.sylow.isPGroup h.std.sylow.le
  rw [← Nat.card_congr e.toEquiv]
  have h1 := c.card_S
  have h2 := c.card_R
  rw [R1.card_of_quat hPn, R1.card_of_quat hQn] at h2
  rw [h1]
  calc 2 * Nat.card ↥(S ⊓ K ⊔ S ⊓ cSec K) = Nat.card ↥(S ⊓ K ⊔ S ⊓ cSec K) * 2 := by ring
    _ = 2 ^ n * 2 ^ n := h2
    _ = 2 ^ (2 * n) := by rw [two_mul, pow_add]


omit [Finite G] in
theorem mem_sup_zpowers_inv49 {H : Subgroup G} {y : G} (hy2 : y * y = 1)
    (hyn : ∀ h ∈ H, y * h * y⁻¹ ∈ H) {w : G} (hw : w ∈ H ⊔ zpowers y) :
    w ∈ H ∨ ∃ q ∈ H, w = q * y := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hyn g hg, fun hg => ?_⟩
    have := hyn _ hg
    have e : y * (y * g * y⁻¹) * y⁻¹ = g := by
      rw [hyinv]
      calc y * (y * g * y) * y = (y * y) * g * (y * y) := by group
        _ = g := by rw [hy2]; group
    rwa [e] at this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H _ hle] at hw
  obtain ⟨q, hq, w', hw', rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hw')
  have ht' : y ^ (2 : ℤ) = 1 := by rw [zpow_two, hy2]
  rw [zpow_eq_zpow_emod k ht']
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [hk, zpow_zero, mul_one]
    exact hq
  · right
    rw [hk, zpow_one]
    exact ⟨q, hq, rfl⟩


theorem bar_rot49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {n : ℕ}
    (hQn : IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n) :
    ∃ s ∈ imgBar z S, ∀ m : ℕ, s ^ m ∈ imgBar z K → 2 ^ (n - 1) ∣ m := by
  obtain ⟨u₁, u₂, c⟩ := setup9_of_ctx49 hc h
  have hS := h.std.sylow.isPGroup
  have hSC : S ≤ Cz z := h.std.sylow.le
  have hy2 := y_sq_one49 h
  obtain ⟨hyQ, ⟨m, hm4, ⟨e⟩⟩⟩ := y_data49 h
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  have hYS : (S ⊓ cSec K) ⊔ zpowers y ≤ S :=
    sup_le inf_le_left (Subgroup.zpowers_le.2 h.y_S)
  have hm3 : 3 ≤ m := by omega
  let a₀ : ↥((S ⊓ cSec K) ⊔ zpowers y) := e.symm (CFSG.Semidihedral.r m)
  have haord : orderOf (a₀ : G) = 2 ^ (m - 1) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact CFSG.Semidihedral.orderOf_r m hm3
  have hY : Nat.card ↥((S ⊓ cSec K) ⊔ zpowers y) = 2 ^ m := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Semidihedral.card m hm3
  have hQs : Nat.card ↥(S ⊓ cSec K) = 2 ^ n := R1.card_of_quat hQn
  have hnm : n < m := by
    have hdvd : 2 ^ n ∣ 2 ^ m := by
      rw [← hQs, ← hY]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hle : n ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hyQ
      have hcard : Nat.card ↥((S ⊓ cSec K) ⊔ zpowers y) ≤ Nat.card ↥(S ⊓ cSec K) := by
        rw [hY, hQs, heq]
      have heq' : S ⊓ cSec K = (S ⊓ cSec K) ⊔ zpowers y := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
      rw [heq']
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haS : (a₀ : G) ∈ S := hYS a₀.2
  have hac : (a₀ : G) ∈ Cz z := hSC haS
  refine ⟨piC z ⟨(a₀ : G), hac⟩, piC_mem_imgBar hSC haS, fun j hj => ?_⟩
  have hajS : (⟨(a₀ : G), hac⟩ : ↥(Cz z)) ^ j ∈ S.subgroupOf (Cz z) :=
    pow_mem (show (⟨(a₀ : G), hac⟩ : ↥(Cz z)) ∈ S.subgroupOf (Cz z) from haS) j
  have hinf := imgBar_inf_of_normal49 (K := K) hS (subgroupOf_normal49 h)
  have hmem : piC z ((⟨(a₀ : G), hac⟩ : ↥(Cz z)) ^ j) ∈ imgBar z S ⊓ imgBar z K := by
    refine ⟨Subgroup.mem_map_of_mem _ hajS, ?_⟩
    rw [map_pow]
    exact hj
  rw [hinf] at hmem
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.1 hmem
  have hbS : b ∈ S.subgroupOf (Cz z) := hb.1
  have hbeq' : b = (⟨(a₀ : G), hac⟩ : ↥(Cz z)) ^ j := eq_of_piC_eq49 hS hbS hajS hbeq
  have hajP : (a₀ : G) ^ j ∈ S ⊓ K := by
    have : ((b : ↥(Cz z)) : G) ∈ S ⊓ K := hb
    rw [hbeq'] at this
    simpa using this
  have hajY : (a₀ : G) ^ j ∈ (S ⊓ cSec K) ⊔ zpowers y := by
    have : ((a₀ ^ j : ↥((S ⊓ cSec K) ⊔ zpowers y)) : G) ∈ (S ⊓ cSec K) ⊔ zpowers y := (a₀ ^ j).2
    simpa using this
  have hsq1 : ((a₀ : G) ^ j) * ((a₀ : G) ^ j) = 1 := by
    rcases mem_sup_zpowers_inv49 hy2 (fun q hq => c.cfg.Q_norm y h.y_S q hq) hajY with hQ | ⟨q, hq, hqe⟩
    · rcases c.cfg.PQ_inf _ hajP hQ with e1 | e1
      · rw [e1, mul_one]
      · rw [e1, c.hz2]
    · exfalso
      apply h.y_R
      have hyq : y = q⁻¹ * (a₀ : G) ^ j := by rw [hqe]; group
      rw [hyq, hRz]
      exact mul_mem (inv_mem (Subgroup.mem_sup_right hq)) (Subgroup.mem_sup_left hajP)
  have hpow : (a₀ : G) ^ (j * 2) = 1 := by
    rw [pow_mul, sq]
    exact hsq1
  have hdvd1 : 2 ^ (m - 1) ∣ j * 2 := haord ▸ orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : 2 ^ (m - 2) ∣ j := by
    have h3 : 2 ^ (m - 2) * 2 ∣ j * 2 := by
      rwa [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
  exact (pow_dvd_pow 2 (by omega)).trans hdvd2

end BarB

section BarC

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem bar_data49 (hc : Closed49) (h44 : II4_44) (_hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤)
    (hK1 : ∀ L : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) L → L = K)
    (h : Ctx49 G z S K F U x y) {n : ℕ} (hPn : IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n)
    (hQn : IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n) :
    (imgBar z K).Normal ∧ IsQuasisimple ↥(imgBar z K) ∧ Nat.card ↥(center ↥(imgBar z K)) = 2 ∧
      pPrimeCore 2 (CentralizerBar z) = ⊥ ∧
      (∀ L : Subgroup (CentralizerBar z), IsComponent L → L ≤ imgBar z K) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (imgBar z S) ⊤ ∧
      IVK.IsQuaternionTwoGroup ↥(imgBar z S ⊓ imgBar z K) n ∧
      IVK.IsQuaternionTwoGroup ↥(imgBar z S ⊓ centralizer (imgBar z K : Set (CentralizerBar z))) n ∧
      Nat.card ↥(imgBar z S) = 2 ^ (2 * n) ∧
      (∃ s ∈ imgBar z S, ∀ m : ℕ, s ^ m ∈ imgBar z K → 2 ^ (n - 1) ∣ m) :=
  ⟨bar_normal49 h, bar_quasi49 h, bar_center49 h44 h, CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2,
    bar_comp49 hK1, bar_sylow49 h, bar_P49 h hPn, bar_Q49 h hQn, bar_card49 hc h hPn hQn,
    bar_rot49 hc h hQn⟩

end BarC

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
