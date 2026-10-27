module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem Sec10Ctx.swap [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (h : Sec10Ctx G t L S z K1 K2) : Sec10Ctx G t L S z K2 K1 :=
  { toSec10Z := h.toSec10Z, pocket1 := h.pocket2, pocket2 := h.pocket1, ne := h.ne.symm }

theorem sec10KS_card_sup [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) : Nat.card ↥(K1 ⊔ K2) = 288 := by
  obtain ⟨K1', K2', _, _, _, _, _, hsup', hrel, _⟩ :=
    hP5 G L hpsp z hctx.toSec10Z.pocket
  have hsup : K1 ⊔ K2 = oTwoRes (L ⊓ centralizer ({z} : Set G)) :=
    sec10K0_pockets_sup hP5 hpsp hctx
  have hKY : K1 ⊔ K2 ≤ L ⊓ centralizer ({z} : Set G) :=
    sup_le hctx.pocket1.2.1 hctx.pocket2.2.1
  have hidx : ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G))).index = 2 := by
    rw [hsup, hsup']
    exact hrel
  have hcardY : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 576 :=
    hC5 G L hpsp z hctx.toSec10Z.pocket
  have h1 := Subgroup.index_mul_card ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G)))
  rw [hcardY, hidx] at h1
  have h2 : Nat.card ↥((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G))) =
      Nat.card ↥(K1 ⊔ K2) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
  rw [h2] at h1
  omega

private theorem sec10KS_card_sup_mul_card_inf [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : ↥H × ↥K →* ↥(H ⊔ K) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hc q.1 q.1.2 p.2 p.2.2]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    let e : ↥f.ker ≃ ↥(H ⊓ K) :=
      { toFun := fun x =>
          ⟨(x.1.1 : G), x.1.1.2, by
            have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := by
              have := congrArg (fun y : ↥(H ⊔ K) => (y : G)) x.2
              simpa [f] using this
            exact (eq_inv_of_mul_eq_one_left hx) ▸ K.inv_mem x.1.2.2⟩
        invFun := fun a =>
          ⟨(⟨a.1, a.2.1⟩, ⟨a.1⁻¹, K.inv_mem a.2.2⟩), by
            apply Subtype.ext
            simp [f]⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := by
              have := congrArg (fun y : ↥(H ⊔ K) => (y : G)) x.2
              simpa [f] using this
            exact (eq_inv_of_mul_eq_one_right hx).symm
        right_inv := fun a => by
          apply Subtype.ext
          rfl }
    exact Nat.card_congr e
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh, k, hk, hkx⟩ := exists_mul_of_mem_sup_of_commute hc x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hkx.symm⟩
  have hquot : Nat.card ((↥H × ↥K) ⧸ f.ker) = Nat.card ↥(H ⊔ K) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).trans
      (by rw [hrange, Subgroup.card_top])
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_prod, hquot, hker] at hcard
  exact hcard.symm

private theorem sec10KS_bound [Finite G] (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    Nat.card ↥(K1 ⊓ K2) ≤ 2 * Nat.card (CFSG.oddCore ↥K1) := by
  obtain ⟨e1⟩ := hctx.pocket1.2.2.2
  let φ : ↥(K1 ⊓ K2) →* (↥K1 ⧸ CFSG.oddCore ↥K1) :=
    (QuotientGroup.mk' (CFSG.oddCore ↥K1)).comp (Subgroup.inclusion inf_le_left)
  have hcenter : Nat.card (Subgroup.center (↥K1 ⧸ CFSG.oddCore ↥K1)) = 2 := by
    rw [show Nat.card (Subgroup.center (↥K1 ⧸ CFSG.oddCore ↥K1)) =
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) from
      Nat.card_congr (Subgroup.centerCongr e1).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  have hD1center : (K1 ⊓ K2).subgroupOf K1 ≤ Subgroup.center ↥K1 := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (sec10Z_comm hP5 hpsp hctx (y : G) y.2 (x : G) hx.2)
  have hrange : φ.range ≤ Subgroup.center (↥K1 ⧸ CFSG.oddCore ↥K1) := by
    have h1 : φ.range =
        ((K1 ⊓ K2).subgroupOf K1).map (QuotientGroup.mk' (CFSG.oddCore ↥K1)) := by
      change ((QuotientGroup.mk' (CFSG.oddCore ↥K1)).comp
        (Subgroup.inclusion inf_le_left)).range =
        ((K1 ⊓ K2).subgroupOf K1).map (QuotientGroup.mk' (CFSG.oddCore ↥K1))
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [h1]
    exact (Subgroup.map_mono hD1center).trans
      (Subgroup.map_center_le_center (f := QuotientGroup.mk' (CFSG.oddCore ↥K1))
        (QuotientGroup.mk'_surjective (CFSG.oddCore ↥K1)))
  have hker_le : Nat.card φ.ker ≤ Nat.card (CFSG.oddCore ↥K1) := by
    let g : ↥φ.ker → ↥(CFSG.oddCore ↥K1) := fun x =>
      ⟨Subgroup.inclusion inf_le_left x.1, by
        have hx : QuotientGroup.mk' (CFSG.oddCore ↥K1)
            (Subgroup.inclusion inf_le_left x.1) = 1 := x.2
        exact (QuotientGroup.eq_one_iff (N := CFSG.oddCore ↥K1)
          (Subgroup.inclusion inf_le_left x.1)).mp hx⟩
    exact Nat.card_le_card_of_injective g (by
      intro x y hxy
      exact Subtype.ext
        (Subgroup.inclusion_injective inf_le_left (Subtype.ext_iff.mp hxy)))
  have hran_le : Nat.card φ.range ≤ 2 := by
    have := Subgroup.card_le_of_le hrange
    rwa [hcenter] at this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hquot : Nat.card (↥(K1 ⊓ K2) ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  calc Nat.card ↥(K1 ⊓ K2)
      = Nat.card (↥(K1 ⊓ K2) ⧸ φ.ker) * Nat.card φ.ker := hcard
    _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot]
    _ ≤ 2 * Nat.card (CFSG.oddCore ↥K1) := Nat.mul_le_mul hran_le hker_le

private theorem sec10KS_oddCore_card [Finite G] (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    Nat.card ↥K1 = 24 ∧ Nat.card ↥K2 = 24 ∧ Nat.card ↥(K1 ⊓ K2) = 2 ∧
      Nat.card (CFSG.oddCore ↥K1) = 1 ∧ Nat.card (CFSG.oddCore ↥K2) = 1 := by
  obtain ⟨e1⟩ := hctx.pocket1.2.2.2
  obtain ⟨e2⟩ := hctx.pocket2.2.2.2
  have hquot1 : Nat.card (↥K1 ⧸ CFSG.oddCore ↥K1) = 24 := by
    rw [Nat.card_congr e1.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hquot2 : Nat.card (↥K2 ⧸ CFSG.oddCore ↥K2) = 24 := by
    rw [Nat.card_congr e2.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcardK1 : Nat.card ↥K1 = Nat.card (CFSG.oddCore ↥K1) * 24 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K1), hquot1,
      Nat.mul_comm]
  have hcardK2 : Nat.card ↥K2 = Nat.card (CFSG.oddCore ↥K2) * 24 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K2), hquot2,
      Nat.mul_comm]
  have hprod : Nat.card ↥(K1 ⊔ K2) * Nat.card ↥(K1 ⊓ K2) = Nat.card ↥K1 * Nat.card ↥K2 :=
    sec10KS_card_sup_mul_card_inf (sec10Z_comm hP5 hpsp hctx)
  rw [sec10KS_card_sup hP5 hC5 hpsp hctx, hcardK1, hcardK2] at hprod
  have hd_eq : Nat.card ↥(K1 ⊓ K2) =
      2 * Nat.card (CFSG.oddCore ↥K1) * Nat.card (CFSG.oddCore ↥K2) := by
    have h : (288 : ℕ) * Nat.card ↥(K1 ⊓ K2) =
        (288 : ℕ) * (2 * Nat.card (CFSG.oddCore ↥K1) * Nat.card (CFSG.oddCore ↥K2)) := by
      rw [hprod]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hb1 := sec10KS_bound hP5 hpsp hctx
  have hb2 : Nat.card ↥(K1 ⊓ K2) ≤ 2 * Nat.card (CFSG.oddCore ↥K2) := by
    have h := sec10KS_bound hP5 hpsp hctx.swap
    rwa [inf_comm] at h
  have hm2 : Nat.card (CFSG.oddCore ↥K2) = 1 := by
    have h : 2 * Nat.card (CFSG.oddCore ↥K1) * Nat.card (CFSG.oddCore ↥K2) ≤
        2 * Nat.card (CFSG.oddCore ↥K1) := by
      rw [← hd_eq]; exact hb1
    have hpos : 0 < 2 * Nat.card (CFSG.oddCore ↥K1) := by
      have := Nat.card_pos (α := ↥(CFSG.oddCore ↥K1))
      omega
    refine le_antisymm ?_ Nat.card_pos
    have hh : (2 * Nat.card (CFSG.oddCore ↥K1)) * Nat.card (CFSG.oddCore ↥K2) ≤
        (2 * Nat.card (CFSG.oddCore ↥K1)) * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left hh hpos
  have hm1 : Nat.card (CFSG.oddCore ↥K1) = 1 := by
    have h : 2 * Nat.card (CFSG.oddCore ↥K1) * Nat.card (CFSG.oddCore ↥K2) ≤
        2 * Nat.card (CFSG.oddCore ↥K2) := by
      rw [← hd_eq]; exact hb2
    rw [hm2, mul_one] at h
    have hle : Nat.card (CFSG.oddCore ↥K1) ≤ 1 := by
      have hh : (2 : ℕ) * Nat.card (CFSG.oddCore ↥K1) ≤ (2 : ℕ) * 1 := by simpa using h
      exact Nat.le_of_mul_le_mul_left hh (by norm_num)
    exact le_antisymm hle Nat.card_pos
  have hd2 : Nat.card ↥(K1 ⊓ K2) = 2 := by
    rw [hd_eq, hm1, hm2]
  exact ⟨by rw [hcardK1, hm1, one_mul], by rw [hcardK2, hm2, one_mul], hd2, hm1, hm2⟩

theorem sec10KS_main [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    Nat.card ↥K1 = 24 ∧ Nat.card ↥K2 = 24 ∧ K1 ⊓ K2 = zpowers z := by
  obtain ⟨hK1, hK2, hD, -, -⟩ := sec10KS_oddCore_card hP5 hC5 hpsp hctx
  refine ⟨hK1, hK2, ?_⟩
  have hle : zpowers z ≤ K1 ⊓ K2 :=
    Subgroup.zpowers_le.mpr ⟨hctx.pocket1.1, hctx.pocket2.1⟩
  have hcardz : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers, hctx.toSec10Z.pocket.1]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hD.trans hcardz.symm))).symm

theorem sec10KS_equiv [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    Nonempty (↥K1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty (↥K2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨-, -, -, hm1, hm2⟩ := sec10KS_oddCore_card hP5 hC5 hpsp hctx
  obtain ⟨e1⟩ := hctx.pocket1.2.2.2
  obtain ⟨e2⟩ := hctx.pocket2.2.2.2
  have hb1 : CFSG.oddCore ↥K1 = ⊥ := Subgroup.eq_bot_of_card_eq (CFSG.oddCore ↥K1) hm1
  have hb2 : CFSG.oddCore ↥K2 = ⊥ := Subgroup.eq_bot_of_card_eq (CFSG.oddCore ↥K2) hm2
  refine ⟨?_, ?_⟩
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq hb1).trans
      QuotientGroup.quotientBot).symm.trans e1⟩
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq hb2).trans
      QuotientGroup.quotientBot).symm.trans e2⟩

end CFSG.OddStandard.SmallF3.Omega