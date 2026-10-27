module

public import CFSG.GH74.GLS.Stage1.Thm4.L98c
public import CFSG.GH74.GLS.Stage1.Thm4.Core98b
public import CFSG.GH74.GLS.Stage1.Thm4.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

theorem odd_card_pPrimeCore {X : Type*} [Group X] [Finite X] : Odd (Nat.card (pPrimeCore 2 X)) :=
  (Nat.coprime_two_left).1 pPrimeCore_coprime_card

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem z_ord : orderOf z = 2 := h.std.z_ord

theorem z_cen : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem z_mem_S : z ∈ S := mem_sylow_of_central h.z_ord h.std.sylow

theorem K_normal_C : (K.subgroupOf (Cz z)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ K := hn
  have := (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer g.2) n).1 hn'
  rw [Subgroup.mem_subgroupOf]
  simpa using this

theorem sylowC : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf (Cz z)) ⊤ := by
  have h1 := h.std.sylow
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (Cz z), Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 h.S_le, Subgroup.map_top, Subgroup.range_subtype]
  exact h1

theorem hypC (hF : Step9_8_Fstar) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) :
    Hyp5B (↥(Cz z) ⧸ pPrimeCore 2 ↥(Cz z))
      ((K.subgroupOf (Cz z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)))) n :=
  h.hyp5B hF hn8 hn11 hcov

theorem zcen (hB : IVK_5_1g) (hF : Step9_8_Fstar) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) :
    ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z := by
  intro w hwS hwc hw2
  haveI : (K.subgroupOf (Cz z)).Normal := h.K_normal_C
  have hyp := h.hypC hF hn8 hn11 hcov
  have hzS := h.z_mem_S
  have hmk := core_center (N := pPrimeCore 2 ↥(Cz z)) (K := K.subgroupOf (Cz z))
    (S := S.subgroupOf (Cz z)) hB hyp odd_card_pPrimeCore h.sylowC
    (zc := ⟨z, h.z_cen⟩) h.z_mem (fun k hk => Subtype.ext (h.z_comm hk))
    (mk'_ne_one_of_orderOf_two odd_card_pPrimeCore (by rw [Subgroup.orderOf_mk]; exact h.z_ord))
    ⟨w, h.S_le hwS⟩ hwS (fun s hs => Subtype.ext (hwc s hs))
    (by rw [Subgroup.orderOf_mk]; exact hw2)
  have hwS' : (⟨w, h.S_le hwS⟩ : ↥(Cz z)) ∈ S.subgroupOf (Cz z) := hwS
  have hzS' : (⟨z, h.z_cen⟩ : ↥(Cz z)) ∈ S.subgroupOf (Cz z) := hzS
  have hx : (⟨w, h.S_le hwS⟩ : ↥(Cz z))⁻¹ * ⟨z, h.z_cen⟩ ∈
      S.subgroupOf (Cz z) ⊓ pPrimeCore 2 ↥(Cz z) :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hwS') hzS', QuotientGroup.eq.1 hmk⟩
  rw [inf_eq_bot_of_odd h.sylowC.isPGroup odd_card_pPrimeCore] at hx
  have h1 := inv_mul_eq_one.1 (Subgroup.mem_bot.1 hx)
  exact congrArg Subtype.val h1

theorem sylowG (hB : IVK_5_1g) (hF : Step9_8_Fstar) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) :
    CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ IsCentralInvolution z :=
  sylow_central_of_zcen h.z_ord h.std.sylow h.z_mem_S (h.zcen hB hF hn8 hn11 hcov)

theorem t_mem_K (h96 : Lemma9_6) (hF : Step9_8_Fstar) {n : ℕ} (hcov : IsDoubleCoverOfAlt Lh n) :
    t ∈ K := by
  obtain ⟨k, hk1, -⟩ := h96 G Lh z t S K h.std n hcov K h.std.K_rigid
  have hk1' : (t * (k : G)⁻¹) ∈ normalizer (K : Set G) ∧
      (t * (k : G)⁻¹) ∈ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) ∧
      ∀ x ∈ K, ⁅x, t * (k : G)⁻¹⁆ ∈ pPrimeCoreOf 2 K := hk1
  have htC : t ∈ Cz z := h.std.t_cen
  have hkC : (k : G) ∈ Cz z := h.K_le k.2
  have hcC : t * (k : G)⁻¹ ∈ Cz z := mul_mem htC (inv_mem hkC)
  have hsup := hF G Lh z t S K h.std h.r1 h.q1 _ hcC fun x hx =>
    h.pPrimeCoreOf_le_Oz (hk1'.2.2 x hx)
  have htKO : t ∈ K ⊔ Oz z := by
    have h1 : t * (k : G)⁻¹ ∈ K ⊔ Oz z :=
      (sup_le_sup_right ((Subgroup.zpowers_le).2 h.z_mem) _) hsup
    have h2 : (k : G) ∈ K ⊔ Oz z := Subgroup.mem_sup_left k.2
    have := mul_mem h1 h2
    simpa using this
  have h3 := mem_sup_subgroupOf_of_mem h.K_le (c := ⟨t, htC⟩) htKO
  haveI := h.K_normal_C
  have ht2 : (⟨t, htC⟩ : ↥(Cz z)) ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← h.std.t_ord]
    exact pow_orderOf_eq_one t
  exact mem_of_mem_sup_odd (K := K.subgroupOf (Cz z)) (N := pPrimeCore 2 ↥(Cz z))
    odd_card_pPrimeCore ht2 h3

theorem eq_z_of_zStar {n : ℕ} (hcov : IsDoubleCoverOfAlt Lh n) {x : G} (hxK : x ∈ K)
    (hx2 : orderOf x = 2) (hxc : ∀ k ∈ K, ⁅k, x⁆ ∈ pPrimeCoreOf 2 K) : x = z := by
  obtain ⟨e⟩ := h.std.K_rigid.2
  have hcov' : IsDoubleCoverOfAlt (HatT K) n := isDoubleCoverOfAlt_congr e.symm hcov
  have hxsq : x * x = 1 := by rw [← pow_two, ← hx2]; exact pow_orderOf_eq_one x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxsq
  have hcomm : ∀ g : ↥K, ⁅g, (⟨x, hxK⟩ : ↥K)⁆ ∈ pPrimeCore 2 ↥K := by
    intro g
    obtain ⟨y, hy, hyc⟩ := hxc g g.2
    have : y = ⁅g, (⟨x, hxK⟩ : ↥K)⁆ := Subtype.ext (hyc.trans rfl)
    rwa [this] at hy
  have key := eq_of_central_involutions (X := ↥K) (M := pPrimeCore 2 ↥K) odd_card_pPrimeCore
    hcov'.2.1 (a := ⟨x, hxK⟩) (b := ⟨z, h.z_mem⟩) (by rw [Subgroup.orderOf_mk]; exact hx2)
    (by rw [Subgroup.orderOf_mk]; exact h.z_ord) (fun g => Subtype.ext (h.z_comm g.2)) ?_
  · exact congrArg Subtype.val key
  · intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.2
    set a : ↥K := ⟨x, hxK⟩ with ha
    have hai : a⁻¹ = a := Subtype.ext hxi
    have e1 : (g * a)⁻¹ * (a * g) = (⁅g⁻¹, a⁆)⁻¹ := by
      have h1 : (g * a)⁻¹ * (a * g) = a⁻¹ * g⁻¹ * a * g := by group
      have h2 : (⁅g⁻¹, a⁆)⁻¹ = a * g⁻¹ * a⁻¹ * g := by simp only [commutatorElement_def]; group
      rw [h1, h2, hai]
    rw [e1]
    exact inv_mem (hcomm g⁻¹)

theorem isConj_z_t {n : ℕ} (hcov : IsDoubleCoverOfAlt Lh n) : IsConj z t := by
  obtain ⟨g, hg⟩ := h.std.t_conj
  have hKz : Kz Lh z = K := by
    unfold Kz
    rw [h.r1]
    exact sSup_singleton
  rw [hKz] at hg
  have hg' : g⁻¹ * t * g ∈ K ∧ (g⁻¹ * t * g) ∈ normalizer (K : Set G) ∧
      (g⁻¹ * t * g) ∈ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) ∧
      ∀ k ∈ K, ⁅k, g⁻¹ * t * g⁆ ∈ pPrimeCoreOf 2 K := hg
  have hx2 : orderOf (g⁻¹ * t * g) = 2 := by
    have := orderOf_conj_eq' g⁻¹ t
    rw [inv_inv] at this
    rw [this]
    exact h.std.t_ord
  have hz := h.eq_z_of_zStar hcov hg'.1 hx2 hg'.2.2.2
  exact isConj_iff.2 ⟨g, by rw [← hz]; group⟩

end Ctx98

end CFSG.GH74.GLS.Stage1.Thm4
