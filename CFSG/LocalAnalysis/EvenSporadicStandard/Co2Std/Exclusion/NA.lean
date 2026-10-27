module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.WHyp

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
  {W W₁ W₂ : Subgroup G}

theorem card_sup_zpowers_of_mem_normalizer {H : Subgroup G} {z : G}
    (hzN : z ∈ normalizer (H : Set G)) (hz2 : z * z = 1) (hzH : z ∉ H) :
    Nat.card ↥(H ⊔ zpowers z) = 2 * Nat.card H := by
  have hz1 : z ≠ 1 := fun h => hzH (h ▸ H.one_mem)
  have hLE : zpowers z ≤ normalizer (H : Set G) := zpowers_le.2 hzN
  have hcoe : (↑(H ⊔ zpowers z) : Set G) = (H : Set G) * (zpowers z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H (zpowers z) hLE
  let f : ↥H × ↥(zpowers z) → ↥(H ⊔ zpowers z) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.2 p.2.2⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨h1, y1⟩ ⟨h2, y2⟩ heq
    have hprod : (h1 : G) * (y1 : G) = (h2 : G) * (y2 : G) := congrArg Subtype.val heq
    have hmem : (h2 : G)⁻¹ * (h1 : G) = (y2 : G) * (y1 : G)⁻¹ := by
      calc (h2 : G)⁻¹ * (h1 : G)
          = (h2 : G)⁻¹ * ((h1 : G) * (y1 : G)) * (y1 : G)⁻¹ := by group
        _ = (h2 : G)⁻¹ * ((h2 : G) * (y2 : G)) * (y1 : G)⁻¹ := by rw [hprod]
        _ = (y2 : G) * (y1 : G)⁻¹ := by group
    have hH : (h2 : G)⁻¹ * (h1 : G) ∈ H := mul_mem (inv_mem h2.2) h1.2
    have hZ : (y2 : G) * (y1 : G)⁻¹ ∈ zpowers z := mul_mem y2.2 (inv_mem y1.2)
    have hZ' : (h2 : G)⁻¹ * (h1 : G) ∈ zpowers z := by rw [hmem]; exact hZ
    have hone : (h2 : G)⁻¹ * (h1 : G) = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hz2 hZ' with h | h
      · exact h
      · exact absurd (h ▸ hH) hzH
    have hhval : (h1 : G) = (h2 : G) := by
      calc (h1 : G) = (h2 : G) * ((h2 : G)⁻¹ * (h1 : G)) := by group
        _ = (h2 : G) * 1 := by rw [hone]
        _ = (h2 : G) := mul_one _
    have hh : h1 = h2 := Subtype.ext hhval
    have hyval : (y1 : G) = (y2 : G) := by
      have h := hprod
      rw [hhval] at h
      exact mul_left_cancel h
    exact Prod.ext hh (Subtype.ext hyval)
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (H : Set G) * (zpowers z : Set G) := hcoe ▸ x.2
    rw [Set.mem_mul] at hx
    obtain ⟨h, hh, y, hy, hxy⟩ := hx
    exact ⟨(⟨h, hh⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  calc Nat.card ↥(H ⊔ zpowers z) = Nat.card (↥H × ↥(zpowers z)) :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
    _ = Nat.card H * Nat.card (zpowers z) := Nat.card_prod ↥H ↥(zpowers z)
    _ = Nat.card H * 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]
    _ = 2 * Nat.card H := Nat.mul_comm _ _

theorem relIndex_eq_two_of_card_eq {H K : Subgroup G} (hHK : H ≤ K) {n : ℕ}
    (hH : Nat.card H = 2 ^ n) (hK : Nat.card K = 2 ^ (n + 1)) : H.relIndex K = 2 := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_eq_left.mpr hHK, hH, hK, pow_succ, mul_comm (2 ^ n) 2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem exists_conj_le_sylow_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (S : Sylow p X) {V : Subgroup X} (hV : IsPGroup p V) :
    ∃ x : X, ∀ v ∈ V, x * v * x⁻¹ ∈ (S : Subgroup X) := by
  obtain ⟨Q, hVQ⟩ := hV.exists_le_sylow
  haveI : Finite (Sylow p X) := Sylow.finite_of_finiteIndex Q
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X Q S
  refine ⟨x, fun v hv => ?_⟩
  have hxQ : v ∈ (Q : Subgroup X) := hVQ hv
  have hmem : (MulAut.conj x) • v ∈ (MulAut.conj x) • (Q : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul v (MulAut.conj x) Q hxQ
  have hQeq : (MulAut.conj x) • (Q : Subgroup X) = (S : Subgroup X) := by
    rw [← Sylow.coe_subgroup_smul, hx]
  rw [hQeq] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem WHyp.elemAb (h : WHyp G L A T z t W W₁ W₂) : IsElementaryAbelian 2 ↥W := by
  have hw := h.w.elemAb
  rwa [h.sup_eq] at hw

theorem WHyp.z_mem_normalizer (h : WHyp G L A T z t W W₁ W₂) : z ∈ normalizer (W : Set G) :=
  h.e3.M_le (h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))).1

theorem WHyp.le_normalizer (h : WHyp G L A T z t W W₁ W₂) :
    L ⊓ normalizer (A : Set G) ≤ normalizer (W : Set G) :=
  h.hyp.le_M.trans h.e3.M_le

theorem WHyp.R₀_eq (h : WHyp G L A T z t W W₁ W₂) : R₀ A z = W ⊔ zpowers z := by
  have hle : W ⊔ zpowers z ≤ R₀ A z := by
    refine sup_le h.e3.le_R₀ ?_
    rw [zpowers_le]
    exact h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))
  have hcard : Nat.card ↥(W ⊔ zpowers z) = 2 ^ 21 := by
    rw [card_sup_zpowers_of_mem_normalizer h.z_mem_normalizer h.hyp.z_sq h.e3.z_not_mem,
      h.e3.card]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.e2.card_R₀, hcard])).symm

theorem WHyp.mem_A_iff (h : WHyp G L A T z t W W₁ W₂) {w : G} (hw : w ∈ W) :
    w ∈ A ↔ z * w = w * z := by
  constructor
  · intro hwA
    exact (h.hyp.commute_of_mem (h.hyp.jc.le hwA)).symm
  · intro hcomm
    rw [← E3Facts.deltaRestrict_eq_one_iff h.hyp h.e2 h.e3 ⟨w, hw⟩]
    apply Subtype.ext
    show delta z w = 1
    rw [delta]
    have hwz : w * z * w⁻¹ = z := by rw [← hcomm]; group
    rw [hwz, inv_mul_cancel]

theorem WHyp.mul_mem_A_of_mul_self (h : WHyp G L A T z t W W₁ W₂) {r : G} (hr : r ∈ R₀ A z)
    (hrW : r ∉ W) (hr2 : r * r = 1) : z * r ∈ A := by
  have hcoe : (↑(W ⊔ zpowers z) : Set G) = (W : Set G) * (zpowers z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W (zpowers z)
      (zpowers_le.2 h.z_mem_normalizer)
  have hr' : r ∈ (W : Set G) * (zpowers z : Set G) := by
    rw [← hcoe, ← h.R₀_eq]
    exact hr
  rw [Set.mem_mul] at hr'
  obtain ⟨w, hwW, b, hb, hwb⟩ := hr'
  rcases eq_one_or_eq_of_mem_zpowers h.hyp.z_sq hb with hb1 | hbz
  · exfalso
    exact hrW (by rw [← hwb, hb1, mul_one]; exact hwW)
  · have hrwz : r = w * z := by rw [← hwb, hbz]
    have hw2 : w * w = 1 := by
      letI : IsElementaryAbelian 2 ↥W := h.elemAb
      simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) w hwW
    have hzw : z * w = w * z := by
      have h1 : w * (z * w) * z = 1 := by
        calc w * (z * w) * z = (w * z) * (w * z) := by group
          _ = 1 := by rw [← hrwz]; exact hr2
      have h2 : w * (z * w) = z := by
        have h4 : (w * (z * w) * z) * z = 1 * z := congrArg (fun x => x * z) h1
        rw [mul_assoc, h.hyp.z_sq, mul_one, one_mul] at h4
        exact h4
      have h3 : z * w = w * z := by
        have h4 : w * (w * (z * w)) = w * z := congrArg (fun x => w * x) h2
        rw [← mul_assoc, hw2, one_mul] at h4
        exact h4
      exact h3
    have hwA : w ∈ A := (h.mem_A_iff hwW).mpr hzw
    have hzr : z * r = w := by
      rw [hrwz]
      calc z * (w * z) = (z * w) * z := by group
        _ = (w * z) * z := by rw [hzw]
        _ = w := by rw [mul_assoc, h.hyp.z_sq, mul_one]
    rw [hzr]
    exact hwA

theorem WHyp.eq_of_le_R₀ (h : WHyp G L A T z t W W₁ W₂) {Y : Subgroup G} (hY : Y ≤ R₀ A z)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hcard : Nat.card Y = 2 ^ 20) : Y = W := by
  classical
  by_cases hYW : Y = W
  · exact hYW
  have hWnotle : ¬ W ≤ Y := by
    intro hle
    exact hYW (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.e3.card])).symm
  have hYWR : Y ⊔ W = R₀ A z := by
    have hR₀p : IsPGroup 2 (R₀ A z) := IsPGroup.of_card h.e2.card_R₀
    have hle : Y ⊔ W ≤ R₀ A z := sup_le hY h.e3.le_R₀
    have hlt : W < Y ⊔ W := lt_of_le_of_ne le_sup_right (fun heq => hYW (by
      have hleYW := le_sup_left (a := Y) (b := W)
      rw [← heq] at hleYW
      exact Subgroup.eq_of_le_of_card_ge hleYW (by rw [hcard, h.e3.card])))
    have hcard_gt : 2 ^ 20 < Nat.card ↥(Y ⊔ W) := by
      have hc := Subgroup.card_lt_of_lt hlt
      rwa [h.e3.card] at hc
    obtain ⟨k, hk⟩ := (hR₀p.to_le hle).exists_card_eq
    have hk20 : 20 < k := by
      have hc : 2 ^ 20 < 2 ^ k := by rwa [hk] at hcard_gt
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hc
    have hge : 2 ^ 21 ≤ Nat.card ↥(Y ⊔ W) := by
      rw [hk]
      gcongr
      omega
    have hle' : Nat.card ↥(Y ⊔ W) ≤ 2 ^ 21 := by
      rw [← h.e2.card_R₀]
      exact Subgroup.card_le_of_le hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h.e2.card_R₀]
    omega
  have hYrel : Y.relIndex (R₀ A z) = 2 :=
    relIndex_eq_two_of_card_eq hY hcard h.e2.card_R₀
  have hzR : z ∈ R₀ A z := h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))
  have hzx : ∀ x ∈ Y ⊓ W, z * x = x * z := by
    intro x hx
    have hxY : x ∈ Y := hx.1
    have hxW : x ∈ W := hx.2
    by_cases hzY : z ∈ Y
    · exact (hcomm x hxY z hzY).symm
    · rw [SetLike.le_def] at hWnotle
      push Not at hWnotle
      obtain ⟨w, hwW, hwY⟩ := hWnotle
      have hwR : w ∈ R₀ A z := h.e3.le_R₀ hwW
      let w' : ↥(R₀ A z) := ⟨w, hwR⟩
      let z' : ↥(R₀ A z) := ⟨z, hzR⟩
      have hY'index : (Y.subgroupOf (R₀ A z)).index = 2 := hYrel
      have hmem : w'⁻¹ * z' ∈ Y.subgroupOf (R₀ A z) := by
        rw [Subgroup.mul_mem_iff_of_index_two hY'index]
        refine iff_of_false ?_ ?_
        · intro h
          apply hwY
          simpa [w', Subgroup.mem_subgroupOf] using (inv_mem h)
        · intro h
          apply hzY
          simpa [z', Subgroup.mem_subgroupOf] using h
      have hyY : w⁻¹ * z ∈ Y := by
        simpa [w', z', Subgroup.mem_subgroupOf] using hmem
      have hzdec : z = w * (w⁻¹ * z) := by group
      have hxw : x * w = w * x := by
        haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
        exact Subgroup.mul_comm_of_mem_isMulCommutative (H := W) hxW hwW
      have hxy : x * (w⁻¹ * z) = (w⁻¹ * z) * x := hcomm x hxY _ hyY
      calc z * x = (w * (w⁻¹ * z)) * x := congrArg (fun y => y * x) hzdec
        _ = w * ((w⁻¹ * z) * x) := by group
        _ = w * (x * (w⁻¹ * z)) := by rw [hxy]
        _ = (w * x) * (w⁻¹ * z) := by group
        _ = (x * w) * (w⁻¹ * z) := by rw [hxw]
        _ = x * (w * (w⁻¹ * z)) := by group
        _ = x * z := congrArg (fun y => x * y) hzdec.symm
  have hYAW : Y ⊓ W ≤ A := fun x hx => (h.mem_A_iff hx.2).mpr (hzx x hx)
  let Y' : Subgroup ↥(R₀ A z) := Y.subgroupOf (R₀ A z)
  have hY'index : Y'.index = 2 := hYrel
  have hY'norm : Y'.Normal := Subgroup.normal_of_index_eq_two hY'index
  letI : Y'.Normal := hY'norm
  let q : ↥W →* ↥(R₀ A z) ⧸ Y' :=
    (QuotientGroup.mk' Y').comp (Subgroup.inclusion h.e3.le_R₀)
  have hker : q.ker = (Y ⊓ W).subgroupOf W := by
    rw [show q = (QuotientGroup.mk' Y').comp (Subgroup.inclusion h.e3.le_R₀) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hrange : Nat.card ↥(q.range) ≤ 2 := by
    have h1 : Nat.card ↥(q.range) ≤ Nat.card (↥(R₀ A z) ⧸ Y') :=
      Nat.card_le_card_of_injective (fun x : ↥(q.range) => (x.1 : ↥(R₀ A z) ⧸ Y'))
        (fun x y hxy => Subtype.ext hxy)
    have h2 : Nat.card (↥(R₀ A z) ⧸ Y') = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hY'index
    omega
  have hcardW : Nat.card ↥W = Nat.card ↥(Y ⊓ W) * Nat.card ↥(q.range) := by
    have h1 : Nat.card ↥W = Nat.card ↥(q.ker) * Nat.card ↥(q.range) :=
      (Subgroup.card_ker_mul_card_range q).symm
    rw [h1, hker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ W ≤ W))
  have hlow : 2 ^ 19 ≤ Nat.card ↥(Y ⊓ W) := by
    have hle : 2 ^ 20 ≤ Nat.card ↥(Y ⊓ W) * Nat.card ↥(q.range) := by
      rw [← hcardW, h.e3.card]
    have hle' : 2 ^ 20 ≤ Nat.card ↥(Y ⊓ W) * 2 :=
      le_trans hle (Nat.mul_le_mul_left _ hrange)
    have hpow : (2 : ℕ) ^ 20 = 2 ^ 19 * 2 := by ring
    rw [hpow] at hle'
    exact Nat.le_of_mul_le_mul_right hle' (by norm_num)
  have hcardA : Nat.card ↥(Y ⊓ W) ≤ 2 ^ 10 := by
    have hc := Subgroup.card_le_of_le hYAW
    rwa [h.hyp.jc.module.card] at hc
  exfalso
  have hcontra : (2 : ℕ) ^ 19 ≤ 2 ^ 10 := le_trans hlow hcardA
  have h19 : (2 : ℕ) ^ 19 = 524288 := by norm_num
  have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  rw [h19, h10] at hcontra
  omega

private theorem map_conj_eq_W_of_mem_normalizer (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) :
    W.map (MulAut.conj n).toMonoidHom = W := by
  set W' : Subgroup G := W.map (MulAut.conj n).toMonoidHom with hW'def
  have hW'le : W' ≤ R₀ A z := by
    have hmap : (R₀ A z).map (MulAut.conj n).toMonoidHom = R₀ A z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
    rw [hW'def, ← hmap]
    exact Subgroup.map_mono h.e3.le_R₀
  have hW'card : Nat.card W' = 2 ^ 20 := by
    rw [hW'def, Subgroup.card_map_of_injective (MulAut.conj n).injective, h.e3.card]
  have hW'comm : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := by
    have he : IsElementaryAbelian 2 ↥W' := by
      rw [hW'def]
      exact h.elemAb.subgroup_map (MulAut.conj n).toMonoidHom
    haveI : IsMulCommutative ↥W' := he.toIsMulCommutative
    intro a ha b hb
    exact Subgroup.mul_comm_of_mem_isMulCommutative (H := W') ha hb
  exact h.eq_of_le_R₀ hW'le hW'comm hW'card

private theorem conj_mem_R₀_and_not_mem_W (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) :
    (∀ r ∈ R₀ A z, n * r * n⁻¹ ∈ R₀ A z) ∧
      (∀ r ∈ R₀ A z, r ∉ W → n * r * n⁻¹ ∉ W) := by
  have hnW : W.map (MulAut.conj n).toMonoidHom = W := map_conj_eq_W_of_mem_normalizer h hn
  have hinvWN : n⁻¹ ∈ normalizer (W : Set G) :=
    inv_mem (Subgroup.mem_normalizer_iff_map_conj_eq.2 hnW)
  constructor
  · intro r hr
    exact (Subgroup.mem_normalizer_iff.1 hn r).1 hr
  · intro r hr hrW hmem
    apply hrW
    have h := (Subgroup.mem_normalizer_iff.1 hinvWN (n * r * n⁻¹)).1 hmem
    simpa [inv_inv, mul_assoc] using h

private theorem conj_z_mul_mem_A (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) :
    z * (n * z * n⁻¹) ∈ A := by
  obtain ⟨hconjR, hnotW⟩ := conj_mem_R₀_and_not_mem_W h hn
  have hzR : z ∈ R₀ A z := h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))
  have hcR : n * z * n⁻¹ ∈ R₀ A z := hconjR z hzR
  have hcW : n * z * n⁻¹ ∉ W := hnotW z hzR h.e3.z_not_mem
  have hc2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
    calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [h.hyp.z_sq]; group
  exact h.mul_mem_A_of_mul_self hcR hcW hc2

private theorem conj_za_mul_mem_A (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) {a : G} (ha : a ∈ A) :
    z * (n * (z * a) * n⁻¹) ∈ A := by
  obtain ⟨hconjR, hnotW⟩ := conj_mem_R₀_and_not_mem_W h hn
  have hzR : z ∈ R₀ A z := h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))
  have hzaR : z * a ∈ R₀ A z := mul_mem hzR (h.e3.le_R₀ (h.e3.A_le ha))
  have hzaW : z * a ∉ W := by
    intro hmem
    apply h.e3.z_not_mem
    have h1 : (z * a) * a⁻¹ ∈ W := mul_mem hmem (inv_mem (h.e3.A_le ha))
    rwa [mul_inv_cancel_right] at h1
  have hza2 : (z * a) * (z * a) = 1 := by
    have haz : a * z = z * a := h.hyp.commute_of_mem (h.hyp.jc.le ha)
    have ha2 : a * a = 1 := by
      letI : IsElementaryAbelian 2 ↥A := h.hyp.jc.module.elemAb
      simpa [pow_two] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    calc (z * a) * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [haz]
      _ = (z * z) * (a * a) := by group
      _ = 1 := by rw [h.hyp.z_sq, ha2, mul_one]
  have hd2 : (n * (z * a) * n⁻¹) * (n * (z * a) * n⁻¹) = 1 := by
    calc (n * (z * a) * n⁻¹) * (n * (z * a) * n⁻¹)
        = n * ((z * a) * (z * a)) * n⁻¹ := by group
      _ = 1 := by rw [hza2]; group
  exact h.mul_mem_A_of_mul_self (hconjR (z * a) hzaR) (hnotW (z * a) hzaR hzaW) hd2

private theorem map_conj_mem_A_of_mem_normalizer (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) {a : G} (ha : a ∈ A) :
    n * a * n⁻¹ ∈ A := by
  have hzc := conj_z_mul_mem_A h hn
  have hzd := conj_za_mul_mem_A h hn ha
  have hsplit : n * (z * a) * n⁻¹ = (n * z * n⁻¹) * (n * a * n⁻¹) := by group
  have hEq : n * a * n⁻¹ =
      (z * (n * z * n⁻¹))⁻¹ * (z * (n * (z * a) * n⁻¹)) := by
    rw [hsplit]
    group
  rw [hEq]
  exact mul_mem (inv_mem hzc) hzd

private theorem map_conj_mem_B_of_mem_normalizer (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (R₀ A z : Set G)) {b : G} (hb : b ∈ B A z) :
    n * b * n⁻¹ ∈ B A z := by
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun a ha =>
    map_conj_mem_A_of_mem_normalizer h hn ha
  have hzc := conj_z_mul_mem_A h hn
  have hnzB : n * z * n⁻¹ ∈ B A z := by
    have hEq : n * z * n⁻¹ = z * (z * (n * z * n⁻¹)) := by
      rw [← mul_assoc, h.hyp.z_sq, one_mul]
    rw [hEq]
    exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hzc)
  have hzA : z ∈ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
      (h.hyp.zpowers_le_centralizer_A (mem_zpowers z))
  have hBcoe : (↑(B A z) : Set G) = (A : Set G) * (zpowers z : Set G) := by
    change (↑(A ⊔ zpowers z) : Set G) = (A : Set G) * (zpowers z : Set G)
    exact Subgroup.coe_mul_of_right_le_normalizer_left A (zpowers z) (zpowers_le.2 hzA)
  change b ∈ (↑(B A z) : Set G) at hb
  rw [hBcoe, Set.mem_mul] at hb
  obtain ⟨a, ha, y, hy, hay⟩ := hb
  have hnyB : n * y * n⁻¹ ∈ B A z := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hconj : n * z ^ k * n⁻¹ = (n * z * n⁻¹) ^ k := by rw [conj_zpow]
    rw [hconj]
    exact (B A z).zpow_mem hnzB k
  have hbEq : n * b * n⁻¹ = (n * a * n⁻¹) * (n * y * n⁻¹) := by rw [← hay]; group
  rw [hbEq]
  exact mul_mem (mem_sup_left (hnA a ha)) hnyB

theorem WHyp.normalizer_R₀_le (h : WHyp G L A T z t W W₁ W₂) :
    normalizer (R₀ A z : Set G) ≤ M A z := by
  intro n hn
  change n ∈ normalizer (B A z : Set G)
  rw [mem_normalizer_iff]
  intro b
  constructor
  · exact fun hb => map_conj_mem_B_of_mem_normalizer h hn hb
  · intro hb
    have h := map_conj_mem_B_of_mem_normalizer h (n := n⁻¹)
      (inv_mem hn) (b := n * b * n⁻¹) hb
    simpa [inv_inv, mul_assoc] using h

theorem WHyp.exists_conj_le_R₀_of_le (h : WHyp G L A T z t W W₁ W₂) {H P : Subgroup G}
    (hRH : R₀ A z ≤ H) (hHC : H ≤ centralizer (A : Set G)) (hP : IsPGroup 2 P) (hPH : P ≤ H) :
    ∃ c ∈ H, ∀ p ∈ P, c * p * c⁻¹ ∈ R₀ A z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR₀p : IsPGroup 2 (R₀ A z) := IsPGroup.of_card h.e2.card_R₀
  have hR'p : IsPGroup 2 ((R₀ A z).subgroupOf H) := hR₀p.comap_subtype
  let S : Sylow 2 ↥H :=
    ⟨(R₀ A z).subgroupOf H, hR'p, by
      intro Q hQ hRQ
      by_contra hne
      have hlt : (R₀ A z).subgroupOf H < Q :=
        lt_of_le_of_ne hRQ (fun h => hne h.symm)
      obtain ⟨n, hnQ, hnR, hnorm⟩ := exists_mem_normalizer_not_mem hQ hlt
      have hnN : (n : G) ∈ normalizer (R₀ A z : Set G) := by
        have hmap : (R₀ A z).map (MulAut.conj (n : G)).toMonoidHom ≤ R₀ A z := by
          rintro x ⟨r, hr, rfl⟩
          have hrS : (⟨r, hRH hr⟩ : ↥H) ∈ (R₀ A z).subgroupOf H := by
            simpa [Subgroup.mem_subgroupOf] using hr
          have h := (hnorm ⟨r, hRH hr⟩ (hRQ hrS)).1 hrS
          simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using h
        have heq : (R₀ A z).map (MulAut.conj (n : G)).toMonoidHom = R₀ A z := by
          refine Subgroup.eq_of_le_of_card_ge hmap ?_
          rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective, h.e2.card_R₀]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
      have hnR₀ : (n : G) ∈ R₀ A z :=
        ⟨h.normalizer_R₀_le hnN, hHC n.2⟩
      exact hnR (by simpa [Subgroup.mem_subgroupOf] using hnR₀)⟩
  have hP'p : IsPGroup 2 (P.subgroupOf H) := hP.comap_subtype
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP'p
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex S
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥H Q S
  refine ⟨(c : G), c.2, fun p hp => ?_⟩
  have hpQ : (⟨p, hPH hp⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hPQ (by simpa [Subgroup.mem_subgroupOf] using hp)
  have hcsub : (Q : Subgroup ↥H).map (MulAut.conj c).toMonoidHom = (S : Subgroup ↥H) := by
    have h1 : MulAut.conj c • (Q : Subgroup ↥H) = (S : Subgroup ↥H) := by
      rw [← Sylow.coe_subgroup_smul, hc]
    rwa [Subgroup.pointwise_smul_def] at h1
  have hsmul : (MulAut.conj c) (⟨p, hPH hp⟩ : ↥H) ∈ (S : Subgroup ↥H) := by
    rw [← hcsub]
    exact Subgroup.mem_map.2 ⟨_, hpQ, rfl⟩
  have hmem : (((MulAut.conj c) (⟨p, hPH hp⟩ : ↥H) : ↥H) : G) ∈ R₀ A z := hsmul
  have hval : (((MulAut.conj c) (⟨p, hPH hp⟩ : ↥H) : ↥H) : G) =
      (c : G) * p * (c : G)⁻¹ := by
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hval] at hmem

theorem WHyp.exists_conj_le_R₀ (h : WHyp G L A T z t W W₁ W₂) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer (A : Set G)) :
    ∃ c ∈ centralizer (A : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ R₀ A z :=
  h.exists_conj_le_R₀_of_le inf_le_right le_rfl hP hPC

theorem WHyp.eq_of_le_centralizer (h : WHyp G L A T z t W W₁ W₂) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hWP : W ≤ P) (hPC : P ≤ centralizer (W : Set G)) : P = W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hPW : P = W
  · exact hPW
  have hlt : W < P := lt_of_le_of_ne hWP (fun h => hPW h.symm)
  have hAPC : P ≤ centralizer (A : Set G) :=
    hPC.trans (Subgroup.centralizer_le h.e3.A_le)
  have hPcard : 2 ^ 21 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hcard_gt : 2 ^ 20 < Nat.card P := by
      have hc := Subgroup.card_lt_of_lt hlt
      rwa [h.e3.card] at hc
    have hk20 : 20 < k := by
      have hc : 2 ^ 20 < 2 ^ k := by rwa [hk] at hcard_gt
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hc
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨c, hcC, hcP⟩ := h.exists_conj_le_R₀ hP hAPC
  let Pc : Subgroup G := P.map (MulAut.conj c).toMonoidHom
  have hPcR : Pc ≤ R₀ A z := by
    rintro x ⟨p, hp, rfl⟩
    exact hcP p hp
  have hPc_card : Nat.card Pc = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hPc_eq : Pc = R₀ A z := by
    refine Subgroup.eq_of_le_of_card_ge hPcR ?_
    rw [hPc_card, h.e2.card_R₀]
    exact hPcard
  let Wc : Subgroup G := W.map (MulAut.conj c).toMonoidHom
  have hWcR : Wc ≤ R₀ A z := by
    have h1 : Wc ≤ Pc := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) hWP
    exact h1.trans (le_of_eq hPc_eq)
  have hWc_card : Nat.card Wc = 2 ^ 20 := by
    rw [show Nat.card Wc = Nat.card W from
      Subgroup.card_map_of_injective (MulAut.conj c).injective, h.e3.card]
  have hWc_comm : ∀ a ∈ Wc, ∀ b ∈ Wc, a * b = b * a := by
    have he : IsElementaryAbelian 2 ↥Wc := by
      simpa [Wc] using h.elemAb.subgroup_map (MulAut.conj c).toMonoidHom
    haveI : IsMulCommutative ↥Wc := he.toIsMulCommutative
    intro a ha b hb
    exact Subgroup.mul_comm_of_mem_isMulCommutative (H := Wc) ha hb
  have hWc_eq : Wc = W := h.eq_of_le_R₀ hWcR hWc_comm hWc_card
  have hR₀C : R₀ A z ≤ centralizer (W : Set G) := by
    rw [← hWc_eq]
    intro r hr
    rw [mem_centralizer_iff]
    intro w hw
    have hrPc : r ∈ Pc := by rw [hPc_eq]; exact hr
    obtain ⟨p, hpP, hp_eq⟩ := hrPc
    obtain ⟨w0, hw0W, hw_eq⟩ := hw
    have hpC : p ∈ centralizer (W : Set G) := hPC hpP
    have hcomm : w0 * p = p * w0 := mem_centralizer_iff.1 hpC w0 hw0W
    have hrr : r = (MulAut.conj c) p := hp_eq.symm
    have hww : w = (MulAut.conj c) w0 := hw_eq.symm
    rw [hrr, hww]
    show (MulAut.conj c) w0 * (MulAut.conj c) p =
      (MulAut.conj c) p * (MulAut.conj c) w0
    simp only [MulAut.conj_apply]
    calc (c * w0 * c⁻¹) * (c * p * c⁻¹) = c * (w0 * p) * c⁻¹ := by group
      _ = c * (p * w0) * c⁻¹ := by rw [hcomm]
      _ = (c * p * c⁻¹) * (c * w0 * c⁻¹) := by group
  have hzC : z ∈ centralizer (W : Set G) :=
    hR₀C (h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z)))
  have hWA : W ≤ A := by
    intro w hw
    exact (h.mem_A_iff hw).mpr (mem_centralizer_iff.1 hzC w hw).symm
  exfalso
  have hcard_le : Nat.card W ≤ Nat.card A := Subgroup.card_le_of_le hWA
  rw [h.e3.card, h.hyp.jc.module.card] at hcard_le
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  rw [h20, h10] at hcard_le
  omega

private noncomputable def sylowT (h : Hyp G L A T z t) : Sylow 2 ↥L :=
  ⟨T.subgroupOf L, h.set.pgroup.comap_subtype, by
    intro Q hQ hTQ
    have hQmap : IsPGroup 2 (Q.map L.subtype) := hQ.map L.subtype
    have hQleL : Q.map L.subtype ≤ L := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hTle : T ≤ Q.map L.subtype := by
      intro x hx
      exact ⟨⟨x, h.set.le hx⟩,
        hTQ (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hEq : Q.map L.subtype = T := h.set.maximal _ hQleL hQmap hTle
    ext q
    constructor
    · intro hq
      have hq' : (q : G) ∈ Q.map L.subtype := ⟨q, hq, rfl⟩
      rw [hEq] at hq'
      simpa [Subgroup.mem_subgroupOf] using hq'
    · intro hq
      have hqT : (q : G) ∈ T := by simpa [Subgroup.mem_subgroupOf] using hq
      have hq' : (q : G) ∈ Q.map L.subtype := by rw [hEq]; exact hqT
      obtain ⟨q', hq', hq'eq⟩ := hq'
      exact (Subtype.ext hq'eq) ▸ hq'⟩

theorem Hyp.card_le_of_le_L (h : Hyp G L A T z t) {U : Subgroup G}
    (hU : IsElementaryAbelian 2 ↥U) (hUL : U ≤ L) : Nat.card U ≤ 2 ^ 10 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 (U.subgroupOf L) :=
    (hU.isPGroup 2 ↥U).of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm
  obtain ⟨l, hl⟩ := exists_conj_le_sylow_of_isPGroup (sylowT h) hUp
  have hVT : ∀ x ∈ U.map (MulAut.conj (l : G)).toMonoidHom, x ∈ T := by
    rintro x ⟨u, hu, rfl⟩
    have hmem := hl ⟨u, hUL hu⟩ (by simpa [Subgroup.mem_subgroupOf] using hu)
    have hmem' : ((l * (⟨u, hUL hu⟩ : ↥L) * l⁻¹ : ↥L) : G) ∈ T := hmem
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply, mul_assoc] using hmem'
  by_contra hcon
  push Not at hcon
  have hVe : IsElementaryAbelian 2 ↥(U.map (MulAut.conj (l : G)).toMonoidHom) :=
    hU.subgroup_map (MulAut.conj (l : G)).toMonoidHom
  have hVcard : 2 ^ 10 ≤ Nat.card ↥(U.map (MulAut.conj (l : G)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (l : G)).toMonoidHom)
      (MulAut.conj (l : G)).injective]
    exact le_of_lt hcon
  have hVeq := eq_A_of_elemAb_le_T h hVT hVe hVcard
  have hcardU : Nat.card U = 2 ^ 10 := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj (l : G)).toMonoidHom)
      (MulAut.conj (l : G)).injective (K := U), hVeq, h.jc.module.card]
  omega

theorem Hyp.exists_conj_eq_A (h : Hyp G L A T z t) {U : Subgroup G}
    (hU : IsElementaryAbelian 2 ↥U) (hUL : U ≤ L) (hcard : Nat.card U = 2 ^ 10) :
    ∃ l ∈ L, ∀ x : G, x ∈ U ↔ l * x * l⁻¹ ∈ A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 (U.subgroupOf L) :=
    (hU.isPGroup 2 ↥U).of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm
  obtain ⟨l, hl⟩ := exists_conj_le_sylow_of_isPGroup (sylowT h) hUp
  refine ⟨(l : G), l.2, fun x => ?_⟩
  set V : Subgroup G := U.map (MulAut.conj (l : G)).toMonoidHom with hVdef
  have hVT : V ≤ T := by
    rw [hVdef]
    rintro y ⟨u, hu, rfl⟩
    have hmem := hl ⟨u, hUL hu⟩ (by simpa [Subgroup.mem_subgroupOf] using hu)
    have hmem' : ((l * (⟨u, hUL hu⟩ : ↥L) * l⁻¹ : ↥L) : G) ∈ T := hmem
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply, mul_assoc] using hmem'
  have hVe : IsElementaryAbelian 2 ↥V := by
    rw [hVdef]
    exact hU.subgroup_map (MulAut.conj (l : G)).toMonoidHom
  have hVcard : 2 ^ 10 ≤ Nat.card V := by
    rw [hVdef, Subgroup.card_map_of_injective (f := (MulAut.conj (l : G)).toMonoidHom)
      (MulAut.conj (l : G)).injective, hcard]
  have hVeq : V = A := eq_A_of_elemAb_le_T h hVT hVe hVcard
  constructor
  · intro hx
    have hxV : (MulAut.conj (l : G)) x ∈ V := by
      rw [hVdef]
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    rw [hVeq] at hxV
    have hxG : (MulAut.conj (l : G)) x = l * x * l⁻¹ := MulAut.conj_apply (l : G) x
    rwa [hxG] at hxV
  · intro hx
    have hxV : (MulAut.conj (l : G)) x ∈ V := by
      rw [hVeq]
      exact hx
    rw [hVdef] at hxV
    obtain ⟨u, hu, hueq⟩ := hxV
    have hux : u = x := by
      have h := congrArg (fun y : G => (l : G)⁻¹ * y * (l : G)) hueq
      simpa [MulAut.conj_apply, inv_inv, mul_assoc] using h
    rwa [← hux]

theorem Hyp.card_le_of_isConj (h : Hyp G L A T z t) {u : G} (hu : IsConj z u) {U : Subgroup G}
    (hU : IsElementaryAbelian 2 ↥U) (hUC : U ≤ centralizer ({u} : Set G)) :
    Nat.card U ≤ 2 ^ 11 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hu
  set V : Subgroup G := U.map (MulAut.conj g⁻¹).toMonoidHom with hVdef
  have hVcard : Nat.card V = Nat.card U := by
    rw [hVdef, Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
  have hVe : IsElementaryAbelian 2 ↥V := by
    rw [hVdef]
    exact hU.subgroup_map (MulAut.conj g⁻¹).toMonoidHom
  have hVC : V ≤ centralizer ({z} : Set G) := by
    rw [hVdef]
    rintro x ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hyu : y * u = u * y := mem_centralizer_singleton_iff.1 (hUC hy)
    have hz : z = g⁻¹ * u * g := by rw [← hg]; group
    have hxval : (MulAut.conj g⁻¹) y = g⁻¹ * y * g := by
      rw [MulAut.conj_apply, inv_inv]
    change (MulAut.conj g⁻¹) y * z = z * (MulAut.conj g⁻¹) y
    rw [hxval, hz]
    calc (g⁻¹ * y * g) * (g⁻¹ * u * g) = g⁻¹ * (y * u) * g := by group
      _ = g⁻¹ * (u * y) * g := by rw [hyu]
      _ = (g⁻¹ * u * g) * (g⁻¹ * y * g) := by group
  rw [h.set.centralizer_z] at hVC
  have hLz : L ≤ centralizer ({z} : Set G) := by
    rw [h.set.centralizer_z]
    exact le_sup_left
  have hzC : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (hLz hl)
  have hzNL : z ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hzC
  have hLrel : L.relIndex (L ⊔ zpowers z) = 2 := by
    have hc := card_sup_zpowers_of_mem_normalizer hzNL h.z_sq h.z_not_mem_L
    have h := Subgroup.relIndex_mul_card (H := L) (K := L ⊔ zpowers z)
    rw [inf_eq_left.mpr le_sup_left, hc] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h
  let K : Subgroup G := L ⊔ zpowers z
  have hVK : V ≤ K := hVC
  let L' : Subgroup ↥K := L.subgroupOf K
  have hL'index : L'.index = 2 := hLrel
  have hL'norm : L'.Normal := Subgroup.normal_of_index_eq_two hL'index
  letI : L'.Normal := hL'norm
  let q : ↥V →* ↥K ⧸ L' := (QuotientGroup.mk' L').comp (Subgroup.inclusion hVK)
  have hker : q.ker = (V ⊓ L).subgroupOf V := by
    rw [show q = (QuotientGroup.mk' L').comp (Subgroup.inclusion hVK) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hrange : Nat.card ↥(q.range) ≤ 2 := by
    have h1 : Nat.card ↥(q.range) ≤ Nat.card (↥K ⧸ L') :=
      Nat.card_le_card_of_injective (fun x : ↥(q.range) => (x.1 : ↥K ⧸ L'))
        (fun x y hxy => Subtype.ext hxy)
    have h2 : Nat.card (↥K ⧸ L') = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hL'index
    omega
  have hcardV : Nat.card V = Nat.card ↥(V ⊓ L) * Nat.card ↥(q.range) := by
    have h1 : Nat.card V = Nat.card ↥(q.ker) * Nat.card ↥(q.range) :=
      (Subgroup.card_ker_mul_card_range q).symm
    rw [h1, hker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ L ≤ V))
  have hVLle : Nat.card ↥(V ⊓ L) ≤ 2 ^ 10 :=
    h.card_le_of_le_L (IsElementaryAbelian.of_le hVe inf_le_left) inf_le_right
  calc Nat.card U = Nat.card V := hVcard.symm
    _ = Nat.card ↥(V ⊓ L) * Nat.card ↥(q.range) := hcardV
    _ ≤ 2 ^ 10 * 2 := Nat.mul_le_mul hVLle hrange
    _ = 2 ^ 11 := by norm_num

theorem WHyp.not_isConj (h : WHyp G L A T z t W W₁ W₂) {w : G} (hw : w ∈ W) :
    ¬ IsConj z w := by
  intro hconj
  have hWc : W ≤ centralizer ({w} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
    exact Subgroup.mul_comm_of_mem_isMulCommutative (H := W) hx hw
  have hle := h.hyp.card_le_of_isConj hconj h.elemAb hWc
  rw [h.e3.card] at hle
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have h11 : (2 : ℕ) ^ 11 = 2048 := by norm_num
  rw [h20, h11] at hle
  omega

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
