module

public import CFSG.GH74.Generic.S3.Prop21Leaves
public import CFSG.GH74.Generic.S3.FourGroup
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.KGroups.L3EpsFour
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section Choice

variable {G : Type} [Group G] [Finite G]

theorem exists_v1_choice {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (C : Conf2A G t p f v w Iv Iw Ivw P) :
    ∃ v₁ : G, v₁ ∈ P ⊓ Ivw ∧ v₁ * v₁ = 1 ∧ v₁ ≠ 1 ∧ v₁ ≠ v ∧
      ((∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u) →
        ∃ s ∈ P ⊓ Ivw, s * s = v₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hSq : ∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u
  · obtain ⟨u, hu, hu2, hu1, huv, hs⟩ := hSq
    exact ⟨u, hu, hu2, hu1, huv, fun _ => hs⟩
  · suffices h : ∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v by
      obtain ⟨u, hu, hu2, hu1, huv⟩ := h
      exact ⟨u, hu, hu2, hu1, huv, fun h => absurd h hSq⟩
    have hR : IsSylowOf 2 (P ⊓ Ivw) Ivw :=
      C.sylow_vw.inf_of_le_normalizer C.comp_vw.1.1 C.comp_vw.le_normalizer
    obtain ⟨Q, hQ⟩ := hR
    have hodd := C.odd_vw
    set π : ↥Ivw →* ↥Ivw ⧸ center ↥Ivw := QuotientGroup.mk' (center ↥Ivw) with hπ
    obtain ⟨hS2, hSmax⟩ := isMax_map_center Q hodd
    have hX : StatedClassicalModel (↥Ivw ⧸ center ↥Ivw) t 3 p f := by
      rcases C.tag with rfl | rfl
      · exact stated_of_lieModel_PSL C.model_vw
      · exact stated_of_lieModel_PSU C.model_vw
    obtain ⟨a, ha, b, hb, ha2, hb2, hab, ha1, hb1, hne⟩ :=
      KGroups.L3Eps.l3eps_sylow_four C.tag C.prime.2.1 hX hS2 hSmax
    obtain ⟨qa, hqa, rfl⟩ := ha
    obtain ⟨qb, hqb, rfl⟩ := hb
    have hQ2 : IsPGroup 2 (Q : Subgroup ↥Ivw) := Q.isPGroup'
    have hQZ : ∀ z : ↥Ivw, z ∈ (Q : Subgroup ↥Ivw) → z ∈ center ↥Ivw → z = 1 :=
      fun z hzQ hzZ => eq_one_of_mem_pGroup_of_mem_center_odd hQ2 hodd hzQ hzZ
    have hqa2 : qa * qa = 1 := by
      have h1 : π (qa * qa) = 1 := by rw [map_mul]; exact ha2
      exact hQZ _ (Q.mul_mem hqa hqa) ((QuotientGroup.eq_one_iff _).1 h1)
    have hqb2 : qb * qb = 1 := by
      have h1 : π (qb * qb) = 1 := by rw [map_mul]; exact hb2
      exact hQZ _ (Q.mul_mem hqb hqb) ((QuotientGroup.eq_one_iff _).1 h1)
    have hqab : qa * qb = qb * qa := by
      have h1 : π ((qb * qa)⁻¹ * (qa * qb)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hab]
        exact inv_mul_cancel _
      have h2 := hQZ _ (Q.mul_mem (Q.inv_mem (Q.mul_mem hqb hqa)) (Q.mul_mem hqa hqb))
        ((QuotientGroup.eq_one_iff _).1 h1)
      exact (inv_mul_eq_one.1 h2).symm
    have hmem : ∀ q ∈ (Q : Subgroup ↥Ivw), (q : G) ∈ P ⊓ Ivw := fun q hq => by
      rw [← hQ]
      exact ⟨q, hq, rfl⟩
    have hqa1 : qa ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have hqb1 : qb ≠ 1 := fun h => hb1 (by rw [h, map_one])
    have hqne : qa ≠ qb := fun h => hne (by rw [h])
    by_cases hva : (qa : G) = v
    · refine ⟨(qb : G), hmem qb hqb, congrArg Subtype.val hqb2,
        fun h => hqb1 (Subtype.ext h), fun h => hqne (Subtype.ext (hva.trans h.symm))⟩
    · exact ⟨(qa : G), hmem qa hqa, congrArg Subtype.val hqa2, fun h => hqa1 (Subtype.ext h), hva⟩

end Choice

section Easy

variable {G : Type} [Group G] [Finite G]

theorem v1_mem_or_wI {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (C : Conf2A G t p f v w Iv Iw Ivw P) {v₁ m : G} (hv₁P : v₁ ∈ P) (hv₁2 : v₁ * v₁ = 1)
    (hm : m ∈ Iw) (hc : v₁ * m⁻¹ ∈ centralizer (Iw : Set G)) : v₁ ∈ Iw ∨ w * v₁ ∈ Iw := by
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [C.w_inv, pow_two] at this
  have hw1 : w ≠ 1 := fun h => by
    have := C.w_inv
    rw [h, orderOf_one] at this
    omega
  have hIwC : Iw ≤ centralizer ({w} : Set G) := C.comp_w.1.1
  have hQ := sylow_inf_centralizer C.sylow_w C.comp_w.le_normalizer
  have hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G)) :=
    noCommInv_of_sylow hQ (noCommInv_of_cyclic C.Q_cyc)
  have hwC : w ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) := by
    refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
    exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hIwC hh)
  have hv₁w : v₁ * w = w * v₁ := mem_centralizer_singleton_iff.1 (C.sylow_w.le hv₁P)
  set c := v₁ * m⁻¹ with hcdef
  have hcC : c ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) := by
    refine ⟨?_, hc⟩
    exact (centralizer ({w} : Set G)).mul_mem (C.sylow_w.le hv₁P)
      ((centralizer ({w} : Set G)).inv_mem (hIwC hm))
  have hmc : m * c = c * m := mem_centralizer_iff.1 hc m hm
  have hxcm : v₁ = c * m := by rw [hcdef]; group
  have hcc : c * c * (m * m) = 1 := by
    calc c * c * (m * m) = c * (c * m) * m := by simp only [mul_assoc]
      _ = c * (m * c) * m := by rw [hmc]
      _ = (c * m) * (c * m) := by simp only [mul_assoc]
      _ = v₁ * v₁ := by rw [← hxcm]
      _ = 1 := hv₁2
  have hccN : c * c ∈ Iw := by
    have : c * c = (m * m)⁻¹ := eq_inv_of_mul_eq_one_left hcc
    rw [this]
    exact Iw.inv_mem (Iw.mul_mem hm hm)
  have hccC : c * c ∈ centralizer (Iw : Set G) := (centralizer (Iw : Set G)).mul_mem hc hc
  have hz : (⟨c * c, hccN⟩ : ↥Iw) ∈ center ↥Iw := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hccC g g.2)
  set n := Nat.card ↥(center ↥Iw) with hn
  have hzpow : (⟨⟨c * c, hccN⟩, hz⟩ : ↥(center ↥Iw)) ^ n = 1 := pow_card_eq_one'
  have hccn : (c * c) ^ n = 1 := by
    have := congrArg (fun t : ↥(center ↥Iw) => ((t : ↥Iw) : G)) hzpow
    simpa using this
  obtain ⟨k, hk⟩ := C.odd_w
  set y := c ^ n with hy
  have hyy : y * y = 1 := by
    rw [hy, ← (Commute.refl c).mul_pow, hccn]
  have hyC : y ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) :=
    Subgroup.pow_mem _ hcC n
  have hyN : v₁⁻¹ * y ∈ Iw := by
    have hk' : n = 2 * k + 1 := hk
    have hy' : y = c * (c * c) ^ k := by
      rw [hy, hk', pow_succ', pow_mul, sq]
    have : v₁⁻¹ * y = m⁻¹ * (c * c) ^ k := by
      rw [hy', hxcm]; group
    rw [this]
    exact Iw.mul_mem (Iw.inv_mem hm) (Iw.pow_mem hccN k)
  have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁2
  by_cases hy1 : y = 1
  · left
    rw [hy1, mul_one, hv₁inv] at hyN
    exact hyN
  · right
    have hcomm : y * w = w * y := mem_centralizer_singleton_iff.1 hyC.1
    rcases hrk y hyC w hwC hyy hw2 hcomm with h | h | h
    · exact absurd h hy1
    · exact absurd h hw1
    · rw [h, hv₁inv] at hyN
      rw [← hv₁w]
      exact hyN

theorem v1_not_wI {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (C : Conf2A G t p f v w Iv Iw Ivw P) {v₁ : G} (hv₁R : v₁ ∈ P ⊓ Ivw) (hv₁2 : v₁ * v₁ = 1)
    (hv₁1 : v₁ ≠ 1) (hv₁v : v₁ ≠ v) : w * v₁ ∉ Iw := by
  intro hwv
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [C.v_inv, pow_two] at this
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [C.w_inv, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by
    have := C.v_inv
    rw [h, orderOf_one] at this
    omega
  have hvv₁ : v * v₁ = v₁ * v := (C.v_central v₁ hv₁R.1).symm
  have hv₁w : v₁ * w = w * v₁ := mem_centralizer_singleton_iff.1 (C.sylow_w.le hv₁R.1)
  have hvIvw : v ∈ Ivw := C.le_vw C.v_mem
  have hvIw : v ∈ Iw := C.le_w C.v_mem
  obtain ⟨g, hgI, hg1, hg2⟩ := b_L3_fourgroup G t p f C.tag C.prime.1 C.prime.2.1 C.prime.2.2 Ivw
    C.comp_vw.1.isQuasisimple C.odd_vw C.model_vw v v₁ hvIvw hv₁R.2 hv2 hv₁2 hvv₁ hv1 hv₁1
    hv₁v.symm
  have hgc : g * (v * w) = (v * w) * g := mem_centralizer_singleton_iff.1 (C.comp_vw.1.1 hgI)
  have hvw : v * w = w * v := C.comm
  have hw_eq : w = (v * w) * v := by
    calc w = (v * v) * w := by rw [hv2, one_mul]
      _ = v * (v * w) := by rw [mul_assoc]
      _ = v * (w * v) := by rw [hvw]
      _ = (v * w) * v := by rw [mul_assoc]
  have hgw : g * w * g⁻¹ = w * v₁ := by
    calc g * w * g⁻¹ = g * ((v * w) * v) * g⁻¹ := by rw [← hw_eq]
      _ = (g * (v * w) * g⁻¹) * (g * v * g⁻¹) := by group
      _ = (v * w) * (v * v₁) := by
          rw [hg1]
          congr 1
          calc g * (v * w) * g⁻¹ = ((v * w) * g) * g⁻¹ := by rw [hgc]
            _ = v * w := by group
      _ = w * v₁ := by
          calc (v * w) * (v * v₁) = v * (w * v) * v₁ := by simp only [mul_assoc]
            _ = v * (v * w) * v₁ := by rw [hvw]
            _ = (v * v) * w * v₁ := by simp only [mul_assoc]
            _ = w * v₁ := by rw [hv2, one_mul]
  have hv₁w' : v₁ ≠ w := by
    intro h
    apply C.notConj_vw
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [hg1, h]
  have hwv1 : w * v₁ ≠ 1 := by
    intro h
    apply hv₁w'
    calc v₁ = w * (w * v₁) := by rw [← mul_assoc, hw2, one_mul]
      _ = w := by rw [h, mul_one]
  have hwv2 : (w * v₁) * (w * v₁) = 1 := by
    calc (w * v₁) * (w * v₁) = w * (v₁ * w) * v₁ := by simp only [mul_assoc]
      _ = w * (w * v₁) * v₁ := by rw [hv₁w]
      _ = (w * w) * (v₁ * v₁) := by simp only [mul_assoc]
      _ = 1 := by rw [hw2, hv₁2, one_mul]
  obtain ⟨h, hhI, hh⟩ := b_L3_class G t p f C.tag C.prime.1 C.prime.2.1 C.prime.2.2 Iw
    C.comp_w.1.isQuasisimple C.odd_w C.model_w (w * v₁) hwv v hvIw hwv2 hwv1 hv2 hv1
  apply C.notConj_w
  refine (isConj_iff.2 ⟨h * g, ?_⟩).symm
  calc h * g * w * (h * g)⁻¹ = h * (g * w * g⁻¹) * h⁻¹ := by group
    _ = v := by rw [hgw]; exact hh

end Easy

section Core

@[expose] def B_S3_v1_inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G t p f v w Iv Iw Ivw P →
      ∀ v₁ : G, v₁ ∈ P ⊓ Ivw → v₁ * v₁ = 1 → v₁ ≠ 1 → v₁ ≠ v →
        ((∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u) →
          ∃ s ∈ P ⊓ Ivw, s * s = v₁) →
        ∃ m ∈ Iw, v₁ * m⁻¹ ∈ centralizer (Iw : Set G)

theorem b_S3_lemma22_v1_of_inner (hinner : B_S3_v1_inner) : B_S3_lemma22_v1 := by
  intro G _ _ hG t p f v w Iv Iw Ivw P hconf
  obtain ⟨v₁, hv₁R, hv₁2, hv₁1, hv₁v, hsq⟩ := exists_v1_choice hconf
  obtain ⟨m, hmI, hmc⟩ := hinner G hG t p f v w Iv Iw Ivw P hconf v₁ hv₁R hv₁2 hv₁1 hv₁v hsq
  have h1 := v1_mem_or_wI hconf hv₁R.1 hv₁2 hmI hmc
  have h2 := v1_not_wI hconf hv₁R hv₁2 hv₁1 hv₁v
  exact ⟨v₁, hv₁R.1, h1.resolve_right h2, hv₁R.2, hv₁2, hv₁1, hv₁v⟩

end Core

end CFSG.GH74.Generic.S3
