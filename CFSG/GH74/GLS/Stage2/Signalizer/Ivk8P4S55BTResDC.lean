module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoPat
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Conj

variable {X : Type*} [Group X]

theorem conjugate_conjugate_eq (H : Subgroup X) (a b : X) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjugate_eq_of_mem_normalizer {H : Subgroup X} {a : X}
    (ha : a ∈ normalizer (H : Set X)) : conjugate H a = H := by
  unfold conjugate
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem ha)

end Conj

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem swaps_mul_mul {L₁ L₂ : Subgroup (CentralizerBar z)} {a b c : G}
    (hsw : Swaps z b L₁ L₂) (haC : a ∈ Cen z) (hcC : c ∈ Cen z)
    (ha₁ : toBar z ⟨a, haC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (ha₂ : toBar z ⟨a, haC⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)))
    (hc₁ : toBar z ⟨c, hcC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hc₂ : toBar z ⟨c, hcC⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Swaps z (a * b * c) L₁ L₂ := by
  obtain ⟨hbC, h1, h2⟩ := hsw
  have habc : a * b * c ∈ Cen z := (Cen z).mul_mem ((Cen z).mul_mem haC hbC) hcC
  have e : toBar z ⟨a * b * c, habc⟩ =
      toBar z ⟨a, haC⟩ * toBar z ⟨b, hbC⟩ * toBar z ⟨c, hcC⟩ := by
    rw [← map_mul, ← map_mul]
    rfl
  refine ⟨habc, ?_, ?_⟩
  · rw [e, ← conjugate_conjugate_eq, ← conjugate_conjugate_eq,
      conjugate_eq_of_mem_normalizer ha₁, h1, conjugate_eq_of_mem_normalizer hc₂]
  · rw [e, ← conjugate_conjugate_eq, ← conjugate_conjugate_eq,
      conjugate_eq_of_mem_normalizer ha₂, h2, conjugate_eq_of_mem_normalizer hc₁]

theorem LC_normalizes {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) {r : G} (hr : r ∈ LC z) (hrC : r ∈ Cen z) :
    toBar z ⟨r, hrC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧
      toBar z ⟨r, hrC⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
  have h := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.of_stage1Pair hP
  have hmem : toBar z ⟨r, hrC⟩ ∈ L₁ ⊔ L₂ := by
    rw [hP.prod.1]
    exact ⟨⟨r, hrC⟩, hr, rfl⟩
  have hn : ∀ {K K' : Subgroup (CentralizerBar z)}, (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) →
      K ⊔ K' ≤ normalizer (K : Set (CentralizerBar z)) := by
    intro K K' hc
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hc a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have e : a = b * a * b⁻¹ := by
        have := hc _ ha b hb
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [← this]; group
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  refine ⟨hn h.comm hmem, ?_⟩
  have h' := hn (fun a ha b hb => (h.comm b hb a ha).symm) (K := L₂) (K' := L₁)
  rw [sup_comm] at h'
  exact h' hmem

omit [Finite G] in
theorem barOf_zpowers {w : G} (hwC : w ∈ Cen z) :
    barOf z (zpowers w) = zpowers (toBar z ⟨w, hwC⟩) := by
  have h1 : (zpowers w).subgroupOf (Cen z) = zpowers (⟨w, hwC⟩ : ↥(Cen z)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simp [hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; simp⟩
  unfold barOf
  rw [h1, MonoidHom.map_zpowers]

omit [Finite G] in
theorem mul_self_eq_one_of_isConj {y : G} (hz2 : z * z = 1) (h : IsConj z y) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hz2]; group

theorem not_mem_LC_of_isConj {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    {x₀ : G} (hz : IsCentralInvolution z) (hx : TwoClassData G z S L₁ L₂ q x₀) {y : G}
    (hy2 : y * y = 1) (hyz : y ≠ z) (hyc : IsConj z y) : y ∉ LC z := by
  intro hyL
  have hz1 : z ≠ 1 := by
    intro h1
    have := hz.1
    rw [h1, orderOf_one] at this
    omega
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hz1 (isConj_one_left.mp hyc)
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  obtain ⟨hxy, -⟩ := hx.invol_L y hyL hord hyz
  exact hx.x_nonCentral
    (P27.Psp4Stage1.isCentralInvolution_of_isConj hz (hyc.trans hxy.symm))

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_two {R S : Subgroup G} (h2 : R.relIndex S = 2) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (haR : a ∉ R) (hbR : b ∉ R) : a⁻¹ * b ∈ R := by
  have hidx : (R.subgroupOf S).index = 2 := h2
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥S)⁻¹)
    (b := ⟨b, hb⟩)).mpr (by
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) haR
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp h) hbR)
  exact Subgroup.mem_subgroupOf.mp key

theorem z_mem_LC {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) : z ∈ LC z := by
  have hc := toBar_z_mem_center z
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hP.fitting] at h1
  exact mem_LC_of_toBar_mem z (mem_Cen_self z) ⟨1, by simpa using hz⟩ h1

theorem swap_criterion {k : Stage12.Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hnt : ¬ TypeOneCase G k) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x₀ : G), Stage1Pair G z S q L₁ L₂ ∧
      TwoClassData G z S L₁ L₂ q x₀ ∧
      ∀ y ∈ S, y * y = 1 → y ≠ z → IsConj z y → ¬ IsConj z (z * y) → Swaps z y L₁ L₂ := by
  have hz := ctx.central
  have hS := ctx.sylow
  have hdet := ctx.detail
  have hSC : S ≤ Cen z := by
    obtain ⟨Q, hQ⟩ := hS
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hd := ctx.data
  clear ctx
  cases hd with
  | g2 h => exact absurd (Or.inl h.one_class) hnt
  | m12 h => exact absurd (Or.inr rfl) hnt
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnt
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnt
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h4⟩ := h
    obtain ⟨x₀, hx⟩ := h4.two
    refine ⟨q, L₁, L₂, x₀, h4.pair, hx, fun y hyS hy2 hyz hyc _ => ?_⟩
    have hyL := not_mem_LC_of_isConj hz hx hy2 hyz hyc
    obtain ⟨s, hsS, hsw⟩ := h4.pair.swap
    have hsL := L52Two.not_mem_LC_of_swaps h4.pair hsw
    have hr : s⁻¹ * y ∈ RC S z :=
      inv_mul_mem_of_relIndex_two h4.index hsS hyS (fun h => hsL h.2) (fun h => hyL h.2)
    have hrC : s⁻¹ * y ∈ Cen z := hSC hr.1
    have h1 := LC_normalizes h4.pair hr.2 hrC
    have h1' := LC_normalizes h4.pair (LC z).one_mem (Cen z).one_mem
    have e : y = 1 * s * (s⁻¹ * y) := by group
    rw [e]
    exact swaps_mul_mul hsw (Cen z).one_mem hrC h1'.1 h1'.2 h1.1 h1.2
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h4⟩ := h
    rcases h4.fusion with ⟨-, h1⟩ | ⟨hq4, x₀, hx, -, -⟩
    · exact absurd (Or.inl h1) hnt
    obtain ⟨t₀, ht₀S, ht₀c, ht₀sw, w₀, hw₀S, hw₀o, ht₀w₀, hw₀Rt, hgood, -, -, -, hcos⟩ :=
      hdet.l4_two ε q L₁ L₂ x₀ rfl h4 hx hq4
    refine ⟨q, L₁, L₂, x₀, h4.pair, hx, fun y hyS hy2 hyz hyc hnc => ?_⟩
    have hP := h4.pair
    have hnorm := P27.RC_conj_mem hSC
    have ht₀2 : t₀ * t₀ = 1 := mul_self_eq_one_of_isConj hz2 ht₀c
    have hw₀2 : w₀ * w₀ = 1 := by
      have := pow_orderOf_eq_one w₀
      rwa [hw₀o, pow_two] at this
    have ht₀R : t₀ ∉ RC S z := fun h => L52Two.not_mem_LC_of_swaps hP ht₀sw h.2
    have hw₀R : w₀ ∉ RC S z := fun h => hw₀Rt (Subgroup.mem_sup_left h)
    obtain ⟨-, -, hSeq⟩ := P27.S45.l4_S_structure (inf_le_left : RC S z ≤ S) hnorm ht₀S hw₀S
      ht₀2 hw₀2 ht₀w₀ ht₀R hw₀Rt h4.index_le
    have hw₀C : w₀ ∈ Cen z := hSC hw₀S
    have hw₀L : ∀ {L : Subgroup (CentralizerBar z)}, L ≤ LBar z →
        toBar z ⟨w₀, hw₀C⟩ ∉ L := by
      intro L hL hmem
      exact hw₀R ⟨hw₀S, mem_LC_of_toBar_mem z hw₀C ⟨1, by simpa using hw₀o⟩ (hL hmem)⟩
    have hL₁ : L₁ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_left
    have hL₂ : L₂ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_right
    obtain ⟨-, -, hpgl₁, hpgl₂⟩ := hgood
    rw [barOf_zpowers hw₀C] at hpgl₁ hpgl₂
    have hw₀n₁ := P27.L4WFacts.normalizer_of_pglOver hP.sl₁ (hw₀L hL₁) hpgl₁
    have hw₀n₂ := P27.L4WFacts.normalizer_of_pglOver hP.sl₂ (hw₀L hL₂) hpgl₂
    have hyL := not_mem_LC_of_isConj hz hx hy2 hyz hyc
    have hzS : z ∈ S := P27.Psp4Stage1.z_mem_of_sylow hz hS
    have hzR : z ∈ RC S z := ⟨hzS, z_mem_LC hP hz.1⟩
    have hyS' : y ∈ (RC S z ⊔ zpowers t₀) ⊔ zpowers w₀ := by
      have h0 : y ∈ RC S z ⊔ (zpowers t₀ ⊔ zpowers w₀) := by
        have h := hSeq ▸ hyS
        exact h
      rw [← sup_assoc] at h0
      exact h0
    have hconj_t : ∀ k ∈ RC S z, t₀ * k * t₀⁻¹ ∈ RC S z := fun k hk => hnorm t₀ ht₀S k hk
    have hsq_t : t₀ * t₀ ∈ RC S z := by rw [ht₀2]; exact one_mem _
    have hconj_w : ∀ k ∈ RC S z ⊔ zpowers t₀, w₀ * k * w₀⁻¹ ∈ RC S z ⊔ zpowers t₀ := by
      intro k hk
      rcases (P27.Psp4.mem_sup_zpowers_iff hconj_t hsq_t).1 hk with hk' | ⟨r, hr, rfl⟩
      · exact Subgroup.mem_sup_left (hnorm w₀ hw₀S k hk')
      · have hwt : w₀ * t₀ = t₀ * w₀ := ht₀w₀.symm
        have e : w₀ * (r * t₀) * w₀⁻¹ = (w₀ * r * w₀⁻¹) * t₀ := by
          calc w₀ * (r * t₀) * w₀⁻¹ = (w₀ * r * w₀⁻¹) * (w₀ * t₀) * w₀⁻¹ := by group
            _ = (w₀ * r * w₀⁻¹) * (t₀ * w₀) * w₀⁻¹ := by rw [hwt]
            _ = (w₀ * r * w₀⁻¹) * t₀ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hnorm w₀ hw₀S r hr))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))
    have hsq_w : w₀ * w₀ ∈ RC S z ⊔ zpowers t₀ := by rw [hw₀2]; exact one_mem _
    have h1' := LC_normalizes hP (LC z).one_mem (Cen z).one_mem
    rcases (P27.Psp4.mem_sup_zpowers_iff hconj_w hsq_w).1 hyS' with hk | ⟨k, hk, hyk⟩
    · rcases (P27.Psp4.mem_sup_zpowers_iff hconj_t hsq_t).1 hk with hyR | ⟨r, hr, hyr⟩
      · exact absurd hyR.2 hyL
      · have h1 := LC_normalizes hP hr.2 (hSC hr.1)
        have e : y = r * t₀ * 1 := by rw [hyr, mul_one]
        rw [e]
        exact swaps_mul_mul ht₀sw (hSC hr.1) (Cen z).one_mem h1.1 h1.2 h1'.1 h1'.2
    · rcases (P27.Psp4.mem_sup_zpowers_iff hconj_t hsq_t).1 hk with hkR | ⟨r, hr, hkr⟩
      · exfalso
        apply hnc
        have hzyS : z * y ∈ S := S.mul_mem hzS hyS
        have hyz' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hSC hyS)
        have hzy2 : z * y * (z * y) = 1 := by
          calc z * y * (z * y) = z * (y * z) * y := by group
            _ = z * (z * y) * y := by rw [hyz']
            _ = (z * z) * (y * y) := by group
            _ = 1 := by rw [hz2, hy2, one_mul]
        have hzy1 : z * y ≠ 1 := by
          intro h
          apply hyz
          calc y = z * (z * y) := by rw [← mul_assoc, hz2, one_mul]
            _ = z := by rw [h, mul_one]
        exact hcos (z * y) hzyS hzy2 hzy1 ⟨z * k, (RC S z).mul_mem hzR hkR, by rw [hyk]; group⟩
      · have h1 := LC_normalizes hP hr.2 (hSC hr.1)
        have e : y = r * t₀ * w₀ := by rw [hyk, hkr]
        rw [e]
        exact swaps_mul_mul ht₀sw (hSC hr.1) hw₀C h1.1 h1.2 hw₀n₁ hw₀n₂

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
