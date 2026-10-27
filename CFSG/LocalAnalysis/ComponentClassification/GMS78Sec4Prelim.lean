module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78L2OutG
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Facts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem exists_mul_eq_of_mem_V {L T : Subgroup G}
    {x : G} (hx : x ∈ gmsV L T) :
    ∃ a ∈ gmsA L T, ∃ t ∈ T ⊓ centralizer (L : Set G), a * t = x := by
  have hN : T ⊓ centralizer (L : Set G) ≤ normalizer ((gmsA L T : Subgroup G) : Set G) := by
    intro t ht
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => ?_)
    exact mem_centralizer_iff.mp (mem_inf.mp ht).2 a (mem_inf.mp (mem_inf.mp ha).1).2
  obtain ⟨t, ht, a, ha, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hN (by rw [sup_comm]; exact hx)
  refine ⟨a, ha, t, ht, ?_⟩
  exact (mem_centralizer_iff.mp (mem_inf.mp ht).2 a (mem_inf.mp (mem_inf.mp ha).1).2)

theorem exists_conj_le_of_isSylowOf [Finite G] {P K Q : Subgroup G} (hP : IsSylowOf 2 P K)
    (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) : ∃ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := by
    intro x
    obtain ⟨n, hn⟩ := hQ ⟨(x : K), mem_subgroupOf.mp x.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨S', hS'⟩ := hQ'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S' S
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h1 : (⟨x, hQK hx⟩ : K) ∈ (S' : Subgroup K) := hS' (mem_subgroupOf.mpr hx)
  have h2 : k * ⟨x, hQK hx⟩ * k⁻¹ ∈ (S : Subgroup K) := by
    rw [← hk, CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
    simpa [mul_assoc] using h1
  rw [hS] at h2
  simpa using mem_subgroupOf.mp h2

theorem exists_mem_normalizer_of_lt [Finite G] {P Q : Subgroup G} (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q)
    (hne : ¬ Q ≤ P) : ∃ a ∈ Q, a ∈ normalizer (P : Set G) ∧ a ∉ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := P.subgroupOf Q with hI
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : Q) ∈ I := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := Q) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : G) ∈ normalizer (P : Set G) := by
    have : x ∈ (normalizer (P : Set G)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hPQ]
      exact hxN
    exact mem_subgroupOf.mp this
  exact ⟨x, x.2, hxN', fun hx => hxI (mem_subgroupOf.mpr hx)⟩

namespace Sec3

variable [Finite G] {L T : Subgroup G} {f : ℕ}

theorem centralizer_le_normalizer_of_mem (h : Sec3 G L T) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht1 : t ≠ 1) (htt : t * t = 1) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨-, -, htight, hNK, -⟩ := h.hyp.standard
  intro g hg
  rw [← hNK]
  by_contra hgN
  have hodd := htight g hgN
  set C := centralizer (L : Set G)
  have hgt : g * t = t * g := mem_centralizer_singleton_iff.mp hg
  have htC : t ∈ C ⊓ C.map (MulAut.conj g).toMonoidHom := by
    refine mem_inf.mpr ⟨ht, mem_map.mpr ⟨t, ht, ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hgt, mul_inv_cancel_right]
  have h2 : orderOf (⟨t, htC⟩ : (C ⊓ C.map (MulAut.conj g).toMonoidHom : Subgroup G)) = 2 := by
    refine orderOf_eq_prime ?_ (fun h1 => ht1 (congrArg Subtype.val h1))
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [sq]
    exact htt
  have h3 := orderOf_dvd_natCard (⟨t, htC⟩ : (C ⊓ C.map (MulAut.conj g).toMonoidHom : Subgroup G))
  rw [h2] at h3
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

theorem gmsA_eq_of_psl2 (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : gmsA L T = T ⊓ L := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hT₁el := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  exact inf_eq_left.mpr (le_centralizer_iff_isMulCommutative.mpr hT₁el.1)

theorem card_le_of_le_normalizer
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {E : Subgroup G}
    (hEN : E ≤ normalizer (L : Set G)) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ Nat.card (gmsV L T) := by
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf h.sylow hEN hEp
  set E' := E.map (MulAut.conj k).toMonoidHom with hE'
  have hE'T : E' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hE'card : Nat.card E' = Nat.card E := card_map_of_injective (MulAut.conj k).injective
  have hV : gmsV L T = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
    show gmsA L T ⊔ _ = _
    rw [h.gmsA_eq_of_psl2 hf e]
  by_contra hlt
  push Not at hlt
  have heq := h.eq_of_psl2 hF hf e hE'T (isElemAbelian_map _ hE) (by rw [← hV, hE'card]; omega)
  rw [← hV] at heq
  rw [← hE'card, heq] at hlt
  exact lt_irrefl _ hlt

theorem mem_V_iff (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {w : G} (hw : w ∈ T) :
    w ∈ gmsV L T ↔ w ∈ L ⊔ centralizer (L : Set G) := by
  have hV : gmsV L T = T ⊓ (L ⊔ centralizer (L : Set G)) := by
    rw [h.inf_sup_eq]
    show gmsA L T ⊔ _ = _
    rw [h.gmsA_eq_of_psl2 hf e]
  rw [hV]
  exact ⟨fun h1 => (mem_inf.mp h1).2, fun h1 => mem_inf.mpr ⟨hw, h1⟩⟩

theorem mem_V_of_commute (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {w : G} (hw : w ∈ T)
    (hwA : ∀ a ∈ gmsA L T, w * a = a * w) : w ∈ gmsV L T := by
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  obtain ⟨m, hm⟩ := h.sylow.isPGroup ⟨w, hw⟩
  have hm' : w ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hP1 : 1 < Nat.card (T ⊓ L : Subgroup G) := by have := h.eight_le_card_T₁; omega
  have hwP : ∀ x ∈ T ⊓ L, w * x = x * w := fun x hx => hwA x (h.gmsA_eq_of_psl2 hf e ▸ hx)
  exact (h.mem_V_iff hf e hw).mpr
    (mem_sup_of_commute hLp hZ (by omega) e h.isSylowOf_T₁ hP1 (h.sylow.le hw) hm' hwP)

theorem mul_inv_mem_V (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {w₁ w₂ : G} (h₁ : w₁ ∈ T) (h₂ : w₂ ∈ T)
    (h₁V : w₁ ∉ gmsV L T) (h₂V : w₂ ∉ gmsV L T) (h₁₁ : w₁ * w₁ ∈ gmsV L T)
    (h₂₂ : w₂ * w₂ ∈ gmsV L T) : w₁ * w₂⁻¹ ∈ gmsV L T := by
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  have hP : ∀ {w : G}, w ∈ T → ∀ x ∈ T ⊓ L, w * x * w⁻¹ ∈ T ⊓ L := fun hw x hx =>
    (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hw) x).mp hx
  rw [h.mem_V_iff hf e h₁] at h₁V
  rw [h.mem_V_iff hf e (mul_mem h₁ h₁)] at h₁₁
  rw [h.mem_V_iff hf e h₂] at h₂V
  rw [h.mem_V_iff hf e (mul_mem h₂ h₂)] at h₂₂
  rw [h.mem_V_iff hf e (mul_mem h₁ (inv_mem h₂))]
  exact mul_inv_mem_sup_of_sq_mem hLp hZ (by omega) e h.isSylowOf_T₁ (h.sylow.le h₁)
    (h.sylow.le h₂) (hP h₁) (hP h₂) h₁V h₂V h₁₁ h₂₂

theorem card_sq_le (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Facts L T (2 ^ f)) {w : G}
    (hw : w ∈ T) (hwV : w ∉ gmsV L T) (hww : w * w ∈ gmsV L T) :
    Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f := by
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  rw [h.mem_V_iff hf e hw] at hwV
  rw [h.mem_V_iff hf e (mul_mem hw hw)] at hww
  have h1 := card_centralizer_sq_le_of_sq_mem hLp hZ (by omega) e h.isSylowOf_T₁ (h.sylow.le hw)
    (fun x hx => (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hw) x).mp hx) hwV hww
  rw [← h.gmsA_eq_of_psl2 hf e, (hX.sylow h).1] at h1
  exact h1

theorem le_V_of_odd (h : Sec3 G L T) (hf : 3 ≤ f) (hodd : Odd f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : T ≤ gmsV L T := by
  classical
  intro w hw
  by_contra hwV
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  obtain ⟨m, hm⟩ := h.sylow.isPGroup ⟨w, hw⟩
  have hm' : w ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hex : ∃ j, w ^ 2 ^ j ∈ gmsV L T := ⟨m, by rw [hm']; exact one_mem _⟩
  have hj₀mem : w ^ 2 ^ Nat.find hex ∈ gmsV L T := Nat.find_spec hex
  have hj₀pos : Nat.find hex ≠ 0 := by
    intro h0
    apply hwV
    have := hj₀mem
    rwa [h0, pow_zero, pow_one] at this
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnot : w ^ 2 ^ i ∉ gmsV L T := Nat.find_min hex (by omega)
  have hw'T : w ^ 2 ^ i ∈ T := pow_mem hw _
  have hsq : w ^ 2 ^ i * w ^ 2 ^ i ∈ gmsV L T := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hi] at hj₀mem
    exact hj₀mem
  rw [h.mem_V_iff hf e (mul_mem hw'T hw'T)] at hsq
  rw [h.mem_V_iff hf e hw'T] at hnot
  exact hnot (mem_sup_of_sq_mem_of_odd hLp hZ (by omega) hodd e h.isSylowOf_T₁
    (h.sylow.le hw'T) (fun x hx => (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hw'T) x).mp hx) hsq)

end Sec3

end CFSG.ComponentClassification.GMS78
