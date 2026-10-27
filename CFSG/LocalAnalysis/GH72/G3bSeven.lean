module

public import CFSG.LocalAnalysis.GH72.G3bEleven
public import CFSG.LocalAnalysis.GH72.G3bNine

public section

namespace CFSG.GH72

open Subgroup

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem prop_3_7 (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁', S₂', hd, h₂, h₃⟩ := lemma_3_9 𝔖 h₁
  have h₁'_raw : IsDihNonab S₁' := by
    rcases hd.dih₁.isKleinFour_or_isDihNonab with hK | hN
    · exfalso
      haveI : IsKleinFour ↥S₁' := hK
      haveI : Nontrivial ↥S₁' :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four]; norm_num)
      obtain ⟨b, hb1⟩ := exists_ne (1 : ↥S₁')
      haveI : Fintype ↥S₁' := Fintype.ofFinite ↥S₁'
      let s : Finset ↥S₁' := {1, b}
      have hs : s.card = 2 := by
        change ({1, b} : Finset ↥S₁').card = 2
        exact Finset.card_pair (Ne.symm hb1)
      have huniv : (Finset.univ : Finset ↥S₁').card = 4 := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsKleinFour.card_four]
      have hlt : s.card < (Finset.univ : Finset ↥S₁').card := by
        rw [hs, huniv]
        norm_num
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hc1 : c ≠ 1 := fun h => hc (by simp [s, h])
      have hcb : c ≠ b := fun h => hc (by simp [s, h])
      have hb_mul : (b : G) * (b : G) = 1 := by
        rw [← Subgroup.coe_mul, IsKleinFour.mul_self b, Subgroup.coe_one]
      have hc_mul : (c : G) * (c : G) = 1 := by
        rw [← Subgroup.coe_mul, IsKleinFour.mul_self c, Subgroup.coe_one]
      have hb_ne1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hc_ne1 : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
      have hb_ord : orderOf (b : G) = 2 := orderOf_eq_prime (by rwa [pow_two]) hb_ne1
      have hc_ord : orderOf (c : G) = 2 := orderOf_eq_prime (by rwa [pow_two]) hc_ne1
      have hcommK : IsMulCommutative ↥S₁' := IsKleinFour.isMulCommutative
      have hS₁'_le_Cb : S₁' ≤ C (b : G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := isMulCommutative_iff.mp hcommK (⟨a, ha⟩ : ↥S₁') b
        simpa using congrArg (fun t : ↥S₁' => (t : G)) h
      have hS₁'_le_Cc : S₁' ≤ C (c : G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := isMulCommutative_iff.mp hcommK (⟨a, ha⟩ : ↥S₁') c
        simpa using congrArg (fun t : ↥S₁' => (t : G)) h
      have hS₂'_le_Cb : S₂' ≤ C (b : G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hd.commute ha) (b : G) b.2).symm
      have hS₂'_le_Cc : S₂' ≤ C (c : G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hd.commute ha) (c : G) c.2).symm
      have hS_b : (𝔖.S : Subgroup G) ≤ C (b : G) := by
        rw [← hd.sup_eq]
        exact sup_le hS₁'_le_Cb hS₂'_le_Cb
      have hS_c : (𝔖.S : Subgroup G) ≤ C (c : G) := by
        rw [← hd.sup_eq]
        exact sup_le hS₁'_le_Cc hS₂'_le_Cc
      obtain ⟨g, -, hg⟩ := h₂ (b : G) b.2 (c : G) c.2 hb_ord hc_ord
      have hconj : IsConj (b : G) (c : G) := isConj_iff.mpr ⟨g, hg⟩
      have heq : (b : G) = (c : G) :=
        lemma_3_8 𝔖 h₁ (b : G) (hd.le_left b.2) (c : G) (hd.le_left c.2) hS_b hS_c
          hb_ord hconj
      exact hcb (Subtype.ext heq.symm)
    · exact hN
  let 𝔖' : Sec3Setting G :=
    { S := 𝔖.S
      S₁ := S₁'
      S₂ := S₂'
      decomp := hd
      noIndexTwo := 𝔖.noIndexTwo }
  have h₁' : IsDihNonab 𝔖'.S₁ := h₁'_raw
  have h38 := lemma_3_8 𝔖' h₁'
  have h311 := lemma_3_11 𝔖' h₁' h₂ h₃
  obtain ⟨z₁, hz₁S₁, hz₁ord, hz₁cent⟩ :=
    exists_central_involution S₁' (isDih_of_isDihNonab h₁'_raw)
  obtain ⟨z₂, hz₂S₂, hz₂ord, hz₂cent⟩ :=
    exists_central_involution S₂' (isDih_of_isDihNonab hd.dih₂)
  have hz₁sq : z₁ * z₁ = 1 := by
    simpa [hz₁ord, pow_two] using pow_orderOf_eq_one z₁
  have hz₂sq : z₂ * z₂ = 1 := by
    simpa [hz₂ord, pow_two] using pow_orderOf_eq_one z₂
  have hz₁_ne1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁ord
    omega
  have hz₂_ne1 : z₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₂ord
    omega
  have hS₂_le_Cz₁ : S₂' ≤ C z₁ := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hd.commute hy) z₁ hz₁S₁).symm
  have hS₁_le_Cz₂ : S₁' ≤ C z₂ := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hd.commute hz₂S₂) y hy
  have hS_z₁ : (𝔖.S : Subgroup G) ≤ C z₁ := by
    rw [← hd.sup_eq]
    exact sup_le hz₁cent hS₂_le_Cz₁
  have hS_z₂ : (𝔖.S : Subgroup G) ≤ C z₂ := by
    rw [← hd.sup_eq]
    exact sup_le hS₁_le_Cz₂ hz₂cent
  have hz₁S : z₁ ∈ (𝔖.S : Subgroup G) := hd.le_left hz₁S₁
  have hz₂S : z₂ ∈ (𝔖.S : Subgroup G) := hd.le_right hz₂S₂
  have hcommz : z₁ * z₂ = z₂ * z₁ := hd.comm hz₁S₁ hz₂S₂
  have hzprodsq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hcommz]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz₁sq, hz₂sq, one_mul]
  have hzprodS : z₁ * z₂ ∈ (𝔖.S : Subgroup G) := by
    rw [← hd.sup_eq]
    exact Subgroup.mul_mem_sup hz₁S₁ hz₂S₂
  have hS_zprod : (𝔖.S : Subgroup G) ≤ C (z₁ * z₂) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : s * z₁ = z₁ * s := Subgroup.mem_centralizer_singleton_iff.mp (hS_z₁ hs)
    have h2 : s * z₂ = z₂ * s := Subgroup.mem_centralizer_singleton_iff.mp (hS_z₂ hs)
    calc s * (z₁ * z₂) = s * z₁ * z₂ := by group
      _ = z₁ * s * z₂ := by rw [h1]
      _ = z₁ * (s * z₂) := by group
      _ = z₁ * (z₂ * s) := by rw [h2]
      _ = (z₁ * z₂) * s := by group
  have hz₂_notS₁ : z₂ ∉ S₁' := by
    intro h
    have hmem : z₂ ∈ S₁' ⊓ S₂' := Subgroup.mem_inf.mpr ⟨h, hz₂S₂⟩
    rw [hd.inf_eq] at hmem
    have hone : z₂ = 1 := Subgroup.mem_bot.mp hmem
    exact hz₂_ne1 hone
  have hz₁_notS₂ : z₁ ∉ S₂' := by
    intro h
    have hmem : z₁ ∈ S₁' ⊓ S₂' := Subgroup.mem_inf.mpr ⟨hz₁S₁, h⟩
    rw [hd.inf_eq] at hmem
    have hone : z₁ = 1 := Subgroup.mem_bot.mp hmem
    exact hz₁_ne1 hone
  have hzprod_ne1 : z₁ * z₂ ≠ 1 := by
    intro h
    have hz₂S₁ : z₂ ∈ S₁' := by
      have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by
        calc z₂ = 1 * z₂ := (one_mul z₂).symm
          _ = (z₁ * z₁) * z₂ := by rw [hz₁sq]
          _ = z₁ * (z₁ * z₂) := by group
      rw [hz₂eq, h, mul_one]
      exact hz₁S₁
    exact hz₂_notS₁ hz₂S₁
  have hzprod_ord : orderOf (z₁ * z₂) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hzprod_ne1
  have hzprod_notS₁ : z₁ * z₂ ∉ S₁' := by
    intro h
    have hz₂S₁ : z₂ ∈ S₁' := by
      have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by
        calc z₂ = 1 * z₂ := (one_mul z₂).symm
          _ = (z₁ * z₁) * z₂ := by rw [hz₁sq]
          _ = z₁ * (z₁ * z₂) := by group
      rw [hz₂eq]
      exact Subgroup.mul_mem S₁' hz₁S₁ h
    exact hz₂_notS₁ hz₂S₁
  have hzprod_notS₂ : z₁ * z₂ ∉ S₂' := by
    intro h
    have hz₁S₂ : z₁ ∈ S₂' := by
      have hz₁eq : z₁ = (z₁ * z₂) * z₂ := by
        calc z₁ = z₁ * 1 := (mul_one z₁).symm
          _ = z₁ * (z₂ * z₂) := by rw [hz₂sq]
          _ = (z₁ * z₂) * z₂ := by group
      rw [hz₁eq]
      exact Subgroup.mul_mem S₂' h hz₂S₂
    exact hz₁_notS₂ hz₁S₂
  have hne : z₁ ≠ z₂ := by
    intro h
    exact hz₁_notS₂ (h ▸ hz₂S₂)
  have hnot₁₂ : ∀ x ∈ S₁', ∀ y ∈ S₂', orderOf x = 2 → orderOf y = 2 → ¬ IsConj x y := by
    intro x hx y hy hx2 hy2 hconj
    obtain ⟨g, -, hg⟩ := h₂ x hx z₁ hz₁S₁ hx2 hz₁ord
    obtain ⟨h, -, hh⟩ := h₃ y hy z₂ hz₂S₂ hy2 hz₂ord
    have hxz : IsConj x z₁ := isConj_iff.mpr ⟨g, hg⟩
    have hyz : IsConj y z₂ := isConj_iff.mpr ⟨h, hh⟩
    have hzz : IsConj z₁ z₂ := hxz.symm.trans (hconj.trans hyz)
    exact hne (h38 z₁ hz₁S z₂ hz₂S hS_z₁ hS_z₂ hz₁ord hzz)
  have hnot₁off : ∀ x ∈ S₁', ∀ y ∈ (𝔖.S : Subgroup G), orderOf x = 2 → orderOf y = 2 →
      y ∉ S₁' → y ∉ S₂' → ¬ IsConj x y := by
    intro x hx y hyS hx2 hy2 hy1 hy2' hconj
    obtain ⟨g, -, hg⟩ := h₂ x hx z₁ hz₁S₁ hx2 hz₁ord
    have hxz : IsConj x z₁ := isConj_iff.mpr ⟨g, hg⟩
    have hyz : IsConj y (z₁ * z₂) :=
      h311 y hyS (z₁ * z₂) hzprodS hy1 hy2' hzprod_notS₁ hzprod_notS₂ hy2 hzprod_ord
    have hzz : IsConj z₁ (z₁ * z₂) := hxz.symm.trans (hconj.trans hyz)
    have heq : z₁ = z₁ * z₂ :=
      h38 z₁ hz₁S (z₁ * z₂) hzprodS hS_z₁ hS_zprod hz₁ord hzz
    have hz₂one : z₂ = 1 := by
      have h := congrArg (fun t => z₁⁻¹ * t) heq
      simpa [mul_assoc] using h.symm
    exact hz₂_ne1 hz₂one
  have hnot₂off : ∀ x ∈ S₂', ∀ y ∈ (𝔖.S : Subgroup G), orderOf x = 2 → orderOf y = 2 →
      y ∉ S₁' → y ∉ S₂' → ¬ IsConj x y := by
    intro x hx y hyS hx2 hy2 hy1 hy2' hconj
    obtain ⟨g, -, hg⟩ := h₃ x hx z₂ hz₂S₂ hx2 hz₂ord
    have hxz : IsConj x z₂ := isConj_iff.mpr ⟨g, hg⟩
    have hyz : IsConj y (z₁ * z₂) :=
      h311 y hyS (z₁ * z₂) hzprodS hy1 hy2' hzprod_notS₁ hzprod_notS₂ hy2 hzprod_ord
    have hzz : IsConj z₂ (z₁ * z₂) := hxz.symm.trans (hconj.trans hyz)
    have heq : z₂ = z₁ * z₂ :=
      h38 z₂ hz₂S (z₁ * z₂) hzprodS hS_z₂ hS_zprod hz₂ord hzz
    have hz₁one : z₁ = 1 := by
      have h := congrArg (fun t => t * z₂⁻¹) heq
      simpa [mul_assoc] using h.symm
    exact hz₁_ne1 hz₁one
  refine ⟨S₁', S₂', hd, ?_⟩
  refine
    { conj₁ := fun x hx y hy hx2 hy2 => ?_
      conj₂ := fun x hx y hy hx2 hy2 => ?_
      conj₃ := fun x hx y hy hx1 hx2 hy1 hy2 hxo hyo => ?_
      separate := fun x hx y hy hx2 hconj => ?_ }
  · obtain ⟨g, -, hg⟩ := h₂ x hx y hy hx2 hy2
    exact isConj_iff.mpr ⟨g, hg⟩
  · obtain ⟨g, -, hg⟩ := h₃ x hx y hy hx2 hy2
    exact isConj_iff.mpr ⟨g, hg⟩
  · exact h311 x (hd.sup_eq ▸ hx) y (hd.sup_eq ▸ hy) hx1 hx2 hy1 hy2 hxo hyo
  · have hy2 : orderOf y = 2 := hconj.orderOf_eq.symm.trans hx2
    have hxS : x ∈ (𝔖.S : Subgroup G) := by rw [← hd.sup_eq]; exact hx
    have hyS : y ∈ (𝔖.S : Subgroup G) := by rw [← hd.sup_eq]; exact hy
    by_cases hx1 : x ∈ S₁'
    · have hx_ne1 : x ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hx2
        omega
      have hx2' : x ∉ S₂' := by
        intro h
        have hmem : x ∈ S₁' ⊓ S₂' := Subgroup.mem_inf.mpr ⟨hx1, h⟩
        rw [hd.inf_eq] at hmem
        exact hx_ne1 (Subgroup.mem_bot.mp hmem)
      have hy2' : y ∉ S₂' := by
        intro h
        exact hnot₁₂ x hx1 y h hx2 hy2 hconj
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          by_contra hy1
          by_cases hy2'' : y ∈ S₂'
          · exact hnot₁₂ x hx1 y hy2'' hx2 hy2 hconj
          · exact hnot₁off x hx1 y hyS hx2 hy2 hy1 hy2'' hconj
        · intro hy1
          exact hx1
      · exact ⟨fun h => (hx2' h).elim, fun h => (hy2' h).elim⟩
    · by_cases hx2mem : x ∈ S₂'
      · have hy1 : y ∉ S₁' := by
          intro h
          exact hnot₁₂ y h x hx2mem hy2 hx2 hconj.symm
        have hy2' : y ∈ S₂' := by
          by_contra hy2''
          by_cases hy1' : y ∈ S₁'
          · exact hnot₁₂ y hy1' x hx2mem hy2 hx2 hconj.symm
          · exact hnot₂off x hx2mem y hyS hx2 hy2 hy1' hy2'' hconj
        refine ⟨⟨fun h => (hx1 h).elim, fun h => (hy1 h).elim⟩, ?_⟩
        exact ⟨fun _ => hy2', fun _ => hx2mem⟩
      · have hy1 : y ∉ S₁' := by
          intro h
          exact hnot₁off y h x hxS hy2 hx2 hx1 hx2mem hconj.symm
        have hy2' : y ∉ S₂' := by
          intro h
          exact hnot₂off y h x hxS hy2 hx2 hx1 hx2mem hconj.symm
        exact ⟨⟨fun h => (hx1 h).elim, fun h => (hy1 h).elim⟩,
          ⟨fun h => (hx2mem h).elim, fun h => (hy2' h).elim⟩⟩

end Sec3Setting

end CFSG.GH72
