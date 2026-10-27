module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIDiag2
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIStep2
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIDiag

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.false_of_card_ge_eight [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) (hL8 : 8 ≤ Nat.card (normIn T T₁)) : False := by
  have hcT : Nat.card T = Nat.card (normIn T T₁) * 2 := by rw [hq, mul_comm]
  have hB := h.mem_normalizer_normIn
  have e1 : normIn T T₂ = normIn T T₁ := h.normIn_eq hB
  have hwc := h.pair.wc
  have hT := hwc.1
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  obtain ⟨g, hg, x₀, hx₀, l₀, hl₀, hx₀l₀⟩ := h.exists_conj_not_comm hTO hBW h214 hInv hnab hq
  obtain ⟨t₀, ht₀T, ht₀U, x, y, hx, hy, hx1, hy1, hxy, hx0, hy0⟩ :=
    h.sec3.exists_two_mem_conj hcT hL8 hg
  have hS2 := h.sec3.conj_of_mem_normalizer hg
  have hL₂g : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hg T₁
  have hsqg : ∀ z ∈ conjSubgroup g (normIn T₁ T), z * z = 1 := fun z hz =>
    elemAbelian_mul_self (isElemAbelian_conjSubgroup h.sec3.cfg.wc₁.1 g)
      (conjSubgroup_mono (normIn_le T₁ T) hz)
  have hl₀g : l₀ ∉ normIn T (conjSubgroup g T₁) := by
    intro hl
    apply hx₀l₀
    have hx' : x₀ ∈ normIn (conjSubgroup g T₁) T := by
      rw [hL₂g]
      exact hx₀
    exact (hS2.cfg.comm_L_L₁ hl hx').symm
  have atype : ∀ z, z ∈ conjSubgroup g (normIn T₁ T) → z ≠ 1 → ⁅t₀, z⁆ ∈ normIn T T₁ →
      (∀ r ∈ T, ⁅r, z⁆ = 1 ∨ ⁅r, z⁆ = ⁅t₀, z⁆) ∧ z * z = 1 ∧
        z ∈ Subgroup.normalizer (T : Set G) ∧
        z ∈ Subgroup.normalizer (normIn T T₁ : Set G) ∧ z * l₀ ≠ l₀ * z := by
    intro z hz hz1 hz0
    have hvals := h.sec3.values_of_mem_conj hcT hg ht₀T ht₀U hz
    have hzz := hsqg z hz
    have hLE := h.sec3.isLElt_conj hg hz hz1
    have haL : ∀ r ∈ T, ⁅r, z⁆ ∈ normIn T T₁ := fun r hr => by
      rcases hvals r hr with h0 | h0
      · rw [h0]
        exact (normIn T T₁).one_mem
      · rw [h0]
        exact hz0
    exact ⟨hvals, hzz, hLE.transv.1, mem_normalizer_of_values hzz haL hLT,
      fun hc => hl₀g (hLE.cent l₀ (hLT hl₀) hc)⟩
  have hxy_mem : x * y ∈ conjSubgroup g (normIn T₁ T) :=
    (conjSubgroup g (normIn T₁ T)).mul_mem hx hy
  have hxy1 : x * y ≠ 1 := fun h1 => hxy (by
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right (hsqg y hy)])
  have hxy0 : ⁅t₀, x * y⁆ ∈ normIn T T₁ := by
    have hx' : x ∈ normIn (conjSubgroup g T₁) T := by
      rw [hL₂g]
      exact hx
    have hy' : y ∈ normIn (conjSubgroup g T₁) T := by
      rw [hL₂g]
      exact hy
    rw [hS2.cfg.comm_mul_right ht₀T hx' hy']
    exact (normIn T T₁).mul_mem hx0 hy0
  obtain ⟨hvx, hxx, hxN, hxL, hxl⟩ := atype x hx hx1 hx0
  obtain ⟨hvy, hyy, hyN, hyL, hyl⟩ := atype y hy hy1 hy0
  let Kg : Subgroup G :=
    Subgroup.normalizer (T : Set G) ⊓ Subgroup.normalizer (normIn T T₁ : Set G)
  have hNK : sec4N T T₁ T₂ ≤ Kg := fun n hn =>
    ⟨sec4N_le_normalizer_left hn, mem_normalizer_of_commute fun m hm =>
      elemAbelian_mul_comm h.isElemAbelian_sec4N hn (normIn_le_sec4N_left hm)⟩
  have hxK : x ∈ Kg := ⟨hxN, hxL⟩
  have hyK : y ∈ Kg := ⟨hyN, hyL⟩
  have hcl : Subgroup.closure ({x, y} : Set G) ≤ conjSubgroup g (normIn T₁ T) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hx, hy]
  have hclK : Subgroup.closure ({x, y} : Set G) ≤ Kg := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hxK, hyK]
  have hclP : IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_of_le
      (isElemAbelian_conjSubgroup h.sec3.cfg.wc₁.1 g)
      (hcl.trans (conjSubgroup_mono (normIn_le T₁ T))))
  obtain ⟨k, hkK, S, hSP, hSK, hAS, hBS⟩ :=
    exists_two_group_conj_le hclP h.isPGroup_sec4N hclK hNK
  have hkT : k ∈ Subgroup.normalizer (T : Set G) := hkK.1
  have hkL : k ∈ Subgroup.normalizer (normIn T T₁ : Set G) := hkK.2
  have hLk : conjSubgroup k (normIn T T₁) = normIn T T₁ := mem_normalizer_iff_conjSubgroup_eq.1 hkL
  have hxS : x ∈ S := hAS (Subgroup.subset_closure (Set.mem_insert _ _))
  have hyS : y ∈ S := hAS (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have h' := h.conj_of_mem_normalizer hkT
  have hL₁' : normIn T (conjSubgroup k T₁) = normIn T T₁ := by
    rw [normIn_conj_left_of_mem_normalizer hkT T₁, hLk]
  have hS₂ : Sec3 T T₂ := sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj
    h.ne_left h.normIn_ne_bot
  have hL₂' : normIn T (conjSubgroup k T₂) = normIn T T₁ := by
    rw [normIn_conj_left_of_mem_normalizer hkT T₂, e1, hLk]
  have hVS₁ : normIn (conjSubgroup k T₁) T ≤ S := by
    rw [normIn_conj_right_of_mem_normalizer hkT T₁]
    exact (conjSubgroup_mono (normIn_le_sec4N_mid (T₂ := T₂))).trans hBS
  have hVS₂ : normIn (conjSubgroup k T₂) T ≤ S := by
    rw [normIn_conj_right_of_mem_normalizer hkT T₂]
    exact (conjSubgroup_mono (normIn_le_sec4N_right (T₁ := T₁))).trans hBS
  have step2 : ∀ (V : Subgroup G), Sec3 T V → normIn T V = normIn T T₁ → normIn V T ≤ S →
      ∀ z ∈ S, z * z = 1 → ∀ u ∈ normIn T T₁, (∀ r ∈ T, ⁅r, z⁆ = 1 ∨ ⁅r, z⁆ = u) →
        ∃ s ∈ T, conjSubgroup z V = conjSubgroup s V := by
    intro V hSV hVL hVS z hzS hzz u hu hvals
    obtain ⟨s, hs, hsV⟩ := hSV.exists_t_conj_normalizes h214 hInv hSz hnab
      (by rw [hVL]; exact hcT) (by rw [hVL]; exact hL8) hSP (fun w hw => (hSK hw).1)
      (by rw [hVL]; exact fun w hw => (hSK hw).2) hVS hzS hzz (by rw [hVL]; exact hu) hvals
    refine ⟨s, hs, ?_⟩
    calc conjSubgroup z V = conjSubgroup s (conjSubgroup (s⁻¹ * z) V) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
      _ = conjSubgroup s V := by rw [hsV]
  obtain ⟨sx₁, hsx₁, hx₁⟩ := step2 _ (h.sec3.conj_of_mem_normalizer hkT) hL₁' hVS₁ x hxS hxx _ hx0
    hvx
  obtain ⟨sx₂, hsx₂, hx₂⟩ := step2 _ (hS₂.conj_of_mem_normalizer hkT) hL₂' hVS₂ x hxS hxx _ hx0
    hvx
  obtain ⟨sy₁, hsy₁, hy₁⟩ := step2 _ (h.sec3.conj_of_mem_normalizer hkT) hL₁' hVS₁ y hyS hyy _ hy0
    hvy
  obtain ⟨sy₂, hsy₂, hy₂⟩ := step2 _ (hS₂.conj_of_mem_normalizer hkT) hL₂' hVS₂ y hyS hyy _ hy0
    hvy
  have hLV₁ : normIn T T₁ ≤ Subgroup.normalizer ((conjSubgroup k T₁ : Subgroup G) : Set G) := by
    rw [← hL₁']
    exact inf_le_right
  have hLV₂ : normIn T T₁ ≤ Subgroup.normalizer ((conjSubgroup k T₂ : Subgroup G) : Set G) := by
    rw [← hL₂']
    exact inf_le_right
  have hxact : ∀ r ∈ T, x * r * x⁻¹ * r⁻¹ ∈ normIn T T₁ := by
    intro r hr
    have e : x * r * x⁻¹ * r⁻¹ = (⁅r, x⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    rcases hvx r hr with h0 | h0
    · rw [h0, inv_one]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact (normIn T T₁).inv_mem hx0
  have final : ∀ z, z ∈ conjSubgroup g (normIn T₁ T) → z ≠ 1 → ⁅t₀, z⁆ ∈ normIn T T₁ →
      ∀ s ∈ T, conjSubgroup z (conjSubgroup k T₁) = conjSubgroup s (conjSubgroup k T₁) →
        conjSubgroup z (conjSubgroup k T₂) = conjSubgroup s (conjSubgroup k T₂) → False := by
    intro z hz hz1 hz0 s hs h₁ h₂
    obtain ⟨hvz, -, hzN, hzNL, hzl⟩ := atype z hz hz1 hz0
    exact h'.false_of_diag (by rw [hL₁']; exact hq) hs hzN
      (fun l hl => by
        rw [hL₁'] at hl ⊢
        exact conj_mem_of_mem_normalizer hzNL hl)
      (by rw [hL₁']; exact hl₀) hzl (by rw [hL₁']; exact hz0) hvz h₁ h₂
  rcases exists_diag_conj hT hLT hcT hLV₁ hLV₂ hxact ⟨sx₁, hsx₁, hx₁⟩ ⟨sx₂, hsx₂, hx₂⟩
    ⟨sy₁, hsy₁, hy₁⟩ ⟨sy₂, hsy₂, hy₂⟩ with ⟨s, hs, hs₁, hs₂⟩ | ⟨s, hs, hs₁, hs₂⟩ |
      ⟨s, hs, hs₁, hs₂⟩
  · exact final x hx hx1 hx0 s hs hs₁ hs₂
  · exact final y hy hy1 hy0 s hs hs₁ hs₂
  · exact final (x * y) hxy_mem hxy1 hxy0 s hs hs₁ hs₂

end CFSG.CGT.Timmesfeld75
