module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightLocalIH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightElem
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightCover

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem relativeWeakClosure_mono_left {C G T S : Subgroup X} (hCG : C ≤ G) :
    relativeWeakClosure C T S ≤ relativeWeakClosure G T S := by
  rw [relativeWeakClosure_le_iff]
  intro x hx hle
  exact rightConjugate_le_relativeWeakClosure (hCG hx) hle

omit [Finite X] in
theorem mem_of_mem_sup_odd {S Y O : Subgroup X} (hS : IsPGroup 2 S) (hYS : Y ≤ S)
    (hYN : Y ≤ Subgroup.normalizer (O : Set X)) (hO : Odd (Nat.card O)) {x : X} (hxS : x ∈ S)
    (hx : x ∈ Y ⊔ O) : x ∈ Y := by
  have hx' : x ∈ (Y : Set X) * (O : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y O hYN]
    exact hx
  obtain ⟨a, ha, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have hoS : o ∈ S := by simpa using S.mul_mem (S.inv_mem (hYS ha)) hxS
  obtain ⟨k, hk⟩ := hS ⟨o, hoS⟩
  have ho1 : o = 1 := eq_one_of_two_pow_of_odd ho hO (congrArg Subtype.val hk)
  rw [ho1, mul_one]
  exact ha

variable {G T S Q H : Subgroup X} {g y : X}

namespace ElemCtx

theorem not_isCyclic (c : ElemCtx G T S Q H g y) : ¬ IsCyclic T := by
  intro hcyc
  obtain ⟨⟨t, ht⟩, hgen⟩ := hcyc.exists_generator
  have hT4 := c.elem.four_le_card
  have hord : orderOf (⟨t, ht⟩ : T) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using c.elem.sq_T t ht)
  have hcard : Nat.card T = orderOf (⟨t, ht⟩ : T) := by
    rw [← Nat.card_zpowers]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv hgen).symm).trans rfl
  have h2 := Nat.le_of_dvd (by norm_num) hord
  omega

theorem exists_ne_one (c : ElemCtx G T S Q H g y) : ∃ t ∈ T, t ≠ 1 := by
  have h4 := c.elem.four_le_card
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr hall
  rw [hbot, Subgroup.card_bot] at h4
  omega

theorem exists_not_mem_W (c : ElemCtx G T S Q H g y) :
    ∃ u ∈ S ⊓ G, u ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hle : S ⊓ G ≤ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
    fun x hx => ⟨hall x hx, hx.2⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_SG c.elem, card_R c.elem] at h1
  have hpos : 0 < Nat.card T * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
  omega

theorem le_sup_of_le (c : ElemCtx G T S Q H g y) {C : Subgroup X} (hPC : S ⊓ G ≤ C) :
    S ≤ C ⊔ T := by
  intro s hs
  obtain ⟨t, ht, k, hk, rfl⟩ := c.frame.mem_sup_iff.mp (c.sylowFrame.sylow.le hs)
  have hkS : k ∈ S := by simpa using S.mul_mem (S.inv_mem (c.sylowFrame.le ht)) hs
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hPC ⟨hkS, hk⟩))

theorem le_normalizer_sup_oddCore (c : ElemCtx G T S Q H g y) {C : Subgroup X} (hCG : C ≤ G)
    (hne : C ≠ G) (hTN : T ≤ Subgroup.normalizer (C : Set X)) (hPC : S ⊓ G ≤ C) :
    C ≤ Subgroup.normalizer ((relativeWeakClosure G T S ⊔ (CFSG.oddCore C).map C.subtype :
      Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.sylowFrame
  have hF := h.toFrame
  have e := c.elem
  have hSCT := c.le_sup_of_le hPC
  have h₁ : SylowFrame C T S := SylowFrame.of_le h hCG hTN hSCT
  have h43₁ := c.hyp43.restrict hCG
  have hidx₁ : T.relIndex (S ⊓ (H ⊓ (C ⊔ T))) ≤ Nat.card T := by
    have heq : S ⊓ (H ⊓ (C ⊔ T)) = S ⊓ H := by
      rw [inf_comm H, ← inf_assoc, inf_eq_left.mpr hSCT]
    rw [heq]
    exact c.index_le
  have hcard : Nat.card (C ⊔ T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) :=
    card_sup_lt hF (lt_of_le_of_ne hCG hne) hTN
  set O := (CFSG.oddCore C).map C.subtype with hOdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact odd_card_oddCore C
  have hCTN : C ⊔ T ≤ Subgroup.normalizer (O : Set X) := by
    have : (CFSG.oddCore C).Characteristic := OddCore.characteristic C
    exact sup_le (fun x hx => mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer hx))
      (fun x hx => mem_normalizer_map_of_characteristic _ (hTN hx))
  rcases conclusion_mod_odd c.ih hcard h₁ h43₁ hidx₁ c.pRank_lt with hN | hab
  swap
  · exact absurd hab (c.not_isMulCommutative_of_le (relative_weak_closure_le _ _ _))
  set WC := relativeWeakClosure C T S with hWCdef
  have hWCS : WC ≤ S := relative_weak_closure_le _ _ _
  have hWCN : WC ≤ Subgroup.normalizer (O : Set X) :=
    (hWCS.trans hSCT).trans hCTN
  have hWCmem : ∀ x ∈ S, x ∈ WC ⊔ O → x ∈ WC := fun x hxS hx =>
    mem_of_mem_sup_odd h.sylow.isPGroup hWCS hWCN hOodd hxS hx
  have hWC : WC = relativeWeakClosure G T S := by
    obtain ⟨u, huP, huW⟩ := c.exists_not_mem_W
    have huC : u ∈ C := hPC huP
    rcases lemma_4_7 h₁ h43₁ hidx₁ with hT | ⟨hcyc, -⟩ | ⟨d, -, hWd, -, -, hWab⟩ |
        ⟨-, hcardW, -, -, -⟩
    ·
      rw [← hWCdef] at hT
      exfalso
      obtain ⟨t, ht, ht1'⟩ := c.exists_ne_one
      have hut : u⁻¹ * t * u = t := by
        have h1 : u⁻¹ * t * u ∈ WC := by
          refine hWCmem _ (S.mul_mem (S.mul_mem (S.inv_mem huP.1) (h.le ht)) huP.1) ?_
          have := (Subgroup.mem_normalizer_iff.mp (hN (C.inv_mem huC)) t).mp
            (Subgroup.mem_sup_left (by rw [hT]; exact ht))
          simpa using this
        rw [hT] at h1
        have h2 : t⁻¹ * (u⁻¹ * t * u) ∈ T ⊓ G := by
          refine ⟨T.mul_mem (T.inv_mem ht) h1, ?_⟩
          have := inv_mul_conj_mem e huP.2 (Subgroup.mem_sup_right ht)
          simpa [mul_assoc] using this
        rw [hF.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h2
        exact h2.symm
      have huZ : u ∈ (T ⊔ rightConjugate T g) ⊓ G := by
        rw [← inf_centralizer_eq_Z e ht ht1']
        refine ⟨huP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc u * t = u * (u⁻¹ * t * u) := by rw [hut]
          _ = t * u := by group
      exact huW (Subgroup.mem_sup_right huZ.1)
    · exact absurd hcyc c.not_isCyclic
    ·
      rw [← hWCdef] at hWd hWab
      exfalso
      obtain ⟨t, ht, ht1'⟩ := c.exists_ne_one
      have hTWC : T ≤ WC := subgroup_le_relative_weak_closure _ _ _ h.le
      have hut : u⁻¹ * t * u ∈ WC := by
        refine hWCmem _ (S.mul_mem (S.mul_mem (S.inv_mem huP.1) (h.le ht)) huP.1) ?_
        have := (Subgroup.mem_normalizer_iff.mp (hN (C.inv_mem huC)) t).mp
          (Subgroup.mem_sup_left (hTWC ht))
        simpa using this
      have hutVZ : u⁻¹ * t * u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G := by
        rw [← conj_M_eq_VZ e huP.1 huW]
        exact conj_mem_rightConjugate (Subgroup.mem_sup_left ht) u
      obtain ⟨v, hv, z, hz, hvz⟩ := mem_VZ_iff e hutVZ
      have hv1 : v ≠ 1 := by
        intro hv1
        rw [hv1, one_mul] at hvz
        have htG : t ∈ G := by
          have h1 := G.mul_mem (G.mul_mem huP.2 (hvz ▸ hz.2)) (G.inv_mem huP.2)
          simpa [mul_assoc] using h1
        have hmem : t ∈ T ⊓ G := ⟨ht, htG⟩
        rw [hF.inf_eq_bot, Subgroup.mem_bot] at hmem
        exact ht1' hmem
      obtain ⟨t', ht', ht'1'⟩ := c.exists_ne_one
      have hnc : t'⁻¹ * (v⁻¹ * t' * v) ≠ 1 := by
        intro h1
        have h2 : t'⁻¹ * (v⁻¹ * t' * v) = (1 : X)⁻¹ * (v⁻¹ * 1 * v) := by
          rw [h1]; group
        exact ht'1' ((e.comm_map hv hv1).2.1 t' ht' 1 T.one_mem h2)
      apply hnc
      have hcomm : (u⁻¹ * t * u) * t' = t' * (u⁻¹ * t * u) := by
        have := hWab.is_comm.comm ⟨_, hut⟩ ⟨t', hTWC ht'⟩
        exact congrArg Subtype.val this
      have hzt : z * t' = t' * z := M_comm' e hz.1 (Subgroup.mem_sup_left ht')
      rw [hvz] at hcomm
      have hvt : v * t' = t' * v := by
        have h1 : v * t' = v * z * t' * z⁻¹ := by
          calc v * t' = v * (z * t') * z⁻¹ := by rw [hzt]; group
            _ = v * z * t' * z⁻¹ := by group
        rw [h1, hcomm]
        group
      calc t'⁻¹ * (v⁻¹ * t' * v) = t'⁻¹ * (v⁻¹ * (t' * v)) := by group
        _ = t'⁻¹ * (v⁻¹ * (v * t')) := by rw [hvt]
        _ = 1 := by group
    ·
      rw [← hWCdef] at hcardW
      apply Subgroup.eq_of_le_of_card_ge (relativeWeakClosure_mono_left hCG)
      rw [hcardW, c.weakClosure_eq, e.card_A]
  rwa [hWC] at hN

theorem le_normalizer_R (c : ElemCtx G T S Q H g y) {C : Subgroup X} (hCG : C ≤ G)
    (hne : C ≠ G) (hTN : T ≤ Subgroup.normalizer (C : Set X)) (hPC : S ⊓ G ≤ C)
    (hCP : C ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)) :
    C ≤ Subgroup.normalizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) := by
  have h := c.sylowFrame
  have hN := c.le_normalizer_sup_oddCore hCG hne hTN hPC
  rw [c.weakClosure_eq] at hN
  set W := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hWdef
  set O := (CFSG.oddCore C).map C.subtype with hOdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact odd_card_oddCore C
  have hWS : W ≤ S := c.elem.A_le_S
  have hWN : W ≤ Subgroup.normalizer (O : Set X) := by
    have : (CFSG.oddCore C).Characteristic := OddCore.characteristic C
    intro w hw
    obtain ⟨t, ht, k, hk, rfl⟩ := c.frame.mem_sup_iff.mp (c.elem.hyp45.le_sup (hWS hw))
    have hkS : k ∈ S := by simpa using S.mul_mem (S.inv_mem (h.le ht)) (hWS hw)
    exact Subgroup.mul_mem _
      (mem_normalizer_map_of_characteristic _ (hTN ht))
      (mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer (hPC ⟨hkS, hk⟩)))
  have hkey : ∀ x ∈ C, ∀ r ∈ W ⊓ G, x⁻¹ * r * x ∈ W ⊓ G := by
    intro x hx r hr
    have hrP : r ∈ S ⊓ G := ⟨hWS hr.1, hr.2⟩
    have h1 : x⁻¹ * r * x ∈ S ⊓ G := by
      have := (Subgroup.mem_normalizer_iff.mp (hCP (C.inv_mem hx)) r).mp hrP
      simpa using this
    have h2 : x⁻¹ * r * x ∈ W ⊔ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hN (C.inv_mem hx)) r).mp
        (Subgroup.mem_sup_left hr.1)
      simpa using this
    exact ⟨mem_of_mem_sup_odd h.sylow.isPGroup hWS hWN hOodd h1.1 h2, h1.2⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have := hkey x⁻¹ (C.inv_mem hx) r hr
    simpa using this
  · intro hr
    have := hkey x hx _ hr
    simpa [mul_assoc] using this

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
