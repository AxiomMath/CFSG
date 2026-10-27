module

public import CFSG.Goldschmidt75.A2Main
public import CFSG.Goldschmidt75.A2M2
public import CFSG.Goldschmidt75.A2Quot
public import CFSG.Goldschmidt75.B1Steps

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_facts (T : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) :
    S₁ ⊓ S₂ ≤ T ∧ IsMulCommutative (S₁ ⊓ S₂ : Subgroup G) ∧
      fusionStronglyClosed ((S₁ ⊓ S₂ : Subgroup G) : Set G) T ∧
      S₁ ≤ centralizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) ∧
      S₂ ≤ centralizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) := by
  have hc₁ : S₁ ≤ centralizer (S₂ : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hc₂ : S₂ ≤ centralizer (S₁ : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hcomm
  refine ⟨inf_le_left.trans h₁, ⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha g hg => ?_,
    hc₁.trans (centralizer_le inf_le_right), hc₂.trans (centralizer_le inf_le_left)⟩
  · exact mem_centralizer_iff.mp (hc₁ (mem_inf.mp b.2).1) a (mem_inf.mp a.2).2
  · exact mem_inf.mpr ⟨hS₁ a (mem_inf.mp ha).1 g hg, hS₂ a (mem_inf.mp ha).2 g hg⟩

theorem commutator_le_of_pCore_ne_bot
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → A2For H)
    (T : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) (hO : goldschmidtOddCore G = ⊥)
    {TM : Sylow 2 (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G))}
    (hcore : CoreHyp _ TM ((S₁ ⊓ S₂).subgroupOf (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G))))
    (hZ : CFSG.Open.pCore 2 (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ≠ ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G := by
  set M := normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) with hM
  have : M.Normal := normalClosure_normal
  set Z := (CFSG.Open.pCore 2 M).map M.subtype with hZdef
  have : Z.Normal := normal_pCore_map
  have hZA : Z ≤ S₁ ⊓ S₂ := pCore_map_le hcore
  have hZne : Z ≠ ⊥ := fun h => hZ ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  obtain ⟨hAT, -, -, hS₁C, -⟩ := inf_facts T h₁ hS₁ hS₂ hcomm
  set q := QuotientGroup.mk' Z with hq
  have hdisj : S₁.map q ⊓ S₂.map q ≤ (S₁ ⊓ S₂).map q := by
    rintro _ ⟨⟨s₁, hs₁, rfl⟩, ⟨s₂, hs₂, hs₂₁⟩⟩
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hs₂₁
    have hs₁S₂ : s₁ ∈ S₂ := by
      have := mul_mem hs₂ (mem_inf.mp (hZA hs₂₁)).2
      simpa using this
    exact ⟨s₁, mem_inf.mpr ⟨hs₁, hs₁S₂⟩, rfl⟩
  have hX := commutator_le_of_quotient (hIH _ (card_quotient_lt hZne)) T h₁ h₂ hS₁ hS₂ hcomm
    hdisj
  set Y := (goldschmidtOddCore (G ⧸ Z)).comap q with hY
  have hYn : Y.Normal := (goldschmidtOddCore_normal _).comap q
  have hQ : Y ⊓ centralizer (Z : Set G) ≤ Z :=
    le_of_le_centralizer_of_odd hO (normal_inf_normal _ _) inf_le_right
      (T.isPGroup'.to_le (hZA.trans hAT)) (odd_index_of_le_comap_oddCore inf_le_left)
  have hH₁ : normalClosure (S₁ : Set G) ≤ centralizer (Z : Set G) :=
    normalClosure_le_normal fun s hs => centralizer_le hZA (hS₁C hs)
  have hXC : ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      centralizer (Z : Set G) := (commutator_le_left _ _).trans hH₁
  have hMC := le_centralizer_pCore_map hcore
  intro x hx
  have hx1 := hX hx
  rw [← SetLike.mem_coe, mul_normal] at hx1
  obtain ⟨m, hm, y, hy, hmy⟩ := hx1
  replace hmy : m * y = x := hmy
  subst hmy
  have hyC : y ∈ centralizer (Z : Set G) := by
    have := mul_mem (inv_mem (hMC hm)) (hXC hx)
    rwa [inv_mul_cancel_left] at this
  have hyZ := hQ (mem_inf.mpr ⟨hy, hyC⟩)
  exact mem_sup_left (mul_mem hm (map_subtype_le _ hyZ))

theorem commutator_le_of_pCore_eq_bot
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → A2For H)
    (T : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) (hO : goldschmidtOddCore G = ⊥) (hA : S₁ ⊓ S₂ ≠ ⊥)
    (hG : normalClosure (S₁ : Set G) ⊔ normalClosure (S₂ : Set G) = ⊤)
    {TM : Sylow 2 (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G))}
    (hTM : (TM : Subgroup _).map (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)).subtype =
      (T : Subgroup G) ⊓ normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G))
    (hcore : CoreHyp _ TM ((S₁ ⊓ S₂).subgroupOf (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G))))
    (hZ : CFSG.Open.pCore 2 (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)) = ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G := by
  set M := normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) with hM
  have : M.Normal := normalClosure_normal
  obtain ⟨-, -, -, hS₁C, hS₂C⟩ := inf_facts T h₁ hS₁ hS₂ hcomm
  have hMne : M ≠ ⊥ := fun h => hA (le_bot_iff.mp (h ▸ le_normalClosure))
  obtain ⟨K, hK⟩ := exists_comp hcore hZ hMne
  set KG := K.map M.subtype with hKG
  have hKn : KG.Normal := by
    have hN : normalizer (KG : Set G) = ⊤ := by
      rw [eq_top_iff, ← hG]
      exact sup_le (normalClosure_le_normalizer_comp hcore hS₁C hK)
        (normalClosure_le_normalizer_comp hcore hS₂C hK)
    exact normalizer_eq_top_iff.mp hN
  obtain ⟨hquasi, htype⟩ := comp_quasi_type hcore hK
  have hZK := center_comp_eq_bot hcore hZ hK
  have hc : A2Comp T S₁ S₂ KG :=
    ⟨h₁, h₂, hS₁, hS₂, hcomm, hKn, hquasi, center_map_eq_bot hZK, htype,
      omega_comp hcore hTM hK hZK⟩
  have hKne : KG ≠ ⊥ := by
    intro h
    apply hc.omega1_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have := (mem_inf.mp (omega1_le_self _ hx)).2
    rwa [h] at this
  set q := QuotientGroup.mk' KG with hq
  have hdisj : S₁.map q ⊓ S₂.map q ≤ (S₁ ⊓ S₂).map q := by
    rintro _ ⟨⟨s₁, hs₁, rfl⟩, ⟨s₂, hs₂, hs₂₁⟩⟩
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hs₂₁
    have hs₁mem : s₁ ∈ (S₁ ⊔ KG) ⊓ (S₂ ⊔ KG) := by
      refine mem_inf.mpr ⟨mem_sup_left hs₁, ?_⟩
      have := mul_mem_sup hs₂ hs₂₁
      simpa using this
    have h := hc.inf_sup_le hs₁mem
    rw [← SetLike.mem_coe, mul_normal] at h
    obtain ⟨a, ha, k, hk, hak⟩ := h
    refine ⟨a, ha, ?_⟩
    rw [hq, ← hak, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using hk
  have hX := commutator_le_of_quotient (hIH _ (card_quotient_lt hKne)) T h₁ h₂ hS₁ hS₂ hcomm
    hdisj
  set Y := (goldschmidtOddCore (G ⧸ KG)).comap q with hY
  have hXK : ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      KG ⊔ centralizer (KG : Set G) := by
    rcases hc.inner with h | h
    · exact (commutator_le_left _ _).trans (normalClosure_le_normal h)
    · exact (commutator_le_right _ _).trans (normalClosure_le_normal h)
  have hMK := le_sup_centralizer_comp hcore hZ hK
  have hQ : centralizer (KG : Set G) ⊓ Y = ⊥ := by
    have hYn : Y.Normal := (goldschmidtOddCore_normal _).comap q
    have hQn : (centralizer (KG : Set G) ⊓ Y).Normal := normal_inf_normal _ _
    have hodd := odd_index_of_le_comap_oddCore (N := KG)
      (Q := centralizer (KG : Set G) ⊓ Y) inf_le_right
    have hbot : KG.subgroupOf (centralizer (KG : Set G) ⊓ Y) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_subgroupOf] at hx
      have : (x : G) ∈ KG ⊓ centralizer (KG : Set G) := mem_inf.mpr ⟨hx, (mem_inf.mp x.2).1⟩
      rw [hc.inf_centralizer_eq_bot, mem_bot] at this
      exact (mem_bot).mpr (Subtype.ext this)
    rw [hbot, Subgroup.index_bot] at hodd
    have h1 := le_oddCore hQn hodd
    rwa [hO, le_bot_iff] at h1
  intro x hx
  have hx1 := hX hx
  have hYn : Y.Normal := (goldschmidtOddCore_normal _).comap q
  rw [← SetLike.mem_coe, mul_normal] at hx1
  obtain ⟨m, hm, y, hy, hmy⟩ := hx1
  replace hmy : m * y = x := hmy
  subst hmy
  have hyKC : y ∈ KG ⊔ centralizer (KG : Set G) := by
    have := mul_mem (inv_mem (hMK hm)) (hXK hx)
    rwa [inv_mul_cancel_left] at this
  rw [← SetLike.mem_coe, normal_mul] at hyKC
  obtain ⟨k, hk, c, hc', hkc⟩ := hyKC
  replace hkc : k * c = y := hkc
  subst hkc
  have hkY : k ∈ Y := by
    rw [hY, mem_comap, hq, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact one_mem _
  have hcY : c ∈ Y := by
    have := mul_mem (inv_mem hkY) hy
    simpa using this
  have hc1 : c ∈ centralizer (KG : Set G) ⊓ Y := mem_inf.mpr ⟨hc', hcY⟩
  rw [hQ, mem_bot] at hc1
  rw [hc1, mul_one]
  exact mem_sup_left (mul_mem hm (map_subtype_le K hk))

end CFSG.Goldschmidt75
