module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Ru
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Classes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace RuB1

section Pieces

variable {G : Type} [Group G]

theorem mem_of_mem_sup_of_orderOf_eq_two {L₀ W : Subgroup G} (hWodd : Odd (Nat.card W))
    (hinf : L₀ ⊓ W = ⊥) (hWC : W ≤ centralizer (L₀ : Set G)) {u : G} (hu : u ∈ L₀ ⊔ W)
    (hu2 : orderOf u = 2) : u ∈ L₀ := by
  have hL₀C : L₀ ≤ centralizer (W : Set G) := le_centralizer_iff.mp hWC
  have hu' : u ∈ ((L₀ ⊔ W : Subgroup G) : Set G) := hu
  rw [coe_mul_of_left_le_normalizer_right L₀ W (hL₀C.trans (centralizer_le_normalizer W))]
    at hu'
  obtain ⟨l, hl, w, hw, rfl⟩ := Set.mem_mul.1 hu'
  refine mem_left_of_mul_of_pow_two hinf hWodd hl hw (mem_centralizer_iff.mp (hWC hw) l hl)
    (k := 1) ?_
  rw [pow_one, ← hu2]
  exact pow_orderOf_eq_one _

theorem centralizer_conj_le {M : Subgroup G} {x c : G} (hx : centralizer ({x} : Set G) ≤ M)
    (hc : c ∈ M) : centralizer ({c * x * c⁻¹} : Set G) ≤ M := by
  intro y hy
  have h1 : c⁻¹ * y * c ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [hy]
      _ = x * (c⁻¹ * y * c) := by group
  have h2 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem hc (hx h1)) (M.inv_mem hc)

theorem fusion_of_two_reps {M : Subgroup G} {f t : G} (hft : ∀ g : G, g * f * g⁻¹ ≠ t)
    (hrep : ∀ u ∈ M, orderOf u = 2 → (∃ c ∈ M, c * f * c⁻¹ = u) ∨ ∃ c ∈ M, c * t * c⁻¹ = u) :
    ∀ u ∈ M, orderOf u = 2 → ∀ g : G, g * u * g⁻¹ ∈ M →
      ∃ c ∈ M, c * u * c⁻¹ = g * u * g⁻¹ := by
  refine AS81.HeSE.fusion_of_reps M ({f, t} : Set G) (fun u hu hu2 => ?_) (fun a ha b hb g hg => ?_)
  · rcases hrep u hu hu2 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact ⟨f, Set.mem_insert _ _, c⁻¹, M.inv_mem hc, by group⟩
    · exact ⟨t, Set.mem_insert_of_mem _ rfl, c⁻¹, M.inv_mem hc, by group⟩
  · have hft' : ∀ g : G, g * t * g⁻¹ ≠ f := fun g h => hft g⁻¹ (by rw [← h]; group)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ⟨1, M.one_mem, by group⟩
    · exact absurd hg (hft g)
    · exact absurd hg (hft' g)
    · exact ⟨1, M.one_mem, by group⟩

end Pieces


theorem exists_conj_eq_of_ru {G : Type} [Group G] {L₀ : Subgroup G}
    (hL₀ : Nonempty (L₀ ≃* NativeSporadic.Ru)) {f t : G} (hf : f ∈ L₀) (ht : t ∈ L₀)
    (hf2 : orderOf f = 2) (ht2 : orderOf t = 2) (hft : ∀ g : G, g * f * g⁻¹ ≠ t) {u : G}
    (hu : u ∈ L₀) (hu2 : orderOf u = 2) :
    (∃ c ∈ L₀, c * f * c⁻¹ = u) ∨ ∃ c ∈ L₀, c * t * c⁻¹ = u := by
  have hne : Nat.card ↥(L₀ ⊓ centralizer ({f} : Set G)) ≠
      Nat.card ↥(L₀ ⊓ centralizer ({t} : Set G)) := by
    intro h
    obtain ⟨c, -, hc⟩ := (ru_involution_classes_sub hL₀ hf ht hf2 ht2).2.2 h
    exact hft c hc
  obtain ⟨hfc, hfu⟩ := ru_involution_classes_sub hL₀ hf hu hf2 hu2
  obtain ⟨htc, htu⟩ := ru_involution_classes_sub hL₀ ht hu ht2 hu2
  obtain ⟨huc, -⟩ := ru_involution_classes_sub hL₀ hu hu hu2 hu2
  by_cases h : Nat.card ↥(L₀ ⊓ centralizer ({f} : Set G)) =
      Nat.card ↥(L₀ ⊓ centralizer ({u} : Set G))
  · exact Or.inl (hfu.2 h)
  · exact Or.inr (htu.2 (by omega))

theorem false_of_isSolvable_of_ru {G : Type} [Group G] {L₀ M : Subgroup G}
    (hL₀ : Nonempty (L₀ ≃* NativeSporadic.Ru)) (hL₀M : L₀ ≤ M) (hM : Group.IsSolvable M)
    {f : G} (hf : f ∈ L₀) (hf1 : f ≠ 1) : False := by
  obtain ⟨e⟩ := hL₀
  have hsRu : IsSimpleGroup NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have : IsSimpleGroup L₀ := @MulEquiv.isSimpleGroup L₀ _ NativeSporadic.Ru _ hsRu e
  have : Group.IsSolvable L₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hL₀M)
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr this
  have hfZ : (⟨f, hf⟩ : L₀) ∈ center L₀ := mem_center_iff.mpr fun g => hcomm g _
  rw [center_eq_bot_of_ru e, mem_bot] at hfZ
  exact hf1 (congrArg Subtype.val hfZ)

theorem false_of_normalizer_eq_sup_ru {G : Type} [Group G] [Finite G] {L₀ W : Subgroup G}
    (hL₀ : Nonempty (L₀ ≃* NativeSporadic.Ru)) (hWodd : Odd (Nat.card W))
    (hN : normalizer (W : Set G) = L₀ ⊔ W) (hinf : L₀ ⊓ W = ⊥)
    (hWC : W ≤ centralizer (L₀ : Set G)) (hNtop : normalizer (W : Set G) ≠ ⊤)
    (hrank : 2 ≤ twoRank G) {f t : G} (hf : f ∈ L₀) (ht : t ∈ L₀) (hf2 : orderOf f = 2)
    (ht2 : orderOf t = 2) (hft : ∀ g : G, g * f * g⁻¹ ≠ t)
    (hCf : centralizer ({f} : Set G) ≤ normalizer (W : Set G))
    (hCt : centralizer ({t} : Set G) ≤ normalizer (W : Set G)) : False := by
  have hL₀M : L₀ ≤ normalizer (W : Set G) := by
    rw [hN]
    exact le_sup_left
  have hinvL : ∀ u ∈ normalizer (W : Set G), orderOf u = 2 → u ∈ L₀ := fun u hu hu2 =>
    mem_of_mem_sup_of_orderOf_eq_two hWodd hinf hWC (hN ▸ hu) hu2
  have hrep : ∀ u ∈ normalizer (W : Set G), orderOf u = 2 →
      (∃ c ∈ normalizer (W : Set G), c * f * c⁻¹ = u) ∨
        ∃ c ∈ normalizer (W : Set G), c * t * c⁻¹ = u := by
    intro u hu hu2
    rcases exists_conj_eq_of_ru hL₀ hf ht hf2 ht2 hft (hinvL u hu hu2) hu2 with
      ⟨c, hc, h⟩ | ⟨c, hc, h⟩
    · exact Or.inl ⟨c, hL₀M hc, h⟩
    · exact Or.inr ⟨c, hL₀M hc, h⟩
  have hcent : ∀ u ∈ normalizer (W : Set G), orderOf u = 2 →
      centralizer ({u} : Set G) ≤ normalizer (W : Set G) := by
    intro u hu hu2
    rcases hrep u hu hu2 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact centralizer_conj_le hCf hc
    · exact centralizer_conj_le hCt hc
  have hev : Even (Nat.card (normalizer (W : Set G))) := by
    have h := Subgroup.orderOf_dvd_natCard _ (hL₀M hf)
    rw [hf2] at h
    exact even_iff_two_dvd.mpr h
  have hSE := AS81.HeSE.isStronglyEmbedded_of_fusion _ hNtop hev (fusion_of_two_reps hft hrep)
    hcent
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hf2
    exact absurd hf2 (by norm_num)
  exact false_of_isSolvable_of_ru hL₀ hL₀M
    (AschbacherStrongEmbedding.strongly_embedded_solvable G _ hSE hrank) hf hf1

end RuB1

namespace SzMinCounter

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem false_of_b1Frame
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hW : AS76b.oddCoreIn (centralizer (L : Set G)) ≠ ⊥) {L₀ : Subgroup G}
    (hfr : Sec3.B1Frame L T L₀)
    (hstar : ∃ f ∈ gmsA L T, f ≠ 1 ∧ centralizer ({f} : Set G) ≤
      normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)) : False := by
  obtain ⟨f, hfA, hf1, hCf⟩ := hstar
  have hWodd := AS76b.odd_card_oddCoreIn (centralizer (L : Set G))
  have hNtop : normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) ≠ ⊤ := by
    intro htop
    have hn : (AS76b.oddCoreIn (centralizer (L : Set G))).Normal :=
      normalizer_eq_top_iff.mp htop
    have h1 := RankTwoSporadic.le_standardComponentOddCore hn hWodd
    rw [hM.hyp.oddCore, le_bot_iff] at h1
    exact hW h1
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le eS
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h3 hF
  have hT₀el := h3.isElemAbelian_T₀ hF
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hrank : 2 ≤ twoRank G :=
    CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G _ hT₀el 2 (by rw [h4]; norm_num)
  obtain ⟨t, htT₀, ht1⟩ : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 := by
    by_contra h
    push Not at h
    rw [(eq_bot_iff_forall _).2 h, card_bot] at h4
    norm_num at h4
  have hf2 : orderOf f = 2 :=
    orderOf_eq_prime (hVel.2 f ((le_sup_left : gmsA L T ≤ gmsV L T) hfA)) hf1
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hT₀el.2 t htT₀) ht1
  have hft : ∀ g : G, g * f * g⁻¹ ≠ t := by
    intro g hg
    have htV : g * f * g⁻¹ ∈ gmsV L T := by
      rw [hg]
      exact (le_sup_right : T ⊓ centralizer (L : Set G) ≤ gmsV L T) htT₀
    have htA := h313.stronglyClosed f hfA g htV
    rw [hg] at htA
    refine ht1 (eq_one_of_mem_of_mem_centralizer hZ (hAL htA) (mem_inf.mp htT₀).2 ?_)
    rw [← pow_two]
    exact hT₀el.2 t htT₀
  exact RuB1.false_of_normalizer_eq_sup_ru hfr.ru hWodd hfr.normalizer_eq hfr.inf_eq
    hfr.centralizer_eq.ge hNtop hrank (hfr.le (hAL hfA)) (hfr.T_le (mem_inf.mp htT₀).1) hf2 ht2
    hft hCf (hM.centralizer_le_normalizer_oddCoreIn h3 hF htT₀ ht1)

end SzMinCounter

end CFSG.ComponentClassification.GMS78
