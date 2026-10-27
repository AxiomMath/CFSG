module

public import CFSG.Goldschmidt75.A2Cases
public import CFSG.Goldschmidt75.TheoremA

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_oddCore_ne_bot (hIH : A2For (G ⧸ goldschmidtOddCore G))
    (T : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G := by
  set O := goldschmidtOddCore G with hO
  set q := QuotientGroup.mk' O with hq
  have hdisj : S₁.map q ⊓ S₂.map q ≤ (S₁ ⊓ S₂).map q := by
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hba
    have h1 := eq_one_of_mem_odd_of_mem_sylow T odd_card_oddCore hba
      (mul_mem (inv_mem (h₂ hb)) (h₁ ha))
    have heq : b = a := inv_mul_eq_one.mp h1
    exact ⟨a, mem_inf.mpr ⟨ha, heq ▸ hb⟩, rfl⟩
  have h := commutator_le_of_quotient hIH T h₁ h₂ hS₁ hS₂ hcomm hdisj
  rwa [oddCore_quotient_eq_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h

theorem normalClosure_le_map_normalClosure (T : Sylow 2 G) {S G₀ : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hG₀ : normalClosure (S : Set G) ≤ G₀) :
    normalClosure (S : Set G) ≤
      (normalClosure ((S.subgroupOf G₀ : Subgroup G₀) : Set G₀)).map G₀.subtype := by
  refine (closure_le _).mpr ?_
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hsx
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure T hST hS c⁻¹
  have h1 : c * s * c⁻¹ ∈ conjSub m S := by
    rw [← hmeq, mem_conjSub]
    simpa [mul_assoc] using hs
  rw [mem_conjSub] at h1
  have hmG₀ : m ∈ G₀ := hG₀ hm
  have hsG₀ : m * (c * s * c⁻¹) * m⁻¹ ∈ G₀ := hG₀ (le_normalClosure h1)
  have h2 : (⟨m * (c * s * c⁻¹) * m⁻¹, hsG₀⟩ : G₀) ∈
      normalClosure ((S.subgroupOf G₀ : Subgroup G₀) : Set G₀) :=
    subset_normalClosure (mem_subgroupOf.mpr h1)
  have h3 := (normalClosure_normal (s := ((S.subgroupOf G₀ : Subgroup G₀) : Set G₀))).conj_mem _
    h2 (⟨m, hmG₀⟩ : G₀)⁻¹
  refine ⟨_, h3, ?_⟩
  simp [mul_assoc]

theorem commutator_le_of_lt {S₁ S₂ : Subgroup G}
    (hIH : A2For (normalClosure (S₁ : Set G) ⊔ normalClosure (S₂ : Set G) : Subgroup G))
    (T : Sylow 2 G) (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G := by
  set G₀ := normalClosure (S₁ : Set G) ⊔ normalClosure (S₂ : Set G) with hG₀
  have : G₀.Normal := Subgroup.sup_normal _ _
  have hH₁ : normalClosure (S₁ : Set G) ≤ G₀ := le_sup_left
  have hH₂ : normalClosure (S₂ : Set G) ≤ G₀ := le_sup_right
  have hS₁G₀ : S₁ ≤ G₀ := le_normalClosure.trans hH₁
  have hS₂G₀ : S₂ ≤ G₀ := le_normalClosure.trans hH₂
  obtain ⟨TH, hTH₁, hTH₂, hcl₁, hcl₂⟩ :=
    exists_sylow_subgroupOf T h₁ h₂ hS₁ hS₂ (sup_le hS₁G₀ hS₂G₀)
  have hcomm' : ⁅S₁.subgroupOf G₀, S₂.subgroupOf G₀⁆ = ⊥ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hS₁G₀, map_subgroupOf_eq_of_le hS₂G₀, hcomm,
      Subgroup.map_bot]
  have h := hIH TH _ _ hTH₁ hTH₂ hcl₁ hcl₂ hcomm'
  have hmap := Subgroup.map_mono (f := G₀.subtype) h
  rw [map_commutator, Subgroup.map_sup] at hmap
  have hAmap : (normalClosure ((S₁.subgroupOf G₀ ⊓ S₂.subgroupOf G₀ : Subgroup G₀) :
      Set G₀)).map G₀.subtype ≤ normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) := by
    refine (map_normalClosure_le _ _).trans (normalClosure_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_subgroupOf.mp (mem_inf.mp hx).1, mem_subgroupOf.mp (mem_inf.mp hx).2⟩
  have hOmap : (goldschmidtOddCore G₀).map G₀.subtype ≤ goldschmidtOddCore G :=
    oddCoreOf_le_of_normal
  calc ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆
      ≤ ⁅(normalClosure ((S₁.subgroupOf G₀ : Subgroup G₀) : Set G₀)).map G₀.subtype,
          (normalClosure ((S₂.subgroupOf G₀ : Subgroup G₀) : Set G₀)).map G₀.subtype⁆ :=
        commutator_mono (normalClosure_le_map_normalClosure T h₁ hS₁ hH₁)
          (normalClosure_le_map_normalClosure T h₂ hS₂ hH₂)
    _ ≤ _ := hmap
    _ ≤ _ := sup_le_sup hAmap hOmap

theorem a2For
    (G : Type) [Group G] [Finite G] : A2For G := by
  suffices key : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → A2For G from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn T S₁ S₂ h₁ h₂ hS₁ hS₂ hcomm
  have hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → A2For H :=
    fun H _ _ hH => ih _ (hn ▸ hH) H rfl
  by_cases hO : goldschmidtOddCore G = ⊥
  swap
  · exact commutator_le_of_oddCore_ne_bot (hIH _ (card_quotient_lt hO)) T h₁ h₂ hS₁ hS₂ hcomm
  by_cases hA : S₁ ⊓ S₂ = ⊥
  · exact (theoremA T T h₁ h₂ hS₁ hS₂ hcomm hA).trans le_sup_right
  by_cases hG : normalClosure (S₁ : Set G) ⊔ normalClosure (S₂ : Set G) = ⊤
  swap
  · exact commutator_le_of_lt (hIH _ (card_lt_of_ne_top hG)) T h₁ h₂ hS₁ hS₂ hcomm
  obtain ⟨hAT, hAab, hAcl, -, -⟩ := inf_facts T h₁ hS₁ hS₂ hcomm
  obtain ⟨TM, hTM, hcore⟩ := exists_coreHyp T hAT hAab hAcl hO
  by_cases hZ : CFSG.Open.pCore 2 (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)) = ⊥
  · exact commutator_le_of_pCore_eq_bot hIH T h₁ h₂ hS₁ hS₂ hcomm hO hA hG hTM hcore hZ
  · exact commutator_le_of_pCore_ne_bot hIH T h₁ h₂ hS₁ hS₂ hcomm hO hcore hZ

theorem corollaryA2
    (T₁ T₂ : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T₁) (hS₂ : fusionStronglyClosed (S₂ : Set G) T₂)
    (hcomm : ⁅S₁, S₂⁆ = ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G := by
  have hc : S₁ ≤ centralizer (S₂ : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hp : IsPGroup 2 (S₁ ⊔ S₂ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (T₁.isPGroup'.to_le h₁) (T₂.isPGroup'.to_le h₂)
      (hc.trans (centralizer_le_normalizer _))
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have h₁T : S₁ ≤ T := le_sup_left.trans hT
  have h₂T : S₂ ≤ T := le_sup_right.trans hT
  exact a2For G T S₁ S₂ h₁T h₂T (stronglyClosed_of_le_sylow T₁ T hS₁ h₁T)
    (stronglyClosed_of_le_sylow T₂ T hS₂ h₂T) hcomm

end CFSG.Goldschmidt75
