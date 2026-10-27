module

public import CFSG.Goldschmidt75.Sec45b
public import CFSG.Goldschmidt75.Sec42d
public import CFSG.Goldschmidt75.Sec44

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.centralizer_le_normalizer_W
    (h : MinCE G T S₁ S₂) {W : Subgroup G}
    (hW : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S₁ → B₂ ≤ S₂ → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      W ∈ NSet (B₁ ⊔ B₂) ∧ ∀ X ∈ NSet (B₁ ⊔ B₂), X ≤ W)
    {s₁ : G} (hs₁ : s₁ ∈ S₁) (hs₁2 : orderOf s₁ = 2) :
    centralizer ({s₁} : Set G) ≤ normalizer (W : Set G) := by
  set L := centralizer ({s₁} : Set G) with hL
  set M := normalizer (W : Set G) with hM
  set K₂ := kSub S₂ S₁ with hK₂
  set O := oddCent s₁ with hO
  have hC₁ : S₂ ≤ centralizer (S₁ : Set G) := le_centralizer_iff.mp h.comm
  have hS₂L : S₂ ≤ L := hC₁.trans (centralizer_le (Set.singleton_subset_iff.mpr hs₁))
  have hzs : zpowers s₁ ≤ S₁ := zpowers_le.mpr hs₁
  have hLz : L = normalizer ((zpowers s₁ : Subgroup G) : Set G) :=
    (normalizer_zpowers_eq hs₁2).symm
  have hNL : ∀ {B : Subgroup G}, B ≤ S₂ → B ≠ ⊥ → ∀ g ∈ L, g ∈ normalizer (B : Set G) →
      g ∈ M := fun hB hB1 g hg hgB =>
    mem_normalizer_of_unique hW hzs hB (zpowers_ne_bot hs₁2) hB1 (hLz ▸ hg) hgB
  have hK₂M : K₂ ≤ M := by
    refine h.symm.kSub_le_of_centralizers fun s hs hs1 hs2 g hg => ?_
    have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
    refine mem_normalizer_of_unique hW le_rfl (zpowers_le.mpr hs) h.ne_bot
      (zpowers_ne_bot hord) (kSub_le_normalizer hg.1) ?_
    rw [normalizer_zpowers_eq hord]
    exact hg.2
  have hOM : O ≤ M := by
    obtain ⟨V, hVS, hV⟩ := h.symm.exists_isKleinFour
    have hVel : IsElemAbelian 2 V :=
      ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (commute_of_isKleinFour hV a.2 b.2),
        fun x hx => by rw [pow_two]; exact mul_self_of_isKleinFour hV hx⟩
    have hVcard : 2 ^ (1 + 1) ≤ Nat.card V := by
      rw [@IsKleinFour.card_four V _ hV]
      norm_num
    have hVN : V ≤ normalizer (O : Set G) :=
      (hVS.trans hS₂L).trans (centralizer_le_normalizer_oddCent s₁)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
      Nat.prime_two V O hVel hVcard hVN
      (Nat.coprime_two_left.mpr (Balance.odd_card_oddCoreOf _))
    rw [← hgen]
    refine iSup₂_le fun S hS g hg => ?_
    obtain ⟨hSV, hScard⟩ := hS
    have hS1 : S ≠ ⊥ := fun h0 => by
      rw [h0, Subgroup.card_bot] at hScard
      norm_num at hScard
    exact hNL (hSV.trans hVS) hS1 g (oddCent_le_centralizer s₁ hg.1)
      (centralizer_le_normalizer _ hg.2)
  intro l hl
  have h43 := h.le_normalizer_kSub_sup hzs (zpowers_ne_bot hs₁2)
  rw [← hLz] at h43
  set X := K₂ ⊔ oddCoreOf L with hX
  have hXM : X ≤ M := sup_le hK₂M hOM
  have hS₂X : S₂ ≤ X := (le_kSub (hC₁.trans (centralizer_le_normalizer _))).trans le_sup_left
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosureIn T h.le₂ h.sc₂ hS₂L hl
  have hmX : m ∈ X := by
    refine normalClosureIn_le_of_conj (fun c hc a ha => ?_) hm
    exact (mem_normalizer_iff.mp (h43 hc) a).mp (hS₂X ha)
  have hmL : m ∈ L := map_subtype_le _ hm
  have hn : l * m⁻¹ ∈ normalizer (S₂ : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have key := congrArg (fun A : Subgroup G => m⁻¹ * x * m ∈ A) hmeq
    simp only [mem_conjSub] at key
    have e1 : l * (m⁻¹ * x * m) * l⁻¹ = l * m⁻¹ * x * (l * m⁻¹)⁻¹ := by group
    have e2 : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rw [e1, e2] at key
    exact (Iff.of_eq key).symm
  have hnM : l * m⁻¹ ∈ M := hNL le_rfl h.symm.ne_bot _ (mul_mem hl (inv_mem hmL)) hn
  have e : l = (l * m⁻¹) * m := by group
  rw [e]
  exact mul_mem hnM (hXM hmX)

theorem MinCE.false
    (h : MinCE G T S₁ S₂) : False := by
  have := h.isSimpleGroup
  have hO := h.oddCore_eq_bot
  obtain ⟨W, hWodd, hWmax, hWb⟩ := exists_W (T.isPGroup'.to_le h.le₁)
    (T.isPGroup'.to_le h.le₂) h.comm h.disj h.coreSep h.exists_isKleinFour
    h.symm.exists_isKleinFour
  have htop := h.iSup_centralizer_eq_top
  by_cases hW1 : W = ⊥
  ·
    have hN : normalizer ((kSub S₂ S₁ : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun s => h.centralizer_le_normalizer_kSub s.2.1
        (orderOf_eq_prime s.2.2.2 s.2.2.1) fun t ht ht2 => ?_
      by_cases ht1 : t = 1
      · intro o _
        rw [ht1, mem_centralizer_singleton_iff, mul_one, one_mul]
      · have h1 := (hWb s.1 s.2.1 (orderOf_eq_prime s.2.2.2 s.2.2.1) t ht
          (orderOf_eq_prime ht2 ht1)).1
        rw [hW1, le_bot_iff] at h1
        rw [← centralizer_zpowers_eq]
        exact commutator_eq_bot_iff_le_centralizer.mp h1
    have hKn : (kSub S₂ S₁).Normal := normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (kSub S₂ S₁) with h0 | h0
    · apply h.symm.ne_bot
      rw [eq_bot_iff, ← h0]
      exact le_kSub ((le_centralizer_iff.mp h.comm).trans (centralizer_le_normalizer _))
    · apply h.ne_bot
      rw [eq_bot_iff, ← h.center_eq_bot]
      intro x hx
      rw [mem_center_iff]
      intro g
      have hg : g ∈ centralizer (S₁ : Set G) :=
        kSub_le_centralizer (le_centralizer_iff.mp h.comm) (h0 ▸ mem_top g)
      exact (mem_centralizer_iff.mp hg x hx).symm
  ·
    have hM : normalizer (W : Set G) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact iSup_le fun s => h.centralizer_le_normalizer_W hWmax s.2.1
        (orderOf_eq_prime s.2.2.2 s.2.2.1)
    have hWn : W.Normal := normalizer_eq_top_iff.mp hM
    apply hW1
    rw [eq_bot_iff, ← hO]
    exact le_oddCore hWn hWodd

end CFSG.Goldschmidt75
