module

public import CFSG.GroupTheory.SylowIntersectionControl.Selection
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.GroupTheory.PSubgroupSelection

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] {p : ℕ} (f : PSubgroupSelection p G)

private abbrev unionLocals (f : PSubgroupSelection p G) : Set (Subgroup G) :=
  f.family ⊤ ∪ f.singularMaxLocals

private lemma exists_sylow_inf_eq [Finite G] [Fact p.Prime] {W M : Subgroup G}
    (hW : IsSylowOf p W M) : ∃ R : Subgroup G, IsSylowOf p R ⊤ ∧ R ⊓ M = W := by
  obtain ⟨R, hWR, hR⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge
      (H := ⊤) hW.isPGroup (hW.le.trans le_top)
  exact ⟨R, hR, IsSylowOf.eq_of_le hW (le_inf hWR hW.le) inf_le_right hR.isPGroup.to_inf_left⟩

private lemma exists_maximal_isPLocal_ge [Finite G] {M : Subgroup G} (hM : IsPLocal p M) :
    ∃ N : Subgroup G, M ≤ N ∧ Maximal (IsPLocal p) N := by
  classical
  obtain ⟨N, hMN, hN⟩ := (Set.toFinite {K : Subgroup G | IsPLocal p K}).exists_le_maximal hM
  exact ⟨N, hMN, hN⟩

private lemma lt_inf_normalizer_of_not_le [Finite G] [Fact p.Prime] {R M W : Subgroup G}
    (hR : IsSylowOf p R ⊤) (hW : R ⊓ M = W) (hnot : ¬ R ≤ M) :
    W < R ⊓ normalizer (W : Set G) := by
  have hlt : R ⊓ M < R := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact hnot (h ▸ (inf_le_right : R ⊓ M ≤ M))
  have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hR.isPGroup hlt
  rwa [hW] at h

private lemma conn_of_link_le [Finite G] [Fact p.Prime] (f : PSubgroupSelection p G)
    {H M W₁ W₂ R₁ R₂ F : Subgroup G}
    (hR₁ : IsSylowOf p R₁ ⊤) (hR₂ : IsSylowOf p R₂ ⊤)
    (hW₁ : IsSylowOf p W₁ M) (hW₂ : IsSylowOf p W₂ M)
    (hR₁M : R₁ ⊓ M = W₁) (hR₂M : R₂ ⊓ M = W₂)
    (hHR : H ≤ R₁ ⊓ R₂)
    (hFW₁ : F ∈ f.sets W₁) (hFW₂ : F ∈ f.sets W₂)
    (hR₁le : R₁ ≤ M) :
    Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) R₁ R₂ := by
  have hR₁eq : R₁ = W₁ := by rw [← hR₁M, inf_eq_left.mpr hR₁le]
  have hcW : Nat.card W₂ = Nat.card W₁ := by rw [hW₂.card_eq, hW₁.card_eq]
  have hcR : Nat.card R₁ = Nat.card R₂ := by rw [hR₁.card_eq, hR₂.card_eq]
  have hR₂eq : R₂ = W₂ := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact hR₂M ▸ (inf_le_left : R₂ ⊓ M ≤ R₂)
    · rw [← hcR, hcW, hR₁eq]
  have hR₁NF : R₁ ≤ normalizer (F : Set G) := by
    rw [hR₁eq]
    exact Subgroup.le_normalizer.trans (f.normalizer_le W₁ hW₁.isPGroup F hFW₁)
  have hR₂NF : R₂ ≤ normalizer (F : Set G) := by
    rw [hR₂eq]
    exact Subgroup.le_normalizer.trans (f.normalizer_le W₂ hW₂.isPGroup F hFW₂)
  have hXfam : normalizer (F : Set G) ∈ f.family ⊤ := by
    refine ⟨R₁, hR₁, F, ?_, ?_⟩
    · rw [hR₁eq]; exact hFW₁
    · rw [top_inf_eq]
  exact Relation.ReflTransGen.single
    (sylowConjLink_of_le (𝓕 := unionLocals f) (K := ⊤) (X := normalizer (F : Set G))
      hR₁ hR₂ (Or.inl hXfam) le_top hR₁NF hR₂NF hHR)

private lemma conn_of_link_not_le [Finite G] [Fact p.Prime] (f : PSubgroupSelection p G)
    {H M W₁ W₂ R₁ R₂ F S' T' : Subgroup G} {k : ℕ}
    (ih : ∀ k' < k, ∀ (S'' T'' N : Subgroup G), Maximal (IsPLocal p) N →
      IsSylowOf p S'' ⊤ → IsSylowOf p T'' ⊤ → H ≤ S'' ⊓ T'' →
      H < S'' ⊓ N → H < T'' ⊓ N →
      Nat.card G * Nat.card G - Nat.card (S'' ⊓ N : Subgroup G) *
        Nat.card (T'' ⊓ N : Subgroup G) ≤ k' →
      Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) S'' T'')
    (hW₁ : IsSylowOf p W₁ M) (hW₂ : IsSylowOf p W₂ M)
    (hR₁ : IsSylowOf p R₁ ⊤) (hR₂ : IsSylowOf p R₂ ⊤)
    (hR₁M : R₁ ⊓ M = W₁) (hR₂M : R₂ ⊓ M = W₂)
    (hHW : H ≤ W₁ ⊓ W₂) (hHR : H ≤ R₁ ⊓ R₂)
    (hFW₁ : F ∈ f.sets W₁) (hFW₂ : F ∈ f.sets W₂)
    (hNF : IsPLocal p (normalizer (F : Set G)))
    (hS'M_le : Nat.card (S' ⊓ M : Subgroup G) ≤ Nat.card W₁)
    (hT'M_le : Nat.card (T' ⊓ M : Subgroup G) ≤ Nat.card W₂)
    (hk : Nat.card G * Nat.card G - Nat.card (S' ⊓ M : Subgroup G) *
      Nat.card (T' ⊓ M : Subgroup G) ≤ k)
    (hR₁le : ¬ R₁ ≤ M) :
    Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) R₁ R₂ := by
  have hR₂le : ¬ R₂ ≤ M := by
    intro hR₂Mle
    have hR₂eq : R₂ = W₂ := by rw [← hR₂M, inf_eq_left.mpr hR₂Mle]
    have hR₂card : Nat.card W₂ = Nat.card R₂ := by rw [hR₂eq]
    have hcW : Nat.card W₁ = Nat.card W₂ := by rw [hW₁.card_eq, hW₂.card_eq]
    have hcR : Nat.card R₁ = Nat.card R₂ := by rw [hR₁.card_eq, hR₂.card_eq]
    have hW₁R₁ : W₁ = R₁ := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · exact hR₁M ▸ (inf_le_left : R₁ ⊓ M ≤ R₁)
      · rw [hcR, ← hR₂card, ← hcW]
    exact hR₁le (hW₁R₁ ▸ (hR₁M ▸ (inf_le_right : R₁ ⊓ M ≤ M)))
  have hlt₁ : H < R₁ ⊓ normalizer (F : Set G) := by
    have h1 : W₁ < R₁ ⊓ normalizer (W₁ : Set G) :=
      lt_inf_normalizer_of_not_le hR₁ hR₁M hR₁le
    have h2 : R₁ ⊓ normalizer (W₁ : Set G) ≤ R₁ ⊓ normalizer (F : Set G) :=
      inf_le_inf_left _ (f.normalizer_le W₁ hW₁.isPGroup F hFW₁)
    exact lt_of_le_of_lt (hHW.trans inf_le_left) (lt_of_lt_of_le h1 h2)
  have hlt₂ : H < R₂ ⊓ normalizer (F : Set G) := by
    have h1 : W₂ < R₂ ⊓ normalizer (W₂ : Set G) :=
      lt_inf_normalizer_of_not_le hR₂ hR₂M hR₂le
    have h2 : R₂ ⊓ normalizer (W₂ : Set G) ≤ R₂ ⊓ normalizer (F : Set G) :=
      inf_le_inf_left _ (f.normalizer_le W₂ hW₂.isPGroup F hFW₂)
    exact lt_of_le_of_lt (hHW.trans inf_le_right) (lt_of_lt_of_le h1 h2)
  obtain ⟨N, hNFN, hNmax⟩ := exists_maximal_isPLocal_ge hNF
  have hlt₁N : H < R₁ ⊓ N := hlt₁.trans_le (inf_le_inf_left _ hNFN)
  have hlt₂N : H < R₂ ⊓ N := hlt₂.trans_le (inf_le_inf_left _ hNFN)
  have hW₁_lt : Nat.card W₁ < Nat.card (R₁ ⊓ N : Subgroup G) := by
    refine Subgroup.card_lt_of_lt (lt_of_lt_of_le ?_ (inf_le_inf_left _ hNFN))
    exact lt_of_lt_of_le (lt_inf_normalizer_of_not_le hR₁ hR₁M hR₁le)
      (inf_le_inf_left _ (f.normalizer_le W₁ hW₁.isPGroup F hFW₁))
  have hW₂_lt : Nat.card W₂ < Nat.card (R₂ ⊓ N : Subgroup G) := by
    refine Subgroup.card_lt_of_lt (lt_of_lt_of_le ?_ (inf_le_inf_left _ hNFN))
    exact lt_of_lt_of_le (lt_inf_normalizer_of_not_le hR₂ hR₂M hR₂le)
      (inf_le_inf_left _ (f.normalizer_le W₂ hW₂.isPGroup F hFW₂))
  have hprod_lt : Nat.card (S' ⊓ M : Subgroup G) * Nat.card (T' ⊓ M : Subgroup G) <
      Nat.card (R₁ ⊓ N : Subgroup G) * Nat.card (R₂ ⊓ N : Subgroup G) :=
    Nat.mul_lt_mul'' (lt_of_le_of_lt hS'M_le hW₁_lt) (lt_of_le_of_lt hT'M_le hW₂_lt)
  have hprod_le : Nat.card (R₁ ⊓ N : Subgroup G) * Nat.card (R₂ ⊓ N : Subgroup G) ≤
      Nat.card G * Nat.card G :=
    Nat.mul_le_mul (Subgroup.card_le_card_group _) (Subgroup.card_le_card_group _)
  have hmeasure_lt : Nat.card G * Nat.card G - Nat.card (R₁ ⊓ N : Subgroup G) *
      Nat.card (R₂ ⊓ N : Subgroup G) < Nat.card G * Nat.card G -
      Nat.card (S' ⊓ M : Subgroup G) * Nat.card (T' ⊓ M : Subgroup G) := by
    omega
  exact ih _ (lt_of_lt_of_le hmeasure_lt hk) R₁ R₂ N hNmax hR₁ hR₂ hHR hlt₁N hlt₂N le_rfl

private lemma conn_of_link [Finite G] [Fact p.Prime] (f : PSubgroupSelection p G)
    {H M W₁ W₂ R₁ R₂ S' T' : Subgroup G} {k : ℕ}
    (hHne : H ≠ ⊥)
    (hf : ∀ P : Subgroup G, IsPGroup p P → P ≠ ⊥ → ∀ F ∈ f.sets P, F ≠ ⊥)
    (ih : ∀ k' < k, ∀ (S'' T'' N : Subgroup G), Maximal (IsPLocal p) N →
      IsSylowOf p S'' ⊤ → IsSylowOf p T'' ⊤ → H ≤ S'' ⊓ T'' →
      H < S'' ⊓ N → H < T'' ⊓ N →
      Nat.card G * Nat.card G - Nat.card (S'' ⊓ N : Subgroup G) *
        Nat.card (T'' ⊓ N : Subgroup G) ≤ k' →
      Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) S'' T'')
    (hR₁ : IsSylowOf p R₁ ⊤) (hR₂ : IsSylowOf p R₂ ⊤)
    (hR₁M : R₁ ⊓ M = W₁) (hR₂M : R₂ ⊓ M = W₂)
    (hS'M_le : Nat.card (S' ⊓ M : Subgroup G) ≤ Nat.card W₁)
    (hT'M_le : Nat.card (T' ⊓ M : Subgroup G) ≤ Nat.card W₂)
    (hk : Nat.card G * Nat.card G - Nat.card (S' ⊓ M : Subgroup G) *
      Nat.card (T' ⊓ M : Subgroup G) ≤ k)
    (hlink : SylowConjLink p (f.family M) M H W₁ W₂) :
    Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) R₁ R₂ := by
  obtain ⟨hW₁, hW₂, X, hX₁, hX₂, hHX, x, hxX, hW₂eq⟩ := hlink
  have hX₁' : X ∈ (fun F : Subgroup G => M ⊓ normalizer (F : Set G)) '' f.sets W₁ := by
    rwa [f.sylowMembers_family hW₁] at hX₁
  obtain ⟨F, hFW₁, hFX⟩ := hX₁'
  have hFX' : M ⊓ normalizer (F : Set G) = X := hFX
  have hxX' : x ∈ M ⊓ normalizer (F : Set G) := by rw [hFX']; exact hxX
  have hxNF : x ∈ normalizer (F : Set G) := hxX'.2
  have hFW₂ : F ∈ f.sets W₂ := by
    have hsets := f.sets_map_conj W₁ hW₁.isPGroup x
    rw [hW₂eq, hsets]
    exact ⟨F, hFW₁, (Subgroup.mem_normalizer_iff_map_conj_eq).mp hxNF⟩
  have hHW₁ : H ≤ W₁ := hHX.trans (inf_le_left.trans inf_le_left)
  have hHW₂ : H ≤ W₂ := hHX.trans (inf_le_left.trans inf_le_right)
  have hHW : H ≤ W₁ ⊓ W₂ := le_inf hHW₁ hHW₂
  have hHR : H ≤ R₁ ⊓ R₂ :=
    le_inf (hHW₁.trans (hR₁M ▸ inf_le_left)) (hHW₂.trans (hR₂M ▸ inf_le_left))
  have hW₁ne : W₁ ≠ ⊥ := fun h => hHne (le_bot_iff.mp (h ▸ hHW₁))
  have hFne : F ≠ ⊥ := hf W₁ hW₁.isPGroup hW₁ne F hFW₁
  have hFp : IsPGroup p F := hW₁.isPGroup.to_le (f.le_of_mem W₁ hW₁.isPGroup F hFW₁)
  have hNF : IsPLocal p (normalizer (F : Set G)) := ⟨F, hFne, hFp, rfl⟩
  by_cases hR₁le : R₁ ≤ M
  · exact conn_of_link_le f hR₁ hR₂ hW₁ hW₂ hR₁M hR₂M hHR hFW₁ hFW₂ hR₁le
  · exact conn_of_link_not_le f ih hW₁ hW₂ hR₁ hR₂ hR₁M hR₂M hHW hHR hFW₁ hFW₂ hNF
      hS'M_le hT'M_le hk hR₁le

private lemma conn_inner [Finite G] [Fact p.Prime] (f : PSubgroupSelection p G)
    {H : Subgroup G} (hHne : H ≠ ⊥)
    (hf : ∀ P : Subgroup G, IsPGroup p P → P ≠ ⊥ → ∀ F ∈ f.sets P, F ≠ ⊥)
    (G1 : ∀ A B : Subgroup G, IsSylowOf p A ⊤ → IsSylowOf p B ⊤ → H < A ⊓ B →
      Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) A B) :
    ∀ k, ∀ (S' T' M : Subgroup G), Maximal (IsPLocal p) M →
      IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' → H < S' ⊓ M → H < T' ⊓ M →
      Nat.card G * Nat.card G - Nat.card (S' ⊓ M : Subgroup G) *
        Nat.card (T' ⊓ M : Subgroup G) ≤ k →
      Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) S' T' := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ihk =>
    intro S' T' M hM hS' hT' hHle hltS hltT hk
    obtain ⟨U₀, hS'MU₀, hU₀⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge
        (R := S' ⊓ M) (H := M) hS'.isPGroup.to_inf_left inf_le_right
    obtain ⟨U, hU, hUM⟩ := exists_sylow_inf_eq hU₀
    obtain ⟨V₀, hT'MV₀, hV₀⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge
        (R := T' ⊓ M) (H := M) hT'.isPGroup.to_inf_left inf_le_right
    obtain ⟨m, hmM, hmconj⟩ := hU₀.exists_mem_conj hV₀
    have hHU₀ : H < U₀ := lt_of_lt_of_le hltS hS'MU₀
    have hHV₀ : H < V₀ := lt_of_lt_of_le hltT hT'MV₀
    have hHU : H ≤ U := hHU₀.le.trans (hUM ▸ (inf_le_left : U ⊓ M ≤ U))
    have hHM : H ≤ M := hHU₀.le.trans (hUM ▸ (inf_le_right : U ⊓ M ≤ M))
    have hltS'U : H < S' ⊓ U :=
      lt_of_lt_of_le hltS (le_inf inf_le_left (hS'MU₀.trans (hUM ▸ inf_le_left)))
    have hS'U : Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) S' U :=
      G1 S' U hS' hU hltS'U
    have hV₀eq : V₀ = U₀.map (MulAut.conj m).toMonoidHom := by
      ext y
      rw [hmconj y]
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · intro hy
        exact ⟨m⁻¹ * y * m, hy, by group⟩
      · rintro ⟨z, hz, rfl⟩
        have h : m⁻¹ * (m * z * m⁻¹) * m = z := by group
        rwa [h]
    have hMmap : M.map (MulAut.conj m).toMonoidHom = M :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hmM)
    let V : Subgroup G := U.map (MulAut.conj m).toMonoidHom
    have hVM : V ⊓ M = V₀ := by
      change U.map (MulAut.conj m).toMonoidHom ⊓ M = V₀
      calc U.map (MulAut.conj m).toMonoidHom ⊓ M
          = U.map (MulAut.conj m).toMonoidHom ⊓ M.map (MulAut.conj m).toMonoidHom := by
            rw [hMmap]
        _ = (U ⊓ M).map (MulAut.conj m).toMonoidHom :=
            (Subgroup.map_inf U M _ (MulAut.conj m).injective).symm
        _ = V₀ := by rw [hUM, hV₀eq]
    have hV : IsSylowOf p V ⊤ := by
      have h := isSylowOf_map_conj hU m
      rw [Subgroup.map_top_of_surjective _ (MulAut.conj m).surjective] at h
      exact h
    have hHV : H ≤ V := hHV₀.le.trans (hVM ▸ (inf_le_left : V ⊓ M ≤ V))
    have hltVT : H < V ⊓ T' :=
      lt_of_lt_of_le hltT (le_inf (hT'MV₀.trans (hVM ▸ inf_le_left)) inf_le_left)
    have hVT : Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) V T' :=
      G1 V T' hV hT' hltVT
    have hUV : Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) U V := by
      by_cases hMsing : M ∈ f.singularMaxLocals
      · refine Relation.ReflTransGen.single ?_
        refine ⟨hU, hV, M, ⟨Or.inr hMsing, ?_⟩, ⟨Or.inr hMsing, ?_⟩,
          le_inf (le_inf hHU hHV) hHM, m, hmM, rfl⟩
        · rw [hUM]; exact hU₀
        · rw [hVM]; exact hV₀
      · have hreg : f.IsRegular M := by
          by_contra h
          exact hMsing ⟨hM, h⟩
        have hHU₀V₀ : H ≤ U₀ ⊓ V₀ := le_inf hHU₀.le hHV₀.le
        have hU₀V₀bot : U₀ ⊓ V₀ ≠ ⊥ := fun h => hHne (le_bot_iff.mp (hHU₀V₀.trans (le_of_eq h)))
        by_cases hU₀V₀ : U₀ = V₀
        · refine G1 U V hU hV (lt_of_lt_of_le hHU₀ (le_inf (hUM ▸ inf_le_left) ?_))
          rw [hU₀V₀]
          exact hVM ▸ inf_le_left
        · have chain : ConjVia p (f.family M) M U₀ V₀ :=
            hreg U₀ V₀ hU₀ hV₀ hU₀V₀ hU₀V₀bot
          have chainH : Relation.ReflTransGen (SylowConjLink p (f.family M) M H) U₀ V₀ :=
            ConjVia.reflTransGen_of_le chain hHU₀V₀
          have lift : ∀ W, Relation.ReflTransGen (SylowConjLink p (f.family M) M H) U₀ W →
              ∀ R, IsSylowOf p R ⊤ → R ⊓ M = W →
              Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ H) U R := by
            intro W hW
            induction hW with
            | refl =>
                intro R hR hRM
                refine G1 U R hU hR (lt_of_lt_of_le hHU₀ ?_)
                exact le_inf (hUM ▸ inf_le_left) (hRM ▸ inf_le_left)
            | tail _ hcd ih =>
                intro R₂ hR₂ hR₂M
                obtain ⟨R₁, hR₁, hR₁M⟩ := exists_sylow_inf_eq hcd.1
                have hb_le : Nat.card (S' ⊓ M : Subgroup G) ≤ Nat.card (R₁ ⊓ M : Subgroup G) := by
                  rw [hR₁M]
                  exact CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_card_le hcd.1
                    hS'.isPGroup.to_inf_left inf_le_right
                have hc_le : Nat.card (T' ⊓ M : Subgroup G) ≤ Nat.card (R₂ ⊓ M : Subgroup G) := by
                  rw [hR₂M]
                  exact CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_card_le hcd.2.1
                    hT'.isPGroup.to_inf_left inf_le_right
                exact (ih R₁ hR₁ hR₁M).trans
                  (conn_of_link f hHne hf ihk hR₁ hR₂ hR₁M hR₂M
                    (hR₁M ▸ hb_le) (hR₂M ▸ hc_le) hk hcd)
          exact lift V₀ chainH V hV hVM
    exact hS'U.trans (hUV.trans hVT)

private lemma conn_of_ne_bot [Finite G] [Fact p.Prime] (f : PSubgroupSelection p G)
    (hf : ∀ P : Subgroup G, IsPGroup p P → P ≠ ⊥ → ∀ F ∈ f.sets P, F ≠ ⊥)
    (S T : Subgroup G) (hS : IsSylowOf p S ⊤) (hT : IsSylowOf p T ⊤)
    (hne : S ⊓ T ≠ ⊥) :
    Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ (S ⊓ T)) S T := by
  have key : ∀ n, ∀ S T : Subgroup G, IsSylowOf p S ⊤ → IsSylowOf p T ⊤ →
      Nat.card G - Nat.card (S ⊓ T : Subgroup G) = n → S ⊓ T ≠ ⊥ →
      Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ (S ⊓ T)) S T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S T hS hT hmeas hne
      have Hne : S ⊓ T ≠ ⊥ := hne
      have G1 : ∀ A B : Subgroup G, IsSylowOf p A ⊤ → IsSylowOf p B ⊤ → S ⊓ T < A ⊓ B →
          Relation.ReflTransGen (SylowConjLink p (unionLocals f) ⊤ (S ⊓ T)) A B := by
        intro A B hA hB hlt
        have hABne : A ⊓ B ≠ ⊥ :=
          fun h => Hne (le_bot_iff.mp (hlt.le.trans (le_of_eq h)))
        have hltcard : Nat.card (S ⊓ T : Subgroup G) < Nat.card (A ⊓ B : Subgroup G) :=
          Subgroup.card_lt_of_lt hlt
        have hmeas' : Nat.card G - Nat.card (A ⊓ B : Subgroup G) < n := by
          rw [← hmeas]
          have hleG : Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card G :=
            Subgroup.card_le_card_group _
          omega
        exact ConjVia.reflTransGen_of_le (ih _ hmeas' A B hA hB rfl hABne) hlt.le
      by_cases hST : S = T
      · subst hST
        exact Relation.ReflTransGen.refl
      · have hHltS : S ⊓ T < S := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro h
          have hSTle : S ≤ T := h ▸ (inf_le_right : S ⊓ T ≤ T)
          exact hST (IsSylowOf.eq_of_le hS hSTle hT.le hT.isPGroup).symm
        have hHltT : S ⊓ T < T := by
          refine lt_of_le_of_ne inf_le_right ?_
          intro h
          have hTSle : T ≤ S := h ▸ (inf_le_left : S ⊓ T ≤ S)
          exact hST (IsSylowOf.eq_of_le hT hTSle hS.le hS.isPGroup)
        have hNloc : IsPLocal p (normalizer (S ⊓ T : Set G)) :=
          ⟨S ⊓ T, Hne, hS.isPGroup.to_inf_left, rfl⟩
        obtain ⟨M, hNM, hMmax⟩ := exists_maximal_isPLocal_ge hNloc
        have hHS : S ⊓ T < S ⊓ normalizer (S ⊓ T : Set G) :=
          CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hS.isPGroup hHltS
        have hHT : S ⊓ T < T ⊓ normalizer (S ⊓ T : Set G) :=
          CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hT.isPGroup hHltT
        have hltS : S ⊓ T < S ⊓ M := hHS.trans_le (inf_le_inf_left _ hNM)
        have hltT : S ⊓ T < T ⊓ M := hHT.trans_le (inf_le_inf_left _ hNM)
        exact conn_inner f Hne hf G1 (Nat.card G * Nat.card G) S T M hMmax hS hT
          (le_inf inf_le_left inf_le_right) hltS hltT (Nat.sub_le _ _)
  exact key (Nat.card G - Nat.card (S ⊓ T : Subgroup G)) S T hS hT rfl hne

theorem controlsSylowIntersections_family_union [Finite G] [Fact p.Prime]
    (hf : ∀ P : Subgroup G, IsPGroup p P → P ≠ ⊥ → ∀ F ∈ f.sets P, F ≠ ⊥) :
    ControlsSylowIntersections p (f.family ⊤ ∪ f.singularMaxLocals) ⊤ := by
  intro S T hS hT hST hHne
  exact conn_of_ne_bot f hf S T hS hT hHne

end CFSG.GroupTheory.PSubgroupSelection
