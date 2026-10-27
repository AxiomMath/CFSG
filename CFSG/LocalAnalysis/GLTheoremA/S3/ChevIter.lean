module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.LBalanceBridge
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private theorem chevIter_mem_normalizer_inf_centralizer {K : Subgroup G} {g a : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hga : g * a = a * g) :
    g ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hK := Subgroup.mem_normalizer_iff.1 hg h
  have hc : Commute a g := hga.symm
  simp only [Subgroup.mem_inf, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr hK ?_
  have := chev_commute_conj_iff (h := h) hc
  exact ⟨fun hh => (this.2 hh.symm).symm, fun hh => (this.1 hh.symm).symm⟩

theorem chev_step (hp : p.Prime) (hB : LBalanceAt G p) (hD : KDChevDown p) (hU : KDChevUnique p)
    {X K A : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hK : GLAPComponent p X K)
    (hchev : IsChevSimple p (PSimple p K)) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {a : G} (ha : a ∈ A) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) :
    ∃ K₁ : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) K₁ ∧
      (∀ L : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L → L = K₁) ∧
      IsChevSimple p (PSimple p K₁) ∧
      ∀ J' : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J' → J' ≤ K₁ := by
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hAK ha
  have hap : a ^ p = 1 := hA.2 a ha
  obtain ⟨hCh, hUn⟩ := chev_one_element hp hD hU hK hchev haK hap
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hle := fun {J' : Subgroup G}
      (hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J') =>
    glaPComponent_le_glaPLayer_centralizer_singleton hp hB hKX hA hAK ha hJ'
  have hex : ∃ L : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L := by
    by_contra hno
    push Not at hno
    have hbot : GLAPLayer p (K ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
      refine le_bot_iff.1 (sSup_le fun L hL => ?_)
      exact absurd hL (hno L)
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ hle hJ))
  obtain ⟨K₁, hK₁⟩ := hex
  have huniq : ∀ L : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L →
      L = K₁ := fun L hL => hUn L K₁ hL hK₁
  have hlayer : GLAPLayer p (K ⊓ Subgroup.centralizer ({a} : Set G)) = K₁ :=
    le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hK₁)
  exact ⟨K₁, hK₁, huniq, hCh K₁ hK₁, fun J' hJ' => hlayer ▸ hle hJ'⟩

theorem chev_iter_aux (hp : p.Prime) (hB : LBalanceAt G p) (hD : KDChevDown p)
    (hU : KDChevUnique p) :
    ∀ (m : ℕ) (X K A : Subgroup G), Nat.card ↥K = m → CFSG.Open.IsKGroup ↥X →
      GLAPComponent p X K → IsChevSimple p (PSimple p K) → IsElemAbelian p A →
      A ≤ Subgroup.normalizer (K : Set G) →
      ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J →
        IsChevSimple p (PSimple p J) ∧
        ∀ J' : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J' → J' = J := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X K A hm hX hK hchev hA hAK J hJ
  by_cases hcen : ∀ a ∈ A, K ≤ Subgroup.centralizer ({a} : Set G)
  ·
    have e : K ⊓ Subgroup.centralizer (A : Set G) = K := by
      refine inf_eq_left.2 fun k hk => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hcen c hc hk)).symm
    rw [e] at hJ
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
    have hKK : GLAPComponent p K K := glaPComponent_of_le hp hK le_rfl hK.1
    obtain ⟨-, hall, -⟩ := glaPLayer_of_isQuasisimple (Y := K) hq
    have hJK : J = K := (hall J hJ).trans (hall K hKK).symm
    subst hJK
    refine ⟨hchev, fun J' hJ' => ?_⟩
    rw [e] at hJ'
    exact (hall J' hJ').trans (hall J hKK).symm
  · push Not at hcen
    obtain ⟨a, ha, hnc⟩ := hcen
    obtain ⟨K₁, hK₁, huniq, hchev₁, hle⟩ := chev_step hp hB hD hU hX hK hchev hA hAK ha hJ
    have hAK₁ : A ≤ Subgroup.normalizer (K₁ : Set G) := by
      intro g hg
      have hgK := hAK hg
      have hga : g * a = a * g := congrArg Subtype.val (hA.1.1.comm ⟨g, hg⟩ ⟨a, ha⟩)
      have hnorm := chevIter_mem_normalizer_inf_centralizer hgK hga
      have hc := glaPComponent_gLBConj hK₁ g
      rw [mem_normalizer_iff_gLBConj_eq.1 hnorm] at hc
      exact mem_normalizer_iff_gLBConj_eq.2 (huniq _ hc)
    have hlt : Nat.card ↥K₁ < m := by
      rw [← hm]
      have h1 : K ⊓ Subgroup.centralizer ({a} : Set G) < K :=
        lt_of_le_of_ne inf_le_left fun h => hnc (inf_eq_left.1 h)
      exact lt_of_le_of_lt (Subgroup.card_le_of_le hK₁.1) (card_lt_of_lt' h1)
    have hX₁ : CFSG.Open.IsKGroup ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) :=
      CFSG.Open.IsKGroup.of_le (CFSG.Open.IsKGroup.of_le hX hK.1) inf_le_left
    have hsub : ∀ {J'' : Subgroup G},
        GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J'' →
        GLAPComponent p (K₁ ⊓ Subgroup.centralizer (A : Set G)) J'' := by
      intro J'' hJ''
      exact glaPComponent_of_le hp hJ'' (le_inf (hle J'' hJ'') (hJ''.1.trans inf_le_right))
        (inf_le_inf_right _ (hK₁.1.trans inf_le_left))
    obtain ⟨hc₁, huniq₁⟩ := ih (Nat.card ↥K₁) hlt (K ⊓ Subgroup.centralizer ({a} : Set G)) K₁ A
      rfl hX₁ hK₁ hchev₁ hA hAK₁ J (hsub hJ)
    exact ⟨hc₁, fun J' hJ' => huniq₁ J' (hsub hJ')⟩

theorem chevClosureAt_of (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {p : ℕ} (hD : KDChevDown p) (hU : KDChevUnique p) : ChevClosureAt G p := by
  intro hp _hp2 X K A hX hK hchev hA hAK J hJ
  exact (chev_iter_aux hp (lBalanceAt_of_catalogueSchreier hS hp) hD hU _ X K A rfl hX hK hchev hA
    hAK J hJ).1

theorem chevUniqueAt_of (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {p : ℕ} (hD : KDChevDown p) (hU : KDChevUnique p) : ChevUniqueAt G p := by
  intro hp _hp2 X K A hX hK hchev hA hAK J J' hJ hJ'
  exact ((chev_iter_aux hp (lBalanceAt_of_catalogueSchreier hS hp) hD hU _ X K A rfl hX hK hchev
    hA hAK J hJ).2 J' hJ').symm

theorem chevInnerAt_of (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {p : ℕ} (hI : KDChevInner p) : ChevInnerAt G p := by
  intro hp _hp2 X K A hX hK hchev hA hAK ⟨J, hJ⟩ a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨hnc, hin⟩ := hcon
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hAK ha
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hle := glaPComponent_le_glaPLayer_centralizer_singleton hp
    (lBalanceAt_of_catalogueSchreier hS hp) hKX hA hAK ha hJ
  have hbot : GLAPLayer p (K ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    refine le_bot_iff.1 (sSup_le fun L hL => ?_)
    exact absurd hL (chev_one_element_inner hp hI hK hchev haK (hA.2 a ha) hnc hin L)
  exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ hle))

end CFSG.LocalAnalysis.GLTheoremA
