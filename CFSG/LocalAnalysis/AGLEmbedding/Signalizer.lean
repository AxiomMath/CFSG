module

public import CFSG.Open.GLBDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalElementary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem primeComplementCoreOf_subgroupOf (p : ℕ) (H : Subgroup G) :
    (primeComplementCoreOf p H).subgroupOf H = primeComplementCore p :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem glbPrimeCore_eq_primeComplementCoreOf [Finite G] (p : ℕ) (H : Subgroup G) :
    GLBPrimeCore p H = primeComplementCoreOf p H := by
  apply le_antisymm
  · apply sSup_le
    rintro N ⟨hNH, hnormal, hcop⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
    refine Subgroup.map_mono (normal_coprime_le_primeComplementCore p _ hnormal ?_)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  · refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [primeComplementCoreOf_subgroupOf]
      infer_instance
    · rw [primeComplementCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
      exact primeComplementCore_coprime p

theorem glbPrimeCore_le (p : ℕ) (H : Subgroup G) : GLBPrimeCore p H ≤ H :=
  sSup_le fun _ hN => hN.1

theorem le_glbPrimeCore {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hcop : p.Coprime (Nat.card N)) :
    N ≤ GLBPrimeCore p H :=
  le_sSup ⟨hNH, (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN, hcop⟩

theorem glbPrimeCore_subgroupOf [Finite G] (p : ℕ) (H : Subgroup G) :
    (GLBPrimeCore p H).subgroupOf H = primeComplementCore p := by
  rw [glbPrimeCore_eq_primeComplementCoreOf, primeComplementCoreOf_subgroupOf]

theorem glbPrimeCore_normal [Finite G] (p : ℕ) (H : Subgroup G) :
    ((GLBPrimeCore p H).subgroupOf H).Normal := by
  rw [glbPrimeCore_subgroupOf]
  infer_instance

theorem le_normalizer_glbPrimeCore [Finite G] (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (GLBPrimeCore p H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (glbPrimeCore_le p H)).mp
    (glbPrimeCore_normal p H)

theorem glbPrimeCore_coprime [Finite G] (p : ℕ) (H : Subgroup G) :
    p.Coprime (Nat.card (GLBPrimeCore p H)) := by
  rw [glbPrimeCore_eq_primeComplementCoreOf, primeComplementCoreOf,
    Subgroup.card_map_of_injective H.subtype_injective]
  exact primeComplementCore_coprime p

theorem pCoreOf_le_glbPrimeCore [Finite G] {p q : ℕ} (hq : q.Prime) (hpq : p.Coprime q)
    (H : Subgroup G) : pCoreOf q H ≤ GLBPrimeCore p H := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup q H)
  exact le_glbPrimeCore (pCoreOf_le q H) (localGroup_le_normalizer_pCoreOf q H)
    (hk ▸ hpq.pow_right k)

theorem glbPrimeCore_inf_eq_of_signalizer [Finite G] {p : ℕ} {H M R : Subgroup G}
    (hR : R ≤ H ⊓ M) (hcore : GLBPrimeCore p H ≤ M)
    (hunique : ∀ Y : Subgroup G, Y ≤ H → p.Coprime (Nat.card Y) →
      R ≤ Subgroup.normalizer (Y : Set G) → Y ≤ GLBPrimeCore p H) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H :=
  le_antisymm
    (hunique _ ((glbPrimeCore_le p _).trans inf_le_left) (glbPrimeCore_coprime p _)
      (hR.trans (le_normalizer_glbPrimeCore p _)))
    (le_glbPrimeCore (le_inf (glbPrimeCore_le p H) hcore)
      (inf_le_left.trans (le_normalizer_glbPrimeCore p H)) (glbPrimeCore_coprime p H))

theorem pCoreOf_inf_eq_of_signalizer [Finite G] {p q : ℕ} (hq : q.Prime) (hpq : p.Coprime q)
    {H M R : Subgroup G} (hR : R ≤ H ⊓ M) (hcore : GLBPrimeCore p H ≤ M)
    (hunique : ∀ Y : Subgroup G, Y ≤ H → p.Coprime (Nat.card Y) →
      R ≤ Subgroup.normalizer (Y : Set G) → Y ≤ GLBPrimeCore p H) :
    pCoreOf q (H ⊓ M) = pCoreOf q H := by
  have hO : GLBPrimeCore p H ≤ H ⊓ M := le_inf (glbPrimeCore_le p H) hcore
  apply le_antisymm
  ·
    have hle : pCoreOf q (H ⊓ M) ≤ GLBPrimeCore p H :=
      (pCoreOf_le_glbPrimeCore hq hpq (H ⊓ M)).trans
        (glbPrimeCore_inf_eq_of_signalizer hR hcore hunique).le
    have hcoreO : pCoreOf q (H ⊓ M) ≤ pCoreOf q (GLBPrimeCore p H) :=
      normal_pGroup_le_pCoreOf q _ _ hle
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
          (hO.trans (localGroup_le_normalizer_pCoreOf q (H ⊓ M))))
        (pCoreOf_isPGroup q (H ⊓ M))
    exact hcoreO.trans (pCoreOf_le_of_normal_subgroupOf q _ H (glbPrimeCore_le p H)
      (glbPrimeCore_normal p H))
  · have hle : pCoreOf q H ≤ H ⊓ M := (pCoreOf_le_glbPrimeCore hq hpq H).trans hO
    exact normal_pGroup_le_pCoreOf q _ _ hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (inf_le_left.trans (localGroup_le_normalizer_pCoreOf q H)))
      (pCoreOf_isPGroup q H)

theorem primeCore_twoCore_eq_of_signalizer_unique [Finite G] {p : ℕ} (hp : Odd p)
    {H M R : Subgroup G} (hR : R ≤ H ⊓ M) (hcore : GLBPrimeCore p H ≤ M)
    (hunique : ∀ Y : Subgroup G, Y ≤ H → p.Coprime (Nat.card Y) →
      R ≤ Subgroup.normalizer (Y : Set G) → Y ≤ GLBPrimeCore p H) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H ∧ pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  ⟨glbPrimeCore_inf_eq_of_signalizer hR hcore hunique,
    pCoreOf_inf_eq_of_signalizer Nat.prime_two (Nat.coprime_two_right.mpr hp) hR hcore hunique⟩

theorem signalizer_le_glbPrimeCore_of_contains [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H A Y : Subgroup G} (hH : HasPrimeConstraint (G := H) p) (hA : IsPGroup p A) (hAH : A ≤ H)
    (hcontains : ∀ x ∈ H, x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hYH : Y ≤ H) (hY : p.Coprime (Nat.card Y)) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p H := by
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  exact ambient_prime_constraint_signalizer_le_core p hp hp2 H A Y hH hA hAH hY hYH hAY hcontains

theorem sylow_contains_centralizing_order_prime {p : ℕ} {H : Subgroup G} (R : Sylow p H) :
    ∀ x ∈ H, x ∈ Subgroup.centralizer (((R : Subgroup H).map H.subtype : Subgroup G) : Set G) →
      orderOf x = p → x ∈ (R : Subgroup H).map H.subtype := by
  intro x hxH hxC hx
  let y : H := ⟨x, hxH⟩
  have hyC : y ∈ Subgroup.centralizer ((R : Subgroup H) : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC r (Subgroup.mem_map_of_mem _ hr))
  have hy : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
  have hsup := R.is_maximal' (R.isPGroup'.to_sup_of_normal_left' hy
    ((Subgroup.zpowers_le.mpr hyC).trans (Subgroup.centralizer_le_normalizer _))) le_sup_left
  have hyR : y ∈ (R : Subgroup H) := hsup ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  exact ⟨y, hyR, rfl⟩

theorem signalizer_le_glbPrimeCore_of_hasPrimeConstraint [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H Y : Subgroup G} (hH : HasPrimeConstraint (G := H) p) (R : Sylow p H)
    (hYH : Y ≤ H) (hY : p.Coprime (Nat.card Y))
    (hRY : (R : Subgroup H).map H.subtype ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p H :=
  signalizer_le_glbPrimeCore_of_contains hp hp2 hH (R.isPGroup'.map H.subtype)
    (Subgroup.map_subtype_le _) (sylow_contains_centralizing_order_prime R) hYH hY hRY

theorem signalizer_le_glbPrimeCore_of_full_rank [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H A Y : Subgroup G} (hH : HasPrimeConstraint (G := H) p) (hAH : A ≤ H)
    (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ pRank p H)
    (hYH : Y ≤ H) (hY : p.Coprime (Nat.card Y)) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p H :=
  signalizer_le_glbPrimeCore_of_contains hp hp2 hH (elementary_isPGroup p A hA) hAH
    (elementary_full_rank_contains_order_prime_centralizer_elements p hp H A hAH hA hcard)
    hYH hY hAY

theorem primeCore_twoCore_eq_of_hasPrimeConstraint [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H M : Subgroup G} (hH : HasPrimeConstraint (G := H) p) (R : Sylow p H)
    (hRM : (R : Subgroup H).map H.subtype ≤ M) (hcore : GLBPrimeCore p H ≤ M) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H ∧ pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  primeCore_twoCore_eq_of_signalizer_unique (hp.odd_of_ne_two hp2)
    (le_inf (Subgroup.map_subtype_le _) hRM) hcore
    fun _ hYH hY hRY => signalizer_le_glbPrimeCore_of_hasPrimeConstraint hp hp2 hH R hYH hY hRY

end CFSG.AGLEmbedding
