module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_barM {M X : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈ Subgroup.normalizer (barM M X : Set _) :=
  Subgroup.le_normalizer_map _
    (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap M.subtype hgX))

theorem eq_bot_or_eq_barM_of_mem_normalizer {M X : Subgroup G} (hXM : X ≤ M) {g : G}
    (hgM : g ∈ M) (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ X → g ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X)
    {Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hY₀ : Y₀ ≤ barM M X)
    (hgY₀ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈ Subgroup.normalizer (Y₀ : Set _)) :
    Y₀ = ⊥ ∨ Y₀ = barM M X := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Y₁ : Subgroup G := X ⊓ (Y₀.comap mk).map M.subtype with hY₁
  have hgY₁ : g ∈ Subgroup.normalizer (Y₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgX, Subgroup.le_normalizer_map M.subtype
      (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap mk hgY₀))⟩
  have hmem : ∀ (x : G) (hx : x ∈ X), x ∈ Y₁ ↔ mk ⟨x, hXM hx⟩ ∈ Y₀ := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ⟨hx, ⟨x, hXM hx⟩, h, rfl⟩⟩
    obtain ⟨m, hm, hmx⟩ := h.2
    have : m = ⟨x, hXM hx⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  rcases hirr Y₁ inf_le_left hgY₁ with h1 | h1
  · refine Or.inl (eq_bot_iff.mpr fun y hy => ?_)
    obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hY₀ hy
    have hxY := (hmem x (Subgroup.mem_subgroupOf.mp hx)).mpr hy
    rw [h1, Subgroup.mem_bot] at hxY
    subst hxY
    exact Subgroup.mem_bot.mpr (map_one mk)
  · refine Or.inr (le_antisymm hY₀ ?_)
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
    exact (hmem x hxX).mp (h1 ▸ hxX)

end Normalizer

section Image

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_mulEquiv_galoisField {p n : ℕ} [Fact p.Prime] {X : Subgroup G}
    (φ : Multiplicative (GaloisField p n) ≃* X) : IsElemAbelian p X := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have : (⟨x, hx⟩ : X) ^ p = 1 := by rw [← ha, ← map_pow, hap, map_one]
    simpa using congrArg Subtype.val this

omit [Finite G] in
theorem isElemAbelian_barM_of_isElemAbelian {M X : Subgroup G} {p : ℕ} (hX : IsElemAbelian p X) :
    IsElemAbelian p (barM M X) := by
  have : IsMulCommutative X := hX.1
  refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x hx => Subtype.ext ?_⟩ _
  simpa using hX.2 x (Subgroup.mem_subgroupOf.mp hx)

theorem D1L2Data.isElemAbelian_barM {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) : IsElemAbelian p (barM M X) := by
  obtain ⟨φ, -⟩ := h.torus
  exact isElemAbelian_barM_of_isElemAbelian (isElemAbelian_of_mulEquiv_galoisField φ)

omit [Finite G] in
theorem eq_one_of_mem_pCoreOf_two {M X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) {x : G} (hx : x ∈ X) (hxQ : x ∈ pCoreOf 2 M) : x = 1 := by
  obtain ⟨k, hk⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := hX ⟨x, hx⟩
  have hj' : x ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (p ^ j) (2 ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hk'))

theorem card_barM_of_isPGroup {M X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : X ≤ M) (hX : IsPGroup p X) : Nat.card (barM M X) = Nat.card X := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  let f : X → barM M X := fun x =>
    ⟨mk ⟨x, hXM x.2⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : mk ((⟨x, hXM x.2⟩ : M)⁻¹ * ⟨y, hXM y.2⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val hxy
    have h2 := eq_one_of_mem_pCoreOf_two hp hp2 hX (X.mul_mem (X.inv_mem x.2) y.2)
      (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  refine le_antisymm ?_ (Nat.card_le_card_of_injective f hf)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

theorem card_barM_eq_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M X : Subgroup G}
    (hX : IsElemAbelian p X) (hXM : X ≤ M) : Nat.card (barM M X) = Nat.card X :=
  card_barM_of_isPGroup hp hp2 hXM fun x => ⟨1, Subtype.ext (by simpa using hX.2 x x.2)⟩

theorem D1L2Data.card_barM {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) : Nat.card (barM M X) = p ^ n := by
  obtain ⟨φ, -⟩ := h.torus
  rw [card_barM_eq_of_isElemAbelian Fact.out h.ph3.ne_two (isElemAbelian_of_mulEquiv_galoisField φ)
    (h.le_R.trans h.ph3.le_M), ← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
    GaloisField.card p n (by have := h.three_le; omega)]

end Image

section Centralizer

variable {G : Type} [Group G] [Finite G]

theorem TwoLocalPhaseThree.le_barM_inf_of_le_centralizer {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _)) :
    T ≤ barM M (H ⊓ M) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Y : Subgroup G := (T.comap mk).map M.subtype with hY
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := h.twoCore_M_le h.twoCore_inf
  have hYS : Y ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    rintro _ ⟨s, hs, rfl⟩
    have hsM : s ∈ M := h.twoCore_le hs
    have hsbar : mk ⟨s, hsM⟩ ∈ barM M (pCoreOf 2 H) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hT hm) _ hsbar
    have hc : mk (⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hq := hQS (coe_mem_pCoreOf_two_of_mk_eq_one _ hc)
    have heq : (MulAut.conj (m : G)).toMonoidHom s =
        (((⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹ : M) : G))⁻¹ * s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    change (MulAut.conj (m : G)).toMonoidHom s ∈ pCoreOf 2 H
    rw [heq]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq) hs
  intro σ hσ
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) σ
  have hmK : (m : G) ∈ H ⊓ M :=
    h.inf_eq_inf_normalizer_twoCore ▸ ⟨m.2, hYS ⟨m, hσ, rfl⟩⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hmK)

theorem D1PhaseThree.le_barM_inf_of_le_centralizer {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _)) :
    T ≤ barM M (H ⊓ M) :=
  h.toTwoLocalPhaseThree.le_barM_inf_of_le_centralizer hT

end Centralizer

theorem stmtFiveOddCore_of (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : StmtFiveOddCore := by
  intro G _ _ p n _ P M H R X h _ s hs hs2 hsp
  by_contra hnot
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨r, t, hr, hnr, -, -, -, -, htK, htX, -, -, -, hirr⟩ := stmtPPDElement h
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have htM : t ∈ M := htK.2
  have hn3 := h.three_le
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : r ≤ Open.pRank s Sg := by
    refine stmtOddCoreRank hs hs2 hp (by omega) hr Sg (barM M X) (mk ⟨t, htM⟩)
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.isElemAbelian_barM ?_
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) (fun k hk Y₀ hY₀ hkY₀ => ?_)
      hnot
    · rw [h.card_barM]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    · have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
        rw [← map_pow]
        rfl
      rw [htk] at hkY₀
      exact eq_bot_or_eq_barM_of_mem_normalizer hXM (M.pow_mem htM k)
        (Subgroup.pow_mem _ htX k) (hirr k hk) hY₀ hkY₀
  have hSgK : Sg ≤ barM M (H ⊓ M) := by
    refine h.ph3.le_barM_inf_of_le_centralizer
      (le_trans ?_ (h.ph3.oddCore_le_centralizer h84 hD2))
    refine le_sSup ⟨inferInstance, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hs).mpr (Ne.symm hs2))
  have h4 : 4 ≤ Open.pRank s (H ⊓ M) :=
    calc 4 ≤ r := by omega
      _ ≤ Open.pRank s Sg := hrank
      _ ≤ Open.pRank s (barM M (H ⊓ M)) :=
        CFSG.PreuniquenessRankFour.Helpers.pRank_mono s hs hSgK
      _ ≤ Open.pRank s (H ⊓ M) := pRank_barM_le hs hs2 M (H ⊓ M) inf_le_right
  exact h.false_of_four_le_pRank hs hs2 hsp h4

end CFSG.AGLEmbedding
