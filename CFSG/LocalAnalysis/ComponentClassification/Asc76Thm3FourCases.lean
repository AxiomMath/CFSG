module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourPsl
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryOut
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Core
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourTwo

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G]

theorem center_eq_bot_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card X) (hne : Nat.card X ≠ p) : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
    have hn : (zpowers x).Normal := by
      constructor
      intro n hn g
      have hg : g ∈ center X := by rw [h]; exact mem_top g
      rw [mem_center_iff] at hg
      have e : g * n * g⁻¹ = n := by rw [← hg n, mul_inv_cancel_right]
      rw [e]
      exact hn
    rcases hn.eq_bot_or_eq_top with h1 | h1
    · have hx1 : x = 1 := zpowers_eq_bot.mp h1
      rw [hx1, orderOf_one] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
    · apply hne
      rw [← hx, ← Nat.card_zpowers, h1, card_top]

theorem pCore_ne_bot_of_equiv_alternating_four {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 4)) : CFSG.pCore 2 X ≠ ⊥ := by
  have hc : Nat.card (Fin 4) = 4 := by simp
  have hV : alternatingGroup.kleinFour (Fin 4) ≤ CFSG.pCore 2 (alternatingGroup (Fin 4)) := by
    refine le_sSup ⟨alternatingGroup.normal_kleinFour hc, ?_⟩
    exact IsPGroup.of_card (n := 2) (by
      rw [alternatingGroup.kleinFour_card_of_card_eq_four hc]
      norm_num)
  have hV1 : alternatingGroup.kleinFour (Fin 4) ≠ ⊥ := by
    intro hb
    have h1 := alternatingGroup.kleinFour_card_of_card_eq_four hc
    rw [hb, card_bot] at h1
    omega
  intro hb
  have h1 := CFSG.pCore_map_iso 2 e
  rw [hb, Subgroup.map_bot] at h1
  exact hV1 (le_bot_iff.mp (hV.trans h1.symm.le))

namespace Setting

variable {K R S : Subgroup G} [Finite G]

theorem le_of_normal_isPGroup (h : Setting K R S) (Q : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) : Q ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(Q ⊔ S) := hQ.to_sup_of_normal_left h.sylow.isPGroup
  have h1 := h.sylow.eq_of_le le_sup_right le_top hp
  rw [← h1]
  exact le_sup_left

theorem cases_dihedral
    (h : Setting K R S) (hKn : ¬ K.Normal) {M : Subgroup G} [hMn : M.Normal]
    (hMdef : M = normalClosure (R : Set G)) (hOM : CFSG.oddCore M = ⊥)
    (hSylM : IsSylowOf 2 (S ⊓ M) M) (hDih : CFSG.GorensteinWalter.HasDihedralSylowTwo M)
    (hP8 : Nat.card (S ⊓ M : Subgroup G) ∣ 8)
    (hcen : ∀ u ∈ S ⊓ M, (∀ s ∈ S ⊓ M, u * s = s * u) → u ∈ R)
    (hmeet : ∀ V : Subgroup G, V ≤ S ⊓ M → 4 ≤ Nat.card V → V ⊓ R ≠ ⊥) :
    (∃ U : Subgroup G, U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2 ∧
      IsMulCommutative (normalClosure (U : Set G))) ∨ IsSmall G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRM : R ≤ M := hMdef ▸ subset_normalClosure
  have hRSM : R ≤ S ⊓ M := le_inf h.le hRM
  have key : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → Q ≤ M → Q ≠ ⊥ →
      ∃ U : Subgroup G, U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2 ∧
        IsMulCommutative (normalClosure (U : Set G)) := fun Q hQn hQ2 hQM hQ1 =>
    (h.normal_or_cyclic hRSM inf_le_left hP8 hcen Q hQ2
      (le_inf (h.le_of_normal_isPGroup Q hQ2) hQM) hQ1).resolve_left
      fun hRn => hKn (h.normal_of_normal_R hRn)
  by_cases hNC : CFSG.HasNormalPComplement 2 M
  ·
    left
    obtain ⟨N, hN, hcop, hq⟩ := hNC
    have hN1 : N = ⊥ := by
      have h1 : N ≤ CFSG.oddCore M := le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩
      rw [hOM] at h1
      exact le_bot_iff.mp h1
    subst hN1
    have hM2 : IsPGroup 2 M := hq.of_equiv QuotientGroup.quotientBot
    refine key M hMn hM2 le_rfl fun hb => h.R_ne_bot ?_
    rw [eq_bot_iff, ← hb]
    exact hRM
  rcases CFSG.ABGDGroups.aSeven_or_exists_normal_psl2 hDih hNC hOM with
    he7 | ⟨F, _, _, hF, N, hNn, ⟨eN⟩, hCN⟩
  ·
    right
    obtain ⟨e7⟩ := he7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup M := e7.isSimpleGroup
    have hcardM : Nat.card M = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hZ : center M = ⊥ :=
      center_eq_bot_of_simple (p := 2) (by rw [hcardM]; norm_num) (by rw [hcardM]; norm_num)
    have hout : Nat.card (Outer M) ∣ 2 ^ 1 := by
      rw [pow_one]
      exact outer_card_dvd_two_of_equiv_outside_six (Or.inr le_rfl) e7
    have hMtop := h.eq_top_of_normal M hRM hZ hout
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨(topEquiv.symm.trans (MulEquiv.subgroupCongr hMtop.symm)).trans e7⟩)))
  ·
    set N' := N.map M.subtype with hN'def
    have eN' : N' ≃* CFSG.GorensteinWalter.PSL2 F :=
      (N.equivMapOfInjective M.subtype M.subtype_injective).symm.trans eN
    have hN'M : N' ≤ M := map_subtype_le N
    have hN'n : ∀ m ∈ M, ∀ x ∈ N', m * x * m⁻¹ ∈ N' := by
      rintro m hm _ ⟨y, hy, rfl⟩
      exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hNn.conj_mem y hy ⟨m, hm⟩, rfl⟩
    have hCN' : ∀ c ∈ M, (∀ x ∈ N', c * x = x * c) → c = 1 := fun c hc hcx => by
      have h1 : (⟨c, hc⟩ : M) ∈ centralizer (N : Set M) := by
        rw [mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact (hcx y ⟨y, hy, rfl⟩).symm
      rw [hCN, mem_bot] at h1
      exact congrArg Subtype.val h1
    by_cases h3 : Nat.card F = 3
    ·
      left
      have : Fintype F := Fintype.ofFinite F
      let eK : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
        (by simpa [Nat.card_eq_fintype_card] using h3)
      have eA : N ≃* alternatingGroup (Fin 4) :=
        eN.trans ((CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
          CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup)
      have hpN : CFSG.pCore 2 N ≠ ⊥ := pCore_ne_bot_of_equiv_alternating_four eA
      have hV : ((CFSG.pCore 2 N).map N.subtype).Normal :=
        ConjAct.normal_of_characteristic_of_normal
      have hV2 : IsPGroup 2 ((CFSG.pCore 2 N).map N.subtype) := CFSG.pCore_isPGroup.map _
      have hle : (CFSG.pCore 2 N).map N.subtype ≤ CFSG.pCore 2 M := le_sSup ⟨hV, hV2⟩
      set Q := (CFSG.pCore 2 M).map M.subtype with hQdef
      have hQn : Q.Normal := ConjAct.normal_of_characteristic_of_normal
      have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
      have hQ1 : Q ≠ ⊥ := by
        intro hb
        apply hpN
        rw [hQdef, map_eq_bot_iff_of_injective _ M.subtype_injective] at hb
        rw [hb, le_bot_iff, map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
        exact hle
      exact key Q hQn hQ2 (map_subtype_le _) hQ1
    · right
      have h5 : 5 ≤ Nat.card F := by
        obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hF
        have hodd : Odd (Nat.card F) := hq ▸ hpodd.pow
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      exact h.small_of_psl2 hKn hRM (hMdef ▸ le_rfl) hSylM hmeet hF h5 hN'M hN'n eN' hCN'

theorem cases
    (h : Setting K R S) (hKn : ¬ K.Normal) (hRd : Nonempty (R ≃* DihedralGroup 2)) :
    (∃ U : Subgroup G, U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2 ∧
      IsMulCommutative (normalClosure (U : Set G))) ∨ IsSmall G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalClosure (R : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hRM : R ≤ M := subset_normalClosure
  have hOM : CFSG.oddCore M = ⊥ := CFSG.ABGDGroups.oddCore_eq_bot_of_normal h.odd M
  have hSylM : IsSylowOf 2 (S ⊓ M) M := h.sylow.inf_of_le_normalizer le_top (by
    rw [normalizer_eq_top_iff.mpr hMn])
  have hS2 : IsPGroup 2 S := h.sylow.isPGroup
  have hRSM : R ≤ S ⊓ M := le_inf h.le hRM
  rcases hallFusionThm32 G S R h.sylow h.le h.card h.elem h.wc with hH1 | hH2 | hH3
  ·
    have hSMR : S ⊓ M = R := hH1.eq_of_le hRSM inf_le_right (hS2.to_le inf_le_left)
    refine h.cases_dihedral hKn hMdef hOM hSylM ?_ ?_ ?_ ?_
    · obtain ⟨Q₀, hQ₀⟩ := hH1
      obtain ⟨eR⟩ := hRd
      intro S'
      refine ⟨1, le_rfl, ⟨?_⟩⟩
      exact ((Sylow.equiv S' Q₀).trans ((Q₀ : Subgroup M).equivMapOfInjective M.subtype
        M.subtype_injective)).trans ((MulEquiv.subgroupCongr hQ₀).trans eR)
    · rw [hSMR, h.card]
      norm_num
    · intro u hu _
      rw [hSMR] at hu
      exact hu
    · intro V hV hV4 hb
      rw [hSMR] at hV
      rw [inf_eq_left.mpr hV] at hb
      rw [hb, card_bot] at hV4
      omega
  ·
    right; left
    obtain ⟨e⟩ := hH2
    have hO' : CFSG.Assembly.oddCore M = ⊥ := hOM
    let eM : M ≃* PSU3 2 2 := (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO'.symm)).trans e
    have : IsSimpleGroup (PSU3 2 2) :=
      CFSG.ShultStronglyClosedTI.unitaryCover_native_simple 2 le_rfl
    have : IsSimpleGroup M := eM.isSimpleGroup
    have hcardM : Nat.card M = 62400 := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3 (by norm_num)]
      norm_num
    have hZ : center M = ⊥ :=
      center_eq_bot_of_simple (p := 2) (by rw [hcardM]; norm_num) (by rw [hcardM]; norm_num)
    have hout : Nat.card (Outer M) ∣ 2 ^ 2 := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eM).toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.UnitaryOut.card_outer_psu3 le_rfl]
      norm_num
    have hMtop := h.eq_top_of_normal M hRM hZ hout
    exact ⟨(topEquiv.symm.trans (MulEquiv.subgroupCongr hMtop.symm)).trans eM⟩
  ·
    obtain ⟨e⟩ := hH3 (S ⊓ M) hSylM
    refine h.cases_dihedral hKn hMdef hOM hSylM ?_ ?_ ?_ ?_
    · intro S'
      obtain ⟨eP⟩ := hH3 ((S' : Subgroup M).map M.subtype) ⟨S', rfl⟩
      exact ⟨2, by norm_num, ⟨((S' : Subgroup M).equivMapOfInjective M.subtype
        M.subtype_injective).trans eP⟩⟩
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    · intro u hu hc
      rcases eq_of_central e hu hc with h1 | h1
      · rw [h1]
        exact one_mem R
      · rw [h1]
        exact dihedralCenter_mem_of_le e hRSM (by rw [h.card])
    · intro V hV hV4 hb
      have h1 : dihedralCenter e ∈ V ⊓ R :=
        ⟨dihedralCenter_mem_of_le e hV hV4, dihedralCenter_mem_of_le e hRSM (by rw [h.card])⟩
      rw [hb, mem_bot] at h1
      exact dihedralCenter_ne_one e h1

end Setting

end CFSG.ComponentClassification.Asc76X.Thm3Four
