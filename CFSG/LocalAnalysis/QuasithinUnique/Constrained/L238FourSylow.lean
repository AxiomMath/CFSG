
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommute
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L238

variable {G : Type} [Group G]

theorem not_isPGroup_two_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) : ¬ IsPGroup 2 L := by
  intro hp
  have h : (⊥ : Subgroup ↥L) = ⊤ := hL.1 ⊥ (fun q => by
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hp x
      exact ⟨k, by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]⟩)
  apply C1GN.isShort2_ne_bot hL
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := h ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_bot.1 h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)

theorem isPGroup_two_bot : IsPGroup 2 (⊥ : Subgroup G) := fun x =>
  ⟨0, Subtype.ext (by simpa using Subgroup.mem_bot.1 x.2)⟩

section Components

variable [Finite G]

theorem mem_cComp_of_isBlock2 {X L : Subgroup G} (hL : IsBlock2 X L)
    (h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : L ∈ cComp X :=
  C1GN.mem_cComp_of_short hL.1 (hL.1.2.2.2.1.resolve_right h3) (C1GN.isSubnormal_of_isBlock2 hL)

omit [Finite G] in
theorem card_ne_three_of_isLin2Type {L : Subgroup G} {n : ℕ} (hn : 1 < n) (h : IsLin2Type L n) :
    ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := h
  intro h3
  have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) :=
    QuotientGroup.quotientMulEquivOfEq hαk.symm
  have e2 := QuotientGroup.quotientKerEquivOfSurjective α hαs
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := Nat.card_congr (e1.trans e2).toEquiv
  rw [h3, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at hc
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have h4 : 4 ≤ Nat.card F := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ Nat.card F ^ 2 := by nlinarith
  have h15 : 15 ≤ Nat.card F ^ 2 - 1 := by omega
  have h60 : Nat.card F * 15 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul_left _ h15
  omega

omit [Finite G] in
theorem card_ne_three_of_isAltType {L : Subgroup G} {m : ℕ} (hm : 5 ≤ m) (h : IsAltType L m) :
    ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  intro h3
  have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) :=
    QuotientGroup.quotientMulEquivOfEq hαk.symm
  have e2 := QuotientGroup.quotientKerEquivOfSurjective α hαs
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin m)) :=
    Nat.card_congr (e1.trans e2).toEquiv
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [h3, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
  have h5 : Nat.factorial 5 = 120 := by decide
  have h120 : Nat.factorial 5 ≤ Nat.factorial m := Nat.factorial_le hm
  omega

theorem mem_cComp_of_isChiBlock {X L : Subgroup G} (hL : IsChiBlock X L) (h3 : ¬ IsAltType L 3) :
    L ∈ cComp X := by
  refine mem_cComp_of_isBlock2 hL.1 ?_
  rcases hL.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · exact card_ne_three_of_isLin2Type hn hlin
  · by_cases hm3' : m = 3
    · subst hm3'
      exact absurd halt h3
    · have hm5 : 5 ≤ m := by
        obtain ⟨k, rfl⟩ := hm
        omega
      exact card_ne_three_of_isAltType hm5 halt

theorem mem_cComp_of_isChi0Block_nonsolvable {X L : Subgroup G} (hL : IsBlock2 X L)
    (hty : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) : L ∈ cComp X := by
  refine mem_cComp_of_isBlock2 hL ?_
  rcases hty with ⟨n, hn, hlin⟩ | h5
  · exact card_ne_three_of_isLin2Type hn hlin
  · exact card_ne_three_of_isAltType le_rfl h5

end Components

section Dichotomy

variable [Finite G]

theorem sylow_dichotomy {X T L : Subgroup G} (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X))
    (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X) :
    X ≤ Subgroup.normalizer (L : Set G) ∨
      (¬ T ≤ Subgroup.normalizer (L : Set G) ∧ ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set G) ∨
        L ⊓ L.map (MulAut.conj s).toMonoidHom ≤ pCoreOf 2 X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLb := modO2Image_mem_cComp hL
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hT)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2⟩ := h38 _ hLb
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨t, htT, htn, hset, -, -, hinter, -, -⟩
  · left
    have hn : (L.subgroupOf X).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥X) (isSolvable_pCore_two_group ↥X)
        (subgroupOf_mem_cComp hL) hnorm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hn
  · right
    refine ⟨?_, ?_⟩
    · intro hTL
      apply htn
      obtain ⟨s', hs'T, rfl⟩ := htT
      have hs'N : s' ∈ Subgroup.normalizer ((L.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        have hsG : (s' : G) ∈ T := hs'T
        have := (Subgroup.mem_normalizer_iff.mp (hTL hsG) (x : G))
        simpa using this
      exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) ⟨s', hs'N, rfl⟩
    · intro s hs
      by_cases hsN : s ∈ Subgroup.normalizer (L : Set G)
      · exact Or.inl hsN
      · right
        have hsX : s ∈ X := hT.1 hs
        let s' : ↥X := ⟨s, hsX⟩
        have hs'T : s' ∈ T.subgroupOf X := hs
        have hπs : QuotientGroup.mk' (CFSG.pCore 2 ↥X) s' ∈
            (T.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
          Subgroup.mem_map.2 ⟨s', hs'T, rfl⟩
        have hmem : (modO2Image X L).map
            (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥X) s')).toMonoidHom ∈
            conjSubgroupsBy ((T.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)))
              (modO2Image X L) := ⟨_, hπs, rfl⟩
        have hconj : modO2Image X (L.map (MulAut.conj s).toMonoidHom) =
            (modO2Image X L).map
              (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥X) s')).toMonoidHom :=
          modO2Image_conj s'
        rw [hset] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · exfalso
          apply hsN
          have hLs : L.map (MulAut.conj s).toMonoidHom ∈ cComp X := map_conj_mem_cComp hL hsX
          have h1 : modO2Image X (L.map (MulAut.conj s).toMonoidHom) = modO2Image X L := by
            rw [hconj]
            exact h
          exact A38.map_conj_eq_iff.mp (modO2Image_injOn X hLs hL h1)
        · intro g hg
          have hgX : g ∈ X := hLX hg.1
          have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨g, hgX⟩ ∈ modO2Image X L := by
            unfold modO2Image
            exact Subgroup.mem_map.2 ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.mpr hg.1, rfl⟩
          have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨g, hgX⟩ ∈
              modO2Image X (L.map (MulAut.conj s).toMonoidHom) := by
            unfold modO2Image
            exact Subgroup.mem_map.2 ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.mpr hg.2, rfl⟩
          rw [hconj, h] at h2
          have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨g, hgX⟩ ∈
              modO2Image X L ⊓ (modO2Image X L).map (MulAut.conj t).toMonoidHom := ⟨h1, h2⟩
          rw [hinter, Subgroup.mem_bot] at h3
          have h4 : (⟨g, hgX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).1 h3
          have hP : (CFSG.pCore 2 ↥X).map X.subtype = pCoreOf 2 X := by
            rfl
          rw [← hP]
          exact ⟨⟨g, hgX⟩, h4, rfl⟩

theorem le_normalizer_of_sylow_le_normalizer {X T L : Subgroup G}
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : X ≤ Subgroup.normalizer (L : Set G) :=
  (sylow_dichotomy h38 hT hL).resolve_right fun h => h.1 hTL

end Dichotomy

section Normalizing

variable [Finite G]

theorem le_normalizer_of_commutator_le {X T L K J : Subgroup G}
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hKL : K ≤ L) (hK2 : ¬ IsPGroup 2 K) (hJT : J ≤ T) (hKJ : ⁅K, J⁆ ≤ L) :
    J ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro j hj
  by_contra hjN
  have hjT : j ∈ T := hJT hj
  have hjX : j ∈ X := hT.1 hjT
  rcases sylow_dichotomy h38 hT hL with hX | ⟨-, hs⟩
  · exact hjN (hX hjX)
  · rcases hs j hjT with h | h
    · exact hjN h
    · apply hK2
      have hKO : K ≤ pCoreOf 2 X := by
        intro g hg
        have h1 : ⁅g, j⁆ ∈ L := hKJ (Subgroup.commutator_mem_commutator hg hj)
        have h2 : j * g * j⁻¹ ∈ L := by
          have h3 : g⁻¹ * ⁅g, j⁆ ∈ L := L.mul_mem (L.inv_mem (hKL hg)) h1
          have h4 : g⁻¹ * ⁅g, j⁆ = (j * g * j⁻¹)⁻¹ := by
            rw [commutatorElement_def]
            group
          rw [h4] at h3
          simpa using L.inv_mem h3
        have h5 : j * g * j⁻¹ ∈ L.map (MulAut.conj j).toMonoidHom := ⟨g, hKL hg, rfl⟩
        have h6 : j * g * j⁻¹ ∈ pCoreOf 2 X := h ⟨h2, h5⟩
        have hN : j⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem hjX)
        have h7 := (Subgroup.mem_normalizer_iff.1 hN (j * g * j⁻¹)).1 h6
        have h8 : j⁻¹ * (j * g * j⁻¹) * j⁻¹⁻¹ = g := by group
        rwa [h8] at h7
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hKO

theorem le_normalizer_of_commutator_le_alt3 {X L K J : Subgroup G} (hX : CharTwo X)
    (hL : IsBlock2 X L) (hL3 : IsAltType L 3) (hKL : K ≤ L) (hK0 : K ≠ ⊥) (hJX : J ≤ X)
    (hKJ : ⁅K, J⁆ ≤ L) : J ≤ Subgroup.normalizer (L : Set G) := by
  intro j hj
  by_contra hjN
  have hjX : j ∈ X := hJX hj
  have hLjb : IsBlock2 X (L.map (MulAut.conj j).toMonoidHom) :=
    CFSG.Quasithin.IsBlock2.conjByElt_of_mem hL hjX
  have hLj3 : IsAltType (L.map (MulAut.conj j).toMonoidHom) 3 :=
    IsAltType.map_equiv hL3 (MulAut.conj j)
  have hne : L ≠ L.map (MulAut.conj j).toMonoidHom := fun h => hjN (A38.map_conj_eq_iff.mp h.symm)
  obtain ⟨c, hc⟩ := S14110.A4Data.of_isShort2 hL.1 hL3
  obtain ⟨c', hc'⟩ := S14110.A4Data.of_isShort2 hLjb.1 hLj3
  rcases S14110.commute_or_eq_of_isSubnormal hX hL.2.1 hLjb.2.1 hL.2.2 hLjb.2.2 hc hc' with
    h | hcomm
  · exact hne h
  · apply hK0
    rw [eq_bot_iff]
    intro g hg
    have h1 : ⁅g, j⁆ ∈ L := hKJ (Subgroup.commutator_mem_commutator hg hj)
    have h2 : j * g * j⁻¹ ∈ L := by
      have h3 : g⁻¹ * ⁅g, j⁆ ∈ L := L.mul_mem (L.inv_mem (hKL hg)) h1
      have h4 : g⁻¹ * ⁅g, j⁆ = (j * g * j⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h4] at h3
      simpa using L.inv_mem h3
    have h5 : j * g * j⁻¹ ∈ L.map (MulAut.conj j).toMonoidHom := ⟨g, hKL hg, rfl⟩
    have h6 : j * g * j⁻¹ = 1 :=
      hc.center _ h2 (fun l hl => (hcomm l hl _ h5).symm)
    have h7 : g = 1 := by
      calc g = j⁻¹ * (j * g * j⁻¹) * j := by group
        _ = 1 := by rw [h6]; group
    rw [h7]
    exact Subgroup.one_mem _

theorem le_normalizer_of_commutator_le_isChiBlock {X T L K J : Subgroup G} (hX : CharTwo X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hL : IsChiBlock X L)
    (hKL : K ≤ L) (hK2 : ¬ IsPGroup 2 K) (hJT : J ≤ T) (hKJ : ⁅K, J⁆ ≤ L) :
    J ≤ Subgroup.normalizer (L : Set G) := by
  by_cases h3 : IsAltType L 3
  · have hK0 : K ≠ ⊥ := fun h => hK2 (by rw [h]; exact isPGroup_two_bot)
    exact le_normalizer_of_commutator_le_alt3 hX hL.1 h3 hKL hK0 (hJT.trans hT.1) hKJ
  · exact le_normalizer_of_commutator_le h38 hT (mem_cComp_of_isChiBlock hL h3) hKL hK2 hJT hKJ

end Normalizing

end L238

end CFSG.QuasithinUnique
