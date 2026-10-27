module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
public import CFSG.Open.GLBDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PPointMaxPair
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.Open Subgroup
  CFSG.AGLEmbedding CFSG.LocalAnalysis.RankFourTheoremC

variable {G : Type} [Group G] [Finite G]

private theorem l34Esc_coprime {A : Subgroup G} (hA : IsPGroup 2 A) :
    Nat.Coprime 3 (Nat.card A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := hA.exists_card_eq
  rw [hb]
  exact Nat.Coprime.pow_right _ (by norm_num)

omit [Finite G] in
private theorem l34Esc_le_normalizer_commutator {A X Y : Subgroup G}
    (hX : A ≤ normalizer (X : Set G)) (hY : A ≤ normalizer (Y : Set G)) :
    A ≤ normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hX ha), mem_normalizer_iff_map_conj_eq.mp (hY ha)]

omit [Finite G] in
private theorem l34Esc_invariantTwoMaximalWithin_map {A K T : Subgroup G} (φ : MulAut G)
    (h : invariantTwoMaximalWithin A K T) :
    invariantTwoMaximalWithin (A.map φ.toMonoidHom) (K.map φ.toMonoidHom)
      (T.map φ.toMonoidHom) := by
  refine ⟨map_mono h.1, h.2.1.map φ.toMonoidHom, ?_, ?_⟩
  · have himage := Subgroup.map_mono (f := φ.toMonoidHom) h.2.2.1
    rwa [Subgroup.map_equiv_normalizer_eq] at himage
  · intro L hLK hL hAL hTL
    have hL' := hL.map φ.symm.toMonoidHom
    have hAL' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hAL
    rw [map_automorphism_symm_map, Subgroup.map_equiv_normalizer_eq] at hAL'
    have hLK' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hLK
    rw [map_automorphism_symm_map] at hLK'
    have hTL' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hTL
    rw [map_automorphism_symm_map] at hTL'
    have heq := h.2.2.2 (L.map φ.symm.toMonoidHom) hLK' hL' hAL' hTL'
    apply Subgroup.map_injective (f := φ.symm.toMonoidHom) φ.symm.injective
    rwa [map_automorphism_symm_map]

omit [Finite G] in
private theorem l34Esc_le_normalizer {M M₀ S₁ T : Subgroup G} {x : G} (hM₀M : M₀ ≤ M)
    (hM₀n : (M₀.subgroupOf M).Normal) (hSM₀ : S₁ ⊓ M ⊓ M₀ = ⁅S₁ ⊓ M, zpowers x⁆) :
    T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) ≤
      normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) := by
  have hMM₀ : M ≤ normalizer (M₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM₀M).mp hM₀n
  rw [← hSM₀]
  exact common_normalizer_le_normalizer_inf _ _ _ inf_le_right
    (((inf_le_left.trans inf_le_right).trans (glbPrimeCore_le 3 M)).trans hMM₀)

private theorem l34Esc_exists_conj {M J U S₁ Sc R₀ : Subgroup G} {x : G}
    (hU : IsPGroup 3 U) (hxU : x ∈ U)
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G))
    (hCU : centralizer (U : Set G) ≤ M)
    (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁) (hS₁M : ¬ S₁ ≤ M)
    (hS₁J : invariantTwoMaximalWithin U J (S₁ ⊓ J))
    (hS₁H : S₁ ≤ normalizer (Sc : Set G)) (hUSc : U ≤ normalizer (Sc : Set G))
    (hSc2 : IsPGroup 2 Sc) (hR₀2 : IsPGroup 2 R₀) (hUR₀ : U ≤ normalizer (R₀ : Set G))
    (hR₀Sc : R₀ ≤ normalizer (Sc : Set G))
    (hR₀O : R₀ ≤ GLBPrimeCore 3 (normalizer (Sc : Set G))) :
    ∃ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' ∧ ¬ S₁' ≤ M ∧
      invariantTwoMaximalWithin U J (S₁' ⊓ J) ∧ Sc ⊔ R₀ ≤ S₁' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := normalizer (Sc : Set G) with hH
  set O : Subgroup G := GLBPrimeCore 3 H with hO
  have hHO : H ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 H
  have hUO : U ≤ normalizer (O : Set G) := hUSc.trans hHO
  have hOcop : Nat.Coprime 3 (Nat.card O) := glbPrimeCore_coprime 3 H
  have hS₁Hm : invariantTwoMaximalWithin U H S₁ :=
    ⟨hS₁H, hS₁.1, hS₁.2.1, fun L _ hL hUL hS₁L => hS₁.2.2 L hL hUL hS₁L⟩
  have hY₀ : IsSylowOf 2 (S₁ ⊓ O) O := isSylowOf_inf_of_invariantTwoMaximalWithin
    Nat.prime_three (by norm_num) hU hUSc (glbPrimeCore_le 3 H) hHO hOcop hS₁Hm
  have hY₀U : U ≤ normalizer ((S₁ ⊓ O : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ O hS₁.2.1 hUO
  have hScO : Sc ≤ O := le_glbPrimeCore Subgroup.le_normalizer le_rfl (l34Esc_coprime hSc2)
  have hA2 : IsPGroup 2 ↥(Sc ⊔ R₀) := isPGroup_sup_of_le_normalizer hSc2 hR₀2 hR₀Sc
  have hAO : Sc ⊔ R₀ ≤ O := sup_le hScO hR₀O
  obtain ⟨Y, hY, hYU, hAY⟩ := exists_invariant_isSylowOf_two_normalized Nat.prime_three
    (by norm_num) hU hUO hOcop (hAO.trans Subgroup.le_normalizer) hA2
    (le_normalizer_sup hUSc hUR₀)
  have hAleY : Sc ⊔ R₀ ≤ Y := by
    have hpg := isPGroup_sup_of_le_normalizer hY.isPGroup hA2 hAY
    exact le_sup_right.trans (hY.eq_of_le le_sup_left (sup_le hY.le hAO) hpg).le
  obtain ⟨c, hc, hcY⟩ := exists_centralizer_conj_of_isSylowOf_two Nat.prime_three hU hUO hOcop
    hY₀ hY hY₀U hYU
  have hcM : c ∈ M := hCU hc.2
  have hcU : U.map (MulAut.conj c).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hc.2)
  have hcJ : J.map (MulAut.conj c).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp
      (hCJ (centralizer_le (Set.singleton_subset_iff.mpr hxU) hc.2))
  refine ⟨S₁.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · have h := rankTwoMaximalInvariantTwoSubgroup_map U S₁ (MulAut.conj c) hS₁
    rwa [hcU] at h
  · intro hle
    exact hS₁M ((conjugate_subgroup_le_iff_of_conjugator_mem S₁ M c hcM).mp hle)
  · have h := l34Esc_invariantTwoMaximalWithin_map (MulAut.conj c) hS₁J
    rwa [hcU, Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcJ] at h
  · rw [← hcY] at hAleY
    exact hAleY.trans (Subgroup.map_mono inf_le_left)

private theorem l34Esc_le_commutator {M M₀ S₁ S₁' R₀ Sc : Subgroup G}
    (hidx : M₀.relIndex M ≤ 2) (hNM₀ : GLBPrimeCore 3 M ≤ M₀)
    (hSM₀ : S₁ ⊓ M ⊓ M₀ = Sc) (hR₀N : R₀ ≤ GLBPrimeCore 3 M) (hA : Sc ⊔ R₀ ≤ S₁')
    (hcmp : Nat.card (S₁' ⊓ M : Subgroup G) < Nat.card (S₁ ⊓ M : Subgroup G) ∨
      (Nat.card (S₁' ⊓ M : Subgroup G) = Nat.card (S₁ ⊓ M : Subgroup G) ∧
        Nat.card (S₁' ⊓ GLBPrimeCore 3 M : Subgroup G) ≤
          Nat.card (S₁ ⊓ GLBPrimeCore 3 M : Subgroup G))) :
    R₀ ≤ Sc := by
  set N : Subgroup G := GLBPrimeCore 3 M with hN
  have hNM : N ≤ M := glbPrimeCore_le 3 M
  have hScM : Sc ≤ M := by
    rw [← hSM₀]
    exact inf_le_left.trans inf_le_right
  by_contra hR₀Sc
  have hS : Nat.card (S₁ ⊓ M : Subgroup G) ≤ 2 * Nat.card Sc := by
    have h1 := Subgroup.relIndex_mul_card M₀ (S₁ ⊓ M)
    rw [inf_comm M₀ (S₁ ⊓ M), hSM₀] at h1
    have hne : M₀.relIndex M ≠ 0 := by
      intro h0
      have h2 := Subgroup.relIndex_mul_card M₀ M
      rw [h0, zero_mul] at h2
      exact Nat.card_pos.ne h2
    have h3 := Subgroup.relIndex_le_of_le_right (inf_le_right : S₁ ⊓ M ≤ M) hne
    rw [← h1]
    exact Nat.mul_le_mul_right _ (h3.trans hidx)
  have hScA : Sc < Sc ⊔ R₀ :=
    lt_of_le_of_ne le_sup_left fun h => hR₀Sc (le_sup_right.trans h.symm.le)
  have hA2 : 2 * Nat.card Sc ≤ Nat.card (Sc ⊔ R₀ : Subgroup G) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : Sc ≤ Sc ⊔ R₀)
    have hlt := Subgroup.card_lt_of_lt hScA
    rw [hk] at hlt ⊢
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · nlinarith
  have hAM : Nat.card (Sc ⊔ R₀ : Subgroup G) ≤ Nat.card (S₁' ⊓ M : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf hA (sup_le hScM (hR₀N.trans hNM)))
  rcases hcmp with hlt | ⟨-, hle⟩
  · omega
  ·
    have h1 : S₁ ⊓ N ≤ Sc ⊓ N := by
      refine le_inf ?_ inf_le_right
      rw [← hSM₀]
      exact le_inf (le_inf inf_le_left (inf_le_right.trans hNM)) (inf_le_right.trans hNM₀)
    have h2 : Sc ⊓ N < Sc ⊓ N ⊔ R₀ := lt_of_le_of_ne le_sup_left fun h =>
      hR₀Sc ((le_sup_right.trans h.symm.le).trans inf_le_left)
    have h3 : Sc ⊓ N ⊔ R₀ ≤ S₁' ⊓ N :=
      sup_le (le_inf ((inf_le_left.trans le_sup_left).trans hA) inf_le_right)
        (le_inf (le_sup_right.trans hA) hR₀N)
    have h4 := (Subgroup.card_le_of_le h1).trans_lt
      ((Subgroup.card_lt_of_lt h2).trans_le (Subgroup.card_le_of_le h3))
    omega

private theorem l34Esc_le_of_normalizer_le {S R : Subgroup G} (hS2 : IsPGroup 2 S)
    (hR2 : IsPGroup 2 R) (hSR : S ≤ normalizer (R : Set G))
    (hR₀ : R ⊓ normalizer (S : Set G) ≤ S) : R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hRS
  have hSupg : IsPGroup 2 ↥(S ⊔ R) := by
    have h := isPGroup_sup_of_le_normalizer hR2 hS2 hSR
    rwa [sup_comm] at h
  have hlt : S < S ⊔ R := lt_of_le_of_ne le_sup_left fun h => hRS (le_sup_right.trans h.symm.le)
  have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two (S ⊔ R) S hSupg
    hlt
  obtain ⟨g, hg, hgS⟩ := Set.not_subset.mp hgrow.not_ge
  have hgSR : g ∈ (↑(S ⊔ R) : Set G) := hg.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S R hSR] at hgSR
  obtain ⟨s, hs, r, hr, rfl⟩ := hgSR
  have hrN : r ∈ normalizer (S : Set G) := by
    have h1 : s⁻¹ * (s * r) ∈ normalizer (S : Set G) :=
      (normalizer (S : Set G)).mul_mem ((normalizer (S : Set G)).inv_mem
        (Subgroup.le_normalizer hs)) hg.2
    simpa using h1
  exact hgS (S.mul_mem hs (hR₀ ⟨hr, hrN⟩))

theorem l34_stepI {M J U S₁ T : Subgroup G} {x : G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUM : U ≤ M) (hxU : x ∈ U)
    (_hJx : J ≤ centralizer ({x} : Set G))
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G))
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) → normalizer (Y : Set G) ≤ M)
    (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁) (hS₁M : ¬ S₁ ≤ M)
    (hS₁J : invariantTwoMaximalWithin U J (S₁ ⊓ J))
    (hmax : ∀ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' → ¬ S₁' ≤ M →
      invariantTwoMaximalWithin U J (S₁' ⊓ J) →
      Nat.card (S₁' ⊓ M : Subgroup G) < Nat.card (S₁ ⊓ M : Subgroup G) ∨
        (Nat.card (S₁' ⊓ M : Subgroup G) = Nat.card (S₁ ⊓ M : Subgroup G) ∧
          Nat.card (S₁' ⊓ GLBPrimeCore 3 M : Subgroup G) ≤
            Nat.card (S₁ ⊓ GLBPrimeCore 3 M : Subgroup G)))
    (hF : S₁ ≤ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G))
    (hH : ∃ M₀ : Subgroup G, M₀ ≤ M ∧ (M₀.subgroupOf M).Normal ∧ M₀.relIndex M ≤ 2 ∧
      GLBPrimeCore 3 M ≤ M₀ ∧ S₁ ⊓ M ⊓ M₀ = ⁅S₁ ⊓ M, zpowers x⁆)
    (hT : invariantTwoMaximalWithin U M T) (hST : S₁ ⊓ M ≤ T) :
    T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) ≤
        normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) ∧
      ¬ (T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) ≤
        GLBPrimeCore 3 (normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G))) := by
  obtain ⟨M₀, hM₀M, hM₀n, hidx, hNM₀, hSM₀⟩ := hH
  have hle := l34Esc_le_normalizer (T := T) hM₀M hM₀n hSM₀
  refine ⟨hle, fun hR₀O => ?_⟩
  have hNM : GLBPrimeCore 3 M ≤ M := glbPrimeCore_le 3 M
  have hMN : M ≤ normalizer (GLBPrimeCore 3 M : Set G) := le_normalizer_glbPrimeCore 3 M
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hUS : U ≤ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ M hS₁.2.1 (hUM.trans Subgroup.le_normalizer)
  have hUx : U ≤ normalizer ((zpowers x : Subgroup G) : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr hU.1).trans
      (centralizer_le (zpowers_le.mpr hxU))).trans (centralizer_le_normalizer _)
  have hUSc : U ≤ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) :=
    l34Esc_le_normalizer_commutator hUS hUx
  have hScS : ⁅S₁ ⊓ M, zpowers x⁆ ≤ S₁ ⊓ M :=
    le_normalizer_iff_commutator_le_left.mp ((zpowers_le.mpr hxU).trans hUS)
  have hS2 : IsPGroup 2 (S₁ ⊓ M : Subgroup G) := hS₁.1.to_inf_left
  have hSc2 : IsPGroup 2 (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) := hS2.to_le hScS
  have hR₀2 : IsPGroup 2
      (T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) : Subgroup G) :=
    hT.2.1.to_inf_left.to_inf_left
  have hUR₀ : U ≤ normalizer
      ((T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) : Subgroup G) :
        Set G) :=
    common_normalizer_le_normalizer_inf U _ _
      (common_normalizer_le_normalizer_inf U T _ hT.2.2.1 (hUM.trans hMN))
      (hUS.trans Subgroup.le_normalizer)
  have hCU : centralizer (U : Set G) ≤ M := by
    obtain ⟨u, huU, hux⟩ : ∃ u ∈ U, u ∉ zpowers x := by
      by_contra hno
      push Not at hno
      have h1 := Subgroup.card_le_of_le (show U ≤ zpowers x from fun u hu => hno u hu)
      have h2 : orderOf x ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hU.2 x hxU)
      rw [hUc, Nat.card_zpowers] at h1
      omega
    exact (centralizer_le (Set.singleton_subset_iff.mpr huU)).trans (hC u huU hux)
  obtain ⟨S₁', hS₁', hS₁'M, hS₁'J, hA⟩ := l34Esc_exists_conj hUp hxU hCJ hCU hS₁ hS₁M hS₁J hF
    hUSc hSc2 hR₀2 hUR₀ hle hR₀O
  have hR₀Sc := l34Esc_le_commutator hidx hNM₀ hSM₀ (inf_le_left.trans inf_le_right) hA
    (hmax S₁' hS₁' hS₁'M hS₁'J)
  have hSR : S₁ ⊓ M ≤ normalizer ((T ⊓ GLBPrimeCore 3 M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf _ T _ (hST.trans Subgroup.le_normalizer)
      (inf_le_right.trans hMN)
  have hRS : T ⊓ GLBPrimeCore 3 M ≤ S₁ ⊓ M :=
    l34Esc_le_of_normalizer_le hS2 hT.2.1.to_inf_left hSR (hR₀Sc.trans hScS)
  have hScN : ⁅S₁ ⊓ M, zpowers x⁆ ⊓ GLBPrimeCore 3 M = T ⊓ GLBPrimeCore 3 M := by
    refine le_antisymm (inf_le_inf_right _ (hScS.trans hST)) (le_inf ?_ inf_le_right)
    rw [← hSM₀]
    exact le_inf hRS (inf_le_right.trans hNM₀)
  have hSyl : IsSylowOf 2 (T ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) :=
    isSylowOf_inf_of_invariantTwoMaximalWithin Nat.prime_three (by norm_num) hUp hUM hNM hMN
      (glbPrimeCore_coprime 3 M) hT
  have hHM := hL43 _ hSc2 (hScS.trans inf_le_right) hUSc (by rw [hScN]; exact hSyl)
  exact hS₁M (hF.trans hHM)

end CFSG.LocalAnalysis.RankThreeTheoremC
