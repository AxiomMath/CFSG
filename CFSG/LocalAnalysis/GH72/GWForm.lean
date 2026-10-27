module

public import CFSG.LocalAnalysis.GH72.OuterFacts
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerStructure
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.GorensteinWalter (HasDihedralSylowTwo IsOddPrimePower PSL2 PGL2)

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_of_hasDihedralSylowTwo (hD : HasDihedralSylowTwo G) :
    2 ∣ Nat.card G := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨m, -, ⟨e⟩⟩ := hD S
  refine dvd_trans ?_ (S : Subgroup G).card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact dvd_mul_right 2 _

theorem index_ne_two_of_normal_index_ne_two (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (M : Subgroup G) : M.index ≠ 2 := fun hM => h2 M (normal_of_index_eq_two hM) hM

theorem nonempty_ringEquiv_galoisField {K : Type} [Field K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hK : Nat.card K = p ^ n) : Nonempty (K ≃+* GaloisField p n) := by
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (GaloisField p n)
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card p n hn])⟩

theorem card_pgl2_eq_two_mul_card_psl2 {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    Nat.card (PGL2 K) = 2 * Nat.card (PSL2 K) := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula, CFSG.GorensteinWalter.psl2_card_formula K hK]
  obtain ⟨p, n, -, hp, -, hq⟩ := hK
  have hodd : Odd (Nat.card K) := hq ▸ hp.pow
  have h2 : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  exact (Nat.mul_div_cancel' h2).symm

theorem false_of_normal_pgl2 (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {K : Type}
    [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (L : Subgroup G) (hLn : L.Normal)
    (hL : Odd L.index) (e : L ≃* PGL2 K) : False := by
  obtain ⟨M, hMn, -, ⟨eM⟩⟩ : ∃ M : Subgroup G, M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* PSL2 K) := by
    by_cases h3 : Nat.card K = 3
    · letI := Fintype.ofFinite K
      let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
        (by simpa [Nat.card_eq_fintype_card] using h3)
      obtain ⟨M, hMn, hML, ⟨eM⟩⟩ :=
        CFSG.GorensteinWalter.exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three L hLn
          (e.trans (CFSG.GorensteinWalter.pgl2RingEquiv eK).symm)
      exact ⟨M, hMn, hML, ⟨eM.trans (CFSG.GorensteinWalter.psl2RingEquiv eK)⟩⟩
    · have hgt : 3 < Nat.card K := by
        obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
        have hodd : Odd (Nat.card K) := hq ▸ hpodd.pow
        have hone : 1 < Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      exact CFSG.GorensteinWalter.exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
        L hLn K hK hgt e
  have hcard : Nat.card L = 2 * Nat.card M := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr eM.toEquiv, card_pgl2_eq_two_mul_card_psl2 hK]
  have hidx : M.index = 2 * L.index := by
    have h1 := M.card_mul_index
    have h1' := L.card_mul_index
    rw [hcard, ← h1] at h1'
    have hpos : 0 < Nat.card M := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← h1']; ring)
  obtain ⟨M₂, hM₂n, hM₂, -⟩ :=
    CFSG.GorensteinWalter.exists_normal_index_two_containing_of_index_eq_two_mul_odd hMn
      (by rw [hidx]; exact dvd_mul_right 2 _)
      (by
        rw [hidx]
        obtain ⟨k, hk⟩ := hL
        omega)
  exact h2 M₂ hM₂n hM₂

theorem le_commutator_of_commutator_eq_top {X : Type*} [Group X] (L : Subgroup X)
    (hL : commutator L = ⊤) : L ≤ commutator X := by
  have h : (commutator L).map L.subtype = ⁅L, L⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [hL, ← MonoidHom.range_eq_map, range_subtype] at h
  rw [h, _root_.commutator_def]
  exact commutator_mono le_top le_top

theorem gw_alternatingGroup_four_or_commutator
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hD : HasDihedralSylowTwo G) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      (Odd (commutator G).index ∧ IsL2OrA7 (commutator G) 5 ∧
        centralizer (commutator G : Set G) = ⊥) := by
  have hO2 : CFSG.pPrimeCore 2 G = ⊥ := (CFSG.ABGDGroups.oddCore_eq_pPrimeCore_two G) ▸ hO
  rcases CFSG.QuasiDihedralFusion.gw_cases hD hO with hP | ⟨⟨e7⟩⟩ | ⟨K, _, _, hK, L, hLn, hLodd, hL⟩
  ·
    exfalso
    exact CFSG.ABGDGroups.not_hasNormalPComplement_of_noIndexTwo
      (index_ne_two_of_normal_index_ne_two h2) (two_dvd_card_of_hasDihedralSylowTwo hD)
      ⟨⊥, inferInstance, by simp, hP.of_equiv (QuotientGroup.quotientBot (G := G)).symm⟩
  ·
    right
    have hperf : commutator G = ⊤ := by
      have h := commutator_alternatingGroup_eq_top (α := Fin 7) (by simp)
      rw [eq_top_iff]
      intro x _
      have hx : e7 x ∈ commutator (alternatingGroup (Fin 7)) := h ▸ mem_top _
      rw [_root_.commutator_def] at hx ⊢
      have := Subgroup.mem_map_of_mem e7.symm.toMonoidHom hx
      rw [map_commutator, map_top_of_surjective _ e7.symm.surjective] at this
      simpa using this
    refine ⟨by rw [hperf, index_top]; exact odd_one, ?_, ?_⟩
    · exact Or.inl ⟨(MulEquiv.subgroupCongr hperf).trans (topEquiv.trans e7)⟩
    · rw [hperf, coe_top, centralizer_univ]
      exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e7
        (alternatingGroup.center_eq_bot (by simp))
  · rcases hL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    swap
    · exact (false_of_normal_pgl2 h2 hK L hLn hLodd e).elim
    haveI := hLn
    have hC : centralizer (L : Set G) = ⊥ :=
      CFSG.GorensteinWalter.centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
        hD hO2 L hLn
        (CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
          (CFSG.GorensteinWalter.psl2_center_eq_bot K))
        (CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
          (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hK))
    by_cases h3 : Nat.card K = 3
    ·
      left
      rcases CFSG.ABGDGroups.nonempty_mulEquiv_psl2_three_or_pgl2_three h3 e hC with
        ⟨⟨eG⟩⟩ | ⟨⟨eG⟩⟩
      · exact ⟨eG.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup⟩
      · exfalso
        have hG : Nat.card G = 2 * Nat.card L := by
          have hK3 : IsOddPrimePower (Nat.card (ZMod 3)) :=
            ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simp⟩
          rw [Nat.card_congr eG.toEquiv, card_pgl2_eq_two_mul_card_psl2 hK3,
            Nat.card_congr e.toEquiv]
          letI := Fintype.ofFinite K
          let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
            (by simpa [Nat.card_eq_fintype_card] using h3)
          rw [Nat.card_congr (CFSG.GorensteinWalter.psl2RingEquiv eK).toEquiv]
        have hidx : L.index = 2 := by
          have h1 := L.card_mul_index
          rw [hG] at h1
          have hpos : 0 < Nat.card L := Nat.card_pos
          exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
        rw [hidx] at hLodd
        exact absurd hLodd (by decide)
    ·
      right
      obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
      haveI : Fact p.Prime := ⟨hp⟩
      have hgt : 3 < Nat.card K := by
        have hodd : Odd (Nat.card K) := hq ▸ hpodd.pow
        have hone : 1 < Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      have hLperf : commutator L = ⊤ := by
        have h := (CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three K hgt).commutator_eq_top
        rw [eq_top_iff]
        intro x _
        have hx : e x ∈ commutator (PSL2 K) := h ▸ mem_top _
        rw [_root_.commutator_def] at hx ⊢
        have := Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
        rw [map_commutator, map_top_of_surjective _ e.symm.surjective] at this
        simpa using this
      have hcomm : commutator G = L := by
        refine le_antisymm ?_ (le_commutator_of_commutator_eq_top L hLperf)
        have h := commutator_le_sup_centralizer_of_outer_mul_comm L
          (outer_mul_comm_of_mulEquiv_psl2 e)
        rwa [hC, sup_bot_eq] at h
      have h5 : 5 ≤ p ^ n := by
        have hodd : Odd (Nat.card K) := hq ▸ hpodd.pow
        obtain ⟨k, hk⟩ := hodd
        omega
      obtain ⟨eK⟩ := nonempty_ringEquiv_galoisField (p := p) (n := n) (by omega) hq
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact absurd hpodd (by decide)
      refine ⟨hcomm ▸ hLodd, Or.inr ⟨p, n, ⟨hp⟩, hp2, h5, ⟨(MulEquiv.subgroupCongr hcomm).trans
          (e.trans (CFSG.GorensteinWalter.psl2RingEquiv eK))⟩⟩, hcomm ▸ hC⟩

theorem isKleinFour_commutator_of_mulEquiv_alternatingGroup_four {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 4)) :
    IsKleinFour (commutator X) ∧ (commutator X).index = 3 := by
  have hmap : (commutator X).map e.toMonoidHom = alternatingGroup.kleinFour (Fin 4) := by
    rw [alternatingGroup.kleinFour_eq_commutator (by simp), _root_.commutator_def,
      _root_.commutator_def, map_commutator, map_top_of_surjective _ e.surjective]
  have hV : IsKleinFour ((alternatingGroup.kleinFour (Fin 4)).map e.symm.toMonoidHom) :=
    CFSG.ABGDGroups.isKleinFour_map_of_injective e.symm.injective
      (alternatingGroup.kleinFour_isKleinFour (by simp))
  have hback : (alternatingGroup.kleinFour (Fin 4)).map e.symm.toMonoidHom = commutator X := by
    rw [← hmap, map_map]
    convert map_id (commutator X)
    ext x
    simp
  rw [hback] at hV
  refine ⟨hV, ?_⟩
  have h12 : Nat.card X = 12 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h1 := (commutator X).card_mul_index
  rw [IsKleinFour.card_four, h12] at h1
  omega

theorem gw_commutator_form
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hD : HasDihedralSylowTwo G) :
    Odd (commutator G).index ∧ IsAStarFactor (commutator G) := by
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨hodd, hF, -⟩
  · obtain ⟨hV, h3⟩ := isKleinFour_commutator_of_mulEquiv_alternatingGroup_four e
    refine ⟨?_, Or.inr (Or.inr hV)⟩
    rw [h3]
    decide
  · refine ⟨hodd, ?_⟩
    rcases hF with h7 | hpsl
    · exact Or.inl h7
    · exact Or.inr (Or.inl hpsl)

theorem gw_center_eq_bot
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hD : HasDihedralSylowTwo G) : center G = ⊥ := by
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨-, -, hC⟩
  · exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp))
  · rw [eq_bot_iff, ← hC]
    intro z hz
    rw [mem_centralizer_iff]
    intro g _
    exact (mem_center_iff.mp hz g)

theorem gw_commutator_isL2OrA7_seven
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hD : HasDihedralSylowTwo G) (h8 : 8 ∣ Nat.card G) : IsL2OrA7 (commutator G) 7 := by
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨hodd, hF, -⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h8
    exact absurd h8 (by decide)
  · rcases hF with h7 | ⟨p, k, hp, hp2, h5, ⟨e⟩⟩
    · exact Or.inl h7
    · refine Or.inr ⟨p, k, hp, hp2, ?_, ⟨e⟩⟩
      by_contra hlt
      have hq5 : p ^ k = 5 := by
        have : Odd p := hp.out.odd_of_ne_two hp2
        have : Odd (p ^ k) := this.pow
        obtain ⟨m, hm⟩ := this
        omega
      have hk : k ≠ 0 := by rintro rfl; simp at hq5
      have hcard : Nat.card (commutator G) = 60 := by
        rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
          ⟨p, k, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk,
            GaloisField.card p k hk⟩, GaloisField.card p k hk, hq5]
        norm_num
      have h1 := (commutator G).card_mul_index
      rw [hcard] at h1
      rw [← h1] at h8
      obtain ⟨m, hm⟩ := hodd
      rw [hm] at h8
      omega

theorem isL2OrA7_commutator_of_subgroup {X : Type*} [Group X] (H : Subgroup X) {q : ℕ}
    (h : IsL2OrA7 (commutator H) q) : IsL2OrA7 (⁅H, H⁆ : Subgroup X) q :=
  isL2OrA7_of_mulEquiv ((MulEquiv.subgroupCongr (map_subtype_commutator H)).symm.trans
    ((commutator H).equivMapOfInjective H.subtype H.subtype_injective).symm) h

theorem isAStarFactor_commutator_of_subgroup {X : Type*} [Group X] (H : Subgroup X)
    (h : IsAStarFactor (commutator H)) : IsAStarFactor (⁅H, H⁆ : Subgroup X) := by
  let e : (⁅H, H⁆ : Subgroup X) ≃* commutator H :=
    (MulEquiv.subgroupCongr (map_subtype_commutator H)).symm.trans
      ((commutator H).equivMapOfInjective H.subtype H.subtype_injective).symm
  rcases h with ⟨⟨f⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨f⟩⟩ | hV
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr (Or.inl ⟨p, k, hp, hp2, hq, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr (IsKleinFour.mk (by rw [Nat.card_congr e.toEquiv]; exact hV.card_four)
      (by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hV.exponent_two)))

end CFSG.GH72
