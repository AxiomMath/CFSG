
module

public import CFSG.Quasithin.Background.C1GNC129

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.SectionRank
open scoped commutatorElement

namespace L238

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def C127StatementCat : Prop :=
  ∀ X T P K : Subgroup G, CharTwo X → IsSylowTwoOf T X → IsSQTKCat ↥X →
    P ∈ uFamHat X T → IsChi0Block P K → ¬ P ≤ cgsIn X T → ⁅K, thompsonJ T⁆ = K →
    P = T ⊔ conjClosure K T →
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n)

@[expose] def C123TwoCgsStatement : Prop :=
  ∀ T Y L : Subgroup G, IsSylowTwoOf T Y → CharTwo Y → IsKGroupCat ↥Y → L ∈ cComp Y →
    (∀ y ∈ Y, ∃ l ∈ L, ∃ r ∈ T, y = l * r) → IsExcA7Block L → Y ≤ cgsIn Y T

@[expose] def C129A7StatementCat : Prop :=
  ∀ X T M L : Subgroup G, CharTwo X → IsSQTKCat X → IsSylowTwoOf T X → cgsIn X T ≤ M → M ≤ X →
    IsBlock2 X L → IsAltType L 7 → ⁅L, thompsonJ T⁆ = L → ¬ L ≤ M → False

omit [Finite G] in
theorem c123TwoCgs_of_gn {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (h : C123TwoStatement C₁ C₂) : C123TwoCgsStatement (G := G) := by
  intro T Y L hT hY _hKY hL hprod hexc
  have hT0 : T ≠ ⊥ := by
    intro hbot
    obtain ⟨-, ⟨α, hα, -⟩, -⟩ := hexc
    have h1 : Nat.card (alternatingGroup (Fin 7)) ∣ Nat.card L :=
      Subgroup.card_dvd_of_surjective hα
    have h2 : 2 ∣ Nat.card (alternatingGroup (Fin 7)) := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have h3 : Nat.card L ∣ Nat.card Y := Subgroup.card_dvd_of_le (le_of_mem_cComp hL)
    have h0 : ¬ 2 ∣ T.relIndex Y := hT.2.2
    apply h0
    rw [hbot, Subgroup.relIndex_bot_left]
    exact h2.trans (h1.trans h3)
  have hY' := h T T Y L hT.2.1 (C1GN.baum_le T) le_rfl hT hY hL hprod hexc
  exact hY'.le.trans (C1GN.le_cgsIn_of_isGNChoice (X := Y) hC hT.2.1 hT0)

end Statements

section Rank

variable {G : Type} [Group G] [Finite G]

theorem rank_le_of_isSQTKCat {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2 :=
  isStronglyQuasithin_iff.mp hX.1 q hq hq2

theorem three_blocks_false_cat {X A B C : Subgroup G}
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2) (hAX : A ≤ X) (hBX : B ≤ X) (hCX : C ≤ X)
    (h2 : CharTwo A ∧ CharTwo B ∧ CharTwo C)
    (h3 : 3 ∣ Nat.card A ∧ 3 ∣ Nat.card B ∧ 3 ∣ Nat.card C)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hc : ⁅A, B⁆ = ⊥ ∧ ⁅A, C⁆ = ⊥ ∧ ⁅B, C⁆ = ⊥) : False := by
  classical
  obtain ⟨hcAB, hcAC, hcBC⟩ := hc
  have hcard : ({A, B, C} : Finset (Subgroup G)).card = 3 :=
    Finset.card_eq_three.2 ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  obtain ⟨E, hEle, hE, hEcard⟩ := C1GN.exists_elemAbelian_three_pow (fun K : Subgroup G => K)
    {A, B, C}
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      exacts [h2.1, h2.2.1, h2.2.2])
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      exacts [h3.1, h3.2.1, h3.2.2])
    (by
      intro i hi j hj hij
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hij
        | assumption
        | (rwa [Subgroup.commutator_comm]))
  have hEX : E ≤ X := by
    refine hEle.trans (iSup₂_le fun i hi => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    exacts [hAX, hBX, hCX]
  rw [hcard] at hEcard
  have hrank : 3 ≤ CFSG.Open.pRank 3 X := le_pRank Nat.prime_three hEX hE hEcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
    pRank_top_subtype (p := 3) X
  omega

theorem isChi0Block_of_isChiBlock_cat (hA7 : C129A7StatementCat (G := G)) {X T M L : Subgroup G}
    (hX : CharTwo X) (hSQ : IsSQTKCat X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hMX : M ≤ X) (hL : IsChiBlock X L) (hLJ : ⁅L, thompsonJ T⁆ = L) (hLM : ¬ L ≤ M) :
    IsChi0Block X L := by
  obtain ⟨hblock, htype⟩ := hL
  refine ⟨hblock, ?_⟩
  rcases htype with h | ⟨m, hm, hm3, hAlt⟩
  · exact Or.inl h
  · obtain ⟨k, rfl⟩ := hm
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
    rcases hcases with rfl | rfl | rfl | hk
    · exact Or.inr (Or.inl hAlt)
    · exact Or.inr (Or.inr hAlt)
    · exact (hA7 X T M L hX hSQ hT hcgs hMX hblock hAlt hLJ hLM).elim
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 : 3 ≤ CFSG.Open.pRank 3 L := C1GN.three_le_pRank_of_isAltType (by omega) hAlt
      have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X :=
        CFSG.SectionRank.pRank_mono (by norm_num) hblock.2.1
      have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
        rank_le_of_isSQTKCat hSQ Nat.prime_three (by norm_num)
      have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
        pRank_top_subtype (p := 3) X
      omega

end Rank

section Alt7

open CFSG.Quasithin.A320

theorem normal_of_pRank_gt_one_cat {H : Type} [Group H] [Finite H]
    (hrk : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) ≤ 2)
    (h38 : A38Part3 (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 1 < CFSG.Open.pRank p L) : L.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hLbar := A318.mem_cComp_quotient hL
  have hrank' : 2 ≤ CFSG.Open.pRank p (L.map π) :=
    (pRank_le_pRank_map hp2 π hker L).trans' hrank
  have hLbarN : (L.map π).Normal := by
    rcases (h38 _ hLbar).1 with h | ⟨-, t, -, hcomm, hinter, -⟩
    · exact h
    · exfalso
      obtain ⟨E, hEL, hEel, hEcard⟩ := exists_pRank hp.one_lt (L.map π)
      have hE'el : IsElemAbelian p (E.map (MulAut.conj t).toMonoidHom) :=
        isElemAbelian_map hEel _
      have hE'card : Nat.card (E.map (MulAut.conj t).toMonoidHom) =
          p ^ CFSG.Open.pRank p (L.map π) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hEcard]
      have hmain := pRank_add_le (⊥ : Subgroup (H ⧸ CFSG.pCore 2 H))
        (by simpa [Nat.dvd_one] using hp.ne_one) hEel hE'el
        (fun x hx e he => by
          have : ⁅x, e⁆ ∈ ⁅L.map π, (L.map π).map (MulAut.conj t).toMonoidHom⁆ :=
            Subgroup.commutator_mem_commutator (hEL hx) (Subgroup.map_mono hEL he)
          rwa [hcomm] at this)
        (fun x hx e he hxe => by
          have hxe1 : x * e = 1 := Subgroup.mem_bot.1 hxe
          have hxL : x ∈ L.map π ⊓ (L.map π).map (MulAut.conj t).toMonoidHom := by
            refine ⟨hEL hx, ?_⟩
            have : x = e⁻¹ := eq_inv_of_mul_eq_one_left hxe1
            rw [this]
            exact Subgroup.inv_mem _ (Subgroup.map_mono hEL he)
          rw [hinter, Subgroup.mem_bot] at hxL
          rw [hxL, one_mul] at hxe1
          exact ⟨hxL, hxe1⟩)
        (a := CFSG.Open.pRank p (L.map π)) (b := CFSG.Open.pRank p (L.map π)) hEcard hE'card
      have := hrk p hp hp2
      omega
  have hLN₂ : (L ⊔ CFSG.pCore 2 H).Normal := by
    have := Subgroup.Normal.comap hLbarN π
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  obtain ⟨-, hperf⟩ := cComp_commutator_perfectCore hL (le_top) (isSolvable_pCore_two H)
    Subgroup.le_normalizer_of_normal
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((L ⊔ CFSG.pCore 2 H : Subgroup H) : Set H) :=
    Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top g)
  have hg' := normalizer_le_normalizer_perfectCore _ hg
  rw [hperf] at hg'
  exact (Subgroup.mem_normalizer_iff.1 hg' n).1 hn

theorem rank_quotient_le_of_isSQTKCat {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X) :
    ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) ≤ 2 := fun q hq hq2 =>
  isStronglyQuasithin_iff.mp
    ((isStronglyQuasithin_quotient_two_group_iff (CFSG.pCore 2 X) CFSG.pCore_isPGroup).2 hX.1)
    q hq hq2

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_exceptionalA7_cat {X L : Subgroup G} (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hL : IsBlock2 X L)
    (hexc : IsExcA7Block L) : X ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc : L ∈ cComp X := C1GN.mem_cComp_of_exceptionalA7 hL hexc
  have hL' : L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := subgroupOf_mem_cComp hLc
  have hrank : 1 < CFSG.Open.pRank 3 (L.subgroupOf X) := by
    have e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.2.1
    have h1 := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have h2 := pRank_top_subtype (p := 3) (L.subgroupOf X)
    have h3 := pRank_top_subtype (p := 3) L
    have h4 := C1GN.two_le_pRank_exceptionalA7 hexc
    omega
  have hnorm : (L.subgroupOf X).Normal :=
    normal_of_pRank_gt_one_cat (rank_quotient_le_of_isSQTKCat hSQ) h38 hL' Nat.prime_three
      (by norm_num) hrank
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL.2.1).1 hnorm

omit [Finite G] in
theorem cgsIn_mono_left {Y X S : Subgroup G} (hYX : Y ≤ X) : cgsIn Y S ≤ cgsIn X S :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ hYX

theorem le_of_isExceptionalA7Block_cat (h123 : C123TwoCgsStatement (G := G))
    {X T L M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hL : IsBlock2 X L) (hexc : IsExcA7Block L) : L ≤ M := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) :=
    hT.1.trans (le_normalizer_of_exceptionalA7_cat hSQ h38 hL hexc)
  have hLX : L ≤ X := hL.2.1
  have hYX : L ⊔ T ≤ X := sup_le hLX hT.1
  have hTY : T ≤ L ⊔ T := le_sup_right
  have hnorm : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTN)
  have hsub : IsSubnormal L (L ⊔ T) := A3.subnormal_of_normal le_sup_left hnorm
  have hLc : L ∈ cComp (L ⊔ T) :=
    C1GN.mem_cComp_of_short hL.1 (C1GN.isQuasisimple_of_isExceptionalA7Block hexc) hsub
  have hprod : ∀ y ∈ L ⊔ T, ∃ l ∈ L, ∃ r ∈ T, y = l * r := by
    intro y hy
    have hy' : y ∈ ((L ⊔ T : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTN] at hy'
    obtain ⟨l, hl, r, hr, hlr⟩ := hy'
    exact ⟨l, hl, r, hr, hlr.symm⟩
  have hKY : IsKGroupCat ↥(L ⊔ T) :=
    (hSQ.2.subgroup ((L ⊔ T).subgroupOf X)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYX).symm
  have hY := h123 T (L ⊔ T) L (C1GN.isSylowTwoOf_of_le hT hTY hYX)
    (C1GN.charTwo_of_le hX hT hTY hYX) hKY hLc hprod hexc
  calc L ≤ L ⊔ T := le_sup_left
    _ ≤ cgsIn (L ⊔ T) T := hY
    _ ≤ cgsIn X T := cgsIn_mono_left hYX
    _ ≤ M := hcgs

end Alt7

end L238

end CFSG.QuasithinUnique
