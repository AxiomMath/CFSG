module

public import CFSG.CGT.PushingUpLit.T2KR.P53Pair
public import CFSG.CGT.PushingUpLit.T2K.SixD
public import CFSG.CGT.PushingUpLit.T2KR.P53Choice

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.Nine CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Glue
open CFSG.CGT.PushingUpLit.T2K (T2Hyp)
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G]

theorem characteristicCoreStar_le_of_unique [Finite G] {T M : Subgroup G} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → T ≤ N → N = M) :
    characteristicCoreStar T ≤ M := by
  have key : ∀ B : Subgroup G, B ≠ ⊥ → IsPGroup 2 B → T ≤ Subgroup.normalizer (B : Set G) →
      Subgroup.normalizer (B : Set G) ≤ M := by
    intro B hB1 hB2 hTB
    obtain ⟨N, hle, hN⟩ := exists_isMaximalTwoLocal_ge (isPLocal_normalizer_of_isPGroup hB2 hB1)
    exact hle.trans (hu N hN (hTB.trans hle)).le
  refine characteristicCoreStar_le ?_ ?_
  · have hZ1 := omegaOneCenterIn_ne_bot hT hT1
    have hZ2 : IsPGroup 2 (omegaOneCenterIn T) := hT.to_le (omegaOneCenterIn_le T)
    exact (Subgroup.centralizer_le_normalizer _).trans
      (key _ hZ1 hZ2 ((le_centralizer_of_le_omegaOneCenterIn le_rfl).trans
        (Subgroup.centralizer_le_normalizer _)))
  · intro B hB1 hBS hBc
    have hB2 : IsPGroup 2 B := hT.to_le (hBS.trans (pushingUpS_le T))
    refine key B hB1 hB2 ?_
    exact Subgroup.le_normalizer.trans
      ((normalizer_le_normalizer_of_characteristic' (pushingUpS_le T)
        (characteristic_pushingUpS T)).trans
        (normalizer_le_normalizer_of_characteristic' hBS hBc))

@[expose] def BenderSuzukiStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X),
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M → CFSG.Open.fusionIsBenderGroup X

variable [Finite G]

theorem _root_.CFSG.CGT.PushingUpLit.T2K.T2Hyp.not_isStronglyEmbeddedOrder {L M : Subgroup G}
    {n : ℕ} (h : T2Hyp G L M n) (hBS : BenderSuzukiStatement) :
    ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  intro hSE
  have := h.simple
  have hB := hBS G M hSE
  obtain ⟨P, hP1, hP2, hMP⟩ := h.maxLocal.1
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hMP ▸ h.le
  have hLns := h.natBlock.not_isSolvable
  obtain ⟨q, k, hq⟩ :=
    CFSG.QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup hB
  exact CFSG.QuasithinUnique.Lin2.false_of_benderBorel hq hP1 hP2 hLP hLns

theorem exists_sylow_of_isSylowOf_top {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hT2.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

theorem exists_setup (hbhs : BHSLocalCStar) (h616 : AschbacherSixSixteenNormal)
    (hBS : BenderSuzukiStatement) {L M : Subgroup G} {n : ℕ} (h : T2Hyp G L M n) (T : Sylow 2 G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ∃ I H S Y L' : Subgroup G, NineChoice M I H S ∧ NinePair M I Y L' ∧
      (∀ Y' L'' : Subgroup G, NinePair M I Y' L'' → Nat.card Y' ≤ Nat.card Y) ∧ InClassXG Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 : (T : Subgroup G) ≠ ⊥ := by
    intro hbot
    have h16 := h.sixteen_dvd_card
    have hcard : Nat.card (T : Subgroup G) = 2 ^ (Nat.card G).factorization 2 := by
      have := Sylow.card_eq_multiplicity T
      simpa using this
    rw [hbot, Subgroup.card_bot] at hcard
    have h1 : (Nat.card G).factorization 2 = 0 := by
      have : 2 ^ (Nat.card G).factorization 2 = 1 := hcard.symm
      exact (Nat.pow_eq_one.1 this).resolve_left (by norm_num)
    have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans (by norm_num : 2 ∣ 16) h16
    have h3 : (Nat.card G).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos.ne') h2).ne'
    exact h3 h1
  have hCM : characteristicCoreStar (T : Subgroup G) ≤ M :=
    characteristicCoreStar_le_of_unique T.isPGroup' hT1 hu
  obtain ⟨I, H, S, hc⟩ := exists_nineChoice_of_le h.charTwo T hCM h.M_ne_top
    (h.not_isStronglyEmbeddedOrder hBS)
  obtain ⟨Y₀, hY₀⟩ := exists_base_pair_of_nineChoice hbhs h.charTwo hc
  obtain ⟨Y, L', hY, hmax⟩ := Glue.exists_extremal_pair M I ⟨Y₀, H, hY₀⟩
  exact ⟨I, H, S, Y, L', hc, hY, hmax,
    inClassXG_of_maximal_pair_normal_of_nineChoice h616 h.kproper h.charTwo hc hY hmax⟩

end CFSG.CGT.PushingUpLit.T2KR.P53
