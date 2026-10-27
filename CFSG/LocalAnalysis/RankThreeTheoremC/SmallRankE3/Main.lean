module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Rank2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Finish
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem main65_exists_commutative {M B F : Subgroup G} [Group.IsSolvable F]
    (hF1 : F ≠ ⊥) (hBF : B ≤ normalizer (F : Set G)) (hFnot : ¬ normalizer (F : Set G) ≤ M) :
    ∃ K : Subgroup G, K ≤ F ∧ K ≠ ⊥ ∧ B ≤ normalizer (K : Set G) ∧
      ¬ normalizer (K : Set G) ≤ M ∧ IsMulCommutative K := by
  obtain ⟨K, ⟨hKF, hK1, hBK, hKnot⟩, hmin⟩ :=
    (measure (fun K : Subgroup G => Nat.card K)).wf.has_min
      {K : Subgroup G | K ≤ F ∧ K ≠ ⊥ ∧ B ≤ normalizer (K : Set G) ∧
        ¬ normalizer (K : Set G) ≤ M} ⟨F, le_rfl, hF1, hBF, hFnot⟩
  refine ⟨K, hKF, hK1, hBK, hKnot, ?_⟩
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKF)
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK1
  refine (commutator_eq_bot_iff ↥K).1 ?_
  by_contra hne
  have hlt : _root_.commutator ↥K < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
  have hN : normalizer (K : Set G) ≤
      normalizer (((_root_.commutator ↥K).map K.subtype : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (_root_.commutator ↥K)
  have hne' : (_root_.commutator ↥K).map K.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
  refine hmin _ ⟨(Subgroup.map_subtype_le _).trans hKF, hne', hBK.trans hN,
    fun hle => hKnot (hN.trans hle)⟩ ?_
  show Nat.card ((_root_.commutator ↥K).map K.subtype) < Nat.card K
  rw [Subgroup.card_subtype]
  calc Nat.card (_root_.commutator ↥K) < Nat.card (⊤ : Subgroup ↥K) :=
        Subgroup.card_lt_of_lt hlt
    _ = Nat.card K := Subgroup.card_top

theorem exists_pGroup_counterexample {M : Subgroup G} {x z : G} {F : Subgroup G} (hFM : F ≤ M)
    (hF1 : F ≠ ⊥) (hF6 : Nat.Coprime (Nat.card F) 6)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hFnot : ¬ normalizer (F : Set G) ≤ M) :
    ∃ f : ℕ, f.Prime ∧ 5 ≤ f ∧ ∃ F₁ : Subgroup G, IsPGroup f F₁ ∧ F₁ ≤ F ∧ F₁ ≠ ⊥ ∧
      zpowers x ⊔ zpowers z ≤ normalizer (F₁ : Set G) ∧ ¬ normalizer (F₁ : Set G) ≤ M := by
  have hodd : Odd (Nat.card F) := by
    have h2 : Nat.Coprime (Nat.card F) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hF6
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h22 : 2 ∣ Nat.card F := even_iff_two_dvd.mp hne
    exact absurd (Nat.Coprime.eq_one_of_dvd h2.symm h22) (by norm_num)
  have : Group.IsSolvable ↥F := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨K, hKF, hK1, hBK, hKnot, hcomm⟩ :=
    main65_exists_commutative (M := M) (B := zpowers x ⊔ zpowers z) hF1 hBF hFnot
  obtain ⟨f, hf, hfK⟩ := Nat.exists_prime_and_dvd
    (show Nat.card K ≠ 1 from fun h1 => hK1 (Subgroup.eq_bot_of_card_eq K h1))
  have : Fact f.Prime := ⟨hf⟩
  have hf6 : ¬ f ∣ 6 :=
    (Nat.Prime.coprime_iff_not_dvd hf).1
      (Nat.Coprime.coprime_dvd_left (hfK.trans (Subgroup.card_dvd_of_le hKF)) hF6)
  have hf5 : 5 ≤ f := by
    by_contra hlt
    have h2 := hf.two_le
    interval_cases f
    · exact hf6 (by norm_num)
    · exact hf6 (by norm_num)
    · exact absurd hf (by norm_num)
  obtain ⟨S⟩ : Nonempty (Sylow f ↥K) := inferInstance
  have : IsMulCommutative ↥K := hcomm
  have hSc : (S : Subgroup ↥K).Characteristic := Sylow.characteristic_of_normal S inferInstance
  have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (S : Subgroup ↥K)
  have hS1 : (S : Subgroup ↥K) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (S : Subgroup ↥K) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [S.card_eq_multiplicity] at h1
    have hk : 0 < (Nat.card ↥K).factorization f :=
      hf.factorization_pos_of_dvd Nat.card_pos.ne' hfK
    exact (Nat.one_lt_pow hk.ne' hf.one_lt).ne' h1
  refine ⟨f, hf, hf5, (S : Subgroup ↥K).map K.subtype, S.isPGroup'.map K.subtype,
    (Subgroup.map_subtype_le _).trans hKF, ?_, hBK.trans hN, fun hle => hKnot (hN.trans hle)⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]

private theorem main65_exists_max {C : Subgroup G → Prop} (hne : ∃ F, C F) :
    ∃ F, C F ∧ ∀ F', C F' → Nat.card F' ≤ Nat.card F := by
  obtain ⟨F, hF, hmin⟩ := (measure (fun F : Subgroup G => Nat.card G - Nat.card F)).wf.has_min
    {F | C F} hne
  refine ⟨F, hF, fun F' hF' => ?_⟩
  have h1 : ¬ Nat.card G - Nat.card F' < Nat.card G - Nat.card F := hmin F' hF'
  have h2 := Subgroup.card_le_card_group F
  have h3 := Subgroup.card_le_card_group F'
  omega

theorem prop65Alpha_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure) :
    GL83SmallRankProp65Alpha G := by
  intro P M hsit hcon x z hx hz F₀ hF₀M hF₀1 hF₀6 hBF₀
  by_contra hF₀not
  have h : Setup65A G P M x z := ⟨hS, hU0, hsit, hcon, hx, hz⟩
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  obtain ⟨f₀, hf₀, hf₀5, F₁, hF₁p, hF₁F, hF₁1, hBF₁, hF₁not⟩ :=
    exists_pGroup_counterexample hF₀M hF₀1 hF₀6 hBF₀ hF₀not
  obtain ⟨F, ⟨⟨f, hf, hf5, hFp⟩, hFM, hF1, hBF, hHM⟩, hmax⟩ := main65_exists_max
    (C := fun F : Subgroup G => (∃ f : ℕ, f.Prime ∧ 5 ≤ f ∧ IsPGroup f F) ∧ F ≤ M ∧ F ≠ ⊥ ∧
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) ∧ ¬ normalizer (F : Set G) ≤ M)
    ⟨F₁, ⟨f₀, hf₀, hf₀5, hF₁p⟩, hF₁F.trans hF₀M, hF₁1, hBF₁, hF₁not⟩
  have hf3 : f ≠ 3 := by omega
  have hF3 : ¬ 3 ∣ Nat.card F := by
    have : Fact f.Prime := ⟨hf⟩
    obtain ⟨k, hk⟩ := hFp.exists_card_eq
    rw [hk]
    intro h3
    exact hf3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hf).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hFD : F ≤ rankThreePrimeCore 3 M := le_primeCore_of_normalizes h hFM hF3 hBF
  obtain ⟨Fs, hFFs, hFsD, hFsp, hsyl, hBFs⟩ := exists_invariant_sylow_ge h hf hf3 hFp hFD hBF
  rcases hFFs.eq_or_lt with heq | hlt
  · subst heq
    exact false_of_sylow_normalizer h hK2 hf hf5 hFp hF1 hFD hsyl hBF hHM
  · have hr2 : 2 ≤ CFSG.Open.pRank 3 (normalizer (F : Set G)) :=
      le_pRank_of_isElemAbelian Nat.prime_three hBF hpl.isElemAbelian hpl.card_eq
    obtain ⟨E, hFE, hEp, hBE, hEO, hOM⟩ : ∃ E : Subgroup G, F < E ∧ IsPGroup f E ∧
        zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) ∧
        E ≤ rankThreePrimeCore 3 (normalizer (F : Set G)) ∧
        rankThreePrimeCore 3 (normalizer (F : Set G)) ≤ M := by
      by_cases hr3 : 3 ≤ CFSG.Open.pRank 3 (normalizer (F : Set G))
      · exact rank_three_enlarge h hK2 hf hf5 hFp hF1 hBF hHM hFsp hFsD hBFs hlt hr3
      · obtain ⟨R, hBR, hRM, hRFs, hR3, -, -, hRrank⟩ :=
          exists_sylow_three_normalizing h hf hf3 hFsD hFsp hsyl hBFs
        exact rank_two_enlarge h hK1 hf hf5 hFp hF1 hBF hHM hFsp hFsD hsyl hBFs hlt hR3 hRM hBR
          hRFs hRrank (by omega)
    refine hHM (normalizer_le_of_enlarged hf hf3 hB3 hFp ?_ hBF hOM hFE hEp hBE hEO)
    intro F' hF'M hF'p hF'1 hBF' hcard
    by_contra hnot
    exact absurd (hmax F' ⟨⟨f, hf, hf5, hF'p⟩, hF'M, hF'1, hBF', hnot⟩) (not_le.mpr hcard)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
