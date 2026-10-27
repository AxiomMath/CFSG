module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTwoNoEnd

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem rank_count_one_weakSBlock (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (ho : ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ∃ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      F ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ IsElemAbelian 3 F ∧
      4 ≤ Open.pRank 3 L + Open.pRank 3 F ∧
      Open.pRank 3 F +
        Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≤ 2 := by
  set S := pCoreOf 2 H
  set Lb := barM M L
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have h3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 M
  set Eb := barM M E
  have hrE : Open.pRank 3 M ≤ Open.pRank 3 E :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 h3 E) ⟨E, le_rfl, hE, hEcard⟩
  have hEb : Open.pRank 3 Eb = Open.pRank 3 E := pRank_barM_eq h3 (by decide) M E hEM
  have hEbel : IsElemAbelian 3 Eb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hE
  have hu3 : ∀ u ∈ Eb, IsPGroup 3 (Subgroup.zpowers u) := fun u hu =>
    CFSG.AGLEmbeddingD2.isPGroup_zpowers_of_pow_eq_one (hEbel.2 u hu)
  have hEN : Eb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun u hu =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL (hu3 u hu)
  have hEL : Eb ≤ Lb ⊔ Cb := fun u hu => ho u (hEN hu) (hu3 u hu)
  have hR1 : Open.pRank 3 Eb ≤ Open.pRank 3 (Eb ⊓ Cb) + Open.pRank 3 Lb :=
    pRank_le_pRank_inf_centralizer_add_pRank h3 hEN hEL hZ
  have hLb : Open.pRank 3 Lb = Open.pRank 3 L := pRank_barM_eq h3 (by decide) M L hL.le
  set F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Eb ⊓ Cb
  have hFel : IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hEbel.2 x hx.1⟩
    refine Subtype.ext ?_
    exact congrArg (Subtype.val : Eb → _)
      (hEbel.1.is_comm.comm ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩ ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩)
  have hFC : F ≤ Cb := inf_le_right
  set N := Subgroup.normalizer (S : Set G)
  have hFK : F ≤ barM M N := fun u hu =>
    h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' => by
      rw [hk1 L' hL']
      exact hFC hu
  set P := barM M (N ⊓ L)
  have hPK : P ≤ barM M N := barM_mono inf_le_left
  have hPL : P ≤ Lb := barM_mono inf_le_right
  have hc : ∀ a ∈ F, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hFC ha) b (hPL hb)).symm
  have hi : Nat.Coprime 3 (Nat.card (F ⊓ P : Subgroup _)) := by
    rw [Nat.Prime.coprime_iff_not_dvd h3]
    intro hdvd
    apply hZ
    exact hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hPL hu.2, hFC hu.1⟩)
  have hs := pRank_add_le_pRank_sup_of_coprime h3 hc hi
  have hsup : F ⊔ P ≤ barM M N := sup_le hFK hPK
  have hK := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsup).trans
    (h.pRank_barM_normalizer_le h3 (by decide))
  refine ⟨F, hFC, hFel, ?_, ?_⟩
  · omega
  · omega

theorem rank_count_two_weakSBlocks (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L₁ L₂ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (ho : ∀ L ∈ ({L₁, L₂} : Set (Subgroup G)),
      ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        IsPGroup 3 (Subgroup.zpowers u) →
          u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ : ∀ L ∈ ({L₁, L₂} : Set (Subgroup G)), ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    4 ≤ Open.pRank 3 L₁ + Open.pRank 3 L₂ ∧
      Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁)) = 1 ∧
      Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂)) = 1 := by
  have hm₁ : L₁ ∈ ({L₁, L₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hm₂ : L₂ ∈ ({L₁, L₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  set L₁b := barM M L₁
  set L₂b := barM M L₂
  set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set K := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    hL₁.component hL₂.component hne
  have hL₁C₂ : L₁b ≤ C₂ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 M
  set Eb := barM M E
  have hrE : Open.pRank 3 M ≤ Open.pRank 3 E :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 h3 E) ⟨E, le_rfl, hE, hEcard⟩
  have hEb : Open.pRank 3 Eb = Open.pRank 3 E := pRank_barM_eq h3 (by decide) M E hEM
  have hEbel : IsElemAbelian 3 Eb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hE
  have hu3 : ∀ u ∈ Eb, IsPGroup 3 (Subgroup.zpowers u) := fun u hu =>
    CFSG.AGLEmbeddingD2.isPGroup_zpowers_of_pow_eq_one (hEbel.2 u hu)
  have hEN₁ : Eb ≤ Subgroup.normalizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun u hu =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL₁ (hu3 u hu)
  have hEN₂ : Eb ≤ Subgroup.normalizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun u hu =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL₂ (hu3 u hu)
  have hEL₁ : Eb ≤ L₁b ⊔ C₁ := fun u hu => ho L₁ hm₁ u (hEN₁ hu) (hu3 u hu)
  have hR₁ : Open.pRank 3 Eb ≤ Open.pRank 3 (Eb ⊓ C₁) + Open.pRank 3 L₁b :=
    pRank_le_pRank_inf_centralizer_add_pRank h3 hEN₁ hEL₁ (hZ L₁ hm₁)
  have hR₂ : Open.pRank 3 (Eb ⊓ C₁) ≤ Open.pRank 3 (Eb ⊓ C₁ ⊓ C₂) + Open.pRank 3 L₂b :=
    pRank_le_pRank_inf_centralizer_add_pRank h3 (inf_le_left.trans hEN₂)
      (fun u hu => ho L₂ hm₂ u (hEN₂ hu.1) (hu3 u hu.1)) (hZ L₂ hm₂)
  have hF0 : Open.pRank 3 (Eb ⊓ C₁ ⊓ C₂) = 0 :=
    pRank_inf_centralizers_eq_zero h h84 h86 hD2 hH hthree hL₁ hL₂ hne hk2 (hZ L₁ hm₁)
      (hZ L₂ hm₂) fun u hu => ⟨hu.1.2, hu.2⟩
  have hL₁b : Open.pRank 3 L₁b = Open.pRank 3 L₁ := pRank_barM_eq h3 (by decide) M L₁ hL₁.le
  have hL₂b : Open.pRank 3 L₂b = Open.pRank 3 L₂ := pRank_barM_eq h3 (by decide) M L₂ hL₂.le
  have hfirst : 4 ≤ Open.pRank 3 L₁ + Open.pRank 3 L₂ := by omega
  set P₁ := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁)
  set P₂ := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂)
  have hP₁L : P₁ ≤ L₁b := barM_mono inf_le_right
  have hP₂L : P₂ ≤ L₂b := barM_mono inf_le_right
  have hP₁K : P₁ ≤ K := barM_mono inf_le_left
  have hP₂K : P₂ ≤ K := barM_mono inf_le_left
  have hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hL₁C₂ (hP₁L ha)) b (hP₂L hb)).symm
  have hi : Nat.Coprime 3 (Nat.card (P₁ ⊓ P₂ : Subgroup _)) := by
    rw [Nat.Prime.coprime_iff_not_dvd h3]
    intro hdvd
    apply hZ L₂ hm₂
    exact hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hP₂L hu.2, hL₁C₂ (hP₁L hu.1)⟩)
  have hs := pRank_add_le_pRank_sup_of_coprime h3 hcomm hi
  have hsup : P₁ ⊔ P₂ ≤ K := sup_le hP₁K hP₂K
  have hK := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsup).trans
    (h.pRank_barM_normalizer_le h3 (by decide))
  have hrk1 : ∀ w : ↥M ⧸ CFSG.pCore 2 ↥M, w ^ 3 = 1 → w ≠ 1 →
      1 ≤ Open.pRank 3 (Subgroup.zpowers w) := fun w hw3 hw1 =>
    CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3
      (by rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1])
  obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ :=
    CFSG.AGLEmbeddingD2.exists_order_three_noncentral hL₁.le (hthree L₁ hL₁) (hZ L₁ hm₁)
  obtain ⟨y₂, hy₂P, hy₂3, hy₂C⟩ :=
    CFSG.AGLEmbeddingD2.exists_order_three_noncentral hL₂.le (hthree L₂ hL₂) (hZ L₂ hm₂)
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁C (h1 ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h1 => hy₂C (h1 ▸ Subgroup.one_mem _)
  have r₁ : 1 ≤ Open.pRank 3 P₁ :=
    (hrk1 y₁ hy₁3 hy₁1).trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3
      (Subgroup.zpowers_le.mpr hy₁P))
  have r₂ : 1 ≤ Open.pRank 3 P₂ :=
    (hrk1 y₂ hy₂3 hy₂1).trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3
      (Subgroup.zpowers_le.mpr hy₂P))
  exact ⟨hfirst, by omega, by omega⟩

end CFSG.AGLEmbeddingD2.McLaughlin
