module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Single
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.commutative_barM_of_two_weakSBlocks_of_pRank_le_one
    (h : AGLPair 3 M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L₁ L₂ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (ho₁ : ∀ u ∈ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L₁ ⊔ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (ho₂ : ∀ u ∈ Subgroup.normalizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L₂ ⊔ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hy₁ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy₂ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hP₁ : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) → IsPGroup 3 T →
        IsElemAbelian 3 T)
    (hr₂ : Open.pRank 3 L₂ ≤ 1) :
    ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set S := pCoreOf 2 H with hS
  set L₁b := barM M L₁ with hL₁b
  set L₂b := barM M L₂ with hL₂b
  set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
  set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₂
  set Rb := barM M R with hRb
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  have hBH : Open.pRank 3 Bb ≤ 2 := (h.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hRB : Rb ≤ Bb := barM_mono fun r hr => by
    rw [h.normalizer_twoCore_H]
    exact h.le_H hr
  have hRp : IsPGroup 3 Rb := isPGroup_barM h.isPGroup_R
  have hR3 : ∀ x ∈ Rb, IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
    hRp.to_le (Subgroup.zpowers_le.mpr hx)
  have hRN₁ : Rb ≤ Subgroup.normalizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun x hx =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL₁ (hR3 x hx)
  have hRN₂ : Rb ≤ Subgroup.normalizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun x hx =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL₂ (hR3 x hx)
  have hRL₁ : Rb ≤ L₁b ⊔ C₁ := fun x hx => ho₁ x (hRN₁ hx) (hR3 x hx)
  have hRL₂ : Rb ≤ L₂b ⊔ C₂ := fun x hx => ho₂ x (hRN₂ hx) (hR3 x hx)
  have hRC₂n : Rb ≤ Subgroup.normalizer (C₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun r hr =>
    normalizer_le_normalizer_centralizer_res3 L₂b (hRN₂ hr)
  have hL₁C₁n : L₁b ≤ Subgroup.normalizer (C₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun l hl =>
    normalizer_le_normalizer_centralizer_res3 L₁b (Subgroup.le_normalizer hl)
  have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    hL₁.component hL₂.component hne
  have hL₁C₂ : L₁b ≤ C₂ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp
  obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ := hy₁
  obtain ⟨y₂, hy₂P, hy₂3, hy₂C⟩ := hy₂
  have hy₁B : y₁ ∈ Bb := barM_mono inf_le_left hy₁P
  have hy₂B : y₂ ∈ Bb := barM_mono inf_le_left hy₂P
  have hy₁L : y₁ ∈ L₁b := barM_mono inf_le_right hy₁P
  have hy₂L : y₂ ∈ L₂b := barM_mono inf_le_right hy₂P
  have hFB : C₁ ⊓ C₂ ≤ Bb := fun c hc =>
    h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' => by
      rcases hk2 L' hL' with he | he
      · exact he.symm ▸ hc.1
      · exact he.symm ▸ hc.2
  have hFrank : Open.pRank 3 (C₁ ⊓ C₂) = 0 := by
    set F := C₁ ⊓ C₂ with hF
    have hFC₁ : F ≤ C₁ := inf_le_left
    have hFC₂ : F ≤ C₂ := inf_le_right
    have hy₁F : y₁ ∈ Subgroup.centralizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hFC₁ hx) y₁ hy₁L).symm
    have hs1 := succ_pRank_le_of_commute (q := 3) (B := F ⊔ Subgroup.zpowers y₁) le_sup_left
      hFC₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)) hy₁3 hy₁C hy₁F
    have hA'C₂ : F ⊔ Subgroup.zpowers y₁ ≤ C₂ :=
      sup_le hFC₂ (Subgroup.zpowers_le.mpr (hL₁C₂ hy₁L))
    have hy₂A' : y₂ ∈ Subgroup.centralizer ((F ⊔ Subgroup.zpowers y₁ : Subgroup _) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hA'C₂ hx) y₂ hy₂L).symm
    have hA'B : F ⊔ Subgroup.zpowers y₁ ≤ Bb :=
      sup_le hFB (Subgroup.zpowers_le.mpr hy₁B)
    have hs2 := succ_pRank_le_of_commute (q := 3) hA'B hA'C₂ hy₂B hy₂3 hy₂C hy₂A'
    omega
  have hC12 : ¬ 3 ∣ Nat.card (C₁ ⊓ C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hd => by
    have := one_le_pRank_of_dvd h3 hd
    omega
  set W := Rb ⊓ C₂ with hW
  have hWL₁ : W ≤ L₁b := by
    intro w hw
    have hw' : w ∈ ((L₁b ⊔ C₁ : Subgroup _) : Set _) := hRL₁ hw.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L₁b C₁ hL₁C₁n] at hw'
    obtain ⟨l, hl, c, hc, rfl⟩ := hw'
    have hcC₂ : c ∈ C₂ := by
      have : c = l⁻¹ * (l * c) := by group
      rw [this]
      exact C₂.mul_mem (C₂.inv_mem (hL₁C₂ hl)) hw.2
    set N := Nat.card (C₁ ⊓ C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) with hN
    have hcN : c ^ N = 1 := by
      have := pow_card_eq_one' (G := (C₁ ⊓ C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)))
        (x := ⟨c, hc, hcC₂⟩)
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hRp ⟨l * c, hw.1⟩
    have hwk : (l * c) ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hcomm : Commute l c := (Subgroup.mem_centralizer_iff.mp hc l hl)
    have hpowN : (l * c) ^ N = l ^ N := by rw [hcomm.mul_pow, hcN, mul_one]
    have hcop : Nat.Coprime N (orderOf (l * c)) := by
      have h1 : orderOf (l * c) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hwk
      have h2 : Nat.Coprime (3 ^ k) N :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h3).mpr hC12)
      exact (Nat.Coprime.coprime_dvd_left h1 h2).symm
    have hmem : l * c ∈ Subgroup.zpowers ((l * c) ^ N) := mem_zpowers_pow_iff.mpr hcop
    rw [hpowN] at hmem
    exact (Subgroup.zpowers_le.mpr (L₁b.pow_mem hl N)) hmem
  have hWB : W ≤ Bb := inf_le_left.trans hRB
  have hWC₂ : W ≤ C₂ := inf_le_right
  have hWP : W ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L₁) := fun w hw =>
    h.barM_inf_barM_le ⟨hWL₁ hw, hWB hw⟩
  have hW3 : IsPGroup 3 W := hRp.to_le inf_le_left
  have hWel : IsElemAbelian 3 W := hP₁ W hWP hW3
  have hWr : Open.pRank 3 W ≤ 1 := by
    have hy₂W : y₂ ∈ Subgroup.centralizer (W : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hWC₂ ht) y₂ hy₂L).symm
    have hsucc := succ_pRank_le_of_commute (q := 3) hWB hWC₂ hy₂B hy₂3 hy₂C hy₂W
    omega
  have hWcard : Nat.card W ∣ 3 := card_dvd_three_of_isElemAbelian_of_pRank_le_one hWel hW3 hWr
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := commutative_of_isPGroup_of_pRank_le_one hW3 hWr
  have hWcentral : ∀ w ∈ W, ∀ x ∈ Rb, x * w = w * x :=
    commute_of_normal_card_dvd_three hRp inf_le_left hWcard fun x hx w hw =>
      ⟨Rb.mul_mem (Rb.mul_mem hx hw.1) (Rb.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hRC₂n hx) w).mp hw.2⟩
  have hL₂1 : Open.pRank 3 L₂b ≤ 1 := by
    rw [hL₂b, pRank_barM_eq h3 (by decide) M L₂ hL₂.le]
    exact hr₂
  obtain ⟨g, hgR, hgsup⟩ := exists_zpowers_sup_centralizer hRN₂ hRL₂ hZ₂ hRp hL₂1
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (C₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.zpowers_le.mpr (hRC₂n hgR)
  have hdec : ∀ x ∈ Rb, ∃ k : ℤ, ∃ w ∈ W, x = g ^ k * w := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers g ⊔ C₂ : Subgroup _) : Set _) := hgsup hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers g) C₂ hgN] at hx'
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨k, c, ⟨?_, hc⟩, rfl⟩
    have : c = (g ^ k)⁻¹ * (g ^ k * c) := by group
    rw [this]
    exact Rb.mul_mem (Rb.inv_mem (Rb.zpow_mem hgR k)) hx
  intro x hx x' hx'
  obtain ⟨k, w, hw, rfl⟩ := hdec x hx
  obtain ⟨k', w', hw', rfl⟩ := hdec x' hx'
  have hgkw : ∀ (m : ℤ), ∀ v ∈ W, g ^ m * v = v * g ^ m := fun m v hv =>
    (Commute.zpow_left (show Commute g v from hWcentral v hv g hgR) m).eq
  have hgg : g ^ k * g ^ k' = g ^ k' * g ^ k := (Commute.zpow_zpow_self g k k').eq
  have e1 : g ^ k * w * (g ^ k' * w') = g ^ k * g ^ k' * (w * w') := by
    calc g ^ k * w * (g ^ k' * w') = g ^ k * (w * g ^ k') * w' := by group
      _ = g ^ k * (g ^ k' * w) * w' := by rw [← hgkw k' w hw]
      _ = g ^ k * g ^ k' * (w * w') := by group
  have e2 : g ^ k' * w' * (g ^ k * w) = g ^ k' * g ^ k * (w' * w) := by
    calc g ^ k' * w' * (g ^ k * w) = g ^ k' * (w' * g ^ k) * w := by group
      _ = g ^ k' * (g ^ k * w') * w := by rw [← hgkw k w' hw']
      _ = g ^ k' * g ^ k * (w' * w) := by group
  rw [e1, e2, hgg, hWcomm w hw w' hw']

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.commutative_barM (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2) (hM3' : Open.pRank 3 M ≤ 3)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    (hout : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        IsPGroup 3 (Subgroup.zpowers u) →
          u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hP : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → IsPGroup 3 T →
          IsElemAbelian 3 T) :
    ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set S := pCoreOf 2 H with hS
  obtain ⟨L₁, hL₁⟩ := h.exists_weakSBlock h84 hD2
  by_cases hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L₁
  · exact h.commutative_barM_of_one_weakSBlock h84 h86 hD2 hH hthree hL₁ hk1 (hout L₁ hL₁)
      (hy L₁ hL₁) (hP L₁ hL₁)
  · simp only [not_forall] at hk1
    obtain ⟨L₂, hL₂, hne⟩ := hk1
    have hne' : barM M L₁ ≠ barM M L₂ := fun he => hne he.symm
    have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₁ ∨ barM M L' = barM M L₂ := by
      intro L' hL'
      by_contra hcon
      simp only [not_or] at hcon
      refine h.false_of_three_weakSBlock_images hH hthree ![L₁, L₂, L'] (fun i => ?_) ?_
      · fin_cases i
        · exact hL₁
        · exact hL₂
        · exact hL'
      · have h13 : barM M L₁ ≠ barM M L' := fun he => hcon.1 he.symm
        have h23 : barM M L₂ ≠ barM M L' := fun he => hcon.2 he.symm
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
        all_goals first
          | exact absurd hij hne' | exact absurd hij.symm hne' | exact absurd hij h13
          | exact absurd hij.symm h13 | exact absurd hij h23 | exact absurd hij.symm h23
    have hk2' : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₂ ∨ barM M L' = barM M L₁ := fun L' hL' => (hk2 L' hL').symm
    set L₁b := barM M L₁ with hL₁b
    set L₂b := barM M L₂ with hL₂b
    set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
    set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₂
    have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      hL₁.component hL₂.component hne'
    have hL₂C₁ : L₂b ≤ C₁ := by
      have : ⁅L₂b, L₁b⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomp
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp this
    have hZ₁ : ¬ 3 ∣ Nat.card (L₁b ⊓ C₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hZ =>
      h.false_of_two_weakSBlocks_of_center h84 h86 hD2 hH hL₁ hL₂ hne' hk2 hZ (hy L₁ hL₁)
        (hy L₂ hL₂)
    have hZ₂ : ¬ 3 ∣ Nat.card (L₂b ⊓ C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hZ =>
      h.false_of_two_weakSBlocks_of_center h84 h86 hD2 hH hL₂ hL₁ hne'.symm hk2' hZ (hy L₂ hL₂)
        (hy L₁ hL₁)
    have hcommL : ∀ x ∈ L₁b, ∀ y ∈ L₂b, x * y = y * x := fun x hx y hy' =>
      Subgroup.mem_centralizer_iff.mp (hL₂C₁ hy') x hx
    have hcop12 : Nat.Coprime 3 (Nat.card (L₁b ⊓ L₂b : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
      rw [Nat.Prime.coprime_iff_not_dvd h3]
      intro hd
      apply hZ₁
      exact hd.trans (Subgroup.card_dvd_of_le fun x hx => ⟨hx.1, hL₂C₁ hx.2⟩)
    have hs12 : Open.pRank 3 L₁b + Open.pRank 3 L₂b ≤ Open.pRank 3 (L₁b ⊔ L₂b) :=
      pRank_add_le_pRank_sup_of_coprime h3 hcommL hcop12
    have hL12M : L₁b ⊔ L₂b ≤ barM M M := sup_le (barM_mono hL₁.le) (barM_mono hL₂.le)
    have hpM : Open.pRank 3 (barM M M) = Open.pRank 3 M := pRank_barM_eq h3 (by decide) M M le_rfl
    have hm : Open.pRank 3 (L₁b ⊔ L₂b) ≤ Open.pRank 3 (barM M M) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hL12M
    have hL₁r : Open.pRank 3 L₁b = Open.pRank 3 L₁ := pRank_barM_eq h3 (by decide) M L₁ hL₁.le
    have hL₂r : Open.pRank 3 L₂b = Open.pRank 3 L₂ := pRank_barM_eq h3 (by decide) M L₂ hL₂.le
    have hsum : Open.pRank 3 L₁ + Open.pRank 3 L₂ ≤ 3 := by omega
    by_cases hr₂ : Open.pRank 3 L₂ ≤ 1
    · exact h.commutative_barM_of_two_weakSBlocks_of_pRank_le_one h84 h86 hD2 hH hthree hL₁ hL₂
        hne' hk2 (hout L₁ hL₁) (hout L₂ hL₂) hZ₂ (hy L₁ hL₁) (hy L₂ hL₂) (hP L₁ hL₁) hr₂
    · exact h.commutative_barM_of_two_weakSBlocks_of_pRank_le_one h84 h86 hD2 hH hthree hL₂ hL₁
        hne'.symm hk2' (hout L₂ hL₂) (hout L₁ hL₁) hZ₁ (hy L₂ hL₂) (hy L₁ hL₁) (hP L₂ hL₂)
        (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC
