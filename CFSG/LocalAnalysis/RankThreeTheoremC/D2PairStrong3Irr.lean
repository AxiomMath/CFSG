module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Lift
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IrreducibleOn {X : Type*} [Group X] (N R : Subgroup X) : Prop :=
  ∀ W : Subgroup X, W ≤ R → N ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = R

@[expose] def TransitiveOnNonidentity {X : Type*} [Group X] (N R : Subgroup X) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, x ≠ 1 → y ≠ 1 → ∃ n ∈ N, n * x * n⁻¹ = y

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

omit [Finite G] in
theorem mem_barM_iff {X : Subgroup G} {x : ↥M ⧸ CFSG.pCore 2 ↥M} :
    x ∈ barM M X ↔ ∃ m : ↥M, (m : G) ∈ X ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = x := by
  simp only [barM, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_centralizer_conj_of_mem_normalizer {Y : Type*} [Group Y] {L : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (L : Set Y)) {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hl'
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * l := by group

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.barM_inf_centralizer_eq_bot (h : AGLPair 3 M H R)
    (hH : Open.pRank 3 H = 2)
    (hR2 : 2 ≤ Open.pRank 3 R)
    (hirr : IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R) {L : Subgroup G}
    (hst : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hn⟩ ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    barM M R ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Bb := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) with hBb
  set W : Subgroup G := R ⊓ (Cb.comap mk).map M.subtype with hW
  have hWR : W ≤ R := inf_le_left
  have hmemW : ∀ r : ↥M, (r : G) ∈ R → mk r ∈ Cb → (r : G) ∈ W := fun r hr hc =>
    ⟨hr, r, hc, rfl⟩
  have hWmem : ∀ r : G, r ∈ W → ∃ hr : r ∈ M, mk ⟨r, hr⟩ ∈ Cb := by
    rintro r ⟨-, m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  have key : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ w : G, w ∈ W →
      n * w * n⁻¹ ∈ W := by
    intro n hn w hw
    have hnM : n ∈ M := hn.1.2
    have hst' := hst n hn hnM
    obtain ⟨hwM, hwC⟩ := hWmem w hw
    have hnR : n * w * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn.2 w).mp (hWR hw)
    have hnwM : n * w * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hwM) (M.inv_mem hnM)
    refine hmemW ⟨_, hnwM⟩ hnR ?_
    have e : mk ⟨n * w * n⁻¹, hnwM⟩ = mk ⟨n, hnM⟩ * mk ⟨w, hwM⟩ * (mk ⟨n, hnM⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact mem_centralizer_conj_of_mem_normalizer hst' hwC
  have hWn : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key n hn w, fun hw => ?_⟩
    have hn' : n⁻¹ ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hn
    have := key n⁻¹ hn' _ hw
    simpa [mul_assoc] using this
  obtain ⟨y, hyP, hy3, hyC⟩ := hy
  have hyB : y ∈ Bb := barM_mono inf_le_left hyP
  have hyL : y ∈ Lb := barM_mono inf_le_right hyP
  have hRB : barM M R ≤ Bb := by
    refine barM_mono fun r hr => ?_
    rw [h.normalizer_twoCore_H]
    exact h.le_H hr
  have hBH : Open.pRank 3 Bb ≤ 2 := (h.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hRbar2 : 2 ≤ Open.pRank 3 (barM M R) := by
    rw [pRank_barM_eq h3 (by decide) M R h.le_M]
    exact hR2
  rcases hirr W hWR hWn with hW0 | hWR'
  · rw [eq_bot_iff]
    rintro x ⟨hxR, hxC⟩
    obtain ⟨r, hrR, rfl⟩ := mem_barM_iff.mp hxR
    have : (r : G) ∈ W := hmemW r hrR hxC
    rw [hW0, Subgroup.mem_bot] at this
    have hr1 : r = 1 := Subtype.ext this
    rw [hr1, map_one]
    exact Subgroup.one_mem _
  · exfalso
    have hRC : barM M R ≤ Cb := by
      intro x hx
      obtain ⟨r, hrR, rfl⟩ := mem_barM_iff.mp hx
      have : (r : G) ∈ W := hWR' ▸ hrR
      obtain ⟨hr, hc⟩ := hWmem r this
      exact hc
    have hyR : y ∈ Subgroup.centralizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hRC hb) y hyL).symm
    have hsucc := succ_pRank_le_of_commute (q := 3) hRB hRC hyB hy3 hyC hyR
    omega

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.exists_survivor_of_irreducible (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM3 : 3 ≤ Open.pRank 3 M) (hM3' : Open.pRank 3 M ≤ 3)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    (hout : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        IsPGroup 3 (Subgroup.zpowers u) →
          u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hRel : IsElemAbelian 3 R) (hR9 : Nat.card R = 9)
    (hirr : IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R) :
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
      (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) ∧
      3 ≤ Open.pRank 3 L ∧
      barM M R ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      barM M R ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  have hBH : Open.pRank 3 Bb ≤ 2 := (h.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hR2 : 2 ≤ Open.pRank 3 R :=
    le_pRank_of_isElemAbelian h3 hRel (by rw [hR9]; norm_num : Nat.card R = 3 ^ 2)
  have hRel' : IsElemAbelian 3 (barM M R) := CFSG.AGLEmbeddingD2.isElemAbelian_barM hRel
  have hRB : barM M R ≤ Bb := barM_mono fun r hr => by
    rw [h.normalizer_twoCore_H]
    exact h.le_H hr
  have hRbar2 : 2 ≤ Open.pRank 3 (barM M R) := by
    rw [pRank_barM_eq h3 (by decide) M R h.le_M]
    exact hR2
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 M
  set Eb := barM M E with hEb
  have hrE : Open.pRank 3 M ≤ Open.pRank 3 E :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 h3 E) ⟨E, le_rfl, hE, hEcard⟩
  have hEb' : Open.pRank 3 Eb = Open.pRank 3 E := pRank_barM_eq h3 (by decide) M E hEM
  have hEbel : IsElemAbelian 3 Eb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hE
  have hu3 : ∀ u ∈ Eb, IsPGroup 3 (Subgroup.zpowers u) := fun u hu =>
    isPGroup_zpowers_of_pow_eq_one (hEbel.2 u hu)
  have hEN : ∀ L : Subgroup G, IsWeakSBlock M S L →
      Eb ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL u hu =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL (hu3 u hu)
  have hEL : ∀ L : Subgroup G, IsWeakSBlock M S L →
      Eb ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL u hu => hout L hL u (hEN L hL hu) (hu3 u hu)
  have hR3 : ∀ x ∈ barM M R, IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
    isPGroup_zpowers_of_pow_eq_one (hRel'.2 x hx)
  have hRN : ∀ L : Subgroup G, IsWeakSBlock M S L →
      barM M R ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL x hx =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL (hR3 x hx)
  have hRL : ∀ L : Subgroup G, IsWeakSBlock M S L →
      barM M R ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL x hx => hout L hL x (hRN L hL hx) (hR3 x hx)
  have hnS : ∀ n ∈ H ⊓ M, n ∈ Subgroup.normalizer (S : Set G) := fun n hn => by
    rw [h.normalizer_twoCore_H]
    exact hn.1
  obtain ⟨L₁, hL₁⟩ := h.exists_weakSBlock h84 hD2
  by_cases hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L₁
  ·
    set Lb := barM M L₁ with hLb
    set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
    have hCB : Cb ≤ Bb := fun c hc =>
      h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' =>
        (hk1 L' hL').symm ▸ hc
    have hst : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
        mk ⟨n, hn⟩ ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      intro n hn hnM
      have hw := hL₁.map_conj hnM (hnS n hn.1)
      have he := hk1 _ hw
      rw [barM_map_conj hnM] at he
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
    have hker := h.barM_inf_centralizer_eq_bot hH hR2 hirr hst (hy L₁ hL₁)
    by_cases hZ : 3 ∣ Nat.card (Lb ⊓ Cb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    ·
      exfalso
      obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ
      rw [Subgroup.orderOf_mk] at hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hz
        exact absurd hz (by norm_num)
      have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have hzB : z ∈ Bb := hCB hzZ.2
      have hLCz : Lb ⊔ Cb ≤ Subgroup.centralizer ({z} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        refine sup_le (fun l hl => ?_) (fun c hc => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hzZ.2 l hl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hc z hzZ.1).symm
      have hzR : z ∈ Subgroup.centralizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLCz (hRL L₁ hL₁ hx))
      have hzR' : z ∉ barM M R := fun hzR'' => hz1 (by
        have : z ∈ barM M R ⊓ Cb := ⟨hzR'', hzZ.2⟩
        rw [hker, Subgroup.mem_bot] at this
        exact this)
      have hsucc := succ_pRank_le_of_commute (q := 3) hRB le_rfl hzB hz3 hzR' hzR
      omega
    ·
      have hlift : Open.pRank 3 (barM M R) ≤ Open.pRank 3 (Lb ⊓ (barM M R ⊔ Cb)) :=
        pRank_le_pRank_inf_sup_centralizer h3 (hRN L₁ hL₁) (hRL L₁ hL₁) hZ hker
      have hcomm : ∀ x ∈ Lb ⊓ (barM M R ⊔ Cb), ∀ y ∈ Eb ⊓ Cb, x * y = y * x := fun x hx y hy =>
        Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
      have hcop : Nat.Coprime 3 (Nat.card ((Lb ⊓ (barM M R ⊔ Cb)) ⊓ (Eb ⊓ Cb) :
          Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
        rw [Nat.Prime.coprime_iff_not_dvd h3]
        intro hd
        apply hZ
        exact hd.trans (Subgroup.card_dvd_of_le fun x hx => ⟨hx.1.1, hx.2.2⟩)
      have hsum : Open.pRank 3 (Lb ⊓ (barM M R ⊔ Cb)) + Open.pRank 3 (Eb ⊓ Cb) ≤
          Open.pRank 3 ((Lb ⊓ (barM M R ⊔ Cb)) ⊔ (Eb ⊓ Cb)) :=
        pRank_add_le_pRank_sup_of_coprime h3 hcomm hcop
      have hle : (Lb ⊓ (barM M R ⊔ Cb)) ⊔ (Eb ⊓ Cb) ≤ Bb :=
        sup_le (inf_le_right.trans (sup_le hRB hCB)) (inf_le_right.trans hCB)
      have hmono : Open.pRank 3 ((Lb ⊓ (barM M R ⊔ Cb)) ⊔ (Eb ⊓ Cb)) ≤ Open.pRank 3 Bb :=
        CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hle
      have hF : Open.pRank 3 (Eb ⊓ Cb) = 0 := by omega
      have hEr : Open.pRank 3 Eb ≤ Open.pRank 3 (Eb ⊓ Cb) + Open.pRank 3 Lb :=
        pRank_le_pRank_inf_centralizer_add_pRank h3 (hEN L₁ hL₁) (hEL L₁ hL₁) hZ
      have hLbL : Open.pRank 3 Lb = Open.pRank 3 L₁ := pRank_barM_eq h3 (by decide) M L₁ hL₁.le
      refine ⟨L₁, hL₁, hk1, ?_, hRL L₁ hL₁, hker⟩
      omega
  ·
    exfalso
    simp only [not_forall] at hk1
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
      · have h12 : barM M L₁ ≠ barM M L₂ := hne'
        have h13 : barM M L₁ ≠ barM M L' := fun he => hcon.1 he.symm
        have h23 : barM M L₂ ≠ barM M L' := fun he => hcon.2 he.symm
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
        all_goals first
          | exact absurd hij h12 | exact absurd hij.symm h12 | exact absurd hij h13
          | exact absurd hij.symm h13 | exact absurd hij h23 | exact absurd hij.symm h23
    set L₁b := barM M L₁ with hL₁b
    set L₂b := barM M L₂ with hL₂b
    set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
    set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₂
    have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      hL₁.component hL₂.component hne'
    have hL₁C₂ : L₁b ≤ C₂ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp
    have hL₂C₁ : L₂b ≤ C₁ := by
      have : ⁅L₂b, L₁b⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomp
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp this
    by_cases hZ₁ : 3 ∣ Nat.card (L₁b ⊓ C₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    · exact h.false_of_two_weakSBlocks_of_center h84 h86 hD2 hH hL₁ hL₂ hne' hk2 hZ₁ (hy L₁ hL₁)
        (hy L₂ hL₂)
    by_cases hZ₂ : 3 ∣ Nat.card (L₂b ⊓ C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    · have hk2' : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
          barM M L' = barM M L₂ ∨ barM M L' = barM M L₁ := fun L' hL' => (hk2 L' hL').symm
      exact h.false_of_two_weakSBlocks_of_center h84 h86 hD2 hH hL₂ hL₁ hne'.symm hk2' hZ₂
        (hy L₂ hL₂) (hy L₁ hL₁)
    obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ := hy L₁ hL₁
    obtain ⟨y₂, hy₂P, hy₂3, hy₂C⟩ := hy L₂ hL₂
    have hy₁B : y₁ ∈ Bb := barM_mono inf_le_left hy₁P
    have hy₂B : y₂ ∈ Bb := barM_mono inf_le_left hy₂P
    have hy₁L : y₁ ∈ L₁b := barM_mono inf_le_right hy₁P
    have hy₂L : y₂ ∈ L₂b := barM_mono inf_le_right hy₂P
    have hFB : Eb ⊓ C₁ ⊓ C₂ ≤ Bb := fun c hc =>
      h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' => by
        rcases hk2 L' hL' with he | he
        · exact he.symm ▸ hc.1.2
        · exact he.symm ▸ hc.2
    have hFrank : Open.pRank 3 (Eb ⊓ C₁ ⊓ C₂) = 0 := by
      set F := Eb ⊓ C₁ ⊓ C₂ with hF
      have hFC₁ : F ≤ C₁ := fun x hx => hx.1.2
      have hFC₂ : F ≤ C₂ := fun x hx => hx.2
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
    have hr₁ : Open.pRank 3 Eb ≤ Open.pRank 3 (Eb ⊓ C₁) + Open.pRank 3 L₁b :=
      pRank_le_pRank_inf_centralizer_add_pRank h3 (hEN L₁ hL₁) (hEL L₁ hL₁) hZ₁
    have hr₂ : Open.pRank 3 (Eb ⊓ C₁) ≤ Open.pRank 3 (Eb ⊓ C₁ ⊓ C₂) + Open.pRank 3 L₂b :=
      pRank_le_pRank_inf_centralizer_add_pRank h3 (E := Eb ⊓ C₁)
        (inf_le_left.trans (hEN L₂ hL₂))
        (fun u hu => hout L₂ hL₂ u (hEN L₂ hL₂ hu.1) (hu3 u hu.1)) hZ₂
    have hcommL : ∀ x ∈ L₁b, ∀ y ∈ L₂b, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hL₂C₁ hy) x hx
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
    have hsum3 : Open.pRank 3 L₁ + Open.pRank 3 L₂ = 3 := by omega
    have hne12 : Open.pRank 3 L₁ ≠ Open.pRank 3 L₂ := by omega
    have hstable : ∀ L₀ L₀' : Subgroup G, IsWeakSBlock M S L₀ → IsWeakSBlock M S L₀' →
        Open.pRank 3 L₀ ≠ Open.pRank 3 L₀' →
        (∀ L' : Subgroup G, IsWeakSBlock M S L' →
          barM M L' = barM M L₀ ∨ barM M L' = barM M L₀') →
        ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
          mk ⟨n, hn⟩ ∈ Subgroup.normalizer (barM M L₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      intro L₀ L₀' hL₀ hL₀' hrk hall n hn hnM
      have hw := hL₀.map_conj hnM (hnS n hn.1)
      rcases hall _ hw with he | he
      · rw [barM_map_conj hnM] at he
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
      · exfalso
        apply hrk
        have e1 : Open.pRank 3 (barM M L₀') = Open.pRank 3 L₀' :=
          pRank_barM_eq h3 (by decide) M L₀' hL₀'.le
        have e2 : Open.pRank 3 (barM M (L₀.map (MulAut.conj n).toMonoidHom)) =
            Open.pRank 3 (L₀.map (MulAut.conj n).toMonoidHom) :=
          pRank_barM_eq h3 (by decide) M _ hw.le
        have e3 : Open.pRank 3 (L₀.map (MulAut.conj n).toMonoidHom) = Open.pRank 3 L₀ :=
          CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3 _
            (MulAut.conj n).injective L₀
        rw [← e1, ← he, e2, e3]
    have hk2' : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₂ ∨ barM M L' = barM M L₁ := fun L' hL' => (hk2 L' hL').symm
    have hker₁ := h.barM_inf_centralizer_eq_bot hH hR2 hirr
      (hstable L₁ L₂ hL₁ hL₂ hne12 hk2) (hy L₁ hL₁)
    have hker₂ := h.barM_inf_centralizer_eq_bot hH hR2 hirr
      (hstable L₂ L₁ hL₂ hL₁ hne12.symm hk2') (hy L₂ hL₂)
    have hlift₁ : Open.pRank 3 (barM M R) ≤ Open.pRank 3 (L₁b ⊓ (barM M R ⊔ C₁)) :=
      pRank_le_pRank_inf_sup_centralizer h3 (hRN L₁ hL₁) (hRL L₁ hL₁) hZ₁ hker₁
    have hlift₂ : Open.pRank 3 (barM M R) ≤ Open.pRank 3 (L₂b ⊓ (barM M R ⊔ C₂)) :=
      pRank_le_pRank_inf_sup_centralizer h3 (hRN L₂ hL₂) (hRL L₂ hL₂) hZ₂ hker₂
    have hle₁ : Open.pRank 3 (L₁b ⊓ (barM M R ⊔ C₁)) ≤ Open.pRank 3 L₁b :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 inf_le_left
    have hle₂ : Open.pRank 3 (L₂b ⊓ (barM M R ⊔ C₂)) ≤ Open.pRank 3 L₂b :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 inf_le_left
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
