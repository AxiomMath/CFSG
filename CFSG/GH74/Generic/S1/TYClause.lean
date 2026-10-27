module

public import CFSG.GH74.Generic.S1.TYCore
public import CFSG.GH74.Generic.S1.TInvThree
public import CFSG.GH74.Generic.S1.TNeg
public import CFSG.GH74.Generic.S1.TLarge
public import CFSG.GH74.Generic.S1.RQ3Good

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

@[expose] def S1CompNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
          centralizer ({c} : Set G) ≤
            normalizer ((symJ (symX x u) 0 ⊔ symJ (symX x u) 1 : Subgroup G) : Set G)

@[expose] def S1CompNormal3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → S1FrameOddFree x u →
          ∀ c ∈ symJ3 (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ3 (symX x u) 3, a * c = c * a) →
            centralizer ({c} : Set G) ≤
              normalizer ((symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1 : Subgroup G) : Set G)

theorem iSup_fin_three {G : Type} [Group G] (A : Fin 3 → Subgroup G) :
    (⨆ i, A i : Subgroup G) = A 0 ⊔ A 1 ⊔ A 2 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact (le_sup_of_le_left le_sup_left : A 0 ≤ A 0 ⊔ A 1 ⊔ A 2)
    · exact (le_sup_of_le_left le_sup_right : A 1 ≤ A 0 ⊔ A 1 ⊔ A 2)
    · exact (le_sup_right : A 2 ≤ A 0 ⊔ A 1 ⊔ A 2)
  · exact sup_le (sup_le (le_iSup A 0) (le_iSup A 1)) (le_iSup A 2)

variable {G : Type} [Group G] [Finite G]

theorem s1YClause_lin (hExact : S1LiftExactProp) (hC : S1CompNormal)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (hbigK : S1LargeModel K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) (hsym : S1SymFrame x u) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 4 = 3) (hlin : S1SymFrameLin x u F) {y : G} (hyJ : y ∈ symJ (symX x u) 1)
    (hy2 : orderOf y = 2) (hyc : ∀ a ∈ symJ (symX x u) 1, a * y = y * a) :
    centralizer ({y} : Set G) ≤ normalizer ((⨆ i, symJ (symX x u) i : Subgroup G) : Set G) := by
  have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  have hstd := fun a b c hab hac hbc => lin_std hF h4 a b c hab hac hbc
  have hchain := lin_chain hF h4
  have hcen := lin_blk_center hF h4
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, -⟩ :=
    symSystem (linBlockOps hF h4) (symX x u) D hw hDact (linKind F) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hlink : S1LinkedLin x (D 4).K F (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedLin x K F (symJ (symX x u)) := hlink.congr hK
  have hq3 : 3 ≤ p ^ f := by rw [← hcard]; omega
  have hfacts := s1A4Facts_lin (symJ (symX x u)) p f F hpp hcard hq3 ⟨hcomm, hpair⟩ hlinkK hyJ hy2 hyc
  obtain ⟨Wc, hWc⟩ := hchain
  have hgen : (linBlockOps hF h4).blk 0 1 ⊔ (linBlockOps hF h4).blk 1 2 ⊔
      (linBlockOps hF h4).blk 2 3 = ⊤ := by
    have := hWc.gen
    rw [iSup_fin_three] at this
    exact this
  have hfus : ∀ s t : G, s ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1 →
      t ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1 → orderOf s = 2 → orderOf t = 2 →
        ∃ g ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1, g * s * g⁻¹ = t := by
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, hfu⟩ := lin_pair_fusion h2 hW01
    intro s t hs ht hs2 ht2
    rw [← hWe] at hs ht
    obtain ⟨g, hg, hgs⟩ := hfu s t hs ht hs2 ht2
    exact ⟨g, hWe ▸ hg, hgs⟩
  exact centralizer_y_le_of_comp (D := D 4) hset.inv (by rw [hK]; exact hset.shape.2)
    (by rw [hK]; exact hfront.b5) (blk := (linBlockOps hF h4).blk) (J := symJ (symX x u))
    (symJ_one (linBlockOps hF h4) (symX x u) D hw hDact)
    (symJ_two (linBlockOps hF h4) (symX x u) D hw hDact)
    (symJ_three (linBlockOps hF h4) (symX x u) D hw hDact) hgen (lin_neg_mul hF)
    (fun g hg h hh => (linBlockOps hF h4).commute 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) g hg h hh) hcomm hfus
    (hC G x K hset hfront hbigK u hu hf hsym) hfacts.classes hyJ hy2 hyc hfacts.noncomm

theorem s1YClause_uni (hExact : S1LiftExactProp) (hC : S1CompNormal)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (hbigK : S1LargeModel K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) (hsym : S1SymFrame x u) {q : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (huni : S1SymFrameUni x u q F) (p f : ℕ)
    [Fact p.Prime] [CharP F p] (hqpf : q = p ^ f) {y : G} (hyJ : y ∈ symJ (symX x u) 1)
    (hy2 : orderOf y = 2) (hyc : ∀ a ∈ symJ (symX x u) 1, a * y = y * a) :
    centralizer ({y} : Set G) ≤ normalizer ((⨆ i, symJ (symX x u) i : Subgroup G) : Set G) := by
  subst hqpf
  have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSU 4 (p ^ f) F), ∀ j,
          ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  have hstd := fun a b c hab hac hbc => uni_std hF hq rfl a b c hab hac hbc
  have hchain := uni_chain hF hq rfl
  have hcen := uni_blk_center hF hq
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, -⟩ :=
    symSystem (uniBlockOps hF hq) (symX x u) D hw hDact (uniKind F p f) hstd hchain hcen
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  have hlink : S1LinkedUni x (D 4).K F p f (symJ (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedUni x K F p f (symJ (symX x u)) := hlink.congr hK
  have hq5 : 5 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    have hq1 : 1 < p ^ f := by
      by_contra hle
      have hle' : p ^ f ≤ 1 := by omega
      interval_cases hpf : p ^ f <;> simp at h1
    omega
  have hfacts := s1A4Facts_uni (symJ (symX x u)) p f F hF hq5 ⟨hcomm, hpair⟩ hlinkK hyJ hy2 hyc
  obtain ⟨Wc, hWc⟩ := hchain
  have hgen : (uniBlockOps hF hq).blk 0 1 ⊔ (uniBlockOps hF hq).blk 1 2 ⊔
      (uniBlockOps hF hq).blk 2 3 = ⊤ := by
    have := hWc.gen
    rw [iSup_fin_three] at this
    exact this
  have hfus : ∀ s t : G, s ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1 →
      t ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1 → orderOf s = 2 → orderOf t = 2 →
        ∃ g ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1, g * s * g⁻¹ = t := by
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, hfu⟩ := uni_pair_fusion hF hodd hW01
    intro s t hs ht hs2 ht2
    rw [← hWe] at hs ht
    obtain ⟨g, hg, hgs⟩ := hfu s t hs ht hs2 ht2
    exact ⟨g, hWe ▸ hg, hgs⟩
  exact centralizer_y_le_of_comp (D := D 4) hset.inv (by rw [hK]; exact hset.shape.2)
    (by rw [hK]; exact hfront.b5) (blk := (uniBlockOps hF hq).blk) (J := symJ (symX x u))
    (symJ_one (uniBlockOps hF hq) (symX x u) D hw hDact)
    (symJ_two (uniBlockOps hF hq) (symX x u) D hw hDact)
    (symJ_three (uniBlockOps hF hq) (symX x u) D hw hDact) hgen (uni_neg_mul hF hq)
    (fun g hg h hh => (uniBlockOps hF hq).commute 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) g hg h hh) hcomm hfus
    (hC G x K hset hfront hbigK u hu hf hsym) hfacts.classes hyJ hy2 hyc hfacts.noncomm

theorem s1YClause_q3 (hC3 : S1CompNormal3)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3) (hlin : S1SymFrameLin x u F)
    (hodd : S1FrameOddFree x u) {y : G} (hyJ : y ∈ symJ3 (symX x u) 1) (hy2 : orderOf y = 2)
    (hyc : ∀ a ∈ symJ3 (symX x u) 1, a * y = y * a) :
    centralizer ({y} : Set G) ≤ normalizer ((⨆ i, symJ3 (symX x u) i : Subgroup G) : Set G) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF3]; exact ⟨1, rfl⟩)
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData3 x u hF3 hodd hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, -⟩ :=
    symSystem3 (linBlockOps3 hF3) (symX x u) D hw hDact (linKind F)
      (fun a b c hab hac hbc => blkLin_standardPair a b c hab hac hbc) blkLin_chain
      (lin_blk_center3 hF3)
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hq3 : 3 ≤ p ^ f := by rw [← hcard, hF3]
  have hlink : S1LinkedLin x (D 4).K F (symJ3 (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedLin x K F (symJ3 (symX x u)) := hlink.congr hK
  have hfacts := s1A4Facts_lin (symJ3 (symX x u)) p f F hpp hcard hq3 ⟨hcomm, hpair⟩ hlinkK hyJ hy2
    hyc
  obtain ⟨Wc, hWc⟩ := (blkLin_chain (F := F))
  have hgen : (linBlockOps3 hF3).blk 0 1 ⊔ (linBlockOps3 hF3).blk 1 2 ⊔
      (linBlockOps3 hF3).blk 2 3 = ⊤ := by
    have := hWc.gen
    rw [iSup_fin_three] at this
    exact this
  have hfus : ∀ s t : G, s ∈ symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1 →
      t ∈ symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1 → orderOf s = 2 → orderOf t = 2 →
        ∃ g ∈ symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1, g * s * g⁻¹ = t := by
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, hfu⟩ := lin_pair_fusion h2 hW01
    intro s t hs ht hs2 ht2
    rw [← hWe] at hs ht
    obtain ⟨g, hg, hgs⟩ := hfu s t hs ht hs2 ht2
    exact ⟨g, hWe ▸ hg, hgs⟩
  exact centralizer_y_le_of_comp (D := (D 4).toLayerData) hset.inv
    (by rw [hK]; exact hset.shape.2) (by rw [hK]; exact hfront.b5)
    (blk := (linBlockOps3 hF3).blk) (J := symJ3 (symX x u))
    (symJ3_one (linBlockOps3 hF3) (symX x u) D hw hDact)
    (symJ3_two (linBlockOps3 hF3) (symX x u) D hw hDact)
    (symJ3_three (linBlockOps3 hF3) (symX x u) D hw hDact) hgen (lin_neg_mul (by rw [hF3]))
    (fun g hg h hh => (linBlockOps3 hF3).commute 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) g hg h hh) hcomm hfus
    (hC3 G x K hset hfront u hu hf F inferInstance inferInstance hF3 hlin hodd) hfacts.classes hyJ
    hy2 hyc hfacts.noncomm

theorem s1NormalizerYClause_of_comp (hExact : S1LiftExactProp) (hC : S1CompNormal) :
    S1NormalizerYClause := by
  intro G _ _ x K hset hfront hbigK u hu hf hsym y hyJ hy2 hyc
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · exact s1YClause_lin hExact hC hset hfront hbigK hf hsym hF hlin hyJ hy2 hyc
  · obtain ⟨p, f, hud, hqpf, -⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    exact s1YClause_uni hExact hC hset hfront hbigK hf hsym hF hq huni p f hqpf hyJ hy2 hyc

theorem s1NormalizerYClause3_of_comp3 (hC3 : S1CompNormal3) : S1NormalizerYClause3 := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin hF3 hlin hodd y hyJ hy2 hyc
  exact s1YClause_q3 hC3 hset hfront hf hF3 hlin hodd hyJ hy2 hyc

end CFSG.GH74.Generic.S1
