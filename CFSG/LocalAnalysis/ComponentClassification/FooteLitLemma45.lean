module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma45Sylow

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def IsFooteM (L M : Subgroup G) : Prop :=
  ∃ (z : G) (A E : Subgroup G), FootePointedMaximal z A ∧ A ∈ footeFamilyOf L ∧
    (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 ∧ E ≤ coreActionKernel A ∧ M = footeME L E

omit [Finite G] in
theorem card_conjugate_eq_card (F : Subgroup G) (k : G) :
    Nat.card (conjugate F k) = Nat.card F := by
  unfold conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective

omit [Finite G] in
theorem sq_eq_one_of_mem_conjugate {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1) (k : G) :
    ∀ x ∈ conjugate F k, x ^ 2 = 1 := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h1 := hF2 _ hx
  calc x ^ 2 = k⁻¹ * (k * x * k⁻¹) ^ 2 * k := by rw [sq, sq]; group
    _ = 1 := by rw [h1]; group

omit [Finite G] in
theorem le_of_conjugate_le {X Y : Subgroup G} {k : G} (h : conjugate X k ≤ conjugate Y k) :
    X ≤ Y := by
  rw [← conjugate_conjugate_inv X k, ← conjugate_conjugate_inv Y k]
  exact map_mono h

omit [Finite G] in
theorem conjugate_le_of_forall {F T : Subgroup G} {k : G} (h : ∀ a ∈ F, k⁻¹ * a * k ∈ T) :
    conjugate F k ≤ T := fun x hx => by
  rw [mem_conjugate_iff] at hx
  have h1 := h _ hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h1

theorem IsFooteM.sylow (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ (e : G) (S : Subgroup G), orderOf e = 2 ∧ e ∈ S ∧
      FootePointedMaximal e (footeF L e) ∧ footeF L e ∈ footeFamilyOf L ∧
      IsSylowOf 2 S (coreActionKernel M) ∧ IsSylowOf 2 S (coreActionKernel (footeF L e)) ∧
      footeF L e ≤ M ∧ footeF L e ⊔ oddCoreIn M = M ∧
      (∀ F : Subgroup G, F ≤ S → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 → footeME L F = M) ∧
      normalizer (S : Set G) ≤ normalizer (M : Set G) := by
  obtain ⟨z, A, E, hAmax, hAF, hE2, hE8, hEA, rfl⟩ := hM
  obtain ⟨e, S, he, heS, hKmax, hKF, hS, hSK, -, hKM, hsup, hall, hN⟩ :=
    foote_lemma_4_5_sylow h hAmax hAF hE2 hE8 hEA
  exact ⟨e, S, he, heS, hKmax, hKF, hS, hSK, hKM, hsup, hall, hN⟩

theorem foote_lemma_4_5_i (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) {a : G}
    (ha : orderOf a = 2) (haC : a ∈ coreActionKernel M) :
    footeFixed M a = footeF L a ∧ M ≤ footeF L a ⊔ oddCoreIn M ∧
      FootePointedMaximal a (footeF L a) ∧ footeF L a ∈ footeFamilyOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, S, -, -, hKmax, hKF, hS, hSK, hKM, hsup, -, -⟩ := hM.sylow h
  set K := footeF L e with hK
  have hclaim : ∀ b ∈ S, orderOf b = 2 →
      footeFixed M b = footeF L b ∧ M ≤ footeF L b ⊔ oddCoreIn M ∧
        FootePointedMaximal b (footeF L b) ∧ footeF L b ∈ footeFamilyOf L := by
    intro b hbS hb
    have hbK : b ∈ coreActionKernel K := hSK.le hbS
    obtain ⟨hB, hBmax, hBF, hTB, hfixK⟩ := footeF_spec h hKmax hKF hb hbK
    set T := oddResidualIn (K ⊓ centralizer ({b} : Set G)) with hT
    have hb2 : IsPGroup 2 (zpowers b) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hb, pow_one]
    have hKres : K ≤ oddResidualIn K :=
      (oddResidualIn_eq_self_of_isPComponent hKmax.1.2.1 hKmax.1.2.2).ge
    have hKcov : K ≤ T ⊔ oddCoreIn K := by
      have h1 := le_oddResidualIn_inf_centralizer_sup hb2 (zpowers_le.mpr hbK) hKres
      rwa [centralizer_zpowers_eq] at h1
    have hOK : oddCoreIn K ≤ oddCoreIn M := oddCoreIn_le_of_sup hKM hsup
    have hMcov : M ≤ T ⊔ oddCoreIn M := by
      calc M = K ⊔ oddCoreIn M := hsup.symm
        _ ≤ T ⊔ oddCoreIn M := sup_le (hKcov.trans (sup_le_sup_left hOK _)) le_sup_right
    refine ⟨le_antisymm ?_ ?_, hMcov.trans (sup_le_sup_right hTB _), hBmax, hBF⟩
    ·
      refine footeFixed_le_of_oddResidualIn_le
        (le_normalizer_of_mem_footeFamilyOf h.huniq hB hBF) ((closure_le _).mpr fun g hg => ?_)
      obtain ⟨hgMb, h2⟩ := hg
      obtain ⟨hgM, hgb⟩ := mem_inf.mp hgMb
      have hTO : T ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G) := fun x hx =>
        mem_normalizer_oddCoreIn (le_normalizer (hKM ((oddResidualIn_le _).trans inf_le_left hx)))
      have hg' := hMcov hgM
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T (oddCoreIn M) hTO] at hg'
      obtain ⟨t, ht, o, ho, hto⟩ := hg'
      have htb : t ∈ centralizer ({b} : Set G) := (mem_inf.mp (oddResidualIn_le _ ht)).2
      have hob : o ∈ centralizer ({b} : Set G) := by
        have h1 : o = t⁻¹ * g := by rw [← hto]; group
        rw [h1]
        exact mul_mem (inv_mem htb) hgb
      set O := oddCoreIn M ⊓ centralizer ({b} : Set G) with hO
      have hOodd : Odd (Nat.card O) :=
        Odd.of_dvd_nat (odd_card_oddCoreIn M) (card_dvd_of_le inf_le_left)
      have hgsup : g ∈ O ⊔ footeF L b := by
        rw [← hto]
        exact mul_mem (mem_sup_right (hTB ht)) (mem_sup_left (mem_inf.mpr ⟨ho, hob⟩))
      exact mem_of_two_element_of_mem_sup
        (fun x hx => le_normalizer_of_mem_footeFamilyOf h.huniq hB hBF (mem_inf.mp hx).2)
        (by rw [oddResidualIn_eq_bot_of_odd hOodd]; exact bot_le) hgsup h2
    ·
      rw [← hfixK, footeFixed_eq_oddResidualIn, footeFixed_eq_oddResidualIn]
      exact oddResidualIn_mono (sup_le_sup_right (inf_le_inf_right _ hKM) _)
  have ha2 : IsPGroup 2 (zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha, pow_one]
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf hS (zpowers_le.mpr haC) ha2
  have hbS : k⁻¹ * a * k ∈ S := hk a (mem_zpowers a)
  have hb : orderOf (k⁻¹ * a * k) = 2 := by
    rw [show k⁻¹ * a * k = MulAut.conj k⁻¹ a by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, ha]
  obtain ⟨h1, h2, h3, h4⟩ := hclaim _ hbS hb
  have hkN : k ∈ normalizer (M : Set G) := hkC.1
  have hMk : conjugate M k = M := conjugate_eq_of_mem_normalizer hkN
  have hOk : conjugate (oddCoreIn M) k = oddCoreIn M :=
    conjugate_eq_of_mem_normalizer (mem_normalizer_oddCoreIn hkN)
  have hFk : footeF L (k⁻¹ * a * k) = conjugate (footeF L a) k := footeF_conj h.huniq a k
  have hfix : footeFixed M (k⁻¹ * a * k) = conjugate (footeFixed M a) k := by
    have h5 := map_footeFixed_mulEquiv (MulAut.conj k⁻¹) M a
    rw [MulAut.conj_apply, inv_inv] at h5
    unfold conjugate
    rw [h5]
    exact congrArg (fun X => footeFixed X (k⁻¹ * a * k)) hMk.symm
  rw [hFk] at h1 h2 h3 h4
  rw [hfix] at h1
  refine ⟨conjugate_injective h1, ?_, ?_, ?_⟩
  · apply le_of_conjugate_le (k := k)
    rw [hMk, UnbalancedLayer.conjugate_sup, hOk]
    exact h2
  · have h5 := h3.conjugate k⁻¹
    rwa [inv_inv, show k * (k⁻¹ * a * k) * k⁻¹ = a by group, conjugate_conjugate_inv] at h5
  · have h5 := conjugate_mem_footeFamilyOf h4 k⁻¹
    rwa [conjugate_conjugate_inv] at h5

theorem foote_lemma_4_5_ii (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hFC : F ≤ coreActionKernel M) :
    footeME L F = M ∧ ∀ W : Subgroup G, IsKleinFour W → W ≤ F → footeME L W = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, S, -, -, hKmax, hKF, hS, hSK, -, -, hall, -⟩ := hM.sylow h
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf hS hFC hFp
  have hMk : conjugate M k = M := conjugate_eq_of_mem_normalizer hkC.1
  have hF'S : conjugate F k ≤ S := conjugate_le_of_forall hk
  have hF'2 := sq_eq_one_of_mem_conjugate hF2 k
  have hF'8 : Nat.card (conjugate F k) = 8 := by rw [card_conjugate_eq_card, hF8]
  have hF' : footeME L (conjugate F k) = M := hall _ hF'S hF'2 hF'8
  have hFM : footeME L F = M := by
    apply conjugate_injective (g := k)
    rw [← footeME_conjugate h.huniq, hF', hMk]
  refine ⟨hFM, fun W hW hWF => ?_⟩
  have hspec := footeME_spec h hKmax hKF (isMulCommutative_of_sq_eq_one hF'2) hF'2 hF'8
    (hF'S.trans hSK.le)
  have hW' : IsKleinFour (conjugate W k) :=
    isKleinFour_of_card_eq_four (by rw [card_conjugate_eq_card, hW.card_four])
      (sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hW hx) k)
  have h1 := hspec.2.2 _ hW' (map_mono hWF)
  rw [hF'] at h1
  apply conjugate_injective (g := k)
  rw [← footeME_conjugate h.huniq, ← h1, hMk]

theorem foote_lemma_4_5_iii (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {X F : Subgroup G} (hXC : X ≤ coreActionKernel M) (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) (hFX : F ≤ X) :
    normalizer (X : Set G) ≤ normalizer (M : Set G) := by
  intro g hg
  have hFg : conjugate F g ≤ X := by
    rw [← conjugate_eq_of_mem_normalizer hg]
    exact map_mono hFX
  have h1 := (foote_lemma_4_5_ii h hM (sq_eq_one_of_mem_conjugate hF2 g)
    (by rw [card_conjugate_eq_card, hF8]) (hFg.trans hXC)).1
  have h2 := (foote_lemma_4_5_ii h hM hF2 hF8 (hFX.trans hXC)).1
  rw [footeME_conjugate h.huniq, h2] at h1
  exact mem_normalizer_of_conjugate_eq h1

theorem foote_lemma_4_5_iii_four (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {W F : Subgroup G} (hW : IsKleinFour W) (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hFC : F ≤ coreActionKernel M) (hWF : W ≤ F) :
    normalizer (W : Set G) ≤ normalizer (M : Set G) := by
  intro g hg
  have hWM := (foote_lemma_4_5_ii h hM hF2 hF8 hFC).2 W hW hWF
  apply mem_normalizer_of_conjugate_eq
  rw [← hWM, ← footeME_conjugate h.huniq, conjugate_eq_of_mem_normalizer hg]

theorem footeF_le_of_card_eight (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {a : G} (ha : orderOf a = 2) (haC : a ∈ coreActionKernel M) {F : Subgroup G}
    (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hFC : F ≤ coreActionKernel M ⊓ centralizer ({a} : Set G)) :
    footeF L a ≤ M ∧ footeF L a ⊔ oddCoreIn M = M := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha; omega
  obtain ⟨F', hF'2, hF'8, haF', hF'le⟩ := exists_card_eight_mem hF2 hF8 ha2
    (fun f hf => (mem_centralizer_singleton_iff.mp (mem_inf.mp (hFC hf)).2))
  have hF'C : F' ≤ coreActionKernel M :=
    hF'le.trans (sup_le (hFC.trans inf_le_left) (zpowers_le.mpr haC))
  have hF'M := (foote_lemma_4_5_ii h hM hF'2 hF'8 hF'C).1
  have hle : footeF L a ≤ M := hF'M ▸ footeF_le_footeME haF' ha1
  exact ⟨hle, le_antisymm (sup_le hle (map_subtype_le _))
    (foote_lemma_4_5_i h hM ha haC).2.1⟩

theorem foote_lemma_4_5_iv (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {a : G} (ha : orderOf a = 2) (haC : a ∈ coreActionKernel M) {F : Subgroup G}
    (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hFC : F ≤ coreActionKernel M ⊓ centralizer ({a} : Set G)) :
    (∀ T : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ coreActionKernel (footeF L a)) →
      IsSylowOf 2 T (coreActionKernel (footeF L a))) ∧
    (∀ T : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ coreActionKernel (footeF L a) ⊓
        centralizer ({a} : Set G)) →
      IsSylowOf 2 T (coreActionKernel (footeF L a) ⊓ centralizer ({a} : Set G))) ∧
    (∃ P : Subgroup G, IsSylowOf 2 P (normalizer (footeF L a : Set G)) ∧
      P ≤ normalizer (M : Set G)) ∧
    ∃ P : Subgroup G, IsSylowOf 2 P (centralizer ({a} : Set G)) ∧
      P ≤ normalizer (M : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := footeF L a with hB
  obtain ⟨hBM, hBsup⟩ := footeF_le_of_card_eight h hM ha haC hF2 hF8 hFC
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM ha haC
  have hBN : centralizer ({a} : Set G) ≤ normalizer (B : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  have hCB : ∀ x ∈ coreActionKernel M, x ∈ normalizer (B : Set G) → x ∈ coreActionKernel B :=
    fun x hx hxN => mem_coreActionKernel_of_le hBM hxN hx
  have hBC : ∀ x ∈ coreActionKernel B, x ∈ normalizer (M : Set G) → x ∈ coreActionKernel M :=
    fun x hx hxN => mem_coreActionKernel_of_sup hBM hBsup hxN hx
  have hFB : F ≤ coreActionKernel B := fun x hx =>
    hCB x (mem_inf.mp (hFC hx)).1 (hBN (mem_inf.mp (hFC hx)).2)
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  have hNT : ∀ X T : Subgroup G, F ≤ X → X ≤ coreActionKernel M → IsSylowOf 2 T X →
      normalizer (T : Set G) ≤ normalizer (M : Set G) := by
    intro X T hFX hXC hT
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hT hFX hFp
    exact foote_lemma_4_5_iii h hM (hT.le.trans hXC) (sq_eq_one_of_mem_conjugate hF2 k)
      (by rw [card_conjugate_eq_card, hF8]) (conjugate_le_of_forall hk)
  have hX₁ : F ≤ coreActionKernel M ⊓ coreActionKernel B :=
    le_inf (hFC.trans inf_le_left) hFB
  have hX₂ : F ≤ coreActionKernel M ⊓ coreActionKernel B ⊓ centralizer ({a} : Set G) :=
    le_inf hX₁ (hFC.trans inf_le_right)
  have hiv1 : ∀ T : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ coreActionKernel B) →
      IsSylowOf 2 T (coreActionKernel B) := by
    intro T hT
    refine isSylowOf_of_normalizer_le hT inf_le_right fun x hx => ?_
    obtain ⟨hxB, hxN⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨hBC x hxB (hNT _ T hX₁ inf_le_left hT hxN), hxB⟩
  have hiv2 : ∀ T : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ coreActionKernel B ⊓
      centralizer ({a} : Set G)) →
      IsSylowOf 2 T (coreActionKernel B ⊓ centralizer ({a} : Set G)) := by
    intro T hT
    refine isSylowOf_of_normalizer_le hT (inf_le_inf_right _ inf_le_right) fun x hx => ?_
    obtain ⟨hxBa, hxN⟩ := mem_inf.mp hx
    obtain ⟨hxB, hxa⟩ := mem_inf.mp hxBa
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hBC x hxB (hNT _ T hX₂ (inf_le_left.trans inf_le_left) hT hxN),
      hxB⟩, hxa⟩
  refine ⟨hiv1, hiv2, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := exists_isSylowOf 2 (coreActionKernel M ⊓ coreActionKernel B)
    obtain ⟨P, hP, -, hPT⟩ := exists_isSylowOf_le_normalizer (hiv1 T hT)
      (fun x hx => hx.1) (fun x hx => mem_normalizer_coreActionKernel hx)
    exact ⟨P, hP, hPT.trans (hNT _ T hX₁ inf_le_left hT)⟩
  · obtain ⟨T, hT⟩ := exists_isSylowOf 2 (coreActionKernel M ⊓ coreActionKernel B ⊓
      centralizer ({a} : Set G))
    obtain ⟨P, hP, -, hPT⟩ := exists_isSylowOf_le_normalizer (hiv2 T hT) inf_le_right
      (fun x hx => mem_normalizer_inf' (mem_normalizer_coreActionKernel (hBN hx))
        (le_normalizer hx))
    exact ⟨P, hP, hPT.trans (hNT _ T hX₂ (inf_le_left.trans inf_le_left) hT)⟩

end CFSG.ComponentClassification.FooteLit
