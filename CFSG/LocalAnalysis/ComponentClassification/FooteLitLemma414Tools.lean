module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Two

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution_inf_center {R H : Subgroup G} (hR : IsPGroup 2 R) (hHR : H ≤ R)
    (hRH : R ≤ normalizer (H : Set G)) (hH : H ≠ ⊥) :
    ∃ x ∈ H, orderOf x = 2 ∧ ∀ r ∈ R, r * x = x * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  set H' := H.subgroupOf R with hH'
  have hn : H'.Normal := (normal_subgroupOf_iff_le_normalizer hHR).mpr hRH
  have hH'1 : H' ≠ ⊥ := by
    intro h1
    apply hH
    rw [eq_bot_iff]
    intro x hx
    have h2 : (⟨x, hHR hx⟩ : ↥R) ∈ H' := hx
    rw [h1, mem_bot] at h2
    rw [mem_bot]
    exact congrArg Subtype.val h2
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hH'1
  set Z := H' ⊓ center ↥R with hZ
  have hZp : IsPGroup 2 Z := hR.to_subgroup Z
  obtain ⟨m, hm⟩ := hZp.exists_card_eq
  have hm1 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hne ((Subgroup.card_eq_one).mp hm)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2
    (by rw [hm]; exact dvd_pow_self 2 hm1)
  refine ⟨((c : ↥R) : G), (mem_inf.mp c.2).1, ?_, fun r hr => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have h1 := mem_center_iff.mp (mem_inf.mp c.2).2 ⟨r, hr⟩
    exact congrArg Subtype.val h1

theorem exists_involution_centralizing {P H : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ normalizer (H : Set G)) (hH : Even (Nat.card H)) :
    ∃ x ∈ H, orderOf x = 2 ∧ ∀ p ∈ P, p * x = x * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := H ⊔ P with hQ
  have hQH : Q ≤ normalizer (H : Set G) := sup_le le_normalizer hPH
  obtain ⟨R, hR, hPR⟩ := exists_isSylowOf_ge_of_le (le_sup_right : P ≤ Q) hP
  have hRH := hR.inf_of_le_normalizer (le_sup_left : H ≤ Q) hQH
  have hRH1 : R ⊓ H ≠ ⊥ := by
    intro h1
    have h2 := hRH.card_eq
    rw [h1, card_bot] at h2
    have h3 : (Nat.card H).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
        (even_iff_two_dvd.mp hH)).ne'
    have h4 : 2 ≤ 2 ^ (Nat.card H).factorization 2 := Nat.le_self_pow h3 2
    omega
  obtain ⟨x, hx, hx2, hxc⟩ := exists_involution_inf_center hR.isPGroup inf_le_left
    (fun r hr => mem_normalizer_inf_of_mem (le_normalizer hr) (hQH (hR.le hr))) hRH1
  exact ⟨x, (mem_inf.mp hx).2, hx2, fun p hp => hxc p (hPR hp)⟩

theorem le_coreActionKernel_of_mem_inf
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    {M : Subgroup G} (hM : IsFooteM L M) {k u : G} (hu : orderOf u = 2)
    (huC : u ∈ coreActionKernel M) (huCk : u ∈ coreActionKernel (conjugate M k))
    {X : Subgroup G} (hXCk : X ≤ coreActionKernel (conjugate M k))
    (hXN : X ≤ normalizer (M : Set G)) (hXu : X ≤ centralizer ({u} : Set G)) :
    X ≤ coreActionKernel M := by
  have hM' := isFooteM_conjugate h hM k
  have hB := inf_centralizer_le_footeB h h47 hM' hu huCk
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM u hu huC)
  obtain ⟨hFM, hFsup⟩ := footeF_le_of_card_eight h hM hu huC hF2 hF8 hF
  intro x hx
  have hxB := hB (mem_inf.mpr ⟨hXCk hx, hXu hx⟩)
  exact mem_coreActionKernel_of_sup hFM hFsup (hXN hx) (mem_inf.mp hxB).2

theorem isSylowOf_inf_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {s : G}
    (hs : FooteInCC M s) {T : Subgroup G}
    (hT : IsSylowOf 2 T (coreActionKernel M ⊓ centralizer ({s} : Set G))) :
    IsSylowOf 2 (T ⊓ footeK L s) (footeK L s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs' := hs
  obtain ⟨hs2, hsC, hCs⟩ := hs'
  obtain ⟨hBN, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM hs2 hsC hCs
  obtain ⟨hKB, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
  obtain ⟨R₀, hR₀, hR₀C⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM hs
  set K := footeK L s with hK
  set C := coreActionKernel M with hC
  have hKs : K ≤ centralizer ({s} : Set G) := hKB.trans hBs
  have hTC : T ≤ C := hT.le.trans inf_le_left
  have hKCD : K ⊓ C ≤ C ⊓ centralizer ({s} : Set G) := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).2, hKs (mem_inf.mp hx).1⟩
  have hDKC : C ⊓ centralizer ({s} : Set G) ≤ normalizer ((K ⊓ C : Subgroup G) : Set G) :=
    fun d hd => mem_normalizer_inf_of_mem (mem_normalizer_footeK (hBN (mem_inf.mp hd).2))
      (le_normalizer (mem_inf.mp hd).1)
  have hTKC := hT.inf_of_le_normalizer hKCD hDKC
  have hTKC' : T ⊓ (K ⊓ C) = T ⊓ K := by
    ext x
    simp only [mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hTC hx.1⟩⟩
  rw [hTKC'] at hTKC
  have hR₀KC : IsSylowOf 2 R₀ (K ⊓ C) := hR₀.of_le (le_inf hR₀.le hR₀C) inf_le_left
  apply isSylowOf_of_card (hTKC.le.trans inf_le_left)
  rw [hTKC.card_eq, ← hR₀KC.card_eq, hR₀.card_eq]

theorem eq_conjugate_of_le_normalizer
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M) {g : G}
    (hle : M ≤ normalizer (conjugate M g : Set G)) {w : G} (hw : orderOf w = 2)
    (hwC : w ∈ coreActionKernel M) (hwNg : w ∈ normalizer (conjugate M g : Set G)) :
    M = conjugate M g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set G) with hN
  set Mg := conjugate M g with hMg
  have hM' := isFooteM_conjugate h hM g
  have hNg : conjugate N g = normalizer (Mg : Set G) := conjugate_normalizer M g
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM w hw hwC)
  obtain ⟨hBM, hBsup⟩ := footeF_le_of_card_eight h hM hw hwC hF2 hF8 hF
  obtain ⟨-, -, hBmax, -⟩ := foote_lemma_4_5_i h hM hw hwC
  obtain ⟨-, hBw, hBpc⟩ := hBmax.1
  set B := footeF L w with hB
  have hKC : B ≤ normalizer (Mg : Set G) ⊓ centralizer ({w} : Set G) :=
    le_inf (hBM.trans hle) hBw
  have hKpc : IsPComponent 2 (B.subgroupOf (normalizer (Mg : Set G) ⊓
      centralizer ({w} : Set G))) :=
    isPComponent_subgroupOf_of_le hKC inf_le_right hBpc
  obtain ⟨D, hDN, hDpc, hBD, -, -⟩ := foote_lemma_2_1_iv_subgroup hwNg hw hKC hKpc
  by_cases hDM : D = Mg
  ·
    have hwD : conjugate D w = D := by
      rw [hDM]
      exact conjugate_eq_of_mem_normalizer hwNg
    rw [hwD, sup_idem, hDM] at hBD
    have hMMg : M ≤ Mg := by
      refine (hM.le_oddResidualIn h).trans ((closure_le _).mpr ?_)
      rintro x ⟨hxM, k, hk⟩
      have hxsup : x ∈ B ⊔ oddCoreIn M := by rw [hBsup]; exact hxM
      have h1 : x ∈ Mg ⊔ oddCoreIn M := (sup_le_sup_right hBD _) hxsup
      exact mem_of_mem_sup_of_le_normalizer (fun o ho => hle (map_subtype_le _ ho))
        (odd_card_oddCoreIn M) h1 (by rw [← hk]; exact pow_orderOf_eq_one x)
    exact Subgroup.eq_of_le_of_card_ge hMMg (by rw [hMg, card_conjugate_eq_card])
  ·
    have hDC : D ≤ coreActionKernel Mg := le_coreActionKernel_of_isPComponent h hM' hDN hDpc hDM
    have hDwC : conjugate D w ≤ coreActionKernel Mg := by
      intro x hx
      rw [mem_conjugate_iff] at hx
      have h1 := hDC hx
      have hwN' : w⁻¹ ∈ normalizer (coreActionKernel Mg : Set G) :=
        normalizer_le_normalizer_coreActionKernel Mg (inv_mem hwNg)
      have h2 := (mem_normalizer_iff.mp hwN' _).mp h1
      rwa [show w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x by group] at h2
    have hBCg : B ≤ coreActionKernel Mg := hBD.trans (sup_le hDC hDwC)
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 B
    have hTM : IsSylowOf 2 T M := by
      rw [isSylowOf_iff] at hT ⊢
      refine ⟨hT.1.trans hBM, hT.2.1, fun hdvd => hT.2.2 ?_⟩
      have hOM : oddCoreIn M ≤ M := map_subtype_le _
      have : ((oddCoreIn M).subgroupOf M).Normal := by
        have h1 : (pPrimeCore 2 ↥M).Normal := inferInstance
        rw [show (oddCoreIn M).subgroupOf M = pPrimeCore 2 ↥M from
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective _]
        exact h1
      have hfac : ∀ b ∈ M, ∃ a ∈ B, ∃ n ∈ oddCoreIn M, b = a * n := by
        intro b hb
        have hBO : B ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G) := fun y hy =>
          mem_normalizer_oddCoreIn (le_normalizer (hBM hy))
        rw [← hBsup] at hb
        have hb' : b ∈ ((B ⊔ oddCoreIn M : Subgroup G) : Set G) := hb
        rw [coe_mul_of_left_le_normalizer_right B (oddCoreIn M) hBO] at hb'
        obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.mp hb'
        exact ⟨a, ha, n, hn, rfl⟩
      have hrel := relIndex_eq_relIndex_inf_of_mul hBM hOM hfac
      have hodd : Odd (B.relIndex M) := by
        rw [hrel]
        exact Odd.of_dvd_nat (odd_card_oddCoreIn M) (Subgroup.relIndex_dvd_card _ _)
      rw [← Subgroup.relIndex_mul_relIndex T B M hT.1 hBM] at hdvd
      exact (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd |>.resolve_right
        (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
    have hTCg : T ≤ coreActionKernel Mg := hT.le.trans hBCg
    obtain ⟨W, hW, hWM⟩ := hM.exists_isKleinFour h
    have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; norm_num)
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hTM hWM hWp
    have hWk : IsKleinFour ↥(conjugate W k) :=
      isKleinFour_of_card_eq_four (by rw [card_conjugate_eq_card, hW.card_four])
        (sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hW hx) k)
    have hNT : normalizer (T : Set G) ≤ normalizer (Mg : Set G) :=
      foote_cor_4_8_iv h h47 hST hM' hTCg hWk (conjugate_le_of_forall hk)
    have hNN : N ≤ normalizer (Mg : Set G) := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := exists_mul_mem_normalizer_of_isSylowOf hTM hx
      rw [show x = x * m * m⁻¹ by group]
      exact mul_mem (hNT hxm) (inv_mem (hle hm))
    have hNeq : N = normalizer (Mg : Set G) :=
      Subgroup.eq_of_le_of_card_ge hNN (by rw [← hNg, card_conjugate_eq_card])
    have hc : ⁅M, Mg⁆ ≤ M ⊓ Mg := by
      rw [commutator_le]
      intro a ha b hb
      have hbN : b ∈ N := hNeq ▸ (le_normalizer hb)
      have h1 : b * a⁻¹ * b⁻¹ ∈ M := (mem_normalizer_iff.mp hbN _).mp (inv_mem ha)
      have h2 : a * b * a⁻¹ ∈ Mg := (mem_normalizer_iff.mp (hle ha) _).mp hb
      rw [commutatorElement_def, mem_inf]
      refine ⟨?_, mul_mem h2 (inv_mem hb)⟩
      rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact mul_mem ha h1
    obtain ⟨F₁, hF₁2, hF₁8, hF₁C⟩ := hM.exists_card_eight h
    obtain ⟨F₂, hF₂2, hF₂8, hF₂C⟩ := hM'.exists_card_eight h
    have hCN : coreActionKernel M ≤ N := fun x hx => (mem_coreActionKernel.mp hx).1
    have hCgN : coreActionKernel Mg ≤ normalizer (Mg : Set G) := fun x hx =>
      (mem_coreActionKernel.mp hx).1
    exact foote_theorem_4_6 h hA5 hE8 hK hcalc hM hM' hc hF₁2 hF₁8
      (le_inf hF₁C (hF₁C.trans (hCN.trans hNeq.le))) hF₂2 hF₂8
      (le_inf hF₂C (hF₂C.trans (hCgN.trans hNeq.symm.le)))

end CFSG.ComponentClassification.FooteLit
