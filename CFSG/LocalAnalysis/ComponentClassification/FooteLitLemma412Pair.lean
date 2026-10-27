module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInnerRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCor48
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution_commute_of_even {X : Subgroup G} (hX : Even (Nat.card X)) {u : G}
    (hu : u ^ 2 = 1) (huX : u ∈ normalizer (X : Set G)) :
    ∃ w ∈ X, orderOf w = 2 ∧ w * u = u * w := by
  have huu : u * u = 1 := by rw [← sq]; exact hu
  have hmem : ∀ x ∈ X, u * x * u⁻¹ ∈ X := fun x hx => (mem_normalizer_iff.mp huX x).mp hx
  have hinv : ∀ x : G, u * (u * x * u⁻¹) * u⁻¹ = x := fun x => by
    calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ := by group
      _ = x := by rw [huu]; group
  let σ : Equiv.Perm X :=
    { toFun := fun x => ⟨u * x * u⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨u * x * u⁻¹, hmem x x.2⟩
      left_inv := fun x => Subtype.ext (hinv x)
      right_inv := fun x => Subtype.ext (hinv x) }
  have hσ : Function.Involutive σ := fun x => Subtype.ext (hinv x)
  have hmod := card_fixed_mod_two_of_involutive σ hσ
  set F := X ⊓ centralizer ({u} : Set G) with hF
  have e : {x : X // σ x = x} ≃ F :=
    { toFun := fun x => ⟨x.1, x.1.2, mem_centralizer_singleton_iff.mpr (by
        have h1 : u * x.1 * u⁻¹ = x.1 := congrArg Subtype.val x.2
        calc (x.1 : G) * u = u * x.1 * u⁻¹ * u := by rw [h1]
          _ = u * x.1 := by group)⟩
      invFun := fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, Subtype.ext (by
        have h1 : (x.1 : G) * u = u * x.1 := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
        show u * x.1 * u⁻¹ = x.1
        rw [← h1]
        group)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hFeven : Even (Nat.card F) := by
    rw [← Nat.card_congr e, Nat.even_iff, hmod, ← Nat.even_iff]
    exact hX
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 2 (even_iff_two_dvd.mp hFeven)
  refine ⟨w, (mem_inf.mp w.2).1, (Subgroup.orderOf_coe w).trans hw,
    mem_centralizer_singleton_iff.mp (mem_inf.mp w.2).2⟩

theorem IsFooteM.isPComponent_normalizer (h : FooteSec4 G L) {M : Subgroup G}
    (hM : IsFooteM L M) : IsPComponent 2 (M.subgroupOf (normalizer (M : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set G) with hN
  have hMN : M ≤ N := le_normalizer
  set X := M.subgroupOf N with hX
  have eX : ↥X ≃* ↥M := subgroupOfEquivOfLe hMN
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
  refine ⟨?_, ?_, ?_⟩
  · have : X.Normal := (normal_subgroupOf_iff_le_normalizer hMN).mpr le_rfl
    exact this.isSubnormal
  ·
    have hres : CatalogueBPrimeJoin.primeResidual 2 ↥M = ⊤ := by
      have hle : M ≤ (CatalogueBPrimeJoin.primeResidual 2 ↥M).map M.subtype := by
        refine (hM.le_oddResidualIn h).trans ((closure_le _).mpr ?_)
        rintro g ⟨hgM, k, hk⟩
        refine ⟨⟨g, hgM⟩, ?_, rfl⟩
        refine CatalogueBPrimeJoin.pSubgroup_le_residual 2 (zpowers ⟨g, hgM⟩) ?_ (mem_zpowers _)
        refine IsPGroup.of_card (n := k) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk]
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hle x.2
      rw [← Subtype.ext hyx]
      exact hy
    rw [eq_top_iff]
    intro x _
    have h1 := (CatalogueBPrimeJoin.primeResidual_map_equiv 2 eX.symm) ▸
      (mem_map_of_mem eX.symm.toMonoidHom (hres ▸ mem_top (eX x)))
    simpa using h1
  ·
    obtain ⟨hs, -⟩ := hM.quotient h
    obtain ⟨a, b, hab⟩ := hM.exists_mul_ne h
    have e : ↥X ⧸ pPrimeCore 2 ↥X ≃* ↥M ⧸ pPrimeCore 2 ↥M :=
      QuotientGroup.congr _ _ eX (CFSG.pPrimeCore_map_iso 2 eX)
    have : IsSimpleGroup (↥X ⧸ pPrimeCore 2 ↥X) := e.isSimpleGroup_congr.mpr hs
    refine isQuasisimple_of_isSimpleGroup' ⟨e.symm a, e.symm b, fun h1 => hab ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, h1]

theorem le_coreActionKernel_of_isPComponent (h : FooteSec4 G L) {M : Subgroup G}
    (hM : IsFooteM L M) {B : Subgroup G} (hBN : B ≤ normalizer (M : Set G))
    (hB : IsPComponent 2 (B.subgroupOf (normalizer (M : Set G))))
    (hne : B ≠ M) : B ≤ coreActionKernel M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set G) with hN
  have hMN : M ≤ N := le_normalizer
  have hMpc := hM.isPComponent_normalizer h
  have hne' : B.subgroupOf N ≠ M.subgroupOf N := fun h1 => hne (by
    have h2 := subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hBN, inf_eq_left.mpr hMN] at h2)
  obtain ⟨-, -, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hB hMpc).2 hne'
  set eM : ↥(M.subgroupOf N) ≃* ↥M := subgroupOfEquivOfLe hMN with heM
  have hO : ∀ y : ↥(M.subgroupOf N), y ∈ pPrimeCore 2 ↥(M.subgroupOf N) →
      (eM y : G) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    intro y hy
    refine ⟨eM y, ?_, rfl⟩
    rw [← CFSG.pPrimeCore_map_iso 2 eM]
    exact mem_map_of_mem _ hy
  intro b hb
  refine mem_coreActionKernel.mpr ⟨hBN hb, fun m hm => ?_⟩
  have h1 : ⁅(⟨m, hMN hm⟩ : N)⁻¹, (⟨b, hBN hb⟩ : N)⁻¹⁆ ∈ ⁅B.subgroupOf N, M.subgroupOf N⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (inv_mem (show (⟨m, hMN hm⟩ : N) ∈ M.subgroupOf N from hm))
      (inv_mem (show (⟨b, hBN hb⟩ : N) ∈ B.subgroupOf N from hb))
  have h2 := (hcomm h1).2
  obtain ⟨y, hy, hyc⟩ := mem_map.mp h2
  have h3 := hO y hy
  have h4 : (eM y : G) = m⁻¹ * b⁻¹ * m * b := by
    have := congrArg Subtype.val hyc
    simp only [subtype_apply, commutatorElement_def, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    rw [← this, heM, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [← h4]
  exact h3

@[expose] def FooteBadPair (M : Subgroup G) (z g : G) : Prop :=
  orderOf z = 2 ∧ z ∈ coreActionKernel M ∧ centralizer ({z} : Set G) ≤ normalizer (M : Set G) ∧
    g⁻¹ * z * g ∈ normalizer (M : Set G) ∧ g ∉ normalizer (M : Set G)

omit [Finite G] in
theorem FooteBadPair.centralizer_le {M : Subgroup G} {z g : G} (hp : FooteBadPair M z g) :
    centralizer ({g⁻¹ * z * g} : Set G) ≤ conjugate (normalizer (M : Set G)) g := by
  intro x hx
  rw [mem_conjugate_iff]
  apply hp.2.2.1
  rw [mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hx]
    _ = z * (g * x * g⁻¹) := by group

omit [Finite G] in
theorem FooteBadPair.mem_coreActionKernel_conjugate {M : Subgroup G} {z g : G}
    (hp : FooteBadPair M z g) : g⁻¹ * z * g ∈ coreActionKernel (conjugate M g) := by
  apply CFSG.ComponentClassification.FooteLit.mem_coreActionKernel_conjugate
  rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
  exact hp.2.1

omit [Finite G] in
theorem FooteBadPair.orderOf_conj {M : Subgroup G} {z g : G} (hp : FooteBadPair M z g) :
    orderOf (g⁻¹ * z * g) = 2 := by
  rw [show g⁻¹ * z * g = MulAut.conj g⁻¹ z by rw [MulAut.conj_apply, inv_inv],
    MulEquiv.orderOf_eq, hp.1]

theorem FooteBadPair.false_of_involution (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {z g : G}
    (hp : FooteBadPair M z g) {w : G} (hw : orderOf w = 2) (hwC : w ∈ coreActionKernel M)
    (hwCg : w ∈ coreActionKernel (conjugate M g))
    (hwu : w * (g⁻¹ * z * g) = (g⁻¹ * z * g) * w) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' := isFooteM_conjugate h hM g
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM w hw hwC)
  obtain ⟨hBM, hBsup⟩ := footeF_le_of_card_eight h hM hw hwC hF2 hF8 hF
  obtain ⟨F', hF', hF'2, hF'8⟩ := exists_card_eight_of_le_pRank (h47 G L h _ hM' w hw hwCg)
  obtain ⟨hBM', -⟩ := footeF_le_of_card_eight h hM' hw hwCg hF'2 hF'8 hF'
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM hw hwC
  have hBN : centralizer ({w} : Set G) ≤ normalizer (footeF L w : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  have huw : g⁻¹ * z * g ∈ centralizer ({w} : Set G) :=
    mem_centralizer_singleton_iff.mpr hwu.symm
  have huB : g⁻¹ * z * g ∈ coreActionKernel (footeF L w) :=
    mem_coreActionKernel_of_le hBM' (hBN huw) hp.mem_coreActionKernel_conjugate
  have huC : g⁻¹ * z * g ∈ coreActionKernel M :=
    mem_coreActionKernel_of_sup hBM hBsup hp.2.2.2.1 huB
  obtain ⟨n, hn, c, hc, hgnc⟩ := foote_cor_4_8_iii h h47 hST hM hp.orderOf_conj huC
    hp.mem_coreActionKernel_conjugate
  apply hp.2.2.2.2
  have hcN := hp.centralizer_le hc
  rw [mem_conjugate_iff] at hcN
  have hgc : g * c * g⁻¹ = g * n⁻¹ := by rw [hgnc]; group
  rw [hgc] at hcN
  rw [show g = g * n⁻¹ * n by group]
  exact mul_mem hcN hn

theorem FooteBadPair.false_of_le (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M) {z g : G}
    (hp : FooteBadPair M z g) (hle : M ≤ normalizer (conjugate M g : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set G) with hN
  set Mg := conjugate M g with hMg
  have hM' := isFooteM_conjugate h hM g
  have hNg : conjugate N g = normalizer (Mg : Set G) := conjugate_normalizer M g
  have hfin : M = Mg → False := fun heq => hp.2.2.2.2 (mem_normalizer_of_conjugate_eq heq.symm)
  obtain ⟨F₀, hF₀2, hF₀8, hF₀C⟩ := hM.exists_card_eight h
  have hCeven : Even (Nat.card (coreActionKernel M)) := by
    refine even_iff_two_dvd.mpr ((show 2 ∣ 8 by norm_num).trans ?_)
    rw [← hF₀8]
    exact Subgroup.card_dvd_of_le hF₀C
  have hu2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    rw [← hp.orderOf_conj]
    exact pow_orderOf_eq_one _
  obtain ⟨w, hwC, hw, hwu⟩ := exists_involution_commute_of_even hCeven hu2
    (normalizer_le_normalizer_coreActionKernel M hp.2.2.2.1)
  have hwNg : w ∈ normalizer (Mg : Set G) :=
    hNg ▸ hp.centralizer_le (mem_centralizer_singleton_iff.mpr hwu)
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
    exact hfin (Subgroup.eq_of_le_of_card_ge hMMg (by rw [hMg, card_conjugate_eq_card]))
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
    exact hfin (foote_theorem_4_6 h hA5 hE8 hK hcalc hM hM' hc hF₁2 hF₁8
      (le_inf hF₁C (hF₁C.trans (hCN.trans hNeq.le))) hF₂2 hF₂8
      (le_inf hF₂C (hF₂C.trans (hCgN.trans hNeq.symm.le))))

@[expose] def FooteEvenOrNormalizes (M : Subgroup G) : Prop :=
  ∀ g : G, ∀ E : Subgroup G, E ≤ coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G) →
    (∀ x ∈ E, x ^ 2 = 1) → Nat.card E = 8 →
    (∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2) ∨
      M ≤ normalizer (conjugate M g : Set G)

theorem FooteBadPair.false_of_card_eight (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M)
    (hPE : FooteEvenOrNormalizes M) {z g : G} (hp : FooteBadPair M z g) {E : Subgroup G}
    (hE : E ≤ coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8' : Nat.card E = 8) : False := by
  rcases hPE g E hE hE2 hE8' with ⟨x, hx, hx2⟩ | hle
  · set X := coreActionKernel M ⊓ coreActionKernel (conjugate M g) with hX
    have hXeven : Even (Nat.card X) := by
      refine even_iff_two_dvd.mpr ?_
      have h1 := Subgroup.orderOf_dvd_natCard X hx
      rwa [hx2] at h1
    have hu2 : (g⁻¹ * z * g) ^ 2 = 1 := by
      rw [← hp.orderOf_conj]
      exact pow_orderOf_eq_one _
    have hu1 := normalizer_le_normalizer_coreActionKernel M hp.2.2.2.1
    have hu2' : g⁻¹ * z * g ∈ normalizer (coreActionKernel (conjugate M g) : Set G) :=
      le_normalizer hp.mem_coreActionKernel_conjugate
    have huX : g⁻¹ * z * g ∈ normalizer (X : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [hX, mem_inf, mem_inf, ← mem_normalizer_iff.mp hu1 y, ← mem_normalizer_iff.mp hu2' y]
    obtain ⟨w, hwX, hw, hwu⟩ := exists_involution_commute_of_even hXeven hu2 huX
    exact hp.false_of_involution h h47 hST hM hw (mem_inf.mp hwX).1 (mem_inf.mp hwX).2 hwu
  · exact hp.false_of_le h h47 hST hA5 hE8 hK hcalc hM hle

end CFSG.ComponentClassification.FooteLit
