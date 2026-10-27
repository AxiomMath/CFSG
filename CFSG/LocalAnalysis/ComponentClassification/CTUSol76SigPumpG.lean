module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL33

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem pump_moves_of_le (hK : K ∈ kStarComponents N) {u : G} (huQ : u ∈ coreActionKernel K)
    (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)))
    {M : Subgroup G} (hM : IsTwoComponentIn M (centralizer ({u} : Set G))) :
    twoLayerIn (K ⊓ centralizer ({u} : Set G)) ≤ coreActionKernel M ∨
      M ≤ oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)) := by
  obtain ⟨-, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  have hKuL := hKuS.trans (solomonKStarOf_le_twoLayerIn _)
  by_cases h : twoLayerIn (K ⊓ centralizer ({u} : Set G)) ≤ coreActionKernel M
  · exact Or.inl h
  · exact Or.inr ((le_conjClosure_of_not_le_coreActionKernel hM hKuL h).trans hP)

theorem oddCoreIn_pump_le_of_le (hK : K ∈ kStarComponents N) {u : G}
    (huQ : u ∈ coreActionKernel K) (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G))) :
    oddCoreIn (twoLayerIn (K ⊓ centralizer ({u} : Set G))) ≤
      oddCoreIn (centralizer ({u} : Set G)) := by
  obtain ⟨-, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  exact oddCoreIn_le_of_conjClosure_le (hKuS.trans (solomonKStarOf_le_twoLayerIn _)) hP

theorem commutator_le_oddCoreIn_of_le_pump_of_le (hK : K ∈ kStarComponents N) {u : G}
    (huQ : u ∈ coreActionKernel K) (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)))
    {S M : Subgroup G} (hSQ : S ≤ coreActionKernel K) (hSu : S ≤ centralizer ({u} : Set G))
    (hMP : M ≤ oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
      twoLayerIn (K ⊓ centralizer ({u} : Set G))) :
    ⁅M, S⁆ ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  set Cu := centralizer ({u} : Set G) with hCu
  obtain ⟨hKu2, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  have hKuL : twoLayerIn (K ⊓ Cu) ≤ twoLayerIn Cu :=
    hKuS.trans (solomonKStarOf_le_twoLayerIn _)
  have hKuC : twoLayerIn (K ⊓ Cu) ≤ Cu := hKu2.1.trans inf_le_right
  have hOLC : oddCoreIn (twoLayerIn Cu) ≤ Cu := (map_subtype_le _).trans (map_subtype_le _)
  have hCO : Cu ≤ normalizer (oddCoreIn Cu : Set G) := le_normalizer_oddCoreIn Cu
  refine (Subgroup.commutator_mono hMP le_rfl).trans ?_
  refine commutator_sup_le_of_le (hKuL.trans (le_normalizer_oddCoreIn _)) (hOLC.trans hCO)
    (hKuC.trans hCO) ?_ ?_
  · exact (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
      (hSu.trans (le_normalizer_oddCoreIn_twoLayerIn Cu))).trans (oddCoreIn_twoLayerIn_le Cu)
  · exact (commutator_le_oddCoreIn_of_le_coreActionKernel (le_coreActionKernel_pump hSQ hSu)).trans
      (oddCoreIn_pump_le_of_le hK huQ hu2 hP)

theorem component_dichotomy_of_pump_of_le (hK : K ∈ kStarComponents N) {u : G}
    (huQ : u ∈ coreActionKernel K) (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)))
    {S₁ S₂ : Subgroup G} (hS₁p : IsPGroup 2 S₁)
    (hS₁Ku : S₁ ≤ K ⊓ centralizer ({u} : Set G))
    (hS₂Q : S₂ ≤ coreActionKernel K) (hS₂u : S₂ ≤ centralizer ({u} : Set G)) :
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({u} : Set G)) →
      S₁ ≤ coreActionKernel M ∨
        ⁅M, S₂⁆ ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  intro M hM
  rcases pump_moves_of_le hK huQ hu2 hP hM with h | h
  · exact Or.inl ((le_pump_of_isPGroup hK huQ hu2 hS₁p hS₁Ku).trans h)
  · exact Or.inr (commutator_le_oddCoreIn_of_le_pump_of_le hK huQ hu2 hP hS₂Q hS₂u h)

theorem inf_inf_le_oddCoreIn_of_le (hK : K ∈ kStarComponents N) {u : G}
    (huQ : u ∈ coreActionKernel K) (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)))
    {S₁ S₂ : Subgroup G} (hS₁ : S₁ ≠ ⊥) (hS₁e : CFSG.Open.IsElemAbelian 2 S₁) (hS₁K : S₁ ≤ K)
    (hS₁u : S₁ ≤ centralizer ({u} : Set G)) (hS₂ : S₂ ≠ ⊥)
    (hS₂e : CFSG.Open.IsElemAbelian 2 S₂) (hS₂Q : S₂ ≤ coreActionKernel K)
    (hS₂u : S₂ ≤ centralizer ({u} : Set G)) :
    oddCoreIn (centralizer (S₁ : Set G)) ⊓ oddCoreIn (centralizer (S₂ : Set G)) ⊓
        centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  have hbranches := component_dichotomy_of_pump_of_le hK huQ hu2 hP
    (S₁ := S₁) (S₂ := S₂)
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 S₁ hS₁e)
    (le_inf hS₁K hS₁u) hS₂Q hS₂u
  exact inf_inf_le_oddCoreIn_of_component_dichotomy hu2 hS₁ hS₁e hS₁u hS₂ hS₂e hS₂u hbranches

theorem commutator_le_oddCoreIn_of_image_le {T L B : Subgroup G}
    (hLC : L ≤ centralizer (T : Set G)) (hBC : B ≤ centralizer (T : Set G))
    (hBN : B ≤ normalizer (L : Set G))
    (h : (B.subgroupOf (centralizer (T : Set G))).map (GrSLit.Sol25.solπ T) ≤
      centralizer (((L.subgroupOf (centralizer (T : Set G))).map (GrSLit.Sol25.solπ T) :
        Subgroup (GrSLit.Sol25.QC T)) : Set (GrSLit.Sol25.QC T))) :
    ⁅L, B⁆ ≤ oddCoreIn L := by
  refine le_trans ?_ (GrSLit.Sol25.inf_le_oddIn hLC)
  rw [commutator_le]
  intro l hl d hd
  refine mem_inf.mpr ⟨?_, GrSLit.Sol25.commutator_le_of_le_normalizer hBN
    (commutator_mem_commutator hl hd)⟩
  have hd' : (⟨d, hBC hd⟩ : ↥(centralizer (T : Set G))) ∈
      B.subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hd
  have hl' : (⟨l, hLC hl⟩ : ↥(centralizer (T : Set G))) ∈
      L.subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hl
  have hc := mem_centralizer_iff.mp (h (mem_map_of_mem _ hd')) _ (mem_map_of_mem _ hl')
  have h1 : GrSLit.Sol25.solπ T
      ⁅(⟨l, hLC hl⟩ : ↥(centralizer (T : Set G))), ⟨d, hBC hd⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, hc]
    group
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem commutator_eq_self_of_not_le {T L B : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G))))
    (hBC : B ≤ centralizer (T : Set G)) (hBN : B ≤ normalizer (L : Set G))
    (hne : ¬ ⁅L, B⁆ ≤ oddCoreIn L) : ⁅L, B⁆ = L :=
  GrSLit.Sol25.commutator_eq_self_of_image hLC hL hBN fun h =>
    hne (commutator_le_oddCoreIn_of_image_le hLC hBC hBN h)

theorem not_le_of_odd_of_isTwoComponentIn {M C O : Subgroup G} (hM : IsTwoComponentIn M C)
    (hO : Odd (Nat.card O)) : ¬ M ≤ O := by
  intro hle
  obtain ⟨x, hxM, hx2⟩ := Sol76T13.exists_orderOf_eq_two_of_isTwoComponentIn hM
  have h1 : orderOf x ∣ Nat.card O := by
    have h3 := orderOf_dvd_natCard (⟨x, hle hxM⟩ : O)
    rwa [Subgroup.orderOf_mk] at h3
  rw [hx2] at h1
  exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h1)

theorem le_oddCoreIn_of_two_actual_hulls
    {G : Type} [Group G] [Finite G]
    {u b epsilon : G} {V X I J : Subgroup G}
    (hu2 : orderOf u = 2) (hb2 : orderOf b = 2)
    (he2 : orderOf epsilon = 2)
    (hub : u * b = b * u)
    (heb : epsilon * b = b * epsilon)
    (hV2 : IsPGroup 2 V)
    (hVu : V ≤ centralizer ({u} : Set G))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓
      centralizer ({u} : Set G))
    (hVX : V ≤ normalizer (X : Set G))
    (heX : epsilon ∈ normalizer (X : Set G))
    (hXV : ⁅X, V⁆ = X)
    (hI : IsTwoComponentIn I (centralizer ({u} : Set G)))
    (heI : epsilon ∈ I)
    (hIV : ⁅I, V⁆ ≤ oddCoreIn (centralizer ({u} : Set G)))
    (hJ : IsTwoComponentIn J (centralizer ({epsilon} : Set G)))
    (hVJ : V ≤ J)
    (hbJ : b ∈ coreActionKernel J) :
    X ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu := centralizer ({u} : Set G) with hCu
  set Ce := centralizer ({epsilon} : Set G) with hCe
  have hbu : b ∈ Cu := mem_centralizer_singleton_iff.mpr hub.symm
  have hVe : V ≤ Ce := hVJ.trans hJ.1
  have hSe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hb2)
  have hS1 := zpowers_ne_bot_of_orderOf_eq_two hb2
  have hTe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hu2)
  have hT1 := zpowers_ne_bot_of_orderOf_eq_two hu2
  have hSTu : zpowers b ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact zpowers_le.mpr hbu
  have h25u := sol25 hS1 hT1 hSe hTe hSTu
  rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h25u
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (hX.trans inf_le_left))
      (coprime_card_oddCoreIn _))
  have hCuO : Cu ≤ normalizer (oddCoreIn Cu : Set G) := le_normalizer_oddCoreIn Cu
  have hCeO : Ce ≤ normalizer (oddCoreIn Ce : Set G) := le_normalizer_oddCoreIn Ce
  have hXCu : X ≤ Cu := hX.trans inf_le_right
  have hXI : X ≤ normalizer (I : Set G) := hX.trans (h25u.2 I hI).1
  have hIX : ⁅I, X⁆ ≤ oddCoreIn Cu :=
    commutator_le_of_eq_commutator hXI (hXCu.trans hCuO) (hVu.trans hCuO)
      (hI.1.trans hCuO) hIV hXV
  have hXeps : ⁅X, zpowers epsilon⁆ ≤ oddCoreIn Cu ⊓ X := by
    rw [commutator_le]
    intro x hx g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [← zpow_mod_orderOf, he2]
    have hk : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk with hk | hk
    · rw [hk, zpow_zero, commutatorElement_one_right]
      exact one_mem _
    · rw [hk, zpow_one]
      have h1 : ⁅epsilon, x⁆ ∈ oddCoreIn Cu := hIX (commutator_mem_commutator heI hx)
      have e1 : ⁅x, epsilon⁆ = ⁅epsilon, x⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      refine ⟨by rw [e1]; exact (oddCoreIn Cu).inv_mem h1, ?_⟩
      rw [commutatorElement_def]
      have h2 : epsilon * x⁻¹ * epsilon⁻¹ ∈ X :=
        (mem_normalizer_iff.mp heX _).mp (inv_mem hx)
      have e2 : x * epsilon * x⁻¹ * epsilon⁻¹ = x * (epsilon * x⁻¹ * epsilon⁻¹) := by
        group
      rw [e2]
      exact mul_mem hx h2
  set Xe := ⁅X ⊓ Ce, V⁆ with hXe
  have hzEps2 : IsPGroup 2 (zpowers epsilon) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one])
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers epsilon) X hzEps2 (zpowers_le.mpr heX)
    (Nat.coprime_two_left.mpr hXodd)
  rw [centralizer_zpowers_eq] at hfac
  have hX1 : X ≤ (oddCoreIn Cu ⊓ X) ⊔ (X ⊓ Ce) :=
    hfac.symm.le.trans (sup_le_sup_right hXeps _)
  have hVXe : V ≤ normalizer ((X ⊓ Ce : Subgroup G) : Set G) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hVX hv), mem_normalizer_iff.mp (le_normalizer
      (hVe hv))]
  have hXeX : Xe ≤ X ⊓ Ce :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ V hVXe
  have hAXN : X ⊓ Ce ≤ normalizer ((oddCoreIn Cu ⊓ X : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hCuO (hXCu hx.1)),
      mem_normalizer_iff.mp (le_normalizer hx.1)]
  have hXeNfac : X ⊓ Ce ≤ normalizer (Xe : Set G) := by
    have h1 := (normal_subgroupOf_iff_le_normalizer (commutator_le_sup (X ⊓ Ce) V)).mp
      (commutator_normal_in_sup (X ⊓ Ce) V)
    exact le_sup_left.trans h1
  have hVA : V ≤ normalizer ((oddCoreIn Cu ⊓ X : Subgroup G) : Set G) := fun v hv => by
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hCuO (hVu hv)), mem_normalizer_iff.mp (hVX hv)]
  have hX2 : X ≤ (oddCoreIn Cu ⊓ X) ⊔ Xe := by
    have h1 : ⁅(oddCoreIn Cu ⊓ X) ⊔ (X ⊓ Ce), V⁆ ≤ (oddCoreIn Cu ⊓ X) ⊔ Xe :=
      commutator_sup_le_of_le hAXN (le_sup_left.trans le_normalizer)
        (le_normalizer_sup hAXN hXeNfac)
        ((CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ V hVA).trans
          le_sup_left)
        le_sup_right
    calc X = ⁅X, V⁆ := hXV.symm
      _ ≤ ⁅(oddCoreIn Cu ⊓ X) ⊔ (X ⊓ Ce), V⁆ := Subgroup.commutator_mono hX1 le_rfl
      _ ≤ (oddCoreIn Cu ⊓ X) ⊔ Xe := h1
  have hXeD : Xe ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ Ce :=
    le_inf ((hXeX.trans inf_le_left).trans (hX.trans inf_le_left))
      (hXeX.trans inf_le_right)
  have hXeV : ⁅Xe, V⁆ = Xe :=
    CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2
      (Odd.of_dvd_nat hXodd (Subgroup.card_dvd_of_le inf_le_left)) hVXe
  have hXeO : Xe ≤ oddCoreIn Ce := by
    refine le_oddCoreIn_of_component_dichotomy he2 hb2 heb hVe hXeD hXeV ?_
    exact component_dichotomy_of_actual_hull_kernel hJ (zpowers_le.mpr hbJ) hVJ
  have hE : ∀ M : Subgroup G, IsTwoComponentIn M Cu → ⁅M, X⁆ ≤ oddCoreIn Cu := by
    intro M hM
    by_cases hMI : M = I
    · subst hMI
      exact hIX
    · have hIM : I ≤ coreActionKernel M :=
        CFSG.ComponentClassification.GSThmB.B5a.le_coreActionKernel_of_ne
          hM.1 hI.1 hM.2 hI.2 hMI
      have hepsM : epsilon ∈ coreActionKernel M := hIM heI
      have hXeNM : Xe ≤ normalizer (M : Set G) :=
        (hXeX.trans inf_le_left).trans (hX.trans (h25u.2 M hM).1)
      have hMXe : ⁅M, Xe⁆ ≤ oddCoreIn M := by
        by_contra hn
        have hCT : centralizer ((zpowers u : Subgroup G) : Set G) = Cu :=
          centralizer_zpowers_eq u
        have hM' : IsTwoComponentIn M (centralizer ((zpowers u : Subgroup G) : Set G)) := by
          rw [hCT]; exact hM
        have hXeC : Xe ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
          rw [hCT]; exact (hXeX.trans inf_le_left).trans hXCu
        have heq := commutator_eq_self_of_not_le hM'.1 hM'.2 hXeC hXeNM hn
        have hcov := inf_centralizer_sup_oddCoreIn_eq hzEps2 (zpowers_le.mpr hepsM)
        rw [centralizer_zpowers_eq] at hcov
        set O' := oddCoreIn M ⊔ (M ⊓ oddCoreIn Ce) with hO'
        have hMCeO : M ⊓ Ce ≤ normalizer (oddCoreIn M : Set G) :=
          inf_le_left.trans (le_normalizer_oddCoreIn M)
        have hO'odd : Odd (Nat.card O') := odd_card_sup_of_le_normalizer
          (inf_le_left.trans (le_normalizer_oddCoreIn M))
          (Nat.coprime_two_left.mp (coprime_card_oddCoreIn M))
          (Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
            (Subgroup.card_dvd_of_le inf_le_right) (coprime_card_oddCoreIn Ce)))
        have hMCeN : M ⊓ Ce ≤ normalizer ((M ⊓ oddCoreIn Ce : Subgroup G) : Set G) := by
          intro m hm
          rw [mem_normalizer_iff]
          intro y
          rw [mem_inf, mem_inf, mem_normalizer_iff.mp (le_normalizer hm.1),
            mem_normalizer_iff.mp (hCeO hm.2)]
        have hle : ⁅oddCoreIn M ⊔ (M ⊓ Ce), Xe⁆ ≤ O' := by
          refine commutator_sup_le_of_le hMCeO (le_sup_left.trans le_normalizer)
            (le_normalizer_sup hMCeO hMCeN) ?_ ?_
          · exact (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
              (fun x hx => mem_normalizer_oddCoreIn (hXeNM hx))).trans le_sup_left
          · refine le_trans ?_ le_sup_right
            rw [commutator_le]
            intro m hm x hx
            refine ⟨?_, ?_⟩
            · rw [commutatorElement_def]
              have h1 : x * m⁻¹ * x⁻¹ ∈ M :=
                (mem_normalizer_iff.mp (hXeNM hx) _).mp (inv_mem hm.1)
              have e1 : m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) := by group
              rw [e1]
              exact mul_mem hm.1 h1
            · rw [commutatorElement_def]
              have hxO : x ∈ oddCoreIn Ce := hXeO hx
              have h1 : m * x * m⁻¹ ∈ oddCoreIn Ce :=
                (mem_normalizer_iff.mp (hCeO hm.2) x).mp hxO
              exact (oddCoreIn Ce).mul_mem h1 ((oddCoreIn Ce).inv_mem hxO)
        have hMle : M ≤ O' := by
          calc M = ⁅M, Xe⁆ := heq.symm
            _ = ⁅oddCoreIn M ⊔ (M ⊓ Ce), Xe⁆ := by rw [sup_comm, hcov]
            _ ≤ O' := hle
        exact not_le_of_odd_of_isTwoComponentIn hM hO'odd hMle
      rw [commutator_comm]
      refine (Subgroup.commutator_mono hX2 le_rfl).trans ?_
      have hXeOCu : Xe ≤ normalizer ((oddCoreIn Cu ⊓ X : Subgroup G) : Set G) :=
        (hXeX.trans inf_le_left).trans fun x hx => by
          rw [mem_normalizer_iff]
          intro y
          rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hCuO (hXCu hx)),
            mem_normalizer_iff.mp (le_normalizer hx)]
      refine commutator_sup_le_of_le hXeOCu ((inf_le_right.trans hXCu).trans hCuO)
        (((hXeX.trans inf_le_left).trans hXCu).trans hCuO) ?_ ?_
      · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
          (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
            (hM.1.trans hCuO))
      · rw [commutator_comm]
        exact hMXe.trans (oddCoreIn_le_of_isTwoComponentIn hM)
  exact le_oddCoreIn_of_commutator_le hXCu hXodd
    ((Subgroup.commutator_mono le_rfl hX).trans h25u.1) hE

theorem le_oddCoreIn_of_pump_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {u b ε : G} (huK' : u ∈ K')
    (hu2 : orderOf u = 2) (hb2 : orderOf b = 2) (hbQ : b ∈ coreActionKernel K')
    (hub : u * b = b * u) (hεK : ε ∈ K) (hε2 : orderOf ε = 2) (hεb : ε * b = b * ε)
    (hεu : ε * u = u * ε) {V X : Subgroup G} (hVK' : V ≤ K') (hV2 : IsPGroup 2 V)
    (hVu : V ≤ centralizer ({u} : Set G)) (hVε : V ≤ centralizer ({ε} : Set G))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({u} : Set G))
    (hVX : V ≤ normalizer (X : Set G)) (hεX : ε ∈ normalizer (X : Set G)) (hXV : ⁅X, V⁆ = X) :
    X ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  set Cu := centralizer ({u} : Set G) with hCu
  set Ce := centralizer ({ε} : Set G) with hCe
  have huQ : u ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm huK'
  have heQ : ε ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne hεK
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hPb := h32 G hG N hN K' hK' K hK hne.symm u huK' hu2
  obtain ⟨I, hIpump, hIsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne huK' hu2
  obtain ⟨J, hJpump, hJsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK' hK hne.symm hεK hε2
  obtain ⟨hPuComp, -, -, -, -⟩ := pump_facts hK huQ hu2
  obtain ⟨hPeComp, -, -, -, -⟩ := pump_facts hK' heQ hε2
  have hPuPerf : ⁅twoLayerIn (K ⊓ Cu), twoLayerIn (K ⊓ Cu)⁆ =
      twoLayerIn (K ⊓ Cu) :=
    UnbalancedCorr.commutator_eq_of_isPComponent hPuComp.1 hPuComp.2
  have hPePerf : ⁅twoLayerIn (K' ⊓ Ce), twoLayerIn (K' ⊓ Ce)⁆ =
      twoLayerIn (K' ⊓ Ce) :=
    UnbalancedCorr.commutator_eq_of_isPComponent hPeComp.1 hPeComp.2
  have hPu_le : twoLayerIn (K ⊓ Cu) ≤ I ⊔ oddCoreIn Cu :=
    (le_sup_left.trans hIsup.le).trans (sup_le_sup_left (oddCoreIn_twoLayerIn_le Cu) I)
  have hPe_le : twoLayerIn (K' ⊓ Ce) ≤ J ⊔ oddCoreIn Ce :=
    (le_sup_left.trans hJsup.le).trans (sup_le_sup_left (oddCoreIn_twoLayerIn_le Ce) J)
  have hOCuN : oddCoreIn Cu ≤ normalizer (I : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hIpump.1.1.1 hIpump.1.1.2
  have hOCeN : oddCoreIn Ce ≤ normalizer (J : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJpump.1.1.1 hJpump.1.1.2
  have hstrengthen {P M C : Subgroup G} (hPperf : ⁅P, P⁆ = P)
      (hPMO : P ≤ M ⊔ oddCoreIn C) (hOM : oddCoreIn C ≤ normalizer (M : Set G)) :
      P ≤ M :=
    le_of_perfect_of_le_sup hPperf (hPMO.trans (sup_le le_normalizer hOM)) hOM
      (Nat.coprime_two_left.mp (coprime_card_oddCoreIn C)) hPMO
  have hPuI : twoLayerIn (K ⊓ Cu) ≤ I := hstrengthen hPuPerf hPu_le hOCuN
  have hPeJ : twoLayerIn (K' ⊓ Ce) ≤ J := hstrengthen hPePerf hPe_le hOCeN
  have hεI : ε ∈ I := hPuI (mem_pump_of_two hK huQ hu2
    ⟨hεK, mem_centralizer_singleton_iff.mpr hεu⟩ (k := 1) (by rw [hε2, pow_one]))
  have hVJ : V ≤ J :=
    (le_pump_of_isPGroup hK' heQ hε2 hV2 (le_inf hVK' hVε)).trans hPeJ
  have hI_le : I ≤ oddCoreIn (twoLayerIn Cu) ⊔ twoLayerIn (K ⊓ Cu) := by
    rw [sup_comm]
    exact (le_sup_left : I ≤ I ⊔ oddCoreIn (twoLayerIn Cu)).trans hIsup.symm.le
  have hIV : ⁅I, V⁆ ≤ oddCoreIn Cu :=
    commutator_le_oddCoreIn_of_le_pump_of_le hK huQ hu2 hPb hVQ hVu hI_le
  have hbJ : b ∈ coreActionKernel J :=
    mem_coreActionKernel_pump hq hR1 hG hN hK' hK hne.symm hεK hε2 hbQ hεb.symm hJpump
  exact le_oddCoreIn_of_two_actual_hulls hu2 hb2 hε2 hub hεb hV2 hVu
    hX hVX hεX hXV hIpump.1.1 hεI hIV hJpump.1.1 hVJ hbJ


end CFSG.ComponentClassification.Sol76.Sig
