module

public import CFSG.ClassicalInvolution.Q3.TL3T27

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_member_card_of_mem_USet (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ L ∈ Ω, U ≤ L ∧ Nat.card L = 2 * Nat.card U ∧ 4 ≤ Nat.card U := by
  obtain ⟨R, -, L, hL, hRL, hUR, -, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨hRL1, -, hRL3⟩ := hRL
  have hRL' : L = R := hRL3 L le_rfl (h2 L hL) hRL1
  refine ⟨L, hL, hRL' ▸ hUR, ?_, h4⟩
  rw [hRL']
  exact hcard

theorem wSet_eq_singleton_of_normal (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (htr : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤)
    (hns : ¬ ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L') {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWn : W.Normal) : WSet Ω = {W} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨η, hη, rfl⟩ := hW
  have hηG := hη
  obtain ⟨S, hηS, -⟩ := hη
  have hW2 : IsPGroup 2 ↥(etaSpan η) := etaSpan_isPGroup hηG
  have hmeet : ∀ (S' : Sylow 2 G), ∀ M ∈ Ω, (∀ V ∈ η, V ≤ (S' : Subgroup G)) →
      2 < Nat.card ↥(M ⊓ (S' : Subgroup G)) → M ⊓ etaSpan η ∈ η := by
    intro S' M hM hηS' hcard
    exact Sec6Gen.l6_11Gen G Ω hΩ S' η hηG hηS' M hM hcard
  have hWn' : (etaSpan η).Normal := hWn
  have hWS' : ∀ S' : Sylow 2 G, etaSpan η ≤ (S' : Subgroup G) := fun S' =>
    hW2.le_sylow_of_normal S'
  have hηle : ∀ S' : Sylow 2 G, ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun S' V hV =>
    (le_etaSpan hV).trans (hWS' S')
  have hMW : ∀ M ∈ Ω, M ⊓ etaSpan η ∈ η := by
    intro M hM
    obtain ⟨S', hMS'⟩ := (h2 M hM).exists_le_sylow
    refine hmeet S' M hM (hηle S') ?_
    rw [inf_eq_left.mpr hMS']
    have := (Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hM (h2 M hM))).eight_le
    omega
  ext W'
  simp only [Set.mem_singleton_iff]
  constructor
  swap
  · rintro rfl
    exact ⟨η, hηG, rfl⟩
  rintro ⟨η', hη', rfl⟩
  have hη'G := hη'
  obtain ⟨S', hη'S', hinv'⟩ := hη'
  have hW'2 : IsPGroup 2 ↥(etaSpan η') := etaSpan_isPGroup hη'G
  have hWcomm := etaSpan_comm hΩ hηG
  have hW'comm := etaSpan_comm hΩ hη'G
  have hMW' : ∀ M ∈ Ω, M ⊓ etaSpan η' ∈ η' := by
    intro M hM
    have hle : M ⊓ etaSpan η ≤ M ⊓ (S' : Subgroup G) := inf_le_inf_left _ (hWS' S')
    obtain ⟨-, -, -, -, h4⟩ := exists_member_card_of_mem_USet hΩ h2 (hηS.1 (hMW M hM)).1
    refine Sec6Gen.l6_11Gen G Ω hΩ S' η' hη'G (fun V hV => (hη'S'.1 hV).2) M hM ?_
    have := Subgroup.card_le_of_le hle
    omega
  have hinvW : ∀ M ∈ Ω, ∀ m : G, IsUniqueInvolution M m → m ∈ etaSpan η ∧ m ∈ etaSpan η' := by
    intro M hM m hm
    obtain ⟨L₁, hL₁, hUL₁, -, h4⟩ := exists_member_card_of_mem_USet hΩ h2 (hηS.1 (hMW M hM)).1
    obtain ⟨L₂, hL₂, hUL₂, -, h4'⟩ := exists_member_card_of_mem_USet hΩ h2 (hη'S'.1 (hMW' M hM)).1
    exact ⟨(hm.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)).2,
      (hm.mem_of_le inf_le_left (hW'2.to_le inf_le_right) (by omega)).2⟩
  have hsub : η' ⊆ η := by
    intro U' hU'
    obtain ⟨L, hL, hU'L, hcardL, h4⟩ := exists_member_card_of_mem_USet hΩ h2 (hη'S'.1 hU').1
    have hU'eq : U' = L ⊓ etaSpan η' := by
      by_contra hne
      exact hη'S'.2.1 U' hU' _ (hMW' L hL) hne L hL ⟨hU'L, inf_le_left⟩
    by_contra hU'η
    have hne : U' ≠ L ⊓ etaSpan η := fun h => hU'η (h ▸ hMW L hL)
    obtain ⟨L', hL', hUL', hcardL', h4U⟩ := exists_member_card_of_mem_USet hΩ h2 (hηS.1 (hMW L hL)).1
    have hUc : IsCyclic ↥(L ⊓ etaSpan η) := by
      obtain ⟨R, -, -, -, -, -, hc, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 (hMW L hL)).1
      exact hc
    have hU'c : IsCyclic ↥U' := by
      obtain ⟨R, -, -, -, -, -, hc, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hη'S'.1 hU').1
      exact hc
    have hUW : ∀ v ∈ L ⊓ etaSpan η, v ∈ etaSpan η := fun v hv => hv.2
    have hU'W : ∀ v ∈ U', v ∈ etaSpan η' := fun v hv => (hU'eq ▸ hv : v ∈ L ⊓ etaSpan η').2
    have hUL : L ⊓ etaSpan η ≤ L := inf_le_left
    set U := L ⊓ etaSpan η with hUdef
    clear_value U
    have hq : IsQuatSub L := Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hL (h2 L hL))
    have hLL' : L' = L := by
      by_contra hne'
      have h1 := (hΩ.omega4 L hL L' hL' (Ne.symm hne')).1
      have hle : U ≤ L ⊓ L' := le_inf hUL hUL'
      have hLL'2 : IsPGroup 2 ↥(L ⊓ L') := (h2 L hL).to_le inf_le_left
      obtain ⟨k, hk⟩ := hLL'2.exists_card_eq
      have hcard := Subgroup.card_le_of_le hle
      rw [hk] at h1 hcard
      rw [padicValNat.prime_pow] at h1
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    subst hLL'
    have hcU' : Nat.card U = Nat.card U' := by omega
    have hU'U : ¬ U' ≤ U := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by omega))
    have hsupL : U ⊔ U' = L' := by
      have hle : U ⊔ U' ≤ L' := sup_le hUL hU'L
      have hlt : U < U ⊔ U' := lt_of_le_of_ne le_sup_left fun h => hU'U (h ▸ le_sup_right)
      have hc1 := Subgroup.card_lt_of_lt hlt
      have hdvd : Nat.card U ∣ Nat.card ↥(U ⊔ U') := Subgroup.card_dvd_of_le le_sup_left
      have hdvd' : Nat.card ↥(U ⊔ U') ∣ Nat.card L' := Subgroup.card_dvd_of_le hle
      obtain ⟨a, ha⟩ := hdvd
      obtain ⟨b, hb⟩ := hdvd'
      have hU0 : 0 < Nat.card U := Nat.card_pos
      have hab : a * b = 2 := by
        have h' : Nat.card U * (a * b) = Nat.card U * 2 := by
          rw [← mul_assoc, ← ha, ← hb, hcardL']
          ring
        exact Nat.eq_of_mul_eq_mul_left hU0 h'
      have ha1 : 2 ≤ a := by
        by_contra h
        push Not at h
        interval_cases a <;> omega
      have hb1 : b = 1 := by
        rcases Nat.lt_or_ge b 2 with h | h
        · interval_cases b <;> omega
        · have : 2 * 2 ≤ a * b := Nat.mul_le_mul ha1 h
          omega
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hb, hb1, mul_one])
    have hcycN : ∀ (V : Subgroup G), V ≤ L' → IsCyclic ↥V → 4 ≤ Nat.card V →
        ∀ M ∈ Ω, M ≠ L' → ∀ m : G, IsUniqueInvolution M m →
          (∀ v ∈ V, v * m = m * v) → V ≤ Subgroup.normalizer (M : Set G) := by
      intro V hVL hVc hV4 M hM hML m hm hVm
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
      have hgord : orderOf (g : G) = Nat.card V := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_card_of_forall_mem_zpowers hg
      have hgL : (g : G) ∈ L' := hVL g.2
      have hgnc : ¬ ∀ w ∈ L', (g : G) * w = w * g := by
        intro hc
        have hgg := hq.sq_eq_one_of_central hgL hc
        have hd : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      have hgN := hΩ.omega5 M hM L' hL' hML m hm g hgL hgnc
        ((h2 L' hL').to_le (Subgroup.zpowers_le.mpr hgL)) (hVm g g.2)
      intro v hv
      obtain ⟨k, hk⟩ := hg ⟨v, hv⟩
      have hv' : v = (g : G) ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      rw [hv']
      exact Subgroup.zpow_mem _ hgN k
    have hLcomm : ∀ M ∈ Ω, M ≠ L' → ∀ x ∈ M, ∀ y ∈ L', x * y = y * x := by
      intro M hM hML
      obtain ⟨⟨m, hm⟩, -⟩ := hΩ.omega1 M hM
      obtain ⟨hmW, hmW'⟩ := hinvW M hM m hm
      have hLN : L' ≤ Subgroup.normalizer (M : Set G) := by
        rw [← hsupL]
        exact sup_le (hcycN U hUL hUc h4U M hM hML m hm fun v hv => hWcomm v (hUW v hv) m hmW)
          (hcycN U' hU'L hU'c h4 M hM hML m hm fun v hv => hW'comm v (hU'W v hv) m hmW')
      exact comm_of_mem_omegaNbr hΩ h2 hM
        ((TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hL, fun h => hML h.symm, hLN⟩)
    apply hns
    have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (L' : Set G) := by
      rw [← hgen]
      refine pSpan_le fun M hM => ?_
      by_cases hML : M = L'
      · rw [hML]
        exact Subgroup.le_normalizer
      · exact le_normalizer_of_comm fun x hx y hy => hLcomm M hM hML x hx y hy
    have hall : ∀ M ∈ Ω, M = L' := by
      intro M hM
      obtain ⟨g, rfl⟩ := htr L' hL M hM
      exact conjSub_eq_of_mem_normalizer (htop (Subgroup.mem_top g))
    intro M hM M' hM'
    rw [hall M hM, hall M' hM']
  have hcard : η.ncard ≤ η'.ncard :=
    hη'S'.2.2 η (fun V hV => ⟨(hηS.1 hV).1, hηle S' V hV⟩) hηS.2.1
  have heq : η' = η := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  rw [heq]

theorem isNormalTwoIn_pCoreOf (z : G) :
    TC.IsNormalTwoIn (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨LieType.BorelTits.pCoreOf_le 2 _, LieType.BorelTits.pCoreOf_isPGroup 2 _,
    fun c hc p hp => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 _ hc) p).mp hp

theorem pCoreOf_le_pCoreOf {H H' : Subgroup G} (hle : H ≤ H')
    (hN : H' ≤ Subgroup.normalizer (H : Set G)) : pCoreOf 2 H ≤ pCoreOf 2 H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((LieType.BorelTits.pCoreOf_le 2 _).trans hle)
    (hN.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem le_pCoreOf_centralizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {L : Subgroup G} (hL : L ∈ Ω) {u : G} (hu : IsUniqueInvolution L u) :
    L ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Set (Subgroup G) := {M | M ∈ Ω ∧ IsUniqueInvolution M u} with hT
  have hLT : L ∈ T := ⟨hL, hu⟩
  have hTC : pSpan T ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun M hM x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (isUniqueInvolution_comm hM.2 hx)
  have hTN : pSpan T ≤ Subgroup.normalizer (L : Set G) := by
    refine pSpan_le fun M hM => ?_
    by_cases hML : M = L
    · rw [hML]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_comm (twin_comm hΩ h2 hM.1 hL hML hM.2 hu)
  have hconj : ∀ c ∈ Subgroup.centralizer ({u} : Set G), ∀ M ∈ T, conjSub c M ∈ T := by
    intro c hc M hM
    have hcu : c * u * c⁻¹ = u := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have h1 := hM.2.conj c
    rw [hcu] at h1
    exact ⟨hΩ.conjInvariant c M hM.1, h1⟩
  have hCN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer ((pSpan T : Subgroup G) : Set G) := fun c hc =>
    mem_normalizer_pSpan (hconj c hc) (hconj c⁻¹ (Subgroup.inv_mem _ hc))
  exact (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_pSpan hLT) hTN (h2 L hL)).trans
    (pCoreOf_le_pCoreOf hTC hCN)

theorem uAt_self_of (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) :
    ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → TC.UAt Ω u L := by
  intro L hL u hu
  have hLs : IsSylow2In L L := ⟨le_rfl, h2 L hL, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
  obtain ⟨U, hU, hUL, -⟩ := Sec6Gen.exists_invariant_mem_USet hΩ hL hLs (h2 L hL) le_rfl
    fun q hq => conjSub_eq_self_of_mem hq
  exact ⟨U, hU, hUL, _, isNormalTwoIn_pCoreOf u, hUL.trans (le_pCoreOf_centralizer hΩ h2 hL hu)⟩

theorem exists_of_WIn_eq (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hPne : P.Nonempty)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    {W : Subgroup G} (hW : WIn P (pSpan P) = {W}) :
    W ≤ pSpan P ∧ pSpan P ≤ Subgroup.normalizer (W : Set G) ∧ IsPGroup 2 W ∧
      ∃ J₀ ∈ P, ∃ U ∈ USet Ω, U ≤ J₀ ∧ U ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan P with hX
  have hc' : ConjInvariant (restrictFamily P X) :=
    conjInvariant_restrictFamily fun L hL x hx => hinv L hL x hx
  have hWmem : W ∈ WIn P X := by rw [hW]; rfl
  obtain ⟨W', hW'mem, rfl⟩ := hWmem
  have hW'uniq : ∀ W'' ∈ WSet (restrictFamily P X), W'' = W' := by
    intro W'' h
    have h1 : W''.map X.subtype ∈ WIn P X := ⟨W'', h, rfl⟩
    rw [hW] at h1
    exact Subgroup.map_injective X.subtype_injective h1
  have hnorm' : ∀ g : X, conjSub g W' = W' := fun g => hW'uniq _ (WSet.conj hc' hW'mem g)
  obtain ⟨η, ⟨S, hη, -⟩, hW'eq⟩ := hW'mem
  have hWS : W' ≤ (S : Subgroup X) := by
    rw [hW'eq]
    exact iSup₂_le fun U hU => (hη.1 hU).2
  have hW2 : IsPGroup 2 ↥(W'.map X.subtype) := (S.isPGroup'.to_le hWS).map _
  have hWX : W'.map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hnorm : ∀ x ∈ X, ∀ q ∈ W'.map X.subtype, x * q * x⁻¹ ∈ W'.map X.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have h1 : (⟨x, hx⟩ : X) * q * (⟨x, hx⟩ : X)⁻¹ ∈ conjSub (⟨x, hx⟩ : X) W' :=
      conj_mem_conjSub hq
    rw [hnorm'] at h1
    exact ⟨_, h1, rfl⟩
  have hXN : X ≤ Subgroup.normalizer ((W'.map X.subtype : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hnorm x hx q, fun h => ?_⟩
    have := hnorm x⁻¹ (X.inv_mem hx) _ h
    simpa [mul_assoc] using this
  refine ⟨hWX, hXN, hW2, ?_⟩
  obtain ⟨L, hL⟩ := hPne
  have hL'2 : IsPGroup 2 ↥(L.subgroupOf X) := (h2 L (hPΩ hL)).comap_subtype
  obtain ⟨S'', hS''⟩ := hL'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S'' S
  have hgS : conjSub g (L.subgroupOf X) ≤ (S : Subgroup X) := by
    rw [← hg, Sec7.coe_smul_sylow]
    exact conjSub_mono hS''
  rw [conjSub_subgroupOf] at hgS
  set L₁ := conjSub (g : G) L with hL₁
  have hL₁P : L₁ ∈ P := hinv L hL g g.2
  have hL₁Ω : L₁ ∈ Ω := hPΩ hL₁P
  have hL₁X : L₁ ≤ X := le_pSpan hL₁P
  have hq₁ : IsQuatSub L₁ :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hL₁Ω (h2 L₁ hL₁Ω))
  obtain ⟨C₁, hC₁L, hC₁c, hC₁card⟩ := hq₁.exists_cyclic_index_two
  set U₁ : Subgroup X := C₁.subgroupOf X with hU₁
  have hL₁'2 : IsPGroup 2 ↥(L₁.subgroupOf X) := (h2 L₁ hL₁Ω).comap_subtype
  have hU1 : U₁ ∈ USet (restrictFamily P X) := by
    refine mem_USet_of_natCard (subgroupOf_mem_restrictFamily hL₁P hL₁X)
      ⟨le_rfl, hL₁'2, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hC₁L (Subgroup.mem_subgroupOf.mp hx))) ?_ ?_
    · have e := Subgroup.subgroupOfEquivOfLe (hC₁L.trans hL₁X)
      exact isCyclic_of_surjective e.symm e.symm.surjective
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hC₁L.trans hL₁X)).toEquiv]
      exact hC₁card
  have hU1S : U₁ ≤ (S : Subgroup X) := fun x hx =>
    hgS (Subgroup.mem_subgroupOf.mpr (hC₁L (Subgroup.mem_subgroupOf.mp hx)))
  have hηpos : η.ncard ≠ 0 := by
    have h1 := hη.2.2 {U₁} (by
      intro U hU
      rw [Set.mem_singleton_iff.mp hU]
      exact ⟨hU1, hU1S⟩) (by
      intro U hU U' hU' hne
      exact absurd ((Set.mem_singleton_iff.mp hU).trans (Set.mem_singleton_iff.mp hU').symm) hne)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨U₀, hU₀⟩ := Set.nonempty_of_ncard_ne_zero hηpos
  obtain ⟨hU₀U, -⟩ := hη.1 hU₀
  obtain ⟨R₀, hR₀, hU₀R₀, hcyc₀, hidx⟩ := hU₀U
  obtain ⟨J₀', hJ₀', hR₀J₀, -, hmax⟩ := mem_RSet_iff.mp hR₀
  obtain ⟨J₀, hJ₀, hJ₀X, rfl⟩ := hJ₀'
  have hJ₀Ω : J₀ ∈ Ω := hPΩ hJ₀
  have hJ₀'2 : IsPGroup 2 ↥(J₀.subgroupOf X) := (h2 J₀ hJ₀Ω).comap_subtype
  have hR₀eq : J₀.subgroupOf X = R₀ := hmax _ le_rfl hJ₀'2 hR₀J₀
  have hU₀W : U₀ ≤ W' := by
    rw [hW'eq]
    exact le_biSup (fun U => U) hU₀
  refine ⟨J₀, hJ₀, U₀.map X.subtype, ?_, ?_, Subgroup.map_mono hU₀W⟩
  · refine mem_USet_of_natCard hJ₀Ω ⟨le_rfl, h2 J₀ hJ₀Ω, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
      ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hR₀J₀ (hU₀R₀ hu))
    · have e := U₀.equivMapOfInjective X.subtype X.subtype_injective
      exact isCyclic_of_surjective e e.surjective
    · have h1 := Subgroup.relIndex_mul_card U₀ R₀
      rw [inf_eq_left.mpr hU₀R₀, hidx, ← hR₀eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ₀X).toEquiv] at h1
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      omega
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hR₀J₀ (hU₀R₀ hu))

theorem exists_normal_etaSpan_of_reach (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {A : Subgroup G → Subgroup G → Prop}
    (hA : ∀ {M N : Subgroup G}, A M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ z : G, IsUniqueInvolution M z → TC.UAt Ω z N)
    (hself : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → TC.UAt Ω u L)
    {K : Subgroup G} (hK : K ∈ Ω) (hreach : ∀ L ∈ Ω, Relation.ReflTransGen A K L)
    (hgen : pSpan Ω = ⊤) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ η ∈ etaG Ω, (etaSpan η).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hKS⟩ := (h2 K hK).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηS' : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  set W := etaSpan η with hWdef
  have hW2 : IsPGroup 2 W := etaSpan_isPGroup hη
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := etaSpan_comm hΩ hη
  obtain ⟨U₀, hU₀, hU₀K, -⟩ := hself K hK z hz
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₀
  have hcard : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hU₀K (hU₀K.trans hKS))
    omega
  have hKW : K ⊓ W ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηS' K hK hcard
  have hKWU : K ⊓ W ∈ USet Ω := (hηS.1 hKW).1
  obtain ⟨-, -, -, -, -, -, -, -, hKW4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hKWU
  have hzW : z ∈ K ⊓ W := hz.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)
  have hWz : W ≤ Subgroup.centralizer ({z} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWcomm w hw z hzW.2
  have hnorm : ∀ L ∈ Ω, L ≤ Subgroup.normalizer (W : Set G) := by
    intro L hL
    obtain ⟨hLΩ, uL, huL, hWuL⟩ := TC.le_centralizer_of_reach hΩ h2 hA hK hz hη hWz (hreach L hL)
    obtain ⟨U₁, hU₁, hU₁L, P, hP, hU₁P⟩ := hself L hL uL huL
    have hact := (TC.normalizes_w_of_le_twoNormal hΩ h2 hη hWuL hLΩ hU₁ hU₁L hP hU₁P).1
    intro l hl
    rw [mem_normalizer_iff_conjSub_eq]
    exact TC.conjSub_etaSpan_eq (hact l hl) (hact l⁻¹ (L.inv_mem hl))
  refine ⟨η, hη, ?_⟩
  have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hgen]
    exact pSpan_le hnorm
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)

namespace CSetting

variable {r : ℕ} {IH : ℕ → Prop} {K J : Subgroup G} (hS : CSetting r IH Ω K J)
include hS

theorem exists_uAt_of_WIn {W : Subgroup G}
    (hW : WIn (orbOf (TC.nbrAdj Ω) K J) (pSpan (orbOf (TC.nbrAdj Ω) K J)) = {W}) {z : G}
    (hz : IsUniqueInvolution K z) : ∃ J₀ ∈ orbOf (TC.nbrAdj Ω) K J, TC.UAt Ω z J₀ := by
  have hD := hS.cex.toThmDHyp
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  have hK : K ∈ Ω := hS.adj.1
  have hPΩ : π ⊆ Ω := fun M hM => (hS.orb_subset hM).1
  have hinv : ∀ L ∈ π, ∀ x ∈ pSpan π, conjSub x L ∈ π :=
    fun L hL x hx => conjSub_mem_orb hK (hS.pSpan_orb_le hx) hL
  have hN : pSpan (omegaNbr Ω K) ≤ Subgroup.normalizer ((pSpan π : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_pSpan (fun L hL => conjSub_mem_orb hK hl hL)
      (fun L hL => conjSub_mem_orb hK (Subgroup.inv_mem _ hl) hL)
  obtain ⟨hWX, hXN, hW2, J₀, hJ₀, U, hU, hUJ₀, hUW⟩ :=
    exists_of_WIn_eq hD.hyp hD.two hPΩ ⟨J, mem_orbOf_self K J⟩ hinv hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : W ≤ pCoreOf 2 (pSpan π) := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWX hXN hW2
  have h2' : pCoreOf 2 (pSpan π) ≤ pCoreOf 2 (pSpan (omegaNbr Ω K)) :=
    pCoreOf_le_pCoreOf hS.pSpan_orb_le hN
  have h3 : pCoreOf 2 (pSpan (omegaNbr Ω K)) ≤ pCoreOf 2 (pSpan (KPerp Ω K)) :=
    pCoreOf_le_pCoreOf (pSpan_le fun J hJ => le_pSpan (Set.mem_insert_of_mem _ hJ))
      (pSpan_kPerp_le_normalizer hD.hyp hD.two hK)
  have h4 : pCoreOf 2 (pSpan (KPerp Ω K)) ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    pCoreOf_le_pCoreOf (pSpan_kPerp_le_centralizer hD.hyp hD.two hK hz)
      (centralizer_le_normalizer_pSpan_kPerp hD.hyp hK hz)
  exact ⟨J₀, hJ₀, U, hU, hUJ₀, _, isNormalTwoIn_pCoreOf z,
    hUW.trans (h1.trans (h2'.trans (h3.trans h4)))⟩

end CSetting

theorem cLeafW_holds (r : ℕ) (IH : ℕ → Prop) : CLeafW r IH := by
  intro G _ _ Ω K J hS W hW
  have hD := hS.cex.toThmDHyp
  have hF := hS.graphFam
  have hK : K ∈ Ω := hS.adj.1
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  obtain ⟨J₀, hJ₀, hU₀⟩ := hS.exists_uAt_of_WIn hW hz
  have h₀ : MaxAdj (TC.nbrAdj Ω) K J₀ := by
    refine ⟨adj_of_mem_orbOf hF.graph hS.adj hJ₀, ?_⟩
    rw [orbOf_eq_of_mem hJ₀]
    exact hS.max
  have hA : ∀ {M N : Subgroup G}, MaxAdj (TC.nbrAdj Ω) M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ u : G, IsUniqueInvolution M u → TC.UAt Ω u N := by
    intro M N hMN _
    refine ⟨hMN.1.2.1, fun u hu => ?_⟩
    obtain ⟨g, rfl, rfl⟩ := TC.exists_conj_maxAdj hF h₀ hMN
    have h1 := TC.uAt_conj hD.hyp.conjInvariant hU₀ g
    have e := hu.eq (hz.conj g)
    rwa [← e] at h1
  obtain ⟨η, hη, hWn⟩ := exists_normal_etaSpan_of_reach hD.hyp hD.two hA
    (uAt_self_of hD.hyp hD.two) hK (reach_maxAdj hF hK) hD.gen hz
  have hns : ¬ ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L' := fun h => hS.cex.not (Or.inl h)
  exact hS.cex.not (Or.inr (Or.inl ⟨_,
    wSet_eq_singleton_of_normal hD.hyp hD.two hD.trans hD.gen hns ⟨η, hη, rfl⟩ hWn⟩))


variable {r : ℕ} {IH : ℕ → Prop}

theorem dLeafC_of₂ (h1 : D1GenLeaf r) (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH)
    (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) : DLeafC r IH :=
  dLeafC_of h1 (cLeafW_holds r IH) hE8 hE64 hE29 hAE

theorem thmDAbs_of_leaves₅ (h1 : D1GenLeaf r) (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH)
    (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH)
    (hend : DLeafEnd r IH) (hih : ∀ n, IH n) : ThmDAbs r :=
  thmDAbs_of_leaves₄ h1 (cLeafW_holds r IH) hE8 hE64 hE29 hAE hE4 hstar hend hih

section Cit3


theorem thmD2Step_of_leaves₄ (h1 : D1GenLeaf r) (hE8 : CLeafE8 r (PackIH r))
    (hE64 : CLeafE64 r (PackIH r)) (hE29 : CLeafE29 r (PackIH r)) (hAE : CLeafAE r (PackIH r))
    (hE4 : DLeafE4 r (PackIH r)) (hstar : DLeafStar r (PackIH r)) (hend : DLeafEnd r (PackIH r))
    (n : ℕ) : CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) :=
  thmD2Step_of_leaves₃ h1 (cLeafW_holds r (PackIH r)) hE8 hE64 hE29 hAE hE4 hstar hend n

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
