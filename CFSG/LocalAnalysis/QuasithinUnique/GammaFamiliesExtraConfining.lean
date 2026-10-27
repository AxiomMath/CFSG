module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def IsS2e {G : Type*} [Group G] (D : Subgroup G) : Prop :=
  D ≠ ⊥ ∧ IsPGroup 2 D ∧ CharTwo (Subgroup.normalizer (D : Set G))

section Tools

namespace GammaExtra

variable {G : Type*} [Group G]

theorem exists_involution_of_ne_bot [Finite G] {Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hne : Z ≠ ⊥) : ∃ z ∈ Z, z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
  have hdvd : 2 ∣ Nat.card Z := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨y, y.2, ?_, orderOf_dvd_iff_pow_eq_one.mp (by rw [hy'])⟩
  intro h1
  rw [h1, orderOf_one] at hy'
  omega

theorem two_mul_card_le_of_lt [Finite G] {S V : Subgroup G} (hSV : S < V) :
    2 * Nat.card S ≤ Nat.card V := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSV.le
  have hlt : Nat.card S < Nat.card V := Subgroup.card_lt_of_lt hSV
  have hS0 : 0 < Nat.card S := Nat.card_pos
  rw [hk] at hlt ⊢
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hk2' : k < 2 := not_le.mp hk2
    interval_cases k <;> simp at hlt
  nlinarith [Nat.mul_le_mul_left (Nat.card S) hk2]

theorem card_eq_two_mul_of_lt_of_le [Finite G] {S V : Subgroup G} (hSV : S ≤ V) (hne : S ≠ V)
    (hle : Nat.card V ≤ 2 * Nat.card S) : Nat.card V = 2 * Nat.card S :=
  le_antisymm hle (two_mul_card_le_of_lt (lt_of_le_of_ne hSV hne))

theorem card_eq_two_mul_of_relIndex_eq_two {R S : Subgroup G} (hRS : R ≤ S)
    (h : R.relIndex S = 2) : Nat.card S = 2 * Nat.card R := by
  have := Subgroup.relIndex_mul_card R S
  rw [inf_eq_left.mpr hRS, h] at this
  exact this.symm

end GammaExtra

end Tools

section Basic

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsWitnessPair.isS2e_pCoreOf (h : UniqueSetting G T M) {U HU : Subgroup G}
    (hp : IsWitnessPair M U HU) : IsS2e (pCoreOf 2 HU) := by
  obtain ⟨hne, hchar⟩ := hp.1.charTwo_normalizer_core h hp.2.1 hp.2.2.2.1
  exact ⟨hne, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU, hchar⟩

omit [Finite G] in
theorem IsGamma.core_normalizer_isGamma {H : Subgroup G} (hH : IsGamma M H) :
    IsGamma M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      ∀ U HU : Subgroup G, IsWitnessPair M U HU → HU ≤ H →
        HU ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  refine ⟨?_, fun U HU _ hle => hle.trans hHN⟩
  obtain ⟨hcore, U, HU, hp, hle⟩ := hH
  refine ⟨fun hbot => hcore (le_bot_iff.mp ?_), U, HU, hp, hle.trans hHN⟩
  have : pCoreOf 2 H ≤ pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  rwa [hbot] at this

end Basic

section ThompsonJ

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.false_of_isSylowTwoOf_of_normalizer_le (h : UniqueSetting G T M)
    {H S K : Subgroup G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hSK : IsSylowTwoOf S K) (hK : Subgroup.normalizer (S : Set G) ≤ K) : False := by
  obtain ⟨-, hSc, hlt⟩ := IsGamma.sylow_properties h hH.isGamma hS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  have hne : S ≠ T' := by
    intro heq
    rw [heq, h.card_eq_of_isSylowTwoOf_M hT'] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hx, hxS⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT'.isPGroup hST' hne
  have hlt' : S < T' ⊓ Subgroup.normalizer (S : Set G) :=
    lt_of_le_of_ne (le_inf hST' Subgroup.le_normalizer) fun heq => hxS (heq ▸ hx)
  have heq := hSK.eq_of_le hlt'.le (inf_le_right.trans hK) (hT'.isPGroup.to_le inf_le_left)
  exact hlt'.ne heq.symm

theorem IsGamma0.isS2e_thompsonJ (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) : IsS2e (thompsonJ S) := by
  obtain ⟨-, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  have hT'1 : T' ≠ ⊥ := ne_bot_of_le_ne_bot hSc.2.1 hST'
  have hZ : T' ⊓ Subgroup.centralizer (T' : Set G) ≠ ⊥ := inf_centralizer_ne_bot hT'.isPGroup hT'1
  obtain ⟨z, hzZ, hz1, hz2⟩ := GammaExtra.exists_involution_of_ne_bot
    (hT'.isPGroup.to_le inf_le_left) hZ
  have hzS := hcentre hzZ
  have hzJ : z ∈ thompsonJ S :=
    GammaExtra.mem_thompsonJ_of_central_involution hzS.1
      (fun s hs => Subgroup.mem_centralizer_iff.mp hzS.2 s hs) hz2
  have hJ1 : thompsonJ S ≠ ⊥ := fun hbot => hz1 (Subgroup.mem_bot.mp (hbot ▸ hzJ))
  have hJ2 : IsPGroup 2 (thompsonJ S) := GammaExtra.isPGroup_thompsonJ hS.isPGroup
  refine ⟨hJ1, hJ2, ?_⟩
  refine charTwo_normalizer_of_inf_center h.qtke.2.1
    (h.isSylowTwoOf_top_of_isSylowTwoOf_M hT') hJ2 ?_
  intro hbot
  have : z ∈ thompsonJ S ⊓ (T' ⊓ Subgroup.centralizer (T' : Set G)) := ⟨hzJ, hzZ⟩
  rw [hbot] at this
  exact hz1 (Subgroup.mem_bot.mp this)

theorem IsGamma0.normalizer_thompsonJ_le (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    Subgroup.normalizer ((thompsonJ S : Subgroup G) : Set G) ≤ M := by
  obtain ⟨hSH, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  obtain ⟨hJ1, hJ2, hJchar⟩ := hH.isS2e_thompsonJ h hS
  by_contra hnot
  set K := Subgroup.normalizer ((thompsonJ S : Subgroup G) : Set G) with hKdef
  have hNS : Subgroup.normalizer (S : Set G) ≤ K := GammaExtra.normalizer_le_normalizer_thompsonJ S
  have hSK : S ≤ K := Subgroup.le_normalizer.trans hNS
  have hcoreK : pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have : thompsonJ S ≤ pCoreOf 2 K :=
      le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hJ2
    rw [hbot] at this
    exact hJ1 (le_bot_iff.mp this)
  have hpair : IsWitnessPair M S K := ⟨hSc, hSK, hcoreK, hJchar, hnot⟩
  have hKΓ : IsGamma M K := hpair.isGamma_of_le le_rfl hcoreK
  have hcase : IsGamma2 M H ∨ (IsGammaU M H ∧ IsGammaTop M K) := by
    rcases hH with hU | h2
    · exact Or.inr ⟨hU, hpair.isGammaTop_of_le le_rfl hcoreK
        (fun V hV => hU.1.card_le_of_isSylowTwoOf hSH hV)⟩
    · exact Or.inl h2
  obtain ⟨-, hSK', -, -, -⟩ := hH.overgroup_of_sylow_le h hS hKΓ hSK hcase
  exact hH.false_of_isSylowTwoOf_of_normalizer_le h hS hSK' hNS

theorem IsGamma0.isConfining_of_relIndex_two (h : UniqueSetting G T M) {H S R : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hJR : thompsonJ S ≤ R) (hRS : R ≤ S)
    (hidx : R.relIndex S = 2) (hC : pCoreOf 2 M ⊓ Subgroup.centralizer (R : Set G) ≤ R) :
    IsConfining M R := by
  have hidx' : Nat.card S = 2 * Nat.card R := GammaExtra.card_eq_two_mul_of_relIndex_eq_two hRS hidx
  obtain ⟨hSH, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  have hJ := hH.isS2e_thompsonJ h hS
  have hJR2 : thompsonJ R = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJR hRS
  have hRM : R ≤ M := hRS.trans hSc.1
  have hR1 : R ≠ ⊥ := ne_bot_of_le_ne_bot hJ.1 hJR
  have hR2 : IsPGroup 2 R := hSc.2.2.1.to_le hRS
  refine ⟨hRM, hR1, hR2, ?_, hC⟩
  by_contra hβ1
  push Not at hβ1
  obtain ⟨V₀, hV₀2, hRV₀, hV₀M, hV₀n⟩ := hβ1
  obtain ⟨V, hVmax⟩ := Set.Finite.exists_maximal
    (s := {V : Subgroup G | IsPGroup 2 V ∧ R ≤ V ∧ V ≤ M ∧ ¬ Subgroup.normalizer (V : Set G) ≤ M})
    (Set.toFinite _) ⟨V₀, hV₀2, hRV₀, hV₀M, hV₀n⟩
  obtain ⟨hV2, hRV, hVM, hVn⟩ := hVmax.1
  have hnormR : Subgroup.normalizer (R : Set G) ≤ M := by
    refine (GammaExtra.normalizer_le_normalizer_thompsonJ R).trans ?_
    rw [hJR2]
    exact hH.normalizer_thompsonJ_le h hS
  have hRVlt : R < V := lt_of_le_of_ne hRV fun heq => hVn (heq ▸ hnormR)
  obtain ⟨T₁, hVT₁, hT₁⟩ := exists_isSylowTwoOf_of_le hVM hV2
  have hV1 : V ≠ ⊥ := ne_bot_of_le_ne_bot hR1 hRV
  have hVT₁ne : V ≠ T₁ := by
    intro heq
    apply hVn
    rw [heq]
    exact h.le_of_isTwoLocal_of_isSylowTwoOf_M hT₁
      ⟨T₁, heq ▸ hV1, hT₁.isPGroup, rfl⟩ Subgroup.le_normalizer
  obtain ⟨x, hx, hxV⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT₁.isPGroup hVT₁ hVT₁ne
  set W := T₁ ⊓ Subgroup.normalizer (V : Set G) with hWdef
  have hVW : V < W := lt_of_le_of_ne (le_inf hVT₁ Subgroup.le_normalizer) fun heq => hxV (heq ▸ hx)
  have hW2 : IsPGroup 2 W := hT₁.isPGroup.to_le inf_le_left
  have hRW : R ≤ W := hRV.trans hVW.le
  have hWM : W ≤ M := inf_le_left.trans hT₁.le
  have hWβ : IsConfining M W := by
    refine ⟨hWM, ne_bot_of_le_ne_bot hR1 hRW, hW2, fun X hX2 hWX hXM => ?_, ?_⟩
    · by_contra hnot
      have hXV := hVmax.2 (show X ∈ {V : Subgroup G | IsPGroup 2 V ∧ R ≤ V ∧ V ≤ M ∧
        ¬ Subgroup.normalizer (V : Set G) ≤ M} from ⟨hX2, hRW.trans hWX, hXM, hnot⟩)
        (hVW.le.trans hWX)
      exact hVW.not_ge (hWX.trans hXV)
    · exact (inf_le_inf_left _ (Subgroup.centralizer_le (by exact_mod_cast hRW))).trans
        (hC.trans hRW)
  have hVchar : CharTwo (Subgroup.normalizer (V : Set G)) :=
    charTwo_normalizer_of_le hV2 (hJR.trans hRV) hJ.2.2
  have hcoreV : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≠ ⊥ := by
    intro hbot
    have : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
      le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hV2
    rw [hbot] at this
    exact hV1 (le_bot_iff.mp this)
  have hpair : IsWitnessPair M W (Subgroup.normalizer (V : Set G)) :=
    ⟨hWβ, inf_le_right, hcoreV, hVchar, hVn⟩
  have hRV' := GammaExtra.two_mul_card_le_of_lt hRVlt
  have hVW' := GammaExtra.two_mul_card_le_of_lt hVW
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hWS : Nat.card S < Nat.card W := by omega
  have hWle : Nat.card W ≤ Nat.card S := by
    rcases hH with hU | h2
    · exact hU.1.card_le_of_isSylowTwoOf hSH ⟨_, hpair⟩
    · have h1 : twoPart (Subgroup.normalizer (V : Set G)) ≤ twoPart H := h2.2 _ hpair.isGamma
      have h3 : Nat.card W ≤ twoPart (Subgroup.normalizer (V : Set G)) :=
        CFSG.QuasithinUnique.card_le_twoPart inf_le_right hW2
      rw [← hSH.card_eq] at h1
      exact h3.trans h1
  omega

theorem IsGamma0.pCore_centralizer_le_of_charTwo (h : UniqueSetting G T M) {H S R₀ : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hHc : CharTwo H)
    (hQR : pCoreOf 2 H ≤ R₀) : pCoreOf 2 M ⊓ Subgroup.centralizer (R₀ : Set G) ≤ R₀ := by
  have hE : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ S :=
    hH.core_centralizer_le h hS
  have hEH : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    le_inf ((hE.trans (hS.le.trans inf_le_left))) inf_le_right
  intro y hy
  have hy' : y ∈ pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    ⟨hy.1, Subgroup.centralizer_le (by exact_mod_cast hQR) hy.2⟩
  exact hQR (hHc (hEH hy'))

end ThompsonJ

section IndexTwo

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem UniqueSetting.card_sylow_ne_two (h : UniqueSetting G T M) : Nat.card T ≠ 2 := by
  intro hT2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ (T : Subgroup G).index := by
    simpa only [index_subgroupOf_top] using h.sylow.2.2
  let P : Sylow 2 G := h.isPGroup.toSylow hidx
  have hP : Nat.card (P : Subgroup G) = 2 := hT2
  have hcyc : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hP
  obtain ⟨N, hN, hcompl⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two P hcyc
  have hcard := hcompl.card_mul_card
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN1 | hN1
  · rw [hN1, hP] at hcard
    simp only [Subgroup.card_bot, one_mul] at hcard
    have hGcyc : IsCyclic G := isCyclic_of_prime_card (p := 2) hcard.symm
    obtain ⟨a, b, hab⟩ := h.nonabelian
    let _ : CommGroup G := IsCyclic.commGroup
    exact hab (mul_comm a b)
  · rw [hN1, hP, Subgroup.card_top] at hcard
    have := Nat.card_pos (α := G)
    omega

theorem isConfining_of_relIndex_two_of_exists_local (h : UniqueSetting G T M) {S : Subgroup G}
    (hST : S ≤ T) (hidx : S.relIndex T = 2)
    (hH : ∃ H : Subgroup G, pCoreOf 2 H ≠ ⊥ ∧ S ≤ H ∧ ¬ H ≤ M) : IsConfining M S := by
  have hidx' : Nat.card T = 2 * Nat.card S := GammaExtra.card_eq_two_mul_of_relIndex_eq_two hST hidx
  have hS2 : IsPGroup 2 S := h.isPGroup.to_le hST
  have hSM : S ≤ M := hST.trans h.le
  have hS1 : S ≠ ⊥ := by
    intro hbot
    apply h.card_sylow_ne_two
    rw [hidx', hbot]
    simp
  have hSne : S ≠ T := by
    intro heq
    have : 0 < Nat.card T := Nat.card_pos
    rw [heq] at hidx'
    omega
  have hTN : T ≤ Subgroup.normalizer (S : Set G) := by
    obtain ⟨x, hx, hxS⟩ := exists_mem_inf_normalizer_of_ne (p := 2) h.isPGroup hST hSne
    have hlt : S < T ⊓ Subgroup.normalizer (S : Set G) :=
      lt_of_le_of_ne (le_inf hST Subgroup.le_normalizer) fun heq => hxS (heq ▸ hx)
    have hc := GammaExtra.card_eq_two_mul_of_lt_of_le hlt.le hlt.ne
      (by rw [← hidx']; exact Subgroup.card_le_of_le inf_le_left)
    have heq : T ⊓ Subgroup.normalizer (S : Set G) = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hidx'])
    rw [← heq]
    exact inf_le_right
  have hNSM : Subgroup.normalizer (S : Set G) ≤ M :=
    h.le_of_isTwoLocal_of_isSylowTwoOf_M h.isSylowTwoOf_M ⟨S, hS1, hS2, rfl⟩ hTN
  have hsyl : ∀ V : Subgroup G, IsPGroup 2 V → S ≤ V → V ≤ M → S ≠ V → IsSylowTwoOf V M := by
    intro V hV hSV hVM hne
    refine isSylowTwoOf_of_card_eq hVM hV ?_
    rw [h.twoPart_M]
    exact (GammaExtra.card_eq_two_mul_of_lt_of_le hSV hne
      (hidx' ▸ h.card_le_of_isPGroup hV)).trans hidx'.symm
  refine ⟨hSM, hS1, hS2, ?_, ?_⟩
  ·
    intro V hV hSV hVM
    by_cases hVS : S = V
    · rw [← hVS]
      exact hNSM
    · exact h.le_of_isTwoLocal_of_isSylowTwoOf_M (hsyl V hV hSV hVM hVS)
        ⟨V, ne_bot_of_le_ne_bot hS1 hSV, hV, rfl⟩ Subgroup.le_normalizer
  ·
    obtain ⟨H₀, hH₀1, hSH₀, hH₀M⟩ := hH
    obtain ⟨H, ⟨hH1, hSH, hHM⟩, hHmax⟩ := Set.exists_max_image
      {X : Subgroup G | pCoreOf 2 X ≠ ⊥ ∧ S ≤ X ∧ ¬ X ≤ M} (fun X => Nat.card X)
      (Set.toFinite _) ⟨H₀, hH₀1, hSH₀, hH₀M⟩
    set Q := pCoreOf 2 H with hQdef
    have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
    have hQn : H ≤ Subgroup.normalizer (Q : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
    have hHN : H = Subgroup.normalizer (Q : Set G) := by
      have hmem : Subgroup.normalizer (Q : Set G) ∈
          {X : Subgroup G | pCoreOf 2 X ≠ ⊥ ∧ S ≤ X ∧ ¬ X ≤ M} := by
        refine ⟨?_, hSH.trans hQn, fun hle => hHM (hQn.trans hle)⟩
        intro hbot
        have : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
          le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hQ2
        rw [hbot] at this
        exact hH1 (le_bot_iff.mp this)
      exact Subgroup.eq_of_le_of_card_ge hQn (hHmax _ hmem)
    have hSsyl : IsSylowTwoOf S H := by
      obtain ⟨P, hSP, hP⟩ := exists_isSylowTwoOf_of_le hSH hS2
      by_cases hPS : S = P
      · rwa [← hPS] at hP
      · exfalso
        have hcP : Nat.card P = 2 * Nat.card S := by
          refine GammaExtra.card_eq_two_mul_of_lt_of_le hSP hPS ?_
          rw [← hidx']
          exact h.card_le_of_isPGroup hP.isPGroup
        have hPT : Nat.card P = Nat.card T := hcP.trans hidx'.symm
        have hPN : P ≤ Subgroup.normalizer (S : Set G) := by
          have hlt : S < P ⊓ Subgroup.normalizer (S : Set G) := by
            obtain ⟨x, hx, hxS⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hP.isPGroup hSP hPS
            exact lt_of_le_of_ne (le_inf hSP Subgroup.le_normalizer) fun heq => hxS (heq ▸ hx)
          have heq : P ⊓ Subgroup.normalizer (S : Set G) = P := by
            refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
            rw [GammaExtra.card_eq_two_mul_of_lt_of_le hlt.le hlt.ne
              (by rw [← hcP]; exact Subgroup.card_le_of_le inf_le_left), hcP]
          rw [← heq]
          exact inf_le_right
        have hPM : P ≤ M := hPN.trans hNSM
        have hPsylM : IsSylowTwoOf P M :=
          isSylowTwoOf_of_card_eq hPM hP.isPGroup (by rw [h.twoPart_M, hPT])
        have hHM' : H ≤ M := by
          calc H = Subgroup.normalizer (Q : Set G) := hHN
            _ ≤ M := h.le_of_isTwoLocal_of_isSylowTwoOf_M hPsylM ⟨Q, hH1, hQ2, rfl⟩
              (le_of_le_of_eq hP.le hHN)
        exact hHM hHM'
    have hQS : Q ≤ S := hSsyl.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
      hQn hQ2
    have hSsyl' : IsSylowTwoOf S (H ⊓ M) :=
      (isSylowTwoOf_of_twoPart_le hSH hSM hS2 hSsyl.card_eq.ge).2
    intro y hy
    have hyH : y ∈ H := by
      rw [hHN]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (by exact_mod_cast hQS) hy.2)
    have hE : pCoreOf 2 M ⊓ H ≤ S := by
      refine hSsyl'.le_of_normalizes
        (le_inf inf_le_right
          (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)))
        ?_ ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left)
      exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf (H ⊓ M)
        (pCoreOf 2 M) H
        (inf_le_right.trans
          (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
        (inf_le_left.trans Subgroup.le_normalizer)
    exact hE ⟨hy.1, hyH⟩

end IndexTwo

end CFSG.QuasithinUnique
