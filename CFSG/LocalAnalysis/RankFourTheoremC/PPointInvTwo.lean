module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_two_normalizer_eq {U T : Subgroup G}
    (hT : rankTwoMaximalInvariantTwoSubgroup U T) : pCoreOf 2 (normalizer (T : Set G)) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := normalizer (T : Set G) with hH
  have hTle : T ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT.1
  exact hT.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    (hT.2.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hTle

theorem inf_centralizer_eq_bot_of_maximal (hchar : IsCharTwoType G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U T : Subgroup G} (hU : IsPGroup p U)
    (hT : rankTwoMaximalInvariantTwoSubgroup U T) (hT1 : T ≠ ⊥) :
    U ⊓ centralizer (T : Set G) = ⊥ := by
  have hloc : IsTwoLocal (normalizer (T : Set G)) := ⟨T, hT1, hT.1, rfl⟩
  have h := hchar _ hloc
  rw [pCoreOf_two_normalizer_eq hT] at h
  rw [eq_bot_iff]
  intro g hg
  have hgT : g ∈ T := h ⟨hT.2.1 hg.1, hg.2⟩
  obtain ⟨a, ha⟩ := hU ⟨g, hg.1⟩
  obtain ⟨b, hb⟩ := hT.1 ⟨g, hgT⟩
  have h1 : orderOf g ∣ p ^ a := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf g ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hb)
  have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (mem_bot).mpr (orderOf_eq_one_iff.mp this)

theorem exists_line_inf_centralizer_ne_bot (hchar : IsCharTwoType G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U T : Subgroup G} (hU : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2)
    (hT : rankTwoMaximalInvariantTwoSubgroup U T) (hT1 : T ≠ ⊥) {x : G} (hxU : x ∈ U) :
    ∃ u ∈ U, u ∉ zpowers x ∧ T ⊓ centralizer ({u} : Set G) ≠ ⊥ := by
  have hUp : IsPGroup p U := elementary_isPGroup p U hU
  have hcop : p.Coprime (Nat.card T) := by
    obtain ⟨b, hb⟩ := hT.1.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hC := inf_centralizer_eq_bot_of_maximal hchar hp hp2 hUp hT hT1
  obtain ⟨L₁, L₂, hne, ⟨hL₁U, hL₁c, hL₁b⟩, ⟨hL₂U, hL₂c, hL₂b⟩⟩ :=
    exists_two_bad_lines hp hU hUcard hT.2.1 hcop (fun d hd hdT => by
      have : d ∈ U ⊓ centralizer (T : Set G) :=
        ⟨hd, mem_centralizer_iff.mpr fun t ht => (hdT t ht).symm⟩
      rw [hC] at this
      exact mem_bot.mp this)
  have key : ∀ L : Subgroup G, L ≤ U → Nat.card L = p → ⁅T ⊓ centralizer (L : Set G), U⁆ ≠ ⊥ →
      L ≠ zpowers x → ∃ u ∈ U, u ∉ zpowers x ∧ T ⊓ centralizer ({u} : Set G) ≠ ⊥ := by
    intro L hLU hLc hLb hLx
    have hLne : L ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hLc
      exact hp.one_lt.ne hLc
    obtain ⟨⟨u, huL⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hLne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hord : orderOf u = p := by
      have hdvd : orderOf u ∣ p := by
        rw [← hLc]
        have := orderOf_dvd_natCard (⟨u, huL⟩ : L)
        rwa [Subgroup.orderOf_mk] at this
      exact ((Nat.dvd_prime hp).mp hdvd).resolve_left fun h1 => hu1' (orderOf_eq_one_iff.mp h1)
    have hzL : zpowers u = L := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr huL) (by
      rw [Nat.card_zpowers, hord, hLc])
    refine ⟨u, hLU huL, fun hux => hLx ?_, fun hbot => hLb ?_⟩
    · rw [← hzL]
      have hxord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hU.2 x hxU)
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hux) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord]
      exact Nat.le_of_dvd hp.pos hxord
    · have hle : T ⊓ centralizer (L : Set G) ≤ T ⊓ centralizer ({u} : Set G) :=
        inf_le_inf_left T (centralizer_le (Set.singleton_subset_iff.mpr huL))
      rw [hbot, le_bot_iff] at hle
      rw [hle, Subgroup.commutator_bot_left]
  by_cases h1 : L₁ = zpowers x
  · exact key L₂ hL₂U hL₂c hL₂b (fun h2 => hne (h1.trans h2.symm))
  · exact key L₁ hL₁U hL₁c hL₁b h1

theorem inf_ne_bot_of_centralizer_le (hchar : IsCharTwoType G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U T M : Subgroup G} (hU : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2)
    (hT : rankTwoMaximalInvariantTwoSubgroup U T) (hT1 : T ≠ ⊥) {x : G} (hxU : x ∈ U)
    (hM : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M) : T ⊓ M ≠ ⊥ := by
  obtain ⟨u, huU, hux, hne⟩ := exists_line_inf_centralizer_ne_bot hchar hp hp2 hU hUcard hT hT1 hxU
  intro hbot
  exact hne (le_bot_iff.mp ((inf_le_inf_left T (hM u huU hux)).trans hbot.le))

theorem coprime_card_sup_of_le_normalizer {p : ℕ} {N T : Subgroup G}
    (hTN : T ≤ normalizer (N : Set G)) (hN : p.Coprime (Nat.card N))
    (hT : p.Coprime (Nat.card T)) : p.Coprime (Nat.card (N ⊔ T : Subgroup G)) := by
  set X : Subgroup G := N ⊔ T with hX
  have hNX : N ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hXN : X ≤ normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  set N' : Subgroup X := N.subgroupOf X with hN'def
  set T' : Subgroup X := T.subgroupOf X with hT'def
  have hN'norm : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hT'N'top : T' ⊔ N' = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, hT'def, hN'def, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTX, inf_eq_left.mpr hNX, Subgroup.map_top,
      Subgroup.range_subtype, sup_comm]
  have hN'cop : p.Coprime (Nat.card N') := by
    rw [hN'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact hN
  have hT'cop : p.Coprime (Nat.card T') := by
    rw [hT'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv]
    exact hT
  have h := normal_coprime_sup_coprime p T' N' hN'norm hT'cop hN'cop
  rwa [hT'N'top, Subgroup.card_top] at h

theorem isSylowOf_two_of_invariantTwoMaximalWithin {p : ℕ} (hp : p.Prime) {U X Z : Subgroup G}
    (hU : IsPGroup p U) (hUX : U ≤ normalizer (X : Set G)) (hX : p.Coprime (Nat.card X))
    (hZ : invariantTwoMaximalWithin U X Z) : CFSG.ABGLocalTools.IsSylowOf 2 Z X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZX : Z ≤ X := hZ.1
  set Z' : Subgroup X := Z.subgroupOf X with hZ'def
  have hZ'2 : IsPGroup 2 Z' := hZ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hZX).symm
  obtain ⟨S, hS⟩ := coprime_maximal_invariant_prime_subgroup_is_sylow
    (ambientSubgroupActionHom U X hUX) p hp hU hX 2 Nat.prime_two Z' hZ'2
    ((ambient_subgroup_action_invariant_iff U X Z hUX hZX).mpr hZ.2.2.1) (by
      intro larger hl hinvl hle
      have hL := (ambient_subgroup_action_image_invariant_iff U X hUX larger).mp hinvl
      have hLX : larger.map X.subtype ≤ X := Subgroup.map_subtype_le _
      have hZL : Z ≤ larger.map X.subtype := by
        have := Subgroup.map_mono (f := X.subtype) hle
        rwa [hZ'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZX] at this
      have heq := hZ.2.2.2 _ hLX (hl.map X.subtype) hL hZL
      apply Subgroup.map_injective X.subtype_injective
      rw [heq, hZ'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZX])
  refine ⟨S, ?_⟩
  rw [hS, hZ'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZX]

theorem isSylowOf_inf_of_invariantTwoMaximalWithin {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U M N T : Subgroup G} (hU : IsPGroup p U) (hUM : U ≤ M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hNp : p.Coprime (Nat.card N))
    (hT : invariantTwoMaximalWithin U M T) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N := by
  set X : Subgroup G := N ⊔ T with hX
  have hXM : X ≤ M := sup_le hNM hT.1
  have hNX : N ≤ X := le_sup_left
  have hXN : X ≤ normalizer (N : Set G) := hXM.trans hMN
  have hUN : U ≤ normalizer (N : Set G) := hUM.trans hMN
  have hUX : U ≤ normalizer (X : Set G) := by
    intro u hu
    have hN' := mem_normalizer_iff_map_conj_eq.mp (hUN hu)
    have hT' := mem_normalizer_iff_map_conj_eq.mp (hT.2.2.1 hu)
    rw [mem_normalizer_iff_map_conj_eq, hX, Subgroup.map_sup, hN', hT']
  have hT2 : p.Coprime (Nat.card T) := by
    obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcopX : p.Coprime (Nat.card X) :=
    coprime_card_sup_of_le_normalizer (hT.1.trans hMN) hNp hT2
  have hTX : invariantTwoMaximalWithin U X T :=
    ⟨le_sup_right, hT.2.1, hT.2.2.1, fun larger hlX => hT.2.2.2 larger (hlX.trans hXM)⟩
  exact (isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUX hcopX hTX).inf_of_le_normalizer
    hNX hXN

theorem exists_centralizer_conj_of_isSylowOf_two {p : ℕ} (hp : p.Prime) {U O Y Y' : Subgroup G}
    (hU : IsPGroup p U) (hUO : U ≤ normalizer (O : Set G)) (hOp : p.Coprime (Nat.card O))
    (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y O) (hY' : CFSG.ABGLocalTools.IsSylowOf 2 Y' O)
    (hYU : U ≤ normalizer (Y : Set G)) (hY'U : U ≤ normalizer (Y' : Set G)) :
    ∃ c ∈ O ⊓ centralizer (U : Set G), Y.map (MulAut.conj c).toMonoidHom = Y' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : ∀ Z : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 Z O → ∀ larger : Subgroup O,
      IsPGroup 2 larger → Z.subgroupOf O ≤ larger → larger = Z.subgroupOf O := by
    intro Z hZ larger hl hle
    have hle' : Z ≤ larger.map O.subtype := by
      have := Subgroup.map_mono (f := O.subtype) hle
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZ.le] at this
    have heq := hZ.eq_of_le hle' (Subgroup.map_subtype_le _) (hl.map O.subtype)
    apply Subgroup.map_injective O.subtype_injective
    rw [heq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZ.le]
  obtain ⟨c, hc, hfix⟩ := coprime_maximal_invariant_prime_subgroups_fixed_conjugator
    (ambientSubgroupActionHom U O hUO) p hp hU hOp 2 Nat.prime_two (Y.subgroupOf O)
    (Y'.subgroupOf O) (hY.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hY.le).symm)
    ((ambient_subgroup_action_invariant_iff U O Y hUO hY.le).mpr hYU)
    (fun larger hl _ hle => hmax Y hY larger hl hle)
    (hY'.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hY'.le).symm)
    ((ambient_subgroup_action_invariant_iff U O Y' hUO hY'.le).mpr hY'U)
    (fun larger hl _ hle => hmax Y' hY' larger hl hle)
  refine ⟨(c : G), ⟨c.2, mem_centralizer_iff.mpr fun u hu => ?_⟩, ?_⟩
  · have h1 := hfix ⟨u, hu⟩
    have h2 := ambientSubgroupActionHom_apply_coe U O hUO ⟨u, hu⟩ c
    rw [h1] at h2
    have h3 : (u : G) * (c : G) * (u : G)⁻¹ = (c : G) := h2.symm
    calc u * (c : G) = ((u : G) * (c : G) * (u : G)⁻¹) * u := by group
      _ = (c : G) * u := by rw [h3]
  · have hmaps : O.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom.comp O.subtype := by
      ext z
      rfl
    have h4 := congrArg (Subgroup.map O.subtype) hc
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY.le, inf_eq_left.mpr hY'.le] at h4
    exact h4

theorem exists_invariant_isSylowOf_two_normalized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U O A : Subgroup G} (hU : IsPGroup p U) (hUO : U ≤ normalizer (O : Set G))
    (hOp : p.Coprime (Nat.card O)) (hAO : A ≤ normalizer (O : Set G)) (hA2 : IsPGroup 2 A)
    (hUA : U ≤ normalizer (A : Set G)) :
    ∃ Y : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 Y O ∧ U ≤ normalizer (Y : Set G) ∧
      A ≤ normalizer (Y : Set G) := by
  set X : Subgroup G := O ⊔ A with hX
  have hOX : O ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hXO : X ≤ normalizer (O : Set G) := sup_le Subgroup.le_normalizer hAO
  have hUX : U ≤ normalizer (X : Set G) := by
    intro u hu
    have hO' := mem_normalizer_iff_map_conj_eq.mp (hUO hu)
    have hA' := mem_normalizer_iff_map_conj_eq.mp (hUA hu)
    rw [mem_normalizer_iff_map_conj_eq, hX, Subgroup.map_sup, hO', hA']
  have hAcop : p.Coprime (Nat.card A) := by
    obtain ⟨b, hb⟩ := hA2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcopX : p.Coprime (Nat.card X) := coprime_card_sup_of_le_normalizer hAO hOp hAcop
  obtain ⟨Z, hAZ, hZ⟩ := exists_invariantTwoMaximalWithin_containing U X A hAX hA2 hUA
  have hZs := isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUX hcopX hZ
  have hYs := hZs.inf_of_le_normalizer hOX hXO
  refine ⟨Z ⊓ O, hYs, common_normalizer_le_normalizer_inf U Z O hZ.2.2.1 hUO, ?_⟩
  exact common_normalizer_le_normalizer_inf A Z O
    ((hAZ.trans (Subgroup.le_normalizer))) (hAO)

end CFSG.LocalAnalysis.RankFourTheoremC
