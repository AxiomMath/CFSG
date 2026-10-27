module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46F2
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo1
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
public import CFSG.Sporadic.Bridge.Co1Surj

public section


namespace CFSG.LocalAnalysis.GLTheoremA.S8.CoRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

variable {G : Type} [Group G] [Finite G]

theorem lift_quot_not_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    {W' T' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hW' : IsElemAbelian p W') (hT' : IsPGroup 2 T')
    (hT'1 : T' ≠ ⊥) (hWT : W' ≤ Subgroup.normalizer (T' : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    ∃ W U : Subgroup G, W ≤ X ∧ IsElemAbelian p W ∧ Nat.card W = Nat.card W' ∧ U ≤ X ∧
      IsPGroup 2 U ∧ ¬ U ≤ GLAPPrimeCoreOf p X ∧ W ≤ Subgroup.normalizer (U : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ : Subgroup ↥X := GLAPPrimeCore p ↥X with hN₀
  have hN : ¬ p ∣ Nat.card N₀ :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
  obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift N₀ hN hW'
  set T₁ : Subgroup ↥X := T'.comap (QuotientGroup.mk' N₀) with hT₁
  have hT₁card : Nat.card T₁ = Nat.card N₀ * Nat.card T' :=
    QuotientGroup.card_preimage_mk N₀ (T' : Set (↥X ⧸ N₀))
  obtain ⟨k, hk⟩ := hT'.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hT'1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have hT₁cop : Nat.Coprime p (Nat.card T₁) := by
    rw [hT₁card, hk]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h2T₁ : 2 ∣ Nat.card T₁ := by
    rw [hT₁card, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hST : S ≤ Subgroup.normalizer (T₁ : Set ↥X) := by
    intro s hs
    have hsW' : QuotientGroup.mk' N₀ s ∈ W' := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem _ hs
    have hnorm := Subgroup.mem_normalizer_iff.1 (hWT hsW')
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have := hnorm (QuotientGroup.mk' N₀ t)
    simpa [hT₁, Subgroup.mem_comap, map_mul, map_inv] using this
  obtain ⟨U', -, hU'2, -, hSU', hU'card⟩ :=
    S3.exists_invariant_sylow hp Nat.prime_two hSel.isPGroup hST hT₁cop h2T₁
  refine ⟨S.map X.subtype, U'.map X.subtype, Subgroup.map_subtype_le _, hSel.map _, ?_,
    Subgroup.map_subtype_le _, hU'2.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hScard]
  ·
    intro hle
    have hU'N : U' ≤ N₀ := by
      intro u hu
      have : (u : G) ∈ GLAPPrimeCoreOf p X := hle ⟨u, hu, rfl⟩
      unfold GLAPPrimeCoreOf at this
      obtain ⟨v, hv, hvu⟩ := this
      rw [← Subtype.ext hvu]
      exact hv
    have hdvd : Nat.card U' ∣ Nat.card N₀ := Subgroup.card_dvd_of_le hU'N
    have hn0 : Nat.card N₀ ≠ 0 := Nat.card_pos.ne'
    have hf : (Nat.card N₀ * 2 ^ k).factorization 2 = (Nat.card N₀).factorization 2 + k := by
      simp [Nat.factorization_mul hn0 (pow_ne_zero _ two_ne_zero), Nat.factorization_pow,
        Nat.prime_two.factorization_self]
    rw [hU'card, hT₁card, hk, hf] at hdvd
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp hdvd
    omega
  · intro w hw
    obtain ⟨s, hs, rfl⟩ := hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s * u * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSU' hs) u).1 hu, by simp⟩
    · rintro ⟨u, hu, hy⟩
      refine ⟨s⁻¹ * u * s, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hSU' (S.inv_mem hs)) u).1 hu
        simpa using this
      · have h1 : (u : G) = (s : G) * y * (s : G)⁻¹ := hy
        simp only [map_mul, map_inv, Subgroup.subtype_apply]
        rw [h1]
        group

theorem lift_elemAbelian {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    {W' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hW' : IsElemAbelian p W') :
    ∃ W : Subgroup G, W ≤ X ∧ IsElemAbelian p W ∧ Nat.card W = Nat.card W' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
  obtain ⟨S, hSel, -, hScard⟩ := exists_elemAbelian_lift _ hN hW'
  exact ⟨S.map X.subtype, Subgroup.map_subtype_le _, hSel.map _,
    by rw [Subgroup.card_map_of_injective X.subtype_injective, hScard]⟩

theorem isElemAbelian_of_class {Q : Type*} [Group Q] {p : ℕ} {E : Subgroup Q}
    (h : CFSG.IsElementaryAbelian p E) : IsElemAbelian p E :=
  ⟨h.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) x hx⟩

theorem isElemAbelian_map_equiv {Q R : Type*} [Group Q] [Group R] {p : ℕ} (ψ : Q ≃* R)
    {E : Subgroup Q} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map ψ.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨a', ha', rfl⟩
    rw [← map_pow, hE.2 a' ha', map_one]

theorem exists_elemAbelian_of_equiv {Y X : Type*} [Group Y] [Group X] {k : ℕ}
    (hE : ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k) (ψ : Y ≃* X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  obtain ⟨E, hE, hc⟩ := hE
  exact ⟨E.map ψ.toMonoidHom, isElemAbelian_map_equiv ψ hE,
    by rw [Subgroup.card_map_of_injective ψ.injective, hc]⟩

theorem exists_local_of_equiv {Y X : Type*} [Group Y] [Group X] {k : ℕ}
    (h : ∃ U : Subgroup Y, IsPGroup 2 U ∧ U ≠ ⊥ ∧ ∃ E : Subgroup Y,
      E ≤ Subgroup.normalizer (U : Set Y) ∧ CFSG.IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ k)
    (ψ : Y ≃* X) :
    ∃ U E : Subgroup X, IsPGroup 2 U ∧ U ≠ ⊥ ∧ E ≤ Subgroup.normalizer (U : Set X) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ := h
  refine ⟨U.map ψ.toMonoidHom, E.map ψ.toMonoidHom, hU2.map _,
    fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U ψ.injective).mp h), ?_,
    isElemAbelian_map_equiv ψ (isElemAbelian_of_class hEe),
    by rw [Subgroup.card_map_of_injective ψ.injective, hEc]⟩
  exact (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)

theorem i1016Co2At_holds
    (G : Type) [Group G] [Finite G] : I1016Co2At G := by
  intro X L _ hL hcat
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Finite CFSG.Blueprint.NativeSporadic.Co2 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  haveI : Group.IsPerfect (PQuot 3 L) := ⟨hq.1⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  let eS : PSimple 3 L ≃* CFSG.Blueprint.NativeSporadic.Co2 := e.trans b.symm
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_kernelTrivialAt
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.kernelTrivialAt_three_Co2 eS
      (I2611.isPGroup_center_pQuot' hp3 L)
  let ψ : PQuot 3 L ≃* CFSG.Blueprint.NativeSporadic.Co2 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eS
  refine ⟨by rw [hZ, Subgroup.card_bot], ?_, ?_⟩
  · obtain ⟨Eb, hEb, hEbc⟩ :=
      exists_elemAbelian_of_equiv CFSG.SectionRank.Co2_elementary_three_rank_four ψ.symm
    obtain ⟨W, hWL, hWe, hWc⟩ := lift_elemAbelian hp3 hEb
    exact ⟨W, hWL, hWe, hWc.trans hEbc⟩
  · obtain ⟨U, E, hU2, hU1, hEN, hEe, hEc⟩ := exists_local_of_equiv
      (CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hp3 (k := 3) (by norm_num)
        CFSG.RankThree.PartTwo.Census.three_le_localRank_nativeCo2) ψ.symm
    obtain ⟨W, V, hWL, hWe, hWc, hVL, hV2, hVO, hWV⟩ :=
      lift_quot_not_le hp3 (by norm_num) hEe hU2 hU1 hEN
    exact ⟨W, V, hWL, hWe, hWc.trans hEc, hVL, hV2, hVO, hWV⟩

section Co1


theorem co1_row {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (eS : PSimple 3 K ≃* CFSG.Blueprint.NativeSporadic.Co1) :
    Subgroup.center (PQuot 3 K) = ⊥ ∧
    ∃ E U : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 4 ∧ U ≤ K ∧ IsPGroup 2 U ∧
      ¬ U ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (U : Set G) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Finite CFSG.Blueprint.NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hK
  haveI : Group.IsPerfect (PQuot 3 K) := ⟨hq.1⟩
  have hZ : Subgroup.center (PQuot 3 K) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_kernelTrivialAt
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.kernelTrivialAt_three_Co1 eS
      (I2611.isPGroup_center_pQuot' hp3 K)
  let ψ : PQuot 3 K ≃* CFSG.Blueprint.NativeSporadic.Co1 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eS
  refine ⟨hZ, ?_⟩
  obtain ⟨U, E, hU2, hU1, hEN, hEe, hEc⟩ := exists_local_of_equiv
    (CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hp3 (k := 4) (by norm_num)
      CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Co1) ψ.symm
  obtain ⟨W, V, hWL, hWe, hWc, hVL, hV2, hVO, hWV⟩ :=
    lift_quot_not_le hp3 (by norm_num) hEe hU2 hU1 hEN
  exact ⟨W, V, hWL, hWe, hWc.trans hEc, hVL, hV2, hVO, hWV⟩

theorem i1016CoAt_holds (G : Type) [Group G] [Finite G] : I1016CoAt G := by
  intro X K hK hsp
  obtain ⟨i, hi, ⟨e⟩⟩ := hsp
  cases i with
  | sporadic s =>
    have hs : s = .Co1 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
    exact co1_row hK (e.trans b.symm)
  | _ => exact absurd hi (by simp [isSporIdx])

theorem i1016Co1At_holds (G : Type) [Group G] [Finite G] : S8.L83.I1016Co1At G := by
  intro X K hK hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  obtain ⟨hZ, E, U, hEK, hEe, hEc, hUK, hU2, hUO, hEU⟩ := co1_row hK (e.trans b.symm)
  refine ⟨E, U, hEK, hEe, hEc, hUK, fun h => hUO (h ▸ bot_le), hU2, hEU, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  rw [Subgroup.mem_bot]
  have hxK : x ∈ K := hEK hxE
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
  have hcen : π ⟨x, hxK⟩ ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) k k.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact S8.L84.eq_one_of_mem_core Nat.prime_three ⟨_, hcen, rfl⟩ (hEe.2 x hxE)

theorem i1016At89_co1 (G : Type) [Group G] [Finite G] :
    ∀ X J : Subgroup G, CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J →
      catalogIs (PSimple 3 J) (sporIs .Co1) →
      ∃ E V : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ E ⊓ centerOf J = ⊥ ∧
        V ≤ J ∧ IsPGroup 2 V ∧ V ≠ ⊥ ∧ E ≤ Subgroup.normalizer (V : Set G) := by
  intro X J _ hJ hcat
  obtain ⟨E, V, hEJ, hEe, hEc, hVJ, hV1, hV2, hEV, hEC⟩ := i1016Co1At_holds G X J hJ hcat
  refine ⟨E, V, hEJ, hEe, hEc, ?_, hVJ, hV2, hV1, hEV⟩
  refine le_bot_iff.mp (le_trans (inf_le_inf_left E ?_) (le_of_eq hEC))
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)

end Co1

end CFSG.LocalAnalysis.GLTheoremA.S8.CoRows
