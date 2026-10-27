module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Cube
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiRows
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSylow
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicTriality
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxE8Twelve
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ClassLeaves
public import CFSG.Goldschmidt.Final
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.ExcHigh.Leaves
public import CFSG.LieType.SeitzGeneration.ExcHigh.FrameDatum
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Families
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

 

theorem c0_exists_plane {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {m : ℕ} (hm : m = 3 ∨ m = 6) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hd : r ∣ CFSG.RankThree.PartOne.K128.phiNat m (ℓ ^ f)) :
    ∃ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hS := CFSG.RankThree.PartOne.K128.sylowShape_D4 hf K hK σ hσ
    (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) hr hr5 hd
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
  obtain ⟨φ⟩ := hS (P.toSubgroup) P.isPGroup' P.not_dvd_index
  have hne : CFSG.RankThree.PartOne.K128.phiNat m (ℓ ^ f) ≠ 0 := by
    have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
    have hq2 : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    rcases hm with rfl | rfl
    · simp only [CFSG.RankThree.PartOne.K128.phiNat]
      omega
    · simp only [CFSG.RankThree.PartOne.K128.phiNat]
      omega
  have he : 1 ≤ (CFSG.RankThree.PartOne.K128.phiNat m (ℓ ^ f)).factorization r :=
    (Nat.Prime.factorization_pos_of_dvd hr hne hd)
  obtain ⟨E, hEle, hEexp, hEcard, -, hEcomm⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_plane_of_sylowShape_omega he
      P.toSubgroup φ
  refine ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hEcomm x.1 (hEle x.2) y.1 (hEle y.2))⟩⟩,
    fun x hx => hEexp x hx⟩,
    hEcard⟩

theorem c0_isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.IsElementaryAbelian p ↥E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.1 hE

theorem c0_planeGen_of_phi {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} {r : ℕ}
    (hP : CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiPlaneGenAt ε r)
    (hr : r.Prime) (hrℓ : r ≠ ℓ)
    (hd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.Open.IsElemAbelian r E) (hEc : Nat.card E = r ^ 2) :
    Subgroup.closure {k : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ :=
  hP ℓ f hℓ hℓ2 hf K hK σ hσ hr hrℓ hd E (c0_isElementaryAbelian_of_isElemAbelian hE) hEc

theorem c0_iso_cat_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ TwistTag.D4.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.card) :
    Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* Cat ⟨.trialityD4 q, hv⟩) := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ q.card := fun c => hσ c
  obtain ⟨ψ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K hK σ.toRingHom hσ'
  have hσ'' : ∀ c, σ.toRingHom c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ' c, PrimePower.card_def]
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]
  obtain ⟨χ⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4
    q.prime_p q.exponent_pos K hK' σ.toRingHom hσ''
  exact ⟨χ.symm.trans ψ⟩

theorem c0_conj_injective {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : ∀ h : M, g * h * g⁻¹ = h := fun h => by
    have := congrArg (fun φ : MulAut M => φ h) hg
    simpa [MulAut.conj_apply] using this
  have hmem : g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact (mul_inv_eq_iff_eq_mul.1 (hg' h)).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

theorem c0_planeGen_of_extSeit (hgold : CFSG.Goldschmidt.TopStatement) (q : PrimePower)
    (hq : q.p = 2) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ TwistTag.D4.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.card)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  obtain ⟨e⟩ := c0_iso_cat_trialityD4 q hv K hK σ hσ
  haveI : Finite (Cat ⟨.trialityD4 q, hv⟩) := (finite_isSimpleGroup_cat_trialityD4 hv).1
  haveI : IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩) := (finite_isSimpleGroup_cat_trialityD4 hv).2
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv _ e.toEquiv.symm
  haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulEquiv.isSimpleGroup e
  obtain ⟨-, -, hcomm, hcent⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux.d4_group_facts q.prime_p
      q.exponent_pos K
    (by rw [hK, PrimePower.card_def]; rfl) σ (Or.inl fun c => by rw [hσ c, PrimePower.card_def])
  have hnonab : ∃ a b : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hle : commutator ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ ⊥ :=
      Subgroup.commutator_le.2 fun g _ k _ => by
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcon g k
    rw [hcomm] at hle
    have htop := le_bot_iff.1 hle
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    have hgb : g ∈ (⊥ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← htop]
      exact Subgroup.mem_top g
    exact hg (Subgroup.mem_bot.1 hgb)
  have hpne : p ≠ (LieTypeIndex.trialityD4 q).characteristic := by
    rw [LieTypeIndex.characteristic_trialityD4, hq]
    omega
  have hIso : CFSG.RankThree.PartOne.Census3.IsoLie
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (LieTypeIndex.trialityD4 q) :=
    ⟨hv, ⟨e⟩⟩
  have hinj : Function.Injective
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    c0_conj_injective hcent
  set Ein : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hEin
  have hEinE : CFSG.Open.IsElemAbelian p Ein := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 x.2
      obtain ⟨b, hb, hyb⟩ := Subgroup.mem_map.1 y.2
      apply Subtype.ext
      show (↑x : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) * ↑y =
        ↑y * ↑x
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, hE.2 a ha, map_one]
  have hEinc : Nat.card ↥Ein = p ^ 2 := by
    rw [hEin, Subgroup.card_map_of_injective hinj, hEc]
  have hinner : ∀ φ ∈ Ein, ∃ g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      φ = MulAut.conj g := by
    intro φ hφ
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hφ
    exact ⟨a, rfl⟩
  have hres := CFSG.LieType.SeitzGeneration.extSeitzAtInnerFor_trialityD4_even hgold hq
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) hnonab hIso p hp (by omega) hpne trivial Ein
    (c0_isElementaryAbelian_of_isElemAbelian hEinE) hEinc hinner
  have hset : {k : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) |
      ∃ F : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        F ≤ Ein ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k = k} =
      {k : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    ext k
    constructor
    · rintro ⟨F, hFE, hFbot, hFfix⟩
      obtain ⟨φ', hφ'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFbot
      have hφF : (φ' : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ F := φ'.2
      have hφ1 : (φ' : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ 1 :=
        fun h => hφ' (Subtype.ext h)
      obtain ⟨x, hxE, hxφ⟩ := Subgroup.mem_map.1 (hFE hφF)
      refine ⟨x, hxE, fun hx => hφ1 ?_, ?_⟩
      · rw [← hxφ, hx, map_one]
      · have hfix := hFfix _ hφF
        rw [← hxφ, MulAut.conj_apply] at hfix
        exact (mul_inv_eq_iff_eq_mul.1 hfix).symm
    · rintro ⟨x, hxE, hx1, hkx⟩
      refine ⟨Subgroup.zpowers (MulAut.conj x), ?_, ?_, ?_⟩
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_map_of_mem _ hxE
      · intro h
        have h1 := Subgroup.zpowers_eq_bot.1 h
        exact hx1 (hinj (h1.trans (map_one _).symm))
      · intro φ hφ
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
        rw [← map_zpow, MulAut.conj_apply]
        have hc : Commute (x ^ n) k := (show Commute x k from hkx.symm).zpow_left n
        exact mul_inv_eq_iff_eq_mul.2 hc.eq
  rcases hres with h | ⟨h5, -⟩
  · rw [hset] at h
    exact h
  · omega

theorem dvd_phiNat_of_orderOf {p e Q : ℕ} (hp : p.Prime) (he : e = 3 ∨ e = 6)
    (h : orderOf ((Q : ℕ) : ZMod p) = e) :
    p ∣ CFSG.RankThree.PartOne.K128.phiNat e Q := by
  haveI := Fact.mk hp
  have hQ2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  rcases he with rfl | rfl
  · have h3 : ((Q : ℕ) : ZMod p) ^ 3 = 1 := by
      rw [← h]
      exact pow_orderOf_eq_one _
    have hne : ((Q : ℕ) : ZMod p) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at h
      omega
    have hfac : (((Q : ℕ) : ZMod p) - 1) *
        (((Q : ℕ) : ZMod p) ^ 2 + ((Q : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination h3
    have h2 := (mul_eq_zero.1 hfac).resolve_left (sub_ne_zero.2 hne)
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [CFSG.RankThree.PartOne.K128.phiNat]
    push_cast
    exact h2
  · have h6 : ((Q : ℕ) : ZMod p) ^ 6 = 1 := by
      rw [← h]
      exact pow_orderOf_eq_one _
    have h3ne : ((Q : ℕ) : ZMod p) ^ 3 ≠ 1 := by
      intro h1
      have hd : orderOf ((Q : ℕ) : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
      rw [h] at hd
      omega
    have hfac1 : (((Q : ℕ) : ZMod p) ^ 3 - 1) * (((Q : ℕ) : ZMod p) ^ 3 + 1) = 0 := by
      linear_combination h6
    have h3p : ((Q : ℕ) : ZMod p) ^ 3 + 1 = 0 :=
      (mul_eq_zero.1 hfac1).resolve_left (sub_ne_zero.2 h3ne)
    have hfac2 : (((Q : ℕ) : ZMod p) + 1) *
        (((Q : ℕ) : ZMod p) ^ 2 - ((Q : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination h3p
    have hne : ((Q : ℕ) : ZMod p) + 1 ≠ 0 := by
      intro h1
      have hx : ((Q : ℕ) : ZMod p) = -1 := by linear_combination h1
      have h2 : ((Q : ℕ) : ZMod p) ^ 2 = 1 := by rw [hx]; norm_num
      have hd : orderOf ((Q : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [h] at hd
      omega
    have h2 := (mul_eq_zero.1 hfac2).resolve_left hne
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [CFSG.RankThree.PartOne.K128.phiNat]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hQ2]
    push_cast
    exact h2

theorem c0_planeGen_all (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ TwistTag.D4.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.card) {m : ℕ} (hm : m = 3 ∨ m = 6)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ≠ q.p)
    (hd : p ∣ CFSG.RankThree.PartOne.K128.phiNat m q.card)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  by_cases h2 : q.p = 2
  · exact c0_planeGen_of_extSeit CFSG.Goldschmidt.topStatement q h2 hv K hK σ hσ hp hp7 E hE hEc
  · have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
      rw [hK, PrimePower.card_def]
    have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
      rw [hσ c, PrimePower.card_def]
    have hQ2 : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
    have hpr : (p : ℕ) ≠ q.p := hpq
    rcases hm with rfl | rfl
    · have hd' : (p : ℤ) ∣
          ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + 1 * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
        have h := Int.natCast_dvd_natCast.2 hd
        rw [PrimePower.card_def] at h
        simpa [CFSG.RankThree.PartOne.K128.phiNat] using h
      exact c0_planeGen_of_phi q.prime_p h2 q.exponent_pos K hK' σ hσ'
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_one_proved (by omega))
        hp hpq hd' E hE hEc
    · have hd' : (p : ℤ) ∣
          ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + (-1) * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
        have h := Int.natCast_dvd_natCast.2 hd
        rw [PrimePower.card_def] at h
        have hQ : (q.p ^ q.exponent) ≤ (q.p ^ q.exponent) ^ 2 := Nat.le_self_pow (by norm_num) _
        have e6 : ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + (-1) * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 =
            (((q.p ^ q.exponent) ^ 2 - q.p ^ q.exponent + 1 : ℕ) : ℤ) := by
          rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hQ]
          push_cast
          ring
        rw [e6]
        exact Int.natCast_dvd_natCast.2 (by
          simpa [CFSG.RankThree.PartOne.K128.phiNat, PrimePower.card_def] using hd)
      have hp5 : 5 ≤ p := by omega
      have hP := CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hp5
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hp5
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSome_holds p hp5)
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSomeThree_holds p hp5))
      exact c0_planeGen_of_phi q.prime_p h2 q.exponent_pos K hK' σ hσ' hP hp hpq hd' E hE hEc

section FrameIso

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb adjEmb_range
  wordProd_smul_eq_wordMat_mulVec commutator_eq_top_iff e8RootVec isRoot_e8RootVec
  isRoot_iff_exists_e8RootVec d4Nodes)

open CFSG.RankThree.PartOne.TCX.E (d4_transported_equiv_E8)

open CFSG.RankThree.PartOne.KD4L (d4_layer_equiv_E8)

open CFSG.RankThree.Classical2
open CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped commutatorElement

theorem graphFixed_normalize {K : Type} [Field K] [Finite K] {Q : ℕ} (hK : Nat.card K = Q ^ 3)
    (σ : K ≃+* K) (hσ : (∀ c, σ c = c ^ Q) ∨ ∀ c, σ c = c ^ Q ^ 2) :
    ∃ σ' : K ≃+* K, (∀ c, σ' c = c ^ Q) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := by
  have hq3 : ∀ c : K, c ^ (Q ^ 3) = c := by
    haveI := Fintype.ofFinite K
    intro c
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rcases hσ with h | h
  · exact ⟨σ, h, ⟨MulEquiv.refl _⟩⟩
  · refine ⟨σ.symm, fun c => ?_, ?_⟩
    · refine σ.symm_apply_eq.2 ?_
      rw [h, ← pow_mul, show Q * Q ^ 2 = Q ^ 3 by ring, hq3]
    · obtain ⟨f, -⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_of_map_eq
        (CFSG.RankThree.Chevalley.trialityTranspositionAut K)
        (CFSG.RankThree.Chevalley.map_trialityTranspositionAut_graphFixedRootGroup σ)
      exact ⟨f⟩

theorem e8Twelve_frame_isos {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hk : Nat.card K = ℓ ^ f) (w : WeylGroup Tag.E8)
    (hw : w = (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve)
    (D : LangLevi Tag.E8 K w) :
    (∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁) (σ₁ : K₁ ≃+* K₁),
        Nat.card K₁ = (ℓ ^ f) ^ 3 ∧ (∀ c, σ₁ c = c ^ (ℓ ^ f)) ∧
        Nonempty (↥(D.frame ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))) ≃*
          graphFixedRootGroup TwistTag.D4 K₁ σ₁.toRingHom)) ∧
    (∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (σ₂ : K₂ ≃+* K₂),
        Nat.card K₂ = (ℓ ^ f) ^ 3 ∧ (∀ c, σ₂ c = c ^ (ℓ ^ f)) ∧
        Nonempty (↥(D.frame (parabolicRoots Tag.E8 (d4Nodes Tag.E8))) ≃*
          graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom)) := by
  have hℓ : ℓ.Prime := Fact.out
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hk
  have hFr : D.Fr = iterateFrobenius D.L ℓ f :=
    RingHom.ext fun c => by rw [D.hFr, hk, iterateFrobenius_def]
  set n : ModGL Tag.E8 D.L := canonicalRep (coxeterSystem Tag.E8) D.L w with hn
  have hnm : n ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hwn : weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hrat := hrat_perfect (Or.inr (Or.inr ⟨rfl, rfl⟩) : (Tag.E8 = Tag.E6 ∧ 1 = 3) ∨
    (Tag.E8 = Tag.E7 ∧ 1 = 2) ∨ (Tag.E8 = Tag.E8 ∧ 1 = 1)) D
  have hcard1 : Nat.card K = ℓ ^ f := hk
  have hP₂ : fixedRootGroup D (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) =
      rootSpan Tag.E8 D.L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius D.L ℓ f))) := by
    show rootSpan Tag.E8 D.L _ ⊓ twistedFixedPoints n (Units.map (entrywiseHom D.Fr)) = _
    rw [hFr]
  have hact₂ : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
    refine ⟨1, one_mem _, fun α hα => ?_⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
    rw [hwn, one_smul, hw, wordProd_smul_eq_wordMat_mulVec]
    exact e8Twelve_act m hα.2
  obtain ⟨K₂, _, _, σ₂, hK₂, hσ₂, ⟨e₂⟩⟩ := d4_layer_equiv_E8 (L := D.L) (ℓ := ℓ) (f := f) hf
    (1 : Fin Tag.E8.rank) 2 4 (by decide) (by decide) (by decide) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) n hnm hact₂
    (fixedRootGroup D (parabolicRoots Tag.E8 (d4Nodes Tag.E8))) hP₂
  obtain ⟨hfin₂, hcard₂, hcomm₂, hcent₂⟩ := d4_group_facts hℓ hf K₂ hK₂ σ₂ hσ₂
  haveI := hfin₂
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom) :=
    Group.isPerfect_def.2 hcomm₂
  obtain ⟨x₂⟩ := frame_equiv_of_equiv D _ hrat e₂
  have hP₁ : fixedRootGroup D ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) =
      rootSpan Tag.E8 D.L ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius D.L ℓ f))) := by
    show rootSpan Tag.E8 D.L _ ⊓ twistedFixedPoints n (Units.map (entrywiseHom D.Fr)) = _
    rw [hFr]
  have hcert₁ : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (e8v1⁻¹ * weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ * e8v1) • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
    refine ⟨1, one_mem _, fun α hα => ?_⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
    have h : e8v1⁻¹ * weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ * e8v1 =
        (coxeterSystem Tag.E8).wordProd (e8v1word.reverse ++ TwClass.wordE8Twelve ++ e8v1word) := by
      rw [hwn, hw, e8v1, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
        CoxeterSystem.wordProd_reverse]
    rw [h, one_smul, wordProd_smul_eq_wordMat_mulVec]
    exact e8Twelve_actB m hα.2
  obtain ⟨K₁, _, _, σ₁, hK₁, hσ₁, ⟨e₁⟩⟩ := d4_transported_equiv_E8 (L := D.L) (ℓ := ℓ) (f := f) hf
    e8v1 (1 : Fin Tag.E8.rank) 2 4 (by decide) (by decide) (by decide) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) n hnm hcert₁
    (fixedRootGroup D ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))) hP₁
  obtain ⟨hfin₁, hcard₁, hcomm₁, hcent₁⟩ := d4_group_facts hℓ hf K₁ hK₁ σ₁ hσ₁
  haveI := hfin₁
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₁ σ₁.toRingHom) :=
    Group.isPerfect_def.2 hcomm₁
  obtain ⟨x₁⟩ := frame_equiv_of_equiv D _ hrat e₁
  obtain ⟨σ₁', hσ₁', ⟨g₁⟩⟩ := graphFixed_normalize hK₁ σ₁ hσ₁
  obtain ⟨σ₂', hσ₂', ⟨g₂⟩⟩ := graphFixed_normalize hK₂ σ₂ hσ₂
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K₁ σ₁'.toRingHom) :=
    Finite.of_equiv _ g₁.toEquiv
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₁ σ₁'.toRingHom) :=
    Group.IsPerfect.ofSurjective (f := g₁.toMonoidHom) g₁.surjective
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K₂ σ₂'.toRingHom) :=
    Finite.of_equiv _ g₂.toEquiv
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₂ σ₂'.toRingHom) :=
    Group.IsPerfect.ofSurjective (f := g₂.toMonoidHom) g₂.surjective
  obtain ⟨x₁'⟩ :=
    frame_equiv_of_equiv D ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))
      hrat (e₁.trans g₁)
  obtain ⟨x₂'⟩ := frame_equiv_of_equiv D (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) hrat (e₂.trans g₂)
  exact ⟨⟨K₁, inferInstance, inferInstance, σ₁', hK₁, hσ₁', ⟨x₁'⟩⟩,
    ⟨K₂, inferInstance, inferInstance, σ₂', hK₂, hσ₂', ⟨x₂'⟩⟩⟩

theorem e8Twelve_X₁_iso {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hk : Nat.card K = ℓ ^ f)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁) (σ₁ : K₁ ≃+* K₁),
      Nat.card K₁ = (ℓ ^ f) ^ 3 ∧ (∀ c, σ₁ c = c ^ (ℓ ^ f)) ∧
      Nonempty (↥(TwClass.e8Twelve.X₁ D) ≃* graphFixedRootGroup TwistTag.D4 K₁ σ₁.toRingHom) := by
  have h := (e8Twelve_frame_isos hf hk TwClass.e8Twelve.w rfl D).1
  rw [show TwClass.e8Twelve.X₁ D = D.frame TwClass.e8Twelve.S₁ from rfl, e8Twelve_S₁_eq]
  exact h

theorem e8Twelve_X₂_iso {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hk : Nat.card K = ℓ ^ f)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (σ₂ : K₂ ≃+* K₂),
      Nat.card K₂ = (ℓ ^ f) ^ 3 ∧ (∀ c, σ₂ c = c ^ (ℓ ^ f)) ∧
      Nonempty (↥(TwClass.e8Twelve.X₂ D) ≃* graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom) := by
  have h := (e8Twelve_frame_isos hf hk TwClass.e8Twelve.w rfl D).2
  rw [show TwClass.e8Twelve.X₂ D = D.frame TwClass.e8Twelve.S₂ from rfl, e8Twelve_S₂_eq]
  exact h

end FrameIso

section Adjoint

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

variable {τ : Tag} {K : Type} [Field K]

theorem isElemAbelian_map_inj {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (f : G →* H) (hf : Function.Injective f) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hyb⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    show (x : H) * (y : H) = (y : H) * (x : H)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  · obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 hx
    rw [← hxa, ← map_pow, hE.2 a ha, map_one]

theorem closing_restrict {X : Subgroup (ModGL τ K)} (hXa : X ≤ adjointGroup τ K)
    (hC : TwFrameClosing τ K X) (H : Subgroup ↥(adjointGroup τ K))
    (hXH : X.subgroupOf (adjointGroup τ K) ≤ H)
    (hH : ¬ H ≤ Subgroup.normalizer ((X.subgroupOf (adjointGroup τ K) : Subgroup _) :
      Set ↥(adjointGroup τ K))) : H = ⊤ := by
  have hHm_le : H.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hXHm : X ≤ H.map (adjointGroup τ K).subtype := by
    intro x hx
    have hxa : x ∈ adjointGroup τ K := hXa hx
    exact ⟨⟨x, hxa⟩, hXH (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hHmN : ¬ H.map (adjointGroup τ K).subtype ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    intro hN
    apply hH
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hn := (Subgroup.mem_normalizer_iff.1 (hN ⟨h, hh, rfl⟩)) (g : ModGL τ K)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hn
  have hTop := hC (H.map (adjointGroup τ K).subtype) hHm_le hXHm hHmN
  rw [eq_top_iff]
  intro a _
  have hamem : (a : ModGL τ K) ∈ H.map (adjointGroup τ K).subtype := by
    rw [hTop]
    exact a.2
  obtain ⟨h, hh, hha⟩ := hamem
  have hea : h = a := Subtype.ext hha
  exact hea ▸ hh

theorem normalizer_of_subgroupOf {X : Subgroup (ModGL τ K)} (hXa : X ≤ adjointGroup τ K)
    {h : ModGL τ K} (hh : h ∈ adjointGroup τ K)
    (hN : (⟨h, hh⟩ : ↥(adjointGroup τ K)) ∈ Subgroup.normalizer
      ((X.subgroupOf (adjointGroup τ K) : Subgroup _) : Set ↥(adjointGroup τ K))) :
    h ∈ Subgroup.normalizer (X : Set (ModGL τ K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ adjointGroup τ K
  · have hn := (Subgroup.mem_normalizer_iff.1 hN) ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn
    simpa using hn
  · have hgX : g ∉ X := fun hgX => hg (hXa hgX)
    have hhgX : h * g * h⁻¹ ∉ X := by
      intro hX
      apply hg
      have hadj : h * g * h⁻¹ ∈ adjointGroup τ K := hXa hX
      have : g = h⁻¹ * (h * g * h⁻¹) * h := by group
      rw [this]
      exact (adjointGroup τ K).mul_mem ((adjointGroup τ K).mul_mem
        ((adjointGroup τ K).inv_mem hh) hadj) hh
    exact ⟨fun h1 => absurd h1 hgX, fun h2 => absurd h2 hhgX⟩

theorem normSolv_restrict {X : Subgroup (ModGL τ K)} (hXa : X ≤ adjointGroup τ K)
    (hN : TwFrameNormalizerSolvable τ K X) (H : Subgroup ↥(adjointGroup τ K))
    (hH : H ≤ Subgroup.normalizer ((X.subgroupOf (adjointGroup τ K) : Subgroup _) :
      Set ↥(adjointGroup τ K)))
    (hs : Group.IsSolvable ↥(H ⊓ X.subgroupOf (adjointGroup τ K))) :
    Group.IsSolvable ↥H := by
  have hinj : Function.Injective (adjointGroup τ K).subtype := Subtype.val_injective
  have hPadj : H.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hPN : H.map (adjointGroup τ K).subtype ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    rintro _ ⟨h, hh, rfl⟩
    exact normalizer_of_subgroupOf hXa h.2 (hH hh)
  have hmap : (H ⊓ X.subgroupOf (adjointGroup τ K)).map (adjointGroup τ K).subtype =
      H.map (adjointGroup τ K).subtype ⊓ X := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyH, hyX⟩, rfl⟩
      exact ⟨⟨y, hyH, rfl⟩, Subgroup.mem_subgroupOf.1 hyX⟩
    · rintro ⟨⟨y, hyH, hyx⟩, hxX⟩
      have hy : y ∈ X.subgroupOf (adjointGroup τ K) := by
        have h' : (y : ModGL τ K) = x := hyx
        exact Subgroup.mem_subgroupOf.2 (by rw [h']; exact hxX)
      exact ⟨y, ⟨hyH, hy⟩, hyx⟩
  have hsP : Group.IsSolvable ↥(H.map (adjointGroup τ K).subtype ⊓ X) := by
    rw [← hmap]
    haveI := hs
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ _ hinj).toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ hinj).surjective
  have hPs : Group.IsSolvable ↥(H.map (adjointGroup τ K).subtype) :=
    hN _ hPadj hPN hsP
  haveI := hPs
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective H _ hinj).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective H _ hinj).symm.surjective

theorem mem_sup_commute' {G : Type*} [Group G] {A F : Subgroup G}
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) {x : G} (hx : x ∈ A ⊔ F) :
    ∃ a ∈ A, ∃ f ∈ F, x = a * f := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ f ∈ F, x = a * f}
      mul_mem' := by
        rintro _ _ ⟨a, ha, f, hf, rfl⟩ ⟨b, hb, g, hg, rfl⟩
        refine ⟨a * b, A.mul_mem ha hb, f * g, F.mul_mem hf hg, ?_⟩
        have hfb : f * b = b * f := (hc b hb f hf).symm
        calc a * f * (b * g) = a * (f * b) * g := by group
          _ = a * (b * f) * g := by rw [hfb]
          _ = a * b * (f * g) := by group
      one_mem' := ⟨1, A.one_mem, 1, F.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, f, hf, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, f⁻¹, F.inv_mem hf, ?_⟩
        have hcomm : a⁻¹ * f⁻¹ = f⁻¹ * a⁻¹ := (Commute.inv_inv (hc a ha f hf)).eq
        rw [mul_inv_rev]
        exact hcomm.symm }
  have hle : A ⊔ F ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, F.one_mem, by simp⟩)
      (fun f hf => ⟨1, A.one_mem, f, hf, by simp⟩)
  exact hle hx

theorem sup_subgroupOf_adjoint {X₁ X₂ : Subgroup (ModGL τ K)}
    (h₁ : X₁ ≤ adjointGroup τ K) (h₂ : X₂ ≤ adjointGroup τ K)
    (hc : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) :
    (X₁ ⊔ X₂).subgroupOf (adjointGroup τ K) =
      X₁.subgroupOf (adjointGroup τ K) ⊔ X₂.subgroupOf (adjointGroup τ K) := by
  refine le_antisymm ?_ (sup_le (fun _ hx => Subgroup.mem_subgroupOf.2
    ((le_sup_left : X₁ ≤ X₁ ⊔ X₂) (Subgroup.mem_subgroupOf.1 hx)))
    (fun _ hx => Subgroup.mem_subgroupOf.2
      ((le_sup_right : X₂ ≤ X₁ ⊔ X₂) (Subgroup.mem_subgroupOf.1 hx))))
  intro x hx
  have hx' : (x : ModGL τ K) ∈ X₁ ⊔ X₂ := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_commute' hc hx'
  have hxe : x = (⟨a, h₁ ha⟩ : ↥(adjointGroup τ K)) * ⟨b, h₂ hb⟩ := Subtype.ext hab
  rw [hxe]
  exact mul_mem ((le_sup_left : X₁.subgroupOf (adjointGroup τ K) ≤
      X₁.subgroupOf (adjointGroup τ K) ⊔ X₂.subgroupOf (adjointGroup τ K))
    (Subgroup.mem_subgroupOf.2 ha))
    ((le_sup_right : X₂.subgroupOf (adjointGroup τ K) ≤
      X₁.subgroupOf (adjointGroup τ K) ⊔ X₂.subgroupOf (adjointGroup τ K))
    (Subgroup.mem_subgroupOf.2 hb))

theorem plane_gen_adjoint {X : Subgroup (ModGL τ K)} (hXa : X ≤ adjointGroup τ K)
    (W : Subgroup ↥X)
    (hgen : Subgroup.closure {g : ↥X | ∃ x ∈ W, x ≠ 1 ∧ g * x = x * g} = ⊤) :
    X.subgroupOf (adjointGroup τ K) ≤ Subgroup.closure {g : ↥(adjointGroup τ K) |
      g ∈ X.subgroupOf (adjointGroup τ K) ∧
        ∃ x ∈ W.map (Subgroup.inclusion hXa), x ≠ 1 ∧ g * x = x * g} := by
  intro y hy
  set z : ↥X := ⟨(y : ModGL τ K), Subgroup.mem_subgroupOf.1 hy⟩ with hz
  have hzS : z ∈ Subgroup.closure {g : ↥X | ∃ x ∈ W, x ≠ 1 ∧ g * x = x * g} := by
    rw [hgen]
    exact Subgroup.mem_top z
  have hmap := Subgroup.mem_map_of_mem (Subgroup.inclusion hXa) hzS
  rw [MonoidHom.map_closure] at hmap
  have hy' : Subgroup.inclusion hXa z = y := Subtype.ext rfl
  rw [hy'] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨g, ⟨x, hxW, hx1, hgx⟩, rfl⟩
  refine ⟨Subgroup.mem_subgroupOf.2 g.2, Subgroup.inclusion hXa x, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem _ hxW
  · intro h1
    exact hx1 (Subgroup.inclusion_injective hXa (h1.trans (map_one _).symm))
  · have := congrArg (Subgroup.inclusion hXa) hgx
    simpa [map_mul] using this

end Adjoint

section Assembly

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

theorem frameDatumIn_adjoint {K : Type} [Field K] {X₁ X₂ : Subgroup (ModGL TwClass.e8Twelve.tag K)}
    {p o : ℕ} (hp : p.Prime)
    (h₁ : X₁ ≤ adjointGroup TwClass.e8Twelve.tag K) (h₂ : X₂ ≤ adjointGroup TwClass.e8Twelve.tag K)
    (hc : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hcl : TwFrameClosing TwClass.e8Twelve.tag K (X₁ ⊔ X₂))
    (hnm : TwFrameNormalizerSolvable TwClass.e8Twelve.tag K (X₁ ⊔ X₂))
    (hz : Nat.card ↥(Subgroup.center ↥X₁) = 1)
    (hb₁ : Nat.card ↥X₁ ≤ o) (hb₂ : Nat.card ↥X₂ ≤ o)
    (W₁ : Subgroup ↥X₁) (hW₁ : IsElemAbelian p W₁) (hW₁c : Nat.card ↥W₁ = p ^ 2)
    (hg₁ : Subgroup.closure {g : ↥X₁ | ∃ x ∈ W₁, x ≠ 1 ∧ g * x = x * g} = ⊤)
    (W₂ : Subgroup ↥X₂) (hW₂ : IsElemAbelian p W₂) (hW₂c : Nat.card ↥W₂ = p ^ 2)
    (hg₂ : Subgroup.closure {g : ↥X₂ | ∃ x ∈ W₂, x ≠ 1 ∧ g * x = x * g} = ⊤) :
    FrameDatumIn ↥(adjointGroup TwClass.e8Twelve.tag K) p o := by
  have hi₁ : Function.Injective (Subgroup.inclusion h₁) := Subgroup.inclusion_injective h₁
  have hi₂ : Function.Injective (Subgroup.inclusion h₂) := Subgroup.inclusion_injective h₂
  refine ⟨W₁.map (Subgroup.inclusion h₁), W₂.map (Subgroup.inclusion h₂),
    X₁.subgroupOf (adjointGroup TwClass.e8Twelve.tag K),
    X₂.subgroupOf (adjointGroup TwClass.e8Twelve.tag K), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isElemAbelian_map_inj _ hi₁ hW₁
  · exact isElemAbelian_map_inj _ hi₂ hW₂
  · rw [Subgroup.card_map_of_injective hi₁]
    exact hW₁c
  · rw [Subgroup.card_map_of_injective hi₂]
    exact hW₂c
  · rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    obtain ⟨w₁, -, rfl⟩ := Subgroup.mem_map.1 hx1
    obtain ⟨w₂, -, hw⟩ := Subgroup.mem_map.1 hx2
    have hval : (w₂ : ModGL TwClass.e8Twelve.tag K) = (w₁ : ModGL TwClass.e8Twelve.tag K) :=
      congrArg Subtype.val hw
    have hcen : w₁ ∈ Subgroup.center ↥X₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : ModGL TwClass.e8Twelve.tag K) * (w₁ : ModGL TwClass.e8Twelve.tag K) =
        (w₁ : ModGL TwClass.e8Twelve.tag K) * (g : ModGL TwClass.e8Twelve.tag K)
      rw [← hval]
      exact hc _ g.2 _ w₂.2
    have h1 : w₁ = 1 := by
      rw [Subgroup.card_eq_one] at hz
      rw [hz, Subgroup.mem_bot] at hcen
      exact hcen
    rw [h1, map_one]
  · intro a ha b hb
    obtain ⟨w₁, -, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨w₂, -, rfl⟩ := Subgroup.mem_map.1 hb
    apply Subtype.ext
    show (w₁ : ModGL TwClass.e8Twelve.tag K) * (w₂ : ModGL TwClass.e8Twelve.tag K) =
      (w₂ : ModGL TwClass.e8Twelve.tag K) * (w₁ : ModGL TwClass.e8Twelve.tag K)
    exact hc _ w₁.2 _ w₂.2
  · intro y hy
    obtain ⟨w₁, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_subgroupOf.2 w₁.2
  · intro y hy
    obtain ⟨w₂, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_subgroupOf.2 w₂.2
  · intro a ha b hb
    apply Subtype.ext
    exact hc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb)
  · intro g hg b hb
    obtain ⟨w₂, -, rfl⟩ := Subgroup.mem_map.1 hb
    apply Subtype.ext
    exact hc _ (Subgroup.mem_subgroupOf.1 hg) _ w₂.2
  · intro g hg b hb
    obtain ⟨w₁, -, rfl⟩ := Subgroup.mem_map.1 hb
    apply Subtype.ext
    exact (hc _ w₁.2 _ (Subgroup.mem_subgroupOf.1 hg)).symm
  · exact plane_gen_adjoint h₁ W₁ hg₁
  · exact plane_gen_adjoint h₂ W₂ hg₂
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv]
    exact hb₁
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv]
    exact hb₂
  · intro H hH hN
    have hH' : (X₁ ⊔ X₂).subgroupOf (adjointGroup TwClass.e8Twelve.tag K) ≤ H := by
      rw [sup_subgroupOf_adjoint h₁ h₂ hc]
      exact hH
    have hN' : ¬ H ≤ Subgroup.normalizer
        ((((X₁ ⊔ X₂).subgroupOf (adjointGroup TwClass.e8Twelve.tag K) :
          Subgroup ↥(adjointGroup TwClass.e8Twelve.tag K)) :
          Set ↥(adjointGroup TwClass.e8Twelve.tag K))) := by
      rw [sup_subgroupOf_adjoint h₁ h₂ hc]
      exact hN
    exact closing_restrict (sup_le h₁ h₂) hcl H hH' hN'
  · intro H hH hs
    rw [← sup_subgroupOf_adjoint h₁ h₂ hc] at hH hs
    exact normSolv_restrict (sup_le h₁ h₂) hnm H hH hs

theorem e8FrameData_of (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) {p e : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ≠ q.p) (he3 : e = 3 ∨ e = 6)
    (he : orderOf ((q.card : ℕ) : ZMod p) = e) : E8FrameData q hv p := by
  obtain ⟨K, _, _, hK, -, ⟨e8⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  obtain ⟨D⟩ := exists_langLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w
    (TwClass.w_theta TwClass.e8Twelve)
  have hfr := e8Twelve_frames K D
  have hmin : TwClass.e8Twelve.minQ ≤ Nat.card K := by
    show 2 ≤ Nat.card K
    exact Finite.one_lt_card
  have hd : p ∣ CFSG.RankThree.PartOne.K128.phiNat e q.card := dvd_phiNat_of_orderOf hp he3 he
  have hd' : p ∣ CFSG.RankThree.PartOne.K128.phiNat e (q.p ^ q.exponent) := by
    rw [PrimePower.card_def] at hd
    exact hd
  obtain ⟨K₁, _, _, σ₁, hK₁, hσ₁, ⟨χ₁⟩⟩ := e8Twelve_X₁_iso q.exponent_pos hk D
  obtain ⟨K₂, _, _, σ₂, hK₂, hσ₂, ⟨χ₂⟩⟩ := e8Twelve_X₂_iso q.exponent_pos hk D
  have hK₁' : Nat.card K₁ = q.card ^ TwistTag.D4.order := by
    rw [hK₁, PrimePower.card_def]
    rfl
  have hK₂' : Nat.card K₂ = q.card ^ TwistTag.D4.order := by
    rw [hK₂, PrimePower.card_def]
    rfl
  have hσ₁' : ∀ c, σ₁ c = c ^ q.card := fun c => by rw [hσ₁ c, PrimePower.card_def]
  have hσ₂' : ∀ c, σ₂ c = c ^ q.card := fun c => by rw [hσ₂ c, PrimePower.card_def]
  obtain ⟨E₁, hE₁, hE₁c⟩ := c0_exists_plane q.exponent_pos K₁ hK₁ σ₁ hσ₁ he3 hp (by omega) hd'
  obtain ⟨E₂, hE₂, hE₂c⟩ := c0_exists_plane q.exponent_pos K₂ hK₂ σ₂ hσ₂ he3 hp (by omega) hd'
  have hg₁E := c0_planeGen_all q (LieTypeIndex.valid_trialityD4 q) K₁ hK₁' σ₁ hσ₁' he3 hp hp7
    hpq hd E₁ hE₁ hE₁c
  have hg₂E := c0_planeGen_all q (LieTypeIndex.valid_trialityD4 q) K₂ hK₂' σ₂ hσ₂' he3 hp hp7
    hpq hd E₂ hE₂ hE₂c
  have hWE₁ : (E₁.map χ₁.symm.toMonoidHom).map χ₁.toMonoidHom = E₁ := by
    rw [Subgroup.map_map]
    have hid : χ₁.toMonoidHom.comp χ₁.symm.toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      exact χ₁.apply_symm_apply x
    rw [hid, Subgroup.map_id]
  have hWE₂ : (E₂.map χ₂.symm.toMonoidHom).map χ₂.toMonoidHom = E₂ := by
    rw [Subgroup.map_map]
    have hid : χ₂.toMonoidHom.comp χ₂.symm.toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      exact χ₂.apply_symm_apply x
    rw [hid, Subgroup.map_id]
  have hW₁ : IsElemAbelian p (E₁.map χ₁.symm.toMonoidHom) :=
    isElemAbelian_map_inj _ χ₁.symm.injective hE₁
  have hW₂ : IsElemAbelian p (E₂.map χ₂.symm.toMonoidHom) :=
    isElemAbelian_map_inj _ χ₂.symm.injective hE₂
  have hW₁c : Nat.card ↥(E₁.map χ₁.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective χ₁.symm.injective]
    exact hE₁c
  have hW₂c : Nat.card ↥(E₂.map χ₂.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective χ₂.symm.injective]
    exact hE₂c
  have hg₁ : Subgroup.closure {g : ↥(TwClass.e8Twelve.X₁ D) |
      ∃ x ∈ E₁.map χ₁.symm.toMonoidHom, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
    refine closure_eq_top_of_mulEquiv χ₁ (E₁.map χ₁.symm.toMonoidHom) ?_
    rw [hWE₁]
    exact hg₁E
  have hg₂ : Subgroup.closure {g : ↥(TwClass.e8Twelve.X₂ D) |
      ∃ x ∈ E₂.map χ₂.symm.toMonoidHom, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
    refine closure_eq_top_of_mulEquiv χ₂ (E₂.map χ₂.symm.toMonoidHom) ?_
    rw [hWE₂]
    exact hg₂E
  have hA := frameDatumIn_adjoint hp (inf_le_left) (inf_le_left)
    (frame_commute TwClass.e8Twelve D) (twClosing_e8Twelve K D) (twNormalizer_e8Twelve K hmin D)
    hfr.2.2 hfr.1.le hfr.2.1.le _ hW₁ hW₁c hg₁ _ hW₂ hW₂c hg₂
  have hC := FrameDatumIn.of_mulEquiv e8 hA
  rw [hK] at hC
  exact hC

theorem e8FrameFactors_three : E8FrameFactors 3 :=
  fun q hv p hp hp7 hpq he => e8FrameData_of q hv hp hp7 hpq (Or.inl rfl) he

theorem e8FrameFactors_six : E8FrameFactors 6 :=
  fun q hv p hp hp7 hpq he => e8FrameData_of q hv hp hp7 hpq (Or.inr rfl) he

end Assembly

end CFSG.LieType.SeitzGeneration.ExcHigh
