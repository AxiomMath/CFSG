module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

section Generic

theorem sl2Eight_eq_one_of_commute {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {A B : SL2 K} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) (hB7 : B ^ 7 = 1) (hAB : A * B = B * A) :
    B = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set D := (HSLHom K).range with hD
  have hDcard : Nat.card D = 7 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective (f := HSLHom K) HSLHom_injective).toEquiv,
      Nat.card_units, hK]
  have hSL : Nat.card (SL2 K) = 7 * 72 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hfac : (Nat.card (SL2 K)).factorization 7 = 1 := by
    rw [hSL, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 72)]
  let Q : Sylow 7 (SL2 K) := Sylow.ofCard D (by rw [hDcard, hfac, pow_one])
  have hE : IsPGroup 7 (Subgroup.zpowers B) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB7, one_zpow]
  obtain ⟨P, hP⟩ := exists_conj_le_sylow' Q _ hE
  have hmem : P * B * P⁻¹ ∈ D := by
    have h1 : P * B * P⁻¹ ∈ (Subgroup.zpowers B).map (MulAut.conj P).toMonoidHom :=
      ⟨B, Subgroup.mem_zpowers B, rfl⟩
    have h2 := hP h1
    rwa [Sylow.coe_ofCard] at h2
  obtain ⟨s, hs⟩ := hmem
  by_contra hB1
  have hs7 : s ^ 7 = 1 := by
    apply HSLHom_injective (K := K)
    rw [map_pow, map_one, hs, conj_pow, hB7, mul_one, mul_inv_cancel]
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hB1
    have h1 : P * B * P⁻¹ = 1 := by rw [← hs, map_one]
    calc B = P⁻¹ * (P * B * P⁻¹) * P := by group
      _ = 1 := by rw [h1]; group
  have hs2 : s ^ 2 ≠ 1 := by
    intro h
    apply hs1
    calc s = s ^ 7 * ((s ^ 2)⁻¹) ^ 3 := by group
      _ = 1 := by rw [hs7, h]; group
  have hcomm : HSL s * (P * A * P⁻¹) = (P * A * P⁻¹) * HSL s := by
    rw [← HSLHom_apply, hs]
    calc P * B * P⁻¹ * (P * A * P⁻¹) = P * (B * A) * P⁻¹ := by group
      _ = P * (A * B) * P⁻¹ := by rw [hAB]
      _ = P * A * P⁻¹ * (P * B * P⁻¹) := by group
  obtain ⟨u, hu⟩ := eq_HSL_of_commute_HSL hs2 hcomm
  have hu3 : u ^ 3 = 1 := by
    apply HSLHom_injective (K := K)
    rw [map_pow, map_one, HSLHom_apply, ← hu, conj_pow, hA3, mul_one, mul_inv_cancel]
  have hu7 : u ^ 7 = 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := u)
    rwa [Nat.card_units, hK] at h
  have hu1 : u = 1 := by
    calc u = u ^ 7 * ((u ^ 3)⁻¹) ^ 2 := by group
      _ = 1 := by rw [hu7, hu3]; group
  apply hA1
  have h1 : P * A * P⁻¹ = 1 := by rw [hu, hu1, ← HSLHom_apply, map_one]
  calc A = P⁻¹ * (P * A * P⁻¹) * P := by group
    _ = 1 := by rw [h1]; group

variable {G : Type*} [Group G] {p : ℕ}

theorem noNormalPPrime_of_map_mulAut (e : MulAut G) {L : Subgroup G}
    (h : NoNormalPPrime p (L.map e.toMonoidHom)) : NoNormalPPrime p L := by
  intro N hNL hNn hNc
  have hb := h (N.map e.toMonoidHom) (Subgroup.map_mono hNL) (by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨y * x * y⁻¹, hNn y hy x hx, by simp⟩)
    (by rwa [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective])
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) N e.injective).1 hb

theorem noNormalPPrime_centralizer_of_conj (g s : G)
    (h : NoNormalPPrime p (Subgroup.centralizer ({g * s * g⁻¹} : Set G))) :
    NoNormalPPrime p (Subgroup.centralizer ({s} : Set G)) := by
  refine noNormalPPrime_of_map_mulAut (MulAut.conj g) ?_
  have e : (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * s * g⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
        _ = g * (s * y) * g⁻¹ := by rw [hy]
        _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hx]
        _ = s * (g⁻¹ * x * g) := by group
  rwa [e]

end Generic

section G2Eight


variable {K : Type} [Field K] [Finite K]

theorem noNormalPPrime_centralizer_g2Short_eight (hK : Nat.card K = 8)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  intro R hRC hRn hRc
  set C := Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) with hC
  have h3 : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  have hQ : CFSG.IsQuasisimple C :=
    KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 (by norm_num [hK]) hzS hz3 hz1
  have hK8 : Nat.card K = 2 ^ 3 := hK.trans (by norm_num)
  have hZ : Nat.card (Subgroup.center C) = 3 := by
    haveI : CharP K 2 :=
      LocalTwoBalance.Cross.G2Aux.charP_two_of_even_natCard K (by rw [hK]; decide)
    obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' K
    haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
    obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU (p := 2) (f := 3)
      hK8 h3 hdeg hzS hz3 hz1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact StatedCenterThree.card_center_statedSU_three
      (by rw [natCard_quadratic hdeg, hK8]) (by norm_num)
  have hN : (R.subgroupOf C).Normal := ⟨fun n hn g => hRn g g.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with h | h
  · exfalso
    have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hzR : z ∈ R := by
      have hmem : (⟨z, hzC⟩ : C) ∈ R.subgroupOf C := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
    have h3R : 3 ∣ Nat.card R := by
      have h1 := Subgroup.orderOf_dvd_natCard R hzR
      rwa [orderOf_eq_prime hz3 hz1] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd hRc h3R) (by norm_num)
  · have h1 : Nat.card (R.subgroupOf C) ∣ 3 := by
      have h2 := Subgroup.card_dvd_of_le h
      rwa [hZ] at h2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv] at h1
    exact Subgroup.eq_bot_of_card_eq R (Nat.Coprime.eq_one_of_dvd hRc.symm h1)

theorem noNormalPPrime_centralizer_g2Long_eight (hK : Nat.card K = 8)
    {z : adjointGroup .G2 K} (hzM : z ∈ g2LongSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  intro R hRC hRn hRc
  have hK4 : 4 ≤ Nat.card K := by norm_num [hK]
  obtain ⟨hB1, hB2⟩ := g2ThreeBCentMinus_holds K (by norm_num [hK]) hK4 z hzM hz3 hz1
  have hSC : g2ShortSL2 K ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) :=
    fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (g2Short_commute_g2Long hs hzM)
  have hX : ∀ c ∈ R, c ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) →
      c = 1 := by
    intro c hcR hcS
    have hcM : c ∈ g2LongSL2 K := mem_g2LongSL2_of_mem_centralizer (by norm_num [hK]) hcS
    have h63 : Nat.card K ^ 2 - 1 = 3 * (3 * 7) := by norm_num [hK]
    have hc63 : c ^ (3 * (3 * 7)) = 1 := h63 ▸ hB2 c (hRC hcR) hcS
    have hco : Nat.Coprime (orderOf c) 3 :=
      (hRc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R hcR)).symm
    have hc7 : c ^ 7 = 1 := orderOf_dvd_iff_pow_eq_one.1
      (hco.dvd_of_dvd_mul_left (hco.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hc63)))
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 (hRC hcR)
    obtain ⟨e⟩ := nonempty_mulEquiv_g2LongSL2 (K := K)
    have hzM3 : (⟨z, hzM⟩ : g2LongSL2 K) ^ 3 = 1 := Subtype.ext (by simp [hz3])
    have hcM7 : (⟨c, hcM⟩ : g2LongSL2 K) ^ 7 = 1 := Subtype.ext (by simp [hc7])
    have hzM1 : (⟨z, hzM⟩ : g2LongSL2 K) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hzc : (⟨z, hzM⟩ : g2LongSL2 K) * ⟨c, hcM⟩ = ⟨c, hcM⟩ * ⟨z, hzM⟩ :=
      Subtype.ext hcz.symm
    have hB := sl2Eight_eq_one_of_commute hK (A := e.symm ⟨z, hzM⟩) (B := e.symm ⟨c, hcM⟩)
      (by rw [← map_pow, hzM3, map_one])
      (fun h => hzM1 (e.symm.injective (h.trans (map_one _).symm)))
      (by rw [← map_pow, hcM7, map_one]) (by rw [← map_mul, ← map_mul, hzc])
    have h1 : (⟨c, hcM⟩ : g2LongSL2 K) = 1 := e.symm.injective (hB.trans (map_one _).symm)
    exact congrArg Subtype.val h1
  have hRS : ∀ r ∈ R, ∀ s ∈ g2ShortSL2 K, r * s * r⁻¹ * s⁻¹ ∈ R ⊓ g2ShortSL2 K := by
    intro r hr s hs
    refine Subgroup.mem_inf.2 ⟨?_, hB1 r (hRC hr) s (hSC hs)⟩
    have h1 : s * r⁻¹ * s⁻¹ ∈ R := hRn s (hSC hs) r⁻¹ (R.inv_mem hr)
    have e : r * s * r⁻¹ * s⁻¹ = r * (s * r⁻¹ * s⁻¹) := by group
    rw [e]
    exact R.mul_mem hr h1
  have hRS1 : ∀ c ∈ R ⊓ g2ShortSL2 K, c = 1 := by
    have hN : ((R ⊓ g2ShortSL2 K).subgroupOf (g2ShortSL2 K)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : adjointGroup .G2 K) ∈ R ⊓ g2ShortSL2 K := Subgroup.mem_subgroupOf.1 hn
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, (g * n * g⁻¹).2⟩)
      exact hRn g (hSC g.2) n (Subgroup.mem_inf.1 hn').1
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_g2ShortSL2 hK4) hN with
      h | h
    · exfalso
      have hSR : g2ShortSL2 K ≤ R := fun s hs => by
        have hmem : (⟨s, hs⟩ : g2ShortSL2 K) ∈
            (R ⊓ g2ShortSL2 K).subgroupOf (g2ShortSL2 K) := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
      have h3S : 3 ∣ Nat.card (g2ShortSL2 K) := by
        obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
        rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
          hK]
        norm_num
      exact absurd (Nat.Coprime.eq_one_of_dvd hRc (h3S.trans (Subgroup.card_dvd_of_le hSR)))
        (by norm_num)
    · intro c hc
      refine hX c (Subgroup.mem_inf.1 hc).1 (Subgroup.mem_centralizer_iff.2 fun s hs => ?_)
      have hcZ := h (show (⟨c, (Subgroup.mem_inf.1 hc).2⟩ : g2ShortSL2 K) ∈
        (R ⊓ g2ShortSL2 K).subgroupOf (g2ShortSL2 K) from Subgroup.mem_subgroupOf.2 hc)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcZ ⟨s, hs⟩)
  refine eq_bot_iff.2 fun r hr => (Subgroup.mem_bot).2
    (hX r hr (Subgroup.mem_centralizer_iff.2 fun s hs => ?_))
  have h1 := hRS1 _ (hRS r hr s hs)
  calc s * r = (r * s * r⁻¹ * s⁻¹)⁻¹ * (r * s) := by group
    _ = r * s := by rw [h1, inv_one, one_mul]

theorem noNormalPPrime_centralizer_adjointG2_eight (hK : Nat.card K = 8)
    {s : adjointGroup .G2 K} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({s} : Set (adjointGroup .G2 K))) := by
  have hK3 : ringChar K ≠ 3 :=
    LocalTwoBalance.Cross.G2Aux.ringChar_ne_three_of_dvd_add_one K (by norm_num [hK])
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 (by norm_num [hK]) s hs3 hs1
  have hz3 : (g * s * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hs3]; group
  have hz1 : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  refine noNormalPPrime_centralizer_of_conj g s ?_
  rcases hg with h | h
  · exact noNormalPPrime_centralizer_g2Short_eight hK h hz3 hz1
  · exact noNormalPPrime_centralizer_g2Long_eight hK h hz3 hz1


theorem isLocallyBalancedAbs_three_one_adjointG2_eight (hK : Nat.card K = 8) :
    IsLocallyBalancedAbs 3 1 ↥(adjointGroup Tag.G2 K) := by
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K)
  have hK8 : Nat.card K = 2 ^ 3 := hK.trans (by norm_num)
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (f := 3) (by norm_num) K hK8
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num : 1 ≤ 3) hK8
  refine isLocallyBalancedAbs_one_of_hom_pGroup Nat.prime_three hinj Θ (fun α hα => ?_)
    (n := 1) (fun y => ?_) (fun x hx hx1 => ?_)
  · have h : α ∈ Θ.ker := hα
    rw [hΘker] at h
    exact h
  · have h := pow_card_eq_one' (x := y)
    rwa [hAut, ← pow_one 3] at h
  · by_cases hxo : x ∈ innerAut ↥(adjointGroup Tag.G2 K)
    · obtain ⟨s, rfl⟩ := hxo
      right
      have hfix : fixSub (MulAut.conj s) =
          Subgroup.centralizer ({s} : Set ↥(adjointGroup Tag.G2 K)) := by
        ext y
        rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
        constructor
        · intro h
          calc y * s = (s * y * s⁻¹) * s := by rw [h]
            _ = s * y := by group
        · intro h
          calc s * y * s⁻¹ = (y * s) * s⁻¹ := by rw [h]
            _ = y := by group
      rw [hfix]
      exact noNormalPPrime_centralizer_adjointG2_eight hK
        (hinj (by rw [map_pow, hx, map_one])) (fun h => hx1 (by rw [h, map_one]))
    · left
      exact g2EightFieldCore K hK x (orderOf_eq_prime hx hx1) hxo

theorem isLocallyBalancedAbs_three_one_G2_eight {q : TauCeti.PrimePower} (hq : IsTwoPow q 3)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hKq : Nat.card (GaloisField 2 3) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq.1 (GaloisField 2 3) hKq
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 (GaloisField 2 3)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact IsLocallyBalancedAbs.of_mulEquiv
    (eB.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
    (isLocallyBalancedAbs_three_one_adjointG2_eight hK)

end G2Eight

end CFSG.HardMathSupport.Dickson.Bal207
