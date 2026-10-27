module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Fac
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12OneOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D

namespace M12Cfg

section Tight

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem cent_le_ht_of_gt_one
    [CaseIAmbient T] (cfg : M12Cfg K z J zJ H S)
    (hm : ¬ sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) {a : T}
    (ha : a ∈ firstFactor K) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set T) ≤ Subgroup.normalizer (firstFactor K : Set T) := by
  have h1 : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  obtain ⟨n, hn, hnN⟩ : ∃ n ∈ sigmaNorm K, n ∉ Subgroup.normalizer (firstFactor K : Set T) := by
    by_contra hcon
    push Not at hcon
    exact hm hcon
  have hne : conjSub (1 : T) (firstFactor K) ≠ conjSub n (firstFactor K) := by
    intro h
    exact hnN (mem_normalizer_iff_conjSub_eq.mpr (h.symm.trans h1))
  have haN : a ∈ Subgroup.normalizer (conjSub n (firstFactor K) : Set T) :=
    cfg.sigmaGen_le_normalizer_conjSub_firstFactor hn (cfg.ht_le ha)
  have ha' : a ∈ conjSub (1 : T) (firstFactor K) := by rw [h1]; exact ha
  have hac : ∀ x ∈ conjSub n (firstFactor K), a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sigmaGen K) :=
    fun x hx => cfg.factor_comm (Subgroup.one_mem _) hn hne ha' hx
  have h2 : IsPGroup 2 (Subgroup.zpowers a) := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hC := m12_20_1_1 cfg hn h2 ha1 haN hac
  intro c hc
  have hcM := hC hc
  have hca : c * a * c⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc]
    group
  have hac' : a ∈ conjSub c (firstFactor K) := hca ▸ conj_mem_conjSub ha
  have heq := cfg.factor_eq_of_mem (Subgroup.one_mem _) hcM ha' hac'
    (not_mem_oddCoreOf_of_sq _ ha2 ha1)
  exact mem_normalizer_iff_conjSub_eq.mpr (heq.symm.trans h1)

theorem mem_normalizer_ht_of_conj_mem
    (cfg : M12Cfg K z J zJ H S) {y : T} (hy : y⁻¹ * z * y ∈ firstFactor K) :
    y ∈ Subgroup.normalizer (firstFactor K : Set T) := by
  have h1 : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hN : y⁻¹ * z * y ∈ Subgroup.normalizer (firstFactor K : Set T) := Subgroup.le_normalizer hy
  have hin : s26Act (firstFactor K) ⟨y⁻¹ * z * y, hN⟩ ∈
      ComponentClassification.OuterAutomorphisms.inner (SecQuot (firstFactor K)) :=
    ⟨((⟨y⁻¹ * z * y, hy⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)),
      (s26Act_eq_conj (firstFactor K) ⟨y⁻¹ * z * y, hy⟩).symm⟩
  have hyM := cfg.mem_sigmaNorm_of_inner rfl hN hin
  have hz := cfg.datum.unique
  have hb2 : (y⁻¹ * z * y) * (y⁻¹ * z * y) = 1 := by
    calc (y⁻¹ * z * y) * (y⁻¹ * z * y) = y⁻¹ * (z * z) * y := by group
      _ = 1 := by rw [hz.sq]; group
  have hb1 : y⁻¹ * z * y ≠ 1 := by
    intro h
    apply hz.ne_one
    calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hbO : y⁻¹ * z * y ∉ oddCoreOf (sigmaGen K) := not_mem_oddCoreOf_of_sq _ hb2 hb1
  have hb0 : y⁻¹ * z * y ∈ conjSub (1 : T) (firstFactor K) := by rw [h1]; exact hy
  have hby : y⁻¹ * z * y ∈ conjSub y⁻¹ (firstFactor K) := by
    have := conj_mem_conjSub (n := y⁻¹) cfg.z_mem_ht
    rwa [inv_inv] at this
  have heq := cfg.factor_eq_of_mem (Subgroup.one_mem _) ((sigmaNorm K).inv_mem hyM) hb0 hby hbO
  have hyi : y⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) :=
    mem_normalizer_iff_conjSub_eq.mpr (heq.symm.trans h1)
  simpa using (Subgroup.normalizer (firstFactor K : Set T)).inv_mem hyi

theorem tight_ht
    (cfg : M12Cfg K z J zJ H S)
    (hcent : ∀ a ∈ firstFactor K, a * a = 1 → a ≠ 1 →
      Subgroup.centralizer ({a} : Set T) ≤ Subgroup.normalizer (firstFactor K : Set T)) :
    TightlyEmbedded (firstFactor K) := by
  have hz := cfg.datum.unique
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzHt := cfg.z_mem_ht
  let Sq : SecQuot (firstFactor K) → Prop := fun w =>
    ∃ v : SecQuot (firstFactor K), orderOf v = 4 ∧ v * v = w
  obtain ⟨R₀, hR₀, k, hk, hk4, hkk⟩ := exists_orderOf_four_of_datum cfg.datum
  have hkHt : k ∈ firstFactor K := cfg.K_le_ht (hR₀.1 hk)
  have hSqz : Sq ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := by
    refine ⟨((⟨k, hkHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)),
      orderOf_mk_eq_four hkHt hk4, ?_⟩
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkk
  have key : ∀ (u : T) (hu : u ∈ firstFactor K), u * u = 1 → u ≠ 1 → ∀ (y : T)
      (hyu : y * u * y⁻¹ ∈ firstFactor K),
      Sq ((⟨u, hu⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) →
      Sq ((⟨y * u * y⁻¹, hyu⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := by
    intro u hu hu2 hu1 y hyu hSq
    have hconj : ∃ w : SecQuot (firstFactor K),
        ((⟨u, hu⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) =
          w * ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) * w⁻¹ := by
      obtain ⟨w, hw⟩ := cfg.involution_conj
        (by rw [← QuotientGroup.mk_mul]; exact congrArg _ (Subtype.ext hz.sq))
        (by rw [← QuotientGroup.mk_mul]; exact congrArg _ (Subtype.ext hu2))
        (mk_ne_one_of_mul_self hzHt hz.sq hz.ne_one) (mk_ne_one_of_mul_self hu hu2 hu1)
        (iff_of_true hSqz hSq)
      exact ⟨w, hw.symm⟩
    obtain ⟨l, hl, hlu⟩ := exists_conj_of_mk_conj hzHt hu hz.sq hu2 hconj
    have hm : ((y * l)⁻¹)⁻¹ * z * (y * l)⁻¹ ∈ firstFactor K := by
      rw [show ((y * l)⁻¹)⁻¹ * z * (y * l)⁻¹ = y * (l * z * l⁻¹) * y⁻¹ by group, hlu]
      exact hyu
    have hyl : y * l ∈ Subgroup.normalizer (firstFactor K : Set T) := by
      simpa using (Subgroup.normalizer (firstFactor K : Set T)).inv_mem
        (cfg.mem_normalizer_ht_of_conj_mem hm)
    have hk'Ht : (y * l) * k * (y * l)⁻¹ ∈ firstFactor K :=
      (Subgroup.mem_normalizer_iff.mp hyl k).mp hkHt
    have hk'4 : orderOf ((y * l) * k * (y * l)⁻¹) = 4 := by
      rw [show (y * l) * k * (y * l)⁻¹ = MulAut.conj (y * l) k by rw [MulAut.conj_apply],
        MulEquiv.orderOf_eq, hk4]
    refine ⟨((⟨(y * l) * k * (y * l)⁻¹, hk'Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)),
      orderOf_mk_eq_four hk'Ht hk'4, ?_⟩
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show (y * l) * k * (y * l)⁻¹ * ((y * l) * k * (y * l)⁻¹) = y * u * y⁻¹
    rw [← hlu, ← hkk]
    group
  refine ⟨even_iff_two_dvd.mpr (hz2 ▸ Subgroup.orderOf_dvd_natCard _ hzHt), fun g hg => ?_⟩
  by_contra hnot
  have heven : Even (Nat.card ↥(firstFactor K ⊓ rightConjugate (firstFactor K) g)) :=
    Nat.not_odd_iff_even.mp hnot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hx' : orderOf (x : T) = 2 := (Subgroup.orderOf_coe x).trans hx
  have ha2 : (x : T) * (x : T) = 1 := by rw [← pow_two]; exact hx' ▸ pow_orderOf_eq_one _
  have ha1 : (x : T) ≠ 1 := fun h => by rw [h, orderOf_one] at hx'; omega
  have haHt : (x : T) ∈ firstFactor K := (Subgroup.mem_inf.mp x.2).1
  have hbHt : g * (x : T) * g⁻¹ ∈ firstFactor K :=
    (mem_rightConjugate_iff (firstFactor K) g x).mp (Subgroup.mem_inf.mp x.2).2
  have hb2 : (g * (x : T) * g⁻¹) * (g * (x : T) * g⁻¹) = 1 := by
    calc (g * (x : T) * g⁻¹) * (g * (x : T) * g⁻¹) = g * ((x : T) * (x : T)) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hb1 : g * (x : T) * g⁻¹ ≠ 1 := fun h => ha1 (by
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this)
  have hab : g⁻¹ * (g * (x : T) * g⁻¹) * g⁻¹⁻¹ ∈ firstFactor K := by
    rw [show g⁻¹ * (g * (x : T) * g⁻¹) * g⁻¹⁻¹ = (x : T) by group]
    exact haHt
  have hiff : Sq ((⟨(x : T), haHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) ↔
      Sq ((⟨g * (x : T) * g⁻¹, hbHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := by
    constructor
    · exact key _ haHt ha2 ha1 g hbHt
    · intro h
      have h1 := key _ hbHt hb2 hb1 g⁻¹ hab h
      have e1 : (⟨g⁻¹ * (g * (x : T) * g⁻¹) * g⁻¹⁻¹, hab⟩ : ↥(firstFactor K)) = ⟨(x : T), haHt⟩ :=
        Subtype.ext (by group)
      rwa [e1] at h1
  obtain ⟨w, hw⟩ := cfg.involution_conj
    (by rw [← QuotientGroup.mk_mul]; exact congrArg _ (Subtype.ext ha2))
    (by rw [← QuotientGroup.mk_mul]; exact congrArg _ (Subtype.ext hb2))
    (mk_ne_one_of_mul_self haHt ha2 ha1) (mk_ne_one_of_mul_self hbHt hb2 hb1) hiff
  obtain ⟨h, hh, hhab⟩ := exists_conj_of_mk_conj haHt hbHt ha2 hb2 ⟨w, hw.symm⟩
  have hc : h⁻¹ * g ∈ Subgroup.centralizer ({(x : T)} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * g * (x : T) = h⁻¹ * (g * (x : T) * g⁻¹) * g := by group
      _ = h⁻¹ * (h * (x : T) * h⁻¹) * g := by rw [hhab]
      _ = (x : T) * (h⁻¹ * g) := by group
  have h1 := hcent _ haHt ha2 ha1 hc
  apply hg
  have e2 : g = h * (h⁻¹ * g) := by group
  rw [e2]
  exact (Subgroup.normalizer (firstFactor K : Set T)).mul_mem (Subgroup.le_normalizer hh) h1

end Tight

section Theorem4


variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem false_of_tight
    [CaseIAmbient T] (h4 : Asc75Theorem4) (cfg : M12Cfg K z J zJ H S)
    (hT : TightlyEmbedded (firstFactor K)) : False := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hv := cfg.viol
  have hz : IsUniqueInvolution K z := hv.hzK
  have ht : IsUniqueInvolution J zJ := hv.hzJ
  have hJA : J ∈ aStar (CoreAssembly.conjClass K) K :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨z, zJ, hv⟩⟩
  have hKΛ : K ≤ firstFactor K := cfg.K_le_ht
  have hJΛ : J ≤ firstFactor K := (le_omegaGen hJA).trans le_sup_left
  have hzΛ : z ∈ firstFactor K := hKΛ hz.mem
  have htΛ : zJ ∈ firstFactor K := hJΛ ht.mem
  have hHtop : sigmaGen K ≠ ⊤ := sigmaGen_ne_top hΩg.conjInvariant cfg.sigma_ne
  have hΛtop : firstFactor K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ cfg.ht_le))
  have hq : CFSG.IsQuasisimple (↥(firstFactor K) ⧸ classicalInvolutionOddCore ↥(firstFactor K)) := by
    obtain ⟨e⟩ := cfg.equiv
    haveI : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact CFSG.IsQuasisimple.of_mulEquiv e
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
        ⟨_, _, CFSG.Sporadic.Schreier.m12_gens_not_comm⟩).1
  have hlay : twoPrimeLayerIn (firstFactor K) = firstFactor K := twoPrimeLayerIn_eq_self hq
  have hne' : twoPrimeLayerIn (firstFactor K) ≠ oddCoreIn (firstFactor K) := by
    rw [hlay]
    intro h
    exact not_mem_oddCoreIn hz (h ▸ hzΛ)
  have hHn : ¬ (firstFactor K).Normal := fun hN => hΛtop (cfg.datum.eq_top_of_normal hN hKΛ)
  have hF : IsSimpleGroup (CFSG.generalizedFitting T) :=
    CaseIAmbient.isSimpleGroup_generalizedFitting
  rcases h4 T (firstFactor K) hT hne' with hBn | ⟨hr, -⟩ | ⟨g, hg, P, hPs, hPN, n, hn, φ, hφ, hker⟩
  · exact false_of_normalIn_twoPrimeLayerIn_top hT hHn hF hne' hBn
  · rw [hlay] at hr
    have h2 := two_le_pRank_of_commuting hz.sq ht.sq hz.ne_one ht.ne_one
      (AViol.ne_involution_gen hΩg hK hv).symm (AViol.comm_gen hΩg hv) hzΛ htΛ
    omega
  · obtain ⟨k, hkK, hkk, hk4⟩ := Q3T6D.exists_sq_eq_involution3 hΩg hK hz
    have hkΛ : k ∈ firstFactor K := hKΛ hkK
    have hkC : k ∈ oUpperTwoPrime (firstFactor K ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : firstFactor K ≤ firstFactor K ⊔ P) hkΛ, 2,
        by simpa using hk4⟩
    have hzC : z ∈ oUpperTwoPrime (firstFactor K ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : firstFactor K ≤ firstFactor K ⊔ P) hzΛ, 1,
        by simpa [pow_two] using hz.sq⟩
    set k' : ↥(oUpperTwoPrime (firstFactor K ⊔ P)) := ⟨k, hkC⟩ with hk'
    set z' : ↥(oUpperTwoPrime (firstFactor K ⊔ P)) := ⟨z, hzC⟩ with hz'
    have hkz : k' ^ 2 = z' := Subtype.ext (by rw [pow_two, Subgroup.coe_mul]; exact hkk)
    have hk'4 : k' ^ 4 = 1 := Subtype.ext (by simpa using hk4)
    have hz1 : φ z' ≠ 1 := by
      intro h
      have hzk : z' ∈ φ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at hzk
      exact not_mem_oddCoreIn hz hzk
    have h44 : (φ k') ^ 4 = 1 := by rw [← map_pow, hk'4, map_one]
    exact hz1 (by rw [← hkz, map_pow]; exact prod_sq_eq_one_of_pow_four _ h44)

theorem false_of_gt_one
    [CaseIAmbient T] (h4 : Asc75Theorem4)
    (cfg : M12Cfg K z J zJ H S)
    (hm : ¬ sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) : False :=
  cfg.false_of_tight h4
    (cfg.tight_ht fun _ ha ha2 ha1 => cfg.cent_le_ht_of_gt_one hm ha ha2 ha1)

end Theorem4

end M12Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
