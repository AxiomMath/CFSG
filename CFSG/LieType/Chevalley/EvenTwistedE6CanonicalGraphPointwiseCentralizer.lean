module

public import CFSG.LieType.Chevalley.EvenE6CanonicalGraphPointwiseCentralizer
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.AlgebraicGroups.E6RationalTwistedFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups

theorem even_twisted_E6_canonical_graph_full_pointwise_centralizer
    {f : ℕ} (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) :
    Subgroup.centralizer {η} ⊓
        Subgroup.centralizer (((((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (algebraMap k K))).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
            MulAut.conj : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ))) :
              Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ))) =
      Subgroup.zpowers η := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have hk2 : ringChar k = 2 := ringChar.eq k 2
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK'
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ σ.injective.bijective_of_finite, RingHom.ext fun _ => rfl⟩
  have hσE : ∀ c, σE c = c ^ (2 ^ f) := hσ
  obtain ⟨-, ⟨η', hη', -, hJC, hfixη, -⟩, -⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σE.toRingHom hσ
  have hηη' : η = η' := MulEquiv.ext fun g => Subtype.ext ((hη g).trans (hη' g).symm)
  subst hηη'
  let C := graphFixedRootGroup TwistTag.E6 K σE.toRingHom
  set P := diagramMap TwistTag.E6 K
  set ι₀ : k →+* K := algebraMap k K
  set J := (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι₀)
  obtain ⟨-, -, -, -, -, hΔ, hδ, hNF, -, hσP, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσE
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hP2 : P * P = 1 := diagramMap_E6_mul_self
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hP2).symm
  have hηN : ∀ n ∈ ((J.subgroupOf C).map MulAut.conj : Subgroup (MulAut C)), n * η = η * n := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 : η * MulAut.conj j * η⁻¹ = MulAut.conj j := by
      rw [mulAut_mul_conj_mul_inv, (hfixη j).2 (Subgroup.mem_subgroupOf.1 hj)]
    calc MulAut.conj j * η = η * MulAut.conj j * η⁻¹ * η := by rw [h1]
      _ = η * MulAut.conj j := by group
  refine le_antisymm (fun β hβ => ?_) (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh],
      Subgroup.mem_centralizer_iff.2 fun n hn => hηN n hn⟩))
  obtain ⟨hβη, hβN⟩ := Subgroup.mem_inf.1 hβ
  have hβη' : η * β = β * η := Subgroup.mem_centralizer_iff.1 hβη η (Set.mem_singleton η)
  have hfixJ : ∀ j : C, (j : ModGL TwistTag.E6.tag K) ∈ J → β j = j := fun j hj => by
    have hn : MulAut.conj j ∈ ((J.subgroupOf C).map MulAut.conj : Subgroup (MulAut C)) :=
      ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have h1 : MulAut.conj j * β = β * MulAut.conj j := Subgroup.mem_centralizer_iff.1 hβN _ hn
    have h2 : MulAut.conj (β j) = MulAut.conj j := by
      rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact hinj h2
  obtain ⟨g, u, δ, hβ⟩ := hNF β
  set D : ModGL TwistTag.E6.tag K :=
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u) with hD
  set x : ModGL TwistTag.E6.tag K := (g : ModGL TwistTag.E6.tag K) * D with hx
  have hβx : ∀ h : C, (β h : ModGL TwistTag.E6.tag K) =
      x * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * x⁻¹ := fun h => by
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hδ, hx, mul_inv_rev, hD]
    simp only [mul_assoc]
  clear_value x D
  have hPδ : Units.map (entrywiseHom δ.toRingHom) P = P :=
    units_map_entrywiseHom_diagramMap δ.toRingHom
  set z : ModGL TwistTag.E6.tag K := (P * x)⁻¹ * (x * P) with hz
  have hzC : ∀ w : C, z * (w : ModGL TwistTag.E6.tag K) = w * z := by
    intro w
    obtain ⟨h, rfl⟩ := (fieldActor σE δ).surjective w
    have e := congrArg (fun φ' : MulAut C => ((φ' h : C) : ModGL TwistTag.E6.tag K)) hβη'
    simp only [MulAut.mul_apply] at e
    rw [hη', hβx, hβx, hη', map_mul, map_mul, map_inv, hPδ] at e
    rw [hδ]
    set w := Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K)
    have e2 : (x * P) * w * (x * P)⁻¹ = (P * x) * w * (P * x)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]
      calc x * P * w * (P⁻¹ * x⁻¹) = x * (P * w * P⁻¹) * x⁻¹ := by group
        _ = P * (x * w * x⁻¹) * P⁻¹ := e.symm
        _ = P * x * w * (x⁻¹ * P⁻¹) := by group
    calc z * w = (P * x)⁻¹ * ((x * P) * w * (x * P)⁻¹) * (x * P) := by
          rw [hz]
          group
      _ = (P * x)⁻¹ * ((P * x) * w * (P * x)⁻¹) * (x * P) := by rw [e2]
      _ = w * z := by
          rw [hz]
          group
  clear_value z
  have hgΓ : (g : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σE.toRingHom :=
    graphFixedRootGroup_le TwistTag.E6 K σE.toRingHom g.2
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 K σE.toRingHom hgΓ
  have hDF : twistHom TwistTag.E6 K σE.toRingHom D = D := by
    rw [hD, twistHom_rootDiagUnit_eq]
    congr 1
    funext i
    rw [← compatDiag_perm, Equiv.apply_symm_apply]
  have hxF : twistHom TwistTag.E6 K σE.toRingHom x = x := by
    rw [hx, map_mul, hDF, ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hgΓ).2]
  have hPF : twistHom TwistTag.E6 K σE.toRingHom P = P := by
    rw [twistHom_apply, units_map_entrywiseHom_diagramMap, mul_inv_cancel_right]
  have hzF : twistHom TwistTag.E6 K σE.toRingHom z = z := by
    rw [hz]
    simp only [map_mul, map_inv, hxF, hPF]
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  obtain ⟨Fr, hFr⟩ := exists_frobenius_of_ringChar k L hk2
  have hFr2 : ∀ c, Fr c = c ^ (2 ^ f) := fun c => by rw [hFr, hk]
  have hιFr : ι.comp σE.toRingHom = Fr.comp ι := RingHom.ext fun c => by
    show ι (σE c) = Fr (ι c)
    rw [hσE, map_pow, hFr2]
  have hxL : baseChangeGL ι x ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hx, map_mul, hD, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup ι hgC)
      (exceptional_Lang_adjoint_diagonal_lift _ L _).1
  have hPL : baseChangeGL ι P = diagramMap TwistTag.E6 L := baseChangeGL_diagramMap ι _
  have hzL : baseChangeGL ι z ∈ adjointGroup TwistTag.E6.tag L := by
    have hconj := (diagramConjAut TwistTag.E6 L ⟨_, hxL⟩).2
    rw [coe_diagramConjAut] at hconj
    have hzk : z = x⁻¹ * (P * x * P⁻¹) := by
      rw [hz, mul_inv_rev, hPinv]
      group
    have e : baseChangeGL ι z = (baseChangeGL ι x)⁻¹ * (diagramMap TwistTag.E6 L *
        baseChangeGL ι x * (diagramMap TwistTag.E6 L)⁻¹) := by
      rw [hzk, map_mul, map_inv, map_mul, map_mul, map_inv, hPL]
    rw [e]
    exact mul_mem (inv_mem hxL) hconj
  have hzR : baseChangeGL ι z ∈ twistedFixedGroup TwistTag.E6 L Fr :=
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨hzL, by rw [twistHom_baseChangeGL ι hιFr, hzF]⟩
  have hzcent : baseChangeGL ι z ∈ Subgroup.centralizer
      ((graphFixedRootGroup TwistTag.E6 K σE.toRingHom).map (baseChangeGL ι) :
        Set (ModGL TwistTag.E6.tag L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h0, hh0, rfl⟩
    rw [← map_mul, ← map_mul, hzC ⟨h0, hh0⟩]
  obtain ⟨-, -, hbot, -⟩ := E6_rational_twisted_fixed_group_faithful_action Nat.prime_two hf K
    hK σE.toRingHom hσ L Fr hFr2
  have hz1 : z = 1 := by
    have hmem : baseChangeGL ι z ∈ (⊥ : Subgroup (ModGL TwistTag.E6.tag L)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.2 ⟨hzR, hzcent⟩
    exact baseChangeGL_injective ι ((Subgroup.mem_bot.1 hmem).trans (map_one _).symm)
  have hxP : P * x = x * P := by
    rw [hz] at hz1
    exact inv_mul_eq_one.1 hz1
  have hxσ : Units.map (entrywiseHom σE.toRingHom) x = x := by
    have h1 : P * Units.map (entrywiseHom σE.toRingHom) x * P⁻¹ = x := hxF
    calc Units.map (entrywiseHom σE.toRingHom) x
        = P⁻¹ * (P * Units.map (entrywiseHom σE.toRingHom) x * P⁻¹) * P := by group
      _ = P⁻¹ * (x * P) := by rw [h1, mul_assoc]
      _ = P⁻¹ * (P * x) := by rw [hxP]
      _ = x := by group
  have hιk : algebraMap k L = ι.comp ι₀ := IsScalarTower.algebraMap_eq k K L
  obtain ⟨x₀, hx₀, hx₀x⟩ : ∃ x₀ ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      baseChangeGL ι₀ x₀ = x := by
    have h1 : baseChangeGL ι x ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
      refine ⟨mem_twistedFixedGroup_id_iff.2 ⟨hxL, ?_⟩, ?_⟩
      · rw [← baseChangeGL_diagramMap ι, ← map_mul, hxP, map_mul]
      · change baseChangeGL Fr (baseChangeGL ι x) = baseChangeGL ι x
        rw [baseChangeGL_baseChangeGL, ← hιFr, ← baseChangeGL_baseChangeGL]
        exact congrArg (baseChangeGL ι) hxσ
    rw [e6_frobenius_fixed_eq_map hk2 Fr hFr] at h1
    obtain ⟨x₀, hx₀, hx₀x⟩ := h1
    refine ⟨x₀, hx₀, baseChangeGL_injective ι ?_⟩
    rw [baseChangeGL_baseChangeGL, ← hιk, hx₀x]
  obtain ⟨s, hs, hδs, -⟩ := exists_frobenius_pow_eq (by omega : 1 ≤ 2 * f) hK' δ
  obtain ⟨φk, hφk, hordk, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hk
  obtain ⟨δ', hδ'⟩ : ∃ δ' : k ≃+* k, ∀ c, δ' c = c ^ 2 ^ s :=
    ⟨φk ^ s, CFSG.LocalAnalysis.ComponentInitial.ringAut_pow_apply_of_sq hφk s⟩
  have hδι : ∀ c : k, δ (ι₀ c) = ι₀ (δ' c) := fun c => by rw [hδs, hδ', map_pow]
  have hδbase : ∀ j : ModGL TwistTag.E6.tag k,
      Units.map (entrywiseHom δ.toRingHom) (baseChangeGL ι₀ j) =
        baseChangeGL ι₀ (Units.map (entrywiseHom δ'.toRingHom) j) := fun j => by
    change baseChangeGL δ.toRingHom (baseChangeGL ι₀ j) =
      baseChangeGL ι₀ (baseChangeGL δ'.toRingHom j)
    have hc : δ.toRingHom.comp ι₀ = ι₀.comp δ'.toRingHom := RingHom.ext fun c => hδι c
    rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]
  have hδΓ : ∀ {j : ModGL TwistTag.E6.tag k}, j ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) →
      Units.map (entrywiseHom δ'.toRingHom) j ∈
        twistedFixedGroup TwistTag.E6 k (RingHom.id k) := fun {j} hj => by
    obtain ⟨hjC, hjP⟩ := mem_twistedFixedGroup_id_iff.1 hj
    refine mem_twistedFixedGroup_id_iff.2
      ⟨(entrywiseAdjointAut TwistTag.E6.tag δ' ⟨j, hjC⟩).2, ?_⟩
    have h1 : Units.map (entrywiseHom δ'.toRingHom) (diagramMap TwistTag.E6 k * j) =
        Units.map (entrywiseHom δ'.toRingHom) (j * diagramMap TwistTag.E6 k) := by rw [hjP]
    rwa [map_mul, map_mul, units_map_entrywiseHom_diagramMap] at h1
  have hJid : ∀ j ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      x₀ * Units.map (entrywiseHom δ'.toRingHom) j * x₀⁻¹ = j := by
    intro j hj
    have hjJ : baseChangeGL ι₀ j ∈ J := Subgroup.mem_map.2 ⟨j, hj, rfl⟩
    have h1 : baseChangeGL ι₀ j =
        x * Units.map (entrywiseHom δ.toRingHom) (baseChangeGL ι₀ j) * x⁻¹ := by
      have h := hβx ⟨_, hJC hjJ⟩
      rwa [hfixJ ⟨_, hJC hjJ⟩ hjJ] at h
    rw [hδbase, ← hx₀x, ← map_inv, ← map_mul, ← map_mul] at h1
    exact (baseChangeGL_injective ι₀ h1).symm
  set e := e6FixedF4Equiv k h2
  have hnat : ∀ jΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      (e ⟨Units.map (entrywiseHom δ'.toRingHom) jΓ, hδΓ jΓ.2⟩ : ModGL Tag.F4 k) =
        Units.map (entrywiseHom δ'.toRingHom) (e jΓ : ModGL Tag.F4 k) := fun jΓ => by
    rw [coe_e6FixedF4Equiv, coe_e6FixedF4Equiv]
    exact e6FixedToF4_baseChangeGL δ'.toRingHom jΓ
  obtain ⟨hy1, hδ'1⟩ := F4_conj_entrywise_eq_id hf hk (e ⟨x₀, hx₀⟩) δ' fun F => by
    obtain ⟨jΓ, rfl⟩ := e.surjective F
    have h3 : (⟨x₀, hx₀⟩ : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) *
        ⟨Units.map (entrywiseHom δ'.toRingHom) jΓ, hδΓ jΓ.2⟩ *
          (⟨x₀, hx₀⟩ : twistedFixedGroup TwistTag.E6 k (RingHom.id k))⁻¹ = jΓ :=
      Subtype.ext (hJid jΓ jΓ.2)
    have h4 : e ⟨x₀, hx₀⟩ * e ⟨Units.map (entrywiseHom δ'.toRingHom) jΓ, hδΓ jΓ.2⟩ *
        (e ⟨x₀, hx₀⟩)⁻¹ = e jΓ := by
      rw [← map_inv, ← map_mul, ← map_mul, h3]
    have h5 := congrArg (fun y : adjointGroup Tag.F4 k => (y : ModGL Tag.F4 k)) h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    rw [hnat] at h5
    exact h5
  have hx₀1 : x₀ = 1 := congrArg Subtype.val (e.injective (hy1.trans (map_one e).symm))
  have hfs : f ∣ s := by
    have h1 : φk ^ s = 1 := RingEquiv.ext fun c => by
      rw [CFSG.LocalAnalysis.ComponentInitial.ringAut_pow_apply_of_sq hφk, ← hδ', hδ'1]
      rfl
    rw [← hordk]
    exact orderOf_dvd_of_pow_eq_one h1
  obtain ⟨n, hn⟩ := hfs
  have hn2 : n = 0 ∨ n = 1 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · omega
    · have : f * 2 ≤ f * n := Nat.mul_le_mul_left f h
      omega
  have hx1 : x = 1 := by rw [← hx₀x, hx₀1, map_one]
  have hβδ : β = fieldActor σE δ := MulEquiv.ext fun h => Subtype.ext (by
    rw [hβx h, hx1, one_mul, inv_one, mul_one, hδ])
  rcases hn2 with rfl | rfl
  · have hδ1 : δ = (1 : RingAut K) := RingEquiv.ext fun c => by
      rw [hδs, hn, mul_zero, pow_zero, pow_one]
      rfl
    rw [hβδ, hδ1, fieldActor_one]
    exact one_mem _
  · have hδσ : δ = σE := RingEquiv.ext fun c => by rw [hδs, hn, mul_one, hσE]
    have hση : fieldActor σE σE = η := MulEquiv.ext fun h => Subtype.ext (by rw [hσP, hη'])
    rw [hβδ, hδσ, hση]
    exact Subgroup.mem_zpowers η

end CFSG.LieType.Chevalley
