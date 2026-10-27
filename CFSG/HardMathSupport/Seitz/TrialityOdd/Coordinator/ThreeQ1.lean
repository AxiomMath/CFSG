module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1Frame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1Long
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiRows
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpMain
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ShortExtract
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Handback
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.TwistedThree

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.CurtisTits CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped MatrixGroups

theorem card_SL3_eq_of_card_eq {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (h : Nat.card F₁ = Nat.card F₂) : Nat.card SL(3, F₁) = Nat.card SL(3, F₂) := by
  have := Fintype.ofFinite F₁
  have := Fintype.ofFinite F₂
  let e : F₁ ≃+* F₂ := FiniteField.ringEquivOfCardEq (by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card])
  refine Nat.card_congr ⟨Matrix.SpecialLinearGroup.map e.toRingHom,
    Matrix.SpecialLinearGroup.map e.symm.toRingHom, fun A => ?_, fun A => ?_⟩
  · apply Subtype.ext
    ext i j
    simp
  · apply Subtype.ext
    ext i j
    simp

theorem isElemAbelian_map_of_injective {G G' : Type*} [Group G] [Group G'] {p : ℕ}
    (φ : G →* G') {F : Subgroup G} (hF : CFSG.Open.IsElemAbelian p F) :
    CFSG.Open.IsElemAbelian p (F.map φ) := by
  obtain ⟨hc, hp⟩ := hF
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ea⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', eb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : G') * (b : G') = (b : G') * (a : G')
    rw [← ea, ← eb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hp y hy, map_one]

@[expose] def AnisoThreeQ1Gen : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) → (ℓ ^ f) % 3 = 1 →
    RankLE2 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      (∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup ℓ R → R ≠ ⊥ →
        ¬ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

theorem anisoThreeQ1Gen_of_closing (hClose : LongTorusClosingOdd) : AnisoThreeQ1Gen := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ hq hrank E hE hcard hanis
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  have hℓ5 : 5 ≤ ℓ := by
    have := hℓ.two_le
    have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; norm_num at hℓ
    omega
  have hq2' : 2 < ℓ ^ f :=
    lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) ℓ)
  have hq2 : 2 ≤ ℓ ^ f := hq2'.le
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ'
  have hcen := Inner.center_twistedGroup_eq_bot σ hK2 hq2 hK hσ
  obtain ⟨β, v, hvE, n, hnE, hv1, hvT, hnM, hnT, Fr, hFE⟩ :=
    d4_toral_q1_data hℓ2 hf hq K hK σ hσ E hE hcard hanis
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'ea : CFSG.IsElementaryAbelian 3 E' := CFSG.IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hcard
  have hE'3 : ∀ e ∈ E', e ^ 3 = 1 := fun e he => CFSG.elemPow_eq_one_of_isElementaryAbelian e he
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative E').is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨ω, hωσ, hω3, hω1, hvω⟩ := q1_line_data hℓ hℓ2 hf hq K hK σ hσ v n hvT hv1
    (hE'3 v hvE) (hE'3 n hnE) (hE'comm n hnE v hvE) hnM hnT
  obtain ⟨x, hxE, hxz, hperf, hRcard, hF'card⟩ :=
    exists_singular_SL3_of_frame hℓ hf K hK σ hσ hq2' hℓ3 Fr E' hcard' hE'3 hFE hvE hv1
  let φ : twistedGroup σ.toRingHom →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (twistedIncl σ.toRingHom).codRestrict _ fun z => Inner.twistedIncl_mem_root σ hK2 hq2 hK hσ z
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => twistedIncl_injective σ.toRingHom ?_, ?_⟩
    · have h' := congrArg Subtype.val h
      exact h'
    rintro ⟨g, hg⟩
    have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
      (σ := σ.toRingHom) hK2 hq2 hK hσ
    rw [← h] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact ⟨⟨a, ha⟩, rfl⟩
  let ε₀ := MulEquiv.ofBijective φ hφ
  have hωK : σ (ω : K) = ω := congrArg Units.val hωσ
  have hωF : (ω : K) ∈ fixedField σ.toRingHom := hωK
  let ωF : (fixedField σ.toRingHom)ˣ :=
    Units.mk0 ⟨(ω : K), hωF⟩ fun h => ω.ne_zero (congrArg Subtype.val h)
  have hωF' : ((ωF : fixedField σ.toRingHom) : K) = ω := rfl
  have hω3K : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hωF3 : ωF ^ 3 = 1 := by
    apply Units.ext
    apply Subtype.ext
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, hωF', Units.val_one, OneMemClass.coe_one]
    exact hω3K
  have hωF1 : ωF ≠ 1 := by
    intro h
    apply hω1
    apply Units.ext
    have := congrArg (fun u : (fixedField σ.toRingHom)ˣ => ((u : fixedField σ.toRingHom) : K)) h
    simp only [hωF', Units.val_one, OneMemClass.coe_one] at this
    exact this
  set t : Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom (ωF ^ 2) with ht
  have htω : t = ω ^ 2 := by
    apply Units.ext
    rw [ht, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    show ((((ωF : fixedField σ.toRingHom) ^ 2 : fixedField σ.toRingHom)) : K) = (ω : K) ^ 2
    rw [SubmonoidClass.coe_pow, hωF']
  have htσ : Units.map σ.toRingHom.toMonoidHom t = t := by
    apply Units.ext
    rw [htω]
    simp [hωK]
  set v' := slShort σ.toRingHom hσ3 (HSL t) with hv'
  have hv'v : ε₀ v' = v := by
    apply Subtype.ext
    show twistedIncl σ.toRingHom v' = (v : ModGL TwistTag.D4.tag K)
    rw [hv', twistedIncl_slShort_HSL hσ3, hvω, Inner.tuple_short (σ := σ) t htσ]
    have e1 : t ^ (2 : ℤ) = ω := by
      rw [htω, zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]
    have e2 : t ^ (-3 : ℤ) = 1 := by
      rw [htω, zpow_neg, zpow_ofNat, ← pow_mul]
      rw [show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow, inv_one]
    rw [e1, e2]
  have hv'sym : ε₀.symm v = v' := by rw [← hv'v, MulEquiv.symm_apply_apply]
  set x' := ε₀.symm x with hx'
  have hx'x : ε₀ x' = x := MulEquiv.apply_symm_apply ε₀ x
  have hxv' : x' * v' = v' * x' := by
    apply ε₀.injective
    rw [map_mul, map_mul, hx'x, hv'v]
    exact hE'comm x hxE v hvE
  have hx3' : x' ^ 3 = 1 := by
    apply ε₀.injective
    rw [map_pow, hx'x, map_one]
    exact hE'3 x hxE
  have hxz' : x' ∉ Subgroup.zpowers v' := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hxz
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← hx'x, ← hk, map_zpow, hv'v]
  have hCmap := Inner.centralizer_singleton_map ε₀.symm x
  have hRmap : ⁅Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom)),
      Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom))⁆ =
      (⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆).map
          ε₀.symm.toMonoidHom := by
    rw [hx', hCmap, Subgroup.map_commutator]
  have hperf' : ⁅⁅Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom)),
        Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom))⁆,
      ⁅Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom)),
        Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom))⁆⁆ =
      ⁅Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom)),
        Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom))⁆ := by
    rw [hRmap, ← Subgroup.map_commutator, hperf]
  have : Finite (RingHom.eqLocusField Fr.Fr (RingHom.id (AlgebraicClosure K))) :=
    Nat.finite_of_card_ne_zero (by rw [hF'card]; positivity)
  have hcard'' : Nat.card SL(3, fixedField σ.toRingHom) ≤
      Nat.card ↥⁅Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom)),
        Subgroup.centralizer ({x'} : Set (twistedGroup σ.toRingHom))⁆ := by
    rw [hRmap, Subgroup.card_map_of_injective ε₀.symm.injective, hRcard,
      card_SL3_eq_of_card_eq (by rw [hF'card, card_fixedField_of_cube σ.toRingHom hq2 hK hσ'])]
  have hrank' : ∀ F : Subgroup (twistedGroup σ.toRingHom), CFSG.Open.IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ 2 := fun F hF => by
    have := hrank (F.map ε₀.toMonoidHom) (isElemAbelian_map_of_injective _ hF)
    rwa [Subgroup.card_map_of_injective (f := ε₀.toMonoidHom) ε₀.injective] at this
  obtain ⟨y, hyC, hyN⟩ := exists_mem_centralizer_not_normalizer_three hσ3 hcen ωF hωF3 hωF1
    hrank' hxv' hx3' hxz' hperf' hcard''
  set E'' := E'.map ε₀.symm.toMonoidHom with hE''
  have hv'E : v' ∈ E'' := ⟨v, hvE, hv'sym⟩
  have hx'E : x' ∈ E'' := ⟨x, hxE, rfl⟩
  have hv'1 : v' ≠ 1 := fun h => hv1 (by rw [← hv'v, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => hxz (by rw [← hx'x, h, map_one]; exact Subgroup.one_mem _)
  have hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1 := by
    have htσ' : σ.toRingHom (t : K) = t := congrArg Units.val htσ
    rw [htσ', htσ', htω]
    calc ((ω ^ 2 : Kˣ) : K) * ((ω ^ 2 : Kˣ) : K) * ((ω ^ 2 : Kˣ) : K) = ((ω : K) ^ 3) ^ 2 := by
          push_cast; ring
      _ = 1 := by rw [hω3K, one_pow]
  have hLH : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ Subgroup.closure (cenGen E'') :=
    fun l hl => Subgroup.subset_closure ⟨v', hv'E, hv'1,
      Subgroup.mem_centralizer_singleton_iff.1
        (Inner.longSub_le_centralizer_slShort_HSL hσ3 t hnorm hl)⟩
  have hTH : (⨆ i, hHat σ.toRingHom i) ≤ Subgroup.closure (cenGen E'') :=
    iSup_le fun i h hh => Subgroup.subset_closure ⟨v', hv'E, hv'1,
      (hHat_commute σ.toRingHom hh (Inner.slShort_HSL_mem_hHat hσ3 t)).eq⟩
  have hyH : y ∈ Subgroup.closure (cenGen E'') :=
    Subgroup.subset_closure ⟨x', hx'E, hx'1, Subgroup.mem_centralizer_singleton_iff.1 hyC⟩
  have htop := hClose ℓ f hℓ hℓ2 hf K hK σ hσ _ hLH hTH ⟨y, hyH, hyN⟩
  have hE'gen : Subgroup.closure (cenGen E') = ⊤ := closure_cenGen_eq_top_of_map ε₀.symm E' htop
  have h := Proving.closure_centralizers_map_mulAut (β⁻¹) E
  change Subgroup.closure (cenGen E') = _ at h
  rw [hE'gen, ← Subgroup.map_top_of_surjective (β⁻¹).toMonoidHom (β⁻¹).surjective] at h
  exact (Subgroup.map_injective (β⁻¹).injective h).symm

theorem innerModelGen_three_of_q1 (h1 : AnisoThreeQ1Gen) (h2 : PhiFramePlaneGenAt (-1) 3)
    (hT : TwistedTorusPlaneGenAt 3) : InnerModelGen (· = 3) := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ p hp hp2 hpℓ hp3 E hE hcard hin hrank hno
  subst hp3
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    conj_injective_of_center_eq_bot hZ
  refine Proving.planeGen_of_closure_centralizers hinj E hin ?_
  set F := E.comap (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hFdef
  have hFea : CFSG.IsElementaryAbelian 3 F := Proving.isElementaryAbelian_comap_conj hinj hE
  have hFcard : Nat.card F = 3 ^ 2 := by rw [Proving.card_comap_conj hinj hin, hcard]
  have hanis := Proving.not_le_normalizer_of_no_invariant hin hno
  have hℓ3 : ℓ ≠ 3 := fun h => hpℓ h.symm
  have htrans : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ F.map (β⁻¹).toMonoidHom, x ≠ 1 ∧ k * x = x * k} = ⊤ →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ F, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    intro β h
    rw [Proving.closure_centralizers_map_mulAut, ← Subgroup.map_top_of_surjective
      (β⁻¹).toMonoidHom (β⁻¹).surjective] at h
    exact Subgroup.map_injective (β⁻¹).injective h
  have hmapea : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 (F.map (β⁻¹).toMonoidHom) := fun β =>
    CFSG.IsElementaryAbelian.map _
  have hmapcard : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card (F.map (β⁻¹).toMonoidHom) = 3 ^ 2 := fun β => by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective, hFcard]
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rcases (by omega : (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2) with hq | hq
  · exact h1 ℓ f hℓ hℓ2 hf K hK σ hσ hq hrank F hFea hFcard hanis
  · rcases d4Minus_plane_dichotomy hℓ hℓ2 hℓ3 hf hq K hK σ hσ F hFea hFcard with hT0 |
      ⟨β, hFr, -⟩
    · exact hT ℓ f hℓ hℓ2 hf K hK σ hσ Nat.prime_three (Ne.symm hℓ3) (by omega) F hFea hFcard hT0
    · refine htrans β (h2 ℓ f hℓ hℓ2 hf K hK σ hσ Nat.prime_three (Ne.symm hℓ3) ?_ _ (hmapea β)
        (hmapcard β) hFr)
      obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = 3 * k + 2 := ⟨ℓ ^ f / 3, by omega⟩
      rw [hk]
      exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩

theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_closing' (hClose : LongTorusClosingOdd)
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) (h63 : PhiFramePlaneGenAt (-1) 3) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback
    (innerModelGen_three_of_q1 (anisoThreeQ1Gen_of_closing hClose) h63 twistedTorusPlaneGenAt_three)
    (seitzExcAnisotropicTrialityOdd_of_closing hClose h6)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
