module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularSA
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularBridgeLift

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE E6DiagRegular
  CFSG.LieType.Steinberg CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Bridge

section Bridge


theorem twE6B_conj_twistHom_rootDiagUnit {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (h3q : 3 ∣ q + 1) {v w' : WeylGroup TwistTag.E6.tag}
    (hw' : ∀ y, w' • y = -permLattice TwistTag.E6.perm (v⁻¹ • y))
    {a : Fin TwistTag.E6.tag.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1) (hwa : w' ∈ rootCharStabilizer a) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
      twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = rootDiagUnit TwistTag.E6.tag a := by
  rw [twistHom_rootDiagUnit_eq]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff a _ v).2 fun u => ?_).symm
  have hρ3 : ∀ z : Fin TwistTag.E6.tag.rank → ℤ,
      permLattice TwistTag.E6.perm.symm z = permLattice TwistTag.E6.perm z := fun z => by
    rw [twE6_perm_symm]
  have h1 : rootChar (fun i => Units.map Fr.toMonoidHom (a (TwistTag.E6.perm.symm i))) u =
      Units.map Fr.toMonoidHom (rootChar a (permLattice TwistTag.E6.perm u)) := by
    rw [rootChar_map_tuple Fr (fun i => a (TwistTag.E6.perm.symm i)) u, ← hρ3,
      rootChar_permLattice a TwistTag.E6.perm.symm u]
  rw [h1]
  have h2 : rootChar a (v • u) = rootChar a (-permLattice TwistTag.E6.perm u) := by
    rw [← hwa (v • u), hw' (v • u), inv_smul_smul]
  rw [h2, twE6_rootChar_neg, ← twE6_pow_eq_inv_of_dvd (twE6_rootChar_pow_three a ha3 _) h3q]
  exact Units.ext (by simp [hFr])

theorem twE6B_twistHom_conj_eq {L : Type} [Field L] (Fr : L →+* L) {v : WeylGroup TwistTag.E6.tag}
    {g0 : ModGL TwistTag.E6.tag L}
    (hg0 : twistHom TwistTag.E6 L Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
    {a : Fin TwistTag.E6.tag.rank → Lˣ}
    (hdF : canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
      twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = rootDiagUnit TwistTag.E6.tag a) :
    twistHom TwistTag.E6 L Fr (g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹) =
      g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ := by
  rw [map_mul, map_mul, map_inv, hg0]
  calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
          (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹
      = g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * g0⁻¹ := by group
    _ = g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ := by rw [hdF]

theorem twE6B_decomp {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f)) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {y : ModGL TwistTag.E6.tag K}
    (hyR : baseChangeGL (algebraMap K L) y ∈ twistedFixedGroup TwistTag.E6 L Fr) :
    ∃ (b' : Fin TwistTag.E6.tag.rank → Kˣ) (u₀ : ModGL TwistTag.E6.tag K),
      u₀ ∈ twistedE6RootGroup K σ ∧ y = rootDiagUnit TwistTag.E6.tag b' * u₀ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨-, hmul, -⟩ := CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
    hℓ hf K hK σ.toRingHom hσ L Fr hFr
  have hyR' : baseChangeGL (algebraMap K L) y ∈
      (twistedFixedGroup TwistTag.E6 L Fr : Set (ModGL TwistTag.E6.tag L)) := hyR
  rw [hmul] at hyR'
  obtain ⟨t, ht, c, hcC, htc⟩ := Set.mem_mul.1 hyR'
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hcC
  obtain ⟨htT, htR⟩ := Subgroup.mem_inf.1 ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have hbF : twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 htR).2
  have hcompat := compat_of_twistHom_rootDiagUnit (t := TwistTag.E6) hbF
  have hpp : ∀ i : Fin TwistTag.E6.tag.rank,
      TwistTag.E6.perm (TwistTag.E6.perm i) = i := fun i => by
    have := Equiv.symm_apply_apply TwistTag.E6.perm i
    rwa [twE6_perm_symm] at this
  have hbK : ∀ i, ∃ x : Kˣ, Units.map (algebraMap K L).toMonoidHom x = b i := by
    intro i
    have h1 : (b (TwistTag.E6.perm i) : L) = Fr (b i : L) := congrArg Units.val (hcompat i)
    have h2 : (b i : L) = Fr (b (TwistTag.E6.perm i) : L) := by
      have := congrArg Units.val (hcompat (TwistTag.E6.perm i))
      rw [hpp] at this
      exact this
    have h4 : Fr (Fr (b i : L)) = (b i : L) ^ Nat.card K := by
      rw [hFr, hFr, ← pow_mul, hK, sq]
    have h3 : (b i : L) ^ Nat.card K = (b i : L) := by
      rw [← h4]
      exact (h2.trans (congrArg Fr h1)).symm
    obtain ⟨x, hx⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K) h3
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact (b i).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  choose b' hb' using hbK
  have hbfun : (fun i => Units.map (algebraMap K L).toMonoidHom (b' i)) = b := funext hb'
  have hbd : baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.E6.tag b') =
      rootDiagUnit TwistTag.E6.tag b := by
    rw [baseChangeGL_rootDiagUnit, hbfun]
  refine ⟨b', u₀, hu₀, ?_⟩
  apply baseChangeGL_injective (algebraMap K L)
  rw [map_mul, hbd]
  exact htc.symm

theorem twE6B_mem_iff_sigma_fixed_lift {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (x : ModGL TwistTag.E6.tag K) :
    x ∈ twistedE6RootGroup K σ ↔ ∃ s : e6Data_valid.minGroup K,
      TwistedE6.sigma K σ.toRingHom s = s ∧
        ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = x := by
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK, sq] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, ← pow_mul]
    exact h
  have hk4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ ℓ ^ f := (hℓ.two_le).trans (Nat.le_self_pow (by omega) ℓ)
    rw [hK]
    nlinarith
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K
      hK σ hσ
  have hrange := range_e6IsogenyFixed σ.toRingHom hθθ hk4
  constructor
  · intro hx
    obtain ⟨⟨s, hsfix⟩, hs⟩ : x ∈ (e6IsogenyFixed σ.toRingHom).range := by
      rw [hrange, hder]
      exact hx
    exact ⟨s, (TwistedE6.mem_fixedGroup _).1 hsfix, hs⟩
  · rintro ⟨s, hsσ, hs⟩
    rw [← hder, ← hrange]
    exact ⟨⟨s, hsσ⟩, hs⟩

theorem twE6LiftBridge_holds : TwE6LiftBridge := by
  intro K _ _ σ q hK3 hσ hK h3q Fr hFr v w' hw' g0 hg0C hg0 a ha3 hc hwa hsh y hy
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K with hL
  set ι₀ : K →+* L := algebraMap K L with hι₀
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hKℓ : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσℓ : ∀ c, σ.toRingHom c = c ^ (ringChar K ^ f) := fun c => by rw [← hqf]; exact hσ c
  have hFrℓ : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [← hqf]; exact hFr c
  have hdaL : rootDiagUnit TwistTag.E6.tag a ∈ adjointGroup TwistTag.E6.tag L :=
    rootDiagUnit_mem_adjointGroup_of_isAlgClosed a
  have hyC : baseChangeGL ι₀ y ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hy]
    exact mul_mem (mul_mem hg0C hdaL) (inv_mem hg0C)
  have hyF : twistHom TwistTag.E6 L Fr (baseChangeGL ι₀ y) = baseChangeGL ι₀ y := by
    rw [hy]
    exact twE6B_twistHom_conj_eq Fr hg0 (twE6B_conj_twistHom_rootDiagUnit Fr hFr h3q hw' ha3 hwa)
  obtain ⟨b', u₀, hu₀, hyb⟩ := twE6B_decomp σ hpr hf1 hKℓ hσℓ Fr hFrℓ ⟨hyC, hyF⟩
  suffices hbC₀ : rootDiagUnit TwistTag.E6.tag b' ∈ twistedE6RootGroup K σ by
    rw [hyb]
    exact mul_mem hbC₀ hu₀
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    obtain ⟨m, hm⟩ := h3q
    refine ⟨m * (q - 1), ?_⟩
    have h1q : 1 ≤ q := by omega
    have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.sub_eq_of_eq_add]
      ring
    rw [e, hm]
    ring
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  have hprimK : IsPrimitiveRoot (g : K) 3 := by
    have h1 : IsPrimitiveRoot g 3 := by
      have := IsPrimitiveRoot.orderOf g
      rwa [hg] at this
    exact IsPrimitiveRoot.coe_units_iff.2 h1
  have hprim : IsPrimitiveRoot (ι₀ (g : K)) 3 := hprimK.map_of_injective ι₀.injective
  obtain ⟨uT, hu3, huc⟩ := exists_cube_params hprim ha3 hc
  obtain ⟨vT, hvc⟩ := exists_e6RootParams_eq (fun i => Units.map ι₀.toMonoidHom (b' i))
  obtain ⟨Ec, hEc⟩ := exists_finset_descent hg0C
  obtain ⟨Ev, hEv⟩ : ∃ Ev : Finset L, ∀ i, ((uT i : Lˣ) : L) ∈ Ev ∧ ((vT i : Lˣ) : L) ∈ Ev := by
    refine ⟨(Finset.univ.image fun i => ((uT i : Lˣ) : L)) ∪
      (Finset.univ.image fun i => ((vT i : Lˣ) : L)), fun i => ?_⟩
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩⟩
  obtain ⟨K₂, hK₂, hEK₂, hrange⟩ := exists_finite_subfield_of_finset (K := K) (Ec ∪ Ev)
  haveI : Finite K₂ := hK₂
  have hcK : (Ec : Set L) ⊆ K₂ := fun x hx =>
    hEK₂ (Finset.mem_coe.2 (Finset.mem_union_left _ hx))
  have hvK : ∀ x ∈ Ev, x ∈ K₂ := fun x hx =>
    hEK₂ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))
  obtain ⟨u₂, hu₂⟩ := exists_units_descent K₂ uT fun i => hvK _ (hEv i).1
  obtain ⟨v₂, hv₂⟩ := exists_units_descent K₂ vT fun i => hvK _ (hEv i).2
  obtain ⟨g₂, hg₂C, hg₂⟩ := hEc K₂ hcK
  obtain ⟨ι, hιι⟩ : ∃ ι : K →+* K₂, K₂.subtype.comp ι = ι₀ :=
    ⟨ι₀.codRestrict K₂ (fun x => hrange ⟨x, rfl⟩), RingHom.ext fun x => rfl⟩
  have hFrK₂ : ∀ x ∈ K₂, Fr x ∈ K₂ := fun x hx => by
    rw [hFr]
    exact pow_mem hx _
  obtain ⟨φ, hφ⟩ : ∃ φ : K₂ →+* K₂, φ = Fr.restrict K₂ K₂ hFrK₂ := ⟨_, rfl⟩
  have hφj : ∀ x : K₂, ((φ x : K₂) : L) = Fr x := fun x => by rw [hφ]; rfl
  have hφpow : ∀ x : K₂, φ x = x ^ q := fun x => Subtype.ext (by rw [hφj, hFr]; rfl)
  have hφcomp : K₂.subtype.comp φ = Fr.comp K₂.subtype := RingHom.ext hφj
  have hφg : twistHom TwistTag.E6 K₂ φ g₂ =
      g₂ * canonicalRep (coxeterSystem TwistTag.E6.tag) K₂ v := by
    apply baseChangeGL_injective K₂.subtype
    rw [← twistHom_baseChangeGL K₂.subtype hφcomp, map_mul, baseChangeGL_canonicalRep, hg₂]
    exact hg0
  obtain ⟨sK, hsKσ, hsKt⟩ := (twE6B_mem_iff_sigma_fixed_lift σ hpr hf1 hKℓ
    (fun c => by rw [← hqf]; exact hσ c) u₀).1 hu₀
  have hfix : ∀ x : K₂, φ (φ x) = x → x ∈ Set.range ι := by
    intro x hx
    have h1 : (x : L) ^ Nat.card K = (x : L) := by
      have h2 : ((φ (φ x) : K₂) : L) = (x : L) := congrArg Subtype.val hx
      rw [hφj, hφj, hFr, hFr, ← pow_mul, ← sq, ← hK] at h2
      exact h2
    obtain ⟨c, hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K) h1
    exact ⟨c, Subtype.ext (by rw [← hc']; exact congrArg (fun f => f c) hιι)⟩
  obtain ⟨s, hsσ, hπs⟩ := twE6B_core σ hσ h3q ι K₂.subtype ι₀ hιι φ (fun x => hφpow x) hfix hw'
    hg₂C hφg hwa hsh hu3 huc hu₂ hvc hv₂ hg₂ hy hyb hsKσ hsKt
  exact (twE6B_mem_iff_sigma_fixed_lift σ hpr hf1 hKℓ (fun c => by rw [← hqf]; exact hσ c) _).2
    ⟨s, hsσ, hπs⟩

end Bridge

end CFSG.LieType.SeitzGeneration.ExcWideThree
