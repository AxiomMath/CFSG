module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Odd
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenCyclotomicFourActors
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourNonregular

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical SteinbergBN
  CFSG.RankThree.Chevalley.EvenF4Actors CFSG.RankThree.Chevalley.EvenF4CyclotomicFourActors
  CFSG.RankThree.Chevalley.EvenF4QPlus
open scoped Pointwise commutatorElement

set_option linter.unusedSectionVars false

section Actor


variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem f4FourActor_even {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3))
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨K₄, hK₄⟩ := exists_intermediateField_finrank K Ω 4
  have : FiniteDimensional K K₄ := Module.finite_of_finrank_eq_succ hK₄
  have : Finite K₄ := Module.finite_of_finite K
  set n := canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3) with hn
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup Tag.F4 Ω ⊓ Γ with hT₀
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, hprime, -⟩ :=
    hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨-, -, -, hdich⟩ := hprime p hp hp3 hpd
  obtain ⟨hcases, -, -⟩ := hdich x hx hxp _ rfl
  obtain ⟨u, ε, hε, hu, huw⟩ := hcases.resolve_left (Set.nonempty_iff_ne_empty.1 hne)
  set h := canonicalRep (coxeterSystem Tag.F4) Ω u with hh
  set Γ₁ := Γ.map (MulAut.conj h).toMonoidHom with hΓ₁
  set D := Γ₁ ⊓ centralizer {h * x * h⁻¹} with hD
  set R := ⁅D, D⁆ with hR
  obtain ⟨-, Z₀, P, hZ₀H, hZ₀odd, ⟨a, ha, hPmem, hρP⟩, ⟨e, he⟩, hcenter, h4, h2, -, -, hcent,
      x₀, hx₀, hCx, R₀, hR₀, k, hk, hRk⟩ :=
    even_F4_cyclotomic_four_nonregular_derived_centralizer hf K hK Ω F hF hp hp3 K₄ hK₄ n g hn hg
      hgn Γ T₀ hΓ hT₀ x hx hxp u ε hε hu huw h (h * x * h⁻¹) hh rfl Γ₁ D R rfl rfl rfl
  have hinjK := baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' := hinjK.comp Subtype.val_injective
  have hquasi : CFSG.IsQuasisimple R ∧ p ∣ Nat.card R := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · have hK2 : Nat.card K = 2 := by rw [hK, show f = 1 by omega, pow_one]
      obtain ⟨hRP, ⟨e6, he6⟩, hsimp, -, hnc⟩ := h2 hK2
      have := hsimp
      refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1, ?_⟩
      have hp5 : p = 5 := by
        have h5 : p ∣ 5 := by simpa [hK2] using hpd
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
      have hRle : R ≤ P := by
        rw [hRP]
        exact Subgroup.commutator_le_self P
      have hcardR : Nat.card R = Nat.card (alternatingGroup (Fin 6)) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv]
        exact Nat.card_congr (e6.toEquiv.subtypeEquiv fun z => he6 z)
      rw [hcardR, nat_card_alternatingGroup, hp5]
      simp [Nat.card_eq_fintype_card]
      decide
    · have hK4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      obtain ⟨hRP, ⟨eP⟩, hsimp, -, hnc⟩ := h4 hK4
      have := hsimp
      refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1, ?_⟩
      have hcardR : Nat.card R = Nat.card (matrixIsometryGroup (f4J0 K)) := by
        rw [hRP, Nat.card_congr eP.toEquiv, matrixIsometryGroup_f4J0_eq_spJ]
      rw [hcardR]
      exact p_dvd_card_f4Sp hpd
  obtain ⟨hRR, hq, hc, hZ⟩ := transport_derived (ι := ι')
    (ψ := (MulAut.conj (g * h⁻¹)).toMonoidHom) hι'inj (MulAut.conj (g * h⁻¹)).injective hCx
  obtain ⟨hq₀, -⟩ := hq hquasi.1
  have hcent₀ := hc (by rw [hcent, hcenter])
  have hZodd₀ : Odd (Nat.card (Subgroup.center (centralizer ({x₀} :
      Set (adjointGroup Tag.F4 K))))) := by
    rw [hZ, ← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcenter]
    exact hZ₀odd
  have hoddC : Odd (Nat.card (centralizer ({x₀} : Set (adjointGroup Tag.F4 K)) ⊓
      centralizer ((⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
          Set (adjointGroup Tag.F4 K)) : Subgroup (adjointGroup Tag.F4 K))) := by
    rw [hcent₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hZodd₀
  have hpR : ¬ Nat.Coprime p (Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K))) := by
    have hcard : Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) =
        Nat.card R := by
      rw [← Subgroup.card_map_of_injective hι'inj, hRR,
        Subgroup.card_map_of_injective (MulAut.conj (g * h⁻¹)).injective]
    rw [hcard]
    exact fun hc' => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl hquasi.2)
  have hx₀₁ : x₀ = x₁ := Subtype.ext (hinjK (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hRg : (R₀.map ((baseChangeGL (algebraMap K K₄)).comp (adjointGroup Tag.F4 K).subtype)).map
      (MulAut.conj k).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map (algebraMap K K₄)).range.map
        (CFSG.RankThree.Classical.conjSL 1)).map (rootSL2 Tag.F4 K₄ (Pi.single 1 1)) := by
    have hid : ∀ H : Subgroup (SL2 K₄), H.map (CFSG.RankThree.Classical.conjSL 1) = H :=
      fun H => by
        ext A
        constructor
        · rintro ⟨A', hA', rfl⟩
          rwa [CFSG.RankThree.Classical.conjSL_one]
        · intro hA
          exact ⟨A, hA, CFSG.RankThree.Classical.conjSL_one A⟩
    rw [hRk, MonoidHom.range_comp, hid]
  have hcen : ∀ η : MulAut (adjointGroup Tag.F4 K), η x₀ = x₀ →
      (∀ r ∈ (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)),
          η r = r) →
      ∃ c ∈ centralizer ({x₀} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
            Set (adjointGroup Tag.F4 K)), η = MulAut.conj c := by
    intro η hηx hηR
    set DC : Subgroup (adjointGroup Tag.F4 K) := centralizer ({x₀} : Set _) with hDC
    set RC : Subgroup (adjointGroup Tag.F4 K) := ⁅DC, DC⁆ with hRC
    have hinv : ∀ u ∈ DC, u ^ 2 = 1 → η u = u := by
      intro u hu hu2
      obtain ⟨z, hz⟩ : ∃ z, z = η u * u⁻¹ := ⟨_, rfl⟩
      have hηu : η u ∈ DC := by
        rw [hDC, mem_centralizer_singleton_iff] at hu ⊢
        rw [← hηx, ← map_mul, ← map_mul, hu]
      have hzR : z ∈ DC ⊓ centralizer (RC : Set (adjointGroup Tag.F4 K)) := by
        refine Subgroup.mem_inf.2 ⟨hz ▸ mul_mem hηu (inv_mem hu),
          Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        have hconj : (MulAut.conj u⁻¹) x₀ = x₀ := by
          rw [MulAut.conj_apply, (mem_centralizer_singleton_iff.1 (inv_mem hu)),
            mul_inv_cancel_right]
        have hr' : u⁻¹ * r * u ∈ RC := by
          have := apply_mem_derivedCentralizer hconj hr
          rwa [MulAut.conj_apply, inv_inv] at this
        have h1 : η (u⁻¹ * r * u) = u⁻¹ * r * u := hηR _ hr'
        have h2 : η r = r := hηR r hr
        rw [map_mul, map_mul, map_inv] at h1
        have h3 : z * r * z⁻¹ = r := by
          calc z * r * z⁻¹ = η u * (u⁻¹ * r * u) * (η u)⁻¹ := by rw [hz]; group
            _ = η u * ((η u)⁻¹ * η r * η u) * (η u)⁻¹ := by rw [h1]
            _ = r := by rw [h2]; group
        exact (mul_inv_eq_iff_eq_mul.1 h3).symm
      have hzZ := hcent₀ ▸ hzR
      obtain ⟨zD, hzD, hzz⟩ := hzZ
      have hzu : z * u = u * z := by
        have := Subgroup.mem_center_iff.1 hzD ⟨u, hu⟩
        rw [← hzz]
        exact (congrArg Subtype.val this).symm
      have hz2 : z ^ 2 = 1 := by
        have h1 : η u = z * u := by rw [hz, inv_mul_cancel_right]
        calc z ^ 2 = z ^ 2 * u ^ 2 := by rw [hu2, mul_one]
          _ = (z * u) ^ 2 := (Commute.mul_pow hzu 2).symm
          _ = η (u ^ 2) := by rw [map_pow, h1]
          _ = 1 := by rw [hu2, map_one]
      have hz2' : (⟨z, hzR⟩ : (DC ⊓ centralizer (RC : Set (adjointGroup Tag.F4 K)) :
          Subgroup (adjointGroup Tag.F4 K))) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
      have hcop : Nat.Coprime (orderOf (⟨z, hzR⟩ : (DC ⊓ centralizer
          (RC : Set (adjointGroup Tag.F4 K)) : Subgroup (adjointGroup Tag.F4 K))))
          (Nat.card (DC ⊓ centralizer (RC : Set (adjointGroup Tag.F4 K)) :
            Subgroup (adjointGroup Tag.F4 K))) :=
        (Nat.coprime_two_left.2 hoddC).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hz2')
      have hord := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_natCard _)
      have hz1 : z = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 hord)
      rw [hz] at hz1
      exact mul_inv_eq_one.1 hz1
    have hfixR₀ : ∀ r ∈ R₀, η r = r := fun r hr =>
      le_of_forall_sq_eq_one_mem_of_descended R₀ K₄ (algebraMap K K₄) 1 hRg
        (X := MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id _))
        (fun u hu hu2 => hinv u (hR₀ hu) hu2) hr
    obtain ⟨c, hc⟩ : ∃ c : adjointGroup Tag.F4 K, MulAut.conj c = η :=
      (even_F4_descended_root_SL2_pointwise_automorphisms_inner hf K hK K₄
        (algebraMap K K₄) R₀ hk (isRoot_single _ 1) 1 hRg).1 η hfixR₀
    refine ⟨c, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hc.symm⟩
    · have h1 := hηx
      rw [← hc, MulAut.conj_apply] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    · have h1 := hηR r hr
      rw [← hc, MulAut.conj_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  refine ⟨hq₀, hpR, hcen, fun y hy => ?_⟩
  obtain ⟨hyC, hyR⟩ := hy
  have h1 : ι' y ∈ (centralizer ({x₀} : Set (adjointGroup Tag.F4 K))).map ι' := ⟨y, hyC, rfl⟩
  rw [hCx] at h1
  obtain ⟨d, hdD, hdy⟩ := h1
  have hdR : d ∈ centralizer (R : Set (ModGL Tag.F4 Ω)) := by
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : (MulAut.conj (g * h⁻¹)).toMonoidHom r ∈
        (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ :
            Subgroup (adjointGroup Tag.F4 K)).map ι' := by
      rw [hRR]
      exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'R, hr'e⟩ := hr'
    have hc := mem_centralizer_iff.1 hyR r' hr'R
    have hdy' : (MulAut.conj (g * h⁻¹)) d = ι' y := hdy
    have hr'e' : ι' r' = (MulAut.conj (g * h⁻¹)) r := hr'e
    apply (MulAut.conj (g * h⁻¹)).injective
    rw [map_mul (MulAut.conj (g * h⁻¹)) r d, map_mul (MulAut.conj (g * h⁻¹)) d r, hdy', ← hr'e',
      ← map_mul ι', ← map_mul ι', hc]
  have hdDR : d ∈ D ⊓ centralizer (R : Set (ModGL Tag.F4 Ω)) := ⟨hdD, hdR⟩
  have hdZ : d ∈ Z₀ := hcent ▸ hdDR
  have hkey : g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g =
      h⁻¹ * d * h⁻¹⁻¹ := by
    change g⁻¹ * ι' y * g = _
    rw [← hdy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hdH : d ∈ torusGroup Tag.F4 Ω := by
    obtain ⟨z, hz, rfl⟩ := hZ₀H hdZ
    have hle : torusGroup Tag.F4 K₄ ≤
        (torusGroup Tag.F4 Ω).comap (baseChangeGL (algebraMap K₄ Ω)) := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    exact hle hz
  have hhN : h ∈ Subgroup.normalizer (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) :=
    hh ▸ canonicalRep_mem_normalizer u
  have hzH : h⁻¹ * d * h⁻¹⁻¹ ∈ torusGroup Tag.F4 Ω :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hhN) d).1 hdH
  have hcommP : ∀ w ∈ P, d * w = w * d := by
    intro w hw
    have key : e (⟨d, hdZ⟩, 1) * e (1, ⟨w, hw⟩) = e (1, ⟨w, hw⟩) * e (⟨d, hdZ⟩, 1) := by
      rw [← map_mul, ← map_mul]
      congr 1
    have := congrArg Subtype.val key
    simpa [Subgroup.coe_mul, he] using this
  have ha' : baseChangeGL (algebraMap K₄ Ω) a ∈ subsystemGroup Tag.F4 Ω {1, 2} :=
    baseChangeGL_mem_subsystemGroup (algebraMap K₄ Ω) ha
  have hχ : d ∈ torusGroup Tag.F4 Ω ∧ torusRootChar d (Pi.single 1 1) = 1 ∧
      torusRootChar d (Pi.single 2 1) = 1 := by
    refine (mem_centralizer_conj_subsystemGroup_iff (algebraMap K Ω) ha'
      (Subgroup.mem_sup_left hdH)).1 ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
    have hmem : (MulAut.conj (baseChangeGL (algebraMap K₄ Ω) a)).toMonoidHom
        (baseChangeGL (algebraMap K Ω) y') ∈ P :=
      (hPmem _).2 ⟨y', hy', by simp [MulAut.conj_apply]⟩
    exact (hcommP _ hmem).symm
  obtain ⟨-, h1', h2'⟩ := hχ
  refine ⟨by rw [hkey]; exact hzH, fun α hα => ?_⟩
  rw [hkey]
  have hJ : ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) = {1, 2} := rfl
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdH
  have hb1 : b 1 = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 1), rootChar_pi_single] at h1'
    exact Units.val_eq_one.1 h1'
  have hb2 : b 2 = 1 := by
    rw [hb, torusRootChar_rootDiagUnit b (isRoot_single Tag.F4 2), rootChar_pi_single] at h2'
    exact Units.val_eq_one.1 h2'
  obtain ⟨a', ha''⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
  have hconj : rootDiagUnit Tag.F4 b = canonicalRep (coxeterSystem Tag.F4) Ω u *
      rootDiagUnit Tag.F4 a' * (canonicalRep (coxeterSystem Tag.F4) Ω u)⁻¹ := by
    rw [← hb, ← ha'', ← hh]
    group
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff b a' u).1 hconj
  have huα : u • α ∈ parabolicRoots Tag.F4 ({1, 2} : Set (Fin Tag.F4.rank)) := by
    rw [← hJ, ← hu]
    exact ⟨α, hα, rfl⟩
  change torusRootChar (h⁻¹ * d * h⁻¹⁻¹) α = 1
  rw [ha'', torusRootChar_rootDiagUnit a' hα.1, ← hchar,
    rootChar_eq_one_of_mem_parabolicRoots hb1 hb2 huα, Units.val_one]

end Actor

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
