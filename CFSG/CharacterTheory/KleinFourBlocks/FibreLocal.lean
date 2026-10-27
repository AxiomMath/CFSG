module

public import CFSG.CharacterTheory.KleinFourBlocks.FibreLabels
public import CFSG.CharacterTheory.KleinFourBlocks.LocalFour
public import CFSG.CharacterTheory.KleinFourBlocks.LocalLabelBlock
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed CFSG.Wreathed.BlockOrbits CFSG.BlockBasics
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourFiber
  CFSG.Semidihedral.Principal.FreeSix

open scoped Classical

namespace CFSG.KleinFourBlocks

section KOrbitPair

variable {G : Type*} [Group G] {V : Subgroup G} {f₀ : G → ℂ}

theorem kOrbit_subset_pair (hdata : FreeBlockData V f₀) {f₁ : G → ℂ} (hf₁ : f₁ ∈ fOrbit V f₀)
    {t y : G} (hK : ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ y⁻¹ * x ∈ dV V) :
    kOrbit V t f₁ ⊆ {f₁, fun g => f₁ (y⁻¹ * g * y)} := by
  rintro f ⟨k, hk, hfk⟩
  rcases hK k hk with hD | hD
  · left
    funext g
    rw [hfk g]
    exact hdata.cls_orbit hf₁ k hD g
  · right
    funext g
    rw [hfk g]
    show f₁ (k⁻¹ * g * k) = f₁ (y⁻¹ * g * y)
    have e : k⁻¹ * g * k = (y⁻¹ * k)⁻¹ * (y⁻¹ * g * y) * (y⁻¹ * k) := by group
    rw [e]
    exact hdata.cls_orbit hf₁ _ hD _

omit [Group G] in
theorem pair_subset_kOrbit {G : Type*} [Group G] {V : Subgroup G} {f₁ : G → ℂ} {t y : G}
    (hyC : y ∈ cT t) (hyM : y ∈ mV V) :
    f₁ ∈ kOrbit V t f₁ ∧ (fun g => f₁ (y⁻¹ * g * y)) ∈ kOrbit V t f₁ :=
  ⟨⟨1, (cT t ⊓ mV V).one_mem, fun g => by simp⟩, ⟨y, ⟨hyC, hyM⟩, fun g => rfl⟩⟩

theorem fun_ne_of_orbit_card_two {f₁ f₂ : G → ℂ} {t : G}
    (hsub : kOrbit V t f₁ ⊆ {f₁, f₂}) (horbit : (kOrbit V t f₁).ncard = 2) : f₁ ≠ f₂ := by
  intro h
  subst h
  have h1 : kOrbit V t f₁ ⊆ {f₁} := by simpa using hsub
  have := Set.ncard_le_ncard h1 (Set.finite_singleton _)
  rw [Set.ncard_singleton] at this
  omega

end KOrbitPair

theorem block_four_characters_gen {G : Type} [Group G] [Fintype G] {V : Subgroup G}
    {t y : G} (sC : cT t) (htV : t ∈ V) (hsV : (sC : G) ∈ V)
    (hs2 : orderOf sC = 2) (ht2 : orderOf t = 2)
    (hst : sC ≠ ⟨t, element_mem_centralizer_zpowers t⟩) (hVC : V ≤ cT t)
    (hcl : Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, sC} : Set (cT t)) =
      V.subgroupOf (cT t))
    (hDmem : ∀ x : G, t * x = x * t → (sC : G) * x = x * (sC : G) → x ∈ dV V)
    {R : Subgroup G} (hRD : R ≤ dV V) (hVR : V ⊓ R = ⊥)
    (hDVR : ∀ x ∈ dV V, ∃ v ∈ V, ∃ r ∈ R, x = v * r)
    (hyC : y ∈ cT t) (hyM : y ∈ mV V) (hys : y * (sC : G) * y⁻¹ = t * (sC : G))
    (hK : ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ y⁻¹ * x ∈ dV V)
    {f₀ : G → ℂ} (hdata : FreeBlockData V f₀)
    (basisD : FiniteIrreducibleCharacterBasis (dV V)) {n₀ : basisD.index}
    (hn₀ : AffordsFun basisD (fun x => (x : G)) f₀ n₀)
    (w : ℕ) (hw : 0 < w) (hf₀1 : f₀ 1 = w) (hwdeg : 2 ^ (Nat.card R).factorization 2 ∣ w)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisC : FiniteIrreducibleCharacterBasis (cT t)) (label : basisC.index)
    (hD : coefficientBlockDefect basisC ideal 2 label (V.subgroupOf (cT t)))
    {f₁ : G → ℂ} (hf₁ : f₁ ∈ fOrbit V f₀) (horbit : (kOrbit V t f₁).ncard = 2)
    (hs : IsPGroup 2 (Subgroup.zpowers sC))
    (hcent : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)) =
      dInC V t)
    (basisCs : FiniteIrreducibleCharacterBasis (Subgroup.centralizer
      ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t))))
    (hfib : brauerFiberBlocks basisC ideal 2 sC hs basisCs label =
      (Finset.univ.filter fun n => ∃ f ∈ kOrbit V t f₁,
        AffordsFun basisCs (fun x => ((x : cT t) : G)) f n).image
        (coefficientBlock basisCs (localizedComplexIntegerRing ideal))) :
    ∃ (θ : Fin 4 → basisC.index) (f : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) label = Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = f) ∧
      ((basisC.representation (θ 0)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 1)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 2)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ) ∧
        (basisC.representation (θ 3)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ)) ∧
      ((basisC.representation (θ 0)).character sC = 2 * (w : ℂ) ∧
        (basisC.representation (θ 1)).character sC = -(2 * (w : ℂ)) ∧
        (basisC.representation (θ 2)).character sC = 0 ∧
        (basisC.representation (θ 3)).character sC = 0) ∧
      (∀ x, x ∉ involutionLocalSection t →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (involutionLocalSection t) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := by
  classical
  set tC : cT t := ⟨t, element_mem_centralizer_zpowers t⟩ with htC
  set yC : cT t := ⟨y, hyC⟩ with hyCdef
  have hDC : dV V ≤ cT t := dV_le_cT htV
  have hRC : R ≤ cT t := hRD.trans hDC
  set R' : Subgroup (cT t) := R.subgroupOf (cT t) with hR'
  have hVmem : ∀ v : cT t, v ∈ Subgroup.closure ({tC, sC} : Set (cT t)) ↔ (v : G) ∈ V := by
    intro v
    rw [hcl, Subgroup.mem_subgroupOf]
  set f₂ : G → ℂ := fun g => f₁ (y⁻¹ * g * y) with hf₂def
  have hf₂Ω : f₂ ∈ fOrbit V f₀ := fOrbit_smul_mem hf₁ hyM
  obtain ⟨hf₁k, hf₂k⟩ := pair_subset_kOrbit (V := V) (f₁ := f₁) hyC hyM
  have hsub : kOrbit V t f₁ ⊆ {f₁, f₂} := kOrbit_subset_pair hdata hf₁ hK
  have hne : f₁ ≠ f₂ := fun_ne_of_orbit_card_two hsub horbit
  let φs : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)) ≃*
      dV V :=
    (MulEquiv.subgroupCongr hcent).trans (KleinFourFiber.centralizerSubgroupOfEquiv hVC hDC)
  have hφs : ∀ x, (φs x : G) = ((x : cT t) : G) := fun x => rfl
  obtain ⟨m₀, hm₀⟩ := exists_affords basisD hn₀ basisCs (fun x => ((x : cT t) : G)) φs hφs hf₁
  obtain ⟨m₁, hm₁⟩ := exists_affords basisD hn₀ basisCs (fun x => ((x : cT t) : G)) φs hφs hf₂Ω
  have hnaff : ∀ n : basisCs.index, n = m₀ ∨ n = m₁ →
      ∃ f ∈ fOrbit V f₀, AffordsFun basisCs (fun x => ((x : cT t) : G)) f n := by
    rintro n (rfl | rfl)
    · exact ⟨f₁, hf₁, hm₀⟩
    · exact ⟨f₂, hf₂Ω, hm₁⟩
  have htcent : ∀ g : cT t, g * tC = tC * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 t (Subgroup.mem_zpowers t)).symm
  have ht' : orderOf tC = 2 := by rw [htC, Subgroup.orderOf_mk]; exact ht2
  have hs' : orderOf sC = 2 := hs2
  have hst' : sC ≠ tC := hst
  have hRD' : R' ≤ Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hxR : ((x : cT t) : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
    have hc : sC * x = x * sC :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hRD hxR) (sC : G) hsV)
    exact (Commute.zpow_left hc k).eq
  have hDVR' : ∀ x ∈ Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) :
      Set (cT t)), ∃ v ∈ Subgroup.closure ({tC, sC} : Set (cT t)), ∃ r ∈ R', x = v * r := by
    intro x hx
    have hxD : ((x : cT t) : G) ∈ dV V := by
      apply hDmem
      · exact Subgroup.mem_centralizer_iff.mp (x : cT t).2 t (Subgroup.mem_zpowers t)
      · exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx sC
          (Subgroup.mem_zpowers sC))
    obtain ⟨v, hv, r, hr, hxvr⟩ := hDVR _ hxD
    exact ⟨⟨v, hVC hv⟩, (hVmem _).mpr hv, ⟨r, hRC hr⟩, Subgroup.mem_subgroupOf.mpr hr,
      Subtype.ext hxvr⟩
  have hVR' : Subgroup.closure ({tC, sC} : Set (cT t)) ⊓ R' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : G) ∈ V ⊓ R :=
      Subgroup.mem_inf.mpr ⟨(hVmem x).mp h1, Subgroup.mem_subgroupOf.mp h2⟩
    rw [hVR, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hyV : yC ∈ Subgroup.normalizer
      ((Subgroup.closure ({tC, sC} : Set (cT t)) : Subgroup (cT t)) : Set (cT t)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hVmem, hVmem]
    exact Subgroup.mem_normalizer_iff.mp hyM (h : G)
  have hys' : yC * sC * yC⁻¹ = tC * sC := Subtype.ext hys
  have hwdeg' : 2 ^ (Nat.card R').factorization 2 ∣ w := by
    have hcard : Nat.card R' = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
    rw [hcard]
    exact hwdeg
  have hN1gen : ∀ {f : G → ℂ}, f ∈ fOrbit V f₀ → ∀ {n : basisCs.index},
      AffordsFun basisCs (fun x => ((x : cT t) : G)) f n →
      ∀ (x x' : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)))
        (v : cT t), v ∈ Subgroup.closure ({tC, sC} : Set (cT t)) →
        (x : cT t) = v * (x' : cT t) → (x' : cT t) ∈ R' →
        (basisCs.representation n).character x = (basisCs.representation n).character x' := by
    intro f hf n hn x x' v hv hx _
    have hvV : (v : G) ∈ V := (hVmem v).mp hv
    have hxG : ((x : cT t) : G) = (v : G) * ((x' : cT t) : G) := by rw [hx]; rfl
    rw [hn x, hn x']
    show f ((x : cT t) : G) = f ((x' : cT t) : G)
    rw [hxG]
    exact hdata.transV_orbit hf (v : G) hvV _
  have hf1gen : ∀ {f : G → ℂ}, f ∈ fOrbit V f₀ → f 1 = (w : ℂ) := by
    rintro f ⟨m, hm, hfm⟩
    rw [hfm]
    simpa using hf₀1
  have hN2gen : ∀ {f : G → ℂ}, f ∈ fOrbit V f₀ → ∀ {n : basisCs.index},
      AffordsFun basisCs (fun x => ((x : cT t) : G)) f n →
      (basisCs.representation n).character 1 = (w : ℂ) := by
    intro f hf n hn
    rw [hn 1]
    exact hf1gen hf
  have hG1b : ∀ {f : G → ℂ}, f ∈ fOrbit V f₀ → ∀ {n : basisCs.index},
      AffordsFun basisCs (fun x => ((x : cT t) : G)) f n →
      (∀ x : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)),
        (x : cT t) ∈ R' → 2 ∣ orderOf (x : cT t) →
          (basisCs.representation n).character x = 0) ∧
      (∀ lam : ↥(Subgroup.closure ({tC, sC} : Set (cT t))) →* ℂˣ,
        ∃ ψ ∈ coefficientBlock basisCs (localizedComplexIntegerRing ideal) n,
          ∀ (x x' : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) :
              Set (cT t))) (v : ↥(Subgroup.closure ({tC, sC} : Set (cT t)))),
            (x : cT t) = (v : cT t) * (x' : cT t) → (x' : cT t) ∈ R' →
              (basisCs.representation ψ).character x =
                (basisCs.representation n).character x' * (lam v : ℂ)) ∧
      (∀ g : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) : Set (cT t)) → ℂ,
        g ∈ coefficientCharacterSpace basisCs
            (coefficientBlock basisCs (localizedComplexIntegerRing ideal) n) ↔
          ∃ F : ↥(Subgroup.closure ({tC, sC} : Set (cT t))) → ℂ,
            ∀ (x x' : Subgroup.centralizer ((Subgroup.zpowers sC : Subgroup (cT t)) :
                Set (cT t))) (v : ↥(Subgroup.closure ({tC, sC} : Set (cT t)))),
              (x : cT t) = (v : cT t) * (x' : cT t) → (x' : cT t) ∈ R' →
                g x = (basisCs.representation n).character x' * F v) := fun {f} hf {n} hn =>
    local_label_block_description tC sC htcent ht' hs' hst' basisCs R' hRD' hDVR' hVR'
      ideal n (hN1gen hf hn) ⟨w, by rw [hN2gen hf hn], hwdeg'⟩
  have hfilter : (Finset.univ.filter fun n => ∃ f ∈ kOrbit V t f₁,
      AffordsFun basisCs (fun x => ((x : cT t) : G)) f n) = {m₀, m₁} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨f, hf, hn⟩
      have hf' := hsub hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf'
      rcases hf' with rfl | rfl
      · exact Or.inl (eq_of_affordsFun basisCs _ _ hn hm₀)
      · exact Or.inr (eq_of_affordsFun basisCs _ _ hn hm₁)
    · rintro (rfl | rfl)
      · exact ⟨f₁, hf₁k, hm₀⟩
      · exact ⟨f₂, hf₂k, hm₁⟩
  have hfiber : brauerFiberBlocks basisC ideal 2 sC hs basisCs label =
      {coefficientBlock basisCs (localizedComplexIntegerRing ideal) m₀,
        coefficientBlock basisCs (localizedComplexIntegerRing ideal) m₁} := by
    rw [hfib, hfilter, Finset.image_insert, Finset.image_singleton]
  have hD' : coefficientBlockDefect basisC ideal 2 label
      (Subgroup.closure ({tC, sC} : Set (cT t))) := by
    rw [hcl]
    exact hD
  obtain ⟨θ, f, hθinj, hθb, hf, hdeg, ht0, ht1', ht2', ht3, hs0, hs1', hs2', hs3, -, -, hsupp,
      -, -, hspan, -, -⟩ :=
    central_involution_defect_zero_local_blocks_four_characters_and_section_line basisC ideal
      tC sC htcent ht' hs' hst' hs basisCs R' hRD' hDVR' hVR' yC hyV hys' w hw m₀ m₁
      (fun n hn => by
        obtain ⟨f, hf, hnf⟩ := hnaff n hn
        exact hN1gen hf hnf)
      (fun n hn => by
        obtain ⟨f, hf, hnf⟩ := hnaff n hn
        exact hN2gen hf hnf)
      (fun n hn => by
        obtain ⟨f, hf, hnf⟩ := hnaff n hn
        exact (hG1b hf hnf).1)
      (fun x x' hx' => by
        rw [hm₁ x, hm₀ x']
        show f₁ (y⁻¹ * ((x : cT t) : G) * y) = f₁ ((x' : cT t) : G)
        have h2 : ((x' : cT t) : G) = y⁻¹ * ((x : cT t) : G) * y := by rw [hx']; rfl
        rw [h2])
      (fun h => hne (by
        funext g
        by_cases hg : g ∈ dV V
        · obtain ⟨x, hx⟩ := φs.surjective ⟨g, hg⟩
          have hxg : ((x : cT t) : G) = g := congrArg Subtype.val hx
          have h0 := hm₀ x
          have h1 := hm₁ x
          rw [h] at h0
          have h3 := h0.symm.trans h1
          simp only [hxg] at h3
          exact h3
        · rw [hdata.supp_orbit hf₁ g hg, hdata.supp_orbit hf₂Ω g hg]))
      (fun n hn => by
        obtain ⟨f, hf, hnf⟩ := hnaff n hn
        exact (hG1b hf hnf).2.1)
      (fun n hn => by
        obtain ⟨f, hf, hnf⟩ := hnaff n hn
        exact (hG1b hf hnf).2.2)
      label hD' hfiber
  exact ⟨θ, f, hθinj, hθb, hf, hdeg, ⟨ht0, ht1', ht2', ht3⟩, ⟨hs0, hs1', hs2', hs3⟩, hsupp, hspan⟩

end CFSG.KleinFourBlocks
