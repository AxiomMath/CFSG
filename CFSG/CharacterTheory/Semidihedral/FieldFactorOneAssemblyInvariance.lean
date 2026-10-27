module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactor

public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

section Stabilizer

variable {G : Type*} [Group G]

theorem centralizer_le_C_of_mem {t : G} {V : Subgroup G} (htV : t ∈ V) :
    Subgroup.centralizer (V : Set G) ≤ C t :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htV)

theorem centralizer_conj_mem_of_mem_normalizer {V : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
  (Subgroup.mem_normalizer_iff.mp
    (StationaryConfinement.normalizer_le_normalizer_centralizer' V hg) x).mp hx

def restrictionStabilizer {t : G} (θ : C t →* ℂˣ) (V : Subgroup G) (htV : t ∈ V) :
    Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (V : Set G) ∧ ∀ c c' : C t,
    (c : G) ∈ Subgroup.centralizer (V : Set G) → (c' : G) = g * c * g⁻¹ → θ c' = θ c}
  mul_mem' := by
    rintro g h ⟨hgV, hg⟩ ⟨hhV, hh⟩
    refine ⟨Subgroup.mul_mem _ hgV hhV, fun c c' hc hc' => ?_⟩
    have hcV := centralizer_conj_mem_of_mem_normalizer hhV hc
    have e : (c' : G) = g * (h * (c : G) * h⁻¹) * g⁻¹ := by
      rw [hc']
      group
    exact (hg ⟨_, centralizer_le_C_of_mem htV hcV⟩ c' hcV e).trans
      (hh c ⟨_, centralizer_le_C_of_mem htV hcV⟩ hc rfl)
  one_mem' := by
    refine ⟨Subgroup.one_mem _, fun c c' _ hc' => ?_⟩
    have e : c' = c := Subtype.ext (by rw [hc']; group)
    rw [e]
  inv_mem' := by
    rintro g ⟨hgV, hg⟩
    refine ⟨Subgroup.inv_mem _ hgV, fun c c' hc hc' => ?_⟩
    have hc'V : (c' : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [hc']
      exact centralizer_conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hgV) hc
    have e : (c : G) = g * (c' : G) * g⁻¹ := by
      rw [hc']
      group
    exact (hg c' c hc'V e).symm

theorem mem_restrictionStabilizer {t : G} (θ : C t →* ℂˣ) (V : Subgroup G) (htV : t ∈ V)
    {g : G} :
    g ∈ restrictionStabilizer θ V htV ↔ g ∈ Subgroup.normalizer (V : Set G) ∧ ∀ c c' : C t,
      (c : G) ∈ Subgroup.centralizer (V : Set G) → (c' : G) = g * c * g⁻¹ → θ c' = θ c :=
  Iff.rfl

theorem restrictionStabilizer_le_normalizer {t : G} (θ : C t →* ℂˣ) (V : Subgroup G)
    (htV : t ∈ V) : restrictionStabilizer θ V htV ≤ Subgroup.normalizer (V : Set G) :=
  fun _ hg => hg.1

theorem inf_le_restrictionStabilizer {t : G} (θ : C t →* ℂˣ) (V : Subgroup G) (htV : t ∈ V) :
    Subgroup.normalizer (V : Set G) ⊓ C t ≤ restrictionStabilizer θ V htV := by
  rintro g ⟨hgV, hgC⟩
  refine ⟨hgV, fun c c' _ hc' => ?_⟩
  have e : c' = ⟨g, hgC⟩ * c * ⟨g, hgC⟩⁻¹ := Subtype.ext hc'
  rw [e, map_mul, map_mul, map_inv, mul_comm (θ ⟨g, hgC⟩) (θ c), mul_inv_cancel_right]

theorem relIndex_inf_C_le_three [Finite G] {t : G} {V : Subgroup G} (htV : t ∈ V)
    (ht1 : t ≠ 1) (hV : Nat.card V = 4) :
    (Subgroup.normalizer (V : Set G) ⊓ C t).relIndex (Subgroup.normalizer (V : Set G)) ≤ 3 := by
  set M := Subgroup.normalizer (V : Set G) with hM
  have hconj : ∀ g : M, (g : G) * t * (g : G)⁻¹ ∈ V := fun g =>
    (Subgroup.mem_normalizer_iff.mp g.2 t).mp htV
  have hne : ∀ g : M, (⟨(g : G) * t * (g : G)⁻¹, hconj g⟩ : V) ≠ 1 := by
    intro g h
    apply ht1
    have h' : (g : G) * t * (g : G)⁻¹ = 1 := congrArg Subtype.val h
    calc t = (g : G)⁻¹ * ((g : G) * t * (g : G)⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  let φ : M ⧸ (M ⊓ C t).subgroupOf M → {x : V // x ≠ 1} :=
    Quotient.lift (fun g : M => ⟨⟨(g : G) * t * (g : G)⁻¹, hconj g⟩, hne g⟩) (by
      intro a b hab
      have hC : ((a⁻¹ * b : M) : G) ∈ C t :=
        (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)).2
      have hC' : (a : G)⁻¹ * b * t = t * ((a : G)⁻¹ * b) :=
        Subgroup.mem_centralizer_singleton_iff.mp hC
      apply Subtype.ext
      apply Subtype.ext
      change (a : G) * t * (a : G)⁻¹ = (b : G) * t * (b : G)⁻¹
      calc (a : G) * t * (a : G)⁻¹ = (a : G) * (t * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = (a : G) * ((a : G)⁻¹ * b * t) * (b : G)⁻¹ := by rw [hC']
        _ = (b : G) * t * (b : G)⁻¹ := by group)
  have hφ : Function.Injective φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    have h : (a : G) * t * (a : G)⁻¹ = (b : G) * t * (b : G)⁻¹ :=
      congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) hxy
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(a⁻¹ * b).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change (a : G)⁻¹ * b * t = t * ((a : G)⁻¹ * b)
    calc (a : G)⁻¹ * b * t = (a : G)⁻¹ * ((b : G) * t * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * b := by rw [h]
      _ = t * ((a : G)⁻¹ * b) := by group
  have hlt := Finite.card_subtype_lt (p := fun x : V => x ≠ 1) (x := 1) (by simp)
  calc (M ⊓ C t).relIndex M = Nat.card (M ⧸ (M ⊓ C t).subgroupOf M) := rfl
    _ ≤ Nat.card {x : V // x ≠ 1} := Nat.card_le_card_of_injective φ hφ
    _ ≤ 3 := by omega

end Stabilizer

theorem invariant_of_moving_element
    (G : Type) [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (θ : C t →* ℂˣ) (η : G)
    (hη : η ∈ Subgroup.normalizer
      ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G))
    (hηt : η * t * η⁻¹ ≠ t)
    (hθη : ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = η * c * η⁻¹ → θ c' = θ c) :
    ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c := by
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨hV, htV, -, -, ht1, -⟩ :=
    StationaryConfinement.pair_facts t (fS (s n) : G) ht2 hs2 hsC (fun h => hst h.symm)
  set V := Subgroup.closure ({t, (fS (s n) : G)} : Set G) with hVdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  set P := restrictionStabilizer θ V htV with hPdef
  have hKP : M ⊓ C t ≤ P := inf_le_restrictionStabilizer θ V htV
  have hPM : P ≤ M := restrictionStabilizer_le_normalizer θ V htV
  have hηP : η ∈ P := ⟨hη, hθη⟩
  have hηK : η ∉ M ⊓ C t := fun h => hηt (by
    rw [Subgroup.mem_centralizer_singleton_iff.mp h.2, mul_inv_cancel_right])
  have h3 : (M ⊓ C t).relIndex M ≤ 3 := relIndex_inf_C_le_three htV ht1 hV.card_four
  have hmul := Subgroup.relIndex_mul_relIndex (M ⊓ C t) P M hKP hPM
  have h1 : (M ⊓ C t).relIndex P ≠ 1 := fun h => hηK (Subgroup.relIndex_eq_one.mp h hηP)
  have h0 : (M ⊓ C t).relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hPM1 : P.relIndex M = 1 := by
    have h0' : P.relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra hne
    have : 2 * 2 ≤ (M ⊓ C t).relIndex P * P.relIndex M :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  intro g hg
  exact (Subgroup.relIndex_eq_one.mp hPM1 hg).2

open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action) in
theorem invariant_of_trivial_on_layer
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (θ : C t →* ℂˣ)
    (hθY : ∀ c ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t),
      θ c = 1)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) :
    ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c := by
  classical
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  set s₀ : G := (fS (s n) : G) with hs₀
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hts : t ≠ s₀ := fun h => hst h.symm
  obtain ⟨-, htV, hsV, -, ht1, -, hVC, -, hts'⟩ :=
    StationaryConfinement.pair_facts t s₀ ht2 hs2 hsC hts
  have hcomm : Commute t s₀ := hts'
  set V := Subgroup.closure ({t, s₀} : Set G) with hVdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  set Y := ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) with hYdef
  set Ya := Y.map (C t).subtype with hYadef
  set D := C t ⊓ Subgroup.centralizer ({s₀} : Set G) with hDdef
  set R := (CFSG.pPrimeCore 2 D).map D.subtype with hRdef
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  let : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hVS : V ≤ (S : Subgroup G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact (fS (s n)).property
  obtain ⟨U, W, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hBR, -, hBn, -⟩ :=
    stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action
      G hGnonab hrec n hn S fS t s₀ ht2 hs2 hsC hts hLnonab hcentral hnc p f hp hpodd hf hq
      hmodel hcov
  have hXn : M ≤ Subgroup.normalizer ((R ⊓ Ya : Subgroup G) : Set G) := by
    rw [← hBR]
    exact hBn
  obtain ⟨W', -, -, -, -, -, -, -, -, ⟨d, hdJ, -, hd2, hds, -⟩, hCV, -⟩ :=
    StationaryConfinement.fixed_factor_ambient_data n hn S fS hG t ht2 hLnonab hcentral hnc
      p f hp hpodd hf hq.le hmodel
      (EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage t s₀ hcov)
      s₀ hsC hs2 hts
  have hdC : d ∈ C t := Subgroup.map_subtype_le _ hdJ
  have hdY : d ∈ Ya := Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_left) hdJ
  have hDeq : Subgroup.centralizer (V : Set G) = D :=
    StationaryConfinement.centralizer_closure_pair t s₀
  have hDM : D ≤ M := hDeq ▸ Subgroup.centralizer_le_normalizer _
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    rw [← hDeq]
    exact StationaryConfinement.normalizer_le_normalizer_centralizer' _
  have hRn : M ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized M D hMD
      (CFSG.pPrimeCore 2 D)
  have hRodd : Odd (Nat.card R) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hRD : R ≤ D := Subgroup.map_subtype_le _
  have hRM : R ≤ M := hRD.trans hDM
  have hRC : R ≤ C t := hRD.trans inf_le_left
  have hRs : R ≤ Subgroup.centralizer ({s₀} : Set G) := hRD.trans inf_le_right
  have hconjR : ∀ g ∈ M, ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hRn hg) x).mp hx
  have hLnormal : (CFSG.generalizedFitting (Gamma t)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hYnormal : Y.Normal := (hLnormal.comap _).comap _
  have hYn : C t ≤ Subgroup.normalizer (Ya : Set G) :=
    StationaryConfinement.le_normalizer_map_of_normal (C t) Y
  have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hdM : d ∈ M := by
    apply StationaryConfinement.mem_normalizer_closure_pair
    · rw [hdt, mul_inv_cancel_right]
    · rw [hds]
      exact Subgroup.mul_mem _ htV hsV
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hs2' : s₀ * s₀ = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hsinv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right hs2'
  set k := s₀ * d with hkdef
  have hkM : k ∈ M := M.mul_mem (Subgroup.le_normalizer hsV) hdM
  have hkC : k ∈ C t := (C t).mul_mem hsC hdC
  have hk2 : k * k = 1 := by
    have h : k * k = s₀ * (d * s₀ * d⁻¹) * d ^ 2 := by
      rw [hkdef]
      group
    rw [h, hds, hd2]
    calc s₀ * (t * s₀) * t = s₀ * (s₀ * t) * t := by rw [hcomm.eq]
      _ = (s₀ * s₀) * (t * t) := by group
      _ = 1 := by rw [hs2', ht2', one_mul]
  have hk1 : k ≠ 1 := by
    intro h
    have hd : d = s₀ := by
      rw [hkdef] at h
      rw [← hsinv]
      exact eq_inv_of_mul_eq_one_right h
    rw [hd, pow_two, hs2'] at hd2
    exact ht1 hd2.symm
  have hkord : orderOf k = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hk2) hk1
  have hkact : ∃ v ∈ V, k * v * k⁻¹ ≠ v := by
    refine ⟨s₀, hsV, fun h => ht1 ?_⟩
    have h' : k * s₀ * k⁻¹ = s₀ * t := by
      calc k * s₀ * k⁻¹ = s₀ * (d * s₀ * d⁻¹) * s₀⁻¹ := by
            rw [hkdef]
            group
        _ = s₀ * t := by
            rw [hds]
            group
    rw [h'] at h
    exact mul_left_cancel (h.trans (mul_one s₀).symm)
  have hkX : ∀ x ∈ R, x⁻¹ * (k * x * k⁻¹) ∈ R ⊓ Ya := by
    intro x hx
    have hdx : d * x * d⁻¹ ∈ R := hconjR d hdM x hx
    have hsx : s₀ * (d * x * d⁻¹) * s₀⁻¹ = d * x * d⁻¹ := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hRs hdx)).symm, mul_inv_cancel_right]
    have hkx : k * x * k⁻¹ = d * x * d⁻¹ := by
      rw [← hsx, hkdef]
      group
    rw [hkx]
    refine ⟨R.mul_mem (R.inv_mem hx) hdx, ?_⟩
    have hxY : x⁻¹ * d * x ∈ Ya := by
      have := (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.inv_mem _ (hRC hx))) d).mp hdY
      simpa only [inv_inv] using this
    have e : x⁻¹ * (d * x * d⁻¹) = (x⁻¹ * d * x) * d⁻¹ := by group
    rw [e]
    exact Ya.mul_mem hxY (Ya.inv_mem hdY)
  obtain ⟨a, haM, haodd, hka, hgen⟩ :=
    StationaryConfinement.exists_inverted_odd_cycling_element n hn S fS t s₀ ht2 hs2 hcomm hts
      R hRodd hRM hRn hCV k hkM hkord hkact
  have haX : ∀ x ∈ R, x⁻¹ * (a * x * a⁻¹) ∈ R ⊓ Ya :=
    StationaryConfinement.odd_trivial_mod_of_inverted (hRn haM) (hXn haM) (hRn hkM) hkX hka
      haodd
  have hVR : ∀ v ∈ V, ∀ x ∈ R, v * x = x * v := by
    intro v hv x hx
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [hDeq]
      exact hRD hx
    exact Subgroup.mem_centralizer_iff.mp hxV v hv
  have hCP : Subgroup.centralizer (V : Set G) ≤ restrictionStabilizer θ V htV := fun x hx =>
    inf_le_restrictionStabilizer θ V htV
      ⟨Subgroup.centralizer_le_normalizer _ hx, centralizer_le_C_of_mem htV hx⟩
  have hkP : k ∈ restrictionStabilizer θ V htV := inf_le_restrictionStabilizer θ V htV ⟨hkM, hkC⟩
  have haP : a ∈ restrictionStabilizer θ V htV := by
    refine ⟨haM, fun c c' hc hc' => ?_⟩
    rw [hCV] at hc
    obtain ⟨v, hv, x, hx, hvx⟩ := StationaryConfinement.mem_sup_of_commute hVR hc
    have hvC : v ∈ C t := hVC hv
    have hxC : x ∈ C t := hRC hx
    have hv' : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp haM v).mp hv
    obtain ⟨-, y₀, hy₀, hy₀eq⟩ := haX x hx
    have hc'eq : c' = ⟨a * v * a⁻¹, hVC hv'⟩ * ⟨x, hxC⟩ * y₀ := by
      apply Subtype.ext
      change (c' : G) = a * v * a⁻¹ * x * (y₀ : G)
      have hy : (y₀ : G) = x⁻¹ * (a * x * a⁻¹) := hy₀eq
      rw [hc', hvx, hy]
      group
    have hceq : c = ⟨v, hvC⟩ * ⟨x, hxC⟩ := Subtype.ext hvx
    rw [hc'eq, hceq, map_mul, map_mul, map_mul, hθS ⟨a * v * a⁻¹, hVC hv'⟩ (hVS hv'),
      hθS ⟨v, hvC⟩ (hVS hv), hθY y₀ hy₀, one_mul, mul_one]
  have hMP := hgen (restrictionStabilizer θ V htV) hCP hkP haP
  intro g hg
  exact (hMP hg).2

end CFSG.Semidihedral.FieldFactorOne
