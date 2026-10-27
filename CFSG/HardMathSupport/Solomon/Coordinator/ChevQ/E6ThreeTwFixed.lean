module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneTw
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.FieldGraphFieldPointwise
open CFSG.RankThree.Chevalley (subfieldRootGroupImage)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  (exists_primePower_fixSubfield_twisted catEquiv_graphFixedRootGroup_of_data
    fixSubfieldRestrict_eq_pow_twE6)



section Data

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def twFJ (σ η : K ≃+* K) : Subgroup ↥(twistedE6RootGroup K σ) :=
  (subfieldRootGroupImage TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η)).subgroupOf
    (twistedE6RootGroup K σ)

theorem mem_twFJ {σ η : K ≃+* K} {x : ↥(twistedE6RootGroup K σ)} :
    x ∈ twFJ σ η ↔ (x : ModGL TwistTag.E6.tag K) ∈
      subfieldRootGroupImage TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η) :=
  Subgroup.mem_subgroupOf

theorem subfieldRootGroupImage_le_twistedE6 (σ η : K ≃+* K) :
    subfieldRootGroupImage TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η) ≤
      twistedE6RootGroup K σ :=
  map_baseChangeGL_graphFixedRootGroup_le (σ := (fixSubfieldRestrict σ η).toRingHom)
    (Fr := σ.toRingHom) (ι := (fixSubfield η).subtype) (fixSubfieldRestrict σ η).surjective
    fun c => (coe_fixSubfieldRestrict σ η c).symm

private theorem baseChangeGL_orbitY_of_comm {t : TwistTag} {L M : Type} [Field L] [Field M]
    {σ : L →+* L} {Fr : M →+* M} {ι : L →+* M} (h : ∀ c, Fr (ι c) = ι (σ c))
    (a : Fin t.foldedTag.rank) (c : orbitField t L σ a) :
    baseChangeGL ι (orbitY t L σ a c : ModGL t.tag L) =
      orbitY t M Fr a ⟨ι c, map_mem_orbitField_of_comm h c.2⟩ := by
  rw [coe_orbitY, coe_orbitY, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, baseChangeGL_yUnit, ← ringHom_pow_apply_comm h]

private theorem mem_orbitField_fixSubfield (σ η : K ≃+* K) {a : Fin TwistTag.E6.foldedTag.rank}
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (hc : η (c : K) = c) :
    (⟨(c : K), (mem_fixSubfield η).2 hc⟩ : fixSubfield η) ∈
      orbitField TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom a := by
  have hσι : ∀ c : fixSubfield η, σ.toRingHom ((fixSubfield η).subtype c) =
      (fixSubfield η).subtype ((fixSubfieldRestrict σ η).toRingHom c) :=
    fun c => (coe_fixSubfieldRestrict σ η c).symm
  rw [mem_orbitField]
  apply (fixSubfield η).subtype.injective
  rw [← ringHom_pow_apply_comm hσι]
  exact mem_orbitField.1 c.2

theorem fixedOrbitX_mem_twFJ (σ η : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (hc : η (c : K) = c) :
    fixedOrbitX TwistTag.E6 K σ.toRingHom a c ∈ twFJ σ η := by
  have hσι : ∀ c : fixSubfield η, σ.toRingHom ((fixSubfield η).subtype c) =
      (fixSubfield η).subtype ((fixSubfieldRestrict σ η).toRingHom c) :=
    fun c => (coe_fixSubfieldRestrict σ η c).symm
  have hc₀ := mem_orbitField_fixSubfield σ η c hc
  have hy := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 (fixSubfieldRestrict σ η).toRingHom a ⟨_, hc₀⟩)
  exact mem_twFJ.2 ⟨_, hy, baseChangeGL_orbitX hσι a ⟨_, hc₀⟩⟩

theorem fixedOrbitY_mem_twFJ (σ η : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (hc : η (c : K) = c) :
    fixedOrbitY TwistTag.E6 K σ.toRingHom a c ∈ twFJ σ η := by
  have hσι : ∀ c : fixSubfield η, σ.toRingHom ((fixSubfield η).subtype c) =
      (fixSubfield η).subtype ((fixSubfieldRestrict σ η).toRingHom c) :=
    fun c => (coe_fixSubfieldRestrict σ η c).symm
  have hc₀ := mem_orbitField_fixSubfield σ η c hc
  have hy := graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
    (orbitY_mem_graphFixedNegUnipotent TwistTag.E6 (fixSubfieldRestrict σ η).toRingHom a ⟨_, hc₀⟩)
  exact mem_twFJ.2 ⟨_, hy, baseChangeGL_orbitY_of_comm hσι a ⟨_, hc₀⟩⟩

theorem twFJ_le_twR (σ η : K ≃+* K) : twFJ σ η ≤ twR σ η := by
  intro x hx
  obtain ⟨y, -, hy⟩ := mem_twFJ.1 hx
  rw [twR, mem_fixedSubgroup]
  refine Subtype.ext ?_
  change Units.map (entrywiseHom η.toRingHom) (x : ModGL TwistTag.E6.tag K) = x
  rw [← hy]
  have hcomp : η.toRingHom.comp (fixSubfield η).subtype = (fixSubfield η).subtype :=
    RingHom.ext fun c => (mem_fixSubfield η).1 c.2
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]

private theorem twFJ_hom_pow (τ : K ≃+* K) (k : ℕ) (x : K) :
    (τ.toRingHom ^ k) x = (τ ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, RingAut.mul_apply]
    exact ih (τ x)

private theorem twFJ_xE6_congr {i j : Fin 6} {x y : K} (hi : i.val = j.val) (hx : x = y) :
    xE6 (Pi.single i 1) x = xE6 (Pi.single j 1) y := by
  obtain rfl : i = j := Fin.ext hi
  subst hx; rfl

private theorem twFJ_xE6_congr_neg {i j : Fin 6} {x y : K} (hi : i.val = j.val) (hx : x = y) :
    xE6 (-Pi.single i 1) x = xE6 (-Pi.single j 1) y := by
  obtain rfl : i = j := Fin.ext hi
  subst hx; rfl

theorem twGens_twFJ {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (η : K ≃+* K) :
    TwGens σ η ((twFJ σ η).map (twIncl σ)) := by
  have hcard0 : (TwistTag.E6.orbit (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 2 := by
    decide
  have hcard1 : (TwistTag.E6.orbit (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 2 := by
    decide
  have hcard2 : (TwistTag.E6.orbit (⟨2, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 1 := by
    decide
  have hcard3 : (TwistTag.E6.orbit (⟨3, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 1 := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi c h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        fixedOrbitX_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitX, hcard3, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twFJ_xE6_congr (by decide) rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        fixedOrbitX_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitX, hcard2, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twFJ_xE6_congr (by decide) rfl
  · intro i hi c h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        fixedOrbitY_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitY, hcard3, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twFJ_xE6_congr_neg (by decide) rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        fixedOrbitY_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitY, hcard2, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twFJ_xE6_congr_neg (by decide) rfl
  · intro ij hij c h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard0, twFJ_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc2⟩,
        fixedOrbitX_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitX, hcard0, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twFJ_xE6_congr (by decide) rfl) (twFJ_xE6_congr (by decide) rfl)
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard1, twFJ_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ ⟨c, hc2⟩,
        fixedOrbitX_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitX, hcard1, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twFJ_xE6_congr (by decide) rfl) (twFJ_xE6_congr (by decide) rfl)
  · intro ij hij c h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard0, twFJ_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc2⟩,
        fixedOrbitY_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitY, hcard0, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twFJ_xE6_congr_neg (by decide) rfl)
        (twFJ_xE6_congr_neg (by decide) rfl)
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard1, twFJ_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ ⟨c, hc2⟩,
        fixedOrbitY_mem_twFJ σ η _ _ h2, ?_⟩
      rw [twIncl_fixedOrbitY, hcard1, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twFJ_xE6_congr_neg (by decide) rfl)
        (twFJ_xE6_congr_neg (by decide) rfl)

end Data

theorem commutator_fixedSubgroup_eq_twFJ {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp2 : p ≠ 2) {η : K ≃+* K}
    (hη : orderOf η = p) :
    ⁅fixedSubgroup (fieldActor (t := TwistTag.E6) σ η),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)⁆ = twFJ σ η := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (fixSubfield η) := Subtype.finite
  set C := twistedE6RootGroup K σ with hC
  set ι : fixSubfield η →+* K := (fixSubfield η).subtype with hιdef
  set σ₀ := fixSubfieldRestrict σ η with hσ₀def
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield η) σ₀ with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ η with hδdef
  show ⁅fixedSubgroup δ, fixedSubgroup δ⁆ = J.subgroupOf C
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hηp : η ^ p = 1 := by
    rw [← hη]
    exact pow_orderOf_eq_one η
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hη2 : ∀ c, η (η c) = c → η c = c := by
    intro c hc
    have hpow : ∀ n : ℕ, (η ^ (2 * n)) c = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, RingAut.mul_apply, pow_two,
          RingAut.mul_apply, hc, ih]
    have h1 : η ^ (2 * (k + 1)) = η := by
      rw [show 2 * (k + 1) = p + 1 by omega, pow_succ, hηp, one_mul]
    calc η c = (η ^ (2 * (k + 1))) c := by rw [h1]
      _ = c := hpow (k + 1)
  have hcomm : ∀ c, σ (η c) = η (σ c) := apply_apply_comm_of_finite σ η
  have hψ2 : ∀ c, (σ * η) ((σ * η) c) = c → η c = c := by
    intro c hc
    apply hη2
    have e : (σ * η) ((σ * η) c) = η (η c) := by
      rw [RingAut.mul_apply, RingAut.mul_apply, ← hcomm (η c), hσσ]
    rw [← e]
    exact hc
  have hσι : ∀ c : fixSubfield η, σ.toRingHom (ι c) = ι (σ₀.toRingHom c) :=
    fun c => (coe_fixSubfieldRestrict σ η c).symm
  have hψι : ∀ c : fixSubfield η, (σ * η).toRingHom (ι c) = ι (σ₀.toRingHom c) := fun c => by
    change σ (η c) = σ c
    rw [(mem_fixSubfield η).1 c.2]
  have hJC : J ≤ C := subfieldRootGroupImage_le_twistedE6 σ η
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 K (σ * η).toRingHom a,
      ∃ c₀ ∈ orbitField TwistTag.E6 (fixSubfield η) σ₀.toRingHom a, ι c₀ = c := by
    intro a c hc
    have h2 : (σ * η) ((σ * η) c) = c := by
      rw [mem_orbitField] at hc
      obtain ⟨n, hn⟩ := a
      have hn' : n < 4 := hn
      interval_cases n
      · rw [show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one] at hc
        change (σ * η) c = c at hc
        rw [hc, hc]
      · rw [show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide, pow_one] at hc
        change (σ * η) c = c at hc
        rw [hc, hc]
    have hck : c ∈ fixSubfield η := (mem_fixSubfield η).2 (hψ2 c h2)
    obtain ⟨c₀, rfl⟩ : ∃ c₀ : fixSubfield η, ι c₀ = c := ⟨⟨c, hck⟩, rfl⟩
    refine ⟨c₀, ?_, rfl⟩
    rw [mem_orbitField] at hc ⊢
    apply ι.injective
    rw [← ringHom_pow_apply_comm hψι, hc]
  have hC0J : graphFixedRootGroup TwistTag.E6 K (σ * η).toRingHom = J :=
    le_antisymm (graphFixedRootGroup_le_map_baseChangeGL (σ := σ₀.toRingHom)
        (Fr := (σ * η).toRingHom) (ι := ι) (σ * η).surjective hψι hpar)
      (map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom) (Fr := (σ * η).toRingHom)
        (ι := ι) σ₀.surjective hψι)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hKq : Nat.card K = (⟨ℓ, f, hℓ, by omega⟩ : TauCeti.PrimePower).card ^ 2 := by
    rw [TauCeti.PrimePower.card_def]
    exact hK
  have hσq : ∀ x, σ x = x ^ (⟨ℓ, f, hℓ, by omega⟩ : TauCeti.PrimePower).card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ x
  obtain ⟨q₀, -, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hKq η hp hp2' hη
  have hσ₀q := fixSubfieldRestrict_eq_pow_twE6 hqq (hp.odd_of_ne_two hp2) σ hσq η hF
  have hK₀' : Nat.card (fixSubfield η) = (q₀.p ^ q₀.exponent) ^ TwistTag.E6.order := by
    rw [hF, TauCeti.PrimePower.card_def, show TwistTag.E6.order = 2 from rfl]
  have hσ₀' : ∀ c : fixSubfield η, σ₀.toRingHom c = c ^ (q₀.p ^ q₀.exponent) := fun c => by
    rw [← TauCeti.PrimePower.card_def]
    exact hσ₀q c
  obtain ⟨hperf₀, -⟩ := finite_fixed_root_group_perfect TwistTag.E6 q₀.prime_p q₀.exponent_pos
    (fixSubfield η) hK₀' σ₀.toRingHom hσ₀'
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJdef, CFSG.RankThree.Chevalley.subfieldRootGroupImage, ← Subgroup.map_commutator,
      hperf₀]
  have hJΓ : J.subgroupOf C ≤ fixedSubgroup δ := twFJ_le_twR σ η
  have hΓψ : (fixedSubgroup δ).map C.subtype ≤
      twistedFixedGroup TwistTag.E6 K (σ * η).toRingHom := by
    rintro _ ⟨g, hg, rfl⟩
    have hδg : Units.map (entrywiseHom η.toRingHom) (g : ModGL TwistTag.E6.tag K) = g :=
      congrArg Subtype.val (mem_fixedSubgroup.1 hg)
    have hgσ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le _ _ _ g.2)
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * η).toRingHom).2 ⟨hgσ.1, ?_⟩
    rw [twistHom_apply] at hgσ ⊢
    rw [show (σ * η).toRingHom = σ.toRingHom.comp η.toRingHom from RingHom.ext fun _ => rfl,
      ← units_map_entrywiseHom_comp, Subgroup.coe_subtype, hδg]
    exact hgσ.2
  have hJsub : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
    rw [CFSG.LieType.Chevalley.commutator_subgroupOf_eq hJC, hJperf]
  refine le_antisymm (fun x hx => ?_) ((le_of_eq hJsub.symm).trans
    (Subgroup.commutator_mono hJΓ hJΓ))
  have h1 : (x : ModGL TwistTag.E6.tag K) ∈ (⁅fixedSubgroup δ, fixedSubgroup δ⁆).map C.subtype :=
    ⟨x, hx, rfl⟩
  rw [Subgroup.map_commutator] at h1
  have h2 := commutator_twistedFixedGroup_le (t := TwistTag.E6) (σ := (σ * η).toRingHom)
    (σ * η).surjective (Subgroup.commutator_mono hΓψ hΓψ h1)
  rw [hC0J] at h2
  exact Subgroup.mem_subgroupOf.2 h2

theorem nonempty_twFJ_equiv_cat {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) {η : K ≃+* K} (hη : orderOf η = p) :
    ∃ q₀ : TauCeti.PrimePower, q₀.p = ℓ ∧
      Nonempty (↥(twFJ σ η) ≃*
        Cat ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩) := by
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hKq : Nat.card K = (⟨ℓ, f, hℓ, by omega⟩ : TauCeti.PrimePower).card ^ 2 := by
    rw [TauCeti.PrimePower.card_def]
    exact hK
  have hσq : ∀ x, σ x = x ^ (⟨ℓ, f, hℓ, by omega⟩ : TauCeti.PrimePower).card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ x
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hKq η hp hp2' hη
  obtain ⟨e₂⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.E6
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q₀
    (TauCeti.LieTypeIndex.valid_twistedE6 q₀) (fixSubfield η) hF (fixSubfieldRestrict σ η)
    (fixSubfieldRestrict_eq_pow_twE6 hqq (hp.odd_of_ne_two hp2) σ hσq η hF)
  exact ⟨q₀, hq₀p, ⟨((Subgroup.subgroupOfEquivOfLe (subfieldRootGroupImage_le_twistedE6 σ η)).trans
    (Subgroup.equivMapOfInjective _ _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) _)).symm).trans e₂.symm⟩⟩

theorem exists_fieldActor_eq_of_fix_twFJ {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (η : K ≃+* K) {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβ : ∀ x ∈ twFJ σ η, β x = x) : ∃ η' : K ≃+* K, β = fieldActor σ η' := by
  classical
  set ι : fixSubfield η →+* K := (fixSubfield η).subtype with hιdef
  set σ₀ := fixSubfieldRestrict σ η with hσ₀def
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield η) σ₀ with hJdef
  have hJC : J ≤ twistedE6RootGroup K σ := subfieldRootGroupImage_le_twistedE6 σ η
  have hregι : (regularElt K : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι (regularElt (fixSubfield η) : ModGL TwistTag.E6.tag (fixSubfield η)) := by
    rw [coe_regularElt (K := K), coe_regularElt (K := fixSubfield η), map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    rw [Function.comp_apply, baseChangeGL_xUnit, map_one]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
  rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
  have hn₀J : canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ ∈ J :=
    ⟨_, canonicalRep_mem_graphFixedRootGroup (K := fixSubfield η) (σ := σ₀.toRingHom) hw₁,
      CFSG.LieType.Chevalley.baseChangeGL_canonicalRep ι w₀⟩
  have hu₀J : (regularElt K : ModGL TwistTag.E6.tag K) ∈ J :=
    ⟨_, regularElt_mem_graphFixedRootGroup (K := fixSubfield η) σ₀.toRingHom, hregι.symm⟩
  have hβ' : ∀ x : twistedE6RootGroup K σ, (x : ModGL TwistTag.E6.tag K) ∈ J → β x = x :=
    fun x hx => hβ x (mem_twFJ.2 hx)
  exact CFSG.RankThree.Chevalley.exists_fieldActor_eq_of_fix_regular_E6 hℓ hf hK σ hσ hw₀
    (n₀ := ⟨_, hJC hn₀J⟩) (u₀ := ⟨_, hJC hu₀J⟩) rfl rfl (hβ' _ hu₀J)
    (hβ' _ (mul_mem (mul_mem hn₀J hu₀J) (inv_mem hn₀J)))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
