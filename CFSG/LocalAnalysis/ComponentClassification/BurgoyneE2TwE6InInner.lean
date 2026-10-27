module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOrb
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6DescendedRootSL2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ClassicalInvolution
open scoped commutatorElement Pointwise

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

omit [CharP k p] [IsAlgClosed k] in
theorem mem_lift_inf_centralizer_iff
    {K : Type} [Field K] [Algebra K k] (σ : K ≃+* K)
    {H : Subgroup (ModGL TwistTag.E6.tag k)}
    (hH : H = (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K k)))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {y : ModGL TwistTag.E6.tag k} :
    y ∈ H ⊓ Subgroup.centralizer
        {baseChangeGL (algebraMap K k) (t : ModGL TwistTag.E6.tag K)} ↔
      ∃ u ∈ fixedSubgroup (MulAut.conj t),
        baseChangeGL (algebraMap K k) (u : ModGL TwistTag.E6.tag K) = y := by
  subst hH
  constructor
  · intro hy
    obtain ⟨⟨g, hgC, rfl⟩, hc⟩ := Subgroup.mem_inf.1 hy
    refine ⟨⟨g, hgC⟩, ?_, rfl⟩
    change t * ⟨g, hgC⟩ * t⁻¹ = ⟨g, hgC⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K k)
    simp only [Subgroup.coe_mul, map_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  · rintro ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨u, u.2, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : t * u = u * t := by
      rw [← mul_inv_eq_iff_eq_mul]
      exact hu
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val h1.symm)

theorem eq_one_of_odd_fix_mask_two
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [Algebra K k] [IsAlgClosure K k]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (w : ModGL .E6 k)
    (hwG : w ∈ adjointGroup .E6 k)
    (hDχ : D.χ = signMaskChar .E6 2) (hDe : D.e = f)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
    (hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K k)) ⊓
        Subgroup.centralizer {baseChangeGL (algebraMap K k) (t : ModGL TwistTag.E6.tag K)}).map
          (MulAut.conj w).toMonoidHom)
    {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hβ : Odd (orderOf β))
    (hfix : ∀ u ∈ fixedSubgroup (MulAut.conj t), β u = u) : β = 1 := by
  classical
  have hp : p.Prime := Fact.out
  set ι := algebraMap K k with hι
  set H := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) with hH
  set x := baseChangeGL ι (t : ModGL TwistTag.E6.tag K) with hx
  have hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := fun γ =>
    (hDθ γ).trans (congrArg toReal (thetaMap_e6_nil_apply γ).symm)
  set a4 : Fin (Tag.rank .E6) → ℤ := Pi.single (e6Node 3) 1 with ha4
  have ha4Δ : a4 ∈ simpleUnion D.χ := by
    rw [hDχ, simpleUnion_e6_two]
    exact Or.inl ⟨2, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : KernelComponent D.χ, a4 ∈ simpleRoots (componentRoots D.χ i) := by
    simpa [simpleUnion] using ha4Δ
  set J₅ : Set.range D.classOrbit := ⟨D.classOrbit i, i, rfl⟩ with hJ₅
  have h5mem : a4 ∈ (D.withOrbit J₅).simpleRootsJ := mem_simpleRootsJ_withOrbit_classOrbit D hi
  have hθ4 : (D.withOrbit J₅).θ (toReal a4) = toReal a4 := by
    have hθ' : ∀ γ, (D.withOrbit J₅).θ (toReal γ) =
        toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := hθ
    rw [hθ', ha4, thetaMap_e6_alpha4]
  obtain ⟨hO, hcard1, hmap⟩ := orbitMap_of_fixed (D.withOrbit J₅) h5mem hθ4
  have hφ : ∀ c : fixSubfield σ,
      ((algebraMap K k).comp (fixSubfield σ).subtype) c ∈ (D.withOrbit J₅).orbitField {a4} := by
    intro c
    rw [OrthogonalSemilinearFixedRootDatum.orbitField, mem_frobeniusFixedField]
    show (algebraMap K k (c : K)) ^ p ^ (D.e * orbitCard ({a4} : Set (Fin (Tag.rank .E6) → ℤ))) =
      algebraMap K k (c : K)
    rw [hcard1, hDe, mul_one, ← map_pow, ← hσ, (mem_fixSubfield σ).1 c.2]
  set φ := ((algebraMap K k).comp (fixSubfield σ).subtype).codRestrict _ hφ with hφdef
  set hh : ModGL .E6 k := w⁻¹ * pinnedWeyl .E6 k a4 with hhh
  set ιE : graphFixedRootGroup TwistTag.E6 K σ.toRingHom → ModGL .E6 k :=
    fun u => baseChangeGL ι (u : ModGL TwistTag.E6.tag K) with hιE
  have hconj : ∀ Z : SL2 k, CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) k) Z = Z := fun Z =>
    Subtype.ext (by simp [CFSG.RankThree.Chevalley.conjGL])
  have hkey : ∀ B : SL2 (fixSubfield σ), ∃ y ∈ H ⊓ Subgroup.centralizer {x},
      hh * simpleRootSL2 .E6 k (pinnedData .E6 a4).1
        (CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) k)
          (Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B)) *
        hh⁻¹ = y := by
    intro B
    rw [hconj]
    have hA : Matrix.SpecialLinearGroup.map ((D.withOrbit J₅).orbitField {a4}).subtype
        (Matrix.SpecialLinearGroup.map φ B) =
        Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B := by
      ext a b
      rfl
    obtain ⟨y, hy, hyeq⟩ := hCY J₅ ((D.withOrbit J₅).orbitMap_mem_orbitGroup hO
      (Matrix.SpecialLinearGroup.map φ B))
    refine ⟨y, hy, ?_⟩
    rw [hmap, hA] at hyeq
    have hroot : ∀ X : SL2 k, rootSL2 .E6 k a4 X = pinnedWeyl .E6 k a4 *
        simpleRootSL2 .E6 k (pinnedData .E6 a4).1 X * (pinnedWeyl .E6 k a4)⁻¹ := fun X => rfl
    rw [hroot] at hyeq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
    calc hh * simpleRootSL2 .E6 k (pinnedData .E6 a4).1
          (Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B) *
            hh⁻¹ =
          w⁻¹ * (pinnedWeyl .E6 k a4 * simpleRootSL2 .E6 k (pinnedData .E6 a4).1
            (Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B) *
              (pinnedWeyl .E6 k a4)⁻¹) * w := by rw [hhh]; group
      _ = w⁻¹ * (w * y * w⁻¹) * w := by rw [hyeq]
      _ = y := by group
  have hU : ∀ B : SL2 (fixSubfield σ), hh * simpleRootSL2 .E6 k (pinnedData .E6 a4).1
      (CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) k)
        (Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B)) * hh⁻¹ ∈
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K k)) := by
    intro B
    obtain ⟨y, hy, hyeq⟩ := hkey B
    rw [hyeq]
    exact (Subgroup.mem_inf.1 hy).1
  have hη : ∀ (u : twistedE6RootGroup K σ) (B : SL2 (fixSubfield σ)),
      baseChangeGL (algebraMap K k) (u : ModGL TwistTag.E6.tag K) =
        hh * simpleRootSL2 .E6 k (pinnedData .E6 a4).1
          (CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) k)
            (Matrix.SpecialLinearGroup.map ((algebraMap K k).comp (fixSubfield σ).subtype) B)) *
          hh⁻¹ → β u = u := by
    intro u B hu
    obtain ⟨y, hy, hyeq⟩ := hkey B
    rw [hyeq] at hu
    obtain ⟨u', hu', hu'eq⟩ := (mem_lift_inf_centralizer_iff σ hH t).1 hy
    have huu : u = u' := Subtype.ext (baseChangeGL_injective ι (hu.trans hu'eq.symm))
    rw [huu]
    exact hfix u' hu'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  obtain ⟨-, a, haG, -, ε, hε, hae⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_descended_root_SL2_pointwise_actors_relative_field_free
      hp hf K hK σ hσ Θ hΘ k (iterateFrobenius k p f) (fun c => iterateFrobenius_def p f c) k
      (pinnedData .E6 a4).1 1 hh hU β hη
  set a' : ModGL .E6 k := a with ha'
  set P : ModGL .E6 k := diagramMap TwistTag.E6 k with hP
  set z₀ : ModGL .E6 k := a' * P ^ ε with hz₀
  have hz₀u : ∀ u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ιE (β u) = z₀ * ιE u * z₀⁻¹ := fun u => by
    calc ιE (β u) = a' * P ^ ε * ιE u * (P ^ ε)⁻¹ * a'⁻¹ := hae u
      _ = z₀ * ιE u * z₀⁻¹ := by rw [hz₀]; group
  have hz₀c : ∀ y : ModGL .E6 k, y ∈ H ⊓ Subgroup.centralizer {x} → z₀ * y = y * z₀ := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_lift_inf_centralizer_iff σ hH t).1 hy
    have h1 := hz₀u u
    rw [hfix u hu] at h1
    calc z₀ * ιE u = (z₀ * ιE u * z₀⁻¹) * z₀ := by group
      _ = ιE u * z₀ := by rw [← h1]
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rw [show TwistTag.E6.order = 2 from rfl, sq] at h
    exact h
  have hPG : ∀ y ∈ adjointGroup .E6 k, P * y * P⁻¹ ∈ adjointGroup .E6 k := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have haG' : a' ∈ adjointGroup .E6 k := haG
  have hz2G : z₀ ^ 2 ∈ adjointGroup .E6 k := by
    obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
    · rw [hz₀, pow_zero, mul_one, sq]
      exact mul_mem haG' haG'
    · have e : z₀ ^ 2 = a' * (P * a' * P⁻¹) * (P * P) := by
        rw [hz₀, pow_one, sq]
        group
      rw [e, hP2, mul_one]
      exact mul_mem haG' (hPG a' haG')
  have hzG : w * z₀ ^ 2 * w⁻¹ ∈ adjointGroup .E6 k :=
    mul_mem (mul_mem hwG hz2G) (inv_mem hwG)
  have hzc : ∀ J' : Set.range D.classOrbit, ∀ c ∈ (D.withOrbit J').orbitGroup,
      (w * z₀ ^ 2 * w⁻¹) * c = c * (w * z₀ ^ 2 * w⁻¹) := by
    intro J' c hc
    obtain ⟨y, hy, rfl⟩ := hCY J' hc
    have h1 := hz₀c y hy
    have h2 : z₀ ^ 2 * y = y * z₀ ^ 2 := by
      rw [sq, mul_assoc, h1, ← mul_assoc, h1, mul_assoc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc w * z₀ ^ 2 * w⁻¹ * (w * y * w⁻¹) = w * (z₀ ^ 2 * y) * w⁻¹ := by group
      _ = w * (y * z₀ ^ 2) * w⁻¹ := by rw [h2]
      _ = w * y * w⁻¹ * (w * z₀ ^ 2 * w⁻¹) := by group
  have hz4 := sq_eq_one_of_commute_orbitGroups_two D (three_le_q D) hDχ hθ hzG hzc
  have hz₀4 : z₀ ^ 4 = 1 := by
    have e : (w * z₀ ^ 2 * w⁻¹) ^ 2 = w * z₀ ^ 4 * w⁻¹ := by
      rw [sq]
      group
    rw [e] at hz4
    calc z₀ ^ 4 = w⁻¹ * (w * z₀ ^ 4 * w⁻¹) * w := by group
      _ = 1 := by rw [hz4]; group
  have hpow : ∀ n : ℕ, ∀ u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ιE ((β ^ n) u) = z₀ ^ n * ιE u * (z₀ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro u
      rw [pow_zero, pow_zero, MulAut.one_apply, one_mul, inv_one, mul_one]
    | succ n ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, ih, hz₀u, pow_succ]
      group
  have hβ4 : β ^ 4 = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext (baseChangeGL_injective ι ?_)
    have h4 := hpow 4 u
    rw [hz₀4, one_mul, inv_one, mul_one] at h4
    exact h4
  have hd : orderOf β ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hβ4
  have hcop : Nat.Coprime (orderOf β) (2 ^ 2) := (Nat.coprime_two_right.2 hβ).pow_right 2
  exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd hd)

theorem burgCoreFor_conj_of_mask_two
    {f : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [Algebra K k]
    [IsAlgClosure K k] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) (h w : ModGL TwistTag.E6.tag k)
    (hwG : w ∈ adjointGroup TwistTag.E6.tag k) (hhT : h ∈ torusGroup TwistTag.E6.tag k)
    (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2) (hDe : D.e = f)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
    (hDF : ∀ y : adjointGroup TwistTag.E6.tag k, (D.F y : ModGL TwistTag.E6.tag k) =
      frobTwistGL TwistTag.E6.tag k p f (h * diagramMap TwistTag.E6 k) y)
    (hcent : (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) ⊓
          Subgroup.centralizer {baseChangeGL (algebraMap K k) (t : ModGL TwistTag.E6.tag K)}).map
          (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype) :
    BurgCoreFor (MulAut.conj t) := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hder, hdec⟩ := twE6_lift_facts (p := p) (k := k) hf hodd K hK σ hσ
  set F := frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set ι := algebraMap K k with hι
  set x := baseChangeGL ι (t : ModGL TwistTag.E6.tag K) with hx
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hxH : x ∈ ⁅R, R⁆ := by
    rw [hder]
    exact ⟨t, t.2, rfl⟩
  have hxR : x ∈ R := hRsub hxH
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow, ← Subgroup.coe_pow, ht2, Subgroup.coe_one, map_one]
  have hx1 : x ≠ 1 := fun h1 =>
    ht1 (Subtype.ext (baseChangeGL_injective ι (by rw [Subgroup.coe_one, map_one]; exact h1)))
  have hq35 : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h3 : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by omega) p)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) ⊓
        Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom := by
    intro J'
    have hle := twE6_orbitGroups_le D h w hhT hDe hDF hcent (by
      rcases hq35 with h3 | h5
      · exact Or.inl ⟨h3, hdec⟩
      · exact Or.inr ⟨h5, hDχ, hDθ⟩) J'
    rwa [hder] at hle
  refine ⟨?_, fun β hβ _ hfix => eq_one_of_odd_fix_mask_two hf K hK σ hσ t D w hwG hDχ hDe hDθ
    hCY hβ hfix⟩
  rw [pPrimeCore_eq_bot_iff]
  intro N hNn hNcop
  set φ : fixedSubgroup (MulAut.conj t) →* ModGL TwistTag.E6.tag k :=
    ((baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype).comp
      (fixedSubgroup (MulAut.conj t)).subtype with hφ
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective ι).comp (Subtype.val_injective.comp Subtype.val_injective)
  have hN'le : N.map φ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨n, -, rfl⟩
    rw [hder]
    exact (mem_lift_inf_centralizer_iff σ rfl t).2 ⟨n.1, n.2, rfl⟩
  have hN'n : ∀ y ∈ ⁅R, R⁆ ⊓ Subgroup.centralizer {x}, ∀ n ∈ N.map φ, y * n * y⁻¹ ∈ N.map φ := by
    rintro y hy _ ⟨n, hn, rfl⟩
    rw [hder] at hy
    obtain ⟨u, hu, rfl⟩ := (mem_lift_inf_centralizer_iff σ rfl t).1 hy
    refine ⟨⟨u, hu⟩ * n * ⟨u, hu⟩⁻¹, hNn.conj_mem n hn ⟨u, hu⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hN'odd : Odd (Nat.card (N.map φ)) := by
    rw [← Nat.card_congr (N.equivMapOfInjective φ hφinj).toEquiv]
    exact Nat.coprime_two_left.1 hNcop
  have hN'bot : N.map φ = ⊥ := by
    rcases hq35 with h3 | h5
    · obtain ⟨-, -, -, hcore, -⟩ := Q3.e6tw_core hp2 hf h3 hk hdec hxR hx2 hx1
      exact hcore _ hN'le hN'n hN'odd
    · exact twE6_two_oddNormal_eq_bot h5 D w hDχ hDe hDθ hcent _ hN'le hN'n hN'odd
  exact (Subgroup.map_eq_bot_iff_of_injective N hφinj).1 hN'bot

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
