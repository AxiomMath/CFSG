module

public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6SixData
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6SixTorus
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Low
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Order
public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesE78

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 Polynomial
open scoped Matrix Pointwise
open CFSG.RankThree.Lattice

section Main

set_option linter.unusedSectionVars false


theorem exists_plane_twistedE6RootGroup_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) (hnd : ¬ p ∣ (ℓ ^ f) ^ 2 - 1) :
    ∃ E R : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      R ≠ ⊥ ∧ IsPGroup ℓ R ∧ ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he0 : (6 : ℕ) ≠ 0 := by norm_num
  set v : WeylGroup TwistTag.E6.tag := (coxeterSystem TwistTag.E6.tag).wordProd twE6PlaneWord
    with hvdef
  set M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    toMat TwistTag.E6.tag.rank twE6PlaneMat with hMdef
  have hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [hvdef, hMdef, wordProd_smul_eq_wordMat_mulVec, twE6Plane_wordMat, toMat_lmul,
      permLattice_E6_eq, Matrix.mulVec_mulVec]
  have hn6 : ¬ p ∣ 6 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd hp (by norm_num)
  have hchar : M.charpoly = cyclotomic 6 ℤ ^ 2 * (cyclotomic 1 ℤ * cyclotomic 2 ℤ) := by
    rw [hMdef, twE6Plane_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ (p : ℤ) ∣ (cyclotomic 1 ℤ * cyclotomic 2 ℤ).eval ((ℓ ^ f : ℕ) : ℤ) := by
    intro h
    apply hnd
    simp only [eval_mul, cyclotomic_one, eval_sub, eval_X, eval_one, cyclotomic_two,
      eval_add] at h
    have h1 : (p : ℤ) ∣ (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow]
      convert h using 1
      push_cast
      ring
    exact Int.natCast_dvd_natCast.1 h1
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨hRfin, -, hder, ⟨k, hk⟩, -, hRcard, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    have hXR : X ≤ R' := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    have hp3' : p ≠ 3 := by omega
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp Nat.prime_three hp3' hk hP
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) := by
    rw [hT0]
    exact isMulCommutative_map _ inferInstance
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hpos : 0 < (cyclotomic 6 ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' 6 (by exact_mod_cast hq2)
  have hRne : (cyclotomic 1 ℤ * cyclotomic 2 ℤ).eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h =>
    hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hchar, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero 2 hpos.ne') hRne
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hpow : M ^ 6 = 1 := twE6Plane_pow
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M he0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hpℓ : p ≠ ℓ := fun h => hpq (by rw [h]; exact dvd_pow_self ℓ (by omega))
  have htors : Nat.card (torsionSubgroup (twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) (twistHom TwistTag.E6 L Fr)) hcomm p) =
      p ^ 2 := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M (cyclotomic 1 ℤ * cyclotomic 2 ℤ) hpow hn6 hchar hpq he hR]
  have hθ : IsRoot TwistTag.E6.tag twE6PlaneTheta := mem_rootFinset.1 twE6PlaneTheta_mem
  have hvθ : v • twE6PlaneTheta = twE6PlaneTheta := by
    rw [hv, permLattice_E6_theta]
    exact twE6Plane_mulVec_theta
  obtain ⟨Y, hYadj, hYfix, hYne, hYr, hYnorm⟩ := exists_rootSingle_fixed_twistedE6 (r := ℓ) Fr hq2
    hFr v hθ permLattice_E6_theta hvθ
  set cg : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L := (MulAut.conj g0).toMonoidHom
    with hcgdef
  have hYR' : Y.map cg ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (mul_mem hg0C (hYadj hy)) (inv_mem hg0C), ?_⟩
    have hyf := hYfix y hy
    change twistHom TwistTag.E6 L Fr (g0 * y * g0⁻¹) = g0 * y * g0⁻¹
    have h1 : twistHom TwistTag.E6 L Fr (g0 * y * g0⁻¹) =
        twistHom TwistTag.E6 L Fr g0 * twistHom TwistTag.E6 L Fr y *
          (twistHom TwistTag.E6 L Fr g0)⁻¹ := by simp only [map_mul, map_inv]
    rw [h1, hg0]
    calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          twistHom TwistTag.E6 L Fr y *
          (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ =
        g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v * twistHom TwistTag.E6 L Fr y *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * g0⁻¹ := by group
      _ = g0 * y * g0⁻¹ := by rw [hyf]
  have hYrange : Y.map cg ≤ ι.range := by
    have : Finite R' := hRfin
    have hfinY : Finite (Y.map cg) :=
      Finite.of_injective (Subgroup.inclusion hYR') (Subgroup.inclusion_injective hYR')
    rw [hrange]
    by_cases hℓ3 : ℓ = 3
    ·
      have hq := CFSG.HardMathSupport.Lang.Coordinator.card_graphFixedRootGroup_E6_mul_gcd hℓ hf hK (σ := σ.toRingHom) hσ
      have hfinC : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := inferInstance
      have hC0pos : 0 < Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
        Nat.card_pos
      have hcardC' : Nat.card C' = Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
        Subgroup.card_map_of_injective (baseChangeGL_injective _) |>.trans rfl
      have hsub : Nat.card (C'.subgroupOf R') = Nat.card C' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      have hmul := Subgroup.card_mul_index (C'.subgroupOf R')
      have hRn : Nat.card R' = CFSG.SeitzReduction.E6Pilot.numTwistedE6 (ℓ ^ f) := hRcard
      rw [hsub, hcardC', hRn, ← hq] at hmul
      have hg1 : Nat.gcd 3 (ℓ ^ f + 1) = 1 := by
        subst hℓ3
        refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => ?_
        have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
        have := (Nat.dvd_add_right h3).1 h
        omega
      rw [hg1, mul_one] at hmul
      have hidx : (C'.subgroupOf R').index = 1 := by
        have := Nat.eq_of_mul_eq_mul_left hC0pos (hmul.trans (mul_one _).symm)
        exact this
      have htop : C'.subgroupOf R' = ⊤ := Subgroup.index_eq_one.1 hidx
      intro x hx
      have hxR := hYR' hx
      have : (⟨x, hxR⟩ : R') ∈ C'.subgroupOf R' := by rw [htop]; exact Subgroup.mem_top _
      exact this
    · exact le_of_isPGroup_of_index_eq_pow hYR' hℓ Nat.prime_three hℓ3 hk (hYr.map cg)
  exact exists_plane_normalizing_of_twisted_torus ι hι (twistHom TwistTag.E6 L Fr)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp
    (Int.natAbs_ne_zero.2 hev) hrat hcomm hcard htors Y hYne hYr hYrange hYnorm

theorem le_normalizer_of_map_conj_eq {G : Type*} [Group G] {E R : Subgroup G}
    (hN : ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R) :
    E ≤ Subgroup.normalizer (R : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hx' := hN x hx
  constructor
  · intro hy
    rw [← hx']
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hx'] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h := congrArg (fun t => x⁻¹ * t * x) hzy
      simpa [MulAut.conj_apply, mul_assoc] using h
    rwa [← this]

theorem excPlaneTwistedE6Six : ExcPlaneTwistedE6Six := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hn1, h6⟩ hr
  have hp3 : p ≠ 3 := CFSG.HardMathSupport.Malle.SeitzCube.ne_three_of_dvd_sq_sub_add_one hn1 h6
  have hp3' : 3 < p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by norm_num)
    · omega
  have h0 : (q.card : ZMod p) ^ 2 - q.card + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h6
    rwa [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q.card), Nat.cast_pow,
      Nat.cast_one] at this
  have hpq : ¬ p ∣ q.card := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [h'] at h0
    have : Fact p.Prime := ⟨hp⟩
    simp at h0
  have h2 : (2 : ZMod p) ≠ 0 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)))
  have h3 : (3 : ZMod p) ≠ 0 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
    ((ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h)))
  have he : orderOf ((q.card : ℕ) : ZMod p) = 6 :=
    CFSG.Walter.Ree.Cyclic.orderOf_eq_six_of_sq_sub_add_one h0 h2 h3
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hinj := conj_injective_cat_twistedE6 q hv
  obtain ⟨E, R, hE, hEc, hRne, hRp, hEN⟩ := exists_plane_twistedE6RootGroup_six q.prime_p
    q.exponent_pos K hK σ hσ hp hp3' (by rw [← hcard]; exact hpq) (by rw [← hcard]; exact he)
    (by rw [← hcard]; exact hn1)
  let f : twistedE6RootGroup K σ →* Cat ⟨.twistedE6 q, hv⟩ := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  have hE₀ : IsElemAbelian p (E.map f) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE f
  have hE₀c : Nat.card (E.map f) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hEc]
  have hN : ∀ x ∈ E.map f, (R.map f).map (MulAut.conj x).toMonoidHom = R.map f := by
    rintro _ ⟨x, hx, rfl⟩
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : x * y * x⁻¹ ∈ R := by
        rw [← hEN x hx]
        exact ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, hy', by simp [MulAut.conj_apply, f]⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : x⁻¹ * y * x ∈ R := by
        have := hEN x⁻¹ (inv_mem hx)
        rw [← this]
        exact ⟨y, hy, by simp⟩
      refine ⟨f (x⁻¹ * y * x), ⟨_, hy', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, f, mul_assoc]
  obtain ⟨A, hA, hAc, hAin, hAN⟩ := exists_plane_of_subgroup hinj hE₀ hE₀c
    (le_normalizer_of_map_conj_eq hN)
  refine ⟨A, hA, hAc, hAin, R.map f, ?_, ?_, hAN⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
  · rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
    exact hRp.map f

end Main

end CFSG.HardMathSupport.Lang.SeitzPlane
