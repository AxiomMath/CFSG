module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoInvert
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTorality

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

set_option linter.unusedSectionVars false

section B3


private theorem ringAut_eq_one_or_eq_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) (δ : K ≃+* K) : δ = 1 ∨ δ = σ := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨σ', hσ', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two le_rfl K hK'
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]; norm_num
  rw [hσσ'] at hord
  have hσ1 : σ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; exact absurd hord (by decide)
  have hσ2 : σ ^ 2 = 1 := by rw [← pow_orderOf_eq_one σ, hord]; rfl
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK2
  have hδ2 : δ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := δ)
    rwa [hcard] at this
  exact eq_one_or_eq_of_sq_eq_one Nat.prime_two hK2 hσ1 hσ2 hδ2

private theorem mem_inner_of_coprime_of_exponent_three {A : Type*} [Group A] {N H : Subgroup A}
    [N.Normal] (h3 : ∀ a : ↥H ⧸ N.subgroupOf H, a ^ 3 = 1) {α : A} (hαH : α ∈ H)
    (hα3 : Nat.Coprime 3 (orderOf α)) : α ∈ N := by
  set a : ↥H ⧸ N.subgroupOf H := QuotientGroup.mk ⟨α, hαH⟩ with ha
  have ha3 := h3 a
  have haord : a ^ orderOf α = 1 := by
    have h1 : (⟨α, hαH⟩ : ↥H) ^ orderOf α = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [ha, ← QuotientGroup.mk_pow, h1]
    rfl
  have ha1 : a = 1 := by
    have h := pow_gcd_eq_one.2 ⟨ha3, haord⟩
    rwa [Nat.Coprime.gcd_eq_one hα3, pow_one] at h
  have h2 := (QuotientGroup.eq_one_iff _).1 ha1
  exact Subgroup.mem_subgroupOf.1 h2

theorem false_of_fixes_inner_torus_fieldAut
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3)
    {u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hcd : ∀ g : twistedE6RootGroup K σ,
      ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹)
    (hfield : ∀ (δ : K ≃+* K) (g : twistedE6RootGroup K σ),
      ((fieldActor σ δ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g)
    {g : twistedE6RootGroup K σ} {α : MulAut (twistedE6RootGroup K σ)}
    (hα : α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ)
    {t : twistedE6RootGroup K σ} {y : Fin 5 → ZMod 3}
    (ht : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) =
      g0 * dV (τ := TwistTag.E6.tag) ω (subLin (τ := TwistTag.E6.tag) e6InnerVec y) * g0⁻¹)
    (hfix : ∀ z ∈ Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)), α z = z) :
    False := by
  classical
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hFin : Finite ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :=
    Finite.of_equiv _ e.toEquiv
  have hcoe := coe_twE6TwoEquiv hK σ hσ hg0C hg0
  set ι := algebraMap K (AlgebraicClosure K) with hι
  set b := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hb
  have hαz : ∀ z : twistedE6RootGroup K σ,
      ((α z : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        ((g : ModGL TwistTag.E6.tag K) * b) *
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL TwistTag.E6.tag K) *
            ((g : ModGL TwistTag.E6.tag K) * b)⁻¹ := by
    intro z
    rw [hα]
    change ((MulAut.conj g (compatDiagAutHom TwistTag.E6 K σ.toRingHom u
      (fieldActor σ σ z)) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = _
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcd, hfield]
    group
  have hmemE : ∀ j : Fin 5, dV (τ := Tag.E6) ω (e6InnerVec j) ∈
      ⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ := fun j =>
    twE6Two_dV_e6InnerVec_mem_commutator hω3 j
  set zj : Fin 5 → twistedE6RootGroup K σ :=
    fun j => e.symm ⟨dV (τ := Tag.E6) ω (e6InnerVec j), hmemE j⟩ with hzj
  have hezj : ∀ j, e (zj j) = ⟨dV (τ := Tag.E6) ω (e6InnerVec j), hmemE j⟩ :=
    fun j => e.apply_symm_apply _
  have hzjι : ∀ j, g0⁻¹ * baseChangeGL ι (zj j : ModGL TwistTag.E6.tag K) * g0 =
      dV (τ := Tag.E6) ω (e6InnerVec j) := by
    intro j
    have h1 := hcoe (zj j)
    rw [hezj j] at h1
    exact h1.symm
  have hcen : ∀ j, zj j ∈ Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)) := by
    intro j
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, hezj j]
    apply Subtype.ext
    have het : ((e t : ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆) :
        ModGL Tag.E6 (AlgebraicClosure K)) =
        dV (τ := Tag.E6) ω (subLin (τ := Tag.E6) e6InnerVec y) := by
      rw [hcoe t]
      have h3 : g0⁻¹ * (g0 * dV (τ := TwistTag.E6.tag) ω
          (subLin (τ := TwistTag.E6.tag) e6InnerVec y) * g0⁻¹) * g0 =
          dV (τ := TwistTag.E6.tag) ω (subLin (τ := TwistTag.E6.tag) e6InnerVec y) := by group
      rw [ht]
      exact h3
    rw [Subgroup.coe_mul, Subgroup.coe_mul, het]
    change dV (τ := Tag.E6) ω (e6InnerVec j) * _ = _ * dV (τ := Tag.E6) ω (e6InnerVec j)
    rw [← dV_add hω3, ← dV_add hω3, add_comm]
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 1 with hFr
  have hcomp : Fr.comp ι = ι.comp σ.toRingHom := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hFr, iterateFrobenius_two_one, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hσ, map_pow]
  obtain ⟨Fs, hFs⟩ : ∃ F : ModGL TwistTag.E6.tag (AlgebraicClosure K) →*
      ModGL TwistTag.E6.tag (AlgebraicClosure K), F = Units.map (entrywiseHom Fr) := ⟨_, rfl⟩
  have hFd : ∀ x : Fin TwistTag.E6.tag.rank → ZMod 3,
      Fs (dV (τ := TwistTag.E6.tag) ω x) = (dV (τ := TwistTag.E6.tag) ω x)⁻¹ := by
    intro x
    have h1 : Fs (dV (τ := TwistTag.E6.tag) ω x) = dV (τ := TwistTag.E6.tag) ω x ^ 2 := by
      rw [hFs]
      exact entrywiseFrobGL_rootDiagUnit_pow (τ := TwistTag.E6.tag) (k := AlgebraicClosure K)
        (p := 2) 1 (torV ω x)
    rw [h1]
    have h3 := dV_pow_three (τ := TwistTag.E6.tag) hω3 x
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)
  have hιg : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι
      ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans
        (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom) g.2)
  have hιb : baseChangeGL ι b ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [hb, baseChangeGL_rootDiagUnit]
    exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
  set A : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL ι ((g : ModGL TwistTag.E6.tag K) * b) with hA
  have hAG : A ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [hA, map_mul]
    exact mul_mem hιg hιb
  have hFg0 : Fs g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [hFs]
    exact entrywiseFrobGL_mem 2 1 hg0C
  set H := g0⁻¹ * A * Fs g0 with hH
  have hHG : H ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem hg0C) hAG) hFg0
  refine false_of_inverts_innerTorus hω hHG fun j => ?_
  set D := dV (τ := TwistTag.E6.tag) ω (e6InnerVec j) with hD
  have h1 := hfix _ (hcen j)
  have h2 : baseChangeGL ι ((α (zj j) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι ((zj j : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by rw [h1]
  have hZ : baseChangeGL ι (zj j : ModGL TwistTag.E6.tag K) = g0 * D * g0⁻¹ := by
    have h4 : g0⁻¹ * baseChangeGL ι (zj j : ModGL TwistTag.E6.tag K) * g0 = D := hzjι j
    calc _ = g0 * (g0⁻¹ * baseChangeGL ι (zj j : ModGL TwistTag.E6.tag K) * g0) * g0⁻¹ := by group
      _ = _ := by rw [h4]
  rw [hαz, map_mul, map_mul, map_inv, ← hA,
    ← units_map_entrywiseHom_baseChangeGL ι Fr σ.toRingHom hcomp, ← hFs, hZ] at h2
  have hFD : Fs D = D⁻¹ := hFd (e6InnerVec j)
  rw [map_mul, map_mul, map_inv, hFD] at h2
  have key : H * D⁻¹ * H⁻¹ = D := by
    calc H * D⁻¹ * H⁻¹ = g0⁻¹ * (A * (Fs g0 * D⁻¹ * (Fs g0)⁻¹) * A⁻¹) * g0 := by
          rw [hH]; group
      _ = g0⁻¹ * (g0 * D * g0⁻¹) * g0 := by rw [h2]
      _ = D := by group
  calc H * D * H⁻¹ = (H * D⁻¹ * H⁻¹)⁻¹ := by group
    _ = D⁻¹ := by rw [key]

theorem twE6TwoRigid_holds :
    TwE6TwoRigid := by
  intro K _ _ hK σ hσ Fr hFr g0 hg0C hg0 ω hω y hy t ht α hα3 hfix
  have hchar : CharP K 2 := charP_two_of_card_four hK
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_two_one]
  subst hFr'
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨-, -, -, -, -, hcd, hfield, hnf, ⟨Θ, hΘ, -, hker, -, hq3, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK2 σ hσ2
  rcases ringAut_eq_one_or_eq_of_card_four hK σ hσ (Θ α) with h1 | hσα
  · have hαker : α ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hαker
    exact mem_inner_of_coprime_of_exponent_three hq3 hαker hα3
  · obtain ⟨g, u, δ, hαe⟩ := hnf α
    have hδ : δ = σ := (hΘ α g u δ hαe).symm.trans hσα
    rw [hδ] at hαe
    exact (false_of_fixes_inner_torus_fieldAut hK σ hσ hg0C hg0 hω (hcd u) hfield hαe ht
      hfix).elim

end B3

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
