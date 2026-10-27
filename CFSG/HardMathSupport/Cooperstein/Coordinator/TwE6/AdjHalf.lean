module

public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.InvariantsTransport
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjPair
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispIso

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc TensorProduct

section BCInv

variable {K : Type*} [Field K] {k : Type*} [Field k] [Algebra K k] {V : Type*} [AddCommGroup V]
  [Module K V] [Module.Finite K V] {G : Type*} [Group G] [Finite G]

theorem finrank_invariants_bc_le (ρ : Representation K G V) :
    Module.finrank k ↥(Representation.invariants (bcRep k ρ)) ≤
      Module.finrank K ↥(Representation.invariants ρ) := by
  classical
  let b := Module.finBasis K V
  have h1 := CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.finrank_invariants_le_of_basis
    (algebraMap K k) (bcRep k ρ) (Algebra.TensorProduct.basis k b)
    (fun g => LinearMap.toMatrix b b (ρ g)) (fun g => LinearMap.toMatrix_baseChange k (ρ g) b b)
  refine h1.trans (le_of_eq ?_)
  have hmat : ∀ (g : G) (x : Fin (Module.finrank K V) → K),
      b.equivFun (ρ g (b.equivFun.symm x)) = Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) x := by
    intro g x
    have key := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm x)
    have hx : ⇑(b.repr (b.equivFun.symm x)) = x := by
      rw [← Module.Basis.equivFun_apply]
      exact b.equivFun.apply_symm_apply x
    rw [hx] at key
    rw [Matrix.toLin'_apply, key, Module.Basis.equivFun_apply]
  have hmap : (Representation.invariants ρ).map b.equivFun.toLinearMap =
      ⨅ g : G, LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) - 1) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero, Representation.mem_invariants]
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      show Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) (b.equivFun v) = b.equivFun v
      rw [← hmat g, b.equivFun.symm_apply_apply, hv g]
    · intro hx
      refine ⟨b.equivFun.symm x, ?_, b.equivFun.apply_symm_apply x⟩
      intro g
      apply b.equivFun.injective
      rw [hmat g, b.equivFun.apply_symm_apply]
      exact hx g
  rw [← hmap]
  exact LinearEquiv.finrank_map_eq b.equivFun _

end BCInv


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

set_option maxHeartbeats 1600000 in
include hf hK hσ in
theorem tw78HalfOffenderBound_of_pair (hpair : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A :
    Subgroup ↥(adjointGroup TwistTag.E6.tag K)), A ≠ ⊥ → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈
    A, a ^ 2 = 1) → Nat.card A ^ 2 * Nat.card K ^ Module.finrank K ↥(fixSub (adjRep TwistTag.E6.tag
    K) A) ≤ Nat.card K ^ 59) : Tw78HalfOffenderBound hf K hK σ hσ := by
  intro k _ _ _ _ m ρ y χ J hρ ht h78 A hA hel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst (K := K) σ
  obtain ⟨b, β, hβ⟩ := twE6_iso_78 hf hK σ hσ hρ ht h78
  have hm : m = 78 := by
    have h1 := LinearEquiv.finrank_eq β
    rw [finrank_frobTwist, Module.finrank_fin_fun, Module.finrank_baseChange, finrank_adj78] at h1
    exact h1.symm
  subst hm
  have hle : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left
  let ψ : ↥A →* ↥(adjointGroup TwistTag.E6.tag K) :=
    ((Subgroup.inclusion hle).comp (coverHom hf hK σ hσ)).comp A.subtype
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : coverHom hf hK σ hσ (x : ↥(TwistedE6.fixedGroup K σ)) =
        coverHom hf hK σ hσ (y : ↥(TwistedE6.fixedGroup K σ)) :=
      Subgroup.inclusion_injective hle hxy
    have h2 : coverHom hf hK σ hσ ((x : ↥(TwistedE6.fixedGroup K σ))⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : ((x : ↥(TwistedE6.fixedGroup K σ))⁻¹ * y) ^ 2 = 1 := by
      have := hel _ (A.mul_mem (A.inv_mem x.2) y.2)
      exact this
    have h4 := (isCentralCover_coverHom hf hK σ hσ).eq_one_of_isPElt (MonoidHom.mem_ker.2 h2)
      ⟨1, by rw [pow_one]; exact h3⟩
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hcard : Nat.card ψ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hne : ψ.range ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
    intro h
    have : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (hψinj (this.trans (map_one ψ).symm))
  have hel' : ∀ a ∈ ψ.range, a ^ 2 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hel x.1 x.2)
    rw [this, map_one]
  have hcomm : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b) ^ 2 = 1 := hel' _ (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hel' a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hel' b hb)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h1)
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hpr := hpair K ψ.range hne hcomm hel'
  rw [hcard] at hpr
  have hinv : Representation.invariants (((twAdj σ).comp (coverHom hf hK σ hσ)).comp A.subtype) =
      fixSub (adjRep TwistTag.E6.tag K) ψ.range := by
    ext v
    rw [Representation.mem_invariants, mem_fixSub]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact h x
    · intro h x
      exact h (ψ x) ⟨x, rfl⟩
  have hc : Module.finrank k ↥(Representation.invariants (ρ.comp A.subtype)) ≤
      Module.finrank K ↥(fixSub (adjRep TwistTag.E6.tag K) ψ.range) := by
    have e1 := finrank_invariants_twist (frobAut k b) (ρ.comp A.subtype)
    have e2 := CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.finrank_invariants_of_linearEquiv
      (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)).comp A.subtype)
      ((twistRep (frobAut k b) ρ).comp A.subtype) β (fun g v => hβ g.1 v)
    have e3 := finrank_invariants_bc_le (k := k)
      (((twAdj σ).comp (coverHom hf hK σ hσ)).comp A.subtype)
    rw [hinv] at e3
    have e4 : Module.finrank k ↥(Representation.invariants ((twistRep (frobAut k b) ρ).comp A.subtype)) =
        Module.finrank k ↥(Representation.invariants (ρ.comp A.subtype)) := e1
    have e5 : Module.finrank k ↥(Representation.invariants
        (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)).comp A.subtype)) ≤
        Module.finrank K ↥(fixSub (adjRep TwistTag.E6.tag K) ψ.range) := e3
    omega
  set q : ℕ := 2 ^ f with hq
  set X : ℕ := Nat.card A with hX
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set c : ℕ := Module.finrank K ↥(fixSub (adjRep TwistTag.E6.tag K) ψ.range) with hcdef
  set c' : ℕ := Module.finrank k ↥(Representation.invariants (ρ.comp A.subtype)) with hc'def
  rw [hK] at hpr
  have hpr' : X ^ 2 * (q ^ c) ^ 2 ≤ q ^ 118 := by
    have : X ^ 2 * (q ^ 2) ^ c ≤ (q ^ 2) ^ 59 := hpr
    calc X ^ 2 * (q ^ c) ^ 2 = X ^ 2 * (q ^ 2) ^ c := by ring
      _ ≤ (q ^ 2) ^ 59 := this
      _ = q ^ 118 := by ring
  have hX1 : 2 * X * q ^ c' ≤ 2 * X * q ^ c :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hc)
  have hbig : (2 * X * q ^ c) ^ 2 < (q ^ 78) ^ 2 := by
    calc (2 * X * q ^ c) ^ 2 = 4 * (X ^ 2 * (q ^ c) ^ 2) := by ring
      _ ≤ 4 * q ^ 118 := Nat.mul_le_mul_left _ hpr'
      _ < q ^ 38 * q ^ 118 := by
        have h38 : 4 < q ^ 38 := by
          calc 4 < 2 ^ 38 := by norm_num
            _ ≤ q ^ 38 := Nat.pow_le_pow_left hq2 38
        have : 0 < q ^ 118 := by positivity
        nlinarith
      _ = (q ^ 78) ^ 2 := by ring
  have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hbig
  exact lt_of_le_of_lt hX1 this

include hf hK hσ in
theorem tw78HalfOffenderBound_holds : Tw78HalfOffenderBound hf K hK σ hσ :=
  tw78HalfOffenderBound_of_pair hf hK σ hσ fun K _ _ _ A hA hc he => by
    have h := FFExc.adj_pair_bound_E6 (K := K) A hA hc he
    have e : FFExc.adjFix K A = fixSub (adjRep TwistTag.E6.tag K) A :=
      Submodule.ext fun _ => Iff.rfl
    rw [e] at h
    exact h

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
