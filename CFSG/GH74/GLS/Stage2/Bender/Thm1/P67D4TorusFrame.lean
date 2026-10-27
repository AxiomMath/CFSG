module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4PhiFrame_of_toral {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {y z : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hz : z ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K))
    (hFy : twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) y =
      z * y)
    (hyE : ∀ e ∈ E, y * triEmb K σ (AlgebraicClosure K) e * y⁻¹ ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    (u : WeylGroup TwistTag.D4.tag)
    (hu : ∀ x, (u * weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨z⁻¹, inv_mem hz⟩ *
        (weylTwist TwistTag.D4 u)⁻¹) • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) :
    ∃ F : D4PhiFrame K σ (ℓ ^ f) ε, F.Contains E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hrange := triEmb_range (L := L) hℓ hf hK hσ Fr hFr
  set F := twistHom TwistTag.D4 L Fr with hF
  set nu := canonicalRep (coxeterSystem TwistTag.D4.tag) L u with hnu
  have hnuM : nu ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L u
  have hnuG : nu ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnuM
  have hFnu : F nu = canonicalRep (coxeterSystem TwistTag.D4.tag) L (weylTwist TwistTag.D4 u) :=
    twistHom_canonicalRep TwistTag.D4 L Fr u
  have hFnuM : F nu ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [hFnu]
    exact canonicalRep_mem_monomialSubgroup L _
  set y' := nu * y with hy'def
  set z' := F nu * z * nu⁻¹ with hz'def
  have hy' : y' ∈ adjointGroup TwistTag.D4.tag L := mul_mem hnuG hy
  have hz'M : z' ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem hFnuM hz) (inv_mem hnuM)
  have hFy' : F y' = z' * y' := by
    rw [hy'def, hz'def, map_mul, hFy]
    group
  have hn : z'⁻¹ ∈ monomialSubgroup TwistTag.D4.tag L := inv_mem hz'M
  have hW : weylQuotientHom TwistTag.D4.tag L ⟨z'⁻¹, hn⟩ =
      u * weylQuotientHom TwistTag.D4.tag L ⟨z⁻¹, inv_mem hz⟩ * (weylTwist TwistTag.D4 u)⁻¹ := by
    have h1 : weylQuotientHom TwistTag.D4.tag L ⟨nu, hnuM⟩ = u :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep u)
    have h2 : weylQuotientHom TwistTag.D4.tag L ⟨F nu, hFnuM⟩ = weylTwist TwistTag.D4 u := by
      refine weylQuotientHom_eq ?_
      change MapsRootLines (F nu) (weylTwist TwistTag.D4 u)
      rw [hFnu]
      exact mapsRootLines_canonicalRep _
    have h3 : (⟨z'⁻¹, hn⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨nu, hnuM⟩ * ⟨z⁻¹, inv_mem hz⟩ * (⟨F nu, hFnuM⟩)⁻¹ := by
      refine Subtype.ext ?_
      change z'⁻¹ = nu * z⁻¹ * (F nu)⁻¹
      rw [hz'def]
      group
    rw [h3, map_mul, map_mul, map_inv, h1, h2]
  have hw : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨z'⁻¹, hn⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x := fun x => by
    rw [hW]
    exact hu x
  have hg0 : F y'⁻¹ = y'⁻¹ * z'⁻¹ := by
    rw [map_inv, hFy']
    group
  have hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) → P ≤ (triEmb K σ L).range :=
    fun P hPC hPF => by
      rw [hrange]
      exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  refine ⟨⟨Fr, hFr, z'⁻¹, hn, _, rfl, hw, y'⁻¹, inv_mem hy', hg0, hperf⟩, ?_⟩
  unfold D4PhiFrame.Contains
  refine ⟨1, fun e he => ?_⟩
  have hh : y' * triEmb K σ L e * y'⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    have hmem := (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer
      (τ := TwistTag.D4.tag) (R := L) u) _).1 (hyE e he)
    rw [hy'def]
    simpa [mul_assoc] using hmem
  have hFe := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm e
  have e1 : F (y' * triEmb K σ L e * y'⁻¹) = z' * (y' * triEmb K σ L e * y'⁻¹) * z'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hFy', hFe]
    group
  change y'⁻¹⁻¹ * triEmb K σ L (1 * e * 1⁻¹) * y'⁻¹ ∈
    twistedTorusOf z'⁻¹ (twistHom TwistTag.D4 L Fr)
  rw [inv_inv, one_mul, inv_one, mul_one]
  refine mem_twistedTorusOf.2 ⟨hh, ?_⟩
  rw [e1]
  group

end CFSG.GH74.GLS.Stage2.Bender.Thm1
