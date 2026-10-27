module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSixW
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4_toral_twist {L : Type} [Field L] (Fr : L →+* L) {y z : ModGL TwistTag.D4.tag L}
    (hy : y ∈ adjointGroup TwistTag.D4.tag L) (hz : z ∈ monomialSubgroup TwistTag.D4.tag L)
    (hFy : twistHom TwistTag.D4 L Fr y = z * y) (u : WeylGroup TwistTag.D4.tag) :
    ∃ (y' z' : ModGL TwistTag.D4.tag L) (hz' : z' ∈ monomialSubgroup TwistTag.D4.tag L),
      y' ∈ adjointGroup TwistTag.D4.tag L ∧ twistHom TwistTag.D4 L Fr y' = z' * y' ∧
      (∀ h, y * h * y⁻¹ ∈ torusGroup TwistTag.D4.tag L →
        y' * h * y'⁻¹ ∈ torusGroup TwistTag.D4.tag L) ∧
      weylQuotientHom TwistTag.D4.tag L ⟨z'⁻¹, inv_mem hz'⟩ =
        u * weylQuotientHom TwistTag.D4.tag L ⟨z⁻¹, inv_mem hz⟩ *
          (weylTwist TwistTag.D4 u)⁻¹ := by
  classical
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
  refine ⟨y', z', hz'M, hy', hFy', fun h hh => ?_, hW⟩
  have hmem := (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer
    (τ := TwistTag.D4.tag) (R := L) u) _).1 hh
  rw [hy'def]
  simpa [mul_assoc] using hmem

theorem d4SteinbergFrame_of_toral {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K]
    [CharP K ℓ] (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    {y z : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hz : z ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K))
    (hFy : twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      y = z * y)
    (hyE : ∀ e ∈ E, y * triEmb K σ (AlgebraicClosure K) e * y⁻¹ ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    (u : WeylGroup TwistTag.D4.tag)
    (hu : ∀ x, (u * weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨z⁻¹, inv_mem hz⟩ *
        (weylTwist TwistTag.D4 u)⁻¹) • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) :
    ∃ F : D4SteinbergFrame K σ (ℓ ^ f) ε, F.Contains E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨y', z', hz', hy', hFy', hconj, hW⟩ := d4_toral_twist Fr hy hz hFy u
  have hw' : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨z'⁻¹, inv_mem hz'⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x := fun x => by
    rw [hW]
    exact hu x
  set nε := threeSixN L ε with hnε
  have hnεM : nε ∈ monomialSubgroup TwistTag.D4.tag L := threeSixN_mem_monomialSubgroup hε
  have hnεw := threeSixN_weylImage (L := L) hε
  have hWeq : weylQuotientHom TwistTag.D4.tag L ⟨z'⁻¹, inv_mem hz'⟩ =
      weylQuotientHom TwistTag.D4.tag L ⟨nε, hnεM⟩ :=
    ext_single fun i => (hw' _).trans (hnεw _).symm
  set t' := z'⁻¹ * nε⁻¹ with ht'def
  have ht'M : t' ∈ monomialSubgroup TwistTag.D4.tag L := mul_mem (inv_mem hz') (inv_mem hnεM)
  have ht'T : t' ∈ torusGroup TwistTag.D4.tag L := by
    refine mem_torusGroup_of_mapsRootLines_one ht'M ?_
    have h1 : weylQuotientHom TwistTag.D4.tag L ⟨t', ht'M⟩ = 1 := by
      have e : (⟨t', ht'M⟩ : monomialSubgroup TwistTag.D4.tag L) =
          ⟨z'⁻¹, inv_mem hz'⟩ * (⟨nε, hnεM⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, hWeq, mul_inv_cancel]
    have := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := L) ⟨t', ht'M⟩
    rwa [h1] at this
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust Fr hFr hnεM (d4T36M ε) hnεw
    (d4T36M_sub_det_ne_zero hε hq1) ht'T
  set F := twistHom TwistTag.D4 L Fr with hF
  set y'' := s * y' with hy''def
  set z'' := F s * z' * s⁻¹ with hz''def
  have hsG : s ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hsT
  have hy'' : y'' ∈ adjointGroup TwistTag.D4.tag L := mul_mem hsG hy'
  have hFy'' : F y'' = z'' * y'' := by
    rw [hy''def, hz''def, map_mul, hFy']
    group
  have hz''inv : z''⁻¹ = nε := by
    have h1 : z'⁻¹ = t' * nε := by
      rw [ht'def]
      group
    calc z''⁻¹ = s * z'⁻¹ * (F s)⁻¹ := by rw [hz''def]; group
      _ = s * (t' * nε) * (F s)⁻¹ := by rw [h1]
      _ = (s * t') * nε * (F s)⁻¹ := by group
      _ = (nε * F s * nε⁻¹) * nε * (F s)⁻¹ := by rw [hs]
      _ = nε := by group
  have hFg : trialityFrob L Fr y''⁻¹ = y''⁻¹ * threeSixN L ε := by
    change F y''⁻¹ = y''⁻¹ * nε
    rw [map_inv, hFy'', mul_inv_rev, hz''inv]
  refine ⟨⟨Fr, hFr, y''⁻¹, inv_mem hy'', hFg⟩, 1, fun x hx => ?_⟩
  obtain ⟨e, he, rfl⟩ := hx
  have hc : (MulAut.conj (1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).toMonoidHom e =
      e := by
    change (1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * e * 1⁻¹ = e
    group
  rw [hc]
  have hh : y'' * triEmb K σ L e * y''⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    have e2 : y'' * triEmb K σ L e * y''⁻¹ = s * (y' * triEmb K σ L e * y'⁻¹) * s⁻¹ := by
      rw [hy''def]
      group
    rw [e2]
    exact mul_mem (mul_mem hsT (hconj _ (hyE e he))) (inv_mem hsT)
  have hFe := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm e
  have e1 : F (y'' * triEmb K σ L e * y''⁻¹) = z'' * (y'' * triEmb K σ L e * y''⁻¹) * z''⁻¹ := by
    rw [map_mul, map_mul, map_inv, hFy'', hFe]
    group
  show threeSixEmb K L σ e ∈ (threeSixTorsion L Fr ε 3).map (MulAut.conj y''⁻¹).toMonoidHom
  refine ⟨y'' * triEmb K σ L e * y''⁻¹, ?_, ?_⟩
  · refine mem_threeSixTorsion.2 ⟨Subgroup.mem_inf.2 ⟨hh, ?_⟩, ?_⟩
    · change nε * F (y'' * triEmb K σ L e * y''⁻¹) * nε⁻¹ = y'' * triEmb K σ L e * y''⁻¹
      have hz''eq : z'' = nε⁻¹ := by rw [← hz''inv, inv_inv]
      rw [e1, hz''eq]
      group
    · rw [conj_pow, ← map_pow (triEmb K σ L) e 3, hE3 e he, map_one, mul_one, mul_inv_cancel]
  · change y''⁻¹ * (y'' * triEmb K σ L e * y''⁻¹) * y''⁻¹⁻¹ = triEmb K σ L e
    group

end CFSG.GH74.GLS.Stage2.Bender.Thm1
