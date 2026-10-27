module

public import CFSG.LieType.SeitzGeneration.QuasiHighLift
public import CFSG.LieType.SeitzGeneration.QuasiHigh6Rest
public import CFSG.LieType.SeitzGeneration.UniPlaneCoverLift
public import CFSG.LieType.SeitzGeneration.CoverDerivedPreimage
public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6Rest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IndicesTwistedA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoLevi
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoLongRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRootSL2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6NegDatumRadical
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLevi
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs
public import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoLeviCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoKill
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogue
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootMono
public import CFSG.LieType.SeitzGeneration.CubeCoverE6Bad
public import Certificates.Certificate214104
public import Certificates.Certificate214105
public import Certificates.Certificate214106
public import Certificates.Certificate214107

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBCentralQuotient
  CFSG.RankThree.PartOne.KE CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh6
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LocalAnalysis.GLTheoremB
  CFSG.LieType.SeitzGeneration.CoverDerivedPreimage
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open scoped commutatorElement

section RootSubgroup

theorem twE6RootSubgroup_pow_ringChar {k : Type} [Field k] [Finite k] {σ : k ≃+* k}
    {β : Fin TwistTag.E6.tag.rank → ℤ} {x : twistedE6RootGroup k σ}
    (hx : x ∈ twE6RootSubgroup k σ β) : x ^ ringChar k = 1 := by
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  haveI : CharP k (ringChar k) := ringChar.charP k
  have hx' : ((x : twistedE6RootGroup k σ) : ModGL TwistTag.E6.tag k) ∈
      rootSubgroup TwistTag.E6.tag k β := hx
  by_cases h1 : ((x : twistedE6RootGroup k σ) : ModGL TwistTag.E6.tag k) = 1
  · rw [show x = 1 from Subtype.ext h1, one_pow]
  · have hord := CFSG.Blueprint.Chevalley.orderOf_eq_of_mem_rootSubgroup hx' h1
    have hpow : ((x : twistedE6RootGroup k σ) : ModGL TwistTag.E6.tag k) ^ ringChar k = 1 := by
      rw [← hord, pow_orderOf_eq_one]
    exact Subtype.ext hpow

end RootSubgroup

section RSet

theorem closure_hyperRSet_le_map_seitzHyperGamma {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) :
    Subgroup.closure (hyperRSet ⊤ (innerImage E) r p) ≤
      (seitzHyperGamma p E).map (QuotientGroup.mk' (Subgroup.center K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro s ⟨-, ⟨n, hn⟩, B, hBE, hBi, hsB⟩
  obtain ⟨F, hFE, hFrel, hF⟩ := exists_hyperplane_of_innerImage hinn hBE hBi
  have hfix : ∀ f ∈ F, quotAut f s = s := by
    intro f hf
    obtain ⟨k, rfl, hk⟩ := hF f hf
    rw [quotAut_conj, Subgroup.mem_centralizer_iff.1 hsB _ hk, mul_inv_cancel_right]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  have hxpow : x ^ r ^ n ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hn]
  have hxcent : ∀ f ∈ F, x⁻¹ * f x ∈ Subgroup.center K := by
    intro f hf
    have h1 := hfix f hf
    rw [quotAut_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  have hrp' : ¬ p ∣ r ^ n := fun hd =>
    hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hd)).symm
  have hFp : IsPGroup p ↥F := (CFSG.Open.IsElemAbelian.isPGroup hE).to_le hFE
  obtain ⟨y, hxy, hyfix⟩ := exists_fixed_mul_center hFp hxcent (Or.inr ⟨r ^ n, hrp', hxpow⟩)
  have hΓ : y ∈ seitzHyperGamma p E :=
    (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFrel⟩ le_rfl) (mem_fixedPoints.2 hyfix)
  refine Subgroup.mem_map.2 ⟨y, hΓ, ?_⟩
  exact (QuotientGroup.eq.2 hxy).symm

theorem coverImage_eq_map_innerImage {K G : Type*} [Group K] [Group G]
    (hperf : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* G)
    {E : Subgroup (MulAut K)} (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) :
    coverImage θ E =
      ((innerImage E).map θ.toMonoidHom).map (MulAut.conj : G →* MulAut G) := by
  rw [coverImage]
  ext φ
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨k, rfl⟩ := hinn hf
    refine ⟨θ (k : K ⧸ Subgroup.center K), ⟨(k : K ⧸ Subgroup.center K),
      mk_mem_innerImage hf, rfl⟩, ?_⟩
    change MulAut.conj (θ.toMonoidHom ((QuotientGroup.mk' (Subgroup.center K)) k)) =
      MulAut.congr θ (quotientCenterAut' K (MulAut.conj k))
    rw [quotientCenterAut'_conj]
    ext g
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨s, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.1 hk
    refine ⟨MulAut.conj k', hk', ?_⟩
    rw [← hk'eq]
    change MulAut.congr θ (quotientCenterAut' K (MulAut.conj k')) =
      MulAut.conj (θ.toMonoidHom ((QuotientGroup.mk' (Subgroup.center K)) k'))
    rw [quotientCenterAut'_conj]
    ext g
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem comap_coverImage_eq_map_innerImage {K G : Type*} [Group K] [Group G]
    (hperf : commutator K = ⊤) (hZ : Subgroup.center G = ⊥)
    (θ : K ⧸ Subgroup.center K ≃* G) {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) :
    (coverImage θ E).comap (MulAut.conj : G →* MulAut G) =
      (innerImage E).map θ.toMonoidHom := by
  rw [coverImage_eq_map_innerImage hperf θ hinn]
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨s, ⟨t, ht, hts⟩, hconj⟩
    rw [← hts] at hconj
    exact ⟨t, ht, mulAut_conj_injective_of_center_eq_bot hZ hconj⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨θ t, ⟨t, ht, rfl⟩, rfl⟩

theorem closure_hyperRSet_le_map_cover {K G : Type*} [Group K] [Group G] [Finite K]
    (hperf : commutator K = ⊤) (hZG : Subgroup.center G = ⊥)
    (θ : K ⧸ Subgroup.center K ≃* G) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup G} (hE₀ : E₀ = (coverImage θ E).comap (MulAut.conj : G →* MulAut G)) :
    Subgroup.closure (hyperRSet ⊤ E₀ r p) ≤
      (seitzHyperGamma p E).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) := by
  classical
  have hE₀' : E₀ = (innerImage E).map θ.toMonoidHom := by
    rw [hE₀, comap_coverImage_eq_map_innerImage hperf hZG θ hinn]
  have hE₀'' : E₀.map θ.symm.toMonoidHom = innerImage E := by
    rw [hE₀', Subgroup.map_map]
    ext x
    simp
  have hmap : hyperRSet ⊤ E₀ r p ⊆
      θ.toMonoidHom '' hyperRSet ⊤ (innerImage E) r p := by
    rintro s ⟨-, ⟨n, hn⟩, B, hB, hBi, hsB⟩
    refine ⟨θ.symm s, ⟨Subgroup.mem_top _, ⟨n, by rw [← map_pow, hn, map_one]⟩,
      B.map θ.symm.toMonoidHom, ?_, ?_, ?_⟩, by simp⟩
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : b ∈ (innerImage E).map θ.toMonoidHom := hE₀' ▸ hB hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.1 hb'
      rw [← hcb]
      simpa using hc
    · rw [← hE₀'', Subgroup.relIndex_map_map_of_injective (f := θ.symm.toMonoidHom) B E₀
        θ.symm.injective, hBi]
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      change θ.symm.toMonoidHom b * θ.symm.toMonoidHom s =
        θ.symm.toMonoidHom s * θ.symm.toMonoidHom b
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hsB b hb]
  have hle : Subgroup.closure (hyperRSet ⊤ E₀ r p) ≤
      (Subgroup.closure (hyperRSet ⊤ (innerImage E) r p)).map θ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨t, ht, hts⟩ := (Set.mem_image _ _ _).1 (hmap hs)
    exact ⟨t, Subgroup.subset_closure ht, hts⟩
  have hclos := closure_hyperRSet_le_map_seitzHyperGamma hperf hp hr hrp hE hinn
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 (hle hx)
  have hmap_t : θ.toMonoidHom t ∈
      ((seitzHyperGamma p E).map (QuotientGroup.mk' (Subgroup.center K))).map
        θ.toMonoidHom := Subgroup.mem_map_of_mem _ (hclos ht)
  rwa [Subgroup.map_map] at hmap_t

section LongRootClosure

theorem longRootSL2_le_closure_hyperRSet {k : Type} [Field k] [Finite k] {σ : k ≃+* k}
    {E₀ : Subgroup (twistedE6RootGroup k σ)} (hE₀ : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) {Fr : AlgebraicClosure k →+* AlgebraicClosure k}
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure k)}
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap k (AlgebraicClosure k)) (x : ModGL TwistTag.E6.tag k) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure k) v)
          (twistHom TwistTag.E6 (AlgebraicClosure k) Fr)).map (MulAut.conj g0).toMonoidHom)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    {X Xm : Subgroup (twistedE6RootGroup k σ)} (hpair : IsTwE6LongRootPair k σ X Xm)
    (hS : ∀ u : twistedE6RootGroup k σ, u ∈ twE6LongRootSL2 X Xm ↔
      baseChangeGL (algebraMap k (AlgebraicClosure k)) (u : ModGL TwistTag.E6.tag k) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure k) {γ, -γ}).map
          (MulAut.conj g0).toMonoidHom) :
    twE6LongRootSL2 X Xm ≤ Subgroup.closure (hyperRSet ⊤ E₀ (ringChar k) 3) := by
  classical
  obtain ⟨F, hFE, hFi, hFcomm⟩ := exists_hyperplane_commute_of_rootSpan hE₀ hcard hT hγ
  obtain ⟨g, hX, hXm⟩ := hpair
  have hpow : ∀ x ∈ (X : Set (twistedE6RootGroup k σ)) ∪
      (Xm : Set (twistedE6RootGroup k σ)), x ^ ringChar k = 1 := by
    rintro x (hx | hx)
    · rw [hX] at hx
      obtain ⟨y, hy, hconj⟩ := Subgroup.mem_map.1 hx
      rw [← hconj, ← map_pow, twE6RootSubgroup_pow_ringChar hy, map_one]
    · rw [hXm] at hx
      obtain ⟨y, hy, hconj⟩ := Subgroup.mem_map.1 hx
      rw [← hconj, ← map_pow, twE6RootSubgroup_pow_ringChar hy, map_one]
  rw [twE6LongRootSL2, Subgroup.closure_le]
  intro u hu
  have huS : u ∈ twE6LongRootSL2 X Xm := Subgroup.subset_closure hu
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ⟨1, by simpa using hpow u hu⟩,
    F, hFE, hFi, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact hFcomm f hf u ((hS u).1 huS)

end LongRootClosure

section LeviPreimage

theorem map_comap_levi_eq_of_inner {K G : Type*} [Group K] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* G) {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup G}
    (hE₀ : E₀ = (coverImage θ E).comap (MulAut.conj : G →* MulAut G))
    {J : Subgroup G} (φ : E₀ →* G) (hφJ : ∀ x, φ x ∈ J)
    (hφc : ∀ x : E₀, ∀ j ∈ J, (x : G) * j * x⁻¹ = φ x * j * (φ x)⁻¹)
    {ε : MulAut K} (hε : ε ∈ E) :
    (J.comap (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))).map
        ε.toMonoidHom =
      J.comap (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) := by
  classical
  let π : K →* G := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let P : Subgroup K := J.comap π
  have hπconj : ∀ k : K,
      ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)) (MulAut.conj k) =
        MulAut.conj (π k) := by
    intro k
    change MulAut.congr θ (quotientCenterAut' K (MulAut.conj k)) = MulAut.conj (π k)
    rw [quotientCenterAut'_conj]
    ext g
    simp [MulAut.congr_apply, MulAut.conj_apply, π]
  have hxE₀ : ∀ k : K, MulAut.conj k ∈ E → π k ∈ E₀ := by
    intro k hk
    rw [hE₀, Subgroup.mem_comap]
    rw [← hπconj k]
    exact Subgroup.mem_map_of_mem _ hk
  have hle : ∀ ε ∈ E, P.map ε.toMonoidHom ≤ P := by
    intro ε hε'
    obtain ⟨k, rfl⟩ := hinn hε'
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hp
    have hπq : π q ∈ J := hq
    have hx : π k ∈ E₀ := hxE₀ k hε'
    change π (k * q * k⁻¹) ∈ J
    rw [map_mul, map_mul, map_inv]
    have h' : π k * π q * (π k)⁻¹ =
        φ ⟨π k, hx⟩ * π q * (φ ⟨π k, hx⟩)⁻¹ := by
      simpa using hφc ⟨π k, hx⟩ (π q) hπq
    rw [h']
    exact J.mul_mem (J.mul_mem (hφJ ⟨π k, hx⟩) hπq) (J.inv_mem (hφJ ⟨π k, hx⟩))
  apply le_antisymm (hle ε hε)
  intro p hp
  have hp' : (ε⁻¹) p ∈ P :=
    hle ε⁻¹ (E.inv_mem hε) (Subgroup.mem_map.2 ⟨p, hp, rfl⟩)
  exact Subgroup.mem_map.2 ⟨ε⁻¹ p, hp', by simp⟩

end LeviPreimage

section LeviAction

theorem leviAction_inner {K G : Type} [Group K] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* G)
    {J : Subgroup G} [Group.IsPerfect J]
    {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup G}
    (hE₀ : E₀ = (coverImage θ E).comap (MulAut.conj : G →* MulAut G))
    (φ : E₀ →* G) (hφJ : ∀ x, φ x ∈ J)
    (hφc : ∀ x : E₀, ∀ j ∈ J, (x : G) * j * x⁻¹ = φ x * j * (φ x)⁻¹)
    (act : E →* MulAut (derivedPreimage (coverPi θ) J))
    (hact_apply : ∀ (ε : E) (j : derivedPreimage (coverPi θ) J),
      ((act ε j : derivedPreimage (coverPi θ) J) : K) = (ε : MulAut K) (j : K)) :
    ∀ ε : E, ∃ y : derivedPreimage (coverPi θ) J,
      ∀ j : derivedPreimage (coverPi θ) J,
        ((act ε j : derivedPreimage (coverPi θ) J) : K) =
          (y : K) * (j : K) * (y : K)⁻¹ := by
  classical
  intro ε
  obtain ⟨k, hk⟩ := hinn ε.2
  let ε' : ↥E := ⟨MulAut.conj k, hk ▸ ε.2⟩
  have hε'eq : ε' = ε := Subtype.ext hk
  have hxE₀ : coverPi θ k ∈ E₀ := by
    rw [hE₀, Subgroup.mem_comap]
    have hconj : ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))
        (MulAut.conj k) = MulAut.conj (coverPi θ k) := by
      change MulAut.congr θ (quotientCenterAut' K (MulAut.conj k)) =
        MulAut.conj (coverPi θ k)
      rw [quotientCenterAut'_conj]
      ext g
      simp [MulAut.congr_apply, MulAut.conj_apply, coverPi]
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ ε'.2
  let x : E₀ := ⟨coverPi θ k, hxE₀⟩
  have hφx : φ x ∈ J := hφJ x
  have hact : ∀ g ∈ J.comap (coverPi θ),
      coverPi θ (k * g * k⁻¹) = φ x * coverPi θ g * (φ x)⁻¹ := by
    intro g hg
    have hπg : coverPi θ g ∈ J := hg
    have h1 : coverPi θ (k * g * k⁻¹) = (x : G) * coverPi θ g * (x : G)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    simpa using hφc x (coverPi θ g) hπg
  obtain ⟨y, hyD, hyeq⟩ :=
    exists_conj_eq_on_derivedPreimage (coverPi θ) (coverPi_surjective θ)
      (le_of_eq (coverPi_ker θ)) hφx hact
  refine ⟨⟨y, hyD⟩, ?_⟩
  intro j
  rw [← hε'eq, hact_apply]
  exact hyeq (j : K) j.2

theorem leviAction_injective {K G : Type} [Group K] [Group G] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* G)
    {Q : TauCeti.PrimePower} {J : Subgroup G} (hJ : IsPSU6Cover J Q) [Group.IsPerfect J]
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup G}
    (hE₀ : E₀ = (coverImage θ E).comap (MulAut.conj : G →* MulAut G))
    (hE₀ab : IsElemAbelian 3 E₀)
    (φ : E₀ →* G) (hφ : Function.Injective φ)
    (hφJ : ∀ x, φ x ∈ J)
    (hφc : ∀ x : E₀, ∀ j ∈ J, (x : G) * j * x⁻¹ = φ x * j * (φ x)⁻¹)
    (act : E →* MulAut (derivedPreimage (coverPi θ) J))
    (hact_apply : ∀ (ε : E) (j : derivedPreimage (coverPi θ) J),
      ((act ε j : derivedPreimage (coverPi θ) J) : K) = (ε : MulAut K) (j : K)) :
    Function.Injective act := by
  rw [injective_iff_map_eq_one]
  intro ε hε1
  obtain ⟨k, hk⟩ := hinn ε.2
  let ε' : ↥E := ⟨MulAut.conj k, hk ▸ ε.2⟩
  have hε'eq : ε' = ε := Subtype.ext hk
  have hε1' : act ε' = 1 := by rw [hε'eq]; exact hε1
  have hfix : ∀ x ∈ derivedPreimage (coverPi θ) J, k * x * k⁻¹ = x := by
    intro x hx
    have h := congrArg (fun f : MulAut ↥(derivedPreimage (coverPi θ) J) => f ⟨x, hx⟩) hε1'
    have h2 := congrArg (fun z : ↥(derivedPreimage (coverPi θ) J) => (z : K)) h
    rw [hact_apply] at h2
    simp only [MulAut.one_apply] at h2
    exact h2
  have hcen : coverPi θ k ∈ Subgroup.centralizer (J : Set G) :=
    map_mem_centralizer_of_conj_fixed (coverPi θ) (coverPi_surjective θ) hfix
  have hxE₀ : coverPi θ k ∈ E₀ := by
    rw [hE₀, Subgroup.mem_comap]
    have hconj : ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))
        (MulAut.conj k) = MulAut.conj (coverPi θ k) := by
      change MulAut.congr θ (quotientCenterAut' K (MulAut.conj k)) = MulAut.conj (coverPi θ k)
      rw [quotientCenterAut'_conj]
      ext g
      simp [MulAut.congr_apply, MulAut.conj_apply, coverPi]
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ ε'.2
  let x : E₀ := ⟨coverPi θ k, hxE₀⟩
  have hφxZ : (⟨φ x, hφJ x⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    change (j' : G) * φ x = φ x * (j' : G)
    have h3 : φ x * (j' : G) * (φ x)⁻¹ = (j' : G) := by
      rw [← hφc x (j' : G) j'.2]
      have hc : (j' : G) * coverPi θ k = coverPi θ k * (j' : G) :=
        Subgroup.mem_centralizer_iff.1 hcen (j' : G) j'.2
      calc (x : G) * (j' : G) * (x : G)⁻¹ = coverPi θ k * (j' : G) * (coverPi θ k)⁻¹ := rfl
        _ = (j' : G) := by rw [hc.symm]; group
    have h4 : φ x * (j' : G) = (j' : G) * φ x := by
      have := congrArg (fun t => t * φ x) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hx1 : x = 1 := by
    by_contra hxne
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE₀ab.2 x x.2)
    have hord3 : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hxne
      · exact h
    have hordφ : orderOf (φ x) = 3 := by
      rw [← hord3]
      exact orderOf_injective φ hφ x
    have hdvdZ : orderOf (φ x) ∣ Nat.card (Subgroup.center ↥J) := by
      have h := orderOf_dvd_natCard (x := (⟨⟨φ x, hφJ x⟩, hφxZ⟩ : Subgroup.center ↥J))
      simpa using h
    rw [hordφ] at hdvdZ
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hJ.2.1.symm)
      (Nat.dvd_trans (by norm_num) hdvdZ)
  have hπk1 : coverPi θ k = 1 := congrArg Subtype.val hx1
  have hkZ : k ∈ Subgroup.center K := by
    rw [← coverPi_ker θ]
    exact MonoidHom.mem_ker.2 hπk1
  have hconj1 : MulAut.conj k = 1 := by
    rw [← MonoidHom.mem_ker, ker_conj]
    exact hkZ
  have hε'1 : ε' = 1 := Subtype.ext hconj1
  rw [← hε'eq, hε'1]

theorem leviAction_image {K G : Type} [Group K] [Group G] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* G)
    {J : Subgroup G} [Group.IsPerfect J]
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (act : E →* MulAut (derivedPreimage (coverPi θ) J))
    (hact_inner : ∀ ε : E, ∃ y : derivedPreimage (coverPi θ) J,
      ∀ j : derivedPreimage (coverPi θ) J,
        ((act ε j : derivedPreimage (coverPi θ) J) : K) =
          (y : K) * (j : K) * (y : K)⁻¹)
    (hact_inj : Function.Injective act) :
    IsElemAbelian 3 act.range ∧ Nat.card act.range = 3 ^ 3 ∧
      act.range ≤ (MulAut.conj :
        ↥(derivedPreimage (coverPi θ) J) →* MulAut ↥(derivedPreimage (coverPi θ) J)).range := by
  have hE_J : IsElemAbelian 3 act.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      change (a : MulAut ↥(derivedPreimage (coverPi θ) J)) *
          (b : MulAut ↥(derivedPreimage (coverPi θ) J)) =
        (b : MulAut ↥(derivedPreimage (coverPi θ) J)) *
          (a : MulAut ↥(derivedPreimage (coverPi θ) J))
      obtain ⟨ε, hε⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.1 b.2
      rw [show (a : MulAut ↥(derivedPreimage (coverPi θ) J)) = act ε from hε.symm,
        show (b : MulAut ↥(derivedPreimage (coverPi θ) J)) = act δ from hδ.symm]
      rw [← map_mul, ← map_mul, hE.1.is_comm.comm ε δ]
    · intro x hx
      obtain ⟨ε, hε⟩ := MonoidHom.mem_range.1 hx
      rw [show x = act ε from hε.symm, ← map_pow]
      have h3 : ε ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (ε : MulAut K) ε.2)
      rw [h3, map_one]
  have hcard_J : Nat.card act.range = 3 ^ 3 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hact_inj]
    simpa using hcard
  have hE_J_inner : act.range ≤ (MulAut.conj :
      ↥(derivedPreimage (coverPi θ) J) →* MulAut ↥(derivedPreimage (coverPi θ) J)).range := by
    rintro _ ⟨ε, rfl⟩
    obtain ⟨y, hyeq⟩ := hact_inner ε
    exact ⟨y, by ext z; rw [MulAut.conj_apply]; exact (hyeq z).symm⟩
  exact ⟨hE_J, hcard_J, hE_J_inner⟩

theorem leviAction_fixed_le {K G : Type} [Group K] [Group G] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* G)
    {J : Subgroup G} [Group.IsPerfect J]
    [Group.IsPerfect ↥(derivedPreimage (coverPi θ) J)]
    {E : Subgroup (MulAut K)}
    (act : E →* MulAut (derivedPreimage (coverPi θ) J))
    (hact_apply : ∀ (ε : E) (j : derivedPreimage (coverPi θ) J),
      ((act ε j : derivedPreimage (coverPi θ) J) : K) = (ε : MulAut K) (j : K))
    (hact_inj : Function.Injective act)
    (hunit : (seitzHyperGamma (K := ↥(derivedPreimage (coverPi θ) J)) 3 act.range) = ⊤) :
    derivedPreimage (coverPi θ) J ≤ seitzHyperGamma 3 E := by
  have hle : (seitzHyperGamma (K := ↥(derivedPreimage (coverPi θ) J)) 3 act.range) ≤
      (seitzHyperGamma 3 E).comap (derivedPreimage (coverPi θ) J).subtype := by
    refine iSup_le fun F_D => iSup_le fun hF_D => ?_
    intro j hj
    let F : Subgroup (MulAut K) := (F_D.comap act).map E.subtype
    have hFE : F ≤ E := Subgroup.map_subtype_le _
    have htopE : E = (⊤ : Subgroup E).map E.subtype := by
      rw [Subgroup.map_top]
      exact (Subgroup.range_subtype E).symm
    have hFrel : F.relIndex E = 3 := by
      rw [htopE, Subgroup.relIndex_map_map_of_injective (f := E.subtype) _ _
        E.subtype_injective]
      have h1 := Subgroup.relIndex_map_map_of_injective (f := act) (F_D.comap act) ⊤ hact_inj
      rw [Subgroup.map_comap_eq_self (f := act) hF_D.1, Subgroup.map_top] at h1
      rw [← h1]
      exact hF_D.2
    have hfix : ∀ f ∈ F, f (j : K) = (j : K) := by
      rintro _ ⟨f', hf', rfl⟩
      have hmapFD : (F_D.comap act).map act = F_D :=
        Subgroup.map_comap_eq_self (f := act) hF_D.1
      have hmem : act f' ∈ F_D := hmapFD ▸ Subgroup.mem_map_of_mem act hf'
      have hfj : act f' j = j := (mem_fixedPoints.1 hj) (act f') hmem
      have hval := congrArg (fun z : ↥(derivedPreimage (coverPi θ) J) => (z : K)) hfj
      rw [hact_apply] at hval
      exact hval
    exact (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K))
      (_ : F ≤ E ∧ F.relIndex E = 3) => fixedPoints F) F ⟨hFE, hFrel⟩ le_rfl)
      (mem_fixedPoints.2 hfix)
  intro j hj
  have hj' : (⟨j, hj⟩ : ↥(derivedPreimage (coverPi θ) J)) ∈
      (seitzHyperGamma (K := ↥(derivedPreimage (coverPi θ) J)) 3 act.range) := by
    rw [hunit]
    exact Subgroup.mem_top _
  exact hle hj'

end LeviAction

section LeviUnitary

theorem leviAction_unitary {K G : Type} [Group K] [Group G] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* G)
    {Q : TauCeti.PrimePower} {J : Subgroup G} (hJ : IsPSU6Cover J Q) [Group.IsPerfect J]
    [Group.IsPerfect ↥(derivedPreimage (coverPi θ) J)]
    {E : Subgroup (MulAut K)}
    (act : E →* MulAut (derivedPreimage (coverPi θ) J))
    (hE_J : IsElemAbelian 3 act.range) (hcard_J : Nat.card act.range = 3 ^ 3)
    (hE_J_inner : act.range ≤ (MulAut.conj :
      ↥(derivedPreimage (coverPi θ) J) →* MulAut ↥(derivedPreimage (coverPi θ) J)).range)
    (h3q : 3 ∣ Q.card + 1) (hq2 : Q.card ≠ 2) :
    (seitzHyperGamma (K := ↥(derivedPreimage (coverPi θ) J)) 3 act.range) = ⊤ := by
  obtain ⟨eZ⟩ := derivedPreimage_centerQuotientEquiv (J := J) (coverPi θ)
    (coverPi_surjective θ) (le_of_eq (coverPi_ker θ))
  obtain ⟨eJ⟩ := hJ.2.2
  have hci : CoverIndex 3 (.twistedA 5 Q) := ⟨by norm_num, h3q⟩
  have hex : ¬ ExcIndex 3 (.twistedA 5 Q) ∨
      (IsSixIndex (.twistedA 5 Q) ∧ act.range ≤ (MulAut.conj :
        ↥(derivedPreimage (coverPi θ) J) →* MulAut ↥(derivedPreimage (coverPi θ) J)).range) := by
    by_cases h8 : Q.card = 8
    · refine Or.inr ⟨?_, hE_J_inner⟩
      exact Or.inr (Or.inr ⟨isTwoPow_of_card_eq' (by rw [h8]; norm_num), Or.inr rfl⟩)
    · refine Or.inl (not_excIndex_twistedA (p := 3) (r := 5) ?_ ?_)
      · rintro ⟨hp, he⟩
        exact hq2 (by rw [TauCeti.PrimePower.card_def, hp, he]; norm_num)
      · rintro ⟨hp, he⟩
        exact h8 (by rw [TauCeti.PrimePower.card_def, hp, he]; norm_num)
  exact QuasiHigh6.seitzHyperGamma_eq_top_unitaryCube Nat.prime_three (by norm_num)
    (K := ↥(derivedPreimage (coverPi θ) J))
    (Group.IsPerfect.commutator_eq_top (G := ↥(derivedPreimage (coverPi θ) J)))
    (eZ.trans eJ) hci hE_J hcard_J hex

theorem levi_le_map_seitzHyperGamma {K G : Type} [Group K] [Group G] [Finite K]
    (hperf : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* G)
    {Q : TauCeti.PrimePower} {J : Subgroup G} (hJ : IsPSU6Cover J Q)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup G}
    (hE₀ : E₀ = (coverImage θ E).comap (MulAut.conj : G →* MulAut G))
    (hE₀ab : IsElemAbelian 3 E₀)
    (φ : E₀ →* G) (hφ : Function.Injective φ)
    (hφJ : ∀ x, φ x ∈ J)
    (hφc : ∀ x : E₀, ∀ j ∈ J, (x : G) * j * x⁻¹ = φ x * j * (φ x)⁻¹)
    (h3q : 3 ∣ Q.card + 1) (hq2 : Q.card ≠ 2) :
    J ≤ (seitzHyperGamma 3 E).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) := by
  classical
  let π : K →* G := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπker : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K)) θ.toMonoidHom
      θ.injective).trans (QuotientGroup.ker_mk' _)
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  haveI hJperf : Group.IsPerfect ↥J := ⟨by
    rw [commutator_def]
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hJ.1⟩
  let Jt : Subgroup K := derivedPreimage π J
  have hJtperf : Group.IsPerfect ↥Jt :=
    derivedPreimage_perfect π hπsurj (le_of_eq hπker) J
  have hJtmap : Jt.map π = J := derivedPreimage_map π hπsurj J
  have hPpres : ∀ ε ∈ E, (J.comap π).map ε.toMonoidHom = J.comap π := fun ε hε =>
    map_comap_levi_eq_of_inner θ hinn hE₀ φ hφJ hφc hε
  have hJtpres : ∀ ε ∈ E, Jt.map ε.toMonoidHom = Jt := by
    intro ε hε
    rw [show Jt = ⁅J.comap π, J.comap π⁆ from derivedPreimage_eq_commutator π J]
    rw [Subgroup.map_commutator, hPpres ε hε]
  let act : E →* MulAut ↥Jt :=
    { toFun := fun ε => (MulEquiv.subgroupMap (ε : MulAut K) Jt).trans
        (MulEquiv.subgroupCongr (hJtpres ε ε.2))
      map_one' := by
        ext x
        rfl
      map_mul' := fun ε δ => by
        ext x
        rfl }
  have hact_apply : ∀ (ε : E) (j : ↥Jt),
      ((act ε j : ↥Jt) : K) = (ε : MulAut K) (j : K) := fun _ _ => rfl
  have hact_inner : ∀ ε : E, ∃ y : Jt,
      ∀ j : Jt, ((act ε j : Jt) : K) = (y : K) * (j : K) * (y : K)⁻¹ :=
    leviAction_inner θ hinn hE₀ φ hφJ hφc act hact_apply
  have hact_inj : Function.Injective act :=
    leviAction_injective θ hJ hE hinn hE₀ hE₀ab φ hφ hφJ hφc act hact_apply
  obtain ⟨hE_J, hcard_J, hE_J_inner⟩ :=
    leviAction_image θ hE hcard act hact_inner hact_inj
  haveI : Group.IsPerfect ↥(derivedPreimage (coverPi θ) J) := hJtperf
  have hunit := leviAction_unitary θ hJ act hE_J hcard_J hE_J_inner h3q hq2
  have hJt_le := leviAction_fixed_le θ act hact_apply hact_inj hunit
  have hJle : J ≤ (seitzHyperGamma 3 E).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) := by
    rw [← hJtmap]
    exact Subgroup.map_mono hJt_le
  exact hJle

end LeviUnitary

section MainBasic

theorem twE6NegDatum_basic {K : Type} [Group K] [Finite K]
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hperf : commutator K = ⊤) (hkq : Nat.card k = q ^ 2) (hqmod : q % 3 = 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup (twistedE6RootGroup k σ)}
    (hE₀ : E₀ = (coverImage θ E).comap
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ))) :
    Subgroup.center (twistedE6RootGroup k σ) = ⊥ ∧
      Function.Injective
        (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)) ∧
      IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 3 ∧ ringChar k ≠ 3 := by
  have hZG : Subgroup.center (twistedE6RootGroup k σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 k σ
  have hconjInj : Function.Injective
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)) :=
    mulAut_conj_injective_of_center_eq_bot hZG
  have hE₀ab : IsElemAbelian 3 E₀ := by
    rw [hE₀]
    exact (isElemAbelian_coverImage θ hE).comap (f := (MulAut.conj :
      twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ))) hconjInj
  have hcardE₀ : Nat.card E₀ = 3 ^ 3 := by
    rw [hE₀, ← Subgroup.card_map_of_injective hconjInj]
    rw [Subgroup.map_comap_eq_self (f := (MulAut.conj :
      twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)))
      (coverImage_le_range_conj θ hEi)]
    rw [card_coverImage hperf θ E, hcard]
  have hr : ringChar k ≠ 3 := by
    intro h3
    have : Fintype k := Fintype.ofFinite k
    have : CharP k (ringChar k) := ringChar.charP k
    obtain ⟨n, -, hn⟩ := FiniteField.card k (ringChar k)
    have h1 : 3 ∣ q ^ 2 := by
      rw [← hkq, Nat.card_eq_fintype_card, hn, h3]
      exact dvd_pow_self 3 n.ne_zero
    have h2 : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow h1
    omega
  exact ⟨hZG, hconjInj, hE₀ab, hcardE₀, hr⟩

end MainBasic

section MainTorus

theorem twE6NegDatum_torus {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hkq : Nat.card k = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (hr : ringChar k ≠ 3)
    {E₀ : Subgroup (twistedE6RootGroup k σ)}
    (hD : TwE6NegDatumDiag k σ q E₀)
    (hNR : ¬ NormalizesRGroup (ringChar k) E₀) :
    ∃ (Fr : AlgebraicClosure k →+* AlgebraicClosure k)
      (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure k)),
      (∀ c, Fr c = c ^ q) ∧
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) ∧
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure k) ∧
      twistHom TwistTag.E6 (AlgebraicClosure k) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure k) v ∧
      (∀ x ∈ E₀,
        baseChangeGL (algebraMap k (AlgebraicClosure k)) (x : ModGL TwistTag.E6.tag k) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure k) v)
            (twistHom TwistTag.E6 (AlgebraicClosure k) Fr)).map
              (MulAut.conj g0).toMonoidHom) ∧
      (∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
        ¬ TwKills k σ E₀ g0 α) := by
  obtain ⟨Fr, hFr, v, hv, g0, hg0C, hg0, hdiag⟩ := hD
  have hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap k (AlgebraicClosure k)) (x : ModGL TwistTag.E6.tag k) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure k) v)
          (twistHom TwistTag.E6 (AlgebraicClosure k) Fr)).map (MulAut.conj g0).toMonoidHom := by
    intro x hx
    have hfix := twBase_twistHom_fix k σ q Fr hσ hFr (x : ModGL TwistTag.E6.tag k) x.2
    refine ⟨g0⁻¹ * baseChangeGL (algebraMap k (AlgebraicClosure k))
        (x : ModGL TwistTag.E6.tag k) * g0, mem_twistedTorusOf.2 ⟨hdiag x hx, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hfix, hg0]
      group
    · show g0 * _ * g0⁻¹ = _
      group
  refine ⟨Fr, v, g0, hFr, hv, hg0C, hg0, hT, ?_⟩
  intro α hα hk
  exact hNR (normalizesRGroup_of_twKills q k σ hkq hσ hr E₀ Fr hFr v g0 hg0C hg0 hT hα hk)

end MainTorus

section MainFinal

theorem seitzHyperGamma_eq_top_of_longRoot_containments {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hkq : Nat.card k = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ)
    {E : Subgroup (MulAut K)}
    (hr : ringChar k ≠ 3)
    {X Xm : Subgroup (twistedE6RootGroup k σ)} (hpair : IsTwE6LongRootPair k σ X Xm)
    {R : Subgroup (twistedE6RootGroup k σ)} (hRQ : R ≤ twE6LongRootRadical X) (hRX : ¬ R ≤ X)
    (hSle : twE6LongRootSL2 X Xm ≤ (seitzHyperGamma 3 E).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))))
    (hRle : R ≤ (seitzHyperGamma 3 E).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))))
    (hJle : twE6LongRootLevi X Xm ≤ (seitzHyperGamma 3 E).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))) :
    seitzHyperGamma 3 E = ⊤ := by
  let π : K →* twistedE6RootGroup k σ :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπker : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K)) θ.toMonoidHom
      θ.injective).trans (QuotientGroup.ker_mk' _)
  have hYtop : (seitzHyperGamma 3 E).map π = ⊤ :=
    eq_top_of_longRoot_le hr hσ hkq hpair hSle hJle hRQ hRle hRX
  have hsup : seitzHyperGamma 3 E ⊔ Subgroup.center K = ⊤ := by
    have h2 := congrArg (Subgroup.comap π) hYtop
    rw [Subgroup.comap_map_eq, hπker, Subgroup.comap_top] at h2
    exact h2
  exact eq_top_of_sup_center_eq_top hperf hsup

end MainFinal

section Main

theorem seitzHyperGamma_eq_top_twE6_negDatum {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hkq : Nat.card k = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hqmod : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup (twistedE6RootGroup k σ)}
    (hE₀ : E₀ = (coverImage θ E).comap
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)))
    (hNR : ¬ NormalizesRGroup (ringChar k) E₀)
    (hD : TwE6NegDatumDiag k σ q E₀) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  obtain ⟨hZG, hconjInj, hE₀ab, hcardE₀, hr⟩ :=
    twE6NegDatum_basic hperf hkq hqmod θ hE hcard hEi hE₀
  obtain ⟨Fr, v, g0, hFr, hv, hg0C, hg0, hT, hreg⟩ :=
    twE6NegDatum_torus hkq hσ hr hD hNR
  obtain ⟨γ, hγ, hES, X, Xm, hpair, hS, R, hRQ, hRH, hRX⟩ :=
    exists_radical_of_negDatum_r q k σ hkq hσ hr E₀ hE₀ab hcardE₀ Fr hFr v g0 hg0C hg0 hT hv hreg
  obtain ⟨φ, hφ, hφJ, hφc⟩ :=
    exists_levi_cube_of_negDatum q k σ hkq hσ hqmod E₀ hE₀ab hcardE₀ Fr hFr v g0 hg0C hg0 hT hv
      hγ hES hpair hS
  have hq2' : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hkq <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq k q hkq hq2'
  let Q : TauCeti.PrimePower := ⟨ringChar k, f, hpr, hf1⟩
  have hQcard : Q.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hJ : IsPSU6Cover (twE6LongRootLevi X Xm) Q := by
    have h0 := twE6LeviCatalogue_holds k σ q hr hσ hkq Q hQcard
    obtain ⟨g, hX, hXm⟩ := hpair
    rw [hX, hXm, twE6LongRootLevi_map]
    exact IsPSU6Cover.of_mulEquiv ((MulAut.conj g).subgroupMap _) h0
  have h3q : 3 ∣ Q.card + 1 := by
    rw [hQcard]
    omega
  have hq2Q : Q.card ≠ 2 := by
    rw [hQcard]
    exact hq2
  let π : K →* twistedE6RootGroup k σ :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπker : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K)) θ.toMonoidHom
      θ.injective).trans (QuotientGroup.ker_mk' _)
  have hSle : twE6LongRootSL2 X Xm ≤ (seitzHyperGamma 3 E).map π :=
    (longRootSL2_le_closure_hyperRSet hE₀ab hcardE₀ hT hγ hpair hS).trans
      (closure_hyperRSet_le_map_cover hperf hZG θ Nat.prime_three hpr hr hE hEi hE₀)
  have hRle : R ≤ (seitzHyperGamma 3 E).map π :=
    hRH.trans (closure_hyperRSet_le_map_cover hperf hZG θ Nat.prime_three hpr hr hE hEi hE₀)
  have hJle : twE6LongRootLevi X Xm ≤ (seitzHyperGamma 3 E).map π :=
    levi_le_map_seitzHyperGamma hperf θ hJ hE hcard hEi hE₀ hE₀ab φ hφ hφJ hφc h3q hq2Q
  exact seitzHyperGamma_eq_top_of_longRoot_containments hperf hkq hσ θ hr hpair hRQ hRX
    hSle hRle hJle

end Main

section NegDatumWiring

theorem coverTwE6NegDatum_holds : CoverTwE6NegDatum := by
  intro K _ _ hperf k _ _ σ q hkq hσ hqmod hq2 θ E hE hcard hEi hNR hD
  exact seitzHyperGamma_eq_top_twE6_negDatum hperf hkq hσ hqmod hq2 θ hE hcard hEi rfl hNR hD

end NegDatumWiring

end RSet

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
