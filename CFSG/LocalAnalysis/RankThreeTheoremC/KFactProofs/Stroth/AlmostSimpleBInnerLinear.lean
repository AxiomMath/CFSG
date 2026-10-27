module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGLMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerReduce
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.CALinearPrimary CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Polynomial

section Centralizer

variable {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ}

theorem oddPCoreInClosure_centralizer_slGL_of_squarefree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Matrix.SpecialLinearGroup (Fin n) k}
    (hsq : Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k)))) :
    OddPCoreInClosure p
      ↥(Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))) := by
  classical
  haveI : Finite (LinearMap.GeneralLinearGroup k (Fin n → k)) := finite_generalLinearGroup'
  have hC : OddPCoreInClosure p ↥(gl_centralizer (slGL n k a)) := by
    refine OddPCoreInClosure.of_mulEquiv (glCentralizerEquivPi hsq).symm ?_
    have hblock : ∀ b : primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)),
        OddPCoreInClosure p (blockGL ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) (b : k[X])) := by
      intro b
      haveI : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      haveI : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
      haveI : CharP (AdjoinRoot (b : k[X])) 2 :=
        charP_of_injective_ringHom (AdjoinRoot.of (b : k[X])).injective 2
      exact oddPCoreInClosure_generalLinearGroup hp hp2
    haveI : ∀ b : primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)),
        Finite (blockGL ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) (b : k[X])) := by
      intro b
      haveI : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      haveI : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
      exact finite_generalLinearGroup'
    exact OddPCoreInClosure.pi hp hblock
  let ψ : ↥(Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))) →*
      ↥(gl_centralizer (slGL n k a)) :=
    ((slGL n k).comp
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))).subtype).codRestrict
      (gl_centralizer (slGL n k a)) (fun g => by
        have hg : (g : Matrix.SpecialLinearGroup (Fin n) k) * a = a * g :=
          Subgroup.mem_centralizer_singleton_iff.1 g.2
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        change slGL n k g * slGL n k a = slGL n k a * slGL n k g
        rw [← map_mul, ← map_mul, hg])
  have hψinj : Function.Injective ψ := fun g₁ g₂ h =>
    Subtype.ext (slGL_injective (congrArg Subtype.val h))
  have hψn : ψ.range.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨g, rfl⟩ := hy
    set z : ↥(gl_centralizer (slGL n k a)) := c * ψ g * c⁻¹ with hz
    let D : LinearMap.GeneralLinearGroup k (Fin n → k) →* kˣ :=
      Units.map (LinearMap.det : Module.End k (Fin n → k) →* k)
    have hDg : D ((ψ g : ↥(gl_centralizer (slGL n k a))) :
        LinearMap.GeneralLinearGroup k (Fin n → k)) = 1 := by
      refine Units.ext ?_
      change LinearMap.det ((slGL n k g : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)) = 1
      rw [coe_slGL, LinearMap.det_toLin']
      exact g.1.2
    have hDz : D (z : LinearMap.GeneralLinearGroup k (Fin n → k)) = 1 := by
      have : (z : LinearMap.GeneralLinearGroup k (Fin n → k)) =
          (c : LinearMap.GeneralLinearGroup k (Fin n → k)) *
            (ψ g : LinearMap.GeneralLinearGroup k (Fin n → k)) *
            (c : LinearMap.GeneralLinearGroup k (Fin n → k))⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hDg, mul_one, mul_inv_cancel]
    have hdet : LinearMap.det ((z : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)) = 1 := by
      have := congrArg Units.val hDz
      simpa [D] using this
    obtain ⟨g', hg'⟩ := mem_range_slGL hdet
    have hzc : (z : LinearMap.GeneralLinearGroup k (Fin n → k)) * slGL n k a =
        slGL n k a * (z : LinearMap.GeneralLinearGroup k (Fin n → k)) :=
      Subgroup.mem_centralizer_singleton_iff.1 z.2
    have hg'c : g' ∈ Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k)) := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      apply slGL_injective
      rw [map_mul, map_mul, hg']
      exact hzc
    exact ⟨⟨g', hg'c⟩, Subtype.ext hg'⟩
  have hrange : OddPCoreInClosure p ↥ψ.range := OddPCoreInClosure.of_normal hp ψ.range hC
  exact OddPCoreInClosure.of_mulEquiv (MonoidHom.ofInjective hψinj).symm hrange

theorem oddPCoreInClosure_centralizer_slGL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Matrix.SpecialLinearGroup (Fin n) k} (hap : a ^ p = 1) :
    OddPCoreInClosure p
      ↥(Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))) := by
  have hpk : (p : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  exact oddPCoreInClosure_centralizer_slGL_of_squarefree hp hp2 (squarefree_minpoly_slGL hpk hap)

theorem exists_lift_pow_eq_one {p : ℕ} (hp : p.Prime)
    (hZ : ∀ z ∈ scalars n k, z ^ p = 1 → z = 1) {d : projectiveSL n k} (hdp : d ^ p = 1) :
    ∃ a : Matrix.SpecialLinearGroup (Fin n) k, proj n k a = d ∧ a ^ p = 1 := by
  obtain ⟨b, rfl⟩ := proj_surjective n k d
  have hmem : b ^ p ∈ scalars n k := by
    rw [← proj_eq_one_iff, map_pow]
    exact hdp
  have hcop : Nat.Coprime (Nat.card (scalars n k)) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := scalars n k) p hdvd
    have hz1 : (z : Matrix.SpecialLinearGroup (Fin n) k) ^ p = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have hz2 : z = 1 := Subtype.ext (hZ z z.2 hz1)
    rw [hz2, orderOf_one] at hz
    exact hp.one_lt.ne hz
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective ⟨(b ^ p)⁻¹, (scalars n k).inv_mem hmem⟩
  have hw' : w ^ p = ⟨(b ^ p)⁻¹, (scalars n k).inv_mem hmem⟩ := hw
  have hwp : (w : Matrix.SpecialLinearGroup (Fin n) k) ^ p = (b ^ p)⁻¹ := congrArg Subtype.val hw'
  have hc : Commute b (w : Matrix.SpecialLinearGroup (Fin n) k) :=
    Subgroup.mem_center_iff.1 (scalars_le_center n k w.2) b
  refine ⟨b * w, ?_, ?_⟩
  · rw [map_mul, (proj_eq_one_iff).2 w.2, mul_one]
  · rw [hc.mul_pow, hwp, mul_inv_cancel]

theorem pClosureOdd_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ∀ z ∈ scalars n k, z ^ p = 1 → z = 1) : PClosureOdd p (projectiveSL n k) := by
  intro d hd1 hdp
  obtain ⟨a, rfl, hap⟩ := exists_lift_pow_eq_one hp hZ hdp
  have hOC := oddPCoreInClosure_centralizer_slGL hp hp2 hap
  let φ : ↥(Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))) →*
      ↥(Subgroup.centralizer ({proj n k a} : Set (projectiveSL n k))) :=
    ((proj n k).comp
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))).subtype).codRestrict
      _ (fun g => by
        have hg : (g : Matrix.SpecialLinearGroup (Fin n) k) * a = a * g :=
          Subgroup.mem_centralizer_singleton_iff.1 g.2
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        change proj n k g * proj n k a = proj n k a * proj n k g
        rw [← map_mul, ← map_mul, hg])
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := proj_surjective n k (y : projectiveSL n k)
    have hy : (y : projectiveSL n k) * proj n k a = proj n k a * (y : projectiveSL n k) :=
      Subgroup.mem_centralizer_singleton_iff.1 y.2
    have h1 : proj n k (g * a * g⁻¹) = proj n k a := by
      rw [map_mul, map_mul, map_inv, hg]
      calc (y : projectiveSL n k) * proj n k a * (y : projectiveSL n k)⁻¹
          = (proj n k a * (y : projectiveSL n k)) * (y : projectiveSL n k)⁻¹ := by rw [hy]
        _ = proj n k a := by group
    have h2 := conj_eq_of_proj_eq_of_scalars hZ hap h1
    have hga : g * a = a * g := by
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [h2]
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 hga⟩, Subtype.ext hg⟩
  have hφker : φ.ker ≤ Subgroup.center
      ↥(Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) k))) := by
    intro g hg
    have h1 : proj n k (g : Matrix.SpecialLinearGroup (Fin n) k) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).1 hg)
    have hs : (g : Matrix.SpecialLinearGroup (Fin n) k) ∈ scalars n k :=
      (proj_eq_one_iff).1 h1
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.1 (scalars_le_center n k hs) h.1)
  exact OddPCoreInClosure.of_surjective_ker_le_center hp φ hφsurj hφker hOC

end Centralizer

section Family

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

theorem scalars_no_pTorsion {k : Type} [Field k] [Finite k] {n p : ℕ} [NeZero n] (hp : p.Prime)
    (hF : ¬ p ∣ Nat.gcd n (Nat.card k - 1)) :
    ∀ z ∈ scalars n k, z ^ p = 1 → z = 1 := by
  intro z hz hzp
  obtain ⟨c, hc, hzc⟩ := hz
  have h1 : ((z : Matrix.SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) ^ p = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) k =>
      (g : Matrix (Fin n) (Fin n) k)) hzp
    simpa using this
  have hcp : c ^ p = 1 := by
    rw [hzc, ← map_pow] at h1
    have h2 : (Matrix.scalar (Fin n)) ((c : k) ^ p) = (Matrix.scalar (Fin n)) 1 := by
      rw [map_one]
      exact h1
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    have h3 : (c : k) ^ p = 1 := Matrix.scalar_inj.1 h2
    exact Units.ext (by simpa using h3)
  have hord : orderOf c = 1 := by
    by_contra hne
    have h4 : orderOf c = p :=
      ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hcp)).resolve_left hne
    have h5 : p ∣ n := h4 ▸ orderOf_dvd_of_pow_eq_one hc
    have h6 : p ∣ Nat.card k - 1 := by
      have := orderOf_dvd_natCard c
      rw [h4, Nat.card_units] at this
      exact this
    exact hF (Nat.dvd_gcd h5 h6)
  have hc1 : c = 1 := orderOf_eq_one_iff.1 hord
  subst hc1
  apply Subtype.ext
  rw [hzc]
  simp

theorem chevTwoPClosureOddFamily_linear : ChevTwoPClosureOddFamily LieFamilyLinear := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | A r q =>
    obtain ⟨e⟩ := he
    have hF' : ¬ p ∣ Nat.gcd (r + 1) (q.card - 1) := hF
    have hdi' : q.p = 2 := hdi
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI : CharP (GaloisField q.p q.exponent) 2 := by
      rw [← hdi']
      infer_instance
    let e1 : L ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          (r + 1) (GaloisField q.p q.exponent)))
    have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
      (CFSG.Models.card_galoisField q).trans (TauCeti.PrimePower.card_def q).symm
    exact PClosureOdd.of_mulEquiv e1.symm
      (pClosureOdd_projectiveSL hp hp2 (scalars_no_pTorsion hp (by rwa [hcard])))
  | _ => exact absurd hF (by simp [LieFamilyLinear])

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
