module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE

section Ennola

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
  {σ : K →+* K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ]
  {Fr : Ω →+* Ω}

@[expose] noncomputable def twE6EnnolaDatum (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    LangDatum Tag.E6 Ω where
  Φ := twistE6 Ω Fr
  q := ℓ ^ f
  n := n0 Ω
  g0 := Classical.choose (twE6EnnolaConj hℓ hf hK hFr)
  steinberg := ⟨Fr, hFr, diagramMap TwistTag.E6 Ω, Or.inr ⟨TwistTag.E6, rfl, rfl⟩,
    fun g => rfl⟩
  n_weyl := ⟨twE6W0, rfl⟩
  g0_mem := (Classical.choose_spec (twE6EnnolaConj hℓ hf hK hFr)).1
  lang := by
    have hgn := (Classical.choose_spec (twE6EnnolaConj hℓ hf hK hFr)).2
    show twistE6 Ω Fr (Classical.choose (twE6EnnolaConj hℓ hf hK hFr)) =
      Classical.choose (twE6EnnolaConj hℓ hf hK hFr) * n0 Ω
    calc twistE6 Ω Fr (Classical.choose (twE6EnnolaConj hℓ hf hK hFr))
        = Classical.choose (twE6EnnolaConj hℓ hf hK hFr) *
            ((Classical.choose (twE6EnnolaConj hℓ hf hK hFr))⁻¹ *
              twistE6 Ω Fr (Classical.choose (twE6EnnolaConj hℓ hf hK hFr))) := by group
      _ = Classical.choose (twE6EnnolaConj hℓ hf hK hFr) * n0 Ω := by rw [hgn]

theorem twE6EnnolaDatum_q (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).q = ℓ ^ f :=
  rfl

theorem twE6EnnolaDatum_torus (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {a : Fin Tag.E6.rank → Ωˣ} :
    rootDiagUnit Tag.E6 a ∈ (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).torus ↔
      ∀ i, a i ^ (ℓ ^ f + 1) = 1 := by
  rw [show (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).torus =
      twistedTorusOf (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).n
        (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).Φ from rfl, mem_twistedTorusOf]
  constructor
  · rintro ⟨-, hfix⟩
    have hfix' : theta Fr (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a := by
      have h1 : (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).n *
          (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).Φ (rootDiagUnit Tag.E6 a) *
          (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).n⁻¹ =
          theta Fr (rootDiagUnit Tag.E6 a) := rfl
      rwa [h1] at hfix
    exact (theta_rootDiagUnit_eq_iff Fr hFr a).1 hfix'
  · intro ha
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    refine ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
    show n0 Ω * twistE6 Ω Fr (rootDiagUnit Tag.E6 a) * (n0 Ω)⁻¹ = rootDiagUnit Tag.E6 a
    exact (theta_rootDiagUnit_eq_iff Fr hFr a).2 ha

theorem twE6EnnolaDatum_frob (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    FrobRootMap (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr) (Equiv.neg (Fin Tag.E6.rank → ℤ)) where
  isRoot_iff γ := ⟨fun h => by simpa using IsRoot.neg h, fun h => IsRoot.neg h⟩
  neg_eq γ := rfl
  iform_eq γ δ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.iform_neg_neg' γ δ
  map_rootSubgroup γ hγ := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    haveI : PerfectField Ω := IsAlgClosed.perfectField Ω
    haveI : ExpChar Ω ℓ := ExpChar.prime hℓ
    haveI : PerfectRing Ω ℓ := PerfectField.toPerfectRing ℓ
    have hsurj : Function.Surjective Fr := by
      rw [show Fr = iterateFrobenius Ω ℓ f from
        RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]]
      exact (bijective_iterateFrobenius Ω ℓ f).2
    have h := map_twFrob_rootSubgroup TwistTag.E6 hsurj twE6W0 hγ
    have hneg : twE6W0 • (permLattice TwistTag.E6.perm γ : Fin Tag.E6.rank → ℤ) = -γ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0_smul_permLattice γ
    have hstep : (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).step =
        twFrob TwistTag.E6 (canonicalRep (coxeterSystem Tag.E6) Ω twE6W0) Fr := rfl
    rw [hstep]
    exact h.trans (congrArg (fun z : Fin Tag.E6.rank → ℤ => rootSubgroup Tag.E6 Ω z) hneg)
  rootChar_eq a ha γ hγ := by
    have hq1 : ∀ i, a i ^ ((twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).q + 1) = 1 := by
      rw [show (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).q = ℓ ^ f from rfl]
      exact (twE6EnnolaDatum_torus hℓ hf hK hFr).1 ha
    have h4 : rootChar a γ ^ ((twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).q + 1) = 1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.rootChar_pow_eq_one' hq1 γ
    change rootChar a (-γ) = rootChar a γ ^ (twE6EnnolaDatum (Ω := Ω) hℓ hf hK hFr).q
    rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.rootChar_neg', eq_comm,
      eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h4

end Ennola

end CFSG.LocalAnalysis.GLTheoremA.Y10F
