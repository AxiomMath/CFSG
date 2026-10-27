module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Layers
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.A2
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6DescendedRootSL2
public import CFSG.RankThree.PartOne.KE.E8Rigid

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}

theorem normal_form_A2 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    (c₀ e : twistedE6RootGroup K σ)
    (hy : frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    (hyp : orderOf (frameEmb K σ Ω g c₀ e) = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13)
    {η : MulAut (twistedE6RootGroup K σ)}
    (hη : ∀ u, frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) → η u = u) :
    ∃ a : ModGL Tag.E6 Ω, a ∈ adjointGroup Tag.E6 Ω ∧ ∃ ε : ℕ, ε < 2 ∧
      ∀ u : twistedE6RootGroup K σ, twE6Emb K σ Ω (η u) =
        a * diagE6 Ω ^ ε * twE6Emb K σ Ω u * (diagE6 Ω ^ ε)⁻¹ * a⁻¹ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨h, hh, hB⟩ := phi3_A2_exists_rootSL2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp hA2
  obtain ⟨hlayer, hCs⟩ := layerA2_eq hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp hA2
  set ι : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω := twE6Emb K σ Ω with hιdef
  set h'' : ModGL Tag.E6 Ω := (ι c₀)⁻¹ * g * h with hh''
  have hKey : ∀ Y : SL2 (fixSubfield σ), ∃ u : twistedE6RootGroup K σ,
      frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) ∧
      ι u = h'' * simpleRootSL2 Tag.E6 Ω (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y) *
          h''⁻¹ := by
    intro Y
    have hZ := hB Y
    have hZP : h * simpleRootSL2 Tag.E6 Ω (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y) *
          h⁻¹ ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) := by
      rw [hlayer]
      exact hZ
    have hZC := hCs hZP
    rw [← range_frameEmb (g := g) c₀] at hZC
    obtain ⟨u, hu⟩ := hZC
    refine ⟨u, by rw [hu]; exact hZP, ?_⟩
    have h3 : g⁻¹ * ι (c₀ * u * c₀⁻¹) * g = h * simpleRootSL2 Tag.E6 Ω (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y) *
          h⁻¹ := by
      rw [← hu]
      exact (frameEmb_apply c₀ u).symm
    have h4 : ι (c₀ * u * c₀⁻¹) = g * (h * simpleRootSL2 Tag.E6 Ω (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y) *
          h⁻¹) * g⁻¹ := by
      rw [← h3]
      group
    rw [map_mul, map_mul, map_inv] at h4
    calc ι u = (ι c₀)⁻¹ * (ι c₀ * ι u * (ι c₀)⁻¹) * ι c₀ := by group
      _ = _ := by rw [h4, hh'']; group
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hU : ∀ Y : SL2 (fixSubfield σ), h'' * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (conjGL (1 : GL (Fin 2) Ω) (Matrix.SpecialLinearGroup.map
        ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y)) * h''⁻¹ ∈
          (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K Ω)) := by
    intro Y
    obtain ⟨u, -, hu⟩ := hKey Y
    rw [conjGL_one, ← hu]
    exact ⟨(u : ModGL TwistTag.E6.tag K), u.2, rfl⟩
  have hηU : ∀ (u : twistedE6RootGroup K σ) (Y : SL2 (fixSubfield σ)),
      baseChangeGL (algebraMap K Ω) (u : ModGL TwistTag.E6.tag K) =
        h'' * simpleRootSL2 Tag.E6 Ω (e6Index 0) (conjGL (1 : GL (Fin 2) Ω)
          (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y)) *
            h''⁻¹ → η u = u := by
    intro u Y hu
    obtain ⟨y, hyL, hy'⟩ := hKey Y
    rw [conjGL_one, ← hy'] at hu
    have hu' : ι u = ι y := hu
    rw [twE6Emb_injective hu']
    exact hη y hyL
  obtain ⟨-, a, haC, -, ε, hε, hae⟩ :=
    twisted_E6_descended_root_SL2_pointwise_actors_relative_field_free hℓ hf K hK σ hσ Θ hΘ Ω Fr
      hFr Ω (e6Index 0) 1 h'' hU η hηU
  exact ⟨a, haC, ε, hε, hae⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
