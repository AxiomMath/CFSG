module

public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6DescendedRootSL2
public import CFSG.RankThree.PartOne.KE.E6FourCore
public import CFSG.RankThree.PartOne.KE.E6TwFourGraph

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6_tw_four_normal_of_fixes {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((ℓ ^ f : ℕ) : ZMod p) = 4) (hΦ : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    (hT : twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom Tag.E6 L))
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    {η : MulAut (twistedE6RootGroup K σ)} (hηx : η x = x)
    (hηd : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ)), η d = d) :
    ∃ a : ModGL Tag.E6 L, a ∈ adjointGroup Tag.E6 L ∧
      twistE6 (iterateFrobenius L ℓ f) a = a ∧
      ∀ u : twistedE6RootGroup K σ, twE6Emb K σ L (η u) = a * twE6Emb K σ L u * a⁻¹ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L := twistE6 Fr with hΦdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hord hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set ι : twistedE6RootGroup K σ →* ModGL Tag.E6 L := twE6Emb K σ L with hιdef
  set h'' : ModGL Tag.E6 L := (ι c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 (fixSubfield σ), ∃ y ∈ (⁅Subgroup.centralizer ({x} :
      Set (twistedE6RootGroup K σ)), Subgroup.centralizer ({x} :
        Set (twistedE6RootGroup K σ))⁆ : Subgroup (twistedE6RootGroup K σ)),
      ι y = h'' * simpleRootSL2 Tag.E6 L (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype) Y) *
          h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    rw [← h2] at hmem
    obtain ⟨y', hy', hy'ψ⟩ := hmem
    refine ⟨(y' : twistedE6RootGroup K σ), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hy', rfl⟩
    · have h3 := hψ y'
      rw [hy'ψ] at h3
      have h4 : ι (c * (y' : twistedE6RootGroup K σ) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 Tag.E6 L (e6Index 0)
            (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype) Y) *
              h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc ι (y' : twistedE6RootGroup K σ)
          = (ι c)⁻¹ * (ι c * ι (y' : twistedE6RootGroup K σ) * (ι c)⁻¹) * ι c := by group
        _ = _ := by rw [h4]; group
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hU : ∀ Y : SL2 (fixSubfield σ), h'' * simpleRootSL2 Tag.E6 L (e6Index 0)
      (conjGL (1 : GL (Fin 2) L) (Matrix.SpecialLinearGroup.map
        ((algebraMap K L).comp (fixSubfield σ).subtype) Y)) * h''⁻¹ ∈
          (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)) := by
    intro Y
    obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one, ← hy]
    exact ⟨(y : ModGL TwistTag.E6.tag K), y.2, rfl⟩
  have hηU : ∀ (u : twistedE6RootGroup K σ) (Y : SL2 (fixSubfield σ)),
      baseChangeGL (algebraMap K L) (u : ModGL TwistTag.E6.tag K) =
        h'' * simpleRootSL2 Tag.E6 L (e6Index 0) (conjGL (1 : GL (Fin 2) L)
          (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype) Y)) *
            h''⁻¹ → η u = u := by
    intro u Y hu
    obtain ⟨y, hyD, hy⟩ := hKey Y
    rw [conjGL_one, ← hy] at hu
    have hu' : ι u = ι y := hu
    rw [twE6Emb_injective hu']
    exact hηd y hyD
  obtain ⟨a, haC', haF', ε, hε, hae'⟩ : ∃ a : ModGL Tag.E6 L, a ∈ adjointGroup Tag.E6 L ∧
      twistE6 Fr a = a ∧ ∃ ε : ℕ, ε < 2 ∧ ∀ u : twistedE6RootGroup K σ,
        ι (η u) = a * diagE6 L ^ ε * ι u * (diagE6 L ^ ε)⁻¹ * a⁻¹ := by
    obtain ⟨-, a, haC, haF, ε, hε, hae⟩ :=
      twisted_E6_descended_root_SL2_pointwise_actors_relative_field_free hℓ hf K hK σ hσ Θ hΘ L
        Fr hFr L (e6Index 0) 1 h'' hU η hηU
    exact ⟨a, haC, haF, ε, hε, hae⟩
  refine ⟨a, haC', haF', ?_⟩
  by_contra hne'
  have hε1 : ε = 1 := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hε with h0 | h1
    · have : ε = 0 := by omega
      exfalso
      apply hne'
      intro u
      rw [hae' u, this]
      simp
    · exact h1
  subst hε1
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  have hη' : ∀ u : twistedE6RootGroup K σ, ι (η u) = (a * Q) * ι u * (a * Q)⁻¹ := by
    intro u
    rw [hae' u, pow_one]
    group
  have hmD : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ)),
      (a * Q) * ι d * (a * Q)⁻¹ = ι d := fun d hd => by
    rw [← hη' d, hηd d hd]
  have hmx : (a * Q) * ι x * (a * Q)⁻¹ = ι x := by
    rw [← hη' x, hηx]
  set m' : ModGL Tag.E6 L := g0⁻¹ * ι c * (a * Q) * (ι c)⁻¹ * g0 with hm'
  set G₃ : ModGL Tag.E6 L := g0⁻¹ * ι c * a * (Q * ((ι c)⁻¹ * g0) * Q⁻¹) with hG₃def
  have hm'eq : m' = G₃ * Q := by
    rw [hm', hG₃def]
    group
  have hG₃adj : G₃ ∈ adjointGroup Tag.E6 L := by
    refine mul_mem (mul_mem (mul_mem (inv_mem hg0C) (twE6Emb_mem c)) haC') ?_
    exact E6GraphLevi.diagramMap_conj_mem_adjointGroup' (mul_mem (inv_mem (twE6Emb_mem c)) hg0C)
  have hfixψ : ∀ d : twistedE6RootGroup K σ, (a * Q) * ι d * (a * Q)⁻¹ = ι d →
      m' * (g0⁻¹ * ι (c * d * c⁻¹) * g0) * m'⁻¹ = g0⁻¹ * ι (c * d * c⁻¹) * g0 := by
    intro d hd
    have e : m' * (g0⁻¹ * ι (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * ι c * ((a * Q) * ι d * (a * Q)⁻¹) * (ι c)⁻¹ * g0 := by
      rw [hm']
      simp only [map_mul, map_inv]
      group
    rw [e, hd]
    simp only [map_mul, map_inv]
    group
  have hbfix : b ∈ fixedCharTuples (e6SM (-1)) Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨a', ha', haa⟩ := hh'
    have : a' = b := hinj0 (haa.trans hb.symm)
    exact this ▸ ha'
  have hbp : orderOf (rootDiagUnit Tag.E6 b) = p := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * ι (c * x * c⁻¹) * g0) = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ twE6Emb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  obtain ⟨z, hz0, hzr0, hcol⟩ := exists_column_of_fixed (e6SM (-1)) Fr hFr hp hbfix hbap hb1
  have hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = (-((ℓ ^ f : ℕ) : ZMod p)) • z :=
    transpose_eigen_neg (weylMatrix e6F4U) ((ℓ ^ f : ℕ) : ZMod p) z hzr0
  have hstabb := e6TwFour_stab_of_fixed Fr hFr hp hp3 hord hΦ hbfix hbap hb1
  have hCent : ∀ y ∈ adjointGroup Tag.E6 L, y * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * y →
      y ∈ (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) *
        (rootSpan Tag.E6 L (sigmaSetE6A3 v) : Set (ModGL Tag.E6 L)) := fun y hy hcomm' =>
    mem_torus_mul_rootSpan_of_commute_of_stab hstabb (sigmaSetE6A3_isRoot v)
      (sigmaSetE6A3_neg v) (by rw [hSeq]) hy hcomm'
  have hfixh : (G₃ * diagE6 L) * rootDiagUnit Tag.E6 b * (G₃ * diagE6 L)⁻¹ =
      rootDiagUnit Tag.E6 b := by
    rw [← hm'eq, hb]
    exact hfixψ x hmx
  have hp5 : p = 5 ∨ 7 < p := e6Four_p_cases hp hp3 hord
  refine e6_tw_graph_contra (L := L) hp5 (r := -((ℓ ^ f : ℕ) : ZMod p))
    (neg_sq_add_one_eq_zero_zmod hΦ) hz0 hzr hcol hSeq hCent hG₃adj hfixh (k := fixSubfield σ)
    (H := H) (fun Y => ?_)
  have hmem : rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map
      (algebraMap (fixSubfield σ) L) Y * H⁻¹) ∈ Pt := hH Y
  rw [← h2] at hmem
  obtain ⟨d', hd', hd'ψ⟩ := hmem
  have hd'D : ((d' : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) :
      twistedE6RootGroup K σ) ∈ (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
        Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
          Subgroup (twistedE6RootGroup K σ)) := by
    rw [← h1]
    exact ⟨d', hd', rfl⟩
  rw [← hm'eq, ← hd'ψ, hψ d']
  exact hfixψ _ (hmD _ hd'D)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
