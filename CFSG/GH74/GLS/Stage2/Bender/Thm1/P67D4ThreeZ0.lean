module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreePerX
public import CFSG.RankThree.PartOne.KGD.D4T36Plane
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4_three_Z0_trivial {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : 2 < ℓ ^ f) (hℓ3 : ℓ ≠ 3)
    {n : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K))
    (w : WeylGroup TwistTag.D4.tag)
    (hnw : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g0 : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.D4 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      P ≤ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) →
      (∀ x ∈ P, twistHom TwistTag.D4 (AlgebraicClosure K)
        (iterateFrobenius (AlgebraicClosure K) ℓ f) x = x) →
        P ≤ (triEmb K σ (AlgebraicClosure K)).range)
    (E : Subgroup 𝒞[K, σ]) (hE : IsElementaryAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (c : 𝒞[K, σ])
    (hc : ∀ y ∈ E, g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * y * c⁻¹) * g0 ∈
      twistedTorusOf n (twistHom TwistTag.D4 (AlgebraicClosure K)
        (iterateFrobenius (AlgebraicClosure K) ℓ f)))
    (Z₀ : Subgroup 𝒞[K, σ]) (hZc : ∀ t ∈ Z₀, ∀ e ∈ E, t * e = e * t)
    (hZab : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a)
    (hZn : ∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]), ∀ t ∈ Z₀,
      s * t * s⁻¹ ∈ Z₀) :
    ∀ t ∈ Z₀, t = 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hcomm := d4Q_hcomm K σ hσ (AlgebraicClosure K)
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) (AlgebraicClosure K) :=
    IsAlgClosure.ofAlgebraic (fixSubfield σ) K (AlgebraicClosure K)
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ hf hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K)) :=
    rootDiagUnit_injective
  have hEexp : ∀ q ∈ E, q ^ 3 = 1 := fun q hq =>
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E) ⟨q, hq⟩)
  let φ : E →* ModGL TwistTag.D4.tag (AlgebraicClosure K) := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((triEmb K σ (AlgebraicClosure K)).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ q : E, φ q =
      g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := fun q => by
    change (MulAut.conj g0⁻¹ : MulAut (ModGL TwistTag.D4.tag (AlgebraicClosure K)))
      (triEmb K σ (AlgebraicClosure K) ((MulAut.conj c : MulAut 𝒞[K, σ]) (q : 𝒞[K, σ]))) = _
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  have hφT : ∀ q : E, φ q ∈ twistedTorusOf n
      (twistHom TwistTag.D4 (AlgebraicClosure K)
        (iterateFrobenius (AlgebraicClosure K) ℓ f)) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
        φ q = rootDiagUnit TwistTag.D4.tag b)
  have hβmul : ∀ q q' : E, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := AlgebraicClosure K)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := AlgebraicClosure K)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hker : ∀ i : Fin TwistTag.D4.tag.rank, ∃ q : E, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : E →* (AlgebraicClosure K)ˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine d4Q_exists_ne_one_ker_of_card_sq hp hEcard χ fun q => ?_
    have h1 : rootDiagUnit TwistTag.D4.tag (β q) ^ 3 = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ 3 = 1 := Subtype.ext (hEexp q q.2)
      rw [this, map_one]
    have h2 : β q ^ 3 = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  have hT := twistedTorus_D4_eq_map_of_weylImage
    (iterateFrobenius (AlgebraicClosure K) ℓ f) hn w hnw (d4T36M ε) hw
  obtain ⟨q₁, hq₁1, hq₁⟩ := hker ⟨0, by decide⟩
  obtain ⟨q₂, hq₂1, hq₂⟩ := hker ⟨1, by decide⟩
  have hc₁ : rootChar (β q₁) (Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1) = 1 := by
    rw [CTTorus.rootChar_single]; exact hq₁
  have hc₂ : rootChar (β q₂) (Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) 1) = 1 := by
    rw [CTTorus.rootChar_single]; exact hq₂
  have hdiff : ∀ i : Fin 4, ¬ ((Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) :
      Fin Tag.D4.rank → ℤ) ∈ trialitySigmaList i ∧
      (Pi.single (⟨1, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∈
        trialitySigmaList i) := by
    decide +kernel
  have hperx : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).Nonempty →
      ∀ V : Subgroup (Subgroup.centralizer ({(x : 𝒞[K, σ])} : Set 𝒞[K, σ])), V.Normal →
      Group.IsSolvable V → ∀ v ∈ V,
      d4QPsi (triEmb K σ (AlgebraicClosure K)) g0 c (x : 𝒞[K, σ]) v ∈ twistedTorusOf n
        (twistHom TwistTag.D4 (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) ℓ f)) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
          d4QPsi (triEmb K σ (AlgebraicClosure K)) g0 c (x : 𝒞[K, σ]) v =
            rootDiagUnit TwistTag.D4.tag a ∧ ∀ α ∈ rootCharKernel (β x), rootChar a α = 1 := by
    intro x hx1 hne
    have hxp : orderOf (x : 𝒞[K, σ]) = 3 :=
      orderOf_eq_prime (hEexp x x.2) (fun h => hx1 (Subtype.ext h))
    have hb : rootDiagUnit TwistTag.D4.tag (β x) =
        g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * (x : 𝒞[K, σ]) * c⁻¹) * g0 := by
      rw [← hβ, hφ]
    have hh : rootDiagUnit TwistTag.D4.tag (β x) ∈ twistedTorusOf n
        (twistHom TwistTag.D4 (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) ℓ f)) := by
      rw [← hβ]
      exact hφT x
    exact d4T36_perx_three hf K σ hkc hε hq2 hℓ3 hn w hnw hw hg0C hg0 hperf hcomm hxp c hb hh hne
  have hpsi : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).Nonempty → ∀ t ∈ Z₀,
      ∃ a : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
      g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * t * c⁻¹) * g0 =
        rootDiagUnit TwistTag.D4.tag a ∧
      a ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius (AlgebraicClosure K) ℓ f) ∧
      ∀ α ∈ rootCharKernel (β x), rootChar a α = 1 := by
    intro x hx1 hne t ht
    have hxt : t ∈ Subgroup.centralizer ({(x : 𝒞[K, σ])} : Set 𝒞[K, σ]) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hZc t ht x x.2)
    let V : Subgroup (Subgroup.centralizer ({(x : 𝒞[K, σ])} : Set 𝒞[K, σ])) :=
      Z₀.subgroupOf _
    have hVn : V.Normal := ⟨fun y hy s => by
      have h := hZn (x : 𝒞[K, σ]) x.2 (fun h => hx1 (Subtype.ext h)) (s : 𝒞[K, σ]) s.2
        (y : 𝒞[K, σ]) (Subgroup.mem_subgroupOf.1 hy)
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact h⟩
    have hVs : Group.IsSolvable V := by
      have : IsMulCommutative V := ⟨⟨fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        exact hZab _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)⟩⟩
      infer_instance
    let tt : Subgroup.centralizer ({(x : 𝒞[K, σ])} : Set 𝒞[K, σ]) := ⟨t, hxt⟩
    have htV : tt ∈ V := Subgroup.mem_subgroupOf.2 ht
    obtain ⟨hTm, a, ha, hk⟩ := hperx x hx1 hne V hVn hVs tt htV
    rw [d4QPsi_apply] at hTm ha
    refine ⟨a, ha, ?_, hk⟩
    rw [hT] at hTm
    obtain ⟨a', ha', haφ⟩ := hTm
    have : a' = a := rootDiagUnit_injective (haφ.trans ha)
    exact this ▸ ha'
  intro t ht
  obtain ⟨a₁, h₁, ha₁F, k₁⟩ := hpsi q₁ hq₁1 ⟨_, ⟨IsRoot.basis _, hc₁⟩⟩ t ht
  obtain ⟨a₂, h₂, -, k₂⟩ := hpsi q₂ hq₂1 ⟨_, ⟨IsRoot.basis _, hc₂⟩⟩ t ht
  have hχ0 : rootChar a₁ (Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1) = 1 :=
    k₁ _ ⟨IsRoot.basis _, hc₁⟩
  have hχ1 : rootChar a₁ (Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) 1) = 1 := by
    have : a₂ = a₁ := rootDiagUnit_injective (h₂.symm.trans h₁)
    rw [← this]
    exact k₂ _ ⟨IsRoot.basis _, hc₂⟩
  have ha1 : a₁ = 1 := by
    by_contra hne
    rcases d4T36_rootCharKernel_cases hε ha₁F hne with h | ⟨i, hi⟩
    · have : (Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 :
          Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel a₁ := ⟨IsRoot.basis _, hχ0⟩
      rw [h] at this
      exact this
    · have m0 : (Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) ∈
          trialitySigma i := by
        rw [← hi]
        exact ⟨IsRoot.basis _, hχ0⟩
      have m1 : (Pi.single (⟨1, by decide⟩ : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) ∈
          trialitySigma i := by
        rw [← hi]
        exact ⟨IsRoot.basis _, hχ1⟩
      exact hdiff i ⟨mem_trialitySigma.1 m0, mem_trialitySigma.1 m1⟩
  have h1 : g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * t * c⁻¹) * g0 = 1 := by
    rw [h₁, ha1, rootDiagUnit_one]
  have h2 : triEmb K σ (AlgebraicClosure K) (c * t * c⁻¹) =
      triEmb K σ (AlgebraicClosure K) 1 := by
    rw [map_one]
    calc triEmb K σ (AlgebraicClosure K) (c * t * c⁻¹)
        = g0 * (g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * t * c⁻¹) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have h3 := triEmb_injective h2
  calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
    _ = 1 := by rw [h3]; group

end CFSG.GH74.GLS.Stage2.Bender.Thm1
