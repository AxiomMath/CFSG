module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeS

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

theorem not_single_zero_three_mem_sigma (i : Fin 4) :
    ¬ (Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) ∈ trialitySigma i ∧
      Pi.single (⟨3, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) ∈ trialitySigma i) := by
  rw [mem_trialitySigma, mem_trialitySigma]
  revert i
  decide +kernel


theorem exists_two_singular_lines_threeSix_plane {ℓ f : ℕ} (K : Type) [Field K]
    (σ : K ≃+* K) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {g : ModGL TwistTag.D4.tag Ω} (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEcard : Nat.card E = 3 ^ 2) (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hc : E.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorsion K Ω σ Fr ε 3 g) :
    ∃ x₁ ∈ E, ∃ x₂ ∈ E, x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₂ ∉ Subgroup.zpowers x₁ ∧
      ∀ x ∈ ({x₁, x₂} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        ∃ a : Fin TwistTag.D4.tag.rank → Ωˣ,
          rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε ∧
          orderOf (rootDiagUnit TwistTag.D4.tag a) = 3 ∧
          (∃ i, survivingRoots a = trialitySigma i) ∧
          threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hinjι := threeSixEmb_injective K Ω σ
  have hTE : ∀ y ∈ E, ∃ a : Fin TwistTag.D4.tag.rank → Ωˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε 3 ∧
        threeSixEmb K Ω σ (c * y * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
    intro y hy
    have hxT : (MulAut.conj c).toMonoidHom y ∈ threeSixFixedTorsion K Ω σ Fr ε 3 g :=
      hc ⟨y, hy, rfl⟩
    obtain ⟨u, hu, hux⟩ := hxT
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu.1.1
    exact ⟨a, hu, hux.symm⟩
  choose β hβT hβ using fun q : E => hTE (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) q.2
  have hβmul : ∀ q q' : E, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := Ω)
    rw [rootDiagUnit_mul]
    have h1 : g * rootDiagUnit TwistTag.D4.tag (β (q * q')) * g⁻¹ =
        g * rootDiagUnit TwistTag.D4.tag (β q) * g⁻¹ *
          (g * rootDiagUnit TwistTag.D4.tag (β q') * g⁻¹) := by
      rw [← hβ, ← hβ, ← hβ, ← map_mul]
      congr 1
      change c * ((q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * q') * c⁻¹ = _
      group
    calc rootDiagUnit TwistTag.D4.tag (β (q * q'))
        = g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (β (q * q')) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (β q) * g⁻¹ *
          (g * rootDiagUnit TwistTag.D4.tag (β q') * g⁻¹)) * g := by rw [h1]
      _ = _ := by group
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := Ω)
    rw [rootDiagUnit_one]
    have h1 : g * rootDiagUnit TwistTag.D4.tag (β 1) * g⁻¹ = 1 := by
      rw [← hβ]
      have : c * ((1 : E) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹ = 1 := by
        change c * 1 * c⁻¹ = 1
        group
      rw [this, map_one]
    calc rootDiagUnit TwistTag.D4.tag (β 1)
        = g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (β 1) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag Ω) := rootDiagUnit_injective
  have hβ3 : ∀ q : E, β q ^ 3 = 1 := fun q => by
    apply hinj0
    rw [map_pow, map_one]
    exact (hβT q).2
  let B : E →* (Fin TwistTag.D4.tag.rank → Ωˣ) :=
    { toFun := β
      map_one' := hβone
      map_mul' := hβmul }
  have hker : ∀ j : Fin TwistTag.D4.tag.rank, ∃ q : E, q ≠ 1 ∧ β q j = 1 := by
    intro j
    let χ : E →* Ωˣ := (Pi.evalMonoidHom (fun _ : Fin TwistTag.D4.tag.rank => Ωˣ) j).comp B
    exact d4Q_exists_ne_one_ker_of_card_sq Nat.prime_three hEcard χ fun q => by
      exact congrFun (hβ3 q) j
  have hdata : ∀ (j : Fin TwistTag.D4.tag.rank) (q : E), q ≠ 1 → β q j = 1 →
      rootDiagUnit TwistTag.D4.tag (β q) ∈ threeSixTorus Ω Fr ε ∧
        orderOf (rootDiagUnit TwistTag.D4.tag (β q)) = 3 ∧
        ∃ i, survivingRoots (β q) = trialitySigma i ∧ Pi.single j 1 ∈ trialitySigma i := by
    intro j q hq1 hq0
    have hne1 : rootDiagUnit TwistTag.D4.tag (β q) ≠ 1 := by
      intro h1
      have h2 : threeSixEmb K Ω σ (c * (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) =
          threeSixEmb K Ω σ 1 := by
        rw [hβ, h1, map_one]
        group
      have h3 := hinjι h2
      have h4 : (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 1 := by
        calc (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
            = c⁻¹ * (c * (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) * c := by
              group
          _ = 1 := by rw [h3]; group
      exact hq1 (Subtype.ext h4)
    have hb1 : β q ≠ 1 := fun h => hne1 (by rw [h, rootDiagUnit_one])
    have hord : orderOf (rootDiagUnit TwistTag.D4.tag (β q)) = 3 :=
      orderOf_eq_prime (hβT q).2 hne1
    have hfix := (rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε (β q)).1 (hβT q).1
    have hmem : Pi.single j 1 ∈ survivingRoots (β q) := by
      refine ⟨IsRoot.basis _, ?_⟩
      rw [CTTorus.rootChar_single]
      exact hq0
    obtain ⟨i, hi⟩ := survivingRoots_eq_sigma_of_nonempty hε hfix hb1 ⟨_, hmem⟩
    exact ⟨(hβT q).1, hord, i, hi, hi ▸ hmem⟩
  obtain ⟨q₀, hq₀1, hq₀⟩ := hker ⟨0, by decide⟩
  obtain ⟨q₃, hq₃1, hq₃⟩ := hker ⟨3, by decide⟩
  obtain ⟨hT₀, hord₀, i₀, hi₀, -⟩ := hdata _ q₀ hq₀1 hq₀
  obtain ⟨hT₃, hord₃, i₃, hi₃, hm₃⟩ := hdata _ q₃ hq₃1 hq₃
  have hne : ∀ q : E, q ≠ 1 → (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ 1 :=
    fun q hq h => hq (Subtype.ext h)
  refine ⟨q₀, q₀.2, q₃, q₃.2, hne q₀ hq₀1, hne q₃ hq₃1, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hk' : q₀ ^ k = q₃ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
    have h0 : β q₃ ⟨0, by decide⟩ = 1 := by
      let χ0 : E →* Ωˣ :=
        (Pi.evalMonoidHom (fun _ : Fin TwistTag.D4.tag.rank => Ωˣ) ⟨0, by decide⟩).comp B
      have e1 : β q₃ ⟨0, by decide⟩ = χ0 q₃ := rfl
      rw [e1, ← hk', map_zpow]
      change (β q₀ ⟨0, by decide⟩) ^ k = 1
      rw [hq₀, one_zpow]
    have hm0 : Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) ∈
        trialitySigma i₃ := by
      rw [← hi₃]
      refine ⟨IsRoot.basis _, ?_⟩
      rw [CTTorus.rootChar_single]
      exact h0
    exact not_single_zero_three_mem_sigma i₃ ⟨hm0, hm₃⟩
  · rintro x (rfl | rfl)
    · exact ⟨β q₀, hT₀, hord₀, ⟨i₀, hi₀⟩, hβ q₀⟩
    · exact ⟨β q₃, hT₃, hord₃, ⟨i₃, hi₃⟩, hβ q₃⟩

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
