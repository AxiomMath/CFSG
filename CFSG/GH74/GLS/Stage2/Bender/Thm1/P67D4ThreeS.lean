module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSing
public import CFSG.RankThree.PartOne.KGD.D4QPlaneGen
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem survivingRoots_eq_sigma_of_nonempty {L : Type} [Field L] {q : ℕ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hfix : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q)
    (ha1 : a ≠ 1) (hne : (survivingRoots a).Nonempty) :
    ∃ i, survivingRoots a = trialitySigma i := by
  have hroot : ∀ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α →
      ∃ j, α ∈ trialitySigma j := by
    intro α hα
    have h : α ∈ ⋃ j, trialitySigma j := by
      rw [← isRoot_eq_iUnion_trialitySigma]
      exact hα
    exact Set.mem_iUnion.1 h
  obtain ⟨α, hα, hα1⟩ := hne
  obtain ⟨j, hj⟩ := hroot α hα
  refine ⟨j, ?_⟩
  ext β
  constructor
  · rintro ⟨hβ, hβ1⟩
    obtain ⟨k, hk⟩ := hroot β hβ
    by_contra hnj
    have hjk : j ≠ k := fun h => hnj (h ▸ hk)
    exact ha1 (eq_one_of_rootChar_eq_one_of_ne hε hfix hjk hj hk hα1 hβ1)
  · intro hβ
    exact ⟨(isRootComponent_trialitySigma j).isRoot β hβ,
      rootChar_eq_one_of_mem_trialitySigma hε hfix hj hα1 hβ⟩


theorem exists_singularData_of_threeSix_plane {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hq2 : 2 < ℓ ^ f) (hℓ3 : ℓ ≠ 3) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL TwistTag.D4.tag Ω}
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hEcard : Nat.card E = 3 ^ 2)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hc : E.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorsion K Ω σ Fr ε 3 g) :
    ∃ x ∈ E, x ≠ 1 ∧ SingularCentralizerData σ (ℓ ^ f) x := by
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
  obtain ⟨q, hq1, hq0⟩ : ∃ q : E, q ≠ 1 ∧ β q ⟨0, by decide⟩ = 1 := by
    let χ : E →* Ωˣ :=
      { toFun := fun q => β q ⟨0, by decide⟩
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    exact d4Q_exists_ne_one_ker_of_card_sq Nat.prime_three hEcard χ fun q => by
      exact congrFun (hβ3 q) ⟨0, by decide⟩
  have hne1 : rootDiagUnit TwistTag.D4.tag (β q) ≠ 1 := by
    intro h1
    have h2 : threeSixEmb K Ω σ (c * (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) =
        threeSixEmb K Ω σ 1 := by
      rw [hβ, h1, map_one]
      group
    have h3 := hinjι h2
    have h4 : (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 1 := by
      calc (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
          = c⁻¹ * (c * (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) * c := by group
        _ = 1 := by rw [h3]; group
    exact hq1 (Subtype.ext h4)
  have hb1 : β q ≠ 1 := fun h => hne1 (by rw [h, rootDiagUnit_one])
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag (β q)) = 3 :=
    orderOf_eq_prime (hβT q).2 hne1
  have hfix := (rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε (β q)).1 (hβT q).1
  have hsurv : (survivingRoots (β q)).Nonempty := by
    refine ⟨Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1, IsRoot.basis _, ?_⟩
    rw [CTTorus.rootChar_single]
    exact hq0
  obtain ⟨i, hi⟩ := survivingRoots_eq_sigma_of_nonempty hε hfix hb1 hsurv
  refine ⟨q, q.2, fun h => hq1 (Subtype.ext h), ?_⟩
  exact singularCentralizerData_of_conj c (singularCentralizerData_threeSix_gen hℓ hf K hK σ hσ Ω
    Fr hFr hε hd hgG hFg Nat.prime_three (by norm_num) hℓ3 hq2 (β q) (hβT q).1 hord ⟨i, hi⟩ _
    (hβ q))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
