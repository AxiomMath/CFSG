module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaExc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOuter

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  refine ⟨q - 1, ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega


namespace TwE6T1

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {L : Type} [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L p]

theorem oddCoreExp_t1 (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀G : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀F : frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₀ = g₀)
    (hg₀t : g₀ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    OddCoreExp (MulAut.conj t) (p ^ f + 1) := by
  classical
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  set d := rootDiagUnit TwistTag.E6.tag
    (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) with hd
  have hg₀R : g₀ ∈ R := mem_fixedPointsIn.2 ⟨hg₀G, hg₀F⟩
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hιR : ∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ι (s : ModGL TwistTag.E6.tag K) ∈ R := fun s => hRR ((t1_preimage hp2 hf hK σ hσ
        (one_mem R)).2 ⟨s, by rw [one_mul, inv_one, mul_one]⟩)
  set Ψ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g₀).toMonoidHom.comp
      (ι.comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj g₀).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hΨapp : ∀ s, Ψ s = g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ := fun s => rfl
  have hΨt : Ψ t = d := hg₀t
  have hΨR : ∀ s, Ψ s ∈ R := fun s => mul_mem (mul_mem hg₀R (hιR s)) (inv_mem hg₀R)
  have hcomm : ∀ s, Ψ s * d = d * Ψ s ↔ s * t = t * s := fun s => by
    rw [← hΨt, ← map_mul, ← map_mul]
    exact hΨinj.eq_iff
  have hfixt : ∀ s, s ∈ fixedSubgroup (MulAut.conj t) ↔ s * t = t * s := fun s => by
    change t * s * t⁻¹ = s ↔ _
    constructor
    · intro h
      calc s * t = t * s * t⁻¹ * t := by rw [h]
        _ = t * s := by group
    · intro h
      rw [← h]
      group
  obtain ⟨CA, hqCA, hCAH, hCAn, hCAind⟩ := exists_t1_layer hp2 hf hK σ hσ hg₀R
  have hCAΨ : CA ≤ Ψ.range := fun y hy => by
    obtain ⟨s, hs⟩ := (t1_preimage hp2 hf hK σ hσ hg₀R).1 (Subgroup.mem_inf.1 (hCAH hy)).1
    exact ⟨s, hs⟩
  let eJ : CA.comap Ψ ≃* CA := ((CA.comap Ψ).equivMapOfInjective Ψ hΨinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hCAΨ))
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  have hJn : ∀ g ∈ fixedSubgroup (MulAut.conj t), ∀ j ∈ CA.comap Ψ, g * j * g⁻¹ ∈ CA.comap Ψ := by
    intro g hg j hj
    have hj' : Ψ j ∈ CA := hj
    have hgd : Ψ g ∈ R ⊓ Subgroup.centralizer {d} :=
      Subgroup.mem_inf.2 ⟨hΨR g, Subgroup.mem_centralizer_singleton_iff.2
        ((hcomm g).2 ((hfixt g).1 hg))⟩
    change Ψ (g * j * g⁻¹) ∈ CA
    rw [map_mul, map_mul, map_inv]
    exact hCAn _ hgd _ hj'
  refine oddCoreExp_of_fix (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (Q := CA.comap Ψ) (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hqCA)
    (fun s hs => ?_) (fun g hg => ?_) fun β hβ _ hβJ => ?_
  ·
    have hs' : Ψ s ∈ CA := hs
    exact (hfixt s).2 ((hcomm s).1
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hCAH hs')).2))
  · rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · exact hJn g hg j
    · intro hj
      have h := hJn g⁻¹ (inv_mem hg) _ hj
      rwa [show g⁻¹ * (g * j * g⁻¹) * g⁻¹⁻¹ = j by group] at h
  ·
    obtain ⟨c, h0, h1, h3', h5, h24, hcR, hcβ⟩ := hCAind β hβ fun s hs => hβJ s hs
    have hcβ' : ∀ s, Ψ (β s) = rootDiagUnit TwistTag.E6.tag c * Ψ s *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ := fun s => by
      rw [hΨapp, hΨapp]
      exact hcβ s
    have hc2 : c (t1Node 2) ^ (p ^ f + 1) = 1 := pow_succ_eq_one_of_mem_t1R h24 hcR
    have hc4 : c (t1Node 4) ^ (p ^ f + 1) = 1 := by
      rw [eq_inv_of_mul_eq_one_right h24, inv_pow, hc2, inv_one]
    have e1 : ∀ x : Lˣ, x = 1 → x ^ (p ^ f + 1) = 1 := fun x hx => by rw [hx, one_pow]
    have hc : c ^ (p ^ f + 1) = 1 := by
      funext i
      obtain ⟨j, rfl⟩ : ∃ j : Fin 6, t1Node j = i := ⟨i, rfl⟩
      rw [Pi.pow_apply, Pi.one_apply]
      fin_cases j
      · exact e1 _ h0
      · exact e1 _ h1
      · exact hc2
      · exact e1 _ h3'
      · exact hc4
      · exact e1 _ h5
    have hdk : rootDiagUnit TwistTag.E6.tag c ^ (p ^ f + 1) = 1 := by
      rw [rootDiagUnit_pow, hc, rootDiagUnit_one]
    exact MulEquiv.ext fun s => hΨinj (by
      rw [map_pow_apply_eq_conj hcβ' (p ^ f + 1) s, hdk, one_mul, inv_one, mul_one,
        MulAut.one_apply])

end TwE6T1

end CFSG.ComponentClassification.Burgoyne.E2

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ClassicalInvolution
open scoped commutatorElement Pointwise
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.OddE6AllInvolution (isAlgebraic_zmod_algebraicClosure)


theorem burgRowExp_twistedE6_nonGraph (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : orderOf α = 2)
    (hF4 : ∀ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ ≠ fieldActor (t := TwistTag.E6) σ σ)
    (hc : ∀ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ ≠ twE6SignAut σ) :
    BurgCoreFor α ∨ OddCoreExp α (p ^ f + 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  by_cases hin : α ∉ twistedE6Inn K σ
  · obtain ⟨ψ, hψ | hψ⟩ := twE6_outer_involution_conj hp hp2 hf K hK σ hσ α hα2 hin
    · exact absurd hψ (hF4 ψ)
    · exact absurd hψ (hc ψ)
  rw [not_not] at hin
  obtain ⟨t, rfl⟩ := hin
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have ht2 : t ^ 2 = 1 := conj_injective hZ (by rw [map_pow, hα2, map_one])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hα
    exact absurd hα (by decide)
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK'
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_algebraicClosure K p
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hder, -⟩ := twE6_lift_facts (p := p) (k := AlgebraicClosure K) hf hodd K hK σ hσ
  have hxH : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) ∈
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure K))),
        fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure K)))⁆ := by
    rw [hder]
    exact ⟨t, t.2, rfl⟩
  have hxR := Subgroup.commutator_le_of_le le_rfl le_rfl hxH
  have hx2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) ^ 2
      = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ht2, Subgroup.coe_one, map_one]
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, -, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    Q3.exc3_e6_datum_conj p hp2 hk hf hxR hx2
  have hrmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hrmask with h0 | h20 | h2
  ·
    exfalso
    apply ht1
    have e1 : rootDiagUnit TwistTag.E6.tag
        (signCharTuple (k := AlgebraicClosure K) (signMaskChar TwistTag.E6.tag r.mask)) = 1 := by
      have e0 : signCharTuple (k := AlgebraicClosure K) (signMaskChar TwistTag.E6.tag 0) = 1 := by
        funext j
        rw [signCharTuple, signMaskChar_single]
        simp
      rw [h0, e0]
      exact rootDiagUnit_one
    rw [e1] at hg₁x
    refine Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) ?_)
    rw [Subgroup.coe_one, map_one]
    calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) =
        g₁⁻¹ * (g₁ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (t : ModGL TwistTag.E6.tag K) * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [hg₁x]; group
  ·
    refine Or.inr (TwE6T1.oddCoreExp_t1 (L := AlgebraicClosure K) hp2 hf hK σ hσ t hg₁G hFg₁ ?_)
    rw [hg₁x, h20]
  ·
    have hwG : rootDiagUnit TwistTag.E6.tag s * g₁ ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      mul_mem (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag _ s).1 hg₁G
    exact Or.inl (burgCoreFor_conj_of_mask_two hp2 hf K hK σ hσ hk t ht1 ht2 D h _ hwG hhT
      (by rw [hDχ, h2]) hDe hDθ hDF hcent)

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem burgRowExp_twistedE6 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : orderOf α = 2) : BurgCoreFor α ∨ OddCoreExp α (p ^ f + 1) := by
  by_cases hc : ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ = fieldActor (t := TwistTag.E6) σ σ
  · obtain ⟨ψ, hψ⟩ := hc
    have hc := (burgCoreFor_twistedE6_graph hp hp2 hf hK σ hσ).conj ψ⁻¹
    rw [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at hc
    exact Or.inl hc
  push Not at hc
  by_cases hc' : ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ = twE6SignAut σ
  · obtain ⟨ψ, hψ⟩ := hc'
    have hc' := (burgCoreFor_twistedE6_signedGraph hp hp2 hf hK σ hσ).conj ψ⁻¹
    rw [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at hc'
    exact Or.inl hc'
  push Not at hc'
  exact TwE6In.burgRowExp_twistedE6_nonGraph p f hp hp2 hf K hK σ hσ α hα hc hc'

theorem pow_eq_one_of_mem_oddCentralizerCore_twistedE6 (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .twistedE6 n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨hp, hf, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf hU
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
    have h1 := pow_eq_one_of_rows hsimple hnab (exceptional_fixed_center_trivial TwistTag.E6 K σ)
      e (burgRowExp_twistedE6 p f hp hp2 hf K hK σ hσ) ht hy
    obtain ⟨c, hc⟩ := card_add_one_dvd_sq_sub_one (p ^ f)
    rw [hc, pow_mul, h1, one_pow]
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
