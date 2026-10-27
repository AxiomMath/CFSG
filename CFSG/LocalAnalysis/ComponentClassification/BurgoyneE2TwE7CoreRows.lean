module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Inner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Reduce
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Core
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Core

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem pPrimeCore_eq_bot_of_mulEquiv {G A : Type*} [Group G] [Group A] {X : Subgroup A}
    (e : G ≃* X)
    (h : ∀ N : Subgroup A, N ≤ X → (∀ y ∈ X, ∀ n ∈ N, y * n * y⁻¹ ∈ N) → Odd (Nat.card N) →
      N = ⊥) :
    pPrimeCore 2 G = ⊥ := by
  have hX : pPrimeCore 2 X = ⊥ := by
    rw [pPrimeCore_eq_bot_iff]
    intro N hN hcop
    have h1 := h (N.map X.subtype) (Subgroup.map_subtype_le N) (fun y hy n hn => by
      obtain ⟨n', hn', rfl⟩ := hn
      exact ⟨⟨y, hy⟩ * n' * ⟨y, hy⟩⁻¹, hN.conj_mem n' hn' ⟨y, hy⟩, rfl⟩) (by
      rw [← Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv]
      exact Nat.coprime_two_left.1 hcop)
    exact (Subgroup.map_eq_bot_iff_of_injective N X.subtype_injective).1 h1
  have h1 := pPrimeCore_map_iso 2 e
  rw [hX] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1


section Fixed

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] (L : Type) [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L p]

abbrev embE7 : adjointGroup .E7 K →* ModGL .E7 L :=
  (baseChangeGL (algebraMap K L)).comp (adjointGroup .E7 K).subtype

theorem map_adjointGroup_eq_commutator (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) =
      ⁅fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1),
        fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1)⁆ := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  set Fr := iterateFrobenius L p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr_def, iterateFrobenius_def, hK]
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hodd L Fr hFr
  have hF1 : frobTwistGL .E7 L p f 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  rw [hF1, ← hder]

theorem map_fixedSubgroup_eq_twCent (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ) :
    (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)).map (embE7 L) =
      twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  have hx : ∀ h : adjointGroup .E7 K,
      liftElt (algebraMap K L) (g : ModGL .E7 K) a * embE7 L h *
          (liftElt (algebraMap K L) (g : ModGL .E7 K) a)⁻¹ =
        embE7 L ((MulAut.conj g * rootDiagAut .E7 K a) h) := fun h =>
    liftElt_conj (algebraMap K L) g a h
  have h1 := map_fixedSubgroup_eq (embE7 L) (hinj.comp Subtype.val_injective)
    (MulAut.conj g * rootDiagAut .E7 K a) _ hx
  have h2 : (embE7 (K := K) L).range = (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) :=
    by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, h2, map_adjointGroup_eq_commutator L hp2 hK]

theorem pPrimeCore_eq_bot_of_twCent (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ)
    (h : ∀ N : Subgroup (ModGL .E7 L),
      N ≤ twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a) →
      (∀ y ∈ twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a), ∀ n ∈ N,
        y * n * y⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥) :
    pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) = ⊥ := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  have he := ((fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)).equivMapOfInjective
    (embE7 L) (hinj.comp Subtype.val_injective)).trans
      (MulEquiv.subgroupCongr (map_fixedSubgroup_eq_twCent L hp2 hK g a))
  exact pPrimeCore_eq_bot_of_mulEquiv he h

end Fixed

section Rows

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem four_mem_simpleRootsJ {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) [Subsingleton (KernelComponent D.χ)]
    {m : ℕ} (hm : m = 2 ∨ m = 3) (hχ : D.χ = signMaskChar .E7 m) :
    Pi.single (e7Node 4) 1 ∈ D.simpleRootsJ := by
  rw [simpleRootsJ_eq_simpleUnion, hχ]
  rcases hm with rfl | rfl
  · rw [simpleUnion_e7_two]
    exact ⟨3, by funext i; fin_cases i <;> rfl⟩
  · rw [simpleUnion_e7_three]
    exact ⟨3, by funext i; fin_cases i <;> rfl⟩

theorem burgCoreFor_twisted_of_core [CharP K p] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f)
    {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hα : orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2)
    (hns : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
      ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
        rootDiagAut .E7 K (signMaskTuple .E7 K m))
    (hcore : pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) = ⊥) :
    BurgCoreFor (MulAut.conj g * rootDiagAut .E7 K a) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  obtain ⟨-, -, r, hr, hm, g₁, hg₁G, hconj, hcoc⟩ := exists_twisted_reduction hp2 hf hK L hα hns
  obtain ⟨D, -, u, -, hDe, hDχ, hDθ, hsub, -, -, hCY, -⟩ := exists_twisted_layer hp2 hf hk hr
    (e7Word2_1_mem_omegaWords hr hm) e7Word2_1_ne_nil hg₁G hconj hcoc
  have hΔ := four_mem_simpleRootsJ D hm hDχ
  have hfixC : ∀ w ∈ D.orbitGroup, g₁⁻¹ * (u * w * u⁻¹) * g₁ ∈
      twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a) := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hCY ⟨w, hw, rfl⟩
    have e : g₁⁻¹ * (u * w * u⁻¹) * g₁ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyw
      rw [← hyw]
      group
    rw [e]
    exact hy
  have hH : ∀ w ∈ D.orbitGroup, g₁⁻¹ * (u * w * u⁻¹) * g₁ ∈
      (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := fun w hw => by
    rw [map_adjointGroup_eq_commutator L hp2 hK]
    exact (Subgroup.mem_inf.1 (hfixC w hw)).1
  refine burgCoreFor_of_inner (center_adjointGroup_eq_bot_field .E7 K) hcore
    fun β hβ _ hfix => mem_inner_of_odd_fix_orbitGroup hK D hDe hDθ hΔ hH hβ fun t ⟨w, hw, ht⟩ => ?_
  have htm : embE7 L t ∈ (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)).map (embE7 L) := by
    rw [map_fixedSubgroup_eq_twCent L hp2 hK]
    change baseChangeGL (algebraMap K L) (t : ModGL .E7 K) ∈ _
    rw [ht]
    exact hfixC w hw
  obtain ⟨t', ht', htt⟩ := htm
  have : t' = t := (hinj.comp Subtype.val_injective) htt
  subst this
  exact hfix t' ht'

theorem twisted_core_or_mask_three [CharP K p] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hα : orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2)
    (hns : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
      ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
        rootDiagAut .E7 K (signMaskTuple .E7 K m)) :
    pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) = ⊥ ∨
      (5 ≤ Nat.card K ∧ ∃ r ∈ e7SignDiagramReps, r.mask = 3 ∧ ∃ g₁ ∈ adjointGroup .E7 L,
        g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹ =
          rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) ∧
        g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1) := by
  classical
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp : p.Prime := Fact.out
  obtain ⟨-, -, r, hr, hm, g₁, hg₁G, hconj, hcoc⟩ := exists_twisted_reduction hp2 hf hK L hα hns
  rcases hm with h2 | h3
  · exact Or.inl (pPrimeCore_eq_bot_of_twCent L hp2 hK g a fun N hN hNn hodd =>
      twisted_two_oddNormal_eq_bot hp2 hf hk hr h2 hg₁G hconj hcoc N hN hNn hodd)
  · by_cases hq3 : Nat.card K = 3
    · refine Or.inl (pPrimeCore_eq_bot_of_twCent L hp2 hK g a fun N hN hNn hodd => ?_)
      have hq3' : p ^ f = 3 := by rw [← hK]; exact hq3
      exact (CFSG.ClassicalInvolution.Q3.e7_twisted_core hp2 hf hq3' hk
        (finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)) hr
        (e7Word2_1_mem_omegaWords hr (Or.inr h3)) e7Word2_1_ne_nil hg₁G hconj hcoc).1
          N hN hNn hodd
    · refine Or.inr ⟨?_, r, hr, h3, g₁, hg₁G, hconj, hcoc⟩
      have h3p : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h hp2
        · have := hp.two_le
          obtain ⟨m, hm⟩ := h
          omega
      have hge : 3 ≤ Nat.card K := by
        rw [hK]
        calc 3 ≤ p := h3p
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨m, hm⟩ := hodd
      omega

end Rows

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
