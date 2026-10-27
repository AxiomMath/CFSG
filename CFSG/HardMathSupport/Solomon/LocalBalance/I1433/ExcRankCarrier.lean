module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankSL2
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local
import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.CentralCover
  CFSG.Assembly.RankThreeEven TauCeti
open scoped MatrixGroups commutatorElement

theorem e6_commuting_SL2
    (d : TypeE6LieIndex) :
    ∃ φ : Fin 4 → SL(2, d.1.fixedField) →* FixedPointCandidate d.steinberg,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), φ i A * φ j B = φ j B * φ i A := by
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e6Data_valid d.1.fixedField
    neighbour_cartan_E6 ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1],
      ![1, 2, 2, 3, 2, 1]] (by decide +kernel)
  refine ⟨fun i => (toQuot (e6Embed d) hC).comp (ρ i),
    fun i => toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i), fun i j hij A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem e7_commuting_SL2
    (d : TypeE7LieIndex) :
    ∃ φ : Fin 5 → SL(2, d.1.fixedField) →* FixedPointCandidate d.steinberg,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), φ i A * φ j B = φ j B * φ i A := by
  have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
    neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1]]
    (by decide +kernel)
  refine ⟨fun i => (toQuot (e7Embed d) hC).comp (ρ i),
    fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i), fun i j hij A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem twistedE6_commuting_SL2
    (d : TypeTwistedE6LieIndex) :
    ∃ φ : Fin 4 → SL(2, d.1.fixedField) →* FixedPointCandidate d.steinberg,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), φ i A * φ j B = φ j B * φ i A := by
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  refine ⟨fun i => (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i),
    fun i => toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA, fun i i' hii A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul,
    te6SL2_commute (quadFrob d) (quadIncl d) hj hii A B]

section Geck

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.TauCetiBridge

theorem finite_fixedField (d : ValidLieTypeIndex) : Finite d.fixedField := inferInstance

theorem e8_commuting_SL2
    (q : PrimePower)
    (hv : (LieTypeIndex.E8 q).Valid) :
    ∃ φ : Fin 5 → SL(2, ValidLieTypeIndex.fixedField ⟨.E8 q, hv⟩) →*
        (CFSGIndex.lie ⟨.E8 q, hv⟩).Group,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, ValidLieTypeIndex.fixedField ⟨.E8 q, hv⟩),
        φ i A * φ j B = φ j B * φ i A := by
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  haveI := finite_fixedField d
  change ∃ φ : Fin 5 → SL(2, d.fixedField) →* FixedPointCandidate d.geckFrobenius,
    (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, d.fixedField), φ i A * φ j B = φ j B * φ i A
  have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
    single_edge_perfect .E8 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
    ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2]] (by decide +kernel)
  have hinj := toQuot_injective (geckEmbed_injective d geckMatchE8) hC center_adjointGroup_eq_bot
  refine ⟨fun i => (toQuot (geckEmbed d geckMatchE8) hC).comp (ι i),
    fun i => hinj.comp (hι i), fun i j hij A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem f4_commuting_SL2
    (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) :
    ∃ φ : Fin 4 → SL(2, ValidLieTypeIndex.fixedField ⟨.F4 q, hv⟩) →*
        (CFSGIndex.lie ⟨.F4 q, hv⟩).Group,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, ValidLieTypeIndex.fixedField ⟨.F4 q, hv⟩),
        φ i A * φ j B = φ j B * φ i A := by
  set d : ValidLieTypeIndex := ⟨.F4 q, hv⟩ with hd
  haveI := finite_fixedField d
  change ∃ φ : Fin 4 → SL(2, d.fixedField) →* FixedPointCandidate d.geckFrobenius,
    (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, d.fixedField), φ i A * φ j B = φ j B * φ i A
  have hC : commutator ↥(adjointGroup .F4 d.fixedField) = ⊤ :=
    single_edge_perfect .F4 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .F4
    ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]] (by decide +kernel)
  have hinj := toQuot_injective (geckEmbed_injective d geckMatchF4) hC center_adjointGroup_eq_bot
  refine ⟨fun i => (toQuot (geckEmbed d geckMatchF4) hC).comp (ι i),
    fun i => hinj.comp (hι i), fun i j hij A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

end Geck

open CFSG.LieType.Chevalley.RootOps in
theorem e6_liftDatum_even
    (d : TypeE6LieIndex) (h2 : ringChar d.1.fixedField = 2) :
    LiftDatum (FixedPointCandidate d.steinberg) 3 := by
  obtain ⟨hr1, hr2, hso, hmod, hplus, hminus, h13⟩ := e6Two_check
  have hroot : ∀ {v}, isRootB .E6 v = true → IsRoot .E6 v := fun h => isRootB_iff.1 h
  have hnot : ∀ {v : Fin (Tag.rank .E6) → ℤ}, isRootB .E6 v = false → ¬ IsRoot .E6 v :=
    fun hv hr => by
      rw [← isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  have : CharP d.1.fixedField 2 := ringChar.of_eq h2
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  set θ := toQuot (e6Embed d) hC with hθ
  choose ρ hinj hmem hcen using fun i =>
    exists_rootSL2' e6Data_valid d.1.fixedField neighbour_cartan_E6 (hroot (hr1 i))
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hij A B
    obtain ⟨h1, h2', h3, h4⟩ := hso i j hij
    exact (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer e6Data_valid _ (hroot (hr1 i))
      (hroot (hr1 j)) h1 h2' (hnot h3) (hnot h4) (hmem i A)) (ρ j B) (hmem j B)).symm
  have hθρ : ∀ i, Function.Injective (θ.comp (ρ i)) := fun i =>
    toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i)
  set PC : Subgroup ↥(e6Data_valid.minGroup d.1.fixedField) :=
    ⨆ j, e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j) with hPC
  have hP2 : IsPGroup 2 PC := by
    refine isPGroup_iSup_rootGroup e6Data_valid _ e6ModuleRoots fun i j x hx y hy => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hx
    obtain ⟨e, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hy
    by_cases hij : i = j
    · subst hij
      rw [← e6Data_valid.xm_add, ← e6Data_valid.xm_add, add_comm]
    · exact commute_xm e6Data_valid _ (hroot (hr2 i)) (hroot (hr2 j)) (hmod i j hij).1
        (hnot (hmod i j hij).2) c e
  have hnorm : ∀ i A, ρ i A ∈ Subgroup.normalizer (PC : Set _) := by
    intro i A
    refine (sup_le ?_ ?_ : _ ≤ Subgroup.normalizer (PC : Set _)) (hmem i A)
    · exact rootGroup_le_normalizer_iSup e6Data_valid _ (hroot (hr1 i)) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hplus i j).1, fun h => (hplus i j).2 (isRootB_iff.2 h)⟩
    · exact rootGroup_le_normalizer_iSup e6Data_valid _
        (CFSG.LieType.Chevalley.IsRoot.neg (hroot (hr1 i))) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hminus i j).1, fun h => (hminus i j).2
          (isRootB_iff.2 h)⟩
  have hnc : e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1 ∉ Subgroup.center _ := by
    intro hc
    obtain ⟨σ, hσ, h⟩ := (e6Data_valid.commutator_xm d.1.fixedField (hroot (hr1 0))
      (hroot (hr2 0)) (hplus 0 0).1).1 (hroot h13)
    have h1 := h 1 1
    have h1' : ⁅e6Data_valid.xm d.1.fixedField (e6OrthoRoots 0) 1,
        e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1⁆ = 1 := by
      rw [commutatorElement_def, Subgroup.mem_center_iff.1 hc]
      group
    rw [h1', mul_one, mul_one] at h1
    have h0 := e6Data_valid.xm_injective d.1.fixedField (hroot h13)
      (h1.symm.trans (e6Data_valid.xm_zero _ _).symm)
    rcases hσ with rfl | rfl <;> simp at h0
  have hP : PC.map θ ≠ ⊥ := by
    intro hbot
    apply hnc
    refine mem_center_of_toQuot_eq_one (e6Embed_injective d) hC ?_
    have : θ (e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1) ∈ PC.map θ :=
      ⟨_, le_iSup (fun j => e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j)) 0
        (e6Data_valid.xm_mem_rootGroup _ _ _), rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  exact liftDatum_of_commuting_SL2_normalizing h2 (m := 3) (fun i => θ.comp (ρ i)) hθρ
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]) hP
    (hP2.map θ) (fun i A => Subgroup.le_normalizer_map θ ⟨_, hnorm i A, rfl⟩)

theorem e6_commuting_SL2'
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) :
    ∃ φ : Fin 4 → SL(2, ValidLieTypeIndex.fixedField ⟨.E6 q, hv⟩) →*
        (CFSGIndex.lie ⟨.E6 q, hv⟩).Group,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, ValidLieTypeIndex.fixedField ⟨.E6 q, hv⟩),
        φ i A * φ j B = φ j B * φ i A :=
  e6_commuting_SL2 ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩

theorem e7_commuting_SL2'
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) :
    ∃ φ : Fin 5 → SL(2, ValidLieTypeIndex.fixedField ⟨.E7 q, hv⟩) →*
        (CFSGIndex.lie ⟨.E7 q, hv⟩).Group,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, ValidLieTypeIndex.fixedField ⟨.E7 q, hv⟩),
        φ i A * φ j B = φ j B * φ i A :=
  e7_commuting_SL2 ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩

theorem twistedE6_commuting_SL2'
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ φ : Fin 4 → SL(2, ValidLieTypeIndex.fixedField ⟨.twistedE6 q, hv⟩) →*
        (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group,
      (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, ValidLieTypeIndex.fixedField ⟨.twistedE6 q, hv⟩),
        φ i A * φ j B = φ j B * φ i A :=
  twistedE6_commuting_SL2 ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩

theorem e6_liftDatum_even'
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (h2 : ringChar (ValidLieTypeIndex.fixedField ⟨.E6 q, hv⟩) = 2) :
    LiftDatum (CFSGIndex.lie ⟨.E6 q, hv⟩).Group 3 :=
  e6_liftDatum_even ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩ h2

private theorem quadFrob_eq_pow (d : TypeTwistedE6LieIndex) (c : quadField d) :
    quadFrob d c = c ^ d.1.fieldOrder :=
  Subtype.ext (by rw [coe_quadFrob, SubmonoidClass.coe_pow])

section TwistedTorus

open CFSG.LieType.Steinberg.TwistedE6

private theorem nm_conj_hm_self
    {k : Type*} [Field k]
    (a : Fin (Tag.rank .E6)) (t : kˣ) :
    e6Data_valid.nm k a * e6Data_valid.hm k a t * (e6Data_valid.nm k a)⁻¹ =
      e6Data_valid.hm k a t⁻¹ := by
  rw [e6Data_valid.nm_conj_hm, Tag.cartan_self, ← e6Data_valid.hm_mul]
  congr 1
  group

private theorem nm_conj_hm_orth
    {k : Type*} [Field k]
    {a b : Fin (Tag.rank .E6)} (hba : Tag.cartan .E6 b a = 0) (t : kˣ) :
    e6Data_valid.nm k a * e6Data_valid.hm k b t * (e6Data_valid.nm k a)⁻¹ =
      e6Data_valid.hm k b t := by
  rw [e6Data_valid.nm_conj_hm, hba, neg_zero, zpow_zero, e6Data_valid.hm_one, mul_one]

private theorem nHatE_three_conj_pair
    {k : Type*} [Field k]
    (t s : kˣ) :
    nHatE k (nf 3) * (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
        (nHatE k (nf 3))⁻¹ =
      (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s)⁻¹ := by
  have c05 : Tag.cartan .E6 (nd 0) (nd 5) = 0 := by decide
  have c50 : Tag.cartan .E6 (nd 5) (nd 0) = 0 := by decide
  have e5 : e6Data_valid.nm k (nd 5) * (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
      (e6Data_valid.nm k (nd 5))⁻¹ = e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s⁻¹ := by
    rw [show ∀ a b c : e6Data_valid.minGroup k, a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹)
      from fun a b c => by group, nm_conj_hm_orth c05, nm_conj_hm_self]
  have e0 : e6Data_valid.nm k (nd 0) *
      (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s⁻¹) *
      (e6Data_valid.nm k (nd 0))⁻¹ =
        e6Data_valid.hm k (nd 0) t⁻¹ * e6Data_valid.hm k (nd 5) s⁻¹ := by
    rw [show ∀ a b c : e6Data_valid.minGroup k, a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹)
      from fun a b c => by group, nm_conj_hm_self, nm_conj_hm_orth c50]
  rw [nHatE_three]
  calc e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) *
        (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
        (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹
      = e6Data_valid.nm k (nd 0) * (e6Data_valid.nm k (nd 5) *
          (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
          (e6Data_valid.nm k (nd 5))⁻¹) * (e6Data_valid.nm k (nd 0))⁻¹ := by group
    _ = e6Data_valid.hm k (nd 0) t⁻¹ * e6Data_valid.hm k (nd 5) s⁻¹ := by rw [e5, e0]
    _ = (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s)⁻¹ := by
      have hinv : ∀ (a : Fin (Tag.rank .E6)) (u : kˣ),
          e6Data_valid.hm k a u⁻¹ = (e6Data_valid.hm k a u)⁻¹ := fun a u =>
        map_inv (e6Data_valid.hHom k a) u
      rw [mul_inv_rev, hinv, hinv]
      exact (hm_commute (k := k) (nd 0) (nd 5) t s).inv_inv.eq

private theorem nHat_three_conj_te6Torus
    {k : Type*} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (t : kˣ) :
    nHat θ (nf 3) * te6Torus θ hθ t * (nHat θ (nf 3))⁻¹ = (te6Torus θ hθ t)⁻¹ := by
  apply Subtype.ext
  change nHatE k (nf 3) * hPairE θ (nd 0) (nd 5) t * (nHatE k (nf 3))⁻¹ =
    (hPairE θ (nd 0) (nd 5) t)⁻¹
  exact nHatE_three_conj_pair t (Units.map (θ : k →* k) t)

variable {k : Type*} [Field k] (θ : k →+* k) {F : Type*} [Field F] (j : F →+* k)
  (hj : ∀ x, θ (j x) = j x) (hθ : ∀ c, θ (θ c) = c)

include hθ in
private theorem liftDatum_te6
    {G : Type} [Group G]
    (Θ : fixedGroup k θ →* G) (hΘ : ∀ g, Θ g = 1 → g ∈ Subgroup.center (fixedGroup k θ))
    (hinj : ∀ i, Function.Injective (Θ.comp (te6SL2 θ j hj i))) (hF : ringChar F = 2)
    {t : kˣ} (htt : t * Units.map (θ : k →* k) t = 1) (ht3 : t ^ 3 = 1)
    (ht2 : ((t : k)) ^ 2 ≠ 1) : LiftDatum G 3 := by
  set φ : Fin 4 → SL(2, F) →* G := fun i => Θ.comp (te6SL2 θ j hj i) with hφ
  have hcomm : ∀ i i', i ≠ i' → ∀ A B : SL(2, F), φ i A * φ i' B = φ i' B * φ i A := by
    intro i i' hii A B
    simp only [hφ, MonoidHom.comp_apply, ← map_mul, te6SL2_commute θ j hj hii A B]
  set s := Θ (te6Torus θ hθ t) with hs
  have hsφ : ∀ i A, Commute (φ i A) s := fun i A =>
    (show Commute (te6Torus θ hθ t) (te6SL2 θ j hj i A) from
      te6Torus_commute θ j hj hθ htt i A).symm.map Θ
  have hne : ∀ i : Fin 3, i.castSucc ≠ (3 : Fin 4) := fun i h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hτ3 : s ^ 3 = 1 := by rw [hs, ← map_pow, te6Torus_pow, ht3, te6Torus_one, map_one]
  have hτ1 : s ≠ 1 := fun h => te6Torus_not_mem_center θ hθ ht2 (hΘ _ h)
  have hgτ : Θ (nHat θ (nf 3)) * s * (Θ (nHat θ (nf 3)))⁻¹ = s⁻¹ := by
    rw [hs, ← map_inv, ← map_mul, ← map_mul, nHat_three_conj_te6Torus, map_inv]
  have hu : orderOf (φ 3 (sl2Upper 1)) = 2 := by
    rw [orderOf_injective _ (hinj 3)]
    exact orderOf_sl2Upper_one hF
  exact liftDatum_of_commuting_SL2_torus hF (m := 3) (fun i => φ i.castSucc) (fun i => hinj _)
    (fun i i' hii A B => hcomm _ _ (fun h => hii (Fin.castSucc_injective 3 h)) A B) hu hτ3 hτ1
    (fun i A => hcomm i.castSucc 3 (hne i) A _) (fun i A => (hsφ _ A).eq)
    ((hsφ 3 (sl2Upper 1)).symm.eq) hgτ

theorem twistedE6_liftDatum_even
    (d : TypeTwistedE6LieIndex) (h2 : ringChar d.1.fixedField = 2)
    (h3 : d.1.fieldOrder % 3 = 2) : LiftDatum (FixedPointCandidate d.steinberg) 3 := by
  classical
  have hθ : ∀ c, quadFrob d (quadFrob d c) = c := quadFrob_quadFrob d
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  have : Fintype (quadField d) := Fintype.ofFinite _
  have hdvd : 3 ∣ Nat.card (quadField d)ˣ := by
    rw [Nat.card_units, card_quadField]
    have h1 : d.1.fieldOrder ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
    have hpos : 1 ≤ d.1.fieldOrder ^ 2 := Nat.one_le_pow _ _ d.1.fieldOrder_pos
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hfr : Units.map (quadFrob d : quadField d →* quadField d) t = t ^ d.1.fieldOrder :=
    Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_ofClass, quadFrob_eq_pow])
  have htt : t * Units.map (quadFrob d : quadField d →* quadField d) t = 1 := by
    rw [hfr, ← pow_succ']
    exact orderOf_dvd_iff_pow_eq_one.1 (ht ▸ (by omega : 3 ∣ d.1.fieldOrder + 1))
  have ht2 : ((t : quadField d)) ^ 2 ≠ 1 := by
    intro h
    have h' : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have h'' : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h'
    rw [ht] at h''
    omega
  exact liftDatum_te6 (quadFrob d) (quadIncl d) hj hθ (toQuot (te6Embed d) hC)
    (fun g hg => mem_center_of_toQuot_eq_one (te6Embed_injective d) hC hg) hinj h2 htt ht3 ht2

theorem twistedE6_liftDatum_even'
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (h2 : ringChar (ValidLieTypeIndex.fixedField ⟨.twistedE6 q, hv⟩) = 2)
    (h3 : q.p ^ q.exponent % 3 = 2) :
    LiftDatum (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group 3 :=
  twistedE6_liftDatum_even ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩ h2
    (by
      show (LieTypeIndex.twistedE6 q).fieldOrder % 3 = 2
      rw [LieTypeIndex.fieldOrder_twistedE6, PrimePower.card_def]
      exact h3)

end TwistedTorus

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
