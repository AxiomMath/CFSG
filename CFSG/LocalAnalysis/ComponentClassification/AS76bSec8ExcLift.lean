module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalSuz
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

section Central

variable {P P' : Type*} [Group P] [Group P']

@[expose] def centralQuotEquiv (hP : Group.IsPerfect P) (f : P →* P')
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) : P ⧸ center P ≃* P' ⧸ center P' :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        LocalCores.comap_center_eq_of_perfect hP f hf hker] :
      center P = ((QuotientGroup.mk' (center P')).comp f).ker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))

theorem isQuasisimple_of_surjective (hP : Group.IsPerfect P) (f : P →* P')
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) (hQ : CFSG.Open.IsQuasisimple P') :
    CFSG.Open.IsQuasisimple P := by
  have := hQ.2
  exact ⟨hP.commutator_eq_top, (centralQuotEquiv hP f hf hker).isSimpleGroup⟩

theorem statedPSL_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {n p f : ℕ}
    (h : StatedClassicalModel S' .PSL n p f) : StatedClassicalModel S .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

end Central

section Inn

variable {C : Type*} [Group C]

@[expose] def inn (S : Subgroup C) : Subgroup (MulAut C) := S.map (MulAut.conj : C →* MulAut C)

theorem conj_mem_inn {S : Subgroup C} {s : C} (hs : s ∈ S) : MulAut.conj s ∈ inn S :=
  ⟨s, hs, rfl⟩

theorem inn_le_range (S : Subgroup C) : inn S ≤ (MulAut.conj : C →* MulAut C).range :=
  map_le_range _ _

theorem commutator_inn {S : Subgroup C} (hS : ⁅S, S⁆ = S) : ⁅inn S, inn S⁆ = inn S := by
  rw [inn, ← map_commutator, hS]

variable (hZC : center C = ⊥)
include hZC

@[expose] def innEquiv (S : Subgroup C) : ↥S ≃* ↥(inn S) :=
  S.equivMapOfInjective _ (RankTwoHypIIY.conj_injective_of_center_eq_bot hZC)

omit hZC in
theorem conj_mem_normalizer_inn {S : Subgroup C} {c : C} (hc : c ∈ normalizer (S : Set C)) :
    MulAut.conj c ∈ normalizer (inn S : Set (MulAut C)) := by
  have key : ∀ d : C, d ∈ normalizer (S : Set C) → ∀ φ ∈ inn S,
      MulAut.conj d * φ * (MulAut.conj d)⁻¹ ∈ inn S := by
    rintro d hd _ ⟨s, hs, rfl⟩
    refine ⟨d * s * d⁻¹, (mem_normalizer_iff.1 hd s).1 hs, ?_⟩
    simp only [map_mul, map_inv]
  refine mem_normalizer_iff.2 fun φ => ⟨key c hc φ, fun h => ?_⟩
  have h1 := key c⁻¹ (inv_mem hc) _ h
  simpa [map_inv, mul_assoc] using h1

end Inn

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit hZC in
theorem ker_leviLiftPsi_le_center' {S : Subgroup (MulAut C)} :
    (leviLiftPsi ψ S).ker ≤ center (leviLift ψ S) := by
  intro l h
  rw [MonoidHom.mem_ker] at h
  have hC : (l : G) ∈ centralizer (A : Set G) := by
    refine (hψ.eq_one_iff ⟨l, le_normalizer (leviLift_le l.2)⟩).1 ?_
    have := congrArg Subtype.val h
    rwa [leviLiftPsi_apply] at this
  rw [mem_center_iff]
  intro l'
  exact Subtype.ext (mem_centralizer_iff.1 hC l' (leviLift_le l'.2))

theorem isQuasisimple_leviLift_inn {S : Subgroup C} (hperf : ⁅S, S⁆ = S)
    (hSq : CFSG.Open.IsQuasisimple ↥S) : CFSG.Open.IsQuasisimple ↥(leviLift ψ (inn S)) :=
  isQuasisimple_of_surjective
    ((Subgroup.isPerfect_iff).2 (commutator_leviLift hψ (inn_le_range S) (commutator_inn hperf)))
    _ (leviLiftPsi_surjective hψ (inn_le_range S) (commutator_inn hperf))
    (ker_leviLiftPsi_le_center' hψ) (isQuasisimple_of_equiv (innEquiv hZC S) hSq)

@[expose] def quotEquiv_leviLift {S : Subgroup C} (hperf : ⁅S, S⁆ = S) :
    ↥(leviLift ψ (inn S)) ⧸ center ↥(leviLift ψ (inn S)) ≃* ↥S ⧸ center ↥S :=
  (centralQuotEquiv
    ((Subgroup.isPerfect_iff).2 (commutator_leviLift hψ (inn_le_range S) (commutator_inn hperf)))
    _ (leviLiftPsi_surjective hψ (inn_le_range S) (commutator_inn hperf))
    (ker_leviLiftPsi_le_center' hψ)).trans (quotCenterCongr (innEquiv hZC S).symm)

omit hZC hψ in
theorem exists_mem_of_mem_leviLift {S : Subgroup C} {l : G} (hl : l ∈ leviLift ψ (inn S)) :
    ∃ s ∈ S, ψ ⟨l, le_normalizer (leviLift_le hl)⟩ = MulAut.conj s := by
  obtain ⟨s, hs, hsl⟩ := psi_mem_of_mem_leviLift hl
  exact ⟨s, hs, hsl.symm⟩

theorem odd_card_center_leviLift [Finite G] (hZA : Odd (Nat.card (center A))) {S : Subgroup C}
    (hperf : ⁅S, S⁆ = S) (hSZ : Odd (Nat.card (center ↥S))) :
    Odd (Nat.card (center ↥(leviLift ψ (inn S)))) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hS := inn_le_range S
  have hP := commutator_inn hperf
  refine AS76b.Lemma22.odd_card_of_forall_orderOf_ne_two fun z hz h2 => ?_
  have hz2 : z ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨y, hyS, hy⟩ := exists_mem_of_mem_leviLift z.2
  have hyZ : (⟨y, hyS⟩ : ↥S) ∈ center ↥S := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    obtain ⟨l', hl', hl'ψ⟩ := exists_mem_leviLift hψ hS hP (conj_mem_inn l.2)
    have hc := mem_center_iff.1 hz ⟨l', hl'⟩
    have h := congrArg (fun x : ↥(leviLift ψ (inn S)) =>
      ψ ⟨x, le_normalizer (leviLift_le x.2)⟩) hc
    simp only [Subgroup.coe_mul] at h
    rw [psi_mul (le_normalizer (leviLift_le hl')) (le_normalizer (leviLift_le z.2)),
      psi_mul (le_normalizer (leviLift_le z.2)) (le_normalizer (leviLift_le hl')), hl'ψ, hy,
      ← map_mul, ← map_mul] at h
    exact hinj h
  have hyy : y ^ 2 = 1 := by
    apply hinj
    rw [map_pow, ← hy, ← map_pow, map_one]
    have hz2' : (⟨(z : G), le_normalizer (leviLift_le z.2)⟩ : normalizer (A : Set G)) ^ 2 = 1 :=
      Subtype.ext (by
        have := congrArg Subtype.val hz2
        simpa using this)
    rw [hz2', map_one]
  have hy2 : (⟨y, hyS⟩ : ↥S) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    simpa using hyy
  have hy1 := RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hSZ hyZ) hy2
  have hψz : ψ ⟨z, le_normalizer (leviLift_le z.2)⟩ = 1 := by
    rw [hy]
    have : y = 1 := congrArg Subtype.val hy1
    rw [this, map_one]
  have hzK := (hψ.eq_one_iff _).1 hψz
  have hz' := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨leviLift_le z.2, hzK⟩)) (k := 1)
    (by rw [pow_one]; exact congrArg Subtype.val hz2)
  exact hz1 (Subtype.ext hz')

omit hZC in
theorem layerCentralizer_eq_leviLift' {Q : Subgroup G} (hQA : Q ≤ A)
    {S : Subgroup (MulAut C)}
    (hQS : ∀ w (hw : w ∈ Q), ∀ s ∈ S,
      ψ ⟨w, le_normalizer (hQA hw)⟩ * s = s * ψ ⟨w, le_normalizer (hQA hw)⟩)
    (hN : ∀ x (hx : x ∈ A ⊓ centralizer (Q : Set G)),
      ψ ⟨x, le_normalizer (mem_inf.1 hx).1⟩ ∈ normalizer (S : Set (MulAut C)))
    (hcomm : ∀ x (hx : x ∈ A ⊓ centralizer (Q : Set G)) y (hy : y ∈ A ⊓ centralizer (Q : Set G)),
      ψ ⟨⁅x, y⁆, le_normalizer (RankTwoL3Even.commutatorElement_mem' (mem_inf.1 hx).1
        (mem_inf.1 hy).1)⟩ ∈ S)
    (hq : CFSG.Open.IsQuasisimple ↥(leviLift ψ S)) :
    layerCentralizer A Q = leviLift ψ S := by
  have hLC : leviLift ψ S ≤ A ⊓ centralizer (Q : Set G) :=
    le_inf leviLift_le fun l hl => mem_centralizer_iff.2 fun w hw =>
      (mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ (le_normalizer (hQA hw))
        (hQS w hw) hl)).symm
  have hcommC : ⁅A ⊓ centralizer (Q : Set G), A ⊓ centralizer (Q : Set G)⁆ ≤ liftIn ψ S := by
    rw [commutator_le]
    intro x hx y hy
    exact mem_liftIn.2 ⟨RankTwoL3Even.commutatorElement_mem' (mem_inf.1 hx).1 (mem_inf.1 hy).1,
      hcomm x hx y hy⟩
  apply le_antisymm
  · have hE : layerCentralizer A Q = ⁅layerCentralizer A Q, layerCentralizer A Q⁆ := by
      rw [layerCentralizer, ← map_commutator, LocalCores.layer_perfect]
    have h1 : layerCentralizer A Q ≤ liftIn ψ S := by
      rw [hE]
      exact (commutator_mono (layerCentralizer_le A Q) (layerCentralizer_le A Q)).trans hcommC
    rw [hE]
    exact commutator_mono h1 h1
  · have hn : ((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hLC).2 fun c hc =>
        mem_normalizer_leviLift (le_normalizer (mem_inf.1 hc).1) (hN c hc)
    have hq' : CFSG.IsQuasisimple ↥((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))) :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).1
        (isQuasisimple_of_equiv (subgroupOfEquivOfLe hLC).symm hq)
    have hcomp : CFSG.IsComponent ((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))) :=
      ⟨hq', hn.isSubnormal⟩
    intro l hl
    exact ⟨⟨l, hLC hl⟩, LocalCores.component_le_layer hcomp (mem_subgroupOf.2 hl), rfl⟩

end Lift

section D0

variable {C : Type*} [Group C]

theorem map_conj_le_centralizer {S D : Subgroup C} (h : D ≤ centralizer (S : Set C)) (c : C) :
    D.map (MulAut.conj c).toMonoidHom ≤
      centralizer ((S.map (MulAut.conj c).toMonoidHom : Subgroup C) : Set C) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  have h1 : s * d = d * s := mem_centralizer_iff.1 (h hd) s hs
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc c * s * c⁻¹ * (c * d * c⁻¹) = c * (s * d) * c⁻¹ := by group
    _ = c * (d * s) * c⁻¹ := by rw [h1]
    _ = c * d * c⁻¹ * (c * s * c⁻¹) := by group

theorem map_conj_map_conj_inv (U : Subgroup C) (c : C) :
    (U.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = U := by
  ext y
  rw [mem_map_equiv, mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_symm_apply,
    show c⁻¹⁻¹ * (c⁻¹ * y * c) * c⁻¹ = y by group]

theorem map_conj_inv_map_conj (U : Subgroup C) (c : C) :
    (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
  have := map_conj_map_conj_inv U c⁻¹
  rwa [inv_inv] at this

theorem D0Data.conj {x : C} {Z : Subgroup C} (h : D0Data x Z) (c : C) :
    D0Data (c * x * c⁻¹) (Z.map (MulAut.conj c).toMonoidHom) := by
  intro S hS hodd
  set S' := S.map (MulAut.conj c⁻¹).toMonoidHom with hS'
  have hS'le : S' ≤ cent x := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := hS hs
    rw [cent_conj, mem_map_equiv, MulAut.conj_symm_apply] at h1
    simpa using h1
  have hS'odd : Odd (Nat.card S') := by
    rw [hS', card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hodd
  obtain ⟨D₀, hperf, hcent, hZ, hW⟩ := h S' hS'le hS'odd
  refine ⟨D₀.map (MulAut.conj c).toMonoidHom, ?_, ?_, map_mono hZ, fun W hWZ hW1 hle => ?_⟩
  · rw [← map_commutator, hperf]
  · have := map_conj_le_centralizer hcent c
    rwa [hS', map_conj_map_conj_inv] at this
  · refine hW (W.map (MulAut.conj c⁻¹).toMonoidHom) ?_ ?_ ?_
    · have := map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hWZ
      rwa [map_conj_inv_map_conj] at this
    · intro h0
      apply hW1
      have := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) h0
      rwa [map_conj_map_conj_inv, Subgroup.map_bot] at this
    · intro d hd
      have h1 := hle ⟨d, hd, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [mem_normalizer_iff] at h1 ⊢
      intro k
      rw [mem_map_equiv, mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_symm_apply, inv_inv,
        h1 (c * k * c⁻¹)]
      constructor <;> intro hk <;> convert hk using 1 <;> group

end D0

end CFSG.ComponentClassification.RankTwoExceptional.Exc
