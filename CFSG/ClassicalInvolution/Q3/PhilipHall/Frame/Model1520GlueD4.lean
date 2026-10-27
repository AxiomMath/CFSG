module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueD4Orth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSpin
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Q3.Q3TLK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1
local notation "Q₄" => quadPlus 4 (GaloisField 3 1)
local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

@[expose] noncomputable def projOfSpin {ι : Type} [Fintype ι] (Q : QuadraticForm 𝔽₃ (ι → 𝔽₃))
    (hmem : ∀ k, spinAction Q k ∈ orthDerived Q) : spinGroup Q →* ProjOrthDerived Q :=
  (QuotientGroup.mk' _).comp ((spinAction Q).codRestrict _ hmem)

theorem projOfSpin_apply {ι : Type} [Fintype ι] (Q : QuadraticForm 𝔽₃ (ι → 𝔽₃))
    (hmem : ∀ k, spinAction Q k ∈ orthDerived Q) (k : spinGroup Q) :
    projOfSpin Q hmem k = QuotientGroup.mk ⟨spinAction Q k, hmem k⟩ := rfl

section D4


theorem inducedBySemilinear_d4_of_fixed
    (hmem : ∀ k, spinAction Q₄ k ∈ orthDerived Q₄)
    (hOD : ∀ g ∈ orthDerived Q₄, g ∈ (spinAction Q₄).range)
    (hπ : Function.Surjective (projOfSpin Q₄ hmem))
    (hπker : (projOfSpin Q₄ hmem).ker = Subgroup.center (spinGroup Q₄))
    (fr : OFrame Q₄) (α : MulAut (ProjOrthDerived Q₄))
    (hfix : ∀ k : spinGroup Q₄, spinAction Q₄ k ∈ fr.La.range ⊔ fr.swap.La.range →
      k ^ 3 = 1 → α (projOfSpin Q₄ hmem k) = projOfSpin Q₄ hmem k) :
    InducedBySemilinear Q₄ α := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup Q₄) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  set π := projOfSpin Q₄ hmem with hπdef
  have hC : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπker]
    exact RouteD.Gaps.not_dvd_card_center_plus (p := 3) (f := 1) (by norm_num) hn3
  obtain ⟨α', hα'⟩ := (ModelFacts.OrthAut.centralPSection_spinPlus (p := 3) (F := 𝔽₃)
    hn3).exists_mulEquiv_lift π hπ hπker.le hC α
  have hZ3 := center_plus4_no_three
  have h3fix : ∀ g ∈ (fr.La.range ⊔ fr.swap.La.range).comap (spinAction Q₄), g ^ 3 = 1 →
      α' g = g := by
    intro g hg hg3
    refine fixed_of_pow_three α' hZ3 hg3 ?_
    rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hα', hfix g hg hg3, inv_mul_cancel]
  obtain ⟨A, φ, μ, hsim, hmat⟩ := d4FixLift3 fr α' h3fix
  let F : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃+ (Fin 4 ⊕ Fin 4 → 𝔽₃) :=
    (AddEquiv.piCongrRight fun _ => φ.toAddEquiv).trans (glLin A).toAddEquiv
  have hF : ∀ v, F v = A.val.mulVec (fun i => φ (v i)) := fun v => glLin_apply A _
  refine ⟨φ, F, fun c v => ?_, (μ : 𝔽₃), μ.ne_zero, fun v => ?_, fun g g' hgg' => ?_⟩
  · rw [hF, hF, ← Matrix.mulVec_smul]
    congr 1
    ext i
    simp
  · rw [hF]
    exact hsim v
  · obtain ⟨x, hx⟩ := hOD g g.2
    have hg : g = ⟨spinAction Q₄ x, hmem x⟩ := Subtype.ext hx.symm
    have hg' : g' = ⟨spinAction Q₄ (α' x), hmem (α' x)⟩ := by
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      obtain ⟨w, rfl⟩ := F.surjective v
      rw [hgg', AddEquiv.symm_apply_apply]
      show F ((g : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) w) =
        spinAction Q₄ (α' x) (F w)
      rw [show (g : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] _) w = spinAction Q₄ x w from by rw [hg]]
      symm
      rw [← glLin_spinMatrix Q₄ (α' x), hmat x, ← glLin_spinMatrix Q₄ x, hF, hF]
      simp only [map_mul, LinearEquiv.mul_apply, glLin_apply]
      have h1 : ∀ u : Fin 4 ⊕ Fin 4 → 𝔽₃,
          ((A⁻¹ : GL (Fin 4 ⊕ Fin 4) 𝔽₃) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝔽₃).mulVec
            ((A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝔽₃).mulVec u) = u := fun u => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h1]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct,
        CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_entry, map_sum,
        map_mul]
    rw [hg, hg']
    have h1 : QuotientGroup.mk (⟨spinAction Q₄ x, hmem x⟩ : orthDerived Q₄) = π x := rfl
    rw [h1, ← hα' x]
    rfl

theorem model1520_of_spinCtx3_d4 {𝓕 : Set (Subgroup (spinGroup Q₄))} (ctx : SpinCtx3 Q₄ 𝓕)
    [Finite (spinGroup Q₄)] (hperf : Group.IsPerfect (spinGroup Q₄))
    (hOD : orthDerived Q₄ = elementaryGroup Q₄)
    {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : spinGroup Q₄ →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q₄))
    {R : Subgroup (spinGroup Q₄)} (hR : R ∈ 𝓕) (e₂ : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e₂) : ↥X) : G) := by
  classical
  have h3 : Nat.card 𝔽₃ = 3 := natCard_galoisField_three
  have hodd := odd_natCard_galoisField_three
  obtain ⟨fr, hfr⟩ := ctx.hframe R hR
  have hθ : spinAction Q₄ (sl2Inv e₂) = fr.La (-1) := theta_sl2Inv e₂ hfr
  have hQ := ctx.hQ
  have hmem : ∀ k, spinAction Q₄ k ∈ orthDerived Q₄ := fun k => by
    rw [hOD, ← ctx.hrange]
    exact ⟨k, rfl⟩
  have hπ : Function.Surjective (projOfSpin Q₄ hmem) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : (g : _ ≃ₗ[𝔽₃] _) ∈ (spinAction Q₄).range := by
      rw [ctx.hrange, ← hOD]
      exact g.2
    obtain ⟨k, hk⟩ := hg
    exact ⟨k, congrArg QuotientGroup.mk (Subtype.ext hk)⟩
  have hπker : (projOfSpin Q₄ hmem).ker = Subgroup.center (spinGroup Q₄) := by
    ext k
    rw [MonoidHom.mem_ker, projOfSpin_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      refine mem_center_of_commutators_central hperf fun y => ker_spinAction_le_center Q₄ ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc := commute_of_mem_scalars (show spinAction Q₄ k ∈ scalars 𝔽₃ _ from hk)
        (spinAction Q₄ y)
      calc spinAction Q₄ k * spinAction Q₄ y * (spinAction Q₄ k)⁻¹ * (spinAction Q₄ y)⁻¹
          = (spinAction Q₄ y * spinAction Q₄ k) * (spinAction Q₄ k)⁻¹ *
              (spinAction Q₄ y)⁻¹ := by
            rw [hc]
        _ = 1 := by group
    · intro hk
      have hz : (⟨spinAction Q₄ k, by rw [← ctx.hrange]; exact ⟨k, rfl⟩⟩ : elementaryGroup Q₄) ∈
          Subgroup.center (elementaryGroup Q₄) := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨g, hg⟩
        rw [← ctx.hrange] at hg
        obtain ⟨y, rfl⟩ := hg
        apply Subtype.ext
        change spinAction Q₄ y * spinAction Q₄ k = spinAction Q₄ k * spinAction Q₄ y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk y]
      exact Subgroup.mem_subgroupOf.mp (ctx.hZ hz)
  obtain ⟨e, he⟩ := exists_equiv_of_covers hperf ψ hψ hker (projOfSpin Q₄ hmem) hπ hπker
  have hP : Group.IsPerfect (ProjOrthDerived Q₄) := Group.IsPerfect.ofSurjective hπ
  have hreg := fr.polarNondegOn_span
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_suppPerp hreg)
  have hspan := fr.finrank_span
  have hdim := ctx.hdim
  have hhmem : fr.La (-1) ∈ orthDerived Q₄ := hθ ▸ hmem _
  have hsq : ((ψ (sl2Inv e₂) : ↥X) : G) * ((ψ (sl2Inv e₂) : ↥X) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, sl2Inv_mul_self hodd e₂, map_one, Subgroup.coe_one]
  have hPc : fr.La.range ⊔ fr.swap.La.range ≤ Subgroup.centralizer {fr.La (-1)} := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact fr.La_neg_one_comm A
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact fr.La_swap_neg_one_comm A
  refine model1520_of_orth_abs_set (X := X) (t := ((ψ (sl2Inv e₂) : ↥X) : G))
    (ψ (sl2Inv e₂)).2 hsq h3 Q₄ hQ hP e fr.span (nondegenerate_polarBilin_restrict hreg)
    (by omega) (by omega) (fr.La (-1)) hhmem (-1) 1 ?_ ?_ ?_
    ((projOfSpin Q₄ hmem) '' {k | spinAction Q₄ k ∈ fr.La.range ⊔ fr.swap.La.range ∧ k ^ 3 = 1})
    ?_ ?_
  · intro w hw
    rw [fr.La_neg_one_apply, ← (fr.mem_span_iff.mp hw)]
    module
  · intro w hw
    rw [← frame_perp_eq_suppPerp, fr.mem_perp_iff] at hw
    rw [fr.La_neg_one_apply, hw]
    simp
  · have := he (sl2Inv e₂)
    rw [this]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    exact hθ
  · rintro s ⟨k, ⟨hk, hk3⟩, rfl⟩
    refine ⟨by rw [← map_pow, hk3, map_one], ?_⟩
    rw [projOfSpin_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPc hk) _ rfl).symm
  · intro α _ hfixS
    refine inducedBySemilinear_d4_of_fixed hmem (fun g hg => by
      rw [ctx.hrange, ← hOD]; exact hg) hπ hπker fr α fun k hk hk3 => ?_
    exact hfixS _ (Or.inr ⟨k, ⟨hk, hk3⟩, rfl⟩)

end D4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
