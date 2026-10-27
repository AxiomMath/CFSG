module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem map_fixedSubgroup_eq {T G : Type*} [Group T] [Group G] (φ : T →* G)
    (hφ : Function.Injective φ) (α : MulAut T) (x : G) (hx : ∀ h, x * φ h * x⁻¹ = φ (α h)) :
    (fixedSubgroup α).map φ = φ.range ⊓ Subgroup.centralizer {x} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, ?_⟩
    have h1 := hx h
    rw [show α h = h from hh] at h1
    calc φ h * x = (x * φ h * x⁻¹) * x := by rw [h1]
      _ = x * φ h := by group
  · rintro ⟨⟨h, rfl⟩, hc⟩
    refine ⟨h, ?_, rfl⟩
    change α h = h
    apply hφ
    rw [← hx h]
    calc x * φ h * x⁻¹ = φ h * x * x⁻¹ := by rw [hc]
      _ = φ h := by group

theorem signMaskTuple_zero {K : Type} [Field K] : signMaskTuple .E7 K 0 = 1 := by
  funext j
  simp [signMaskTuple]

theorem map_signMaskTuple {K L : Type} [Field K] [Field L] (ι : K →+* L) (m : ℕ) :
    (fun i => Units.map ι.toMonoidHom (signMaskTuple .E7 K m i)) = signMaskTuple .E7 L m := by
  funext j
  simp [signMaskTuple]

section Lift

variable {K : Type} [Field K] {L : Type} [Field L] (ι : K →+* L)

@[expose] def liftElt (g : ModGL .E7 K) (a : Fin Tag.E7.rank → Kˣ) : ModGL .E7 L :=
  baseChangeGL ι g * rootDiagUnit .E7 fun i => Units.map ι.toMonoidHom (a i)

theorem liftElt_conj (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ)
    (h : adjointGroup .E7 K) :
    liftElt ι (g : ModGL .E7 K) a * baseChangeGL ι (h : ModGL .E7 K) *
        (liftElt ι (g : ModGL .E7 K) a)⁻¹ =
      baseChangeGL ι ((MulAut.conj g * rootDiagAut .E7 K a) h : ModGL .E7 K) := by
  have e : (((MulAut.conj g * rootDiagAut .E7 K a) h : adjointGroup .E7 K) : ModGL .E7 K) =
      (g : ModGL .E7 K) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ *
        (g : ModGL .E7 K)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_rootDiagAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, baseChangeGL_rootDiagUnit,
    liftElt]
  group

end Lift

theorem exists_twisted_reduction {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hα : orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2)
    (hns : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
      ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
        rootDiagAut .E7 K (signMaskTuple .E7 K m)) :
    liftElt (algebraMap K L) (g : ModGL .E7 K) a ∈
        fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) ∧
      liftElt (algebraMap K L) (g : ModGL .E7 K) a ^ 2 = 1 ∧
      ∃ r ∈ e7SignDiagramReps, (r.mask = 2 ∨ r.mask = 3) ∧
        ∃ g₁ ∈ adjointGroup .E7 L,
          g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹ =
            rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) ∧
          g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  set ι := algebraMap K L with hι
  set Fr := iterateFrobenius L p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr_def, iterateFrobenius_def, hK]
  set α := MulAut.conj g * rootDiagAut .E7 K a with hα_def
  set x := liftElt ι (g : ModGL .E7 K) a with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K
    hodd L ι
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hodd L Fr hFr
  have hgG : baseChangeGL ι (g : ModGL .E7 K) ∈ adjointGroup .E7 L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup .E7 L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift .E7 L _).1
  have hxconj : ∀ h : adjointGroup .E7 K,
      x * baseChangeGL ι (h : ModGL .E7 K) * x⁻¹ = baseChangeGL ι (α h : ModGL .E7 K) :=
    liftElt_conj ι g a
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr)
      (rootDiagUnit .E7 fun i => Units.map ι.toMonoidHom (a i)) =
        rootDiagUnit .E7 fun i => Units.map ι.toMonoidHom (a i) := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag _) = rootDiag _
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    change Fr (ι (a i : K)) = ι (a i : K)
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hF1 : frobTwistGL .E7 L p f 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hxR : x ∈ fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) := by
    refine mem_fixedPointsIn.2 ⟨hxG, ?_⟩
    rw [hF1, hx_def, liftElt, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have h2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have := congrArg (fun φ : MulAut (adjointGroup .E7 K) => φ h) h2
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  refine ⟨hxR, hx2, ?_⟩
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r, hr, l, hl, -, -, g₁, hg₁G, hconj, hcoc, -⟩ :=
    isFiniteToralTwistReduction_of_reps_exact p hp2 (e := f) hf (map_conj_one_adjointGroup _ L)
      1 (fun b hb => by
        rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p f hb, one_mul, inv_one,
          mul_one]
        rfl)
      e7SignDiagramReps h7.permChar_eq h7.exists_rep h7.coe_kernelPosStabilizer
      (finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)) hxR hx2
  refine ⟨r, hr, ?_⟩
  by_cases hl0 : l = []
  ·
    exfalso
    subst hl0
    have hFg : Units.map (entrywiseHom Fr) g₁ = g₁ := by
      have h1 : g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = 1 := hcoc
      rw [hF1] at h1
      exact (mul_inv_eq_one.1 h1).symm
    obtain ⟨c, u, hu, hgc⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hg₁G hFg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hu
    rw [← hι] at hgc
    set b := signMaskTuple .E7 K r.mask with hb_def
    have ht : signCharTuple (k := L) (signMaskChar .E7 r.mask) =
        fun i => Units.map ι.toMonoidHom (b i) := by
      rw [signCharTuple_signMaskChar, hb_def, map_signMaskTuple]
    have hcomm : baseChangeGL ι (rootDiagUnit .E7 c) *
        rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) =
          rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) *
            baseChangeGL ι (rootDiagUnit .E7 c) := by
      rw [baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hux : baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ =
        rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) := by
      have h1 : g₁ * x * g₁⁻¹ = baseChangeGL ι (rootDiagUnit .E7 c) *
          (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
            (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ := by
        rw [hgc]
        group
      rw [hconj] at h1
      calc baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ =
          (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ *
            (baseChangeGL ι (rootDiagUnit .E7 c) *
              (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
                (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹) *
                  baseChangeGL ι (rootDiagUnit .E7 c) := by group
        _ = (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ *
            rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) *
              baseChangeGL ι (rootDiagUnit .E7 c) := by rw [← h1]
        _ = rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) := by
            rw [mul_assoc, ← hcomm]
            group
    have hK' : g' * ((g : ModGL .E7 K) * rootDiagUnit .E7 a) * g'⁻¹ = rootDiagUnit .E7 b := by
      apply hinj
      rw [map_mul, map_mul, map_inv, map_mul, baseChangeGL_rootDiagUnit, baseChangeGL_rootDiagUnit,
        ← ht]
      exact hux
    set ψ : MulAut (adjointGroup .E7 K) := MulAut.conj ⟨g', hg'⟩ with hψ
    have hψα : ψ * α * ψ⁻¹ = rootDiagAut .E7 K b := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e1 : ((ψ * α * ψ⁻¹) h : ModGL .E7 K) =
          (g' * ((g : ModGL .E7 K) * rootDiagUnit .E7 a) * g'⁻¹) * h *
            (g' * ((g : ModGL .E7 K) * rootDiagUnit .E7 a) * g'⁻¹)⁻¹ := by
        simp only [hψ, hα_def, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
          MulAut.conj_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
        group
      rw [e1, hK', coe_rootDiagAut]
    simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have h1 : α = 1 := by
        have h0 : ψ * α * ψ⁻¹ = 1 := by
          rw [hψα, hb_def]
          change rootDiagAut .E7 K (signMaskTuple .E7 K 0) = 1
          rw [signMaskTuple_zero]
          exact (rootDiagAutHom .E7 K).map_one
        calc α = ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ := by group
          _ = 1 := by rw [h0]; group
      rw [h1, orderOf_one] at hα
      exact absurd hα (by decide)
    · exact hns 1 (Or.inl rfl) ψ hψα
    · exact hns 2 (Or.inr (Or.inl rfl)) ψ hψα
    · exact hns 3 (Or.inr (Or.inr rfl)) ψ hψα
  ·
    have hm := mask_eq_two_or_three_of_ne_nil hr hl hl0
    have hlw : l = e7Word2_1 := by
      simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp [e7OmegaWords0] at hl
        exact absurd hl hl0
      · simp [e7OmegaWords1] at hl
        exact absurd hl hl0
      · simp only [e7OmegaWords2, List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.resolve_left hl0
      · simp only [e7OmegaWords3, List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.resolve_left hl0
    refine ⟨hm, g₁, hg₁G, hconj, ?_⟩
    rw [← hlw]
    exact hcoc

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
