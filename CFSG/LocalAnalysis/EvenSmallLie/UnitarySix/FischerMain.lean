module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerSylow
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerHyperoval
public import CFSG.Sporadic.Fi22.Uniqueness

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup CFSG.EvenSmallLie.ThreeTransposition
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

namespace FischerHyp

theorem isThreeTranspositionSet
    [Finite G] (h : FischerHyp t L E p) :
    (commGraph (tClass t)).Connected ∧ IsThreeTranspositionSet (tClass t) :=
  h.connected_of_hii h.hii

theorem localGroup_le
    (h : FischerHyp t L E p) : LocalGroup (tClass t) t ≤ L :=
  (closure_le L).2 fun _ hs => h.mem_L hs

@[expose] noncomputable def localHom
    (h : FischerHyp t L E p) :
    LocalGroup (tClass t) t →* Equiv.Perm (Fin 693) :=
  p.comp (Subgroup.inclusion h.localGroup_le)

theorem localHom_star
    (h : FischerHyp t L E p) (s : LocalClass (tClass t) t) :
    h.localHom ⟨s, subset_closure s.2⟩ = tvP (h.pt s) :=
  h.p_pt s

theorem range_localHom
    (h : FischerHyp t L E p) : h.localHom.range = T46 := by
  refine le_antisymm (fun _ ⟨x, hx⟩ => hx ▸ h.todd.mem_T46 _) ?_
  rw [T46_eq_closure, closure_le]
  rintro _ ⟨m, rfl⟩
  obtain ⟨s, rfl⟩ := h.pt_surjective m
  exact ⟨⟨s, subset_closure s.2⟩, h.localHom_star s⟩

theorem eq_one_of_commute_tvP
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46)
    (hc : ∀ m, g * tvP m = tvP m * g) : g = 1 := by
  ext m
  have e := (isPolarAut_of_mem hg).mul_tvP_mul_inv m
  rw [hc m, mul_inv_cancel_right] at e
  exact congrArg Fin.val (tvP_injective e).symm

theorem ker_localHom
    (h : FischerHyp t L E p) :
    h.localHom.ker = center (LocalGroup (tClass t) t) := by
  ext x
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro hx y
    have hx' := (h.todd.ker ⟨x, h.localGroup_le x.2⟩).1 hx
    rcases hx' with hx1 | hxt
    · have : x = 1 := Subtype.ext hx1
      rw [this, one_mul, mul_one]
    · refine Subtype.ext ?_
      simp only [Subgroup.coe_mul]
      rw [hxt]
      exact h.commute_t (h.localGroup_le y.2)
  · intro hx
    refine eq_one_of_commute_tvP (h.todd.mem_T46 _) fun m => ?_
    obtain ⟨s, rfl⟩ := h.pt_surjective m
    rw [← h.localHom_star s, ← map_mul, ← map_mul, hx]


@[expose] noncomputable def localIso
    (h : FischerHyp t L E p) :
    LocalQuotient (tClass t) t ≃* PSU (1 : Matrix (Fin 6) (Fin 6) Blueprint.Fischer.K) :=
  ((QuotientGroup.quotientMulEquivOfEq h.ker_localHom.symm).trans
    ((QuotientGroup.quotientKerEquivRange h.localHom).trans
      (MulEquiv.subgroupCongr h.range_localHom))).trans psuT46.symm

theorem psuT46_localIso_mk
    (h : FischerHyp t L E p) (x : LocalGroup (tClass t) t) :
    ((psuT46 (h.localIso (QuotientGroup.mk x)) : T46) : Equiv.Perm (Fin 693)) = h.localHom x := by
  rw [localIso, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem localIso_image
    (h : FischerHyp t L E p) :
    h.localIso '' LocalImages (tClass t) t = Transvections 1 := by
  rw [transvections_eq]
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨h.pt ⟨x, hx⟩, psuT46.injective (Subtype.ext ?_)⟩
    rw [psuT46_tvPsu, psuT46_localIso_mk]
    exact (h.localHom_star ⟨x, hx⟩).symm
  · rintro ⟨m, rfl⟩
    obtain ⟨s, rfl⟩ := h.pt_surjective m
    refine ⟨QuotientGroup.mk ⟨s, subset_closure s.2⟩, ⟨⟨s, subset_closure s.2⟩, s.2, rfl⟩, ?_⟩
    refine psuT46.injective (Subtype.ext ?_)
    rw [psuT46_tvPsu, psuT46_localIso_mk]
    exact h.localHom_star s

variable [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem not_mem_center
    (h : FischerHyp t L E p) : t ∉ center G := by
  intro ht
  obtain ⟨n, -, hne⟩ := h.todd.move
  exact hne (by rw [mem_center_iff.1 ht n⁻¹, inv_mul_cancel_right])

omit [Finite G] in
theorem center_eq_bot
    (h : FischerHyp t L E p) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
  · exact hc
  · exact absurd (hc ▸ mem_top t) h.not_mem_center

omit [Finite G] in
theorem commutator_eq_top
    (h : FischerHyp t L E p) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · refine absurd (mem_center_iff.2 fun g => ?_) h.not_mem_center
    have hgt : ⁅g, t⁆ ∈ commutator G :=
      commutator_mem_commutator (mem_top g) (mem_top t)
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hgt
    exact hgt
  · exact hc

omit [Finite G] in
theorem isSimpleGroup_commutator
    (h : FischerHyp t L E p) : IsSimpleGroup (commutator G) :=
  MulEquiv.isSimpleGroup (CFSG.Sporadic.Fi22.equivOfEqTop h.commutator_eq_top)

omit [Finite G] in
theorem closure_tClass
    (h : FischerHyp t L E p) : closure (tClass t) = ⊤ := by
  have hN : (closure (tClass t)).Normal := ⟨fun n hn g => by
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact subset_closure (conj_mem_tClass g hx)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (closure (tClass t)) with hc | hc
  · have := subset_closure (self_mem_tClass t)
    rw [hc, SetLike.mem_coe, mem_bot] at this
    exact absurd this (ThreeTransposition.ne_one_of_orderOf h.orderOf_t)
  · exact hc

theorem pair
    (h : FischerHyp t L E p) : Pair G (tClass t) :=
  ⟨inferInstance, ⟨t, rfl⟩, fun _ hx => orderOf_of_mem_tClass h.orderOf_t hx,
    h.isThreeTranspositionSet.2.2.2, h.closure_tClass⟩

theorem f22
    (h : FischerHyp t L E p) : F22 G (tClass t) :=
  ⟨h.pair, t, self_mem_tClass t, 1, isNondegenerateHermitian_one, h.localIso, h.localIso_image⟩

end FischerHyp

theorem fi22_of_hunt
    [Finite G] [IsSimpleGroup G] (h : FischerHyp t L E p) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  obtain ⟨iso, -⟩ := CFSG.Sporadic.Fi22.fischer_uniqueness_zero polarFacts G (tClass t) h.pair
    h.center_eq_bot h.isSimpleGroup_commutator h.f22
  exact ⟨iso⟩

end CFSG.EvenSmallLie.UnitarySix.Fischer
