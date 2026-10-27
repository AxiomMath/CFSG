module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFinal2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

@[expose] def preBar (T : Subgroup G) (Ubar : Subgroup (NQuot T)) : Subgroup G :=
  (Ubar.comap (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G))))).map
    (Subgroup.normalizer (T : Set G)).subtype

omit [Finite G] in
theorem mem_preBar {Ubar : Subgroup (NQuot T)} {x : G} :
    x ∈ preBar T Ubar ↔ ∃ hx : x ∈ Subgroup.normalizer (T : Set G), barElt T hx ∈ Ubar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hU⟩
    exact ⟨⟨x, hx⟩, hU, rfl⟩

omit [Finite G] in
theorem preBar_le_normalizer (Ubar : Subgroup (NQuot T)) :
    preBar T Ubar ≤ Subgroup.normalizer (T : Set G) := fun _ hx => (mem_preBar.1 hx).1

omit [Finite G] in
theorem isPGroup_preBar (hT : IsPGroup 2 T) {Ubar : Subgroup (NQuot T)} (hU : IsPGroup 2 Ubar) :
    IsPGroup 2 (preBar T Ubar) := by
  have hker : IsPGroup 2
      (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))).ker := by
    rw [QuotientGroup.ker_mk']
    exact hT.comap_subtype
  exact (hU.comap_of_ker_isPGroup _ hker).map _

omit [Finite G] in
theorem le_preBar_barSub {R : Subgroup G} (hR : R ≤ Subgroup.normalizer (T : Set G)) :
    R ≤ preBar T (barSub T R) := fun _ hr =>
  mem_preBar.2 ⟨hR hr, barElt_mem_barSub (hR hr) hr⟩

omit [Finite G] in
theorem preBar_mono {Ubar Vbar : Subgroup (NQuot T)} (h : Ubar ≤ Vbar) :
    preBar T Ubar ≤ preBar T Vbar := fun _ hx => by
  obtain ⟨hx', hU⟩ := mem_preBar.1 hx
  exact mem_preBar.2 ⟨hx', h hU⟩

theorem Sec4Hyp.weaklyClosedIn_barSub_sec4R
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction) (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16)
    {Ubar : Subgroup (NQuot T)} (hU : IsPGroup 2 Ubar)
    (hRU : barSub T (sec4R T T₁ T₂) ≤ Ubar) :
    WeaklyClosedIn (barSub T (sec4R T T₁ T₂)) Ubar := by
  refine ⟨hRU, fun gbar hg => ?_⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective gbar
  have hkT : (k : G) ∈ Subgroup.normalizer (T : Set G) := k.2
  have hTP : IsPGroup 2 T := isPGroup_two_of_isElemAbelian h.pair.wc.1
  have hUP := isPGroup_preBar hTP hU
  have hRU' : sec4R T T₁ T₂ ≤ preBar T Ubar :=
    (le_preBar_barSub sec4R_le_normalizer_left).trans (preBar_mono hRU)
  have hgk : (QuotientGroup.mk k : NQuot T) = barElt T hkT := rfl
  have hconjU : conjSubgroup (k : G) (sec4R T T₁ T₂) ≤ preBar T Ubar := by
    have hle : conjSubgroup (k : G) (sec4R T T₁ T₂) ≤ Subgroup.normalizer (T : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hkT (sec4R_le_normalizer_left hr))
        ((Subgroup.normalizer (T : Set G)).inv_mem hkT)
    refine (le_preBar_barSub hle).trans (preBar_mono ?_)
    rw [← conjSubgroup_barSub hkT]
    rw [hgk] at hg
    exact hg
  have hconj : conjSubgroup (k : G) (sec4R T T₁ T₂) ≤
      Subgroup.closure ((preBar T Ubar : Set G) ∩ sec4E T T₁ T₂) := by
    rw [← h.closure_sec4R_inter_eq]
    unfold conjSubgroup
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨d, hd, rfl⟩
    refine Subgroup.subset_closure ⟨hconjU ⟨d, hd.1, rfl⟩, ?_⟩
    have hkd : (k : G) * d * (k : G)⁻¹ ∈ sec4E T T₁ T₂ :=
      sec4E_conj (subset_sec4E hd.2 hd.1) hkT
    simpa [MulAut.conj_apply] using hkd
  rw [h.closure_inter_sec4E_eq hnab hind hAsc hA hC hq h16 hUP hRU' (preBar_le_normalizer Ubar)]
    at hconj
  have heq : conjSubgroup (k : G) (sec4R T T₁ T₂) = sec4R T T₁ T₂ := conjSubgroup_eq_of_le hconj
  rw [hgk, conjSubgroup_barSub hkT, heq]

end CFSG.CGT.Timmesfeld75
