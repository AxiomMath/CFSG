module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFusion
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.exists_eq_barElt_sec4N (h : Sec4Hyp T T₁ a T₂)
    {s : NQuot T} (hs : s ∈ barSub T (sec4R T T₁ T₂)) :
    ∃ (m : G) (hm : m ∈ sec4N T T₁ T₂), s = barElt T (sec4N_le_normalizer_left hm) := by
  obtain ⟨r, hrN, hrR, rfl⟩ := exists_eq_barElt_of_mem_barSub hs
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right T (sec4N T T₁ T₂)
    h.left_le_normalizer_sec4N
  have hr' : r ∈ (T : Set G) * (sec4N T T₁ T₂ : Set G) := by
    rw [← hmul]
    exact hrR
  obtain ⟨t, ht, m, hm, rfl⟩ := hr'
  refine ⟨m, hm, (barElt_eq_iff _ _).2 ?_⟩
  have e : (t * m)⁻¹ * m = m⁻¹ * t⁻¹ * (m⁻¹)⁻¹ := by group
  rw [e]
  exact conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem
    (sec4N_le_normalizer_left hm)) (T.inv_mem ht)

theorem Sec4Hyp.mem_sec4R_of_conj_centralizes
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction) (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) {g w a' b' : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (ha : a' ∈ normIn T₁ T) (hb : b' ∈ normIn T₂ T)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwg : w = g * (a' * b') * g⁻¹)
    (hcent : ∀ m ∈ sec4N T T₁ T₂, w * m * w⁻¹ * m⁻¹ ∈ T) : w ∈ sec4R T T₁ T₂ := by
  have hab : a' * b' ∈ sec4N T T₁ T₂ :=
    (sec4N T T₁ T₂).mul_mem (normIn_le_sec4N_mid ha) (normIn_le_sec4N_right hb)
  have habT : a' * b' ∈ Subgroup.normalizer (T : Set G) := sec4N_le_normalizer_left hab
  have hgi : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer (T : Set G)).inv_mem hg
  have hRP : IsPGroup 2 (barSub T (sec4R T T₁ T₂)) := isPGroup_barSub h.isPGroup_sec4R
  have hx : ∀ s ∈ barSub T (sec4R T T₁ T₂), barElt T habT * s = s * barElt T habT := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := h.exists_eq_barElt_sec4N hs
    rw [barElt_mul, barElt_mul]
    refine (barElt_eq_iff _ _).2 ?_
    have hc : (a' * b') * m = m * (a' * b') :=
      elemAbelian_mul_comm h.isElemAbelian_sec4N hab hm
    rw [hc]
    simp
  have hy : ∀ s ∈ barSub T (sec4R T T₁ T₂), barElt T hw * s = s * barElt T hw := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := h.exists_eq_barElt_sec4N hs
    rw [barElt_mul, barElt_mul]
    refine (barElt_eq_iff _ _).2 ?_
    have hmN := sec4N_le_normalizer_left hm
    have hu := hcent m hm
    have hwm : w * m ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).mul_mem hw hmN
    have e : (w * m)⁻¹ * (m * w) = (w * m)⁻¹ * (w * m * w⁻¹ * m⁻¹)⁻¹ * (w * m)⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hwm)
      (T.inv_mem hu)
  have hxy : (barElt T hgi)⁻¹ * barElt T habT * barElt T hgi = barElt T hw := by
    rw [barElt_inv, barElt_mul, barElt_mul]
    refine ((barElt_eq_iff _ _).2 ?_).symm
    have e : w⁻¹ * ((g⁻¹)⁻¹ * (a' * b') * g⁻¹) = 1 := by
      rw [hwg]
      group
    rw [e]
    exact T.one_mem
  obtain ⟨hbar, hhn, hconj⟩ := normalizer_controls_fusion_of_weaklyClosedIn_pGroup hRP
    (fun _ hU hRU => h.weaklyClosedIn_barSub_sec4R hnab hind hAsc hA hC hq h16 hU hRU) hx hy hxy
  have hxR : barElt T habT ∈ barSub T (sec4R T T₁ T₂) :=
    barElt_mem_barSub habT (sec4N_le_sec4R hab)
  have hyR : barElt T hw ∈ barSub T (sec4R T T₁ T₂) := by
    rw [← hconj]
    have := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (barSub T (sec4R T T₁ T₂) : Set (NQuot T))).inv_mem hhn) _).1 hxR
    simpa using this
  obtain ⟨u, -, huR, hu⟩ := (barElt_mem_barSub_iff hw).1 hyR
  have e : w = u * (u⁻¹ * w) := by group
  rw [e]
  exact (sec4R T T₁ T₂).mul_mem huR (left_le_sec4R hu)

end CFSG.CGT.Timmesfeld75
