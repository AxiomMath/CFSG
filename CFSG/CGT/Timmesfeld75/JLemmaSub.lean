module

public import CFSG.CGT.Timmesfeld75.Sec3Root

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Classes

variable {G : Type} [Group G] {R T : Subgroup G}

theorem mem_classD_subgroupOf_iff {r : ↥R} :
    r ∈ classD (T.subgroupOf R) ↔ (r : G) ∈ classDIn R T := by
  constructor
  · rintro ⟨g, t, ht, ht1, hr⟩
    have hr' : (r : G) = (g : G)⁻¹ * (t : G) * (g : G) := by
      rw [hr]
      rfl
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have ht' : (t : G) = (g : G) * (r : G) * (g : G)⁻¹ := by
      rw [hr']
      group
    refine ⟨fun h1 => ht1 (Subtype.ext ?_), (g : G)⁻¹, R.inv_mem g.2, ?_⟩
    · rw [Subgroup.coe_one, ht', h1]
      group
    · rw [mem_conjSubgroup, inv_inv, hr']
      have e : (g : G) * ((g : G)⁻¹ * (t : G) * (g : G)) * (g : G)⁻¹ = (t : G) := by group
      rw [e]
      exact htT
  · rintro ⟨hr1, x, hx, hxr⟩
    have hxr' : x⁻¹ * (r : G) * x ∈ T := mem_conjSubgroup.1 hxr
    refine ⟨⟨x⁻¹, R.inv_mem hx⟩, ⟨x⁻¹ * (r : G) * x, R.mul_mem (R.mul_mem (R.inv_mem hx) r.2) hx⟩,
      Subgroup.mem_subgroupOf.2 hxr', fun h => hr1 ?_, Subtype.ext ?_⟩
    · have h' : x⁻¹ * (r : G) * x = 1 := congrArg Subtype.val h
      calc (r : G) = x * (x⁻¹ * (r : G) * x) * x⁻¹ := by group
        _ = 1 := by rw [h']; group
    · show (r : G) = (x⁻¹)⁻¹ * (x⁻¹ * (r : G) * x) * x⁻¹
      group

theorem isRootInvolutionSet_classD_subgroupOf
    (h : CFSG.Timmesfeld.IsRootInvolutionSet (classDIn R T)) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classD (T.subgroupOf R)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun d hd => ?_, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact h1 _ (mem_classD_subgroupOf_iff.1 hd)
  · have := h2 _ (mem_classD_subgroupOf_iff.1 hd) _ (mem_classD_subgroupOf_iff.1 he)
    simpa only [← Subgroup.coe_mul, Subgroup.orderOf_coe] using this
  · have h4' : orderOf ((d : G) * (e : G)) = 4 := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact h4
    have := h3 _ (mem_classD_subgroupOf_iff.1 hd) _ (mem_classD_subgroupOf_iff.1 he) h4'
    exact mem_classD_subgroupOf_iff.2 (by simpa [Subgroup.coe_pow, Subgroup.coe_mul] using this)

theorem normalClosure_subgroupOf_eq_top_of_le (hTR : T ≤ R)
    (hgen : R ≤ ⨆ g : R, conjSubgroup (g : G) T) :
    Subgroup.normalClosure ((T.subgroupOf R : Subgroup ↥R) : Set ↥R) = ⊤ := by
  set M := Subgroup.normalClosure ((T.subgroupOf R : Subgroup ↥R) : Set ↥R) with hM
  have hle : ∀ g : R, conjSubgroup (g : G) T ≤ M.map R.subtype := by
    rintro g _ ⟨t, ht, rfl⟩
    refine ⟨g * ⟨t, hTR ht⟩ * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.normalClosure_normal
        (s := ((T.subgroupOf R : Subgroup ↥R) : Set ↥R))).conj_mem _
          (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ht)) g
    · simp [MulAut.conj_apply]
  have hR : R ≤ M.map R.subtype := hgen.trans (iSup_le hle)
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hmy⟩ := hR y.2
  rwa [show m = y from Subtype.ext hmy] at hm

end Classes

section Cards

theorem card_map_mk'_mul_card_inf {H : Type*} [Group H] (S O : Subgroup H) [O.Normal] :
    Nat.card (S.map (QuotientGroup.mk' O)) * Nat.card ↥(S ⊓ O) = Nat.card S := by
  let φ : ↥S →* H ⧸ O := (QuotientGroup.mk' O).comp S.subtype
  have hrange : φ.range = S.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = O.subgroupOf S := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange] at h
  have hc : Nat.card (O.subgroupOf S) = Nat.card ↥(S ⊓ O) := by
    rw [← inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ S ≤ S)).toEquiv
  rw [hc] at h
  rw [mul_comm]
  exact h

end Cards

section PCore

variable {G : Type} [Group G] [Finite G] {R T : Subgroup G}

theorem coe_mem_normalizer_conjSubgroup_of_mem_pCore (hT : IsWC T) (hTR : T ≤ R) {g : G}
    (hg : g ∈ R) {s : ↥R} (hs : s ∈ CFSG.pCore 2 ↥R) :
    (s : G) ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
  pCoreOf_le_normalizer_conjSubgroup hT hTR hg
    ⟨s, hs, rfl⟩

end PCore

end CFSG.CGT.Timmesfeld75
