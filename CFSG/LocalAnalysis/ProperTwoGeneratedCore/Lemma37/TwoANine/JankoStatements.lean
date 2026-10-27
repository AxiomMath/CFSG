module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatementsStepsLate
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Statements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Isolated

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

@[expose] def JankoLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
    IsTwoANine (Subgroup.centralizer ({z} : Set G)) →
    ∀ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) → g * z * g⁻¹ ≠ z → False

theorem noSimpleCentralizerTwoANine_of_jankoLocal (h : JankoLocal) :
    NoSimpleCentralizerTwoANine := by
  intro X _ _ hsimple hnonab t ht hperf hcard he
  obtain ⟨g, hg, hne⟩ := Assembly.exists_conj_commute_ne hsimple hnonab ht
  exact h X t ht ⟨hperf, hcard, he⟩ g hg hne

section Setting

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite G] in
theorem card_centralizer_inf_conj (k a b : G) :
    Nat.card (centralizer ({k * a * k⁻¹} : Set G) ⊓ centralizer ({k * b * k⁻¹} : Set G) :
      Subgroup G) = Nat.card (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) :
      Subgroup G) := by
  rw [centralizer_conj, centralizer_conj, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective]
  exact Subgroup.card_map_of_injective (MulAut.conj k).injective

omit [Finite G] in
theorem zbar_centralizer_eq (hz : orderOf z = 2) (hH : IsTwoANine (centralizer ({z} : Set G))) :
    (zbar (centralizer ({z} : Set G)) : G) = z := by
  refine congrArg Subtype.val (hH.eq_zbar_of_mem_center (z := ⟨z, mem_centralizer_singleton_iff.mpr
    rfl⟩) ?_ fun h => ne_one_of_orderOf_eq_two hz (congrArg Subtype.val h)).symm
  exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

omit [Finite G] in
theorem mem_centralizer_of_mem_normalizer (hz : orderOf z = 2)
    (hH : IsTwoANine (centralizer ({z} : Set G))) (T : Sylow 2 (centralizer ({z} : Set G)))
    {x : G} (hx : x ∈ normalizer (((T : Subgroup _).map (centralizer ({z} : Set G)).subtype :
      Subgroup G) : Set G)) : x ∈ centralizer ({z} : Set G) := by
  have hzT : z ∈ (T : Subgroup _).map (centralizer ({z} : Set G)).subtype :=
    ⟨⟨z, mem_centralizer_singleton_iff.mpr rfl⟩, hH.center_le_sylow T
      (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)),
      rfl⟩
  obtain ⟨w, hwT', hw⟩ := (Subgroup.mem_normalizer_iff.mp hx z).mp hzT
  have hw' : (w : G) = x * z * x⁻¹ := hw
  have hcen := (hH.mem_center_sylow_iff T hwT').mp (Subgroup.mem_center_iff.mpr fun s => by
    refine Subtype.ext (Subtype.ext ?_)
    obtain ⟨c, -, hc⟩ : x⁻¹ * ((s : centralizer ({z} : Set G)) : G) * x ∈
        (T : Subgroup _).map (centralizer ({z} : Set G)).subtype := by
      have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) _).mp ⟨s, s.2, rfl⟩
      rwa [inv_inv] at h
    have hc' : (c : G) = x⁻¹ * ((s : centralizer ({z} : Set G)) : G) * x := hc
    have hcz : (c : G) * z = z * c := mem_centralizer_singleton_iff.mp c.2
    change ((s : centralizer ({z} : Set G)) : G) * w = w * s
    rw [hw', hc'] at *
    calc ((s : centralizer ({z} : Set G)) : G) * (x * z * x⁻¹) =
        x * ((x⁻¹ * s * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by rw [← hc', hcz]
      _ = x * z * x⁻¹ * s := by group)
  rcases hH.mem_center_iff.mp hcen with h | h
  · exfalso
    have h1 : x * z * x⁻¹ = 1 := by rw [← hw', h]; rfl
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact ne_one_of_orderOf_eq_two hz h1
  · have h1 : x * z * x⁻¹ = z := by rw [← hw', h, zbar_centralizer_eq hz hH]
    rw [mem_centralizer_singleton_iff]
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h1]

theorem exists_sylow_le_centralizer (hz : orderOf z = 2)
    (hH : IsTwoANine (centralizer ({z} : Set G))) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ centralizer ({z} : Set G) := by
  set C := centralizer ({z} : Set G)
  obtain ⟨T⟩ : Nonempty (Sylow 2 C) := inferInstance
  set T' : Subgroup G := (T : Subgroup C).map C.subtype
  obtain ⟨Q, hQ⟩ := (T.isPGroup'.map C.subtype).exists_le_sylow
  refine ⟨Q, ?_⟩
  suffices h : T' = Q by rw [← h]; exact Subgroup.map_subtype_le _
  by_contra hne
  have hlt := lt_inf_normalizer_of_lt Q.isPGroup' (lt_of_le_of_ne hQ hne)
  have hle : (Q : Subgroup G) ⊓ normalizer (T' : Set G) ≤ C := fun x hx =>
    mem_centralizer_of_mem_normalizer hz hH T hx.2
  have hR : IsPGroup 2 (((Q : Subgroup G) ⊓ normalizer (T' : Set G)).subgroupOf C) :=
    (Q.isPGroup'.to_inf_left).comap_subtype
  have hTR : (T : Subgroup C) ≤ ((Q : Subgroup G) ⊓ normalizer (T' : Set G)).subgroupOf C :=
    fun c hc => Subgroup.mem_subgroupOf.mpr ⟨hQ ⟨c, hc, rfl⟩, Subgroup.le_normalizer ⟨c, hc, rfl⟩⟩
  have heq := T.is_maximal' hR hTR
  refine hlt.not_ge fun x hx => ⟨⟨x, hle hx⟩, ?_, rfl⟩
  rw [← heq]
  exact Subgroup.mem_subgroupOf.mpr hx

theorem jankoLocal_of_forall_jankoSetting
    (h : ∀ (G : Type) [Group G] [Finite G] (z : G), JankoSetting G z → False) : JankoLocal := by
  intro G _ _ z hz hH g hgz hgne
  set C := centralizer ({z} : Set G)
  have hzbar := zbar_centralizer_eq hz hH
  obtain ⟨Q, hQC⟩ := exists_sylow_le_centralizer hz hH
  have hwC : g * z * g⁻¹ ∈ C := mem_centralizer_singleton_iff.mpr hgz
  have hw2 : orderOf (g * z * g⁻¹) = 2 := by rw [orderOf_conj_eq, hz]
  have hconj : ∀ u : G, orderOf u = 2 → IsConj u z := by
    intro u hu
    obtain ⟨x, hx⟩ := exists_conj_mem_sylow Q hu
    have hux : IsConj u (x * u * x⁻¹) := isConj_iff.mpr ⟨x, rfl⟩
    by_cases hxz : x * u * x⁻¹ = z
    · rwa [hxz] at hux
    have hC := hH.isConj_of_orderOf_eq_two (x := ⟨x * u * x⁻¹, hQC hx⟩) (y := ⟨_, hwC⟩)
      (by rw [Subgroup.orderOf_mk, orderOf_conj_eq, hu]) (by rw [Subgroup.orderOf_mk, hw2])
      (fun h => hxz ((congrArg Subtype.val h).trans hzbar))
      (fun h => hgne ((congrArg Subtype.val h).trans hzbar))
    exact (hux.trans (C.subtype.map_isConj hC)).trans (isConj_iff.mpr ⟨g, rfl⟩).symm
  refine h G z ⟨hz, hH, hzbar, hconj, ?_, fun u hu => ?_⟩
  · have h2 := (Subgroup.relIndex_mul_index hQC).symm ▸ Q.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun hd => h2 (dvd_mul_of_dvd_right hd _))
  · obtain ⟨c, rfl⟩ := isConj_iff.mp (hconj u hu).symm
    exact hH.of_mulEquiv (centralizerConj c z)

end Setting

@[expose] def JankoFrames (G : Type) [Group G] : Prop :=
  ∀ u : G, orderOf u = 2 → Nonempty (JankoFrame G u)

@[expose] def JankoStep7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr

@[expose] def JankoStep9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr →
      ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)

@[expose] def JankoStep10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr →
      ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G) → JankoProp10 fr

@[expose] def JankoStep11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr →
      ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G) → JankoProp10 fr →
        JankoProp11 fr

@[expose] def JankoStep12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr →
      ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G) → JankoProp10 fr →
        JankoProp11 fr → JankoProp12 fr

@[expose] def JankoStepFinal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (fr : JankoFrame G z),
    JankoSetting G z → JankoFrames G → JankoProp7 fr →
      ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G) → JankoProp10 fr →
        JankoProp11 fr → JankoProp12 fr → False

theorem jankoLocal_of_steps (hframe : JankoFrameExists) (h7 : JankoStep7) (h9 : JankoStep9)
    (h10 : JankoStep10) (h11 : JankoStep11) (h12 : JankoStep12) (hfin : JankoStepFinal) :
    JankoLocal := by
  refine jankoLocal_of_forall_jankoSetting fun G _ _ z hset => ?_
  have hfrs : JankoFrames G := fun u hu => hframe G u hu (hset.twoANine_centralizer u hu)
  obtain ⟨fr⟩ := hfrs z hset.orderOf_z
  have p7 := h7 G z fr hset hfrs
  have p9 := h9 G z fr hset hfrs p7
  have p10 := h10 G z fr hset hfrs p7 p9
  have p11 := h11 G z fr hset hfrs p7 p9 p10
  exact hfin G z fr hset hfrs p7 p9 p10 p11 (h12 G z fr hset hfrs p7 p9 p10 p11)

theorem noSimpleCentralizerTwoANine_of_steps (hframe : JankoFrameExists) (h7 : JankoStep7)
    (h9 : JankoStep9) (h10 : JankoStep10) (h11 : JankoStep11) (h12 : JankoStep12)
    (hfin : JankoStepFinal) : NoSimpleCentralizerTwoANine :=
  noSimpleCentralizerTwoANine_of_jankoLocal (jankoLocal_of_steps hframe h7 h9 h10 h11 h12 hfin)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
