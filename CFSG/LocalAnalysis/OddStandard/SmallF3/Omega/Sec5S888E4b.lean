module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X} {E : Subgroup X}

private abbrev s888N (V : Subgroup X) : Subgroup X := normalizer (V : Set X)

private abbrev s888E' (V : Subgroup X) (E : Subgroup X) : Subgroup (s888N V) :=
  E.subgroupOf (s888N V)

private noncomputable abbrev s888K (V : Subgroup X) (W : Fin 4 → Subgroup X) (E : Subgroup X)
    (hS : PlaneSys V W) : Subgroup (s888E' V E) :=
  ((planeHom hS).domRestrict (s888E' V E)).ker

private theorem s888_mem_centralizer_of_suppVec_eq_zero (hS : PlaneSys V W)
    (y : s888N V) (hy : suppVec W y = 0) :
    (y : X) ∈ centralizer (V : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcentral : ∀ v ∈ V, (y : X) * v = v * (y : X) := by
    rw [centralizes_V_iff hS y]
    intro i w hw
    have hnot : ¬ ActsNontriv (W i) (y : X) := by
      have h := congrFun hy i
      simp only [Pi.zero_apply, suppVec] at h
      by_contra hc
      rw [if_pos hc] at h
      exact one_ne_zero h
    have hconj := (not_actsNontriv_iff (A := W i) (y := (y : X))).mp hnot w hw
    rwa [mul_inv_eq_iff_eq_mul] at hconj
  exact (hcentral v hv).symm

private theorem s888_suppVec_eq_zero_of_mem_centralizer (hS : PlaneSys V W)
    (y : s888N V) (hy : (y : X) ∈ centralizer (V : Set X)) :
    suppVec W y = 0 := by
  funext i
  have hnot : ¬ ActsNontriv (W i) (y : X) := by
    rw [not_actsNontriv_iff]
    intro a ha
    have hcomm := (Subgroup.mem_centralizer_iff.mp hy) a (hS.le i ha)
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  simp [suppVec, hnot]

private noncomputable def s888_suppHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    s888K V W E hS →* Multiplicative (Fin 4 → ZMod 2) :=
  MonoidHom.mk' (fun k => Multiplicative.ofAdd (suppVec W ((k : s888E' V E) : s888N V))) (by
    intro k l
    have hk : (((k : s888E' V E) : s888N V) : X) ∈ E := (k : s888E' V E).2
    have hl : (((l : s888E' V E) : s888N V) : X) ∈ E := (l : s888E' V E).2
    have hk1 : planeHom hS ((k : s888E' V E) : s888N V) = 1 := by
      have h := MonoidHom.mem_ker.mp k.2
      rwa [MonoidHom.domRestrict_apply] at h
    have hl1 : planeHom hS ((l : s888E' V E) : s888N V) = 1 := by
      have h := MonoidHom.mem_ker.mp l.2
      rwa [MonoidHom.domRestrict_apply] at h
    have hsupp := suppVec_mul hS hE hk hl hk1 hl1
    simp only [Subgroup.coe_mul]
    rw [hsupp]
    rfl)

private theorem s888_range_suppHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    ((s888_suppHom hS hE).range : Set (Multiplicative (Fin 4 → ZMod 2))) =
      Multiplicative.ofAdd '' (suppSet hS E : Set (Fin 4 → ZMod 2)) := by
  ext m
  rw [SetLike.mem_coe, MonoidHom.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨suppVec W ((k : s888E' V E) : s888N V), ?_, rfl⟩
    rw [Finset.mem_coe, mem_suppSet]
    exact ⟨((k : s888E' V E) : s888N V), (k : s888E' V E).2,
      (by have h := MonoidHom.mem_ker.mp k.2; rwa [MonoidHom.domRestrict_apply] at h), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    rw [Finset.mem_coe, mem_suppSet] at hc
    obtain ⟨y, hy, hy1, rfl⟩ := hc
    have hy' : y ∈ s888E' V E := by rwa [Subgroup.mem_subgroupOf]
    exact ⟨⟨⟨y, hy'⟩, by rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]; exact hy1⟩, rfl⟩

private theorem s888_card_range_suppHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card (s888_suppHom hS hE).range = (suppSet hS E).card := by
  rw [show Nat.card (s888_suppHom hS hE).range =
      Nat.card (((s888_suppHom hS hE).range : Set (Multiplicative (Fin 4 → ZMod 2))))
      from rfl]
  rw [s888_range_suppHom hS hE]
  rw [Nat.card_image_of_injective Multiplicative.ofAdd.injective]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Finset.toFinset_coe]

private noncomputable def s888_kerEquiv (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    (s888_suppHom hS hE).ker ≃ ↥(E ⊓ centralizer (V : Set X)) where
  toFun k :=
    ⟨k.1.1.1.1, by
      refine ⟨k.1.1.2, ?_⟩
      apply s888_mem_centralizer_of_suppVec_eq_zero hS k.1.1.1
      have hk : s888_suppHom hS hE k.1 = 1 := MonoidHom.mem_ker.mp k.2
      simpa only [s888_suppHom, MonoidHom.mk'_apply, ofAdd_eq_one] using hk⟩
  invFun z := by
    have hzE : (z : X) ∈ E := z.2.1
    have hzC : (z : X) ∈ centralizer (V : Set X) := z.2.2
    let y : s888N V := ⟨(z : X), hE.le_normalizer hzE⟩
    have hyE : y ∈ s888E' V E := by rw [Subgroup.mem_subgroupOf]; exact hzE
    refine ⟨⟨⟨y, hyE⟩, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      apply planeHom_eq_one_of_centralizes hS
      intro v hv
      rw [mul_inv_eq_iff_eq_mul]
      exact ((Subgroup.mem_centralizer_iff.mp hzC) v hv).symm
    · change Multiplicative.ofAdd (suppVec W y) = 1
      rw [ofAdd_eq_one]
      exact s888_suppVec_eq_zero_of_mem_centralizer hS y hzC
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

private theorem s888_card_ker_suppHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card (s888_suppHom hS hE).ker = Nat.card ↥(E ⊓ centralizer (V : Set X)) :=
  Nat.card_congr (s888_kerEquiv hS hE)

private theorem s888_range_planeHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    (((planeHom hS).domRestrict (s888E' V E)).range : Set (Equiv.Perm (Fin 4))) =
      (planeImage hS E : Set (Equiv.Perm (Fin 4))) := by
  ext a
  rw [SetLike.mem_coe, MonoidHom.mem_range]
  rw [Finset.mem_coe, mem_planeImage]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : s888N V), (k : s888E' V E).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem s888_card_range_planeHom (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card ((planeHom hS).domRestrict (s888E' V E)).range = (planeImage hS E).card := by
  rw [show Nat.card ((planeHom hS).domRestrict (s888E' V E)).range =
      Nat.card ((((planeHom hS).domRestrict (s888E' V E)).range : Set (Equiv.Perm (Fin 4))))
      from rfl]
  rw [s888_range_planeHom hS hE]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Finset.toFinset_coe]

private noncomputable def s888_subgroupOfEquiv :
    (centralizer (V : Set X)).subgroupOf E ≃ ↥(E ⊓ centralizer (V : Set X)) where
  toFun y := ⟨((y : E) : X), (y : E).2, y.2⟩
  invFun z := ⟨⟨(z : X), z.2.1⟩, z.2.2⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

private theorem s888_card_subgroupOf_centralizer :
    Nat.card ((centralizer (V : Set X)).subgroupOf E) =
      Nat.card ↥(E ⊓ centralizer (V : Set X)) :=
  Nat.card_congr s888_subgroupOfEquiv

theorem card_eq_planeImage_mul [Finite X] (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card E = (planeImage hS E).card * (suppSet hS E).card *
      Nat.card ↥(E ⊓ centralizer (V : Set X)) := by
  have h1 := Subgroup.card_ker_mul_card_range ((planeHom hS).domRestrict (s888E' V E))
  have h2 := Subgroup.card_ker_mul_card_range (s888_suppHom hS hE)
  have h3 : Nat.card (s888E' V E) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le_normalizer).toEquiv
  have h4 := s888_card_range_planeHom (V := V) (W := W) (E := E) hS hE
  have h5 := s888_card_range_suppHom (V := V) (W := W) (E := E) hS hE
  have h6 := s888_card_ker_suppHom (V := V) (W := W) (E := E) hS hE
  rw [← h3, ← h1, ← h2, h6, h5, h4]
  ring

theorem relIndex_centralizer_eq [Finite X] (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    (centralizer (V : Set X)).relIndex E = (planeImage hS E).card * (suppSet hS E).card := by
  have hcard := card_eq_planeImage_mul (V := V) (W := W) (E := E) hS hE
  have hNpos : 0 < Nat.card ↥(E ⊓ centralizer (V : Set X)) := Nat.card_pos
  have hindex : Nat.card ↥(E ⊓ centralizer (V : Set X)) *
      (centralizer (V : Set X)).relIndex E = Nat.card E := by
    rw [Subgroup.relIndex]
    rw [← Subgroup.card_mul_index ((centralizer (V : Set X)).subgroupOf E)]
    rw [s888_card_subgroupOf_centralizer (V := V) (E := E)]
  rw [hcard] at hindex
  rw [mul_comm ((planeImage hS E).card * (suppSet hS E).card)] at hindex
  exact mul_left_cancel₀ hNpos.ne' hindex

end CFSG.OddStandard.SmallF3.Omega
