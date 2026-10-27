module

public import CFSG.CGT.Timmesfeld75.Sec5Nine

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] {T L₁ : Subgroup G}

theorem normal_subgroupOf_hSub (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    (T.subgroupOf (hSub T L₁)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer left_le_hSub).2 (hSub_le_normalizer hL₁)

@[expose] def hToHBar (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    ↥(hSub T L₁) →* ↥(hBar T L₁) where
  toFun h := ⟨barElt T (hSub_le_normalizer hL₁ h.2), barElt_mem_hBar hL₁ _ h.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem hToHBar_surjective (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    Function.Surjective (hToHBar hL₁) := by
  rintro ⟨y, hy⟩
  obtain ⟨u, hu, huH, rfl⟩ := exists_mem_hSub_of_mem_hBar hL₁ hy
  exact ⟨⟨u, huH⟩, rfl⟩

theorem hToHBar_ker (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    (hToHBar hL₁).ker = T.subgroupOf (hSub T L₁) := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    exact (barElt_eq_one_iff (hSub_le_normalizer hL₁ h.2)).1 (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext ((barElt_eq_one_iff (hSub_le_normalizer hL₁ h.2)).2 h1)

@[expose] noncomputable def isoHBar [(T.subgroupOf (hSub T L₁)).Normal]
    (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    ↥(hSub T L₁) ⧸ T.subgroupOf (hSub T L₁) ≃* ↥(hBar T L₁) :=
  (QuotientGroup.quotientMulEquivOfEq (hToHBar_ker hL₁).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hToHBar_surjective hL₁))

theorem isoHBar_mk [(T.subgroupOf (hSub T L₁)).Normal]
    (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) (h : ↥(hSub T L₁)) :
    isoHBar hL₁ (QuotientGroup.mk h) = hToHBar hL₁ h := rfl

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := Subgroup.mem_center_iff.1 ha
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨g', rfl⟩ := e.surjective g
    show e g' * e a = e a * e g'
    rw [← map_mul, ← map_mul, ha' g']
  · intro hb
    have hb' := Subgroup.mem_center_iff.1 hb
    refine ⟨e.symm b, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hb' (e g)

theorem naturalSL_of (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {n m : ℕ}
    (e : ↥(hBar T L₁) ≃* SL(n, GaloisField 2 m))
    (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m))
    (hcompat : ∀ (y : ↥(hBar T L₁)) (v : ↥T), φ (actHBar T L₁ hTc y v) =
      Multiplicative.ofAdd (((e y : SL(n, GaloisField 2 m)) :
        Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ v)))) :
    NaturalSL T (hSub T L₁) n m := by
  have hN := normal_subgroupOf_hSub hL₁
  refine ⟨hN, (isoHBar hL₁).trans e, φ, fun h t hmem => ?_⟩
  have h1 := hcompat (hToHBar hL₁ h) t
  have h2 : actHBar T L₁ hTc (hToHBar hL₁ h) t = ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ :=
    Subtype.ext rfl
  rw [h2] at h1
  rw [MulEquiv.trans_apply, isoHBar_mk]
  exact h1

theorem isHatA_of (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) {k : ℕ}
    (hperf : commutator ↥(hBar T L₁) = ⊤) (hZ : Nat.card (Subgroup.center ↥(hBar T L₁)) ∣ 3)
    (hK : Nonempty (↥(hBar T L₁) ⧸ Subgroup.center ↥(hBar T L₁) ≃* alternatingGroup (Fin k))) :
    haveI := normal_subgroupOf_hSub hL₁
    IsHatA k (↥(hSub T L₁) ⧸ T.subgroupOf (hSub T L₁)) := by
  have := normal_subgroupOf_hSub hL₁
  set ι := isoHBar hL₁ with hι
  have hmap : (Subgroup.center (↥(hSub T L₁) ⧸ T.subgroupOf (hSub T L₁))).map ι.toMonoidHom =
      Subgroup.center ↥(hBar T L₁) := map_center_mulEquiv ι
  refine ⟨?_, Subgroup.center _, le_rfl, ?_, inferInstance, ?_⟩
  · apply Subgroup.map_injective (f := ι.toMonoidHom) ι.injective
    rw [show commutator (↥(hSub T L₁) ⧸ T.subgroupOf (hSub T L₁)) =
      ⁅(⊤ : Subgroup (↥(hSub T L₁) ⧸ T.subgroupOf (hSub T L₁))), ⊤⁆ from rfl,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ ι.surjective]
    exact hperf
  · rw [← Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective, hmap]
    exact hZ
  · obtain ⟨f⟩ := hK
    exact ⟨(QuotientGroup.congr _ _ ι hmap).trans f⟩

end CFSG.CGT.Timmesfeld75
