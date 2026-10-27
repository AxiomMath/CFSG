module

public import CFSG.FeitThompson.Local.FittingEqualsChiefActionKernel

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem mk_commute_iff {Q0 : Subgroup X} [Q0.Normal] (x y : X) :
    (x : X ⧸ Q0) * (y : X ⧸ Q0) = (y : X ⧸ Q0) * (x : X ⧸ Q0) ↔ x⁻¹ * (y⁻¹ * x * y) ∈ Q0 := by
  rw [← QuotientGroup.eq_one_iff,
    show ((x⁻¹ * (y⁻¹ * x * y) : X) : X ⧸ Q0)
      = (x : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0)⁻¹ * (x : X ⧸ Q0) * (y : X ⧸ Q0)) by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
  constructor
  · intro hcomm
    calc (x : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0)⁻¹ * (x : X ⧸ Q0) * (y : X ⧸ Q0))
        = (x : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0)⁻¹ * ((x : X ⧸ Q0) * (y : X ⧸ Q0))) := by group
      _ = (x : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0) * (x : X ⧸ Q0))) := by rw [hcomm]
      _ = 1 := by group
  · intro hmem
    calc (x : X ⧸ Q0) * (y : X ⧸ Q0)
        = (y : X ⧸ Q0) * ((x : X ⧸ Q0) *
            ((x : X ⧸ Q0)⁻¹ * ((y : X ⧸ Q0)⁻¹ * (x : X ⧸ Q0) * (y : X ⧸ Q0)))) := by group
      _ = (y : X ⧸ Q0) * (x : X ⧸ Q0) := by rw [hmem, mul_one]

theorem mem_ker_conjQuotientAut_iff_mk_mem_centralizer (Q Q0 : Subgroup X) [Q.Normal] [Q0.Normal]
    {y : X} : y ∈ (conjQuotientAut Q Q0).ker ↔
      (y : X ⧸ Q0) ∈ centralizer ((Q.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0)) := by
  rw [mem_ker_conjQuotientAut, mem_centralizer_iff]
  refine ⟨?_, fun hy x hx => (mk_commute_iff x y).1 (hy ((x : X ⧸ Q0)) ⟨x, hx, rfl⟩)⟩
  rintro hy _ ⟨x, hx, rfl⟩
  exact (mk_commute_iff x y).2 (hy x hx)

theorem le_ker_conjQuotientAut_of_commutator_le {Q Q0 A : Subgroup X} [Q.Normal] [Q0.Normal]
    (hle : ⁅Q, A⁆ ≤ Q0) : A ≤ (conjQuotientAut Q Q0).ker := by
  intro a ha
  rw [mem_ker_conjQuotientAut]
  intro x hx
  have h1 : ⁅x⁻¹, a⁻¹⁆ ∈ Q0 :=
    hle (Subgroup.commutator_mem_commutator (Q.inv_mem hx) (A.inv_mem ha))
  rw [commutatorElement_def] at h1
  simpa [mul_assoc] using h1

theorem le_normalizer_of_commutator_le {A T : Subgroup X} (hTA : T ≤ A) (hc : ⁅A, A⁆ ≤ T) :
    A ≤ normalizer (T : Set X) := by
  refine Subgroup.le_normalizer_iff.2 fun a ha t ht => ?_
  have h1 : ⁅a, t⁆ ∈ T := hc (Subgroup.commutator_mem_commutator ha (hTA ht))
  rw [commutatorElement_def] at h1
  rw [show a * t * a⁻¹ = a * t * a⁻¹ * t⁻¹ * t by group]
  exact mul_mem h1 ht

def sectionFixKer (Q0 Y : Subgroup X) [Q0.Normal] (W : Set (X ⧸ Q0)) : Subgroup X :=
  Y ⊓ (centralizer W).comap (mk' Q0)

theorem sectionFixKer_le (Q0 Y : Subgroup X) [Q0.Normal] (W : Set (X ⧸ Q0)) :
    sectionFixKer Q0 Y W ≤ Y := inf_le_left

theorem mem_sectionFixKer_iff {Q0 Y : Subgroup X} [Q0.Normal] {W : Set (X ⧸ Q0)} {y : X} :
    y ∈ sectionFixKer Q0 Y W ↔
      y ∈ Y ∧ ∀ w ∈ W, (y : X ⧸ Q0) * w * (y : X ⧸ Q0)⁻¹ = w := by
  rw [sectionFixKer, Subgroup.mem_inf, Subgroup.mem_comap, mem_centralizer_iff]
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  rw [mk'_apply]
  constructor
  · intro hc
    calc (y : X ⧸ Q0) * w * (y : X ⧸ Q0)⁻¹ = w * (y : X ⧸ Q0) * (y : X ⧸ Q0)⁻¹ := by rw [hc]
      _ = w := by group
  · intro hc
    calc w * (y : X ⧸ Q0) = (y : X ⧸ Q0) * w * (y : X ⧸ Q0)⁻¹ * (y : X ⧸ Q0) := by rw [hc]
      _ = (y : X ⧸ Q0) * w := by group

theorem mem_sectionFixKer_iff_forall_mem {Q Q0 Y : Subgroup X} [Q0.Normal] {W : Set (X ⧸ Q0)}
    (hWQ : W ⊆ ((Q.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0))) {y : X} :
    y ∈ sectionFixKer Q0 Y W ↔
      y ∈ Y ∧ ∀ x ∈ Q, ((x : X ⧸ Q0) ∈ W) → ((y * x * y⁻¹ : X) : X ⧸ Q0) = (x : X ⧸ Q0) := by
  have hkey : ∀ a b : X, ((a * b * a⁻¹ : X) : X ⧸ Q0)
      = (a : X ⧸ Q0) * (b : X ⧸ Q0) * (a : X ⧸ Q0)⁻¹ := by
    intro a b
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mem_sectionFixKer_iff]
  refine and_congr_right fun _ => ⟨fun hy x _ hxW => ?_, fun hy w hw => ?_⟩
  · rw [hkey]; exact hy _ hxW
  · obtain ⟨x, hxQ, hxw⟩ := hWQ hw
    rw [mk'_apply] at hxw
    rw [← hxw, ← hkey]
    exact hy x hxQ (hxw ▸ hw)

theorem sectionFixKer_mono {Q0 Y : Subgroup X} [Q0.Normal] {W W' : Set (X ⧸ Q0)} (hW : W ⊆ W') :
    sectionFixKer Q0 Y W' ≤ sectionFixKer Q0 Y W :=
  inf_le_inf_left _ (Subgroup.comap_mono (Subgroup.centralizer_le hW))

theorem le_sectionFixKer_iff {Q0 Y T : Subgroup X} [Q0.Normal] {W : Set (X ⧸ Q0)} :
    T ≤ sectionFixKer Q0 Y W ↔ T ≤ Y ∧ (T.map (mk' Q0) : Subgroup (X ⧸ Q0)) ≤ centralizer W := by
  rw [sectionFixKer, le_inf_iff, Subgroup.map_le_iff_le_comap]

theorem map_mk'_sectionFixKer_le_centralizer (Q0 Y : Subgroup X) [Q0.Normal] (W : Set (X ⧸ Q0)) :
    ((sectionFixKer Q0 Y W).map (mk' Q0) : Subgroup (X ⧸ Q0)) ≤ centralizer W :=
  (le_sectionFixKer_iff.1 le_rfl).2

theorem le_normalizer_sectionFixKer {Q0 Y A : Subgroup X} [Q0.Normal] {W : Set (X ⧸ Q0)}
    (hAY : A ≤ normalizer (Y : Set X))
    (hAW : (A.map (mk' Q0) : Subgroup (X ⧸ Q0)) ≤ centralizer W) :
    A ≤ normalizer ((sectionFixKer Q0 Y W : Subgroup X) : Set X) := by
  rw [sectionFixKer]
  refine le_normalizer_inf hAY (Subgroup.le_normalizer_iff.2 fun a ha t ht => ?_)
  have haC : a ∈ (centralizer W).comap (mk' Q0) := Subgroup.mem_comap.2 (hAW ⟨a, ha, rfl⟩)
  exact mul_mem (mul_mem haC ht) (inv_mem haC)

theorem sectionFixKer_map_mk'_eq_chiefActionKer (Q Q0 Y : Subgroup X) [Q.Normal] [Q0.Normal] :
    sectionFixKer Q0 Y ((Q.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0))
      = chiefActionKer Q Q0 Y := by
  rw [sectionFixKer, chiefActionKer_eq_inf]
  refine congrArg (Y ⊓ ·) (Subgroup.ext fun y => ?_)
  rw [Subgroup.mem_comap, mk'_apply, ← mem_ker_conjQuotientAut_iff_mk_mem_centralizer]

theorem sectionFixKer_top_map_mk'_eq_ker (Q Q0 : Subgroup X) [Q.Normal] [Q0.Normal] :
    sectionFixKer Q0 ⊤ ((Q.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0))
      = (conjQuotientAut Q Q0).ker := by
  rw [sectionFixKer_map_mk'_eq_chiefActionKer, chiefActionKer_eq_inf, top_inf_eq]

variable {q : ℕ} {Q D K Z : Subgroup X}

namespace IsPrimeFixedSectionSetup

variable (h : IsPrimeFixedSectionSetup X q Q D K Z)
  (hQ0 : Q ⊓ centralizer (D : Set X) < Q)

include h hQ0

theorem commutator_sup_Q_D_le_fittingRaw (hD : Group.IsNilpotent ↥D) :
    haveI := h.finite
    ⁅Q ⊔ D, Q ⊔ D⁆ ≤ fittingRaw X := by
  have := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [fittingRaw_eq_chiefActionKer h hQ0 hD, chiefActionKer_eq_inf, le_inf_iff]
  refine ⟨commutator_self_le _, ?_⟩
  rw [← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, Subgroup.map_sup,
    (Subgroup.map_eq_bot_iff Q).2 (Q_le_ker_conjQuotientAut h hQ0), bot_sup_eq,
    ← Subgroup.map_commutator, (Subgroup.map_eq_bot_iff _).2
      (le_ker_conjQuotientAut_of_commutator_le
        (commutator_commutator_le_inf_centralizer h hQ0))]

theorem not_dvd_natCard_ker_conjQuotientAut :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    ¬ Nat.card ↥K ∣ Nat.card ↥(conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker := by
  have hfin : Finite X := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  have hp : (Nat.card ↥K).Prime := prime_natCard_K h hQ0
  intro hdvd
  have hne := inf_ne_bot_of_dvd_natCard_of_sylow hp
    (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker K
    (h.natCard_K_eq_pow_factorization hp) hdvd
  rw [Ne, Subgroup.eq_bot_iff_forall] at hne
  push Not at hne
  obtain ⟨k, hk, hk1⟩ := hne
  have hkc : (k : X ⧸ (Q ⊓ centralizer (D : Set X))) ∈
      centralizer ((Q.map (mk' (Q ⊓ centralizer (D : Set X))) :
        Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
          Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) :=
    (mem_ker_conjQuotientAut_iff_mk_mem_centralizer Q _).1 hk.1
  have hzp : ((zpowers k).map (mk' (Q ⊓ centralizer (D : Set X))) :
      Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X))))
      = zpowers (k : X ⧸ (Q ⊓ centralizer (D : Set X))) := MonoidHom.map_zpowers _ _
  have hVeq : Q.map (mk' (Q ⊓ centralizer (D : Set X)))
      = Z.map (mk' (Q ⊓ centralizer (D : Set X))) := by
    rw [← inf_centralizer_map_mk'_K_eq h hQ0,
      ← inf_centralizer_map_mk'_singleton_eq h hQ0 hk.2 hk1, hzp]
    exact (inf_eq_left.2 (Subgroup.le_centralizer_iff.1 (zpowers_le.2 hkc))).symm
  have hcard : q ^ Nat.card ↥K = q ^ 1 := by
    rw [pow_one, ← natCard_map_mk'_Q h hQ0, hVeq, natCard_map_mk'_Z h hQ0]
  exact hp.one_lt.ne' (Nat.pow_right_injective h.prime.two_le hcard)

theorem ker_conjQuotientAut_le_sup_Q_D :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker ≤ Q ⊔ D := by
  have hfin : Finite X := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  have := h.normal_sup_Q_D
  exact le_of_index_eq_prime_of_not_dvd (S := (Q ⊔ D : Subgroup X)) (prime_natCard_K h hQ0)
    h.index_sup_Q_D (not_dvd_natCard_ker_conjQuotientAut h hQ0)

theorem fittingRaw_eq_sectionFixKer_top (hD : Group.IsNilpotent ↥D) :
    haveI := h.finite
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    fittingRaw X = sectionFixKer (Q ⊓ centralizer (D : Set X)) ⊤
      ((Q.map (mk' (Q ⊓ centralizer (D : Set X))) :
        Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
          Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) := by
  have := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [sectionFixKer_top_map_mk'_eq_ker, fittingRaw_eq_chiefActionKer h hQ0 hD,
    chiefActionKer_eq_inf, inf_eq_right.2 (ker_conjQuotientAut_le_sup_Q_D h hQ0)]

theorem fittingRaw_eq_sectionFixKer_inf_centralizer_K (hD : Group.IsNilpotent ↥D) :
    haveI := h.finite
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    fittingRaw X = sectionFixKer (Q ⊓ centralizer (D : Set X)) (Q ⊔ D)
      ((Q.map (mk' (Q ⊓ centralizer (D : Set X))) ⊓
        centralizer ((K.map (mk' (Q ⊓ centralizer (D : Set X))) :
          Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
            Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
              Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
                Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) := by
  have := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  set Q0 : Subgroup X := Q ⊓ centralizer (D : Set X) with hQ0def
  set V : Subgroup (X ⧸ Q0) := Q.map (mk' Q0) with hV
  set W : Subgroup (X ⧸ Q0) :=
    V ⊓ centralizer ((K.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0)) with hWdef
  set T : Subgroup X := sectionFixKer Q0 (Q ⊔ D) (W : Set (X ⧸ Q0)) with hT
  have hWV : (W : Set (X ⧸ Q0)) ⊆ (V : Set (X ⧸ Q0)) := inf_le_left
  have hFT : fittingRaw X ≤ T := by
    rw [hT, le_sectionFixKer_iff]
    refine ⟨fittingRaw_le_sup_Q_D h hQ0 hD, le_trans ?_ (Subgroup.centralizer_le hWV)⟩
    rw [fittingRaw_eq_sectionFixKer_top h hQ0 hD]
    exact map_mk'_sectionFixKer_le_centralizer _ _ _
  have hSnorm : (Q ⊔ D : Subgroup X) ≤ normalizer (T : Set X) :=
    le_normalizer_of_commutator_le (sectionFixKer_le _ _ _)
      (le_trans (commutator_sup_Q_D_le_fittingRaw h hQ0 hD) hFT)
  have hKnorm : K ≤ normalizer (T : Set X) := by
    have := h.normal_sup_Q_D
    exact le_normalizer_sectionFixKer (le_normalizer_of_normal K (Q ⊔ D))
      (Subgroup.le_centralizer_iff.1 inf_le_right)
  have hTnormal : T.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.sup_eq_top]
    exact sup_le (le_trans le_sup_left hSnorm)
      (sup_le (le_trans le_sup_right hSnorm) hKnorm)
  have hCVT : V ⊓ centralizer ((T.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0)) = V := by
    have hTVn : (T.map (mk' Q0) : Subgroup (X ⧸ Q0)).Normal := hTnormal.map _ (mk'_surjective _)
    have hVn : V.Normal := normal_map_mk' h hQ0
    have hn : (V ⊓ centralizer ((T.map (mk' Q0) : Subgroup (X ⧸ Q0)) :
        Set (X ⧸ Q0))).Normal := inferInstance
    have hWle : W ≤ V ⊓ centralizer ((T.map (mk' Q0) : Subgroup (X ⧸ Q0)) : Set (X ⧸ Q0)) :=
      le_inf inf_le_left (Subgroup.le_centralizer_iff.1
        (map_mk'_sectionFixKer_le_centralizer Q0 (Q ⊔ D) (W : Set (X ⧸ Q0))))
    have hWne : W ≠ ⊥ := by
      rw [hWdef, hV, inf_centralizer_map_mk'_K_eq h hQ0, Ne,
        ← Subgroup.card_eq_one, natCard_map_mk'_Z h hQ0]
      exact h.prime.one_lt.ne'
    by_contra hne
    exact hWne (le_bot_iff.1 (le_trans hWle
      (le_of_eq (forall_normal_lt_map_mk'_eq_bot h hQ0 _ hn
        (lt_of_le_of_ne inf_le_left hne)))))
  refine le_antisymm hFT ?_
  rw [fittingRaw_eq_sectionFixKer_top h hQ0 hD, le_sectionFixKer_iff]
  exact ⟨le_top, Subgroup.le_centralizer_iff.1 (le_trans (le_of_eq hCVT.symm) inf_le_right)⟩

end IsPrimeFixedSectionSetup

end CFSG.FeitThompson
