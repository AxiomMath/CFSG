module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cls3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Excl

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem conjR_mul_of_S {Y : Subgroup G} {x s : G} (hx : x ∈ normalizer (S : Set G)) (hs : s ∈ S)
    (hY : ∀ s' ∈ S, conjR Y s' = Y) : conjR Y (x * s) = conjR Y x := by
  have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hx s).1 hs
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← Dbl.conjR_conjR, hY _ hxs]

omit [Finite G] in
theorem conjR_blockU0_of_S {s : G} (hs : s ∈ S) : conjR (blockU0 S L) s = blockU0 S L :=
  C5.conjSubgroup_eq_self (C56.S_le_normalizer_conjJoin (blockU L) hs)

omit [Finite G] in
theorem conjR_baumD_of_S {s : G} (hs : s ∈ S) : conjR (baumD S L) s = baumD S L := by
  show conjSubgroup (baum S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G)) s = _
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer,
    C5.conjSubgroup_eq_self (C56.S_le_normalizer_conjJoin L hs),
    C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hs))]
  rfl

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem exists_good {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    ∃ x ∈ M₀, x ∉ S ∧ ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥ := by
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x, hxM, hxS⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have hxN : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM h2 hxM
  have hnot := C56.not_conj_le_of_mem_diff D.hcs hSM hMT h2 hxM hxS
  have hVS : conjR (blockU L) x ≤ S := by
    have := C5.conjSubgroup_mono D.blockU_le_S x
    rwa [C5.conjSubgroup_eq_self hxN] at this
  have hVc : ¬ conjR (blockU L) x ≤ centralizer ((U0 L t : Subgroup G) : Set G) := by
    intro h
    apply hnot
    intro v hv
    rw [← D.campbell_pkg.2.2.2]
    exact Subgroup.mem_inf.2 ⟨hVS hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subgroup.mem_centralizer_iff.1 (h hv) u hu⟩
  obtain ⟨v, hv, hvc⟩ : ∃ v ∈ conjR (blockU L) x,
      v ∉ centralizer ((U0 L t : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hVc hcon
  obtain ⟨u, hu, hnc⟩ : ∃ u ∈ U0 L t, ¬ u * v = v * u := by
    by_contra hcon
    push Not at hcon
    exact hvc (Subgroup.mem_centralizer_iff.2 hcon)
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_U0 hu
  by_cases hav : a * v = v * a
  ·
    have hbv : ¬ b * v = v * b := by
      intro hbv
      apply hnc
      calc a * b * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [hbv]
        _ = (a * v) * b := by group
        _ = (v * a) * b := by rw [hav]
        _ = v * (a * b) := by group
    refine ⟨x * t⁻¹, M₀.mul_mem hxM (M₀.inv_mem (hSM D.ht)), ?_, ?_⟩
    · intro h
      apply hxS
      have := S.mul_mem h D.ht
      simpa using this
    · intro hbot
      have h1 : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
        have e : conjR ⁅blockU2 L t, conjR (blockU L) x⁆ t⁻¹ =
            ⁅blockU L, conjR (blockU L) (x * t⁻¹)⁆ := by
          have e1 : conjR ⁅blockU2 L t, conjR (blockU L) x⁆ t⁻¹ =
              ⁅conjR (blockU2 L t) t⁻¹, conjR (conjR (blockU L) x) t⁻¹⁆ :=
            C5.conjSubgroup_commutator _ _ t⁻¹
          rw [e1, show conjR (blockU2 L t) t⁻¹ = blockU L from Dbl.conjR_conjR_inv (blockU L) t,
            Dbl.conjR_conjR]
        rw [hbot] at e
        exact Lin2.conjR_eq_bot_iff.1 e
      have hc : b ∈ centralizer (conjR (blockU L) x : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hb
      exact hbv (Subgroup.mem_centralizer_iff.1 hc v hv).symm
  · refine ⟨x, hxM, hxS, fun hbot => ?_⟩
    apply hav
    have hc : a ∈ centralizer (conjR (blockU L) x : Set G) := by
      have : blockU L ≤ centralizer (conjR (blockU L) x : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact this ha
    exact (Subgroup.mem_centralizer_iff.1 hc v hv).symm

end Dbl

theorem c56DoubleA5 :
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
      IsAltType L 5 → conjJoin S L ≠ L →
      ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀ := by
  intro G _ _ T M H S L hcs h5 hne M₀ hSM hMT h2
  obtain ⟨t, ⟨D⟩⟩ := exists_dbl hcs h5 hne
  obtain ⟨x₁, hx₁M, hx₁S, hgood⟩ := D.exists_good hSM hMT h2
  have hx₁N : x₁ ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM h2 hx₁M
  obtain ⟨C⟩ := D.nonempty_cfg
  obtain ⟨C'⟩ := D.swap.nonempty_cfg
  let X : Two T M H S L t x₁ := ⟨C, C', hx₁N, hgood, M₀, hSM, hMT, h2, hx₁M, hx₁S⟩
  refine ⟨X.blockU0_eq_pCoreOf, ?_, X.baumD_eq_blockD, X.pCoreOf_eq, X.pCoreOf_isMax,
    X.thompsonJ_eq_baum.symm, ?_⟩
  · rw [X.baumD_eq_blockD]
    exact X.blockD_isElemAbelian
  · intro x hxM hxS
    have hs : x₁⁻¹ * x ∈ S := inv_mul_mem_of_relIndex_two h2 hx₁M hx₁S hxM hxS
    have hxe : x₁ * (x₁⁻¹ * x) = x := by group
    have hU : conjR (blockU0 S L) x = conjR (blockU0 S L) x₁ := by
      have := conjR_mul_of_S hx₁N hs (fun s' hs' => conjR_blockU0_of_S (L := L) hs')
      rwa [hxe] at this
    have hDx : conjR (baumD S L) x = conjR (baumD S L) x₁ := by
      have := conjR_mul_of_S hx₁N hs (fun s' hs' => conjR_baumD_of_S (L := L) hs')
      rwa [hxe] at this
    refine ⟨?_, ?_, fun h => absurd h hne, fun h => absurd h hne, fun _ A hA => ?_⟩
    · rw [hDx]
      exact X.baumD_inf_conj
    · rw [hU]
      exact X.baum_eq
    · rw [hU]
      exact X.invariant_isMax_iff hA

end CFSG.QuasithinUnique.AppCS2
