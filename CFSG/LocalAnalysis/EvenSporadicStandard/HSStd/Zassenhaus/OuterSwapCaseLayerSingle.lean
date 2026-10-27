module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerTheta

public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Single

variable {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ} {τ : Γ} {K : Subgroup Γ}

theorem SwapOrbit.single_le (hK : SwapOrbit J τ K) (hcj : PartA.cj τ K = K) : J ≤ K := by
  have := hK.le
  rwa [hcj, sup_idem] at this

omit [Finite Γ] in
theorem SwapOrbit.single_inv (hcj : PartA.cj τ K = K) : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K := by
  intro x hx
  have := mem_cj_mk (g := τ) hx
  rwa [hcj] at this

theorem eq_one_of_comm_alt8 {J : Subgroup Γ} (e : ↥J ≃* alternatingGroup (Fin 8)) {x : Γ}
    (hx : x ∈ J) (h : ∀ j ∈ J, j * x = x * j) : x = 1 := by
  have hc : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have h1 : e ⟨x, hx⟩ ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h y y.2)
  rw [hc, Subgroup.mem_bot] at h1
  have : (⟨x, hx⟩ : ↥J) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

theorem commutator_eq_self_of_isComponent {K : Subgroup Γ} (hK : IsComponent K) : ⁅K, K⁆ = K := by
  have hperf : commutator ↥K = ⊤ := hK.1.1.1
  have h2 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, hperf, Subgroup.map_top, Subgroup.range_subtype]

theorem SwapX.tauAut_ne_one (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K) (hcj : PartA.cj τ K = K)
    (hall : ∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) :
    tauAut K hX.sq (SwapOrbit.single_inv hcj) ≠ 1 := by
  intro h1
  have hc : ∀ q ∈ K, q * τ = τ * q := by
    intro q hq
    have h := congrArg (fun f : MulAut ↥K => ((f ⟨q, hq⟩ : ↥K) : Γ)) h1
    simp only [tauAut_apply, MulAut.one_apply] at h
    calc q * τ = (τ * q * τ⁻¹) * τ := by rw [h]
      _ = τ * q := by group
  have hKJ : K ≤ J := hX.perfect_le hc (commutator_eq_self_of_isComponent hK.comp)
  have hJK : J = K := le_antisymm (hK.single_le hcj) hKJ
  apply hX.not_normal
  rw [hJK]
  exact normal_single_of_cj hcj hall

@[expose] def tauQuot {X : Type*} [Group X] {τ : X} (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) : MulAut (↥K ⧸ center ↥K) :=
  sylowQuotAut (tauAut K ht2 hK)

theorem tauQuot_mk {X : Type*} [Group X] {τ : X} (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) (x : ↥K) :
    tauQuot K ht2 hK (x : ↥K ⧸ center ↥K) = ((⟨τ * x * τ⁻¹, hK x x.2⟩ : ↥K) : ↥K ⧸ center ↥K) :=
  rfl

theorem tauQuot_sq {X : Type*} [Group X] {τ : X} (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) : tauQuot K ht2 hK * tauQuot K ht2 hK = 1 :=
  sylowQuotAut_sq _ (tauAut_sq K ht2 hK)

theorem SwapX.single_hyps (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K) (hcj : PartA.cj τ K = K)
    (hall : ∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) :
    IsSimpleGroup (↥K ⧸ center ↥K) ∧
      tauQuot K hX.sq (SwapOrbit.single_inv hcj) * tauQuot K hX.sq (SwapOrbit.single_inv hcj) = 1 ∧
      tauQuot K hX.sq (SwapOrbit.single_inv hcj) ≠ 1 ∧
      Nat.card (autCentralizer (tauQuot K hX.sq (SwapOrbit.single_inv hcj))) ≤ 161280 ∧
      ∃ D : Subgroup ↥(autCentralizer (tauQuot K hX.sq (SwapOrbit.single_inv hcj))),
        D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧
        ∀ x : ↥(autCentralizer (tauQuot K hX.sq (SwapOrbit.single_inv hcj))),
          ∃ n : ℕ, x ^ (2 ^ n) ∈ D := by
  have hinv := SwapOrbit.single_inv hcj
  set σ := tauAut K hX.sq hinv with hσ
  have hperf : commutator ↥K = ⊤ := hK.comp.1.1.1
  have hJK : J ≤ K := hK.single_le hcj
  obtain ⟨e⟩ := hX.alt8
  refine ⟨hK.comp.1.2.1, tauQuot_sq K hX.sq hinv, ?_, ?_, ?_⟩
  · intro h
    exact hX.tauAut_ne_one hK hcj hall (eq_one_of_sylowQuotAut_eq_one hperf σ h)
  · have h1 := card_autCentralizer_sylowQuotAut_le σ
    have h2 : Nat.card (autCentralizer σ) ≤ 161280 := by
      rw [hσ, card_autCentralizer_tauAut K hX.sq hinv]
      exact (Subgroup.card_le_of_le inf_le_right).trans hX.card_le
    exact h1.trans h2
  ·
    refine theta_hyps σ (isPGroup_center_component hX.oddCore hK.comp) (J.subgroupOf K) ?_ ?_ ?_ ?_ ?_
      ((Subgroup.subgroupOfEquivOfLe hJK).trans e)
    · rintro j hj
      have hjJ : ((j : ↥K) : Γ) ∈ J := hj
      apply Subtype.ext
      show τ * (j : Γ) * τ⁻¹ = j
      rw [← hX.cent _ hjJ]
      group
    · have h1 : (⁅J.subgroupOf K, J.subgroupOf K⁆).map K.subtype = J := by
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJK]
        exact hX.perfect
      have h2 : (J.subgroupOf K).map K.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJK
      exact Subgroup.map_injective K.subtype_injective (h1.trans h2.symm)
    · rw [eq_bot_iff]
      rintro x ⟨hxJ, hxZ⟩
      have hxJ' : ((x : ↥K) : Γ) ∈ J := hxJ
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      refine eq_one_of_comm_alt8 e hxJ' fun j hj => ?_
      have := mem_center_iff.1 hxZ ⟨j, hJK hj⟩
      exact congrArg Subtype.val this
    · intro Q hQσ hQp
      have hQ' : ⁅Q.map K.subtype, Q.map K.subtype⁆ = Q.map K.subtype := by
        rw [← Subgroup.map_commutator, hQp]
      have hQt : ∀ q ∈ Q.map K.subtype, q * τ = τ * q := by
        rintro _ ⟨q, hq, rfl⟩
        have h := congrArg (fun y : ↥K => (y : Γ)) (hQσ q hq)
        simp only [hσ, tauAut_apply] at h
        calc (q : Γ) * τ = (τ * q * τ⁻¹) * τ := by rw [h]
          _ = τ * q := by group
      intro q hq
      exact hX.perfect_le hQt hQ' ⟨q, hq, rfl⟩
    · intro w hw
      have h := congrArg (fun y : ↥K => (y : Γ)) hw
      simp only [hσ, tauAut_apply] at h
      have hwt : (w : Γ) * τ = τ * w := by
        calc (w : Γ) * τ = (τ * w * τ⁻¹) * τ := by rw [h]
          _ = τ * w := by group
      exact hX.sq_mem w hwt

end Single

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
