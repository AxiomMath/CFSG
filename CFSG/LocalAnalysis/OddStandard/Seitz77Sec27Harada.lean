module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27HaradaLocal
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndBalanced
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs
public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint CFSG.OddStandard Equiv Equiv.Perm

variable {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}

theorem exists_E8_two_part (c : Local27 N X t) :
    ∃ E : Subgroup N, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      ∀ g : N, g ∈ centralizer (E : Set N) → IsPGroup 2 (zpowers g) → g ∈ E := by
  obtain ⟨e⟩ := c.exists_equiv_alt
  have htt := c.t_mul_t
  have hVt : ∀ v ∈ kleinIn e, ∀ s ∈ zpowers t, v * s = s * v := by
    intro v hv s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
    exact (Commute.zpow_right (c.t_cent v (kleinIn_le e hv)) k).eq
  have hVinf : kleinIn e ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy, hyt⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt hyt with rfl | rfl
    · exact one_mem _
    · exact absurd (kleinIn_le e hy) c.t_not_mem_X
  have hcard : Nat.card ↥(kleinIn e ⊔ zpowers t) = 8 := by
    rw [card_sup_of_commute hVt hVinf, card_kleinIn, Nat.card_zpowers, c.t_order]
  have hcomm : ∀ x ∈ kleinIn e ⊔ zpowers t, ∀ y ∈ kleinIn e ⊔ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_iff_of_commute hVt x).1 hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_commute hVt y).1 hy
    have hbb : Commute b₁ b₂ := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb₁
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb₂
      exact Commute.zpow_zpow_self t k m
    have hab₁ : Commute a₁ b₂ := hVt a₁ ha₁ b₂ hb₂
    have hba₂ : Commute b₁ a₂ := (hVt a₂ ha₂ b₁ hb₁).symm
    have haa : Commute a₁ a₂ := mul_comm_of_mem_kleinIn e ha₁ ha₂
    exact ((haa.mul_right hab₁).mul_left (hba₂.mul_right hbb)).eq
  have hsq : ∀ x ∈ kleinIn e ⊔ zpowers t, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hVt x).1 hx
    have hbb : b * b = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt hb with rfl | rfl
      · exact one_mul 1
      · exact htt
    have haa : a * a = 1 := mul_self_of_mem_kleinIn e ha
    have hba : Commute b a := (hVt a ha b hb).symm
    calc a * b * (a * b) = (a * a) * (b * b) := hba.mul_mul_mul_comm a b
      _ = 1 := by rw [haa, hbb, one_mul]
  refine ⟨kleinIn e ⊔ zpowers t, ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => by
    rw [pow_two]; exact hsq x hx⟩, hcard, ?_⟩
  intro g hg hg2
  have hgE : ∀ x ∈ kleinIn e ⊔ zpowers t, x * g = g * x := mem_centralizer_iff.1 hg
  have htg : t * g = g * t := hgE t (mem_sup_right (mem_zpowers t))
  have hgH : g ∈ centralizer ({t} : Set N) := mem_centralizer_singleton_iff.2 htg.symm
  let gM : normalizer (X : Set N) := ⟨g, c.centralizer_t_le_normalizer hgH⟩
  have hρ : ∀ w : alternatingGroup (Fin 5), (w : Perm (Fin 5)) ∈ kleinFive →
      rhoOf e gM * (w : Perm (Fin 5)) = (w : Perm (Fin 5)) * rhoOf e gM := by
    intro w hw
    have hv : altIncl e w ∈ kleinIn e := (mem_kleinIn_iff e).2 ⟨w, hw, rfl⟩
    have hvg : altIncl e w * g = g * altIncl e w := hgE _ (mem_sup_left hv)
    let vM : normalizer (X : Set N) := ⟨altIncl e w, le_normalizer (altIncl_mem e w)⟩
    have h1 : vM * gM = gM * vM := Subtype.ext hvg
    have h2 := congrArg (rhoOf e) h1
    rw [map_mul, map_mul, show rhoOf e vM = (w : Perm (Fin 5)) from rhoOf_altIncl e w] at h2
    exact h2.symm
  have hσ : rhoOf e gM ∈ kleinFive :=
    mem_kleinFive_of_commute
      (hρ ⟨pairA, kleinFive_le_alternatingGroup pairA_mem_kleinFive⟩ pairA_mem_kleinFive)
      (hρ ⟨pairB, kleinFive_le_alternatingGroup pairB_mem_kleinFive⟩ pairB_mem_kleinFive)
  obtain ⟨w₀, hw₀, hrho⟩ : ∃ w₀ : alternatingGroup (Fin 5), (w₀ : Perm (Fin 5)) ∈ kleinFive ∧
      (w₀ : Perm (Fin 5)) = rhoOf e gM :=
    ⟨⟨rhoOf e gM, kleinFive_le_alternatingGroup hσ⟩, hσ, rfl⟩
  have hv₀E : altIncl e w₀ ∈ kleinIn e := (mem_kleinIn_iff e).2 ⟨w₀, hw₀, rfl⟩
  let v₀M : normalizer (X : Set N) := ⟨altIncl e w₀, le_normalizer (altIncl_mem e w₀)⟩
  have hker : gM * v₀M⁻¹ ∈ (rhoOf e).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      show rhoOf e v₀M = (w₀ : Perm (Fin 5)) from rhoOf_altIncl e w₀, hrho, mul_inv_cancel]
  rw [rhoOf_ker, mem_subgroupOf] at hker
  have hrC : g * (altIncl e w₀)⁻¹ ∈ centralizer (X : Set N) := hker
  have hv₀X : altIncl e w₀ ∈ X := kleinIn_le e hv₀E
  have hrH : g * (altIncl e w₀)⁻¹ ∈ centralizer ({t} : Set N) :=
    Subgroup.mul_mem _ hgH (Subgroup.inv_mem _ (c.X_le_centralizer_t hv₀X))
  have hv₀2 : IsPGroup 2 (zpowers (altIncl e w₀)) :=
    isPGroup_zpowers_of_mul_self (mul_self_of_mem_kleinIn e hv₀E)
  have hcom : g * (altIncl e w₀)⁻¹ = (altIncl e w₀)⁻¹ * g := by
    have := hgE _ (mem_sup_left hv₀E)
    calc g * (altIncl e w₀)⁻¹ = (altIncl e w₀)⁻¹ * (altIncl e w₀ * g) * (altIncl e w₀)⁻¹ := by
          group
      _ = (altIncl e w₀)⁻¹ * g := by rw [this]; group
  have hv₀inv2 : IsPGroup 2 (zpowers (altIncl e w₀)⁻¹) := by
    rw [zpowers_inv]; exact hv₀2
  have hr2 : IsPGroup 2 (zpowers (g * (altIncl e w₀)⁻¹)) :=
    isPGroup_zpowers_mul_of_commute hcom hg2 hv₀inv2
  have hrt : g * (altIncl e w₀)⁻¹ ∈ zpowers t := c.mem_zpowers_of_isPGroup ⟨hrH, hrC⟩ hr2
  have : g = (g * (altIncl e w₀)⁻¹) * altIncl e w₀ := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_right hrt) (mem_sup_left hv₀E)

theorem harada27 (hHar : ComponentClassification.HSFLit.HaradaInput)
    (c : Local27 N X t) :
    ∀ P : Subgroup N, IsPGroup 2 P → ∃ s : Finset N, s.card ≤ 4 ∧
      Subgroup.closure (s : Set N) = P := by
  classical
  obtain ⟨E, hEab, hE8, hE2⟩ := exists_E8_two_part c
  have hEel : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEab.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext
        (hEab.2 x x.2) }
  obtain ⟨Q, hEQ⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  have : IsElementaryAbelian 2 (E.subgroupOf (Q : Subgroup N)) :=
    IsElementaryAbelian.subgroupOf hEQ
  have hcard : Nat.card (E.subgroupOf (Q : Subgroup N)) = 8 := by
    rw [← hE8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg (fun z : E => (z : N)) (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcent : centralizer ((E.subgroupOf (Q : Subgroup N) : Subgroup (Q : Subgroup N)) :
      Set (Q : Subgroup N)) = E.subgroupOf (Q : Subgroup N) := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_subgroupOf.mpr (hE2 _ ?_ ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := Subgroup.mem_centralizer_iff.mp hx ⟨y, hEQ hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
        exact congrArg Subtype.val this
      · exact Q.isPGroup'.to_le (zpowers_le.2 x.2)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact hcomm _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hx)
  have hS := hHar.1 (Q : Subgroup N) Q.isPGroup' (E.subgroupOf (Q : Subgroup N)) inferInstance
    hcard hcent
  refine CFSG.ClassicalInvolution.fourGenerated_of_sylow Q (fun P' hP'Q => ?_)
  obtain ⟨X', hX4, hXcl⟩ := hS (P'.subgroupOf (Q : Subgroup N))
  refine ⟨X'.image (Q : Subgroup N).subtype, Finset.card_image_le.trans hX4, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXcl]
  exact Subgroup.map_subgroupOf_eq_of_le hP'Q

end CFSG.OddStandard.Seitz77
