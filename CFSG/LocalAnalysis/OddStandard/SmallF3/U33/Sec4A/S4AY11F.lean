module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11E
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Counting

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_card_le_relIndex_mul {A V E : Subgroup G} (hEV : E ≤ V) :
    Nat.card E ≤ A.relIndex V * Nat.card ↥(A ⊓ E) := by
  have h1 : A.relIndex V ≠ 0 := by
    intro h0
    have h2 := Subgroup.relIndex_mul_card (H := A) (K := V)
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := V)).ne h2
  have h3 := Subgroup.relIndex_le_of_le_right (H := A) hEV h1
  have h4 := Subgroup.relIndex_mul_card (H := A) (K := E)
  calc Nat.card E = A.relIndex E * Nat.card ↥(A ⊓ E) := h4.symm
    _ ≤ A.relIndex V * Nat.card ↥(A ⊓ E) := Nat.mul_le_mul_right _ h3

theorem m11_relIndex_RV (h : L41GPh8 t L S x₁ x₂ lam rho) :
    (l41R t x₁ x₂ rho).relIndex (l41V S t x₁ x₂) = 4 := by
  have h1 := Subgroup.relIndex_mul_card (H := l41R t x₁ x₂ rho) (K := l41V S t x₁ x₂)
  rw [inf_eq_left.mpr (m11_R_le_V h), h.rfacts.card_R, m11_card_V h] at h1
  omega

theorem m11_F_le_V (h : L41GPh8 t L S x₁ x₂ lam rho) : l41F t x₁ x₂ rho ≤ l41V S t x₁ x₂ :=
  sup_le (m11_R_le_V h) (Subgroup.zpowers_le.mpr (m11_t_mem_V h))

theorem m11_relIndex_FV (h : L41GPh8 t L S x₁ x₂ lam rho) :
    (l41F t x₁ x₂ rho).relIndex (l41V S t x₁ x₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := l41F t x₁ x₂ rho) (K := l41V S t x₁ x₂)
  rw [inf_eq_left.mpr (m11_F_le_V h), m13_card_F h, m11_card_V h] at h1
  omega

theorem m11_card_le_four_of_cent (h : L41GPh10 t L S x₁ x₂ lam rho) {D : Subgroup G}
    (hDY : D ≤ l41Y t x₁ x₂ rho) {e : G} (heV : e ∈ l41V S t x₁ x₂)
    (heR : e ∉ l41R t x₁ x₂ rho) (hc : ∀ x ∈ D, e * x = x * e) : Nat.card D ≤ 4 := by
  have hDR : D ≤ l41R t x₁ x₂ rho := hDY.trans (m13_Y_le_R t x₁ x₂ rho)
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  obtain ⟨r, hr, hcases⟩ := m11_mem_V_cases h.toL41GPh8 heV
  rcases hcases with he | he | he | he
  · exact absurd (he ▸ hr) heR
  · subst he
    have hk : ∀ x ∈ D, t * x = x * t := m11_cent_mul h hDR hr hc
    have hle : D ≤ fourGrp x₁ x₂ := fun x hx => by
      rw [← m11_Y_inf_cent_t h]
      exact Subgroup.mem_inf.mpr ⟨hDY hx, mem_invCent_iff.mpr (hk x hx).symm⟩
    exact (Subgroup.card_le_of_le hle).trans (n4_card_four h.toCtx0).le
  · subst he
    have hk : ∀ x ∈ D, lam * x = x * lam := m11_cent_mul h hDR hr hc
    have hle : D ≤ l41Y t x₁ x₂ rho ⊓ centralizer ({lam} : Set G) := fun x hx =>
      Subgroup.mem_inf.mpr ⟨hDY hx, Subgroup.mem_centralizer_singleton_iff.mpr (hk x hx).symm⟩
    exact (Subgroup.card_le_of_le hle).trans (m11_card_cent_lam h).le
  · subst he
    have hk := m11_cent_mul h hDR hr hc
    rw [htl] at hk
    have hle : D ≤ l41Y t x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) := fun x hx =>
      Subgroup.mem_inf.mpr ⟨hDY hx, Subgroup.mem_centralizer_singleton_iff.mpr (hk x hx).symm⟩
    exact (Subgroup.card_le_of_le hle).trans (m11_card_cent_lamt h).le

theorem m11_E16_V (h : L41GPh10 t L S x₁ x₂ lam rho) {E : Subgroup G}
    (hE : IsE16In (l41V S t x₁ x₂) E) : E = l41Y t x₁ x₂ rho := by
  obtain ⟨hEV, hEel, hE16⟩ := hE
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => hEel.mul_self_eq_one hx
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hEel.comm hx hy
  by_cases hER : E ≤ l41R t x₁ x₂ rho
  · refine Subgroup.eq_of_le_of_card_ge
      (fun x hx => (m11_mem_Y_iff h).mpr ⟨hER hx, hEsq x hx⟩) ?_
    rw [m11_card_Y h, hE16]
  · exfalso
    obtain ⟨e, heE, heR⟩ := Set.not_subset.mp hER
    have hDY : l41R t x₁ x₂ rho ⊓ E ≤ l41Y t x₁ x₂ rho := fun x hx =>
      (m11_mem_Y_iff h).mpr ⟨hx.1, hEsq x hx.2⟩
    have hD4 : Nat.card ↥(l41R t x₁ x₂ rho ⊓ E) ≤ 4 :=
      m11_card_le_four_of_cent h hDY (hEV heE) heR (fun x hx => hEc e heE x hx.2)
    have hDge : 4 ≤ Nat.card ↥(l41R t x₁ x₂ rho ⊓ E) := by
      have h1 := m11_card_le_relIndex_mul (A := l41R t x₁ x₂ rho) (V := l41V S t x₁ x₂) hEV
      rw [m11_relIndex_RV h.toL41GPh8, hE16] at h1
      omega
    have hDeq4 : Nat.card ↥(l41R t x₁ x₂ rho ⊓ E) = 4 := le_antisymm hD4 hDge
    have hFE8 : 8 ≤ Nat.card ↥(l41F t x₁ x₂ rho ⊓ E) := by
      have h1 := m11_card_le_relIndex_mul (A := l41F t x₁ x₂ rho) (V := l41V S t x₁ x₂) hEV
      rw [m11_relIndex_FV h.toL41GPh8, hE16] at h1
      omega
    have hFER : ¬ (l41F t x₁ x₂ rho ⊓ E ≤ l41R t x₁ x₂ rho) := by
      intro hle
      have hle' : l41F t x₁ x₂ rho ⊓ E ≤ l41R t x₁ x₂ rho ⊓ E := fun x hx => ⟨hle hx, hx.2⟩
      have := Subgroup.card_le_of_le hle'
      omega
    obtain ⟨e', he'FE, he'R⟩ := Set.not_subset.mp hFER
    obtain ⟨k, hk, he'⟩ : ∃ k ∈ l41R t x₁ x₂ rho, e' = t * k := by
      rcases m13_mem_F h.toL41GPh8 he'FE.1 with hR | hk
      · exact absurd hR he'R
      · exact hk
    have htD : ∀ x ∈ l41R t x₁ x₂ rho ⊓ E, t * x = x * t := by
      intro x hx
      have hc : e' * x = x * e' := hEc e' he'FE.2 x hx.2
      rw [he'] at hc
      apply mul_right_cancel (b := k)
      calc t * x * k = t * (x * k) := mul_assoc _ _ _
        _ = t * (k * x) := by rw [m13_comm_R h hx.1 hk]
        _ = t * k * x := (mul_assoc _ _ _).symm
        _ = x * (t * k) := hc
        _ = x * t * k := (mul_assoc _ _ _).symm
    have hDF2 : l41R t x₁ x₂ rho ⊓ E ≤ fourGrp x₁ x₂ := fun x hx => by
      rw [← m11_Y_inf_cent_t h]
      exact Subgroup.mem_inf.mpr ⟨hDY hx, mem_invCent_iff.mpr (htD x hx).symm⟩
    have hDeqF2 : l41R t x₁ x₂ rho ⊓ E = fourGrp x₁ x₂ :=
      Subgroup.eq_of_le_of_card_ge hDF2 (by rw [n4_card_four h.toCtx0, hDeq4])
    by_cases hEF : E ≤ l41F t x₁ x₂ rho
    · have h1 := m11_card_le_relIndex_mul (A := l41R t x₁ x₂ rho) (V := l41F t x₁ x₂ rho) hEF
      rw [m13_relIndex_RF h.toL41GPh8, hE16] at h1
      omega
    · obtain ⟨g, hgE, hgF⟩ := Set.not_subset.mp hEF
      have hg : g ∈ l41V S t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hEV hgE, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hx' : x ∈ l41R t x₁ x₂ rho ⊓ E := by
          rw [hDeqF2]
          exact hx
        exact hEc x hx'.2 g hgE
      rw [m11_cent_V_F2 h] at hg
      exact hgF hg

end Counting

section AutInv

variable {G : Type} [Group G]

@[expose] def m11AutInv (V A : Subgroup G) : Prop :=
  ∀ α : ↥V ≃* ↥V, ∀ v : ↥V, (v : G) ∈ A → ((α v : ↥V) : G) ∈ A

theorem m11AutInv.char {V A : Subgroup G} (h : m11AutInv V A) :
    (A.subgroupOf V).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro α
  rintro _ ⟨v, hv, rfl⟩
  exact h α v (Subgroup.mem_subgroupOf.mp hv)

theorem m11AutInv.cent {V A : Subgroup G} (hAV : A ≤ V) (h : m11AutInv V A) :
    m11AutInv V (V ⊓ centralizer (A : Set G)) := by
  intro α v hv
  obtain ⟨-, hvc⟩ := Subgroup.mem_inf.mp hv
  refine Subgroup.mem_inf.mpr ⟨(α v).2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have haV : a ∈ V := hAV ha
  have ha' : ((α.symm ⟨a, haV⟩ : ↥V) : G) ∈ A := h α.symm ⟨a, haV⟩ ha
  have hcomm : ((α.symm ⟨a, haV⟩ : ↥V) : G) * (v : G) =
      (v : G) * ((α.symm ⟨a, haV⟩ : ↥V) : G) := Subgroup.mem_centralizer_iff.mp hvc _ ha'
  have hcomm' : α.symm ⟨a, haV⟩ * v = v * α.symm ⟨a, haV⟩ := Subtype.ext hcomm
  have key := congrArg (fun w => ((α w : ↥V) : G)) hcomm'
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at key
  exact key

theorem m11AutInv.inf {V A B : Subgroup G} (hA : m11AutInv V A) (hB : m11AutInv V B) :
    m11AutInv V (A ⊓ B) := fun α v hv =>
  Subgroup.mem_inf.mpr ⟨hA α v (Subgroup.mem_inf.mp hv).1, hB α v (Subgroup.mem_inf.mp hv).2⟩

end AutInv

section Y11F

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_Y_le_V (h : L41GPh8 t L S x₁ x₂ lam rho) : l41Y t x₁ x₂ rho ≤ l41V S t x₁ x₂ :=
  (m13_Y_le_R t x₁ x₂ rho).trans (m11_R_le_V h)

theorem m11_autInv_Y (h : L41GPh10 t L S x₁ x₂ lam rho) :
    m11AutInv (l41V S t x₁ x₂) (l41Y t x₁ x₂ rho) := by
  intro α v hv
  have hYV := m11_Y_le_V h.toL41GPh8
  have hE : IsE16In (l41V S t x₁ x₂)
      ((((l41Y t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).map α.toMonoidHom).map
        (l41V S t x₁ x₂).subtype) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨w, -, rfl⟩
      exact w.2
    · exact ((((m11_Y_elem h).subgroupOf (l41V S t x₁ x₂)).map α.toMonoidHom).map
        (l41V S t x₁ x₂).subtype)
    · rw [Subgroup.card_map_of_injective (l41V S t x₁ x₂).subtype_injective,
        Subgroup.card_map_of_injective α.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYV).toEquiv, m11_card_Y h]
  rw [← m11_E16_V h hE]
  exact Subgroup.mem_map.mpr ⟨α v, Subgroup.mem_map.mpr ⟨v, Subgroup.mem_subgroupOf.mpr hv, rfl⟩,
    rfl⟩

theorem m11_autInv_R (h : L41GPh10 t L S x₁ x₂ lam rho) :
    m11AutInv (l41V S t x₁ x₂) (l41R t x₁ x₂ rho) := by
  have h1 := (m11_autInv_Y h).cent (m11_Y_le_V h.toL41GPh8)
  rwa [m11_cent_V_Y h] at h1

theorem m11_autInv_F2 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    m11AutInv (l41V S t x₁ x₂) (fourGrp x₁ x₂) := by
  intro α v hv
  have hvR : (v : G) ∈ l41R t x₁ x₂ rho := h.rfacts.fourGrp_le hv
  have hmem : (⟨(v : G), hvR⟩ : ↥(l41R t x₁ x₂ rho)) ∈ (m11Sq h).range := by
    rw [m11Sq_range h]
    exact hv
  obtain ⟨r, hr⟩ := hmem
  have hrr : (r : G) * (r : G) = (v : G) :=
    (m11Sq_apply h r).symm.trans (congrArg Subtype.val hr)
  have hrV : (r : G) ∈ l41V S t x₁ x₂ := m11_R_le_V h.toL41GPh8 r.2
  have hv' : v = ⟨(r : G), hrV⟩ * ⟨(r : G), hrV⟩ := Subtype.ext hrr.symm
  have hαr : ((α ⟨(r : G), hrV⟩ : ↥(l41V S t x₁ x₂)) : G) ∈ l41R t x₁ x₂ rho :=
    m11_autInv_R h α _ r.2
  rw [hv', map_mul, Subgroup.coe_mul]
  exact h.rfacts.sq_mem _ hαr

theorem m11_autInv_F (h : L41GPh10 t L S x₁ x₂ lam rho) :
    m11AutInv (l41V S t x₁ x₂) (l41F t x₁ x₂ rho) := by
  have h1 := (m11_autInv_F2 h).cent (h.rfacts.fourGrp_le.trans (m11_R_le_V h.toL41GPh8))
  rwa [m11_cent_V_F2 h] at h1

theorem m11_autInv_B (h : L41GPh10 t L S x₁ x₂ lam rho) :
    m11AutInv (l41V S t x₁ x₂) (baseGrp x₁ x₂) := by
  have h1 := (m11_autInv_F h).cent (m11_F_le_V h.toL41GPh8)
  have h2 := (m11_autInv_F h).inf h1
  have h3 : l41F t x₁ x₂ rho ⊓ (l41V S t x₁ x₂ ⊓
      centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G)) = baseGrp x₁ x₂ := by
    rw [← inf_assoc, inf_eq_left.mpr (m11_F_le_V h.toL41GPh8)]
    exact m11_center_F h
  rwa [h3] at h2

theorem l41_y_of (h : L41GPh10 t L S x₁ x₂ lam rho) : L41YFacts t S x₁ x₂ lam rho where
  exists_F := m11_exists_F h
  Y_elem := ⟨m11_Y_elem h, m11_card_Y h⟩
  cent_Y_t := m11_Y_inf_cent_t h
  card_cent_Y_lam := m11_card_cent_lam h
  card_cent_Y_lamt := m11_card_cent_lamt h
  quot_V_R := m11_quot_V_R h.toL41GPh8
  cent_V_R := m11_cent_V_R h
  cent_V_Y := m11_cent_V_Y h
  cent_V_F2 := m11_cent_V_F2 h
  cent_Y_V := m11_cent_Y_V h
  center_F := m11_center_F h
  E16_V := fun _ hE => m11_E16_V h hE
  char_Y := (m11_autInv_Y h).char
  char_R := (m11_autInv_R h).char
  char_F2 := (m11_autInv_F2 h).char
  char_F := (m11_autInv_F h).char
  char_B := (m11_autInv_B h).char

end Y11F

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_y_holds : L41YStmt :=
  fun h => S4A.l41_y_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
