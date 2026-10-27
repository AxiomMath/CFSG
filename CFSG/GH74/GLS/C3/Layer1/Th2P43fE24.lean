module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fKlein
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

section Proj

variable {G : Type} [Group G]

@[expose] def projL (A B E : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {u | u ∈ A ∧ ∃ w ∈ B, u * w ∈ E}
  one_mem' := ⟨A.one_mem, 1, B.one_mem, by simp⟩
  mul_mem' := by
    rintro u u' ⟨hu, w, hw, huw⟩ ⟨hu', w', hw', hu'w'⟩
    refine ⟨A.mul_mem hu hu', w * w', B.mul_mem hw hw', ?_⟩
    have : u * u' * (w * w') = (u * w) * (u' * w') := by
      calc u * u' * (w * w') = u * (u' * w) * w' := by group
        _ = u * (w * u') * w' := by rw [hcomm u' hu' w hw]
        _ = (u * w) * (u' * w') := by group
    rw [this]
    exact E.mul_mem huw hu'w'
  inv_mem' := by
    rintro u ⟨hu, w, hw, huw⟩
    refine ⟨A.inv_mem hu, w⁻¹, B.inv_mem hw, ?_⟩
    have : u⁻¹ * w⁻¹ = (u * w)⁻¹ := by
      calc u⁻¹ * w⁻¹ = (w * u)⁻¹ := by group
        _ = (u * w)⁻¹ := by rw [← hcomm u hu w hw]
    rw [this]
    exact E.inv_mem huw

theorem projL_le {A B E : Subgroup G} {hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} :
    projL A B E hcomm ≤ A := fun _ hu => hu.1

theorem projL_elem {A B E : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) (hel : CFSG.IsElementaryAbelian 2 ↥E) :
    CFSG.IsElementaryAbelian 2 ↥(projL A B E hcomm) := by
  obtain ⟨hEc, hEs⟩ := forall_of_isElementaryAbelian hel
  refine isElementaryAbelian_of_forall (fun u hu u' hu' => ?_) (fun u hu => ?_)
  · obtain ⟨huA, w, hw, huw⟩ := hu
    obtain ⟨hu'A, w', hw', hu'w'⟩ := hu'
    have h1 := hEc _ huw _ hu'w'
    have e1 : u * w * (u' * w') = (u * u') * (w * w') := by
      calc u * w * (u' * w') = u * (w * u') * w' := by group
        _ = u * (u' * w) * w' := by rw [hcomm u' hu'A w hw]
        _ = (u * u') * (w * w') := by group
    have e2 : u' * w' * (u * w) = (u' * u) * (w' * w) := by
      calc u' * w' * (u * w) = u' * (w' * u) * w := by group
        _ = u' * (u * w') * w := by rw [hcomm u huA w' hw']
        _ = (u' * u) * (w' * w) := by group
    rw [e1, e2] at h1
    exact (eq_of_mul_eq_of_inf_eq_bot hdisj (A.mul_mem huA hu'A) (A.mul_mem hu'A huA)
      (B.mul_mem hw hw') (B.mul_mem hw' hw) h1).1
  · obtain ⟨huA, w, hw, huw⟩ := hu
    have h1 := hEs _ huw
    have e1 : u * w * (u * w) = (u * u) * (w * w) := by
      calc u * w * (u * w) = u * (w * u) * w := by group
        _ = u * (u * w) * w := by rw [hcomm u huA w hw]
        _ = (u * u) * (w * w) := by group
    rw [e1] at h1
    have h2 : (u * u) * (w * w) = 1 * 1 := by rw [h1, one_mul]
    exact (eq_of_mul_eq_of_inf_eq_bot hdisj (A.mul_mem huA huA) A.one_mem (B.mul_mem hw hw)
      B.one_mem h2).1

end Proj

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

omit [Group G] in
theorem conjugate_conjugate_inv' {G : Type} [Group G] (X : Subgroup G) (a : G) :
    conjugate (conjugate X a⁻¹) a = X := by
  ext y
  rw [mem_conjugate_iff', mem_conjugate_iff']
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rw [e]

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem E24 [Finite G] {E : Subgroup G} (hE : E ≤ T) (hel : CFSG.IsElementaryAbelian 2 ↥E)
    (hcard : Nat.card ↥E = 16) :
    ∃ V V₂ : Subgroup G, IsFourSub (T ⊓ K) V ∧ IsFourSub (T ⊓ K) V₂ ∧
      E = V ⊔ conjugate V₂ a := by
  have hcomm := F.core.comm_P_conj
  have hdisj := F.core.P_inf_conj
  have hE' : E ≤ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ hE
  have hcomm' : ∀ b ∈ conjugate (T ⊓ K) a, ∀ a' ∈ T ⊓ K, b * a' = a' * b :=
    fun b hb a' ha' => (hcomm a' ha' b hb).symm
  have hdisj' : conjugate (T ⊓ K) a ⊓ (T ⊓ K) = ⊥ := by rw [inf_comm]; exact hdisj
  set V₁ := projL (T ⊓ K) (conjugate (T ⊓ K) a) E hcomm with hV₁
  set V₂' := projL (conjugate (T ⊓ K) a) (T ⊓ K) E hcomm' with hV₂'
  have hV₁el : CFSG.IsElementaryAbelian 2 ↥V₁ := projL_elem hcomm hdisj hel
  have hV₂el : CFSG.IsElementaryAbelian 2 ↥V₂' := projL_elem hcomm' hdisj' hel
  have hV₁4 : Nat.card ↥V₁ ≤ 4 := F.core.P_d8.card_le_four projL_le hV₁el
  have hV₂4 : Nat.card ↥V₂' ≤ 4 := (F.core.P_d8.conjugate a).card_le_four projL_le hV₂el
  have hEle : E ≤ V₁ ⊔ V₂' := by
    intro e he
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute hcomm (hE' he)
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hp, q, hq, he⟩)
      (Subgroup.mem_sup_right ⟨hq, p, hp, ?_⟩)
    rw [← hcomm p hp q hq]
    exact he
  have hcommV : ∀ u ∈ V₁, ∀ w ∈ V₂', u * w = w * u := fun u hu w hw => hcomm u hu.1 w hw.1
  have hdiscV : V₁ ⊓ V₂' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hy.1.1, hy.2.1⟩
    rw [hdisj] at this
    exact this
  have hcardsup : Nat.card ↥(V₁ ⊔ V₂') = Nat.card ↥V₁ * Nat.card ↥V₂' :=
    card_sup_of_commute_of_disjoint hcommV hdiscV
  have hle16 : 16 ≤ Nat.card ↥(V₁ ⊔ V₂') := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hEle
  have hpos1 : 0 < Nat.card ↥V₁ := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥V₂' := Nat.card_pos
  have h44 : Nat.card ↥V₁ = 4 ∧ Nat.card ↥V₂' = 4 := by
    rw [hcardsup] at hle16
    constructor <;> nlinarith
  have hEeq : E = V₁ ⊔ V₂' :=
    Subgroup.eq_of_le_of_card_ge hEle (by rw [hcardsup, h44.1, h44.2, hcard])
  have hV₂P : conjugate V₂' a⁻¹ ≤ T ⊓ K := by
    intro y hy
    rw [mem_conjugate_iff'] at hy
    have h1 : a⁻¹ * y * a⁻¹⁻¹ ∈ conjugate (T ⊓ K) a := projL_le hy
    have h2 := mem_conjugate_iff'.1 h1
    have e : a * (a⁻¹ * y * a⁻¹⁻¹) * a⁻¹ = y := by group
    rwa [e] at h2
  refine ⟨V₁, conjugate V₂' a⁻¹, ⟨projL_le, hV₁el, h44.1⟩,
    ⟨hV₂P, isElementaryAbelian_conjugate hV₂el a⁻¹, by rw [card_conjugate', h44.2]⟩, ?_⟩
  rw [conjugate_conjugate_inv']
  exact hEeq

theorem D_norm_T [Finite G] {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D) :
    ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
  have hDnP := mem_of_two_mul_card hD.1 (by rw [hD.2.2, F.core.P_d8.card_eq])
  intro t ht d hd
  have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ ht
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
  have hdq : d * q = q * d := F.core.comm_P_conj d (hD.1 hd) q hq
  have e : p * q * d * (p * q)⁻¹ = p * d * p⁻¹ := by
    calc p * q * d * (p * q)⁻¹ = p * (q * d) * q⁻¹ * p⁻¹ := by group
      _ = p * (d * q) * q⁻¹ * p⁻¹ := by rw [hdq]
      _ = p * d * p⁻¹ := by group
  rw [e]
  exact hDnP p hp d hd

theorem B_eq [Finite G] {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D) :
    (⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) = D ⊔ conjugate D a := by
  have hDnT := F.D_norm_T hD
  apply le_antisymm
  · refine iSup₂_le fun s hs' => ?_
    rintro _ ⟨d, hd, rfl⟩
    rcases F.S_cases s hs' with hsT | hsT
    · exact Subgroup.mem_sup_left (show s * d * s⁻¹ ∈ D from hDnT s hsT d hd)
    · refine Subgroup.mem_sup_right ?_
      have h1 : (a⁻¹ * s) * d * (a⁻¹ * s)⁻¹ ∈ D := hDnT _ hsT d hd
      have h2 := F.core.conj_fwd hDnT h1
      have e : a * ((a⁻¹ * s) * d * (a⁻¹ * s)⁻¹) * a⁻¹ = s * d * s⁻¹ := by group
      rw [e] at h2
      exact h2
  · refine sup_le ?_ ?_
    · intro d hd
      exact Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem (one_mem S)
        ⟨d, hd, by show 1 * d * 1⁻¹ = d; group⟩)
    · intro y hy
      have hy' : a * y * a⁻¹ ∈ D := mem_conjugate_iff'.1 hy
      exact Subgroup.mem_iSup_of_mem a⁻¹ (Subgroup.mem_iSup_of_mem (S.inv_mem F.core.a_mem)
        ⟨a * y * a⁻¹, hy', by show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y; group⟩)

theorem a_mem_normalizer_B [Finite G] {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D) :
    a ∈ normalizer ((D ⊔ conjugate D a : Subgroup G) : Set G) := by
  have hDnT := F.D_norm_T hD
  have h1 : ∀ y ∈ D, a * y * a⁻¹ ∈ D ⊔ conjugate D a := fun y hy =>
    Subgroup.mem_sup_right (F.core.conj_fwd hDnT hy)
  have h2 : ∀ y ∈ D, a⁻¹ * y * a ∈ D ⊔ conjugate D a := fun y hy =>
    Subgroup.mem_sup_right (C3.Layer1.Bk.Sec4Core.mem_conj_of D hy)
  have h3 : ∀ y ∈ conjugate D a, a * y * a⁻¹ ∈ D ⊔ conjugate D a := fun y hy =>
    Subgroup.mem_sup_left (mem_conjugate_iff'.1 hy)
  have h4 : ∀ y ∈ conjugate D a, a⁻¹ * y * a ∈ D ⊔ conjugate D a := fun y hy =>
    Subgroup.mem_sup_left (F.core.conj_inv_mem hDnT hy)
  apply mem_normalizer_of_two_sided
  · intro w hw
    have hle : D ⊔ conjugate D a ≤ (D ⊔ conjugate D a).comap (MulAut.conj a).toMonoidHom :=
      sup_le (fun y hy => by simpa [MulAut.conj_apply] using h1 y hy)
        (fun y hy => by simpa [MulAut.conj_apply] using h3 y hy)
    simpa [MulAut.conj_apply] using hle hw
  · intro w hw
    have hle : D ⊔ conjugate D a ≤ (D ⊔ conjugate D a).comap (MulAut.conj a⁻¹).toMonoidHom :=
      sup_le (fun y hy => by simpa [MulAut.conj_apply] using h2 y hy)
        (fun y hy => by simpa [MulAut.conj_apply] using h4 y hy)
    simpa [MulAut.conj_apply] using hle hw

end Frame

end CFSG.GH74.GLS.Th2.P43f
