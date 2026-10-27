module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step10

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Eight

open S6M

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

section Step10

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

theorem parity_of_comm {f : X} (hf : f * y⁻¹ ∈ C.W) (hf' : f⁻¹ * y⁻¹ ∈ C.W) {e g : X}
    (he : e ∈ C.E) (hg : g ∈ conjugate C.E y) (hx : f * (e * g) = e * g * f) :
    e ∈ C.E0 ↔ g ∈ conjugate C.E0 y := by
  have ha : f * e * f⁻¹ ∈ conjugate C.E y := C.conj_mem_Ey hyU hyN hyW C.W_le_normalizer_E hf he
  have hb : f * g * f⁻¹ ∈ C.E := C.conj_mem_E C.W_le_normalizer_E hf hg
  have hxx : e * g = (f * g * f⁻¹) * ((f * g * f⁻¹)⁻¹ * (f * e * f⁻¹) * (f * g * f⁻¹)) := by
    calc e * g = f * (e * g) * f⁻¹ := by rw [hx, mul_inv_cancel_right]
      _ = _ := by group
  have hbab : (f * g * f⁻¹)⁻¹ * (f * e * f⁻¹) * (f * g * f⁻¹) ∈ conjugate C.E y := by
    have hbN := C.W_le_normalizer_E (C.E_le_W hb)
    have hyE : conjugate C.E y ≤ normalizer ((conjugate C.E y : Subgroup X) : Set X) :=
      le_normalizer
    have hEN : C.E ≤ normalizer ((conjugate C.E y : Subgroup X) : Set X) := by
      intro w hw
      have hwW := C.E_le_W hw
      apply mem_normalizer_of_conjugate_eq
      have hw' : y * w * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN w).mp hwW
      rw [conjugate_conjugate, show y * w = (y * w * y⁻¹) * y by group, ← conjugate_conjugate,
        conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E hw')]
    have := (mem_normalizer_iff.mp (inv_mem (hEN hb)) _).mp ha
    rwa [inv_inv] at this
  have h1 := C.parity_eq hyU hyN hyW he hb hg hbab hxx
  rw [h1]
  constructor
  · intro hb0
    have := C.conj_mem_Ey hyU hyN hyW C.W_le_normalizer_E0 hf' hb0
    rwa [show f⁻¹ * (f * g * f⁻¹) * f⁻¹⁻¹ = g by group] at this
  · intro hg0
    exact C.conj_mem_E C.W_le_normalizer_E0 hf hg0

omit hyU hyN hyW in
theorem mul_mem_E0y {g g' : X} (hg : g ∈ conjugate C.E y) (hg' : g' ∈ conjugate C.E y)
    (h0 : g ∉ conjugate C.E0 y) (h0' : g' ∉ conjugate C.E0 y) : g * g' ∈ conjugate C.E0 y := by
  rw [mem_conjugate_iff] at hg hg' h0 h0' ⊢
  have := C.mul_mem_E0 hg hg' h0 h0'
  rwa [show y * g * y⁻¹ * (y * g' * y⁻¹) = y * (g * g') * y⁻¹ by group] at this

theorem conj_E_le_W_of_le {h : X} (hF : conjugate C.E h ≤ C.NUW) : conjugate C.E h ≤ C.W := by
  set F := conjugate C.E h with hFdef
  by_contra hFW
  obtain ⟨f, hfF, hfW⟩ := Set.not_subset.mp hFW
  have hf : f * y⁻¹ ∈ C.W := (C.mem_W_or hyU hyN hyW f (hF hfF)).resolve_left hfW
  have hfNUW := hF hfF
  have hf' : f⁻¹ * y⁻¹ ∈ C.W := by
    have hy2 := C.sq_mem_W hyU hyN hyW
    have h1 : y * (f * y⁻¹) * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN _).mp hf
    have h2 := mul_mem h1 hy2
    have h3 := inv_mem h2
    rwa [show (y * (f * y⁻¹) * y⁻¹ * (y * y))⁻¹ = f⁻¹ * y⁻¹ by group] at h3
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => by
    rw [hFdef, mem_conjugate_iff] at hx
    have := C.E_sq hx
    calc x * x = h⁻¹ * ((h * x * h⁻¹) * (h * x * h⁻¹)) * h := by group
      _ = 1 := by rw [this]; group
  have hFc : ∀ x ∈ F, ∀ x' ∈ F, x * x' = x' * x := fun x hx x' hx' => by
    rw [hFdef, mem_conjugate_iff] at hx hx'
    have := C.E_comm hx hx'
    calc x * x' = h⁻¹ * ((h * x * h⁻¹) * (h * x' * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x' * h⁻¹) * (h * x * h⁻¹)) * h := by rw [this]
      _ = x' * x := by group
  have hF32 : Nat.card F = 32 := by rw [hFdef, Eight.card_conjugate_eq, C.card_E]
  have h1 : Nat.card F ≤ 2 * Nat.card ↥(F ⊓ C.W) := by
    refine Eight.card_le_two_mul_card_inf fun x hx x' hx' hxW hx'W => ?_
    have hxy := (C.mem_W_or hyU hyN hyW x (hF hx)).resolve_left hxW
    have hx'y := (C.mem_W_or hyU hyN hyW x' (hF hx')).resolve_left hx'W
    have := (mem_normalizer_iff.mp (inv_mem hyN) _).mp (mul_mem (inv_mem hxy) hx'y)
    rwa [show y⁻¹ * ((x * y⁻¹)⁻¹ * (x' * y⁻¹)) * y⁻¹⁻¹ = x⁻¹ * x' by group] at this
  have hFWle : F ⊓ C.W ≤ C.W := inf_le_right
  have h2 : Nat.card ↥(F ⊓ C.W) ≤ 2 * Nat.card ↥(F ⊓ C.W ⊓ C.Q y) := by
    refine Eight.card_le_two_mul_card_inf fun x hx x' hx' hxQ hx'Q => ?_
    have hxW := (Subgroup.mem_inf.mp hx).2
    have hx'W := (Subgroup.mem_inf.mp hx').2
    have hπx : C.π ⟨x, hxW.2⟩ ∉ Vlist := fun h => hxQ (C.mem_Q_of_π hyU hyN hyW hxW h)
    have hπx' : C.π ⟨x', hx'W.2⟩ ∉ Vlist := fun h => hx'Q (C.mem_Q_of_π hyU hyN hyW hx'W h)
    have h3 := List.all_eq_true.mp (List.all_eq_true.mp Wlist_coset _ (C.π_mem_W hxW)) _
      (C.π_mem_W hx'W)
    simp only [Bool.or_eq_true, List.contains_iff_mem, hπx, hπx', false_or] at h3
    have hW' : x⁻¹ * x' ∈ C.W := mul_mem (inv_mem hxW) hx'W
    refine C.mem_Q_of_π hyU hyN hyW hW' ?_
    rw [show (⟨x⁻¹ * x', hW'.2⟩ : ↥C.N) = (⟨x, hxW.2⟩ : ↥C.N)⁻¹ * ⟨x', hx'W.2⟩ from rfl, map_mul,
      map_inv]
    exact h3
  have h3 : Nat.card ↥(F ⊓ C.Q y) ≤ 2 * Nat.card ↥(F ⊓ C.Q y ⊓ C.Q0 y) := by
    refine Eight.card_le_two_mul_card_inf fun x hx x' hx' hxQ0 hx'Q0 => ?_
    obtain ⟨hxF, hxQ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hx'F, hx'Q⟩ := Subgroup.mem_inf.mp hx'
    obtain ⟨e, he, g, hg, rfl⟩ := C.exists_mul_of_mem_Q hyN hxQ
    obtain ⟨e', he', g', hg', rfl⟩ := C.exists_mul_of_mem_Q hyN hx'Q
    have hp := C.parity_of_comm hyU hyN hyW hf hf' he hg (hFc f hfF _ hxF)
    have hp' := C.parity_of_comm hyU hyN hyW hf hf' he' hg' (hFc f hfF _ hx'F)
    have he0 : e ∉ C.E0 := fun h0 => hxQ0 (mul_mem (mem_sup_left h0) (mem_sup_right (hp.mp h0)))
    have he0' : e' ∉ C.E0 := fun h0 =>
      hx'Q0 (mul_mem (mem_sup_left h0) (mem_sup_right (hp'.mp h0)))
    have hg0 : g ∉ conjugate C.E0 y := fun h0 => he0 (hp.mpr h0)
    have hg0' : g' ∉ conjugate C.E0 y := fun h0 => he0' (hp'.mpr h0)
    have hee : e⁻¹ * e' ∈ C.E0 := by
      rw [inv_eq_of_mul_eq_one_right (C.E_sq he)]
      exact C.mul_mem_E0 he he' he0 he0'
    have hgg : g⁻¹ * g' ∈ conjugate C.E0 y := by
      rw [inv_eq_of_mul_eq_one_right (C.conj_E_sq hg)]
      exact C.mul_mem_E0y hg hg' hg0 hg0'
    have hgW := C.conj_le_W le_rfl hyN hg
    have hconj : g⁻¹ * (e⁻¹ * e') * g⁻¹⁻¹ ∈ C.E0 := C.conj_E0_mem ⟨g⁻¹, inv_mem hgW.2⟩ hee
    rw [show (e * g)⁻¹ * (e' * g') = (g⁻¹ * (e⁻¹ * e') * g⁻¹⁻¹) * (g⁻¹ * g') by group]
    exact mul_mem (mem_sup_left hconj) (mem_sup_right hgg)
  have hKF : ∀ x ∈ F ⊓ C.Q y ⊓ C.Q0 y, ∃ v ∈ Klist, C.θ v = x := by
    intro x hx
    obtain ⟨hx1, hxQ0⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxF, -⟩ := Subgroup.mem_inf.mp hx1
    have hfx := hFc f hfF x hxF
    have hxfx : f * x * f⁻¹ = x := by rw [hfx, mul_inv_cancel_right]
    rcases C.mem_or_mem_of_sq hyU hyN hyW hxQ0 (hF2 x hxF) with h0 | h0
    · have h1 := C.conj_mem_Ey hyU hyN hyW C.W_le_normalizer_E hf (C.E0_le_E h0)
      rw [hxfx] at h1
      exact (C.mem_inf_iff hyU hyN hyW).mp (Subgroup.mem_inf.mpr ⟨h1, C.E0_le_E h0⟩)
    · have h1 := C.conj_mem_E C.W_le_normalizer_E hf (C.conj_E0_le y h0)
      rw [hxfx] at h1
      exact (C.mem_inf_iff hyU hyN hyW).mp (Subgroup.mem_inf.mpr ⟨C.conj_E0_le y h0, h1⟩)
  have h4 : Nat.card ↥(F ⊓ C.Q y ⊓ C.Q0 y) ≤ 4 := by
    rw [← Klist_ncard]
    exact C.card_le_ncard _ fun x hx => hKF x hx
  have h5 : Nat.card ↥(F ⊓ C.W ⊓ C.Q y) ≤ Nat.card ↥(F ⊓ C.Q y) :=
    card_le_of_le (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hK4 : Nat.card ↥(F ⊓ C.Q y ⊓ C.Q0 y) = 4 := by omega
  have hKsub : ∀ v ∈ Klist, C.θ v ∈ F := by
    have hle : ((F ⊓ C.Q y ⊓ C.Q0 y : Subgroup X) : Set X) ⊆ C.θ '' {v | v ∈ Klist} := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hKF x hx
      exact ⟨v, hv, rfl⟩
    have heq : ((F ⊓ C.Q y ⊓ C.Q0 y : Subgroup X) : Set X) = C.θ '' {v | v ∈ Klist} := by
      refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
      rw [Set.ncard_image_of_injective _ C.θ_injective, Klist_ncard, ← Nat.card_coe_set_eq,
        SetLike.coe_sort_coe, hK4]
    intro v hv
    have : C.θ v ∈ ((F ⊓ C.Q y ⊓ C.Q0 y : Subgroup X) : Set X) := by
      rw [heq]
      exact ⟨v, hv, rfl⟩
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp this).1).1
  have hout : ∃ w ∈ F ⊓ C.W, w ∉ C.Q y := by
    by_contra hall
    push Not at hall
    have : Nat.card ↥(F ⊓ C.W) ≤ Nat.card ↥(F ⊓ C.Q y) :=
      card_le_of_le fun w hw => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, hall w hw⟩
    omega
  obtain ⟨w, hw, hwQ⟩ := hout
  obtain ⟨hwF, hwW⟩ := Subgroup.mem_inf.mp hw
  have hfixK : (Klist.all fun v => veq (act (C.π ⟨w, hwW.2⟩) v) v) = true := by
    refine List.all_eq_true.mpr fun v hv => veq_iff.mpr ?_
    exact (C.comm_iff ⟨w, hwW.2⟩ v).mp (hFc w hwF _ (hKsub v hv))
  have h6 := List.all_eq_true.mp Wlist_centK _ (C.π_mem_W hwW)
  simp only [hfixK, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h6
  exact hwQ (C.mem_Q_of_π hyU hyN hyW hwW h6)

theorem conj_E_le_Q {h : X} (hF : conjugate C.E h ≤ C.NUW) : conjugate C.E h ≤ C.Q y := by
  have hFW := C.conj_E_le_W_of_le hyU hyN hyW hF
  have hF2 : ∀ x ∈ conjugate C.E h, x * x = 1 := fun x hx => by
    rw [mem_conjugate_iff] at hx
    have := C.E_sq hx
    calc x * x = h⁻¹ * ((h * x * h⁻¹) * (h * x * h⁻¹)) * h := by group
      _ = 1 := by rw [this]; group
  have hFc : ∀ x ∈ conjugate C.E h, ∀ x' ∈ conjugate C.E h, x * x' = x' * x := fun x hx x' hx' => by
    rw [mem_conjugate_iff] at hx hx'
    have := C.E_comm hx hx'
    calc x * x' = h⁻¹ * ((h * x * h⁻¹) * (h * x' * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x' * h⁻¹) * (h * x * h⁻¹)) * h := by rw [this]
      _ = x' * x := by group
  have hV := C.range_ψW_le_V hFW hF2 hFc (by rw [Eight.card_conjugate_eq, C.card_E])
  intro x hx
  exact C.mem_Q_of_π hyU hyN hyW (hFW hx) (hV ((C.mem_range_ψW hFW).mpr ⟨x, hx, rfl⟩))

theorem y_mem_normalizer_Q : y ∈ normalizer ((C.Q y : Subgroup X) : Set X) := by
  apply mem_normalizer_of_conjugate_eq
  rw [Q, conjugate_sup, conjugate_conjugate,
    conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E (C.sq_mem_W hyU hyN hyW)), sup_comm]

omit hyU hyW in
theorem W_le_normalizer_Q : C.W ≤ normalizer ((C.Q y : Subgroup X) : Set X) := by
  intro w hw
  apply mem_normalizer_of_conjugate_eq
  have hw' : y * w * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN w).mp hw
  rw [Q, conjugate_sup, conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E hw),
    conjugate_conjugate, show y * w = (y * w * y⁻¹) * y by group, ← conjugate_conjugate,
    conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E hw')]

theorem conj_Q_eq {g : X} (hg : conjugate (C.Q y) g ≤ C.NUW) : conjugate (C.Q y) g = C.Q y := by
  have h1 : conjugate C.E g ≤ C.NUW := le_trans (by
    intro x hx
    rw [mem_conjugate_iff] at hx ⊢
    exact mem_sup_left hx) hg
  have h2 : conjugate C.E (y * g) ≤ C.NUW := le_trans (by
    intro x hx
    rw [mem_conjugate_iff] at hx ⊢
    exact mem_sup_right (by
      rw [mem_conjugate_iff]
      rwa [show y * (g * x * g⁻¹) * y⁻¹ = y * g * x * (y * g)⁻¹ by group])) hg
  have hle : conjugate (C.Q y) g ≤ C.Q y := by
    rw [Q, conjugate_sup, conjugate_conjugate]
    exact sup_le (C.conj_E_le_Q hyU hyN hyW h1) (C.conj_E_le_Q hyU hyN hyW h2)
  exact eq_of_le_of_card_ge hle (by rw [Eight.card_conjugate_eq])

omit hyU hyW in
theorem E_le_normalizer_Ey : C.E ≤ normalizer ((conjugate C.E y : Subgroup X) : Set X) := by
  intro w hw
  have hwW := C.E_le_W hw
  apply mem_normalizer_of_conjugate_eq
  have hw' : y * w * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN w).mp hwW
  rw [conjugate_conjugate, show y * w = (y * w * y⁻¹) * y by group, ← conjugate_conjugate,
    conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E hw')]

theorem conj_E0_le_Q0 {m : X} (hm : m ∈ normalizer ((C.Q y : Subgroup X) : Set X)) :
    conjugate C.E0 m ≤ C.Q0 y := by
  have hAQ : ∀ {m' : X}, m' ∈ normalizer ((C.Q y : Subgroup X) : Set X) →
      conjugate C.E0 m' ≤ C.Q y := by
    intro m' hm' x hx
    rw [mem_conjugate_iff] at hx
    have := (mem_normalizer_iff.mp (inv_mem hm') _).mp (mem_sup_left (C.E0_le_E hx))
    rwa [show m'⁻¹ * (m' * x * m'⁻¹) * m'⁻¹⁻¹ = x by group] at this
  have hπ0 : ∀ {m' : X}, m' ∈ normalizer ((C.Q y : Subgroup X) : Set X) →
      ∀ x ∈ conjugate C.E0 m', ∃ e ∈ C.E, ∃ g ∈ conjugate C.E0 y, x = e * g := by
    intro m' hm'
    have hAW : conjugate C.E0 m' ≤ C.W := (hAQ hm').trans (C.Q_le_W hyN)
    have hA2 : ∀ x ∈ conjugate C.E0 m', x * x = 1 := fun x hx => by
      rw [mem_conjugate_iff] at hx
      have := C.E_sq (C.E0_le_E hx)
      calc x * x = m'⁻¹ * ((m' * x * m'⁻¹) * (m' * x * m'⁻¹)) * m' := by group
        _ = 1 := by rw [this]; group
    have hAc : ∀ x ∈ conjugate C.E0 m', ∀ x' ∈ conjugate C.E0 m', x * x' = x' * x :=
      fun x hx x' hx' => by
        rw [mem_conjugate_iff] at hx hx'
        have := C.E_comm (C.E0_le_E hx) (C.E0_le_E hx')
        calc x * x' = m'⁻¹ * ((m' * x * m'⁻¹) * (m' * x' * m'⁻¹)) * m' := by group
          _ = m'⁻¹ * ((m' * x' * m'⁻¹) * (m' * x * m'⁻¹)) * m' := by rw [this]
          _ = x' * x := by group
    have hG0V : (C.ψW hAW).range ≤ Vsub := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := (C.mem_range_ψW hAW).mp ht
      exact C.π_mem_V_of_mem_Q hyU hyN hyW (hAQ hm' hx)
    have hnoswap : ∀ t ∈ (C.ψW hAW).range, t ∉ [s01, s23, s45] := by
      intro t ht hts
      obtain ⟨x, hx, rfl⟩ := (C.mem_range_ψW hAW).mp ht
      rw [mem_conjugate_iff] at hx
      by_cases he1 : m' * x * m'⁻¹ = 1
      · have hx1 : x = 1 := by
          calc x = m'⁻¹ * (m' * x * m'⁻¹) * m' := by group
            _ = 1 := by rw [he1]; group
        have : C.π ⟨x, (hAW (by rwa [mem_conjugate_iff])).2⟩ = 1 := by
          rw [← map_one C.π]
          congr 1
          exact Subtype.ext hx1
        rw [this] at hts
        exact one_not_mem_swaps hts
      · exact C.fus_z _ hx he1 m' _ (by group) (hAW (by rwa [mem_conjugate_iff])).1
          (isSwap_of_mem hts)
    have hV0 : (C.ψW hAW).range ≤ V0sub := by
      rcases noswap_cases _ hG0V hnoswap with h | h
      · exact h
      · intro t ht
        rcases h t ht with rfl | rfl
        · exact one_mem _
        · exfalso
          have hcard := C.card_eq_mul_of_le_W hAW
          rw [Eight.card_conjugate_eq, C.card_E0] at hcard
          have hle : Nat.card (C.ψW hAW).range ≤ 2 := by
            calc Nat.card (C.ψW hAW).range =
                ((C.ψW hAW).range : Set (Equiv.Perm (Fin 6))).ncard := (Nat.card_coe_set_eq _).symm
              _ ≤ ({1, t135} : Set (Equiv.Perm (Fin 6))).ncard :=
                  Set.ncard_le_ncard (fun s hs => h s hs) (Set.toFinite _)
              _ ≤ 2 := ncard_pair_le _ _
          have hK : Nat.card ↥(conjugate C.E0 m' ⊓ C.E) ≤ 4 := by
            have h2 : {v : V5 | (isEvenB v && [t135].all fun t => veq (act t v) v) = true}.ncard =
                4 := by
              rw [ncard_eq_length]
              exact t135_facts.1
            rw [← h2]
            refine C.card_le_ncard _ fun k hk => ?_
            obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
            have hk0 : k ∈ C.E0 := by
              have h1 := mem_conjugate_iff.mp hk1
              have h3 := C.fus_sc _ h1 m' (by rwa [show m'⁻¹ * (m' * k * m'⁻¹) * m' = k by group])
              rwa [show m'⁻¹ * (m' * k * m'⁻¹) * m' = k by group] at h3
            obtain ⟨v, hv, rfl⟩ := C.mem_E0_iff.mp hk0
            refine ⟨v, ?_, rfl⟩
            simp only [Set.mem_ofPred_eq, Bool.and_eq_true, isEvenB_iff.mpr hv, true_and,
              List.all_cons, List.all_nil, Bool.and_true]
            exact veq_iff.mpr (C.fix_of_le_W hAW hAc hk1 _ ht)
          have hpos : 0 < Nat.card (C.ψW hAW).range := Nat.card_pos
          nlinarith
    intro x hx
    have hxW := hAW hx
    exact C.exists_mul_of_π0 hyU hyN hyW hxW (hV0 ((C.mem_range_ψW hAW).mpr ⟨x, hx, rfl⟩))
  intro x hx
  obtain ⟨e, he, g, hg, rfl⟩ := hπ0 hm _ hx
  have hmy : m * y ∈ normalizer ((C.Q y : Subgroup X) : Set X) :=
    mul_mem hm (C.y_mem_normalizer_Q hyU hyN hyW)
  have hx' : y⁻¹ * (e * g) * y ∈ conjugate C.E0 (m * y) := by
    rw [mem_conjugate_iff] at hx ⊢
    rwa [show m * y * (y⁻¹ * (e * g) * y) * (m * y)⁻¹ = m * (e * g) * m⁻¹ by group]
  obtain ⟨e', he', g', hg', hx''⟩ := hπ0 hmy _ hx'
  have hxeq : e * g = (y * g' * y⁻¹) * ((y * g' * y⁻¹)⁻¹ * (y * e' * y⁻¹) * (y * g' * y⁻¹)) := by
    calc e * g = y * (y⁻¹ * (e * g) * y) * y⁻¹ := by group
      _ = y * (e' * g') * y⁻¹ := by rw [hx'']
      _ = _ := by group
  have hg'0 : y * g' * y⁻¹ ∈ C.E0 := by
    rw [mem_conjugate_iff] at hg'
    exact hg'
  have he'y : y * e' * y⁻¹ ∈ conjugate C.E y := by
    rw [← C.conj_inv_eq hyU hyN hyW C.W_le_normalizer_E, mem_conjugate_iff, inv_inv]
    rwa [show y⁻¹ * (y * e' * y⁻¹) * y = e' by group]
  have hconj : (y * g' * y⁻¹)⁻¹ * (y * e' * y⁻¹) * (y * g' * y⁻¹) ∈ conjugate C.E y := by
    have := (mem_normalizer_iff.mp (inv_mem (C.E_le_normalizer_Ey hyN
      (C.E0_le_E hg'0))) _).mp he'y
    rwa [inv_inv] at this
  have hpar := C.parity_eq hyU hyN hyW he (C.E0_le_E hg'0) (C.conj_E0_le y hg) hconj hxeq
  exact mul_mem (mem_sup_left (hpar.mpr hg'0)) (mem_sup_right hg)

omit [Finite X] hyU hyN hyW in
theorem le_or_le_of_forall {A B B' : Subgroup X} (h : ∀ x ∈ A, x ∈ B ∨ x ∈ B') :
    A ≤ B ∨ A ≤ B' := by
  by_contra hne
  push Not at hne
  obtain ⟨hAB, hAB'⟩ := hne
  obtain ⟨b, hbA, hbB⟩ := Set.not_subset.mp hAB
  obtain ⟨b', hb'A, hb'B'⟩ := Set.not_subset.mp hAB'
  have hb := (h b hbA).resolve_left hbB
  have hb' := (h b' hb'A).resolve_right hb'B'
  rcases h (b * b') (mul_mem hbA hb'A) with h1 | h1
  · exact hbB (by simpa using mul_mem h1 (inv_mem hb'))
  · exact hb'B' (by simpa using mul_mem (inv_mem hb) h1)

theorem conj_E0_cases {m : X} (hm : m ∈ normalizer ((C.Q y : Subgroup X) : Set X)) :
    conjugate C.E0 m = C.E0 ∨ conjugate C.E0 m = conjugate C.E0 y := by
  have hle := C.conj_E0_le_Q0 hyU hyN hyW hm
  have h1 : ∀ x ∈ conjugate C.E0 m, x ∈ C.E0 ∨ x ∈ conjugate C.E0 y := by
    intro x hx
    refine C.mem_or_mem_of_sq hyU hyN hyW (hle hx) ?_
    rw [mem_conjugate_iff] at hx
    have := C.E_sq (C.E0_le_E hx)
    calc x * x = m⁻¹ * ((m * x * m⁻¹) * (m * x * m⁻¹)) * m := by group
      _ = 1 := by rw [this]; group
  rcases le_or_le_of_forall h1 with h | h
  · left
    exact eq_of_le_of_card_ge h (by rw [Eight.card_conjugate_eq])
  · right
    exact eq_of_le_of_card_ge h (by rw [Eight.card_conjugate_eq, Eight.card_conjugate_eq])

theorem mem_E_of_comm_E0 {q : X} (hq : q ∈ C.Q y) (hc : ∀ e ∈ C.E0, q * e = e * q) : q ∈ C.E := by
  have hqW := C.Q_le_W hyN hq
  have hπ := C.π_mem_V_of_mem_Q hyU hyN hyW hq
  have h1 := List.all_eq_true.mp Vlist_faithful _ hπ
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h1
  rcases h1 with h1 | ⟨v, -, hv, hfix⟩
  · exact C.π_ker _ hqW.1 h1
  · exfalso
    have := (C.comm_iff ⟨q, hqW.2⟩ v).mp (hc _ (C.mem_E0_iff.mpr ⟨v, isEvenB_iff.mp hv, rfl⟩))
    rw [← veq_iff] at this
    rw [this] at hfix
    exact Bool.false_ne_true hfix.symm

end Step10

section Step11

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

theorem NUW_eq : C.NUW = C.U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨T, hT⟩ := C.U_sylow
  have hU2 : IsPGroup 2 C.U := hT ▸ T.isPGroup'
  obtain ⟨w, hwU, hwN, hwn⟩ := Eight.exists_mem_normalizer_not_mem hU2 inf_le_left hne
  have hyNUW : y ∈ C.NUW := ⟨hyU, hyN⟩
  have hwQ : w ∈ normalizer ((C.Q y : Subgroup X) : Set X) := by
    have h1 : conjugate (C.Q y) w⁻¹ ≤ C.NUW := by
      intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have := hwn _ ((C.W_le_NUW.trans le_rfl) (C.Q_le_W hyN hx))
      rwa [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at this
    have h2 := C.conj_Q_eq hyU hyN hyW h1
    simpa using inv_mem (mem_normalizer_of_conjugate_eq h2)
  obtain ⟨w', hw'U, hw'N, hw'Q, hw'0⟩ : ∃ w' : X, w' ∈ C.U ∧ w' ∉ C.NUW ∧
      w' ∈ normalizer ((C.Q y : Subgroup X) : Set X) ∧ conjugate C.E0 w' = C.E0 := by
    rcases C.conj_E0_cases hyU hyN hyW hwQ with h | h
    · exact ⟨w, hwU, hwN, hwQ, h⟩
    · refine ⟨w * y⁻¹, mul_mem hwU (inv_mem hyU), fun h' => hwN ?_,
        mul_mem hwQ (inv_mem (C.y_mem_normalizer_Q hyU hyN hyW)), ?_⟩
      · have := mul_mem h' hyNUW
        rwa [inv_mul_cancel_right] at this
      · rw [← conjugate_conjugate, h, conjugate_conjugate, mul_inv_cancel]
        ext x
        rw [mem_conjugate_iff]
        simp
  have hle : conjugate C.E w' ≤ C.E := by
    intro x hx
    have hxQ : x ∈ C.Q y := by
      rw [mem_conjugate_iff] at hx
      have := (mem_normalizer_iff.mp (inv_mem hw'Q) _).mp (mem_sup_left hx)
      rwa [show w'⁻¹ * (w' * x * w'⁻¹) * w'⁻¹⁻¹ = x by group] at this
    refine C.mem_E_of_comm_E0 hyU hyN hyW hxQ fun e he => ?_
    have he' : e ∈ conjugate C.E0 w' := by rw [hw'0]; exact he
    rw [mem_conjugate_iff] at hx he'
    have := C.E_comm hx (C.E0_le_E he')
    calc x * e = w'⁻¹ * ((w' * x * w'⁻¹) * (w' * e * w'⁻¹)) * w' := by group
      _ = w'⁻¹ * ((w' * e * w'⁻¹) * (w' * x * w'⁻¹)) * w' := by rw [this]
      _ = e * x := by group
  have heq : conjugate C.E w' = C.E := eq_of_le_of_card_ge hle (by rw [Eight.card_conjugate_eq])
  exact hw'N (C.W_le_NUW ⟨hw'U, mem_normalizer_of_conjugate_eq heq⟩)

end Step11

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
