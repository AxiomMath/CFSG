module

public import CFSG.CGT.Foote81L6.TStruct.Classes

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

namespace TStruct

variable {G : Type*} [Group G]

theorem mem_normalizer_inf_centralizer {P : Subgroup G} [Finite P] {τ y : G}
    (hy : y ∈ normalizer (P : Set G)) (hyτ : y * τ = τ * y) :
    y ∈ normalizer ((P ⊓ centralizer ({τ} : Set G) : Subgroup G) : Set G) := by
  haveI : Finite ↥(P ⊓ centralizer ({τ} : Set G)) :=
    Finite.of_injective _ (inclusion_injective (inf_le_left : P ⊓ centralizer ({τ} : Set G) ≤ P))
  refine mem_normalizer_of_forall_conj_mem fun z hz => ?_
  obtain ⟨hzP, hzc⟩ := mem_inf.1 hz
  have hzτ : z * τ = τ * z := mem_centralizer_singleton_iff.1 hzc
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hy z).1 hzP, mem_centralizer_singleton_iff.2 ?_⟩
  have hyτ' : y⁻¹ * τ = τ * y⁻¹ := by
    calc y⁻¹ * τ = y⁻¹ * (τ * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * τ) * y⁻¹ := by rw [hyτ]
      _ = τ * y⁻¹ := by group
  calc y * z * y⁻¹ * τ = y * z * (y⁻¹ * τ) := by group
    _ = y * (z * τ) * y⁻¹ := by rw [hyτ']; group
    _ = y * (τ * z) * y⁻¹ := by rw [hzτ]
    _ = (y * τ) * z * y⁻¹ := by group
    _ = τ * (y * z * y⁻¹) := by rw [hyτ]; group

theorem map_conj_map_conj_of_fixed {Q : Subgroup G} {τ : G}
    (hQ : Q.map (MulAut.conj τ).toMonoidHom = Q) (β : G) :
    (Q.map (MulAut.conj β).toMonoidHom).map (MulAut.conj τ).toMonoidHom =
      Q.map (MulAut.conj (τ * β * τ⁻¹)).toMonoidHom := by
  conv_rhs => rw [← hQ]
  rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel_right]

end TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

@[expose] def tConj (X : Subgroup G) : Subgroup G := X.map (MulAut.conj D.t).toMonoidHom

theorem tConj_tConj (X : Subgroup G) : D.tConj (D.tConj X) = X := by
  rw [tConj, tConj, map_conj_map_conj, D.t_mul_t, map_conj_one]

theorem tConj_le_B₀t {V : Subgroup G} (hV : V ≤ D.B₀) : D.tConj V ≤ D.B₀t := map_mono hV

theorem tConj_inf_B₀B₁ (X : Subgroup G) :
    D.tConj (X ⊓ (D.B₀ ⊔ D.B₁)) = D.tConj X ⊓ (D.B₀ ⊔ D.B₁) := by
  simp only [tConj]
  rw [map_conj_inf, map_conj_eq_self_of_mem_normalizer D.t_mem_normalizer_B₀B₁]

theorem typ_inf_B₀B₁ (X : Subgroup G) : D.typ (X ⊓ (D.B₀ ⊔ D.B₁)) = D.typ X := by
  rw [typ, typ, inf_assoc, inf_of_le_right (le_sup_left : D.B₀ ≤ D.B₀ ⊔ D.B₁), inf_assoc,
    inf_of_le_right (le_sup_right : D.B₁ ≤ D.B₀ ⊔ D.B₁)]

theorem mul_mem_B₀B₁_of_not_mem {x y : G} (hx : x ∈ D.B) (hx' : x ∉ D.B₀ ⊔ D.B₁) (hy : y ∈ D.B)
    (hy' : y ∉ D.B₀ ⊔ D.B₁) : x * y ∈ D.B₀ ⊔ D.B₁ := by
  have hxs := (D.mem_B_iff.1 hx).resolve_left hx'
  have hys := (D.mem_B_iff.1 hy).resolve_left hy'
  have h2 := (mem_normalizer_iff.1 (inv_mem D.s_mem_normalizer_B₀B₁) _).1 hys
  have e : x * y = (x * D.s) * (D.s⁻¹ * (y * D.s) * D.s⁻¹⁻¹) := by
    calc x * y = x * y * (D.s * D.s) := by rw [D.s_mul_s, mul_one]
      _ = (x * D.s) * (D.s⁻¹ * (y * D.s) * D.s⁻¹⁻¹) := by group
  rw [e]
  exact mul_mem hxs h2

@[expose] def IsE16 (P : Subgroup G) : Prop :=
  P ≤ D.B₀ ⊔ D.B₁ ∧ (∀ x ∈ P, x * x = 1) ∧ Nat.card P = 16

theorem E16_decomp {P : Subgroup G} (hP : D.IsE16 P) :
    P = (P ⊓ D.B₀) ⊔ (P ⊓ D.B₁) ∧ IsFourIn D.B₀ (P ⊓ D.B₀) ∧ IsFourIn D.B₁ (P ⊓ D.B₁) := by
  haveI := D.finite_B₀
  haveI := D.finite_B₁
  obtain ⟨hdec, h0, h1⟩ := eq_sup_inf_of_card D.B₀_comm_B₁ D.B₀_inf_B₁ D.elemBound_B₀
    D.elemBound_B₁ hP.1 hP.2.1 (hP.2.2.trans (by norm_num))
  exact ⟨hdec, ⟨inf_le_right, fun x hx => hP.2.1 x (mem_inf.1 hx).1, h0⟩,
    ⟨inf_le_right, fun x hx => hP.2.1 x (mem_inf.1 hx).1, h1⟩⟩

theorem isE16_inf_B₀B₁ {E : Subgroup G} (hE : IsE64 T E) : D.IsE16 (E ⊓ (D.B₀ ⊔ D.B₁)) := by
  haveI := D.finite_A
  haveI := D.finite_B₀B₁
  obtain ⟨-, -, h16⟩ := eq_sup_inf_of_card D.A_comm_B₀B₁ D.A_inf_B₀B₁ D.elemBound_A
    (ElemBound.sup D.B₀_comm_B₁ D.B₀_inf_B₁ D.elemBound_B₀ D.elemBound_B₁)
    (D.le_T₁_of_isE64 hE) hE.mul_self (by rw [hE.2.2]; norm_num)
  exact ⟨inf_le_right, fun x hx => hE.mul_self x (mem_inf.1 hx).1, h16.trans (by norm_num)⟩

theorem isE16_map_conj {P : Subgroup G} (hP : D.IsE16 P) {y : G} (hy : y ∈ T) :
    D.IsE16 (P.map (MulAut.conj y).toMonoidHom) :=
  ⟨map_conj_le hP.1 fun _ hw => D.conj_mem_B₀B₁ hy hw, mul_self_map_conj hP.2.1 y,
    by rw [card_map_conj, hP.2.2]⟩

theorem isE16_tConj {P : Subgroup G} (hP : D.IsE16 P) : D.IsE16 (D.tConj P) :=
  D.isE16_map_conj hP D.t_mem_T

theorem typ_map_conj_B₀B₁ {P : Subgroup G} (hP : D.IsE16 P) {β : G} (hβ : β ∈ D.B₀ ⊔ D.B₁) :
    D.typ (P.map (MulAut.conj β).toMonoidHom) = D.typ P := by
  obtain ⟨-, h₀, h₁⟩ := D.E16_decomp hP
  exact D.typ_map_conj_T₁ h₀ h₁ (D.B₀B₁_le_T₁ hβ)

theorem exists_conj_E16_of_typ_eq {P P' : Subgroup G} (hP : D.IsE16 P) (hP' : D.IsE16 P')
    (h : D.typ P = D.typ P') : ∃ β ∈ D.B₀ ⊔ D.B₁, P.map (MulAut.conj β).toMonoidHom = P' := by
  obtain ⟨hdec, h₀, h₁⟩ := D.E16_decomp hP
  obtain ⟨hdec', h₀', h₁'⟩ := D.E16_decomp hP'
  obtain ⟨β₀, hβ₀, β₁, hβ₁, e₀, e₁⟩ := D.exists_conj_parts_of_typ_eq h₀ h₁ h₀' h₁' h
  refine ⟨β₀ * β₁, mul_mem (mem_sup_left hβ₀) (mem_sup_right hβ₁), ?_⟩
  have eB₀ : (P ⊓ D.B₀).map (MulAut.conj (β₀ * β₁)).toMonoidHom = P' ⊓ D.B₀ := by
    rw [← e₀]
    refine map_conj_eq_of_agree fun v hv => ?_
    have := D.conj_mul_of_mem_B₀ (one_mem D.A) hβ₀ hβ₁ (mem_inf.1 hv).2
    rwa [one_mul] at this
  have eB₁ : (P ⊓ D.B₁).map (MulAut.conj (β₀ * β₁)).toMonoidHom = P' ⊓ D.B₁ := by
    rw [← e₁]
    refine map_conj_eq_of_agree fun v hv => ?_
    have := D.conj_mul_of_mem_B₁ (one_mem D.A) hβ₀ hβ₁ (mem_inf.1 hv).2
    rwa [one_mul] at this
  conv_lhs => rw [hdec]
  conv_rhs => rw [hdec']
  rw [Subgroup.map_sup, eB₀, eB₁]

theorem exists_swap_of_symm {X : Subgroup G} (h₀ : IsFourIn D.B₀ (X ⊓ D.B₀))
    (h₁ : IsFourIn D.B₁ (X ⊓ D.B₁)) (hsym : (D.typ X).1 = (D.typ X).2) :
    ∃ s' ∈ D.B, s' ∉ D.B₀ ⊔ D.B₁ ∧ s' * s' = 1 ∧
      D.B₀.map (MulAut.conj s').toMonoidHom = D.B₁ ∧
      (X ⊓ D.B₀).map (MulAut.conj s').toMonoidHom = X ⊓ D.B₁ ∧
      (X ⊓ D.B₁).map (MulAut.conj s').toMonoidHom = X ⊓ D.B₀ := by
  obtain ⟨w, hw, hwV⟩ := (D.cls_eq_iff h₀ (D.isFourIn_sConj₁ h₁)).1 hsym
  have hs2 : w⁻¹ * D.s * w * (w⁻¹ * D.s * w) = 1 := by
    calc w⁻¹ * D.s * w * (w⁻¹ * D.s * w) = w⁻¹ * (D.s * D.s) * w := by group
      _ = 1 := by rw [D.s_mul_s]; group
  have hsplit : ∀ Y : Subgroup G, Y.map (MulAut.conj (w⁻¹ * D.s * w)).toMonoidHom =
      ((Y.map (MulAut.conj w).toMonoidHom).map (MulAut.conj D.s).toMonoidHom).map
        (MulAut.conj w⁻¹).toMonoidHom := fun Y => by
    rw [map_conj_map_conj, map_conj_map_conj, mul_assoc]
  have hss : (D.sConj (X ⊓ D.B₁)).map (MulAut.conj D.s).toMonoidHom = X ⊓ D.B₁ :=
    D.sConj_sConj _
  have e₀ : (X ⊓ D.B₀).map (MulAut.conj (w⁻¹ * D.s * w)).toMonoidHom = X ⊓ D.B₁ := by
    rw [hsplit, hwV, hss]
    exact map_conj_eq_self_of_comm fun x hx => D.B₀_comm_B₁ _ (inv_mem hw) x (mem_inf.1 hx).2
  refine ⟨w⁻¹ * D.s * w, mul_mem (mul_mem (inv_mem (D.B₀_le_B hw)) D.s_mem_B) (D.B₀_le_B hw),
    fun h => D.s_not_mem_B₀B₁ ?_, hs2, ?_, e₀, ?_⟩
  · rw [show D.s = w * (w⁻¹ * D.s * w) * w⁻¹ by group]
    exact mul_mem (mul_mem (mem_sup_left hw) h) (inv_mem (mem_sup_left hw))
  · rw [hsplit, map_conj_eq_self_of_mem_normalizer (le_normalizer hw), D.conj_s_B₀]
    exact map_conj_eq_self_of_comm fun x hx => D.B₀_comm_B₁ _ (inv_mem hw) x hx
  · rw [← e₀, map_conj_map_conj, hs2, map_conj_one]

theorem exists_s_normalizer {E : Subgroup G} (hE : IsE64 T E)
    (hsym : (D.typ E).1 = (D.typ E).2) :
    ∃ s' ∈ D.B ⊓ normalizer (E : Set G), D.B₀.map (MulAut.conj s').toMonoidHom = D.B₁ := by
  obtain ⟨hdec, -, h₀, h₁⟩ := D.E64_decomp hE
  obtain ⟨s', hs'B, -, -, hB, e₀, e₁⟩ := D.exists_swap_of_symm h₀ h₁ hsym
  refine ⟨s', mem_inf.2 ⟨hs'B, mem_normalizer_of_map_conj_eq ?_⟩, hB⟩
  have eA : (E ⊓ D.A).map (MulAut.conj s').toMonoidHom = E ⊓ D.A :=
    map_conj_eq_self_of_comm fun x hx => (D.A_comm_B x (mem_inf.1 hx).2 s' hs'B).symm
  conv_lhs => rw [hdec]
  rw [Subgroup.map_sup, Subgroup.map_sup, eA, e₀, e₁, sup_comm (E ⊓ D.B₁)]
  exact hdec.symm

@[expose] def pairT (V : Subgroup G) : Subgroup G := V ⊔ D.tConj V

theorem comm_tConj {V : Subgroup G} (hV : V ≤ D.B₀) :
    ∀ x ∈ V, ∀ y ∈ D.tConj V, x * y = y * x :=
  fun _ hx _ hy => D.B₀_comm_B₀t (hV hx) (D.tConj_le_B₀t hV hy)

theorem inf_tConj {V : Subgroup G} (hV : V ≤ D.B₀) : V ⊓ D.tConj V = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf hV (D.tConj_le_B₀t hV)).trans D.B₀_inf_B₀t.le)

theorem pairT_le {V : Subgroup G} (hV : V ≤ D.B₀) : D.pairT V ≤ D.B₀ ⊔ D.B₁ :=
  sup_le (hV.trans le_sup_left) ((D.tConj_le_B₀t hV).trans D.B₀t_le_B₀B₁)

theorem mem_pairT {V : Subgroup G} (hV : V ≤ D.B₀) {x : G} :
    x ∈ D.pairT V ↔ ∃ v ∈ V, ∃ u ∈ D.tConj V, x = v * u :=
  mem_sup_iff_of_le_normalizer (le_normalizer_of_comm (D.comm_tConj hV))

theorem pairT_inf_B₀ {V : Subgroup G} (hV : V ≤ D.B₀) : D.pairT V ⊓ D.B₀ = V := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hV)
  obtain ⟨hxP, hxB⟩ := mem_inf.1 hx
  obtain ⟨v, hv, u, hu, rfl⟩ := (D.mem_pairT hV).1 hxP
  have hu1 : u ∈ D.B₀ ⊓ D.B₀t := by
    refine mem_inf.2 ⟨?_, D.tConj_le_B₀t hV hu⟩
    rw [show u = v⁻¹ * (v * u) by group]
    exact mul_mem (inv_mem (hV hv)) hxB
  rw [D.B₀_inf_B₀t, mem_bot] at hu1
  rw [hu1, mul_one]
  exact hv

theorem pairT_inf_B₀t {V : Subgroup G} (hV : V ≤ D.B₀) : D.pairT V ⊓ D.B₀t = D.tConj V := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right (D.tConj_le_B₀t hV))
  obtain ⟨hxP, hxB⟩ := mem_inf.1 hx
  obtain ⟨v, hv, u, hu, rfl⟩ := (D.mem_pairT hV).1 hxP
  have hv1 : v ∈ D.B₀ ⊓ D.B₀t := by
    refine mem_inf.2 ⟨hV hv, ?_⟩
    rw [show v = (v * u) * u⁻¹ by group]
    exact mul_mem hxB (inv_mem (D.tConj_le_B₀t hV hu))
  rw [D.B₀_inf_B₀t, mem_bot] at hv1
  rw [hv1, one_mul]
  exact hu

theorem tConj_pairT (V : Subgroup G) : D.tConj (D.pairT V) = D.pairT V := by
  change (V ⊔ D.tConj V).map (MulAut.conj D.t).toMonoidHom = V ⊔ D.tConj V
  rw [Subgroup.map_sup]
  change D.tConj V ⊔ D.tConj (D.tConj V) = V ⊔ D.tConj V
  rw [D.tConj_tConj, sup_comm]

theorem t_mem_normalizer_pairT (V : Subgroup G) :
    D.t ∈ normalizer ((D.pairT V : Subgroup G) : Set G) :=
  mem_normalizer_of_map_conj_eq (D.tConj_pairT V)

theorem mul_self_pairT {V : Subgroup G} (hV : IsFourIn D.B₀ V) :
    ∀ x ∈ D.pairT V, x * x = 1 :=
  fun _ hx => mul_self_of_mem_sup hV.2.1 (mul_self_map_conj hV.2.1 D.t) (D.comm_tConj hV.1) hx

theorem card_pairT {V : Subgroup G} (hV : IsFourIn D.B₀ V) : Nat.card (D.pairT V) = 16 := by
  have h : Nat.card (D.pairT V) = 4 * 4 := by
    rw [pairT, card_sup_of_le_normalizer (le_normalizer_of_comm (D.comm_tConj hV.1))
      (D.inf_tConj hV.1), tConj, card_map_conj, hV.2.2]
  exact h.trans (by norm_num)

theorem isE16_pairT {V : Subgroup G} (hV : IsFourIn D.B₀ V) : D.IsE16 (D.pairT V) :=
  ⟨D.pairT_le hV.1, D.mul_self_pairT hV, D.card_pairT hV⟩

theorem finite_pairT {V : Subgroup G} (hV : IsFourIn D.B₀ V) : Finite (D.pairT V) :=
  Nat.finite_of_card_ne_zero (by rw [D.card_pairT hV]; norm_num)

theorem mem_normalizer_pairT_of_mem {V : Subgroup G} (hV : IsFourIn D.B₀ V) {r : G}
    (hr : r ∈ D.B₀ ⊓ normalizer (V : Set G)) :
    r ∈ normalizer ((D.pairT V : Subgroup G) : Set G) := by
  haveI := D.finite_pairT hV
  obtain ⟨hrB, hrN⟩ := mem_inf.1 hr
  refine mem_normalizer_of_forall_conj_mem fun p hp => ?_
  obtain ⟨v, hv, u, hu, rfl⟩ := (D.mem_pairT hV.1).1 hp
  have hru : r * u = u * r := D.B₀_comm_B₀t hrB (D.tConj_le_B₀t hV.1 hu)
  have hru' : u * r⁻¹ = r⁻¹ * u := by
    calc u * r⁻¹ = r⁻¹ * (r * u) * r⁻¹ := by group
      _ = r⁻¹ * (u * r) * r⁻¹ := by rw [hru]
      _ = r⁻¹ * u := by group
  have e : r * (v * u) * r⁻¹ = (r * v * r⁻¹) * u := by
    calc r * (v * u) * r⁻¹ = r * v * (u * r⁻¹) := by group
      _ = r * v * (r⁻¹ * u) := by rw [hru']
      _ = (r * v * r⁻¹) * u := by group
  rw [e]
  exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hrN v).1 hv)) (mem_sup_right hu)

theorem inf_normalizer_pairT_le {V : Subgroup G} (hV : IsFourIn D.B₀ V) :
    (D.B₀ ⊔ D.B₁) ⊓ normalizer ((D.pairT V : Subgroup G) : Set G) ≤
      (D.B₀ ⊓ normalizer (V : Set G)) ⊔
        (D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G)) := by
  haveI : Finite V := hV.finite
  haveI : Finite (D.tConj V) := Nat.finite_of_card_ne_zero (by
    rw [tConj, card_map_conj, hV.2.2]; norm_num)
  intro w hw
  obtain ⟨hwB, hwN⟩ := mem_inf.1 hw
  rw [← D.B₀_sup_B₀t] at hwB
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    fun x hx y hy => D.B₀_comm_B₀t hx hy)).1 hwB
  refine mul_mem (mem_sup_left (mem_inf.2 ⟨hw₀, ?_⟩)) (mem_sup_right (mem_inf.2 ⟨hw₁, ?_⟩))
  · refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    have hc : w₁ * v = v * w₁ := (D.B₀_comm_B₀t (hV.1 hv) hw₁).symm
    have e : w₀ * w₁ * v * (w₀ * w₁)⁻¹ = w₀ * v * w₀⁻¹ := by
      calc w₀ * w₁ * v * (w₀ * w₁)⁻¹ = w₀ * (w₁ * v) * w₁⁻¹ * w₀⁻¹ := by group
        _ = w₀ * v * w₀⁻¹ := by rw [hc]; group
    have h2 : w₀ * w₁ * v * (w₀ * w₁)⁻¹ ∈ D.pairT V ⊓ D.B₀ := mem_inf.2
      ⟨(mem_normalizer_iff.1 hwN v).1 (show v ∈ D.pairT V from mem_sup_left hv),
        by rw [e]; exact mul_mem (mul_mem hw₀ (hV.1 hv)) (inv_mem hw₀)⟩
    rwa [D.pairT_inf_B₀ hV.1, e] at h2
  · refine mem_normalizer_of_forall_conj_mem fun u hu => ?_
    have huB : u ∈ D.B₀t := D.tConj_le_B₀t hV.1 hu
    have hy : w₁ * u * w₁⁻¹ ∈ D.B₀t := mul_mem (mul_mem hw₁ huB) (inv_mem hw₁)
    have hc : w₀ * (w₁ * u * w₁⁻¹) = (w₁ * u * w₁⁻¹) * w₀ := D.B₀_comm_B₀t hw₀ hy
    have e : w₀ * w₁ * u * (w₀ * w₁)⁻¹ = w₁ * u * w₁⁻¹ := by
      calc w₀ * w₁ * u * (w₀ * w₁)⁻¹ = (w₀ * (w₁ * u * w₁⁻¹)) * w₀⁻¹ := by group
        _ = w₁ * u * w₁⁻¹ := by rw [hc]; group
    have h2 : w₀ * w₁ * u * (w₀ * w₁)⁻¹ ∈ D.pairT V ⊓ D.B₀t := mem_inf.2
      ⟨(mem_normalizer_iff.1 hwN u).1 (show u ∈ D.pairT V from mem_sup_right hu),
        by rw [e]; exact hy⟩
    rwa [D.pairT_inf_B₀t hV.1, e] at h2

theorem card_pairT_inf_centralizer {V : Subgroup G} (hV : IsFourIn D.B₀ V) :
    Nat.card ↥(D.pairT V ⊓ centralizer ({D.t} : Set G)) = 4 := by
  haveI := D.finite_pairT hV
  haveI : Finite ↥(D.pairT V ⊓ centralizer ({D.t} : Set G)) :=
    Finite.of_injective _ (inclusion_injective
      (inf_le_left : D.pairT V ⊓ centralizer ({D.t} : Set G) ≤ D.pairT V))
  have hXY : ∀ x ∈ V, D.t * x * D.t⁻¹ ∈ D.tConj V := fun x hx => conj_mem_map_conj hx
  have hinj := wreathDiag_injective (D.comm_tConj hV.1) (D.inf_tConj hV.1) D.t hXY
  have hle : (wreathDiag (D.comm_tConj hV.1) D.t hXY).range ≤
      D.pairT V ⊓ centralizer ({D.t} : Set G) := by
    intro y hy
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hy
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2
      (wreathDiag_comm (D.comm_tConj hV.1) D.t_mul_t hXY v)⟩
    rw [wreathDiag_apply]
    exact mul_mem (mem_sup_left v.2) (mem_sup_right (hXY v v.2))
  apply le_antisymm
  · refine D.elemBound_CBt _ ?_ fun x hx => D.mul_self_pairT hV x (mem_inf.1 hx).1
    exact inf_le_inf_right _ ((D.pairT_le hV.1).trans D.B₀B₁_le_B)
  · calc 4 = Nat.card V := hV.2.2.symm
      _ = Nat.card (wreathDiag (D.comm_tConj hV.1) D.t hXY).range :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      _ ≤ _ := card_le_of_le hle

theorem not_mem_normalizer_pairT {V : Subgroup G} (hV : IsFourIn D.B₀ V) {x : G} (hxB : x ∈ D.B)
    (hx : x ∉ D.B₀ ⊔ D.B₁) : x ∉ normalizer ((D.pairT V : Subgroup G) : Set G) := by
  intro hxN
  obtain ⟨e⟩ := D.B₀_iso
  haveI := D.finite_pairT hV
  have hR0 : D.B₀ ⊓ normalizer (V : Set G) ≤ D.B₀ := inf_le_left
  have hR'0 : D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G) ≤ D.B₀t := inf_le_left
  have hc : ∀ y ∈ D.B₀ ⊓ normalizer (V : Set G),
      ∀ z ∈ D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G), y * z = z * y :=
    fun y hy z hz => D.B₀_comm_B₀t (hR0 hy) (hR'0 hz)
  have hd : (D.B₀ ⊓ normalizer (V : Set G)) ⊓
      (D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G)) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hR0 hR'0).trans D.B₀_inf_B₀t.le)
  have hXY : ∀ y ∈ D.B₀ ⊓ normalizer (V : Set G),
      D.t * y * D.t⁻¹ ∈ D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G) :=
    fun y hy => mem_inf.2 ⟨D.conj_t_mem_B₀t (hR0 hy),
      conj_mem_normalizer_map_conj (mem_inf.1 hy).2⟩
  have hYX : ∀ z ∈ D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G),
      D.t * z * D.t⁻¹ ∈ D.B₀ ⊓ normalizer (V : Set G) :=
    fun z hz => mem_inf.2 ⟨D.mem_B₀t_iff.1 (hR'0 hz),
      conj_mem_normalizer_of_map_conj_eq (D.tConj_tConj V) (mem_inf.1 hz).2⟩
  have hxt : x * D.t * x⁻¹ * D.t⁻¹ ∈ (D.B₀ ⊓ normalizer (V : Set G)) ⊔
      (D.B₀t ⊓ normalizer ((D.tConj V : Subgroup G) : Set G)) := by
    refine D.inf_normalizer_pairT_le hV (mem_inf.2 ⟨?_, ?_⟩)
    · have hy : D.t * x⁻¹ * D.t⁻¹ ∈ D.B := D.conj_t_B _ (inv_mem hxB)
      have hy' : D.t * x⁻¹ * D.t⁻¹ ∉ D.B₀ ⊔ D.B₁ := by
        intro h
        apply hx
        have h2 := D.conj_mem_B₀B₁ (inv_mem D.t_mem_T) h
        rw [show D.t⁻¹ * (D.t * x⁻¹ * D.t⁻¹) * D.t⁻¹⁻¹ = x⁻¹ by group] at h2
        simpa using inv_mem h2
      rw [show x * D.t * x⁻¹ * D.t⁻¹ = x * (D.t * x⁻¹ * D.t⁻¹) by group]
      exact D.mul_mem_B₀B₁_of_not_mem hxB hx hy hy'
    · have ht := D.t_mem_normalizer_pairT V
      exact mul_mem (mul_mem (mul_mem hxN ht) (inv_mem hxN)) (inv_mem ht)
  have hg2 : x * D.t * x⁻¹ * (x * D.t * x⁻¹) = 1 := by
    calc x * D.t * x⁻¹ * (x * D.t * x⁻¹) = x * (D.t * D.t) * x⁻¹ := by group
      _ = 1 := by rw [D.t_mul_t, mul_one, mul_inv_cancel]
  obtain ⟨u, huR, hu⟩ := exists_conj_of_wreath hc hd D.t_mul_t hXY hYX hxt hg2
  have huB₀ : u ∈ D.B₀ := hR0 huR
  have hqt : u⁻¹ * x * D.t = D.t * (u⁻¹ * x) := by
    have h1 : D.t = u⁻¹ * (x * D.t * x⁻¹) * u := by rw [← hu]; group
    calc u⁻¹ * x * D.t = u⁻¹ * (x * D.t * x⁻¹) * u * (u⁻¹ * x) := by group
      _ = D.t * (u⁻¹ * x) := by rw [← h1]
  have hqB : u⁻¹ * x ∈ D.B := mul_mem (inv_mem (D.B₀_le_B huB₀)) hxB
  have hqn : u⁻¹ * x ∉ D.B₀ ⊔ D.B₁ := by
    intro h
    apply hx
    rw [show x = u * (u⁻¹ * x) by group]
    exact mul_mem (mem_sup_left huB₀) h
  have hqN : u⁻¹ * x ∈ normalizer ((D.pairT V : Subgroup G) : Set G) :=
    mul_mem (inv_mem (D.mem_normalizer_pairT_of_mem hV huR)) hxN
  have hΔ4 := D.card_pairT_inf_centralizer hV
  have hΔB : D.pairT V ⊓ centralizer ({D.t} : Set G) ≤ D.B ⊓ centralizer ({D.t} : Set G) :=
    inf_le_inf_right _ ((D.pairT_le hV.1).trans D.B₀B₁_le_B)
  have hΔ2 : ∀ y ∈ D.pairT V ⊓ centralizer ({D.t} : Set G), y * y = 1 :=
    fun y hy => D.mul_self_pairT hV y (mem_inf.1 hy).1
  obtain ⟨eQ⟩ := D.CBt_iso
  have h8 := card_inf_normalizer_le_of_semidihedral (by have := D.three_le_n; omega) eQ hΔB hΔ2
    hΔ4
  haveI : Finite ↥(D.B ⊓ centralizer ({D.t} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [D.card_CBt]; positivity)
  haveI : Finite ↥(D.B ⊓ centralizer ({D.t} : Set G) ⊓
      normalizer ((D.pairT V ⊓ centralizer ({D.t} : Set G) : Subgroup G) : Set G)) :=
    Finite.of_injective _ (inclusion_injective inf_le_left)
  have hmemM : ∀ y : G, y ∈ D.B → y * D.t = D.t * y →
      y ∈ normalizer ((D.pairT V : Subgroup G) : Set G) →
      y ∈ D.B ⊓ centralizer ({D.t} : Set G) ⊓
        normalizer ((D.pairT V ⊓ centralizer ({D.t} : Set G) : Subgroup G) : Set G) :=
    fun y hyB hyt hyN => mem_inf.2 ⟨mem_inf.2 ⟨hyB, mem_centralizer_singleton_iff.2 hyt⟩,
      mem_normalizer_inf_centralizer hyN hyt⟩
  have hKM : (wreathDiag hc D.t hXY).range ≤ D.B ⊓ centralizer ({D.t} : Set G) ⊓
      normalizer ((D.pairT V ⊓ centralizer ({D.t} : Set G) : Subgroup G) : Set G) := by
    intro k hk
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.1 hk
    have hrN := D.mem_normalizer_pairT_of_mem hV r.2
    have ht := D.t_mem_normalizer_pairT V
    refine hmemM _ ?_ (wreathDiag_comm hc D.t_mul_t hXY r) ?_
    · rw [wreathDiag_apply]
      exact mul_mem (D.B₀_le_B (hR0 r.2)) (D.conj_t_B _ (D.B₀_le_B (hR0 r.2)))
    · rw [wreathDiag_apply]
      exact mul_mem hrN (mul_mem (mul_mem ht hrN) (inv_mem ht))
  have hK8 : Nat.card (wreathDiag hc D.t hXY).range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (wreathDiag_injective hc hd D.t hXY)).toEquiv]
    exact card_inf_normalizer_four e D.two_le_n_sub_one hV
  have hKeq := eq_of_le_of_card_ge hKM (h8.trans hK8.symm.le)
  have hqM := hmemM _ hqB hqt hqN
  rw [← hKeq] at hqM
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hqM
  apply hqn
  rw [← hr, wreathDiag_apply]
  exact mul_mem (mem_sup_left (hR0 r.2)) (D.B₀t_le_B₀B₁ (hR'0 (hXY r r.2)))

theorem exists_conj_pairT {P : Subgroup G} (hP16 : Nat.card P = 16)
    (hV : IsFourIn D.B₀ (P ⊓ D.B₀)) {x : G} (hx : x * D.t⁻¹ ∈ D.B₀ ⊔ D.B₁)
    (hxN : x ∈ normalizer (P : Set G)) :
    ∃ c ∈ D.B₀ ⊔ D.B₁, (D.pairT (P ⊓ D.B₀)).map (MulAut.conj c).toMonoidHom = P := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP16]; norm_num)
  rw [← D.B₀_sup_B₀t] at hx
  obtain ⟨w₀, hw₀, w₁, hw₁, hw⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    fun y hy z hz => D.B₀_comm_B₀t hy hz)).1 hx
  have hxw : x = w₀ * w₁ * D.t := by
    calc x = x * D.t⁻¹ * D.t := by group
      _ = w₀ * w₁ * D.t := by rw [hw]
  refine ⟨w₁, D.B₀t_le_B₀B₁ hw₁, eq_of_le_of_card_ge ?_
    (hP16.trans ((D.card_pairT hV).symm.trans (card_map_conj _ _).symm)).le⟩
  rw [pairT, Subgroup.map_sup, sup_le_iff]
  constructor
  · rw [map_conj_eq_self_of_comm (X := P ⊓ D.B₀)
      fun v hv => (D.B₀_comm_B₀t (mem_inf.1 hv).2 hw₁).symm]
    exact inf_le_left
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hvB : v ∈ D.B₀ := (mem_inf.1 hv).2
    have hy : w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹ ∈ D.B₀t :=
      mul_mem (mul_mem hw₁ (D.conj_t_mem_B₀t hvB)) (inv_mem hw₁)
    have hc : w₀ * (w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹) = (w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹) * w₀ :=
      D.B₀_comm_B₀t hw₀ hy
    have e : x * v * x⁻¹ = w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹ := by
      rw [hxw]
      calc w₀ * w₁ * D.t * v * (w₀ * w₁ * D.t)⁻¹ =
          (w₀ * (w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹)) * w₀⁻¹ := by group
        _ = w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹ := by rw [hc]; group
    show w₁ * (D.t * v * D.t⁻¹) * w₁⁻¹ ∈ P
    rw [← e]
    exact (mem_normalizer_iff.1 hxN v).1 (mem_inf.1 hv).1

theorem not_mem_normalizer_of_symm {P : Subgroup G} (hP : D.IsE16 P)
    (hsym : (D.typ P).1 = (D.typ P).2) {x : G} (hx : x * D.t⁻¹ ∈ D.B₀ ⊔ D.B₁) :
    x ∉ normalizer (P : Set G) := by
  intro hxN
  obtain ⟨hdec, h₀, h₁⟩ := D.E16_decomp hP
  obtain ⟨c, hc, hcP⟩ := D.exists_conj_pairT hP.2.2 h₀ hx hxN
  obtain ⟨s', hs'B, hs'n, -, -, e₀, e₁⟩ := D.exists_swap_of_symm h₀ h₁ hsym
  have hs'N : s' ∈ normalizer (P : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    conv_lhs => rw [hdec]
    rw [Subgroup.map_sup, e₀, e₁, sup_comm]
    exact hdec.symm
  have hY : P.map (MulAut.conj c⁻¹).toMonoidHom = D.pairT (P ⊓ D.B₀) := by
    conv_lhs => rw [← hcP]
    exact map_conj_inv_map_conj _ _
  have hN := conj_mem_normalizer_of_map_conj_eq hY hs'N
  rw [inv_inv] at hN
  refine D.not_mem_normalizer_pairT h₀ ?_ ?_ hN
  · exact mul_mem (mul_mem (inv_mem (D.B₀B₁_le_B hc)) hs'B) (D.B₀B₁_le_B hc)
  · intro h
    apply hs'n
    rw [show s' = c * (c⁻¹ * s' * c) * c⁻¹ by group]
    exact mul_mem (mul_mem hc h) (inv_mem hc)

theorem typ_pairT_asymm {V : Subgroup G} (hV : IsFourIn D.B₀ V) :
    (D.typ (D.pairT V)).1 ≠ (D.typ (D.pairT V)).2 := fun h =>
  D.not_mem_normalizer_of_symm (D.isE16_pairT hV) h (x := D.t)
    (by rw [mul_inv_cancel]; exact one_mem _) (D.t_mem_normalizer_pairT V)

theorem typ_tConj_of_asymm {P : Subgroup G} (hP : D.IsE16 P) (h : (D.typ P).1 ≠ (D.typ P).2) :
    D.typ (D.tConj P) = D.typ P := by
  obtain ⟨-, h₀, -⟩ := D.E16_decomp hP
  have hQ := D.isE16_pairT h₀
  have hQ1 : (D.typ (D.pairT (P ⊓ D.B₀))).1 = (D.typ P).1 := by
    simp only [typ]
    rw [D.pairT_inf_B₀ h₀.1]
  have heq : D.typ (D.pairT (P ⊓ D.B₀)) = D.typ P := by
    have key : ∀ a b c d : ZMod 2, a ≠ b → c ≠ d → a = c → (a, b) = (c, d) := by decide
    exact key _ _ _ _ (D.typ_pairT_asymm h₀) h hQ1
  obtain ⟨β, hβ, hβP⟩ := D.exists_conj_E16_of_typ_eq hQ hP heq
  have e : D.tConj P =
      (D.pairT (P ⊓ D.B₀)).map (MulAut.conj (D.t * β * D.t⁻¹)).toMonoidHom := by
    rw [← map_conj_map_conj_of_fixed (D.tConj_pairT _), hβP, tConj]
  rw [e, D.typ_map_conj_B₀B₁ hQ (D.conj_mem_B₀B₁ D.t_mem_T hβ), heq]

theorem typ_tConj_ne_of_symm {P : Subgroup G} (hP : D.IsE16 P) (h : (D.typ P).1 = (D.typ P).2) :
    D.typ (D.tConj P) ≠ D.typ P := by
  intro heq
  obtain ⟨β, hβ, hβP⟩ := D.exists_conj_E16_of_typ_eq (D.isE16_tConj hP) hP heq
  have hN : β * D.t ∈ normalizer (P : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    rw [← map_conj_map_conj]
    exact hβP
  exact D.not_mem_normalizer_of_symm hP h (by rw [mul_inv_cancel_right]; exact hβ) hN

theorem typ_tConj_E16 {P : Subgroup G} (hP : D.IsE16 P) :
    D.typ (D.tConj P) = ((D.typ P).2 + 1, (D.typ P).1 + 1) := by
  have h1 : (D.typ P).1 ≠ (D.typ P).2 → D.typ (D.tConj P) = D.typ P := D.typ_tConj_of_asymm hP
  have h2 : (D.typ P).1 = (D.typ P).2 → D.typ (D.tConj P) ≠ D.typ P := D.typ_tConj_ne_of_symm hP
  have h3 : (D.typ (D.tConj P)).1 ≠ (D.typ (D.tConj P)).2 → D.typ P = D.typ (D.tConj P) := by
    intro h
    have := D.typ_tConj_of_asymm (D.isE16_tConj hP) h
    rwa [D.tConj_tConj] at this
  generalize D.typ P = τ at h1 h2 h3 ⊢
  generalize D.typ (D.tConj P) = τ' at h1 h2 h3 ⊢
  obtain ⟨a, b⟩ := τ
  obtain ⟨c, d⟩ := τ'
  revert a b c d
  decide

theorem typ_tConj {E : Subgroup G} (hE : IsE64 T E) :
    D.typ (D.tConj E) = ((D.typ E).2 + 1, (D.typ E).1 + 1) := by
  have h := D.typ_tConj_E16 (D.isE16_inf_B₀B₁ hE)
  rwa [D.tConj_inf_B₀B₁, D.typ_inf_B₀B₁, D.typ_inf_B₀B₁] at h

theorem typ_map_conj_of_mem_T₀ {E : Subgroup G} (hE : IsE64 T E) {h : G} (hh : h ∈ D.T₀) :
    D.typ (E.map (MulAut.conj h).toMonoidHom) = D.typ E ∨
      D.typ (E.map (MulAut.conj h).toMonoidHom) = (D.typ E).swap := by
  obtain ⟨-, -, h₀, h₁⟩ := D.E64_decomp hE
  rcases D.mem_T₁_or_mul_s_mem_T₁ hh with h1 | h1
  · exact Or.inl (D.typ_map_conj_T₁ h₀ h₁ h1)
  · right
    obtain ⟨-, -, h₀', h₁'⟩ := D.E64_decomp (hE.map_conj (D.B_le_T D.s_mem_B))
    have e : E.map (MulAut.conj h).toMonoidHom =
        (E.map (MulAut.conj D.s).toMonoidHom).map (MulAut.conj (h * D.s)).toMonoidHom := by
      rw [map_conj_map_conj, mul_assoc, D.s_mul_s, mul_one]
    rw [e, D.typ_map_conj_T₁ h₀' h₁' h1, D.typ_map_conj_s]

theorem typ_map_conj_of_mem_T {E : Subgroup G} (hE : IsE64 T E) {h : G} (hh : h ∈ T) :
    D.typ (E.map (MulAut.conj h).toMonoidHom) = D.typ E ∨
      D.typ (E.map (MulAut.conj h).toMonoidHom) = (D.typ E).swap ∨
      D.typ (E.map (MulAut.conj h).toMonoidHom) = ((D.typ E).2 + 1, (D.typ E).1 + 1) ∨
      D.typ (E.map (MulAut.conj h).toMonoidHom) = ((D.typ E).1 + 1, (D.typ E).2 + 1) := by
  rcases D.mem_T_iff.1 hh with h0 | h0
  · rcases D.typ_map_conj_of_mem_T₀ hE h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have e : E.map (MulAut.conj h).toMonoidHom =
        (E.map (MulAut.conj D.t).toMonoidHom).map (MulAut.conj (h * D.t)).toMonoidHom := by
      rw [map_conj_map_conj, mul_assoc, D.t_mul_t, mul_one]
    have ht := D.typ_tConj hE
    rw [tConj] at ht
    rw [e]
    rcases D.typ_map_conj_of_mem_T₀ (hE.map_conj D.t_mem_T) h0 with h1 | h1
    · rw [h1, ht]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h1, ht]
      exact Or.inr (Or.inr (Or.inr rfl))

theorem typ_symm_map_conj_iff {E : Subgroup G} (hE : IsE64 T E) {h : G} (hh : h ∈ T) :
    (D.typ (E.map (MulAut.conj h).toMonoidHom)).1 = (D.typ (E.map (MulAut.conj h).toMonoidHom)).2 ↔
      (D.typ E).1 = (D.typ E).2 := by
  have key : ∀ a b c d : ZMod 2, ((c, d) = (a, b) ∨ (c, d) = (b, a) ∨ (c, d) = (b + 1, a + 1) ∨
      (c, d) = (a + 1, b + 1)) → (c = d ↔ a = b) := by decide
  have h1 := D.typ_map_conj_of_mem_T hE hh
  generalize D.typ E = τ at h1 ⊢
  generalize D.typ (E.map (MulAut.conj h).toMonoidHom) = τ' at h1 ⊢
  obtain ⟨a, b⟩ := τ
  obtain ⟨c, d⟩ := τ'
  exact key a b c d h1

theorem not_mem_normalizer_T₁st {E : Subgroup G} (hE : IsE64 T E) {y : G} (hy : y ∈ D.T₁) :
    y * D.s * D.t ∉ normalizer (E : Set G) := by
  intro hN
  have heq := map_conj_eq_self_of_mem_normalizer hN
  have hst := (hE.map_conj D.t_mem_T).map_conj (D.B_le_T D.s_mem_B)
  obtain ⟨-, -, h₀, h₁⟩ := D.E64_decomp hst
  have h1 : ((E.map (MulAut.conj D.t).toMonoidHom).map (MulAut.conj D.s).toMonoidHom).map
      (MulAut.conj y).toMonoidHom = E := by
    rw [map_conj_map_conj, map_conj_map_conj]
    simpa only [mul_assoc] using heq
  have h2 := D.typ_map_conj_T₁ h₀ h₁ hy
  have ht := D.typ_tConj hE
  rw [tConj] at ht
  rw [h1, D.typ_map_conj_s, ht] at h2
  generalize D.typ E = τ at h2
  obtain ⟨a, b⟩ := τ
  revert h2
  revert a b
  decide

theorem mul_t_mem_T₁_of_mem_normalizer {E : Subgroup G} (hE : IsE64 T E) {x : G} (hx : x ∈ T)
    (hx0 : x ∉ D.T₀) (hxN : x ∈ normalizer (E : Set G)) : x * D.t ∈ D.T₁ := by
  have hxt : x * D.t ∈ D.T₀ := (D.mem_T_iff.1 hx).resolve_left hx0
  refine (D.mem_T₁_or_mul_s_mem_T₁ hxt).resolve_right fun h => D.not_mem_normalizer_T₁st hE h ?_
  rw [show x * D.t * D.s * D.s * D.t = x * (D.t * (D.s * D.s) * D.t) by group, D.s_mul_s,
    mul_one, D.t_mul_t, mul_one]
  exact hxN

end FooteCore

end CFSG.CGT.Foote81L6
