module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD5

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem range_card_index {N α : Type*} [Group N] (K : Subgroup N) (f : N → α)
    (hf : ∀ n m : N, f n = f m ↔ n⁻¹ * m ∈ K) : Nat.card (Set.range f) = K.index := by
  let g : N ⧸ K → α := Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((hf _ _).mp hab)
  have hrange : Set.range f = Set.range g := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H n => exact ⟨n, rfl⟩
  rw [hrange, Nat.card_range_of_injective hg]
  rfl

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem V_le_Cq : V ≤ Q ⊓ centralizer ({t * τ} : Set H) := by
  intro v hv
  have hvY : v ∈ Y := by rw [h.Y_eq]; exact Subgroup.mem_sup_left hv
  have hvQ : v ∈ Q := h.Y_le_Q hvY
  have hτ1 : τ * v * τ⁻¹ = v := by
    rw [h.tau_inv v hvQ, inv_eq_of_mul_eq_one_right (h.Y_sq v hvY)]
  have htv : t * v = v * t := h.V_cent_t v hv
  have hτv : τ * v = v * τ := by
    calc τ * v = (τ * v * τ⁻¹) * τ := by group
      _ = v * τ := by rw [hτ1]
  refine Subgroup.mem_inf.mpr ⟨hvQ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc v * (t * τ) = (v * t) * τ := by group
    _ = (t * v) * τ := by rw [← htv]
    _ = t * (v * τ) := by group
    _ = t * (τ * v) := by rw [← hτv]
    _ = (t * τ) * v := by group

theorem inv_Cq {c : H} (hc : c ∈ Q ⊓ centralizer ({t * τ} : Set H)) : t * c * t⁻¹ = c⁻¹ := by
  have hcQ : c ∈ Q := hc.1
  have hcomm : c * (t * τ) = (t * τ) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hconj : (t * τ) * c * (t * τ)⁻¹ = c := by
    rw [← hcomm]; group
  have h1 : t * (τ * c * τ⁻¹) * t⁻¹ = c := by
    have h2 : (t * τ) * c * (t * τ)⁻¹ = t * (τ * c * τ⁻¹) * t⁻¹ := by group
    rw [← h2]; exact hconj
  have h2 : t * c⁻¹ * t⁻¹ = c := by
    have h3 := h1
    rw [h.tau_inv c hcQ] at h3
    exact h3
  calc t * c * t⁻¹ = (t * c⁻¹ * t⁻¹)⁻¹ := by group
    _ = c⁻¹ := by rw [h2]

theorem rho_norm_Cq {c : H} (hc : c ∈ Q ⊓ centralizer ({t * τ} : Set H)) :
    ρ * c * ρ⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
  have hcQ : c ∈ Q := hc.1
  have hcommc : c * (t * τ) = (t * τ) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hρ_tτ : ρ * (t * τ) = (t * τ) * ρ := by
    calc ρ * (t * τ) = (ρ * t) * τ := by group
      _ = (t * ρ) * τ := by rw [h.t_rho]
      _ = t * (ρ * τ) := by group
      _ = t * (τ * ρ) := by rw [h.tau_rho]
      _ = (t * τ) * ρ := by group
  have hρi_tτ : ρ⁻¹ * (t * τ) = (t * τ) * ρ⁻¹ := by
    have h := congrArg (fun x => ρ⁻¹ * x * ρ⁻¹) hρ_tτ
    have h' : (t * τ) * ρ⁻¹ = ρ⁻¹ * (t * τ) := by simpa [mul_assoc] using h
    exact h'.symm
  refine Subgroup.mem_inf.mpr ⟨h.rho_norm_Q c hcQ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (ρ * c * ρ⁻¹) * (t * τ) = ρ * c * (ρ⁻¹ * (t * τ)) := by group
    _ = ρ * c * ((t * τ) * ρ⁻¹) := by rw [hρi_tτ]
    _ = ρ * (c * (t * τ)) * ρ⁻¹ := by group
    _ = ρ * ((t * τ) * c) * ρ⁻¹ := by rw [hcommc]
    _ = (ρ * (t * τ)) * (c * ρ⁻¹) := by group
    _ = ((t * τ) * ρ) * (c * ρ⁻¹) := by rw [hρ_tτ]
    _ = (t * τ) * (ρ * c * ρ⁻¹) := by group

theorem card_Cq_le :
    Nat.card ↥(Q ⊓ centralizer ({t * τ} : Set H)) ≤ 16 := by
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  change Nat.card ↥Cq ≤ 16
  have hCqQ : Cq ≤ Q := inf_le_left
  have hCY : Cq ⊓ Y = V := by
    apply le_antisymm
    · intro u hu
      have huCq : u ∈ Cq := (Subgroup.mem_inf.mp hu).1
      have huY : u ∈ Y := (Subgroup.mem_inf.mp hu).2
      refine h.Y_cent_t u huY ?_
      have hcomm : (t * τ) * u = u * (t * τ) :=
        (Subgroup.mem_centralizer_singleton_iff.mp huCq.2).symm
      have hτu : τ * u = u * τ := by
        calc τ * u = (τ * u * τ⁻¹) * τ := by group
          _ = u⁻¹ * τ := by rw [h.tau_inv u huCq.1]
          _ = u * τ := by rw [inv_eq_of_mul_eq_one_right (h.Y_sq u huY)]
      have h1 : (t * u) * τ = (u * t) * τ := by
        calc (t * u) * τ = t * (u * τ) := by group
          _ = t * (τ * u) := by rw [hτu]
          _ = (t * τ) * u := by group
          _ = u * (t * τ) := hcomm
          _ = (u * t) * τ := by group
      exact mul_right_cancel h1
    · intro u hu
      exact Subgroup.mem_inf.mpr
        ⟨V_le_Cq h hu, by rw [h.Y_eq]; exact Subgroup.mem_sup_left hu⟩
  have he : Y.subgroupOf Cq = (Cq ⊓ Y).subgroupOf Cq := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hcardYsubC : Nat.card (Y.subgroupOf Cq) = 4 := by
    rw [he, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Cq ⊓ Y ≤ Cq)).toEquiv,
      hCY, h.card_V]
  have hcardYsubQ : Nat.card (Y.subgroupOf Q) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Y_le_Q).toEquiv, h.card_Y]
  have hYQidx : (Y.subgroupOf Q).index = 4 := by
    have hmul := Subgroup.index_mul_card (Y.subgroupOf Q)
    rw [hcardYsubQ, h.card_Q] at hmul
    omega
  haveI : Y.IsFiniteRelIndex Q :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have hrelLe : (Y.subgroupOf Cq).index ≤ 4 := by
    have hle := Subgroup.relIndex_le_of_le_right (H := Y) (K := Cq) (L := Q) hCqQ
      (Subgroup.relIndex_ne_zero (H := Y) (K := Q))
    simpa [Subgroup.relIndex, hYQidx] using hle
  have hmul := Subgroup.index_mul_card (Y.subgroupOf Cq)
  rw [hcardYsubC] at hmul
  omega

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

theorem comm_t_mem_Cq {w : H} (hw : w ∈ Mh) :
    w * t * w⁻¹ * t⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
  set c : H := w * t * w⁻¹ * t⁻¹ with hcdef
  have hcQ : c ∈ Q := by rw [hcdef]; exact Mh_comm_t h hMh hw
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have htc : t * c * t⁻¹ = c⁻¹ := by
    have hL : t * c * t⁻¹ = t * w * t * w⁻¹ := by
      rw [hcdef, hti]
      rw [show t * (w * t * w⁻¹ * t) * t = t * w * t * w⁻¹ * (t * t) by group,
        h.t_sq, mul_one]
    have hR : c⁻¹ = t * w * t * w⁻¹ := by
      rw [hcdef, hti]
      simp only [mul_inv_rev, inv_inv, hti]
      group
    rw [hL, hR]
  have hτc : τ * c * τ⁻¹ = c⁻¹ := h.tau_inv c hcQ
  have hconjc : (t * τ) * c * (t * τ)⁻¹ = c := by
    have h1 : t * (τ * c * τ⁻¹) * t⁻¹ = c := by
      rw [hτc]
      calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
        _ = (c⁻¹)⁻¹ := by rw [htc]
        _ = c := inv_inv c
    have h2 : (t * τ) * c * (t * τ)⁻¹ = t * (τ * c * τ⁻¹) * t⁻¹ := by group
    rw [h2, h1]
  have hcommc : c * (t * τ) = (t * τ) * c := by
    have h := congrArg (fun x => x * (t * τ)) hconjc
    have h' : (t * τ) * c = c * (t * τ) := by simpa [mul_assoc] using h
    exact h'.symm
  refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcommc

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

private theorem card_range_conj_t (hb : ZJBound t) :
    Nat.card (Set.range (fun w : Mc => (w : H) * t * (w : H)⁻¹)) = 16 := by
  let f : Mc → H := fun w => (w : H) * t * (w : H)⁻¹
  change Nat.card (Set.range f) = 16
  have hBleMc : B ≤ Mc := h.B_le_Q.trans (Q_le_Mc h hMh hMc)
  let K : Subgroup Mc := B.subgroupOf Mc
  have hf : ∀ n m : Mc, f n = f m ↔ n⁻¹ * m ∈ K := by
    intro n m
    change f n = f m ↔ n⁻¹ * m ∈ B.subgroupOf Mc
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro heq
      have heq' : (n : H) * t * (n : H)⁻¹ = (m : H) * t * (m : H)⁻¹ := heq
      have hcomm : t * ((n : H)⁻¹ * (m : H)) = ((n : H)⁻¹ * (m : H)) * t := by
        have h2 := congrArg (fun x => (n : H)⁻¹ * x * (m : H)) heq'
        convert h2 using 1 <;> group
      exact Mc_cent_t h hMh hMc hb (Mc.mul_mem (Mc.inv_mem n.2) m.2) hcomm
    · intro hnm
      have hcoe : (((n⁻¹ * m : Mc) : H)) = (n : H)⁻¹ * (m : H) := rfl
      have htd : t * (((n⁻¹ * m : Mc) : H)) = (((n⁻¹ * m : Mc) : H)) * t :=
        h.B_cent_t _ hnm
      calc f n = (n : H) * t * (n : H)⁻¹ := rfl
        _ = (n : H) * t * ((((n⁻¹ * m : Mc) : H)) * (m : H)⁻¹) := by
              rw [show (n : H)⁻¹ = (((n⁻¹ * m : Mc) : H)) * (m : H)⁻¹ by
                rw [hcoe]; group]
        _ = (n : H) * (t * (((n⁻¹ * m : Mc) : H))) * (m : H)⁻¹ := by group
        _ = (n : H) * ((((n⁻¹ * m : Mc) : H)) * t) * (m : H)⁻¹ := by rw [htd]
        _ = ((n : H) * (((n⁻¹ * m : Mc) : H))) * t * (m : H)⁻¹ := by group
        _ = (m : H) * t * (m : H)⁻¹ := by
              rw [show (n : H) * (((n⁻¹ * m : Mc) : H)) = (m : H) by
                rw [hcoe]; group]
        _ = f m := rfl
  have hKcard : Nat.card K = 16 := by
    change Nat.card (B.subgroupOf Mc) = 16
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleMc).toEquiv, h.card_B]
  have hMcCard : Nat.card Mc = 256 := card_Mc h hMh hMc
  have hidx : K.index = 16 := by
    have hmul := Subgroup.index_mul_card K
    rw [hKcard, hMcCard] at hmul
    omega
  rw [range_card_index K f hf, hidx]

theorem exists_conj_t (hb : ZJBound t) {c : H} (hc : c ∈ Q ⊓ centralizer ({t * τ} : Set H)) :
    ∃ w ∈ Mc, w * t * w⁻¹ = c * t := by
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  let f : Mc → H := fun w => (w : H) * t * (w : H)⁻¹
  let S : Set H := {x | ∃ d ∈ Cq, x = d * t}
  have hfcard : Nat.card (Set.range f) = 16 := card_range_conj_t h hMh hMc hb
  have hsub : Set.range f ⊆ S := by
    rintro x ⟨w, rfl⟩
    exact ⟨(w : H) * t * (w : H)⁻¹ * t⁻¹,
      comm_t_mem_Cq h hMh (Mc_le_Mh h hMh hMc w.2), by simp only [f]; group⟩
  have hScard : Nat.card S ≤ 16 := by
    let g : Cq → H := fun d => (d : H) * t
    have hinj : Function.Injective g := by
      intro a b hab
      exact Subtype.ext (mul_right_cancel hab)
    have hSe : S = Set.range g := by
      ext x
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨⟨d, hd⟩, rfl⟩
      · rintro ⟨d, rfl⟩
        exact ⟨d, d.2, rfl⟩
    rw [hSe, Nat.card_range_of_injective hinj]
    exact card_Cq_le h
  have hEq : Set.range f = S := by
    apply Set.eq_of_subset_of_ncard_le hsub
    have hcardle : Nat.card S ≤ Nat.card (Set.range f) := by omega
    rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcardle
  have hmemS : c * t ∈ S := ⟨c, hc, rfl⟩
  rw [← hEq] at hmemS
  obtain ⟨w, hw⟩ := hmemS
  exact ⟨(w : H), w.2, hw⟩

theorem card_Cq (hb : ZJBound t) : Nat.card ↥(Q ⊓ centralizer ({t * τ} : Set H)) = 16 := by
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  change Nat.card ↥Cq = 16
  have hle : Nat.card ↥Cq ≤ 16 := card_Cq_le h
  have hge : 16 ≤ Nat.card ↥Cq := by
    let f : Mc → H := fun w => (w : H) * t * (w : H)⁻¹
    let S : Set H := {x | ∃ d ∈ Cq, x = d * t}
    have hfcard : (Set.range f).ncard = 16 := by
      rw [← Nat.card_coe_set_eq, card_range_conj_t h hMh hMc hb]
    have hsub : Set.range f ⊆ S := by
      rintro x ⟨w, rfl⟩
      exact ⟨(w : H) * t * (w : H)⁻¹ * t⁻¹,
        comm_t_mem_Cq h hMh (Mc_le_Mh h hMh hMc w.2), by simp only [f]; group⟩
    have hSle : S.ncard ≤ Nat.card ↥Cq := by
      let g : Cq → H := fun d => (d : H) * t
      have hinj : Function.Injective g := by
        intro a b hab
        exact Subtype.ext (mul_right_cancel hab)
      have hSe : S = Set.range g := by
        ext x
        constructor
        · rintro ⟨d, hd, rfl⟩
          exact ⟨⟨d, hd⟩, rfl⟩
        · rintro ⟨d, rfl⟩
          exact ⟨d, d.2, rfl⟩
      rw [hSe, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    calc 16 = (Set.range f).ncard := hfcard.symm
      _ ≤ S.ncard := Set.ncard_le_ncard hsub
      _ ≤ Nat.card ↥Cq := hSle
  omega

theorem Il_tQ (hb : ZJBound t) {q : H} (hq : q ∈ Q) (h2 : t * q * (t * q) = 1) :
    ∃ w ∈ Mc, t * q = w * t * w⁻¹ := by
  have h3 : t * q * t = q⁻¹ := by
    have h4 := congrArg (fun x => x * q⁻¹) h2
    simpa [mul_assoc] using h4
  have htq' : t * q = q⁻¹ * t := by
    have h5 := congrArg (fun x => x * t) h3
    simpa [mul_assoc, h.t_sq] using h5
  have hτ1 : τ * q⁻¹ * τ⁻¹ = q := by
    rw [h.tau_inv (q⁻¹) (Q.inv_mem hq), inv_inv]
  have hτ' : τ * q⁻¹ = q * τ := by
    calc τ * q⁻¹ = (τ * q⁻¹ * τ⁻¹) * τ := by group
      _ = q * τ := by rw [hτ1]
  have hqinv : q⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
    refine Subgroup.mem_inf.mpr ⟨Q.inv_mem hq, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q⁻¹ * (t * τ) = (q⁻¹ * t) * τ := by group
      _ = (t * q) * τ := by rw [htq'.symm]
      _ = t * (q * τ) := by group
      _ = t * (τ * q⁻¹) := by rw [hτ'.symm]
      _ = (t * τ) * q⁻¹ := by group
  obtain ⟨w, hw, hw_eq⟩ := exists_conj_t h hMh hMc hb hqinv
  refine ⟨w, hw, ?_⟩
  rw [hw_eq]
  exact htq'

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
