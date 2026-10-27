module

public import CFSG.GH74.GLS.SP.Local.SPLAltCoverB
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem diag_pow_dvd_le {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}
    (hX : XCtx X z t A T₁) (L : Subgroup X) {n : ℕ} (hn : 2 ^ n ∣ Nat.card ↥L) :
    2 ^ n ≤ 2 * Nat.card ↥T₁ ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 hn
  have hKp : IsPGroup 2 ↥K := IsPGroup.of_card hK
  have hP2 : IsPGroup 2 ↥(K.map L.subtype) :=
    hKp.of_equiv (Subgroup.equivMapOfInjective K L.subtype L.subtype_injective)
  have hPc : Nat.card ↥(K.map L.subtype) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hK]
  have := hX.bound _ hP2
  rwa [hPc] at this

section Structure

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ L : Subgroup X}

omit [Finite X] in
theorem diag_mem_conjSub_iff (hz : z * z = 1) {y : X} :
    y ∈ conjSub z⁻¹ L ↔ z * y * z ∈ L := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have key : ∀ x : X, z * (z * x * z) * z = x := fun x => by
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hz]; group
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : z * (MulAut.conj z⁻¹).toMonoidHom x * z = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz']
      exact key x
    rw [this]
    exact hx
  · intro h
    refine ⟨z * y * z, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz']
    exact key y

theorem diag_range_eq (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range) :
    (swapDiag hAB).range = A := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right ctx.z_sq
  have hLq : CFSG.Assembly.IsQuasisimple L := assembly_isQuasisimple_of_isComponent hL
  have hperf : ⁅(swapDiag hAB).range, (swapDiag hAB).range⁆ = (swapDiag hAB).range :=
    commutator_self_of_isQuasisimple (isQuasisimple_range_swapDiag hAB hLq)
  refine le_antisymm (ctx.perfect_le _ (fun c hc => ?_) hperf) hAD
  obtain ⟨x, rfl⟩ := hc
  exact mem_centralizer_iff.1 (swapDiag_mem_centralizer hAB hz' x) z rfl

theorem diag_center_le_ker (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range) {x : ↥L}
    (hx : x ∈ center ↥L) : swapDiag hAB x = 1 := by
  have hAcen : center ↥A = ⊥ := by
    obtain ⟨q, -, -, hAL2⟩ := ctx.A_L2
    exact altCover_center_eq_bot_of_isL2 hAL2
  have hmem : swapDiag hAB x ∈ A := (diag_range_eq ctx hL hAB hAD).le ⟨x, rfl⟩
  have hc : (⟨swapDiag hAB x, hmem⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : (g : X) ∈ (swapDiag hAB).range := hAD g.2
    apply Subtype.ext
    show (g : X) * swapDiag hAB x = swapDiag hAB x * g
    rw [← hy, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [hAcen, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem diag_ker_map (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range) :
    (swapDiag hAB).ker.map L.subtype = L ⊓ conjSub z⁻¹ L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_inf.2 ⟨y.2, (Subgroup.mem_inf.1 (mem_inf_of_mem_ker_swapDiag hAB hy)).2⟩
  · intro hx
    obtain ⟨hxL, hxL'⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    refine diag_center_le_ker ctx hL hAB hAD ?_
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_commutator_conj_eq_bot hAB g.2 hxL')

theorem diag_card_L (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range) :
    Nat.card ↥L = Nat.card ↥(L ⊓ conjSub z⁻¹ L) * Nat.card ↥A := by
  have h := Subgroup.card_ker_mul_card_range (swapDiag hAB)
  rw [diag_range_eq ctx hL hAB hAD] at h
  rw [← h, ← diag_ker_map ctx hL hAB hAD, Subgroup.card_map_of_injective L.subtype_injective]

theorem diag_card_M (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range) :
    Nat.card ↥(L ⊔ conjSub z⁻¹ L) = Nat.card ↥(L ⊓ conjSub z⁻¹ L) * Nat.card ↥A ^ 2 := by
  have hcomm : ∀ x ∈ L, ∀ y ∈ conjSub z⁻¹ L, x * y = y * x := fun x hx y hy =>
    commute_of_commutator_conj_eq_bot hAB hx hy
  have h1 := card_sup_mul_card_inf_of_commute hcomm
  rw [card_conjSub] at h1
  have h2 := diag_card_L ctx hL hAB hAD
  have hpos : 0 < Nat.card ↥(L ⊓ conjSub z⁻¹ L) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  nth_rewrite 1 [h2]
  nth_rewrite 1 [h2]
  ring

omit [Finite X] in
theorem diag_normalizes_L (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) {g : X} (hg : g ∈ L ⊔ conjSub z⁻¹ L)
    {x : X} (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  rw [← SetLike.mem_coe, coe_sup_conjSub hAB] at hg
  obtain ⟨l, hl, l', hl', rfl⟩ := hg
  have hc : x * l' = l' * x := commute_of_commutator_conj_eq_bot hAB hx hl'
  have h : l * l' * x * (l * l')⁻¹ = l * x * l⁻¹ := by
    calc l * l' * x * (l * l')⁻¹ = l * (l' * x) * l'⁻¹ * l⁻¹ := by group
      _ = l * (x * l') * l'⁻¹ * l⁻¹ := by rw [hc]
      _ = l * x * l⁻¹ := by group
  rw [h]
  exact mul_mem (mul_mem hl hx) (inv_mem hl)

omit [Finite X] in
theorem diag_false_of_stable (hz : z * z = 1) (hLz : conjSub z⁻¹ L ≠ L)
    (h : ∀ x ∈ L, z * x * z⁻¹ ∈ L) : False := by
  apply hLz
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have key : ∀ x : X, z * (z * x * z) * z = x := fun x => by
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hz]; group
  refine le_antisymm (fun y hy => ?_) (fun x hx => ?_)
  · have h1 := h _ ((diag_mem_conjSub_iff hz).1 hy)
    rw [hz', key] at h1
    exact h1
  · refine (diag_mem_conjSub_iff hz).2 ?_
    have h1 := h x hx
    rwa [hz'] at h1

theorem diag_z_not_mem (ctx : XCtx X z t A T₁) (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥)
    (hLz : conjSub z⁻¹ L ≠ L) : z ∉ L ⊔ conjSub z⁻¹ L := fun hzM =>
  diag_false_of_stable ctx.z_sq hLz fun _ hx => diag_normalizes_L hAB hzM hx

theorem diag_zt_not_mem (ctx : XCtx X z t A T₁) (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥)
    (hLz : conjSub z⁻¹ L ≠ L) : z * t ∉ L ⊔ conjSub z⁻¹ L := fun hzM =>
  diag_false_of_stable ctx.z_sq hLz fun x hx => by
    have h := diag_normalizes_L hAB hzM hx
    have e : z * t * x * (z * t)⁻¹ = z * x * z⁻¹ := by
      calc z * t * x * (z * t)⁻¹ = z * (t * x * t⁻¹) * z⁻¹ := by group
        _ = z * x * z⁻¹ := by rw [← ctx.t_central x]; group
    rwa [e] at h

omit [Finite X] in
theorem diag_z_mem_normalizer (hz : z * z = 1) :
    z ∈ normalizer ((L ⊔ conjSub z⁻¹ L : Subgroup X) : Set X) := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have key : ∀ x : X, z * (z * x * z) * z = x := fun x => by
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hz]; group
  have hone : ∀ h : X, h ∈ L ⊔ conjSub z⁻¹ L → z * h * z⁻¹ ∈ L ⊔ conjSub z⁻¹ L := by
    intro h hh
    have hle : L ⊔ conjSub z⁻¹ L ≤
        (L ⊔ conjSub z⁻¹ L).comap (MulAut.conj z).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · refine mem_sup_right ((diag_mem_conjSub_iff hz).2 ?_)
        have : z * (z * x * z⁻¹) * z = x := by rw [hz']; exact key x
        show z * (z * x * z⁻¹) * z ∈ L
        rw [this]
        exact hx
      · refine mem_sup_left ?_
        have h1 := (diag_mem_conjSub_iff hz).1 hy
        simpa [hz'] using h1
    exact hle hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hone h, fun hh => ?_⟩
  have h1 := hone _ hh
  have e : z * (z * h * z⁻¹) * z⁻¹ = h := by
    rw [hz']
    calc z * (z * h * z) * z = (z * z) * h * (z * z) := by group
      _ = h := by rw [hz]; group
  rwa [e] at h1

theorem diag_t_not_mem (ctx : XCtx X z t A T₁) (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥) (hAD : A ≤ (swapDiag hAB).range)
    (hodd : Odd (Nat.card ↥(L ⊓ conjSub z⁻¹ L))) (htM : t ∈ L ⊔ conjSub z⁻¹ L) : False := by
  rw [← SetLike.mem_coe, coe_sup_conjSub hAB] at htM
  obtain ⟨l, hl, l', hl', hlt⟩ := htM
  have hl_eq : l = t * l'⁻¹ := by rw [← hlt]; group
  have hlc : (⟨l, hl⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : X) * l = l * g
    have hc : (g : X) * l'⁻¹ = l'⁻¹ * g :=
      commute_of_commutator_conj_eq_bot hAB g.2 (inv_mem hl')
    calc (g : X) * l = g * (t * l'⁻¹) := by rw [← hl_eq]
      _ = (g * t) * l'⁻¹ := by group
      _ = (t * g) * l'⁻¹ := by rw [ctx.t_central g]
      _ = t * (g * l'⁻¹) := by group
      _ = t * (l'⁻¹ * g) := by rw [hc]
      _ = (t * l'⁻¹) * g := by group
      _ = l * g := by rw [← hl_eq]
  have hlI := mem_inf_of_mem_ker_swapDiag hAB
    (MonoidHom.mem_ker.2 (diag_center_le_ker ctx hL hAB hAD hlc))
  have htL' : t ∈ conjSub z⁻¹ L := by
    rw [← hlt]
    exact mul_mem (Subgroup.mem_inf.1 hlI).2 hl'
  have htL : t ∈ L := by
    have h1 := (diag_mem_conjSub_iff ctx.z_sq).1 htL'
    have e : z * t * z = t := by rw [ctx.t_central z, mul_assoc, ctx.z_sq, mul_one]
    rwa [e] at h1
  have htI : t ∈ L ⊓ conjSub z⁻¹ L := Subgroup.mem_inf.2 ⟨htL, htL'⟩
  have h1 : orderOf t ∣ Nat.card ↥(L ⊓ conjSub z⁻¹ L) := Subgroup.orderOf_dvd_natCard _ htI
  have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ctx.t_sq)
  have h3 : orderOf t = 1 := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h2 h1
  exact ctx.t_ne_one (orderOf_eq_one_iff.1 h3)

end Structure

end CFSG.GH74.GLS.SP.Local
