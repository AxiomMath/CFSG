module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1Centre

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped Pointwise commutatorElement

section Generic

variable {G : Type*} [Group G]

@[expose] def commutatorMemSubgroupD4 [Finite G] (x : G) (N : Subgroup G) : Subgroup G where
  carrier := {r | r ∈ normalizer (N : Set G) ∧ ⁅x, r⁆ ∈ N}
  mul_mem' := fun {r₁ r₂} h₁ h₂ => ⟨mul_mem h₁.1 h₂.1, by
    have e : ⁅x, r₁ * r₂⁆ = ⁅x, r₁⁆ * (r₁ * ⁅x, r₂⁆ * r₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h₁.2 ((mem_normalizer_iff.1 h₁.1 _).1 h₂.2)⟩
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := fun {r} hr => ⟨inv_mem hr.1, by
    have e : ⁅x, r⁻¹⁆ = r⁻¹ * ⁅x, r⁆⁻¹ * r⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hr.1) _).1 (inv_mem hr.2)⟩

theorem mem_map_upperCentralSeries_succ_iff_D4 {H T : Subgroup G} {n : ℕ}
    (hT : (Subgroup.upperCentralSeries H n).map H.subtype = T) {x : G} :
    x ∈ (Subgroup.upperCentralSeries H (n + 1)).map H.subtype ↔
      x ∈ H ∧ ∀ y ∈ H, ⁅x, y⁆ ∈ T := by
  rw [mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    rw [← hT]
    exact ⟨⁅z, ⟨y, hy⟩⁆, Subgroup.mem_upperCentralSeries_succ_iff.1 hz _, rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    have hy := h y y.2
    rw [← hT] at hy
    obtain ⟨w, hw, hw'⟩ := hy
    have hw'' : w = ⁅(⟨x, hx⟩ : H), y⁆ := Subtype.ext hw'
    rwa [← hw'']

theorem le_normalizer_map_upperCentralSeries_D4 [Finite G] (H : Subgroup G) (n : ℕ) :
    H ≤ normalizer (((Subgroup.upperCentralSeries H n).map H.subtype : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹,
    (inferInstance : (Subgroup.upperCentralSeries H n).Normal).conj_mem z hz _, rfl⟩

theorem mul_comm_of_isMulCommutative_D1 {A : Subgroup G} (hA : IsMulCommutative A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mul_comm_of_mem_sup_D1 [Finite G] {A B : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x y : G} (hx : x ∈ A ⊔ B) (hy : y ∈ A ⊔ B) :
    x * y = y * x := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).2
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((A ⊔ B : Subgroup G) : Set G) := hy
  rw [hset] at hx' hy'
  obtain ⟨a, ha, b, hb, e⟩ := hx'
  obtain ⟨a', ha', b', hb', e'⟩ := hy'
  have e1 : a * b = x := e
  have e2 : a' * b' = y := e'
  subst e1 e2
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [(hAB a' ha' b hb).symm]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hA a ha a' ha', hB b hb b' hb']
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
    _ = a' * b' * (a * b) := by group

theorem le_thompsonSubgroup_D1 {S A : Subgroup G} (hA : A ≤ S) (hc : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A) :
    A ≤ CFSG.Open.thompsonSubgroup S := by
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hc (le_iSup_of_le hmax le_rfl)))

theorem thompsonSubgroup_le_D1 {S D : Subgroup G}
    (h : ∀ A : Subgroup G, A ≤ S → IsMulCommutative A →
      (∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A) → A ≤ D) :
    CFSG.Open.thompsonSubgroup S ≤ D := by
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact iSup_le fun A => iSup_le fun hA => iSup_le fun hAc => iSup_le fun hAm => h A hA hAc hAm

end Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Generators

theorem commutator_mem_of_generators (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {N : Subgroup G}
    {x : G} (hN : yamadaR₂ d t ≤ normalizer (N : Set G))
    (hS : ∀ s ∈ d.S.map L.subtype, ⁅x, s⁆ ∈ N) (hY : ∀ y ∈ yamadaY₂ d t, ⁅x, y⁆ ∈ N)
    (ht : ⁅x, t⁆ ∈ N) : ∀ r ∈ yamadaR₂ d t, ⁅x, r⁆ ∈ N := by
  have hR := (h.yamada_5_9_1 d hlay).2.2.1
  have hle : yamadaR₂ d t ≤ commutatorMemSubgroupD4 x N := by
    conv_lhs => rw [hR]
    refine sup_le (sup_le (fun s hs => ⟨hN (le_sup_right (a := yamadaL₂ d t) hs), hS s hs⟩)
      (fun y hy => ⟨hN ((h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans le_sup_left hy), hY y hy⟩))
      ((zpowers_le).2 ⟨hN (le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)), ht⟩)
  exact fun r hr => (hle hr).2

theorem mul_self_eq_one_of_mem_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y : G}
    (hy : y ∈ yamadaY₂ d t) : y * y = 1 := by
  have hV := (h.yamada_5_6_2 d hlay).1.2
  have hy' : y ∈ ((yamadaY₂ d t : Subgroup G) : Set G) := hy
  rw [h.coe_yamadaY₂ d hlay] at hy'
  obtain ⟨w, hw, w', hw', e⟩ := hy'
  have e' : w * w' = y := e
  subst e'
  obtain ⟨z, hz, rfl⟩ := hw'
  have hww : w * w = 1 := by rw [← sq]; exact hV w hw
  have hzz : z * z = 1 := by rw [← sq]; exact hV z hz
  have hc := h.mul_comm_of_mem_yamadaY₂ d hlay (yamadaV₁_le_yamadaY₂ d hw)
    (yamadaV₁_conj_le_yamadaY₂ d ⟨z, hz, rfl⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc ⊢
  calc w * ((d.v : G) * z * ((d.v : L) : G)⁻¹) * (w * ((d.v : G) * z * ((d.v : L) : G)⁻¹)) =
      w * (((d.v : G) * z * ((d.v : L) : G)⁻¹) * w) * ((d.v : G) * z * ((d.v : L) : G)⁻¹) := by
        group
    _ = w * (w * ((d.v : G) * z * ((d.v : L) : G)⁻¹)) * ((d.v : G) * z * ((d.v : L) : G)⁻¹) := by
        rw [← hc]
    _ = (w * w) * ((d.v : G) * (z * z) * ((d.v : L) : G)⁻¹) := by group
    _ = 1 := by rw [hww, hzz]; group

theorem commutator_t_mem_V_of_mem_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {w : G}
    (hw : w ∈ yamadaV₁ d t) : ⁅w, t⁆ ∈ d.V.map L.subtype := by
  have h562 := h.yamada_5_6_2 d hlay
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h562.1.2 w hw)
  have htw : t * w * t ∈ yamadaV₁ d t := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁ d) w).1 hw
    rwa [htinv] at this
  have hc : w * (t * w * t) = t * w * t * w :=
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 htw).2 w (Subgroup.mem_inf.1 hw).1
  rw [commutatorElement_def, htinv, hww, ← h562.2.2.1]
  refine Subgroup.mem_inf.2 ⟨by simpa [mul_assoc] using mul_mem hw htw,
    mem_centralizer_singleton_iff.2 ?_⟩
  calc w * t * w * t * t = t * (t * w * t * w) := by
        rw [show t * (t * w * t * w) = (t * t) * w * t * w by group, h.t_mul_t, one_mul,
          mul_assoc (w * t * w), h.t_mul_t, mul_one]
    _ = t * (w * (t * w * t)) := by rw [hc]
    _ = t * (w * t * w * t) := by group

theorem commutator_t_mem_Y_of_mem_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y : G}
    (hy : y ∈ yamadaY₂ d t) : ⁅y, t⁆ ∈ d.Y.map L.subtype := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.mul_self_eq_one_of_mem_yamadaY₂ d hlay hy)
  have hty : t * y * t ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaY₂_D1 d) y).1 hy
    rwa [htinv] at this
  have hc : y * (t * y * t) = t * y * t * y := h.mul_comm_of_mem_yamadaY₂ d hlay hy hty
  rw [commutatorElement_def, htinv, hyy, ← h.yamadaY₂_inf_centralizer d hlay]
  refine Subgroup.mem_inf.2 ⟨by simpa [mul_assoc] using mul_mem hy hty,
    mem_centralizer_singleton_iff.2 ?_⟩
  calc y * t * y * t * t = t * (t * y * t * y) := by
        rw [show t * (t * y * t * y) = (t * t) * y * t * y by group, h.t_mul_t, one_mul,
          mul_assoc (y * t * y), h.t_mul_t, mul_one]
    _ = t * (y * (t * y * t)) := by rw [hc]
    _ = t * (y * t * y * t) := by group

theorem yamadaY₁_le_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₁ d t ≤ yamadaY₂ d t :=
  sup_le (h.Y_map_le_yamadaY₂ d hlay) (yamadaV₁_le_yamadaY₂ d)

theorem yamadaY₁_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₁ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype :=
  le_antisymm ((h.yamadaY₂_inf_centralizer d hlay) ▸
    inf_le_inf_right _ (h.yamadaY₁_le_yamadaY₂ d hlay))
    (le_inf le_sup_left ((map_subtype_le _).trans h.L_le_centralizer))

end Generators

section Series

theorem map_upperCentralSeries_one_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype := by
  have hR := (h.yamada_5_9_1 d hlay).2.2.1
  have hVV₁ := h.V_map_le_yamadaV₁ d hlay
  have hS₂ : yamadaS₂ d t ≤ yamadaR₂ d t := hR ▸ le_sup_left
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  refine map_upperCentralSeries_succ (map_upperCentralSeries_zero _) fun x => ?_
  simp only [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro hx
    refine ⟨hS₂ (((hVV₁.trans (yamadaV₁_le_yamadaY₂ d)).trans le_sup_right) hx), fun y hy => ?_⟩
    rw [hR, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hy
    have hxc : x ∈ centralizer (yamadaS₂ d t : Set G) :=
      (le_centralizer_iff.1 (h.yamadaS₂_le_centralizer_yamadaV₁ d hlay)) (hVV₁ hx)
    have hxt : x * t = t * x := mem_centralizer_iff.1 h.htL x (map_subtype_le _ hx)
    rcases hy with hy | hy
    · exact (mem_centralizer_iff.1 hxc y hy).symm
    · have hy' : y = t * (t * y) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      have h1 := mem_centralizer_iff.1 hxc _ hy
      rw [hy']
      calc x * (t * (t * y)) = t * (x * (t * y)) := by rw [← mul_assoc, hxt, mul_assoc]
        _ = t * (t * y * x) := by rw [h1]
        _ = t * (t * y) * x := by group
  · rintro ⟨hx, hc⟩
    rw [hR, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hx
    have hxV₁ : x ∈ centralizer (yamadaV₁ d t : Set G) := mem_centralizer_iff.2 fun w hw =>
      (hc w (hS₂ ((yamadaV₁_le_yamadaY₂ d).trans le_sup_right hw))).symm
    rcases hx with hx | hx
    · rw [← (h.yamada_5_6_2 d hlay).2.2.1]
      refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2
        (hc t (le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)))⟩
      rw [← h.yamadaS₂_inf_centralizer d hlay]
      exact Subgroup.mem_inf.2 ⟨hx, mem_centralizer_iff.2 fun y hy => (hc y (hS₂ hy)).symm⟩
    · exfalso
      apply h.t_not_mem_centralizer_yamadaV₁ d hlay
      have := mul_mem (h.yamadaS₂_le_centralizer_yamadaV₁ d hlay hx) (inv_mem hxV₁)
      rwa [mul_inv_cancel_right] at this

theorem commutator_mem_yamadaV₁_of_mem_yamadaS₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x y : G}
    (hx : x ∈ yamadaS₂ d t) (hy : y ∈ yamadaY₂ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  have hx' : x ∈ ((d.S.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ (h.S_map_le_normalizer_yamadaY₂ d hlay)] at hx'
  obtain ⟨s, hs, y₀, hy₀, e⟩ := hx'
  have e' : s * y₀ = x := e
  subst e'
  have hc := h.mul_comm_of_mem_yamadaY₂ d hlay hy₀ hy
  have e2 : s * y₀ * y * (s * y₀)⁻¹ * y⁻¹ = (y * s * y⁻¹ * s⁻¹)⁻¹ := by
    calc s * y₀ * y * (s * y₀)⁻¹ * y⁻¹ = s * (y₀ * y) * y₀⁻¹ * s⁻¹ * y⁻¹ := by group
      _ = s * (y * y₀) * y₀⁻¹ * s⁻¹ * y⁻¹ := by rw [hc]
      _ = (y * s * y⁻¹ * s⁻¹)⁻¹ := by group
  rw [e2]
  exact inv_mem (h.commutator_mem_yamadaV₁_of_mem_yamadaY₂ d hlay hy hs)

theorem map_upperCentralSeries_two_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype =
      yamadaY₁ d t := by
  have h1 := h.map_upperCentralSeries_one_yamadaR₂ d hlay
  have hN : yamadaR₂ d t ≤ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    h1 ▸ le_normalizer_map_upperCentralSeries_D4 _ 1
  have hR := (h.yamada_5_9_1 d hlay).2.2.1
  have hS₂ : yamadaS₂ d t ≤ yamadaR₂ d t := hR ▸ le_sup_left
  have hSR : d.S.map L.subtype ≤ yamadaR₂ d t := le_sup_right
  have hYR : yamadaY₂ d t ≤ yamadaR₂ d t := (h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans le_sup_left
  have htR : t ∈ yamadaR₂ d t := le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have hVV₁ := h.V_map_le_yamadaV₁ d hlay
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have key := fun x => mem_map_upperCentralSeries_succ_iff_D4 (x := x) h1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxc⟩ := (key x).1 hx
    rw [hR, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hxR
    rcases hxR with hxS | hxS
    ·
      have hxY : x ∈ yamadaY₂ d t := (h.mem_yamadaY₂_iff d hlay).2
        ⟨hxS, fun y hy => hVV₁ (hxc y (hS₂ hy))⟩
      have hx' : x ∈ ((yamadaY₂ d t : Subgroup G) : Set G) := hxY
      rw [h.coe_yamadaY₂ d hlay] at hx'
      obtain ⟨w, hw, w', hw', e⟩ := hx'
      have e' : w * w' = x := e
      subst e'
      have hwt := h.commutator_t_mem_V_of_mem_yamadaV₁ d hlay hw
      have htw' : t * w' * t ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
        have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w').1 hw'
        rwa [htinv] at this
      have hcw : w * (w' * t * w'⁻¹ * t⁻¹) = (w' * t * w'⁻¹ * t⁻¹) * w := by
        refine h.mul_comm_of_mem_yamadaY₂ d hlay (yamadaV₁_le_yamadaY₂ d hw)
          (yamadaV₁_conj_le_yamadaY₂ d ?_)
        rw [htinv]
        have e3 : w' * t * w'⁻¹ * t = w' * (t * w'⁻¹ * t) := by group
        rw [e3]
        refine mul_mem hw' ?_
        have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w'⁻¹).1 (inv_mem hw')
        rwa [htinv] at this
      have h2 : w' * t * w'⁻¹ * t⁻¹ ∈ d.V.map L.subtype := by
        have e4 : w' * t * w'⁻¹ * t⁻¹ =
            (w * w' * t * (w * w')⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹)⁻¹ := by
          calc w' * t * w'⁻¹ * t⁻¹ = w * (w' * t * w'⁻¹ * t⁻¹) * w⁻¹ := by
                rw [hcw, mul_inv_cancel_right]
            _ = (w * w' * t * (w * w')⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹)⁻¹ := by group
        rw [e4]
        have hxt := hxc t htR
        rw [commutatorElement_def] at hxt hwt
        exact mul_mem hxt (inv_mem hwt)
      have h3 : w' * t * w'⁻¹ * t⁻¹ = 1 := by
        refine mem_bot.1 ((h.yamadaV₁_inf_conj_v d hlay).le (Subgroup.mem_inf.2 ⟨hVV₁ h2, ?_⟩))
        rw [htinv]
        have e3 : w' * t * w'⁻¹ * t = w' * (t * w'⁻¹ * t) := by group
        rw [e3]
        refine mul_mem hw' ?_
        have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w'⁻¹).1 (inv_mem hw')
        rwa [htinv] at this
      have hw't : t * w' = w' * t := by
        have := h3
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have hw'Y : w' ∈ d.Y.map L.subtype := by
        have := h.mem_U₅_of_mem_yamadaV₁_conj d hlay hw' hw't
        exact map_mono d.U₅_le_Y this
      exact mul_mem (mem_sup_right hw) (mem_sup_left hw'Y)
    ·
      exfalso
      apply h.t_not_mem_centralizer_yamadaV₁ d hlay
      have hxS' : t⁻¹ * x ∈ yamadaS₂ d t := by rw [htinv]; exact hxS
      have htV : ∀ w' ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom,
          t * w' = w' * t := by
        intro w' hw'
        have hw'Y := yamadaV₁_conj_le_yamadaY₂ d hw'
        have h1' := hxc w' (hYR hw'Y)
        rw [commutatorElement_def] at h1'
        have h2' := h.commutator_mem_yamadaV₁_of_mem_yamadaS₂ d hlay hxS' hw'Y
        have e5 : t * w' * t⁻¹ * w'⁻¹ = (t * (t⁻¹ * x * w' * (t⁻¹ * x)⁻¹ * w'⁻¹) * t⁻¹)⁻¹ *
            (x * w' * x⁻¹ * w'⁻¹) := by group
        have hc2 : t * w' * t⁻¹ * w'⁻¹ ∈ yamadaV₁ d t := by
          rw [e5]
          exact mul_mem (inv_mem ((mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁ d) _).1 h2'))
            (hVV₁ h1')
        have hc1 : t * w' * t⁻¹ * w'⁻¹ ∈
            (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :=
          mul_mem ((mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w').1 hw')
            (inv_mem hw')
        have h4 : t * w' * t⁻¹ * w'⁻¹ = 1 :=
          mem_bot.1 ((h.yamadaV₁_inf_conj_v d hlay).le (Subgroup.mem_inf.2 ⟨hc2, hc1⟩))
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
        exact h4
      have hvt := h.v_mul_t d
      rw [mem_centralizer_iff]
      intro w hw
      have h5 := htV _ (⟨w, hw, rfl⟩ : ((d.v : L) : G) * w * ((d.v : L) : G)⁻¹ ∈
        (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom)
      have e6 : ((d.v : L) : G) * (w * t) * ((d.v : L) : G)⁻¹ =
          ((d.v : L) : G) * (t * w) * ((d.v : L) : G)⁻¹ := by
        calc ((d.v : L) : G) * (w * t) * ((d.v : L) : G)⁻¹ =
            (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) * (((d.v : L) : G) * t *
              ((d.v : L) : G)⁻¹) := by group
          _ = (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) * t := by rw [hvt, mul_inv_cancel_right]
          _ = t * (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) := h5.symm
          _ = (((d.v : L) : G) * t * ((d.v : L) : G)⁻¹) *
              (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) := by rw [hvt, mul_inv_cancel_right]
          _ = ((d.v : L) : G) * (t * w) * ((d.v : L) : G)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e6)
  · refine sup_le (fun a ha => (key a).2 ⟨hSR (map_mono (d.Y_le_W.trans (d.W_le_F.trans
      (d.F_le_D.trans d.D_le_S))) ha), h.commutator_mem_of_generators d hlay hN ?_ ?_ ?_⟩)
      (fun w hw => (key w).2 ⟨hS₂ ((yamadaV₁_le_yamadaY₂ d).trans le_sup_right hw),
        h.commutator_mem_of_generators d hlay hN ?_ ?_ ?_⟩)
    · rintro _ ⟨s', hs', rfl⟩
      obtain ⟨a', ha', rfl⟩ := ha
      have := (d.mem_Y_iff_forall.1 ha').2 s' hs'
      have hm : L.subtype ⁅a', s'⁆ ∈ d.V.map L.subtype := ⟨_, this, rfl⟩
      rwa [map_commutatorElement] at hm
    · intro y hy
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (h.mul_comm_of_mem_yamadaY₂ d hlay (h.Y_map_le_yamadaY₂ d hlay ha) hy)]
      exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 h.htL a
        (map_subtype_le _ ha))]
      exact one_mem _
    · intro s hs
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 (h.S_map_le_centralizer_yamadaV₁ d hlay hs) w hw)]
      exact one_mem _
    · intro y hy
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (h.mul_comm_of_mem_yamadaY₂ d hlay (yamadaV₁_le_yamadaY₂ d hw) hy)]
      exact one_mem _
    · exact h.commutator_t_mem_V_of_mem_yamadaV₁ d hlay hw

theorem mem_W_map_of_mem_yamadaW₂_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {z : G}
    (hz : z ∈ yamadaW₂ d t ⊔ zpowers t) (hzL : z ∈ L) : z ∈ d.W.map L.subtype := by
  have hWM : d.W.map L.subtype ≤ d.M.map L.subtype := map_mono (d.W_le_F.trans d.F_le_M)
  have hYW : yamadaY₂ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (mem_centralizer_iff.1 (h.M_map_le_centralizer_yamadaY₂ d hlay (hWM ha)) y hy).symm)
  have hset : ((yamadaW₂ d t : Subgroup G) : Set G) =
      ((d.W.map L.subtype : Subgroup G) : Set G) * (yamadaY₂ d t : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hYW
  have htW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.W) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have hYC : ∀ y ∈ yamadaY₂ d t, t * y = y * t → y ∈ d.Y.map L.subtype := fun y hy hyt => by
    rw [← h.yamadaY₂_inf_centralizer d hlay]
    exact Subgroup.mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hyt.symm⟩
  have hLC : ∀ l ∈ L, t * l = l * t := fun l hl => (mem_centralizer_iff.1 h.htL l hl).symm
  have hYW' : d.Y.map L.subtype ≤ d.W.map L.subtype := map_mono d.Y_le_W
  rw [h.mem_sup_zpowers_iff_of_normalizer htW₂] at hz
  rcases hz with hz | hz
  · have hz' : z ∈ ((yamadaW₂ d t : Subgroup G) : Set G) := hz
    rw [hset] at hz'
    obtain ⟨a, ha, y, hy, e⟩ := hz'
    have e' : a * y = z := e
    have hyL : y ∈ L := by
      have : y = a⁻¹ * z := by rw [← e', inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem (map_subtype_le _ ha)) hzL
    rw [← e']
    exact mul_mem ha (hYW' (hYC y hy (hLC y hyL)))
  · exfalso
    have hz' : t * z ∈ ((yamadaW₂ d t : Subgroup G) : Set G) := hz
    rw [hset] at hz'
    obtain ⟨a, ha, y, hy, e⟩ := hz'
    have e' : a * y = t * z := e
    have haL : a ∈ L := map_subtype_le _ ha
    have hyt : t * y = y * t := by
      have ey : y = a⁻¹ * (t * z) := by rw [← e', inv_mul_cancel_left]
      have h1 := hLC _ (inv_mem haL)
      have h2 := hLC z hzL
      rw [ey]
      calc t * (a⁻¹ * (t * z)) = a⁻¹ * (t * (t * z)) := by rw [← mul_assoc, h1, mul_assoc]
        _ = a⁻¹ * (t * (z * t)) := by rw [h2]
        _ = a⁻¹ * (t * z) * t := by group
    have hyL : y ∈ L := map_subtype_le _ (hYC y hy hyt)
    apply h.t_not_mem_L
    have : t = a * y * z⁻¹ := by rw [e', mul_inv_cancel_right]
    rw [this]
    exact mul_mem (mul_mem haL hyL) (inv_mem hzL)

theorem map_upperCentralSeries_three_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t := by
  have h2 := h.map_upperCentralSeries_two_yamadaR₂ d hlay
  have hN : yamadaR₂ d t ≤ normalizer ((yamadaY₁ d t : Subgroup G) : Set G) :=
    h2 ▸ le_normalizer_map_upperCentralSeries_D4 _ 2
  have key := fun x => mem_map_upperCentralSeries_succ_iff_D4 (x := x) h2
  have hR := (h.yamada_5_9_1 d hlay).2.2.1
  have hSR : d.S.map L.subtype ≤ yamadaR₂ d t := le_sup_right
  have hYR : yamadaY₂ d t ≤ yamadaR₂ d t := (h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans le_sup_left
  have htR : t ∈ yamadaR₂ d t := le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  have hYY₁ : d.Y.map L.subtype ≤ yamadaY₁ d t := le_sup_left
  have hV₁Y₁ : yamadaV₁ d t ≤ yamadaY₁ d t := le_sup_right
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 h.htL l hl
  have ht3 : t ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype :=
    (key t).2 ⟨htR, h.commutator_mem_of_generators d hlay hN
      (fun s hs => by
        rw [commutatorElement_eq_one_iff_mul_comm.2 (hLt s (map_subtype_le _ hs)).symm]
        exact one_mem _)
      (fun y hy => by
        rw [← commutatorElement_inv]
        exact inv_mem (hYY₁ (h.commutator_t_mem_Y_of_mem_yamadaY₂ d hlay hy)))
      (by rw [commutatorElement_self]; exact one_mem _)⟩
  have hY3 : ∀ y ∈ yamadaY₂ d t,
      y ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype :=
    fun y hy => (key y).2 ⟨hYR hy, h.commutator_mem_of_generators d hlay hN
      (fun s hs => hV₁Y₁ (by
        rw [commutatorElement_def]
        exact h.commutator_mem_yamadaV₁_of_mem_yamadaY₂ d hlay hy hs))
      (fun y' hy' => by
        rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_comm_of_mem_yamadaY₂ d hlay hy hy')]
        exact one_mem _)
      (hYY₁ (h.commutator_t_mem_Y_of_mem_yamadaY₂ d hlay hy))⟩
  have hW3 : ∀ a ∈ d.W.map L.subtype,
      a ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype :=
    fun a ha => (key a).2 ⟨hSR (map_mono (d.W_le_F.trans (d.F_le_D.trans d.D_le_S)) ha),
      h.commutator_mem_of_generators d hlay hN
        (by
          rintro _ ⟨s', hs', rfl⟩
          obtain ⟨a', ha', rfl⟩ := ha
          have hm : L.subtype ⁅a', s'⁆ ∈ d.Y.map L.subtype :=
            ⟨_, (d.mem_W_iff_forall.1 ha').2 s' hs', rfl⟩
          rw [map_commutatorElement] at hm
          exact hYY₁ hm)
        (fun y hy => by
          rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1
            (hMY (map_mono (d.W_le_F.trans d.F_le_M) ha)) y hy).symm]
          exact one_mem _)
        (by
          rw [commutatorElement_eq_one_iff_mul_comm.2 (hLt a (map_subtype_le _ ha))]
          exact one_mem _)⟩
  refine le_antisymm (fun x hx => ?_) (sup_le (sup_le hW3 hY3) ((zpowers_le).2 ht3))
  have hgen : ∀ x' ∈ yamadaS₂ d t,
      x' ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype →
        x' ∈ yamadaW₂ d t := by
    intro x' hx'S hx'3
    have hx'' : x' ∈ ((d.S.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hx'S
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S_map_le_normalizer_yamadaY₂ d hlay)]
      at hx''
    obtain ⟨s, hs, y, hy, e⟩ := hx''
    have e' : s * y = x' := e
    subst e'
    have hs3 : s ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype := by
      have := mul_mem hx'3 (inv_mem (hY3 y hy))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨-, hsc⟩ := (key s).1 hs3
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have hs₀W : s₀ ∈ d.W := by
      refine d.mem_W_iff_forall.2 ⟨hs₀, fun s' hs' => ?_⟩
      have h1 := hsc (L.subtype s') (hSR ⟨s', hs', rfl⟩)
      rw [← map_commutatorElement] at h1
      have h3 : L.subtype ⁅s₀, s'⁆ ∈ d.Y.map L.subtype := by
        rw [← h.yamadaY₁_inf_centralizer d hlay]
        exact Subgroup.mem_inf.2 ⟨h1, h.L_le_centralizer (⁅s₀, s'⁆ : L).2⟩
      obtain ⟨v, hv, hv'⟩ := h3
      rw [← L.subtype_injective hv']
      exact hv
    exact mul_mem (le_sup_left (a := d.W.map L.subtype) ⟨s₀, hs₀W, rfl⟩)
      (le_sup_right (a := d.W.map L.subtype) hy)
  obtain ⟨hxR, -⟩ := (key x).1 hx
  rw [hR, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hxR
  rcases hxR with hxS | hxS
  · exact mem_sup_left (hgen x hxS hx)
  · have h1 := hgen _ hxS (mul_mem ht3 hx)
    have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem map_upperCentralSeries_four_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t := by
  have h3 := h.map_upperCentralSeries_three_yamadaR₂ d hlay
  have h2 := h.map_upperCentralSeries_two_yamadaR₂ d hlay
  have hN : yamadaR₂ d t ≤ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h3 ▸ le_normalizer_map_upperCentralSeries_D4 _ 3
  have key3 := fun x => mem_map_upperCentralSeries_succ_iff_D4 (x := x) h2
  have key := fun x => mem_map_upperCentralSeries_succ_iff_D4 (x := x) h3
  have hR := (h.yamada_5_9_1 d hlay).2.2.1
  have hSR : d.S.map L.subtype ≤ yamadaR₂ d t := le_sup_right
  have hYR : yamadaY₂ d t ≤ yamadaR₂ d t := (h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans le_sup_left
  have htR : t ∈ yamadaR₂ d t := le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  have hY₁W : yamadaY₁ d t ≤ yamadaW₂ d t ⊔ zpowers t :=
    (sup_le_sup (map_mono d.Y_le_W) (yamadaV₁_le_yamadaY₂ d)).trans le_sup_left
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 h.htL l hl
  have h3' : ∀ x ∈ yamadaW₂ d t ⊔ zpowers t,
      x ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype := by
    intro x hx
    rw [← h3] at hx
    obtain ⟨hxR, hxc⟩ := (key3 x).1 hx
    exact (key x).2 ⟨hxR, fun y hy => hY₁W (hxc y hy)⟩
  have ht4 := h3' t (mem_sup_right (mem_zpowers t))
  have hY4 := fun y (hy : y ∈ yamadaY₂ d t) => h3' y (mem_sup_left (mem_sup_right hy))
  have hF4 : ∀ a ∈ d.F.map L.subtype,
      a ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype :=
    fun a ha => (key a).2 ⟨hSR (map_mono (d.F_le_D.trans d.D_le_S) ha),
      h.commutator_mem_of_generators d hlay hN
        (by
          rintro _ ⟨s', hs', rfl⟩
          obtain ⟨a', ha', rfl⟩ := ha
          have hm : L.subtype ⁅a', s'⁆ ∈ d.W.map L.subtype :=
            ⟨_, (d.mem_F_iff_forall.1 ha').2 s' hs', rfl⟩
          rw [map_commutatorElement] at hm
          exact mem_sup_left (mem_sup_left hm))
        (fun y hy => by
          rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1
            (hMY (map_mono d.F_le_M ha)) y hy).symm]
          exact one_mem _)
        (by
          rw [commutatorElement_eq_one_iff_mul_comm.2 (hLt a (map_subtype_le _ ha))]
          exact one_mem _)⟩
  refine le_antisymm (fun x hx => ?_) (sup_le (sup_le hF4 hY4) ((zpowers_le).2 ht4))
  have hgen : ∀ x' ∈ yamadaS₂ d t,
      x' ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype →
        x' ∈ yamadaF₂ d t := by
    intro x' hx'S hx'4
    have hx'' : x' ∈ ((d.S.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hx'S
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S_map_le_normalizer_yamadaY₂ d hlay)]
      at hx''
    obtain ⟨s, hs, y, hy, e⟩ := hx''
    have e' : s * y = x' := e
    subst e'
    have hs4 : s ∈ (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype := by
      have := mul_mem hx'4 (inv_mem (hY4 y hy))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨-, hsc⟩ := (key s).1 hs4
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have hs₀F : s₀ ∈ d.F := by
      refine d.mem_F_iff_forall.2 ⟨hs₀, fun s' hs' => ?_⟩
      have h1 := hsc (L.subtype s') (hSR ⟨s', hs', rfl⟩)
      rw [← map_commutatorElement] at h1
      obtain ⟨v, hv, hv'⟩ := h.mem_W_map_of_mem_yamadaW₂_sup d hlay h1 (⁅s₀, s'⁆ : L).2
      rw [← L.subtype_injective hv']
      exact hv
    exact mul_mem (le_sup_left (a := d.F.map L.subtype) ⟨s₀, hs₀F, rfl⟩)
      (le_sup_right (a := d.F.map L.subtype) hy)
  obtain ⟨hxR, -⟩ := (key x).1 hx
  rw [hR, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hxR
  rcases hxR with hxS | hxS
  · exact mem_sup_left (hgen x hxS hx)
  · have h1 := hgen _ hxS (mul_mem ht4 hx)
    have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem yamada_5_10_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
        d.V.map L.subtype ∧
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype =
        yamadaY₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
        yamadaW₂ d t ⊔ zpowers t ∧
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
        yamadaF₂ d t ⊔ zpowers t :=
  ⟨h.map_upperCentralSeries_one_yamadaR₂ d hlay, h.map_upperCentralSeries_two_yamadaR₂ d hlay,
    h.map_upperCentralSeries_three_yamadaR₂ d hlay,
    h.map_upperCentralSeries_four_yamadaR₂ d hlay⟩

end Series

section Thompson

theorem yamadaF₂_le_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₂ d t ≤ centralizer (yamadaV₁ d t : Set G) :=
  sup_le ((map_mono (d.F_le_D.trans d.D_le_S)).trans (h.S_map_le_centralizer_yamadaV₁ d hlay))
    (h.yamadaY₂_le_centralizer_yamadaV₁ d hlay)

theorem t_not_mem_yamadaF₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ yamadaF₂ d t :=
  fun ht => h.t_not_mem_centralizer_yamadaV₁ d hlay
    (h.yamadaF₂_le_centralizer_yamadaV₁ d hlay ht)

theorem t_mem_normalizer_yamadaF₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaF₂ d t : Set G) :=
  mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.F) (h.t_mem_normalizer_yamadaY₂_D1 d)

theorem yamadaF₂_le_centralizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₂ d t ≤ centralizer (yamadaY₂ d t : Set G) :=
  sup_le ((map_mono d.F_le_M).trans (h.M_map_le_centralizer_yamadaY₂ d hlay))
    (fun _ hy => mem_centralizer_iff.2 fun _ hz => h.mul_comm_of_mem_yamadaY₂ d hlay hz hy)

theorem card_sup_yamadaY₂_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {A : Subgroup G}
    (hAF : A ≤ yamadaF₂ d t) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card (A ⊔ yamadaY₂ d t : Subgroup G) ≤ (2 ^ f) ^ 7 := by
  have hYc := h.yamadaF₂_le_centralizer_yamadaY₂ d hlay
  have hAY : ∀ x ∈ A, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (hYc (hAF hx)) y hy).symm
  have hKcomm : ∀ x ∈ A ⊔ yamadaY₂ d t, ∀ y ∈ A ⊔ yamadaY₂ d t, x * y = y * x :=
    fun x hx y hy => mul_comm_of_mem_sup_D1 hA
      (fun a ha b hb => h.mul_comm_of_mem_yamadaY₂ d hlay ha hb) hAY hx hy
  have hKF : A ⊔ yamadaY₂ d t ≤ yamadaF₂ d t := sup_le hAF le_sup_right
  have hYN : yamadaY₂ d t ≤ normalizer ((d.F.map L.subtype : Subgroup G) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (mem_centralizer_iff.1 (hYc (le_sup_left (a := d.F.map L.subtype) ha)) y hy).symm)
  have hKeq : A ⊔ yamadaY₂ d t ≤ ((A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype) ⊔ yamadaY₂ d t := by
    intro k hk
    have hk' : k ∈ ((d.F.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hKF hk
    rw [coe_mul_of_right_le_normalizer_left _ _ hYN] at hk'
    obtain ⟨a, ha, y, hy, e⟩ := hk'
    have e' : a * y = k := e
    have haK : a ∈ A ⊔ yamadaY₂ d t := by
      have ea : a = k * y⁻¹ := by rw [← e', mul_inv_cancel_right]
      rw [ea]
      exact mul_mem hk (inv_mem (le_sup_right (a := A) hy))
    rw [← e']
    exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨haK, ha⟩)) (mem_sup_right hy)
  have hKF5 : Nat.card ((A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype : Subgroup G) ≤ (2 ^ f) ^ 5 := by
    have hmap : (((A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype).comap L.subtype).map L.subtype =
        (A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype :=
      Subgroup.map_comap_eq_self (by
        rw [range_subtype]
        exact inf_le_right.trans (map_subtype_le _))
    rw [← hmap, card_map_of_injective L.subtype_injective]
    refine d.yamada_3_11_1 (fun b hb => ?_) (fun b hb b' hb' => Subtype.ext ?_)
    · obtain ⟨b', hb'F, e⟩ := (Subgroup.mem_inf.1 hb).2
      rw [← L.subtype_injective e]
      exact d.F_le_D hb'F
    · exact hKcomm _ (Subgroup.mem_inf.1 hb).1 _ (Subgroup.mem_inf.1 hb').1
  have hcomm : ∀ x ∈ (A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype, ∀ y ∈ yamadaY₂ d t,
      x * y = y * x := fun x hx y hy => (mem_centralizer_iff.1 (hYc (hKF (Subgroup.mem_inf.1 hx).1))
        y hy).symm
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  have hinf : (A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype ⊓ yamadaY₂ d t = d.Y.map L.subtype := by
    refine le_antisymm ?_ (le_inf (le_inf ((h.Y_map_le_yamadaY₂ d hlay).trans le_sup_right)
      (map_mono (d.Y_le_W.trans d.W_le_F))) (h.Y_map_le_yamadaY₂ d hlay))
    rw [← h.map_inf_yamadaY₂ d hlay (d.Y_le_W.trans d.W_le_F)]
    exact inf_le_inf_right _ inf_le_right
  rw [hinf, card_map_of_injective L.subtype_injective, d.card_Y, h.card_yamadaY₂ d hlay] at h1
  have h2 := card_le_of_le hKeq
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  have h3 : Nat.card (((A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype) ⊔ yamadaY₂ d t : Subgroup G) *
      (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 7 * (2 ^ f) ^ 2 := by
    rw [h1]
    calc Nat.card ((A ⊔ yamadaY₂ d t) ⊓ d.F.map L.subtype : Subgroup G) * (2 ^ f) ^ 4 ≤
        (2 ^ f) ^ 5 * (2 ^ f) ^ 4 := Nat.mul_le_mul_right _ hKF5
      _ = (2 ^ f) ^ 7 * (2 ^ f) ^ 2 := by ring
  exact h2.trans (Nat.le_of_mul_le_mul_right h3 hpos)

theorem yamadaF₂_sup_zpowers_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (yamadaF₂ d t ⊔ zpowers t) ⊓
        centralizer ((yamadaF₂ d t ⊔ zpowers t : Subgroup G) : Set G) = d.Y.map L.subtype := by
  have htF := h.t_mem_normalizer_yamadaF₂ d
  have hV₁F : yamadaV₁ d t ≤ yamadaF₂ d t := (yamadaV₁_le_yamadaY₂ d).trans le_sup_right
  have hYF : d.Y.map L.subtype ≤ d.F.map L.subtype := map_mono (d.Y_le_W.trans d.W_le_F)
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 h.htL l hl
  apply le_antisymm
  · intro z hz
    obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.1 hz
    rw [h.mem_sup_zpowers_iff_of_normalizer htF] at hzQ
    have hzV : z ∈ centralizer (yamadaV₁ d t : Set G) := mem_centralizer_iff.2 fun w hw =>
      mem_centralizer_iff.1 hzc w (mem_sup_left (hV₁F hw))
    rcases hzQ with hzF | hzF
    · have hzt : t * z = z * t := mem_centralizer_iff.1 hzc t (mem_sup_right (mem_zpowers t))
      have hzFm : z ∈ d.F.map L.subtype := by
        have hz' : z ∈ ((d.F.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hzF
        have hYN : yamadaY₂ d t ≤ normalizer ((d.F.map L.subtype : Subgroup G) : Set G) :=
          fun y hy => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
            (mem_centralizer_iff.1 (h.yamadaF₂_le_centralizer_yamadaY₂ d hlay
              (le_sup_left (a := d.F.map L.subtype) ha)) y hy).symm)
        rw [coe_mul_of_right_le_normalizer_left _ _ hYN] at hz'
        obtain ⟨a, ha, y, hy, e⟩ := hz'
        have e' : a * y = z := e
        have haL : a ∈ L := map_subtype_le _ ha
        have hyt : t * y = y * t := by
          have ey : y = a⁻¹ * z := by rw [← e', inv_mul_cancel_left]
          have h1 := (hLt _ (inv_mem haL)).symm
          rw [ey]
          calc t * (a⁻¹ * z) = a⁻¹ * (t * z) := by rw [← mul_assoc, h1, mul_assoc]
            _ = a⁻¹ * (z * t) := by rw [hzt]
            _ = a⁻¹ * z * t := by group
        have hyY : y ∈ d.Y.map L.subtype := by
          rw [← h.yamadaY₂_inf_centralizer d hlay]
          exact Subgroup.mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hyt.symm⟩
        rw [← e']
        exact mul_mem ha (hYF hyY)
      rw [← map_inf_centralizer_map d.F_inf_centralizer_F]
      exact Subgroup.mem_inf.2 ⟨hzFm, mem_centralizer_iff.2 fun x hx =>
        mem_centralizer_iff.1 hzc x (mem_sup_left (le_sup_left (a := d.F.map L.subtype) hx))⟩
    · exfalso
      apply h.t_not_mem_centralizer_yamadaV₁ d hlay
      have := mul_mem (h.yamadaF₂_le_centralizer_yamadaV₁ d hlay hzF) (inv_mem hzV)
      rwa [mul_inv_cancel_right] at this
  · refine le_inf (hYF.trans (le_sup_left.trans le_sup_left)) (le_centralizer_iff.1 ?_)
    refine sup_le (sup_le ?_ ?_) ((zpowers_le).2 (mem_centralizer_iff.2 fun y hy =>
      hLt y (map_subtype_le _ hy)))
    · rintro _ ⟨a, ha, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ d.F ⊓ centralizer (d.F : Set L) := d.F_inf_centralizer_F ▸ hy
      exact (congrArg Subtype.val (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy').2 a ha)).symm
    · exact fun y hy => mem_centralizer_iff.2 fun z hz =>
        h.mul_comm_of_mem_yamadaY₂ d hlay (h.Y_map_le_yamadaY₂ d hlay hz) hy

theorem card_le_of_not_le_yamadaF₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {B : Subgroup G}
    (hBQ : B ≤ yamadaF₂ d t ⊔ zpowers t) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBF : ¬ B ≤ yamadaF₂ d t) : Nat.card B ≤ 2 * (2 ^ f) ^ 5 := by
  have htF := h.t_mem_normalizer_yamadaF₂ d
  have hYc := h.yamadaF₂_le_centralizer_yamadaY₂ d hlay
  have hcardQ := h.card_sup_zpowers_of_not_mem htF (h.t_not_mem_yamadaF₂ d hlay)
  have h3 : Nat.card B ≤ 2 * Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) := by
    have h1 := ncard_mul_mul_card_inf B (yamadaF₂ d t)
    have h2 : ((B : Set G) * (yamadaF₂ d t : Set G)).ncard ≤
        Nat.card (yamadaF₂ d t ⊔ zpowers t : Subgroup G) := by
      calc ((B : Set G) * (yamadaF₂ d t : Set G)).ncard ≤
          ((yamadaF₂ d t ⊔ zpowers t : Subgroup G) : Set G).ncard := by
            refine Set.ncard_le_ncard ?_ (Set.toFinite _)
            rintro _ ⟨x, hx, y, hy, rfl⟩
            exact mul_mem (hBQ hx) (mem_sup_left hy)
        _ = Nat.card (yamadaF₂ d t ⊔ zpowers t : Subgroup G) := (Nat.card_coe_set_eq _).symm
    have h4 : Nat.card B * Nat.card (yamadaF₂ d t) ≤
        2 * Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) * Nat.card (yamadaF₂ d t) := by
      calc Nat.card B * Nat.card (yamadaF₂ d t) = ((B : Set G) * (yamadaF₂ d t : Set G)).ncard *
            Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) := h1.symm
        _ ≤ Nat.card (yamadaF₂ d t ⊔ zpowers t : Subgroup G) *
            Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) := Nat.mul_le_mul_right _ h2
        _ = 2 * Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) * Nat.card (yamadaF₂ d t) := by
            rw [hcardQ]; ring
    exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  have hQ : yamadaF₂ d t ⊔ zpowers t ≤ B ⊔ yamadaF₂ d t := by
    obtain ⟨b, hb, hbF⟩ := Set.not_subset.1 hBF
    have htb : t * b ∈ yamadaF₂ d t := by
      have := hBQ hb
      rw [h.mem_sup_zpowers_iff_of_normalizer htF] at this
      exact this.resolve_left hbF
    refine sup_le le_sup_right ((zpowers_le).2 ?_)
    have hmem : (t * b) * b⁻¹ ∈ B ⊔ yamadaF₂ d t :=
      mul_mem (mem_sup_right htb) (mem_sup_left (inv_mem hb))
    rwa [mul_inv_cancel_right] at hmem
  have hBY : (B ⊓ yamadaF₂ d t) ⊓ yamadaY₂ d t ≤ d.Y.map L.subtype := by
    rw [← h.yamadaF₂_sup_zpowers_inf_centralizer d hlay]
    intro z hz
    obtain ⟨hzBF, hzY⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hzB, hzF⟩ := Subgroup.mem_inf.1 hzBF
    have hle : B ⊔ yamadaF₂ d t ≤ centralizer ({z} : Set G) :=
      sup_le (fun b hb => mem_centralizer_singleton_iff.2 (hB b hb z hzB))
        (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hYc hx) z hzY).symm)
    exact Subgroup.mem_inf.2 ⟨mem_sup_left hzF, mem_centralizer_iff.2 fun x hx =>
      mem_centralizer_singleton_iff.1 (hle (hQ hx))⟩
  have hcomm : ∀ x ∈ B ⊓ yamadaF₂ d t, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (hYc (Subgroup.mem_inf.1 hx).2) y hy).symm
  have h5 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [h.card_yamadaY₂ d hlay] at h5
  have h6 := h.card_sup_yamadaY₂_le d hlay (A := B ⊓ yamadaF₂ d t) inf_le_right
    (fun x hx y hy => hB x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1)
  have h7 : Nat.card ((B ⊓ yamadaF₂ d t) ⊓ yamadaY₂ d t : Subgroup G) ≤ (2 ^ f) ^ 2 := by
    calc Nat.card ((B ⊓ yamadaF₂ d t) ⊓ yamadaY₂ d t : Subgroup G) ≤
        Nat.card (d.Y.map L.subtype) := card_le_of_le hBY
      _ = (2 ^ f) ^ 2 := by rw [card_map_of_injective L.subtype_injective, d.card_Y]
  have h8 : Nat.card (B ⊓ yamadaF₂ d t : Subgroup G) * (2 ^ f) ^ 4 ≤ (2 ^ f) ^ 5 * (2 ^ f) ^ 4 := by
    rw [← h5]
    calc Nat.card ((B ⊓ yamadaF₂ d t) ⊔ yamadaY₂ d t : Subgroup G) *
        Nat.card ((B ⊓ yamadaF₂ d t) ⊓ yamadaY₂ d t : Subgroup G) ≤
          (2 ^ f) ^ 7 * (2 ^ f) ^ 2 := Nat.mul_le_mul h6 h7
      _ = (2 ^ f) ^ 5 * (2 ^ f) ^ 4 := by ring
  have h9 := Nat.le_of_mul_le_mul_right h8 (by positivity)
  omega

theorem yamada_5_10_2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t := by
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
  have hq5 : 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 7 := by
    have : (2 ^ f) ^ 7 = (2 ^ f) ^ 2 * (2 ^ f) ^ 5 := by ring
    rw [this]
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    have h5 : 0 < (2 ^ f) ^ 5 := by positivity
    nlinarith
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  have hYcomm : ∀ x ∈ yamadaY₂ d t, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    h.mul_comm_of_mem_yamadaY₂ d hlay hx hy
  have hmax : ∀ B : Subgroup G, B ≤ yamadaF₂ d t ⊔ zpowers t → IsMulCommutative B →
      Nat.card B ≤ (2 ^ f) ^ 7 := by
    intro B hBQ hBc
    have hB := fun x (hx : x ∈ B) y (hy : y ∈ B) => mul_comm_of_isMulCommutative_D1 hBc hx hy
    by_cases hBF : B ≤ yamadaF₂ d t
    · exact (card_le_of_le le_sup_left).trans (h.card_sup_yamadaY₂_le d hlay hBF hB)
    · exact (h.card_le_of_not_le_yamadaF₂ d hlay hBQ hB hBF).trans hq5.le
  have hin : ∀ B : Subgroup G, B ≤ yamadaF₂ d t ⊔ zpowers t → IsMulCommutative B →
      (2 ^ f) ^ 7 ≤ Nat.card B → B ≤ yamadaF₂ d t := by
    intro B hBQ hBc hcard
    by_contra hBF
    have := h.card_le_of_not_le_yamadaF₂ d hlay hBQ
      (fun x hx y hy => mul_comm_of_isMulCommutative_D1 hBc hx hy) hBF
    omega
  have hgen : ∀ E : Subgroup L, d.Y ≤ E → E ≤ d.F → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      Nat.card E = (2 ^ f) ^ 5 → E.map L.subtype ⊔ yamadaY₂ d t ≤ CFSG.Open.thompsonSubgroup
        (yamadaF₂ d t ⊔ zpowers t) := by
    intro E hYE hEF hEc hEcard
    have hEY : ∀ x ∈ E.map L.subtype, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
      (mem_centralizer_iff.1 (hMY (map_mono (hEF.trans d.F_le_M) hx)) y hy).symm
    have hEc' : ∀ x ∈ E.map L.subtype, ∀ y ∈ E.map L.subtype, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hEc x hx y hy)
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hEY).1
    rw [h.map_inf_yamadaY₂ d hlay hYE, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, d.card_Y, hEcard, h.card_yamadaY₂ d hlay]
      at hcard
    have hcard7 : Nat.card (E.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) = (2 ^ f) ^ 7 :=
      Nat.eq_of_mul_eq_mul_right (by positivity) (hcard.trans (by ring))
    refine le_thompsonSubgroup_D1 (sup_le ((map_mono hEF).trans (le_sup_left.trans le_sup_left))
      ((le_sup_right (a := d.F.map L.subtype)).trans le_sup_left))
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_sup_D1 hEc' hYcomm hEY a.2 b.2)⟩⟩ ?_
    intro B hBQ hBc
    rw [hcard7]
    exact hmax B hBQ hBc
  apply le_antisymm
  · refine thompsonSubgroup_le_D1 fun A hAQ hAc hAm => hin A hAQ hAc ?_
    have hW := hAm (d.W.map L.subtype ⊔ yamadaY₂ d t)
      ((sup_le_sup_right (map_mono d.W_le_F) _).trans le_sup_left)
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_sup_D1 (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (d.mul_comm_of_mem_W hx hy)) hYcomm (fun x hx y hy =>
          (mem_centralizer_iff.1 (hMY (map_mono (d.W_le_F.trans d.F_le_M) hx)) y hy).symm)
        a.2 b.2)⟩⟩
    have hcardW := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (d.W.map L.subtype)
      (yamadaY₂ d t) (fun x hx y hy =>
        (mem_centralizer_iff.1 (hMY (map_mono (d.W_le_F.trans d.F_le_M) hx)) y hy).symm)).1
    rw [h.map_inf_yamadaY₂ d hlay d.Y_le_W, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, d.card_Y, d.card_W,
      h.card_yamadaY₂ d hlay] at hcardW
    have hW7 : Nat.card (d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) = (2 ^ f) ^ 7 :=
      Nat.eq_of_mul_eq_mul_right (by positivity) (hcardW.trans (by ring))
    rw [hW7] at hW
    exact hW
  ·
    have hW := hgen d.W d.Y_le_W d.W_le_F (fun x hx y hy => d.mul_comm_of_mem_W hx hy) d.card_W
    set U₃Y := (TrialityD4Data.tripleHom d.x₃_add d.x₅_add d.x₆_add d.commute₃₅ d.commute₃₆
      d.commute₅₆).range with hU₃Y
    have hU₃YF : U₃Y ≤ d.F := by
      rintro _ ⟨p, rfl⟩
      exact mul_mem (mul_mem (d.x₃_mem_F _) (d.x₅_mem_F _)) (d.x₆_mem_F _)
    have hYU₃Y : d.Y ≤ U₃Y := by
      refine sup_le ?_ ?_
      · rintro _ ⟨b, rfl⟩
        have := TrialityD4Data.mem_range_tripleHom d.x₃_add d.x₅_add d.x₆_add d.commute₃₅
          d.commute₃₆ d.commute₅₆ 0 b 0
        rwa [d.x₃_zero, d.x₆_zero, one_mul, mul_one] at this
      · rintro _ ⟨c, rfl⟩
        have := TrialityD4Data.mem_range_tripleHom d.x₃_add d.x₅_add d.x₆_add d.commute₃₅
          d.commute₃₆ d.commute₅₆ 0 0 c
        rwa [d.x₃_zero, d.x₅_zero, one_mul, one_mul] at this
    have hU₃Yc : ∀ x ∈ U₃Y, ∀ y ∈ U₃Y, x * y = y * x := fun x hx y hy =>
      mul_comm_of_isMulCommutative_D1 (TrialityD4Data.isElemAbelian_range_tripleHom _ _ _ _ _ _
        (TrialityD4Data.prod_add_self_eq_zero CharTwo.add_self_eq_zero d.add_self_Γ₀
          d.add_self_Γ₀)).1 hx hy
    have hU₃Ycard : Nat.card U₃Y = (2 ^ f) ^ 5 := by
      rw [hU₃Y, TrialityD4Data.card_range_tripleHom, d.card_Γ, d.card_Γ₀]
      · ring
      · intro p p' hp
        have h' : d.nf (0, 0, p.1, 0, p.2.1, p.2.2) = d.nf (0, 0, p'.1, 0, p'.2.1, p'.2.2) := by
          simpa only [TrialityD4Data.nf_apply, d.x₁_zero, d.x₂_zero, d.x₄_zero, mul_one,
            one_mul] using hp
        have := d.nf_injective h'
        simp only [Prod.mk.injEq] at this
        exact Prod.ext this.2.2.1 (Prod.ext this.2.2.2.2.1 this.2.2.2.2.2)
    have hU := hgen U₃Y hYU₃Y hU₃YF hU₃Yc hU₃Ycard
    refine sup_le ?_ (le_sup_right.trans hW)
    show (d.U₃ ⊔ d.W).map L.subtype ≤ _
    rw [Subgroup.map_sup]
    refine sup_le ?_ (le_sup_left.trans hW)
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine hU (mem_sup_left ⟨d.x₃ a, ?_, rfl⟩)
    have := TrialityD4Data.mem_range_tripleHom d.x₃_add d.x₅_add d.x₆_add d.commute₃₅
      d.commute₃₆ d.commute₅₆ a 0 0
    rwa [d.x₅_zero, d.x₆_zero, mul_one, mul_one] at this

end Thompson

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
