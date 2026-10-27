module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowOuter
public import CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

section Generic

variable {G G' : Type*} [Group G] [Group G']

theorem ElemAbMod.map {N E : Subgroup G} (hE : ElemAbMod N E) (φ : G →* G') :
    ElemAbMod (N.map φ) (E.map φ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x * x, hE.1 x hx, map_mul _ _ _⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨⁅x, y⁆, hE.2 x hx y hy, map_commutatorElement _ _ _⟩

theorem zpow_eq_one_or_eq_of_mul_self {t : G} (ht : t * t = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.emod_add_mul_ediv k 2, hk, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem mul_self_t_mul {t e : G} (ht : t * t = 1) (hte : e * t = t * e) :
    t * e * (t * e) = e * e := by
  calc t * e * (t * e) = t * (e * t) * e := by group
    _ = t * (t * e) * e := by rw [hte]
    _ = e * e := by rw [← mul_assoc, ht, one_mul]

theorem commutatorElement_t_mul_left {t a b : G} (ht : t * t = 1) (hta : a * t = t * a)
    (htb : b * t = t * b) : ⁅t * a, b⁆ = ⁅a, b⁆ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : a⁻¹ * t = t * a⁻¹ := by
    calc a⁻¹ * t = a⁻¹ * (t * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * t) * a⁻¹ := by rw [hta]
      _ = t * a⁻¹ := by group
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, htinv]
  calc t * a * b * (a⁻¹ * t) * b⁻¹ = t * a * b * (t * a⁻¹) * b⁻¹ := by rw [h1]
    _ = t * (a * (b * t)) * a⁻¹ * b⁻¹ := by group
    _ = t * (a * (t * b)) * a⁻¹ * b⁻¹ := by rw [htb]
    _ = t * ((a * t) * b) * a⁻¹ * b⁻¹ := by group
    _ = t * ((t * a) * b) * a⁻¹ * b⁻¹ := by rw [hta]
    _ = (t * t) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [ht, one_mul]

theorem commutatorElement_t_mul_right {t a b : G} (ht : t * t = 1) (hta : a * t = t * a)
    (htb : b * t = t * b) : ⁅a, t * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_t_mul_left ht htb hta, commutatorElement_inv]

theorem conj_mem_centerIn {X : Subgroup G} {y z : G} (hy : y ∈ normalizer (X : Set G))
    (hz : z ∈ CFSG.centerIn X) : y * z * y⁻¹ ∈ CFSG.centerIn X := by
  refine ⟨(mem_normalizer_iff.1 hy z).1 hz.1, mem_centralizer_iff.2 fun k hk => ?_⟩
  have hk' : y⁻¹ * k * y ∈ X := by
    have := (mem_normalizer_iff.1 (inv_mem hy) k).1 hk
    rwa [inv_inv] at this
  have := mem_centralizer_iff.1 hz.2 _ hk'
  calc k * (y * z * y⁻¹) = y * ((y⁻¹ * k * y) * z) * y⁻¹ := by group
    _ = y * (z * (y⁻¹ * k * y)) * y⁻¹ := by rw [this]
    _ = y * z * y⁻¹ * k := by group

end Generic

section GenericFinite

variable {G : Type} [Group G] [Finite G]

theorem exists_of_mem_zpowers_sup_of_commute {t : G} (ht : t * t = 1) {E : Subgroup G}
    (hE : ∀ e ∈ E, e * t = t * e) {x : G} (hx : x ∈ zpowers t ⊔ E) :
    ∃ e ∈ E, x = e ∨ x = t * e := by
  obtain ⟨y, hy, e, he, hye⟩ := exists_mul_of_mem_sup_of_commute (fun y hy e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hE e he).symm k).eq) hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  refine ⟨e, he, ?_⟩
  rcases zpow_eq_one_or_eq_of_mul_self ht k with h1 | h1
  · left
    rw [hye, h1, one_mul]
  · right
    rw [hye, h1]

theorem ElemAbMod.zpowers_sup {t : G} (ht : t * t = 1) {N E : Subgroup G} (hE : ElemAbMod N E)
    (hEt : ∀ e ∈ E, e * t = t * e) : ElemAbMod (zpowers t ⊔ N) (zpowers t ⊔ E) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨e, he, hxe | hxe⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hx
    · rw [hxe]
      exact mem_sup_right (hE.1 e he)
    · rw [hxe, mul_self_t_mul ht (hEt e he)]
      exact mem_sup_right (hE.1 e he)
  · obtain ⟨a, ha, hxa | hxa⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hx <;>
    obtain ⟨b, hb, hyb | hyb⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hy <;>
    rw [hxa, hyb]
    · exact mem_sup_right (hE.2 a ha b hb)
    · rw [commutatorElement_t_mul_right ht (hEt a ha) (hEt b hb)]
      exact mem_sup_right (hE.2 a ha b hb)
    · rw [commutatorElement_t_mul_left ht (hEt a ha) (hEt b hb)]
      exact mem_sup_right (hE.2 a ha b hb)
    · rw [commutatorElement_t_mul_left ht (hEt a ha) (by rw [mul_assoc, hEt b hb]),
        commutatorElement_t_mul_right ht (hEt a ha) (hEt b hb)]
      exact mem_sup_right (hE.2 a ha b hb)

end GenericFinite

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {X : Subgroup G} {n : G}
    (hn : n ∈ normalizer (X : Set G)) : X.map (MulAut.conj n).toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hn x).1 hx
  · intro y hy
    refine ⟨n⁻¹ * y * n, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
    rwa [inv_inv] at this

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
  (d : Data G h)

@[expose] def B₂ : Subgroup G := zpowers d.t ⊔ d.A₂

theorem elemAbMod_pull {N M : Subgroup (hypSU h 2 1)} (hM : ElemAbMod N M) :
    ElemAbMod (d.pull N) (d.pull M) :=
  hM.map d.η

theorem A₁_sup_A₂ : d.A₁ ⊔ d.A₂ = d.pull (Vsub h ⊔ A₂sub h) :=
  (Subgroup.map_sup _ _ _).symm

theorem A₂_le_L : d.A₂ ≤ d.L := d.A₂_le_P.trans d.P_le_L

theorem Zp_le_A₂ : d.Zp ≤ d.A₂ := d.Zp_le_Z₂p.trans d.Z₂p_le_A₂

theorem A₁_sup_A₂_le_P : d.A₁ ⊔ d.A₂ ≤ d.P := sup_le d.A₁_le_P d.A₂_le_P

theorem card_A₃ : Nat.card d.A₃ = (2 ^ f) ^ 8 := by
  rw [Data.A₃, d.card_pull Ssub_le_Usub, card_Ssub]

theorem card_A₁_sup_A₂ : Nat.card (d.A₁ ⊔ d.A₂ : Subgroup G) = (2 ^ f) ^ 8 := by
  rw [d.A₁_sup_A₂, d.card_pull (sup_le (Vsub_le_Ssub.trans Ssub_le_Usub) A₂sub_le_U),
    Vsub_sup_A₂sub_eq, card_patSub_sB₂]

theorem elemAbMod_A₁_A₃ : ElemAbMod d.A₁ d.A₃ := d.elemAbMod_pull elemAbMod_Vsub_Ssub

theorem elemAbMod_A₁_sup_A₂ : ElemAbMod d.A₁ (d.A₁ ⊔ d.A₂) := by
  rw [d.A₁_sup_A₂]
  exact d.elemAbMod_pull (by rw [Vsub_sup_A₂sub_eq]; exact elemAbMod_Vsub_sB₂)

theorem elemAbMod_Zp_A₂ : ElemAbMod d.Zp d.A₂ := d.elemAbMod_pull elemAbMod_ZPsub_A₂sub

theorem B₁_sup_A₂ : d.B₁ ⊔ d.A₂ = zpowers d.t ⊔ (d.A₁ ⊔ d.A₂) :=
  sup_assoc _ _ _

theorem B₃_sup_B₁_sup_A₂ : d.B₃ ⊔ (d.B₁ ⊔ d.A₂) = d.tP := by
  have hP := d.A₃_sup_A₁_sup_A₂
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (le_sup_of_le_right d.A₃_le_P))
      (sup_le (sup_le le_sup_left (le_sup_of_le_right d.A₁_le_P)) (le_sup_of_le_right d.A₂_le_P))
  · refine sup_le (le_sup_of_le_left le_sup_left) ?_
    rw [← hP]
    exact sup_le (le_sup_of_le_left le_sup_right)
      (sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_right))
        (le_sup_of_le_right le_sup_right))

theorem B₃_le_tP : d.B₃ ≤ d.tP :=
  (le_sup_left : d.B₃ ≤ d.B₃ ⊔ (d.B₁ ⊔ d.A₂)).trans d.B₃_sup_B₁_sup_A₂.le

theorem B₁_sup_A₂_le_tP : d.B₁ ⊔ d.A₂ ≤ d.tP :=
  (le_sup_right : d.B₁ ⊔ d.A₂ ≤ d.B₃ ⊔ (d.B₁ ⊔ d.A₂)).trans d.B₃_sup_B₁_sup_A₂.le

end Data

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.comm_t (hd : d.Hyp) {x : G} (hx : x ∈ d.L) : x * d.t = d.t * x :=
  mem_centralizer_iff.1 hd.t_mem x hx

theorem Hyp.exists_of_mem_zpowers_sup (hd : d.Hyp) {M : Subgroup G} (hM : M ≤ d.L) {x : G}
    (hx : x ∈ zpowers d.t ⊔ M) : ∃ m ∈ M, x = m ∨ x = d.t * m :=
  exists_of_mem_zpowers_sup_of_commute hd.t_mul_t (fun _ hm => hd.comm_t (hM hm)) hx

theorem Hyp.card_zpowers_sup (hd : d.Hyp) {M : Subgroup G} (hM : M ≤ d.L) :
    Nat.card (zpowers d.t ⊔ M : Subgroup G) = 2 * Nat.card M := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers d.t) M
    fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact (Commute.zpow_left (hd.comm_t (hM hy)).symm k).eq
  have hinf : zpowers d.t ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxt, hxM⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases hd.zpow_t_eq k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hxM
      exact absurd (hM hxM) hd.t_not_mem_L
  rw [hinf, Subgroup.card_bot, mul_one, hd.card_zpowers_t] at hc
  exact hc

theorem Hyp.elemAbMod_zpowers_sup (hd : d.Hyp) {N M : Subgroup G} (hM : M ≤ d.L)
    (hNM : ElemAbMod N M) : ElemAbMod (zpowers d.t ⊔ N) (zpowers d.t ⊔ M) :=
  hNM.zpowers_sup hd.t_mul_t fun _ hm => hd.comm_t (hM hm)

theorem Hyp.card_B₂ (hd : d.Hyp) : Nat.card d.B₂ = 2 * (2 ^ f) ^ 7 := by
  rw [Data.B₂, hd.card_zpowers_sup d.A₂_le_L, d.card_A₂]

theorem Hyp.card_B₃ (hd : d.Hyp) : Nat.card d.B₃ = 2 * (2 ^ f) ^ 8 := by
  rw [Data.B₃, hd.card_zpowers_sup (d.A₃_le_P.trans d.P_le_L), d.card_A₃]

theorem Hyp.card_B₁_sup_A₂ (hd : d.Hyp) :
    Nat.card (d.B₁ ⊔ d.A₂ : Subgroup G) = 2 * (2 ^ f) ^ 8 := by
  rw [d.B₁_sup_A₂, hd.card_zpowers_sup (d.A₁_sup_A₂_le_P.trans d.P_le_L), d.card_A₁_sup_A₂]

theorem Hyp.elemAbMod_B₁_B₃ (hd : d.Hyp) : ElemAbMod d.B₁ d.B₃ :=
  hd.elemAbMod_zpowers_sup (d.A₃_le_P.trans d.P_le_L) d.elemAbMod_A₁_A₃

theorem Hyp.elemAbMod_B₁_B₁_sup_A₂ (hd : d.Hyp) : ElemAbMod d.B₁ (d.B₁ ⊔ d.A₂) := by
  rw [d.B₁_sup_A₂]
  exact hd.elemAbMod_zpowers_sup (d.A₁_sup_A₂_le_P.trans d.P_le_L) d.elemAbMod_A₁_sup_A₂

theorem Hyp.tP_le_T (hd : d.Hyp) : d.tP ≤ d.T := sup_le (zpowers_le.2 hd.t_mem_T) hd.P_le

theorem Hyp.tP_le_centralizer (hd : d.Hyp) : d.tP ≤ centralizer ({d.t} : Set G) :=
  hd.tP_le_T.trans hd.T_le_centralizer

theorem Hyp.act_mem_Vh_of_mem_B₁ (hd : d.Hyp) {x : G} (hxB : x ∈ d.B₁)
    (hxN : x ∈ normalizer (d.L : Set G)) : d.act ⟨x, hxN⟩ ∈ Vh h := by
  obtain ⟨a, ha, hxa | hxa⟩ := hd.exists_of_mem_B₁ hxB <;> subst x
  · rw [← d.actImage_A₁]
    exact d.mem_actImage.2 ⟨a, ha, hxN, rfl⟩
  · have htN : d.t ∈ normalizer (d.L : Set G) := Subgroup.centralizer_le_normalizer _ hd.t_mem
    have haN : a ∈ normalizer (d.L : Set G) := le_normalizer (d.A₁_le_P.trans d.P_le_L ha)
    have e : (⟨d.t * a, hxN⟩ : normalizer (d.L : Set G)) = ⟨d.t, htN⟩ * ⟨a, haN⟩ := rfl
    rw [e, map_mul, (d.act_eq_one_iff _).2 hd.t_mem, one_mul, ← d.actImage_A₁]
    exact d.mem_actImage.2 ⟨a, ha, haN, rfl⟩

theorem Hyp.mem_zpowers_sup_of_act_mem (hd : d.Hyp) {M : Subgroup G} (hM : M ≤ d.P) {x : G}
    (hxT : x ∈ d.T) (hxN : x ∈ normalizer (d.L : Set G)) (hx : d.act ⟨x, hxN⟩ ∈ d.actImage M) :
    x ∈ zpowers d.t ⊔ M := by
  obtain ⟨a, haM, haN, ha⟩ := d.mem_actImage.1 hx
  have hc : a⁻¹ * x ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨a⁻¹ * x, mul_mem (inv_mem haN) hxN⟩).1 ?_
    have e : (⟨a⁻¹ * x, mul_mem (inv_mem haN) hxN⟩ : normalizer (d.L : Set G)) =
        (⟨a, haN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨x, hxN⟩ := rfl
    rw [e, map_mul, map_inv, ha, inv_mul_cancel]
  have hcT : a⁻¹ * x ∈ d.T := mul_mem (inv_mem (hd.P_le (hM haM))) hxT
  have hct : a⁻¹ * x ∈ zpowers d.t :=
    (hd.sec3_1').1 ▸ ⟨hc, hd.T_le_centralizer hcT⟩
  rw [show x = a * (a⁻¹ * x) by group]
  exact mul_mem (mem_sup_right haM) (mem_sup_left hct)

theorem Hyp.card_le_of_elemAbMod_B₁ (hd : d.Hyp) {E : Subgroup G} (hET : E ≤ d.T)
    (hE : ElemAbMod d.B₁ E) :
    Nat.card E ≤ 2 * (2 ^ f) ^ 8 ∧
      (Nat.card E = 2 * (2 ^ f) ^ 8 → E = d.B₃ ∨ E = d.B₁ ⊔ d.A₂) := by
  have hEN : E ≤ normalizer (d.L : Set G) := hET.trans hd.T_le_normalizer
  set ψ : E →* MulAut (hypPSU h 2 1) := d.act.comp (Subgroup.inclusion hEN) with hψ
  have hψ_apply : ∀ x : E, ψ x = d.act ⟨x, hEN x.2⟩ := fun _ => rfl
  have hrT : ψ.range ≤ d.actImage d.T := by
    rintro _ ⟨x, rfl⟩
    exact d.mem_actImage.2 ⟨x, hET x.2, hEN x.2, rfl⟩
  have hX : ElemAbMod (Vh h) ψ.range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [← map_mul, hψ_apply]
      exact hd.act_mem_Vh_of_mem_B₁ (hE.1 x x.2) _
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_commutatorElement, hψ_apply]
      exact hd.act_mem_Vh_of_mem_B₁ (hE.2 x x.2 y y.2) _
  obtain ⟨hr1, hr2⟩ := elemAbMod_Vh_T hd.center_hypPSU hd.two_le hd.inf_Pi_actImage_T hrT hX
  have hker : Nat.card ψ.ker ≤ 2 := by
    calc Nat.card ψ.ker = Nat.card (ψ.ker.map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card (zpowers d.t) := by
          refine Subgroup.card_le_of_le ?_
          rintro _ ⟨z, hz, rfl⟩
          exact (hd.sec3_1').1 ▸ ⟨(d.act_eq_one_iff _).1 (MonoidHom.mem_ker.1 hz),
            hd.T_le_centralizer (hET z.2)⟩
      _ = 2 := hd.card_zpowers_t
  have hprod := Subgroup.card_ker_mul_card_range ψ
  refine ⟨?_, fun hcard => ?_⟩
  · rw [← hprod]
    exact Nat.mul_le_mul hker hr1
  · have hr8 : Nat.card ψ.range = (2 ^ f) ^ 8 := by
      refine le_antisymm hr1 ?_
      by_contra hlt
      push Not at hlt
      have : Nat.card ψ.ker * Nat.card ψ.range < 2 * (2 ^ f) ^ 8 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt two_pos)
      rw [hprod, hcard] at this
      exact lt_irrefl _ this
    rcases hr2 hr8.ge with hS | hB
    · left
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hd.card_B₃, hcard])
      have hmem : ψ ⟨x, hx⟩ ∈ d.actImage d.A₃ := by
        rw [d.actImage_A₃, ← hS]
        exact ⟨⟨x, hx⟩, rfl⟩
      exact hd.mem_zpowers_sup_of_act_mem d.A₃_le_P (hET hx) (hEN hx) hmem
    · right
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hd.card_B₁_sup_A₂, hcard])
      have hmem : ψ ⟨x, hx⟩ ∈ d.actImage (d.A₁ ⊔ d.A₂) := by
        rw [d.A₁_sup_A₂, d.actImage_pull, ← hB]
        exact ⟨⟨x, hx⟩, rfl⟩
      rw [d.B₁_sup_A₂]
      exact hd.mem_zpowers_sup_of_act_mem d.A₁_sup_A₂_le_P (hET hx) (hEN hx) hmem

theorem Hyp.ZtP_eq (hd : d.Hyp) : d.ZtP = zpowers d.t ⊔ d.Zp := by
  have hZP : CFSG.centerIn d.P = d.Zp := d.sec2_2_three.2.2.2.2
  have hZL : d.Zp ≤ d.L := d.Zp_le_A₂.trans d.A₂_le_L
  apply le_antisymm
  · rintro x ⟨hxt, hxc⟩
    obtain ⟨p, hp, hxp | hxp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hxt <;> subst x
    · refine mem_sup_right (hZP ▸ ⟨hp, mem_centralizer_iff.2 fun y hy => ?_⟩)
      exact mem_centralizer_iff.1 hxc y (mem_sup_right hy)
    · refine mul_mem (mem_sup_left (mem_zpowers _))
        (mem_sup_right (hZP ▸ ⟨hp, mem_centralizer_iff.2 fun y hy => ?_⟩))
      have h1 := mem_centralizer_iff.1 hxc y (mem_sup_right hy)
      have hyt := hd.comm_t (d.P_le_L hy)
      have : d.t * (y * p) = d.t * (p * y) := by
        calc d.t * (y * p) = (d.t * y) * p := by group
          _ = (y * d.t) * p := by rw [hyt]
          _ = y * (d.t * p) := by group
          _ = d.t * p * y := h1
          _ = d.t * (p * y) := by group
      exact mul_left_cancel this
  · refine le_inf (sup_le_sup_left (d.Zp_le_A₂.trans d.A₂_le_P) _) (sup_le ?_ ?_)
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_singleton_iff.1 (hd.tP_le_centralizer hy)
    · intro z hz
      have hz' : z ∈ CFSG.centerIn d.P := hZP ▸ hz
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨p, hp, hyp | hyp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hy <;> subst y
      · exact mem_centralizer_iff.1 hz'.2 p hp
      · have h1 : p * z = z * p := mem_centralizer_iff.1 hz'.2 p hp
        have h2 : z * d.t = d.t * z := hd.comm_t (hZL hz)
        calc d.t * p * z = d.t * (p * z) := by group
          _ = d.t * (z * p) := by rw [h1]
          _ = (d.t * z) * p := by group
          _ = (z * d.t) * p := by rw [h2]
          _ = z * (d.t * p) := by group

theorem Hyp.ZtP_inf_P (hd : d.Hyp) : d.ZtP ⊓ d.P = d.Zp := by
  rw [hd.ZtP_eq]
  apply le_antisymm
  · rintro x ⟨hx, hxP⟩
    obtain ⟨z, hz, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup (d.Zp_le_A₂.trans d.A₂_le_L) hx
    · exact hz
    · exfalso
      have hzP : z ∈ d.P := (d.Zp_le_A₂.trans d.A₂_le_P) hz
      have hxP' : d.t * z ∈ d.P := hxP
      have : d.t ∈ d.P := by
        have := mul_mem hxP' (inv_mem hzP)
        rwa [mul_inv_cancel_right] at this
      exact hd.t_not_mem_L (d.P_le_L this)
  · exact le_inf le_sup_right (d.Zp_le_A₂.trans d.A₂_le_P)

theorem Hyp.card_le_of_elemAbMod_ZtP (hd : d.Hyp) {E : Subgroup G} (hZE : d.ZtP ≤ E)
    (hEt : E ≤ d.tP) (hE : ElemAbMod d.ZtP E) :
    Nat.card E ≤ 2 * (2 ^ f) ^ 7 ∧ (Nat.card E = 2 * (2 ^ f) ^ 7 → E = d.B₂) := by
  set E₀ := E ⊓ d.P with hE₀def
  have hE₀P : E₀ ≤ d.P := inf_le_right
  have hE₀ : ElemAbMod d.Zp E₀ := by
    rw [← hd.ZtP_inf_P]
    refine ⟨fun x hx => Subgroup.mem_inf.2 ⟨hE.1 x hx.1, ?_⟩,
      fun x hx y hy => Subgroup.mem_inf.2 ⟨hE.2 x hx.1 y hy.1, ?_⟩⟩
    · have hxP : x ∈ d.P := hx.2
      exact mul_mem hxP hxP
    have hxP : x ∈ d.P := hx.2
    have hyP : y ∈ d.P := hy.2
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxP hyP) (inv_mem hxP)) (inv_mem hyP)
  have htE : d.t ∈ E := hZE (by rw [hd.ZtP_eq]; exact mem_sup_left (mem_zpowers _))
  have hEeq : E = zpowers d.t ⊔ E₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, hxp | hxp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L (hEt hx) <;> subst x
      · exact mem_sup_right ⟨hx, hp⟩
      · have hpE : p ∈ E := by
          have := mul_mem (inv_mem htE) hx
          rwa [inv_mul_cancel_left] at this
        exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ⟨hpE, hp⟩)
    · exact sup_le (zpowers_le.2 htE) inf_le_left
  have hcard : Nat.card E = 2 * Nat.card E₀ := by
    rw [hEeq]
    exact hd.card_zpowers_sup (hE₀P.trans d.P_le_L)
  obtain ⟨-, hc7, hc⟩ := d.sec2_2_modZp hE₀P hE₀
  refine ⟨by rw [hcard]; exact Nat.mul_le_mul_left 2 hc7, fun h7 => ?_⟩
  have h7' : Nat.card E₀ = (2 ^ f) ^ 7 := by
    rw [hcard] at h7
    exact Nat.eq_of_mul_eq_mul_left two_pos h7
  rw [hEeq, hc h7'.ge]
  rfl

theorem Hyp.B₂_spec (hd : d.Hyp) :
    d.ZtP ≤ d.B₂ ∧ d.B₂ ≤ d.tP ∧ ElemAbMod d.ZtP d.B₂ ∧ Nat.card d.B₂ = 2 * (2 ^ f) ^ 7 := by
  refine ⟨?_, sup_le_sup_left d.A₂_le_P _, ?_, hd.card_B₂⟩
  · rw [hd.ZtP_eq]
    exact sup_le_sup_left d.Zp_le_A₂ _
  · rw [hd.ZtP_eq]
    exact hd.elemAbMod_zpowers_sup d.A₂_le_L d.elemAbMod_Zp_A₂

theorem Hyp.weakly_closed_tP (hd : d.Hyp) (c : G) (hc : ∀ r ∈ d.tP, c⁻¹ * r * c ∈ d.T) :
    ∀ r ∈ d.tP, c⁻¹ * r * c ∈ d.tP := by
  set φ : G →* G := (MulAut.conj c⁻¹).toMonoidHom with hφ
  have hφapp : ∀ x, φ x = c⁻¹ * x * c := fun x => by simp [hφ]
  have hinj : Function.Injective φ := (MulAut.conj c⁻¹).injective
  have hle : ∀ X ≤ d.tP, X.map φ ≤ d.T := by
    rintro X hX _ ⟨x, hx, rfl⟩
    rw [hφapp]
    exact hc x (hX hx)
  have hB₁tP : d.B₁ ≤ d.tP := sup_le_sup_left d.A₁_le_P _
  have hB₁ : d.B₁.map φ = d.B₁ := by
    have := hd.isElementaryAbelian_B₁
    refine (hd.sec3_1').2.2.1 _ (hle _ hB₁tP) (CFSG.IsElementaryAbelian.map _) ?_
    rw [Subgroup.card_map_of_injective hinj, hd.card_B₁]
  have hW : ∀ W : Subgroup G, W ≤ d.tP → d.B₁ ≤ W → ElemAbMod d.B₁ W →
      Nat.card W = 2 * (2 ^ f) ^ 8 → W.map φ ≤ d.tP := by
    intro W hWt hBW hWe hcard
    have h2 : ElemAbMod d.B₁ (W.map φ) := hB₁ ▸ hWe.map φ
    have h3 : Nat.card (W.map φ) = 2 * (2 ^ f) ^ 8 := by
      rw [Subgroup.card_map_of_injective hinj, hcard]
    rcases (hd.card_le_of_elemAbMod_B₁ (hle _ hWt) h2).2 h3 with e | e
    · rw [e]
      exact d.B₃_le_tP
    · rw [e]
      exact d.B₁_sup_A₂_le_tP
  have hmap : (d.B₃ ⊔ (d.B₁ ⊔ d.A₂)).map φ ≤ d.tP := by
    rw [Subgroup.map_sup]
    exact sup_le (hW _ d.B₃_le_tP d.B₁_le_B₃ hd.elemAbMod_B₁_B₃ hd.card_B₃)
      (hW _ d.B₁_sup_A₂_le_tP le_sup_left hd.elemAbMod_B₁_B₁_sup_A₂ hd.card_B₁_sup_A₂)
  intro r hr
  rw [← hφapp]
  rw [← d.B₃_sup_B₁_sup_A₂] at hr
  exact hmap ⟨r, hr, rfl⟩

theorem Hyp.normalizer_T_le (hd : d.Hyp) :
    normalizer (d.T : Set G) ≤ normalizer (d.tP : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_le fun r hr => ?_
  have h := hd.weakly_closed_tP n⁻¹ (fun r hr => by
    rw [inv_inv]
    exact (mem_normalizer_iff.1 hn r).1 (hd.tP_le_T hr)) r hr
  rwa [inv_inv] at h

theorem normalizer_tP_le_normalizer_ZtP (d : Data G h) :
    normalizer (d.tP : Set G) ≤ normalizer (d.ZtP : Set G) :=
  fun _ hn => mem_normalizer_of_conj_le fun _ hz => conj_mem_centerIn hn hz

theorem Hyp.normalizer_tP_le (hd : d.Hyp) :
    normalizer (d.tP : Set G) ≤ normalizer (d.B₂ : Set G) := by
  intro n hn
  set φ : G →* G := (MulAut.conj n).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj n).injective
  have hZ : d.ZtP.map φ = d.ZtP :=
    map_conj_eq_of_mem_normalizer (d.normalizer_tP_le_normalizer_ZtP hn)
  have ht : d.tP.map φ = d.tP := map_conj_eq_of_mem_normalizer hn
  obtain ⟨hZB, hBt, hBe, hBc⟩ := hd.B₂_spec
  have h1 : d.ZtP ≤ d.B₂.map φ := hZ ▸ Subgroup.map_mono hZB
  have h2 : d.B₂.map φ ≤ d.tP := ht ▸ Subgroup.map_mono hBt
  have h3 : ElemAbMod d.ZtP (d.B₂.map φ) := hZ ▸ hBe.map φ
  have h4 : Nat.card (d.B₂.map φ) = 2 * (2 ^ f) ^ 7 := by
    rw [Subgroup.card_map_of_injective hinj, hBc]
  have e := (hd.card_le_of_elemAbMod_ZtP h1 h2 h3).2 h4
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rw [← e]
  exact ⟨b, hb, rfl⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
