module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611Def
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.NotZ2A6Base

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem eq_on_closure {G : Type*} [Group G] {E : Subgroup G} {s : Set G}
    (hE : Subgroup.closure s = E) {f f' : G → G}
    (hf : ∀ e ∈ E, ∀ e' ∈ E, f (e * e') = f e * f e')
    (hf' : ∀ e ∈ E, ∀ e' ∈ E, f' (e * e') = f' e * f' e')
    (hs : ∀ e ∈ s, f e = f' e) : ∀ e ∈ E, f e = f' e := by
  have h1 : f 1 = 1 := by
    have := hf 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have h1' : f' 1 = 1 := by
    have := hf' 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ e ∈ E, f e⁻¹ = (f e)⁻¹ := fun e he => by
    have := hf e he e⁻¹ (E.inv_mem he)
    rw [mul_inv_cancel, h1] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hinv' : ∀ e ∈ E, f' e⁻¹ = (f' e)⁻¹ := fun e he => by
    have := hf' e he e⁻¹ (E.inv_mem he)
    rw [mul_inv_cancel, h1'] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  intro e he
  rw [← hE] at he
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => rw [h1, h1']
  | mul x y hx hy ihx ihy =>
    rw [hE] at hx hy
    rw [hf x hx y hy, hf' x hx y hy, ihx, ihy]
  | inv x hx ih =>
    rw [hE] at hx
    rw [hinv x hx, hinv' x hx, ih]

theorem cmt_eq_one_iff {G : Type*} [Group G] {q e : G} : q * e * q⁻¹ * e⁻¹ = 1 ↔ q * e = e * q := by
  constructor
  · intro h1
    calc q * e = (q * e * q⁻¹ * e⁻¹) * (e * q) := by group
      _ = e * q := by rw [h1, one_mul]
  · intro h1
    rw [h1]
    group

theorem mem_on_closure {G : Type*} [Group G] {E : Subgroup G} {s : Set G}
    (hE : Subgroup.closure s = E) {f : G → G} (hf : ∀ e ∈ E, ∀ e' ∈ E, f (e * e') = f e * f e')
    {A : Subgroup G} (hs : ∀ e ∈ s, f e ∈ A) : ∀ e ∈ E, f e ∈ A := by
  have h1 : f 1 = 1 := by
    have := hf 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  intro e he
  rw [← hE] at he
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => rw [h1]; exact A.one_mem
  | mul x y hx hy ihx ihy =>
    rw [hE] at hx hy
    rw [hf x hx y hy]
    exact A.mul_mem ihx ihy
  | inv x hx ih =>
    rw [hE] at hx
    have := hf x hx x⁻¹ (E.inv_mem hx)
    rw [mul_inv_cancel, h1] at this
    rw [eq_inv_of_mul_eq_one_right this.symm]
    exact A.inv_mem ih

open Classical in
@[expose] noncomputable def iota {G : Type*} [Group G] (ζ c : G) : G := if c = 1 then 1 else ζ

theorem iota_one {G : Type*} [Group G] (ζ : G) : iota ζ 1 = 1 := by simp [iota]

theorem iota_of_ne {G : Type*} [Group G] {ζ c : G} (hc : c ≠ 1) : iota ζ c = ζ := by
  simp [iota, hc]

theorem iota_eq_one_iff {G : Type*} [Group G] {ζ c : G} (hζ : ζ ≠ 1) : iota ζ c = 1 ↔ c = 1 := by
  by_cases hc : c = 1
  · simp [hc, iota_one]
  · simp [iota_of_ne hc, hζ, hc]

theorem iota_mem {G : Type*} [Group G] (ζ c : G) : iota ζ c = 1 ∨ iota ζ c = ζ := by
  by_cases hc : c = 1
  · left; simp [hc, iota_one]
  · right; exact iota_of_ne hc

theorem iota_mul {G : Type*} [Group G] {ζ t c c' : G} (hζ : ζ * ζ = 1) (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (hc : c = 1 ∨ c = t) (hc' : c' = 1 ∨ c' = t) :
    iota ζ (c * c') = iota ζ c * iota ζ c' := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · simp [iota_one]
  · simp [iota_one]
  · simp [iota_one]
  · rw [ht2, iota_one, iota_of_ne ht1, hζ]

theorem iota_inv_self {G : Type*} [Group G] {ζ : G} (hζ : ζ * ζ = 1) (c : G) :
    (iota ζ c)⁻¹ = iota ζ c := by
  rcases iota_mem ζ c with h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact inv_eq_of_mul_eq_one_right hζ

theorem bilin_ext {G : Type*} [Group G] {E : Subgroup G} {E2 : Set G}
    (hE : Subgroup.closure E2 = E) {t ζ : G} (ht1 : t ≠ 1) (ht2 : t * t = 1) (hζ : ζ * ζ = 1)
    {κ P : G → G → G} (hκ : ∀ x ∈ E, ∀ y ∈ E, κ x y = 1 ∨ κ x y = t)
    (hκL : ∀ x ∈ E, ∀ x' ∈ E, ∀ y ∈ E, κ (x * x') y = κ x y * κ x' y)
    (hκR : ∀ x ∈ E, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y * κ x y')
    (hPL : ∀ x ∈ E, ∀ x' ∈ E, ∀ y ∈ E, P (x * x') y = P x y * P x' y)
    (hPR : ∀ x ∈ E, ∀ y ∈ E, ∀ y' ∈ E, P x (y * y') = P x y * P x y')
    (hbase : ∀ x ∈ E2, ∀ y ∈ E2, P x y = iota ζ (κ x y)) :
    ∀ x ∈ E, ∀ y ∈ E, P x y = iota ζ (κ x y) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hP1l : ∀ y ∈ E, P 1 y = 1 := fun y hy => by
    have := hPL 1 E.one_mem 1 E.one_mem y hy
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have hP1r : ∀ x ∈ E, P x 1 = 1 := fun x hx => by
    have := hPR x hx 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have hκ1l : ∀ y ∈ E, κ 1 y = 1 := fun y hy => by
    have := hκL 1 E.one_mem 1 E.one_mem y hy
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have hκ1r : ∀ x ∈ E, κ x 1 = 1 := fun x hx => by
    have := hκR x hx 1 E.one_mem 1 E.one_mem
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have hκinvl : ∀ x ∈ E, ∀ y ∈ E, κ x⁻¹ y = κ x y := fun x hx y hy => by
    have h1 := hκL x hx x⁻¹ (E.inv_mem hx) y hy
    rw [mul_inv_cancel, hκ1l y hy] at h1
    have h2 : κ x⁻¹ y = (κ x y)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    rw [h2]
    rcases hκ x hx y hy with h3 | h3 <;> rw [h3]
    · simp
    · exact hti
  have hκinvr : ∀ x ∈ E, ∀ y ∈ E, κ x y⁻¹ = κ x y := fun x hx y hy => by
    have h1 := hκR x hx y hy y⁻¹ (E.inv_mem hy)
    rw [mul_inv_cancel, hκ1r x hx] at h1
    have h2 : κ x y⁻¹ = (κ x y)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    rw [h2]
    rcases hκ x hx y hy with h3 | h3 <;> rw [h3]
    · simp
    · exact hti
  have hPinvl : ∀ x ∈ E, ∀ y ∈ E, P x⁻¹ y = (P x y)⁻¹ := fun x hx y hy => by
    have h1 := hPL x hx x⁻¹ (E.inv_mem hx) y hy
    rw [mul_inv_cancel, hP1l y hy] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hPinvr : ∀ x ∈ E, ∀ y ∈ E, P x y⁻¹ = (P x y)⁻¹ := fun x hx y hy => by
    have h1 := hPR x hx y hy y⁻¹ (E.inv_mem hy)
    rw [mul_inv_cancel, hP1r x hx] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  intro x hx y hy
  rw [← hE] at hx hy
  refine Subgroup.closure_induction₂ (k := E2)
    (p := fun x y _ _ => P x y = iota ζ (κ x y)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    exact hbase x hx y hy
  · intro y hy
    have hyE : y ∈ E := hE ▸ hy
    rw [hP1l y hyE, hκ1l y hyE, iota_one]
  · intro x hx
    have hxE : x ∈ E := hE ▸ hx
    rw [hP1r x hxE, hκ1r x hxE, iota_one]
  · intro x y z hx hy hz hxz hyz
    have hxE : x ∈ E := hE ▸ hx
    have hyE : y ∈ E := hE ▸ hy
    have hzE : z ∈ E := hE ▸ hz
    rw [hPL x hxE y hyE z hzE, hxz, hyz, hκL x hxE y hyE z hzE,
      iota_mul hζ ht1 ht2 (hκ x hxE z hzE) (hκ y hyE z hzE)]
  · intro y z x hy hz hx hxy hxz
    have hxE : x ∈ E := hE ▸ hx
    have hyE : y ∈ E := hE ▸ hy
    have hzE : z ∈ E := hE ▸ hz
    rw [hPR x hxE y hyE z hzE, hxy, hxz, hκR x hxE y hyE z hzE,
      iota_mul hζ ht1 ht2 (hκ x hxE y hyE) (hκ x hxE z hzE)]
  · intro x y hx hy hxy
    have hxE : x ∈ E := hE ▸ hx
    have hyE : y ∈ E := hE ▸ hy
    rw [hPinvl x hxE y hyE, hxy, hκinvl x hxE y hyE, iota_inv_self hζ]
  · intro x y hx hy hxy
    have hxE : x ∈ E := hE ▸ hx
    have hyE : y ∈ E := hE ▸ hy
    rw [hPinvr x hxE y hyE, hxy, hκinvr x hxE y hyE, iota_inv_self hζ]

theorem exists_noncomm_inf_centralizer {G : Type*} [Group G] [Finite G] {L : Subgroup G} {t : G}
    {E : Subgroup G} (hW : WFacts L t E) {β : G} (hβL : β ∈ L) (hβt : β * t = t * β)
    (hβ3 : orderOf β = 3) :
    ∃ d₁ ∈ E ⊓ centralizer ({β} : Set G), ∃ d₂ ∈ E ⊓ centralizer ({β} : Set G),
      d₁ * d₂ ≠ d₂ * d₁ := by
  obtain ⟨β₁, hβ₁L, hβ₁t, hβ₁3, -, d₁, hd₁, d₂, hd₂, hne⟩ := hW.beta
  have hmem : ∀ y ∈ L, y * t = t * y → y ∈ L ⊓ centralizer ({t} : Set G) := fun y hy hyt =>
    ⟨hy, mem_centralizer_singleton_iff.2 hyt⟩
  obtain ⟨w, hwW, hw⟩ := exists_conj_of_order_three (W := L ⊓ centralizer ({t} : Set G))
    hW.card_cent (hmem β₁ hβ₁L hβ₁t) (hmem β hβL hβt) hβ₁3 hβ3
  have hwL : w ∈ L := hwW.1
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 hwW.2
  have hc : centralizer ({w * β₁ * w⁻¹} : Set G) = centralizer ({β} : Set G) := by
    rcases hw with hw | hw
    · rw [hw]
    · rw [hw]
      ext g
      simp only [mem_centralizer_singleton_iff]
      constructor
      · intro hg
        exact ((Commute.inv_right_iff).1 (show Commute g β⁻¹ from hg)).eq
      · intro hg
        exact (Commute.inv_right (show Commute g β from hg)).eq
  have himg := map_conj_inf_centralizer hW hwL hwt β₁
  rw [hc] at himg
  refine ⟨w * d₁ * w⁻¹, ?_, w * d₂ * w⁻¹, ?_, fun h1 => hne ?_⟩
  · rw [← himg]; exact ⟨d₁, hd₁, rfl⟩
  · rw [← himg]; exact ⟨d₂, hd₂, rfl⟩
  · have := congrArg (fun y => w⁻¹ * y * w) h1
    simpa [mul_assoc] using this

theorem iota_one_left {G : Type*} [Group G] (c : G) : iota (1 : G) c = 1 := by
  rcases iota_mem (1 : G) c with h1 | h1 <;> exact h1

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem Zg_cent_Q {α : G} (hα : AlphaSpec S z t α) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    a ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
      ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), a * q = q * a :=
  (h.center_QF hα).2 ((h.mem_Zg hα).1 ha)

theorem E_le_Qs {α : G} (hα : AlphaSpec S z t α) :
    E ≤ Fsub h hα ⊓ centralizer ({α} : Set G) := fun e he =>
  ⟨h.U_le_Fsub hα (mem_sup_right he),
    mem_centralizer_singleton_iff.2 (h.S_comm_E α hα.mem e he).symm⟩

theorem Zg_le_Qs {α : G} (hα : AlphaSpec S z t α) :
    (zpowers α ⊔ zpowers t : Subgroup G) ≤ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  fun _ ha => (h.Zg_cent_Q hα ha).1

theorem cmt_mem {α : G} (hα : AlphaSpec S z t α) {q r : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q * r * q⁻¹ * r⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  obtain ⟨c, hc, hqr⟩ := h.QF_comm hα hq hr
  have : q * r * q⁻¹ * r⁻¹ = c := by rw [hqr]; group
  rw [this]
  exact (h.mem_Zg hα).2 hc

theorem cmt_central {α : G} (hα : AlphaSpec S z t α) {q r s : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hs : s ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    s * (q * r * q⁻¹ * r⁻¹) = (q * r * q⁻¹ * r⁻¹) * s :=
  ((h.Zg_cent_Q hα (h.cmt_mem hα hq hr)).2 s hs).symm

theorem cmt_mul_left {α : G} (hα : AlphaSpec S z t α) {q q' r : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hq' : q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    (q * q') * r * (q * q')⁻¹ * r⁻¹ = (q * r * q⁻¹ * r⁻¹) * (q' * r * q'⁻¹ * r⁻¹) := by
  have hc := h.cmt_mem hα hq hr
  have hc' := h.cmt_mem hα hq' hr
  have hc'q := h.cmt_central hα hq' hr hq
  calc (q * q') * r * (q * q')⁻¹ * r⁻¹
      = q * (q' * r * q'⁻¹ * r⁻¹) * q⁻¹ * (q * r * q⁻¹ * r⁻¹) := by group
    _ = (q' * r * q'⁻¹ * r⁻¹) * (q * r * q⁻¹ * r⁻¹) := by rw [hc'q]; group
    _ = (q * r * q⁻¹ * r⁻¹) * (q' * r * q'⁻¹ * r⁻¹) := h.Zg_comm hα hc' hc

theorem cmt_mul_right {α : G} (hα : AlphaSpec S z t α) {q r r' : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr' : r' ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q * (r * r') * q⁻¹ * (r * r')⁻¹ = (q * r * q⁻¹ * r⁻¹) * (q * r' * q⁻¹ * r'⁻¹) := by
  have hc' := h.cmt_central hα hq hr' hr
  calc q * (r * r') * q⁻¹ * (r * r')⁻¹
      = (q * r * q⁻¹ * r⁻¹) * (r * (q * r' * q⁻¹ * r'⁻¹) * r⁻¹) := by group
    _ = (q * r * q⁻¹ * r⁻¹) * (q * r' * q⁻¹ * r'⁻¹) := by rw [hc']; group

theorem W_cent_Z {α : G} (hα : AlphaSpec S z t α) {w a : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : w * a = a * w := by
  have hZS : a ∈ S := by
    rcases (h.mem_Zg hα).1 ha with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h.t_mem_S
    · exact hα.mem
    · exact mul_mem hα.mem h.t_mem_S
  exact h.W_cent_S hw hZS

theorem W_norm_Qs {α : G} (hα : AlphaSpec S z t α) {w q : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    w * q * w⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  h.QF_normal hα (h.W_mem_M hw) hq

theorem chi_conj_W {α : G} (hα : AlphaSpec S z t α) {w q e : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) (he : e ∈ E) :
    (w * q * w⁻¹) * e * (w * q * w⁻¹)⁻¹ * e⁻¹ =
      q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹ := by
  have he' : w⁻¹ * e * w ∈ E := by
    have := h.W_norm_E (inv_mem hw) he
    simpa using this
  have hc := h.cmt_mem hα hq (h.E_le_Qs hα he')
  have hwc : w * (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) =
      (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) * w := h.W_cent_Z hα hw hc
  calc (w * q * w⁻¹) * e * (w * q * w⁻¹)⁻¹ * e⁻¹
      = w * (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) * w⁻¹ := by group
    _ = q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹ := by rw [hwc]; group

theorem chi_conj_z {q e : G} (he : e ∈ E) :
    (z * q * z⁻¹) * e * (z * q * z⁻¹)⁻¹ * e⁻¹ = z * (q * e * q⁻¹ * e⁻¹) * z⁻¹ := by
  have hze : z * e = e * z := h.S_comm_E z h.zS e he
  have h1 : z⁻¹ * e * z = e := by
    calc z⁻¹ * e * z = z⁻¹ * (e * z) := by group
      _ = z⁻¹ * (z * e) := by rw [hze]
      _ = e := by group
  have h3 : z⁻¹ * e⁻¹ * z = e⁻¹ := by
    calc z⁻¹ * e⁻¹ * z = (z⁻¹ * e * z)⁻¹ := by group
      _ = e⁻¹ := by rw [h1]
  calc (z * q * z⁻¹) * e * (z * q * z⁻¹)⁻¹ * e⁻¹
      = z * q * (z⁻¹ * e * z) * q⁻¹ * z⁻¹ * e⁻¹ := by group
    _ = z * q * e * q⁻¹ * z⁻¹ * e⁻¹ := by rw [h1]
    _ = z * (q * e * q⁻¹ * (z⁻¹ * e⁻¹ * z)) * z⁻¹ := by group
    _ = z * (q * e * q⁻¹ * e⁻¹) * z⁻¹ := by rw [h3]

theorem z_norm_Qs {α : G} (hα : AlphaSpec S z t α) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    z * q * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  h.QF_normal hα (le_normalizer (mem_sup_left h.zS)) hq

theorem z_conj_t : z * t * z⁻¹ = t := h.conj_t_of_M h.z_mem_M

theorem card_Zs {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(zpowers α ⊔ zpowers t : Subgroup G) = 4 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hset : ((zpowers α ⊔ zpowers t : Subgroup G) : Set G) = {1, t, α, α * t} := by
    ext u
    simpa using h.mem_Zg hα
  have hαt1 : α * t ≠ 1 := by
    intro h1
    apply hα.ne_t
    have := eq_inv_of_mul_eq_one_left h1
    rw [this, hti]
  have hαtt : α * t ≠ t := fun h1 => hα.ne_one (mul_eq_right.1 h1)
  have hαta : α * t ≠ α := fun h1 => h.t_ne (mul_eq_left.1 h1)
  have hc : Nat.card ↥(zpowers α ⊔ zpowers t : Subgroup G) =
      Set.ncard ({1, t, α, α * t} : Set G) := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have n1 : (1 : G) ∉ ({t, α, α * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h1 => h.t_ne h1.symm, fun h1 => hα.ne_one h1.symm, fun h1 => hαt1 h1.symm⟩
  have n2 : t ∉ ({α, α * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h1 => hα.ne_t h1.symm, fun h1 => hαtt h1.symm⟩
  have n3 : α ≠ α * t := fun h1 => hαta h1.symm
  rw [hc, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]

@[expose] noncomputable def cmtHom {α : G} (hα : AlphaSpec S z t α) {e : G}
    (he : e ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) →* ↥(zpowers α ⊔ zpowers t : Subgroup G) where
  toFun q := ⟨(q : G) * e * (q : G)⁻¹ * e⁻¹, h.cmt_mem hα q.2 he⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q q' := Subtype.ext (h.cmt_mul_left hα q.2 q'.2 he)

@[expose] noncomputable def Phi4 {α : G} (hα : AlphaSpec S z t α) {a b c d : G}
    (ha : a ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hb : b ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hc : c ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hd : d ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) →*
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) :=
  (h.cmtHom hα ha).prod ((h.cmtHom hα hb).prod ((h.cmtHom hα hc).prod (h.cmtHom hα hd)))

theorem Phi4_surj {α : G} (hα : AlphaSpec S z t α) {a b c d : G}
    (hE : Subgroup.closure ({a, b, c, d} : Set G) = E) (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) (c₁ c₂ c₃ c₄ : G) (h₁ : c₁ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₂ : c₂ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₃ : c₃ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₄ : c₄ ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    ∃ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), q * a * q⁻¹ * a⁻¹ = c₁ ∧
      q * b * q⁻¹ * b⁻¹ = c₂ ∧ q * c * q⁻¹ * c⁻¹ = c₃ ∧ q * d * q⁻¹ * d⁻¹ = c₄ := by
  set f := h.Phi4 hα (h.E_le_Qs hα ha) (h.E_le_Qs hα hb) (h.E_le_Qs hα hc)
    (h.E_le_Qs hα hd) with hf
  have hfq : ∀ q : ↥(Fsub h hα ⊓ centralizer ({α} : Set G)),
      f q = (⟨(q : G) * a * (q : G)⁻¹ * a⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα ha)⟩,
        ⟨(q : G) * b * (q : G)⁻¹ * b⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hb)⟩,
        ⟨(q : G) * c * (q : G)⁻¹ * c⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hc)⟩,
        ⟨(q : G) * d * (q : G)⁻¹ * d⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hd)⟩) := fun q => rfl
  have hker : f.ker = (zpowers α ⊔ zpowers t : Subgroup G).subgroupOf
      (Fsub h hα ⊓ centralizer ({α} : Set G)) := by
    ext q
    rw [MonoidHom.mem_ker, mem_subgroupOf, hfq]
    constructor
    · intro h0
      have h1 := congrArg (fun p => ((p.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h2 := congrArg (fun p => ((p.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one] at h1 h2 h3 h4
      have hcl : Subgroup.closure ({a, b, c, d} : Set G) ≤ centralizer ({(q : G)} : Set G) := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        rcases hg with rfl | rfl | rfl | rfl
        · exact (cmt_eq_one_iff.1 h1).symm
        · exact (cmt_eq_one_iff.1 h2).symm
        · exact (cmt_eq_one_iff.1 h3).symm
        · exact (cmt_eq_one_iff.1 h4).symm
      have hcent : ∀ e ∈ E, (q : G) * e = e * (q : G) := by
        intro e he
        rw [← hE] at he
        have := hcl he
        rw [mem_centralizer_singleton_iff] at this
        exact this.symm
      exact (h.mem_Zg hα).2 (h.QF_cent_E hα q.2 hcent)
    · intro hqZ
      have hc' : ∀ e ∈ E, (q : G) * e * (q : G)⁻¹ * e⁻¹ = 1 := fun e he =>
        cmt_eq_one_iff.2 (h.Zg_comm_E hα hqZ he)
      refine Prod.ext (Subtype.ext (hc' a ha)) (Prod.ext (Subtype.ext (hc' b hb))
        (Prod.ext (Subtype.ext (hc' c hc)) (Subtype.ext (hc' d hd))))
  have hcardker : Nat.card f.ker = 4 := by
    rw [hker, ← h.card_Zs hα]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.Zg_le_Qs hα)).toEquiv
  have hidx := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcardker, h.card_QF hα] at hidx
  have hrange : Nat.card f.range = 256 := by omega
  have htarget : Nat.card (↥(zpowers α ⊔ zpowers t : Subgroup G) ×
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G)) = 256 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_Zs hα]
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, htarget])
  have hmem : ((⟨c₁, h₁⟩, ⟨c₂, h₂⟩, ⟨c₃, h₃⟩, ⟨c₄, h₄⟩) : ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G)) ∈ f.range := by
    rw [htop]
    exact mem_top _
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 hmem
  rw [hfq] at hq
  have e1 := congrArg (fun p => ((p.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e2 := congrArg (fun p => ((p.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  exact ⟨q, q.2, e1, e2, e3, e4⟩

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
