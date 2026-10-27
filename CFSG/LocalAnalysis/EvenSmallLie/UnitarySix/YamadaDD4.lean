module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDAvg

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_commutator_left [Finite G] (H K : Subgroup G) :
    H ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem
  have hle : ⁅H, K⁆ ≤ (⁅H, K⁆).comap (MulAut.conj a).toMonoidHom := by
    rw [commutator_le]
    intro b hb c hc
    change a * ⁅b, c⁆ * a⁻¹ ∈ ⁅H, K⁆
    have e : a * ⁅b, c⁆ * a⁻¹ = ⁅a * b, c⁆ * ⁅a, c⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (commutator_mem_commutator (mul_mem ha hb) hc)
      (inv_mem (commutator_mem_commutator ha hc))
  exact fun y hy => hle hy

theorem le_normalizer_commutator_right [Finite G] (H K : Subgroup G) :
    K ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [commutator_comm]
  exact le_normalizer_commutator_left K H

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem withT_A₄_sq {w : G} (hw : w ∈ d.withT d.A₄) : w * w = 1 := by
  rcases (h.mem_withT_iff h.A₄_le_L).mp hw with hw | hw
  · exact h.A₄_sq hw
  · set b := w * d.t with hb
    have hc : b * d.t = d.t * b := h.comm_of_mem_L (h.A₄_le_L hw)
    have hwb : w = b * d.t := by rw [hb, mul_assoc, h.t_sq, mul_one]
    rw [hwb]
    calc b * d.t * (b * d.t) = b * (d.t * b) * d.t := by group
      _ = b * b * (d.t * d.t) := by rw [← hc]; group
      _ = 1 := by rw [h.A₄_sq hw, h.t_sq, one_mul]

theorem D_le_U₄ [Finite G] : d.D ≤ d.U₄ := le_inf D_le_X₄ h.D_le_cent_A₄

theorem D_sq [Finite G] {x : G} (hx : x ∈ d.D) : x * x ∈ d.A₄ := by
  have hxU := h.D_le_U₄ hx
  have hxx : x * x ∈ d.withT d.A₄ := by
    rw [← h.D_inf_H]
    refine mem_inf.mpr ⟨mul_mem hx hx, ?_⟩
    change x * x ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq, h.crossed_U₄_mul hxU hxU]
    exact h.A₄_sq (h.crossed_X₄ hxU.1)
  rcases (h.mem_withT_iff h.A₄_le_L).mp hxx with h1 | h1
  · exact h1
  · exfalso
    set a := x * x * d.t with ha
    obtain ⟨c, hc, hct⟩ := h.exists_D_conj h1
    have hxa : x * x = a * d.t := by rw [ha, mul_assoc _ d.t d.t, h.t_sq, mul_one]
    set y := c * x * c⁻¹ with hy
    have hyD : y ∈ d.D := mul_mem (mul_mem hc hx) (inv_mem hc)
    have hyy : y * y = d.t := by
      calc y * y = c * (x * x) * c⁻¹ := by rw [hy]; group
        _ = c * (c⁻¹ * d.t * c) * c⁻¹ := by rw [hxa, hct]
        _ = d.t := by group
    have hyt : y * d.t = d.t * y := by rw [← hyy]; group
    have hyH : y ∈ d.withT d.A₄ := by
      rw [← h.D_inf_H]
      exact mem_inf.mpr ⟨hyD, mem_centralizer_singleton_iff.mpr hyt⟩
    apply h.t_ne_one
    rw [← hyy]
    exact h.withT_A₄_sq hyH

theorem D_comm_mod [Finite G] {x y : G} (hx : x ∈ d.D) (hy : y ∈ d.D) :
    x * y * x⁻¹ * y⁻¹ ∈ d.A₄ := by
  have e : x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by
    group
  rw [e]
  refine mul_mem (mul_mem (h.D_sq (mul_mem hx hy)) ?_) (inv_mem (h.D_sq hy))
  have hy' : y⁻¹ ∈ d.X₄ := inv_mem (D_le_X₄ hy)
  have := (mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ hy') _).mp (inv_mem (h.D_sq hx))
  simpa using this

theorem A₄_le_D [Finite G] : d.A₄ ≤ d.D := (le_withT _).trans h.withT_A₄_le_D

theorem A₄_comm_D [Finite G] {a x : G} (ha : a ∈ d.A₄) (hx : x ∈ d.D) : a * x = x * a :=
  (mem_centralizer_iff.mp (h.D_le_cent_A₄ hx) a ha)

theorem Λ_le_NLA₃ : d.Λ ≤ d.NLA₃ := le_inf h.Λ_le_L h.Λ_le_NA₃

theorem comm_Λ_D_le_D [Finite G] : ⁅d.Λ, d.D⁆ ≤ d.D := by
  rw [commutator_le]
  intro l hl x hx
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp (h.X₄_le_normalizer_D (h.Λ_le_X₄ hl)) x).mp hx)
    (inv_mem hx)

theorem A₄_le_comm_Λ_D [Finite G] : d.A₄ ≤ ⁅d.Λ, d.D⁆ := by
  refine h.A₄_le_comm.trans ?_
  rw [commutator_comm]
  exact commutator_mono le_rfl h.A₄_le_D

theorem exists_comm_Λ_D_conj [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ y ∈ ⁅d.Λ, d.D⁆, y⁻¹ * d.t * y = a * d.t := by
  let R : Subgroup G :=
    { carrier := {b | ∃ y ∈ ⁅d.Λ, d.D⁆, y⁻¹ * d.t * y * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul (h.D_le_U₄ (h.comm_Λ_D_le_D hp))
          (h.D_le_U₄ (h.comm_Λ_D_le_D hq))⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv (h.D_le_U₄ (h.comm_Λ_D_le_D hp))⟩ }
  have hle : ⁅d.A₄, d.Λ⁆ ≤ R := by
    rw [commutator_le]
    intro b hb l hl
    obtain ⟨x, hx, hxt⟩ := h.exists_D_conj hb
    have hxU := h.D_le_U₄ hx
    have hq := (h.commutator_mem_Q₄ hxU hl).2
    have hxb : x⁻¹ * d.t * x * d.t = b := by rw [hxt, mul_assoc, h.t_sq, mul_one]
    rw [hxb] at hq
    refine ⟨⁅x, l⁆, ?_, hq⟩
    rw [commutator_comm]
    exact commutator_mem_commutator hx hl
  obtain ⟨y, hy, hyb⟩ := hle (h.A₄_le_comm ha)
  exact ⟨y, hy, by rw [← hyb, mul_assoc _ d.t d.t, h.t_sq, mul_one]⟩

theorem exists_mul_comm_Λ_D [Finite G] {x : G} (hx : x ∈ d.D) :
    ∃ w ∈ d.withT d.A₄, ∃ y ∈ ⁅d.Λ, d.D⁆, x = w * y := by
  obtain ⟨y, hy, hyt⟩ := h.exists_comm_Λ_D_conj (h.crossed_X₄ (D_le_X₄ hx))
  refine ⟨x * y⁻¹, ?_, y, hy, by group⟩
  rw [← h.D_inf_H]
  refine mem_inf.mpr ⟨mul_mem hx (inv_mem (h.comm_Λ_D_le_D hy)), ?_⟩
  change x * y⁻¹ ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff]
  have e1 : x⁻¹ * d.t * x = y⁻¹ * d.t * y := by rw [hyt, mul_assoc _ d.t d.t, h.t_sq, mul_one]
  calc x * y⁻¹ * d.t = x * (y⁻¹ * d.t * y) * y⁻¹ := by group
    _ = x * (x⁻¹ * d.t * x) * y⁻¹ := by rw [e1]
    _ = d.t * (x * y⁻¹) := by group

theorem conj_mem_A₄_iff [Finite G] {x w : G} (hx : x ∈ d.X₄) :
    x * w * x⁻¹ ∈ d.A₄ ↔ w ∈ d.A₄ := by
  constructor
  · intro hw
    have := (mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ hx) w).mpr hw
    exact this
  · intro hw
    exact (mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ hx) w).mp hw

theorem mul_mem_A₄_of_same [Finite G] {w w' : G} (hw : w ∈ d.withT d.A₄)
    (hw' : w' ∈ d.withT d.A₄) (hiff : w ∈ d.A₄ ↔ w' ∈ d.A₄) : w * w' ∈ d.A₄ := by
  by_cases h1 : w ∈ d.A₄
  · exact mul_mem h1 (hiff.mp h1)
  · have h2 : w' ∉ d.A₄ := fun h2 => h1 (hiff.mpr h2)
    have ha := ((h.mem_withT_iff h.A₄_le_L).mp hw).resolve_left h1
    have ha' := ((h.mem_withT_iff h.A₄_le_L).mp hw').resolve_left h2
    have hc : d.t * (w' * d.t) = (w' * d.t) * d.t := (h.comm_of_mem_L (h.A₄_le_L ha')).symm
    have e : w * w' = (w * d.t) * (w' * d.t) := by
      calc w * w' = (w * d.t) * (d.t * (w' * d.t)) * d.t⁻¹ := by
            rw [show (w * d.t) * (d.t * (w' * d.t)) * d.t⁻¹ =
              w * (d.t * d.t) * w' * (d.t * d.t⁻¹) by group, h.t_sq]; group
        _ = (w * d.t) * (w' * d.t) := by rw [hc]; group
    rw [e]
    exact mul_mem ha ha'

theorem conj_comm_mem_withT [Finite G] {σ x : G} (hσL : σ ∈ d.L)
    (hσA : σ ∈ centralizer (d.A₄ : Set G)) (hx : x ∈ d.D) :
    σ * x * σ⁻¹ * x⁻¹ ∈ d.withT d.A₄ := by
  have hσX : σ ∈ d.X₄ := CA₄_le_X₄ ⟨hσA, h.L_le_H hσL⟩
  have hσt : σ * d.t = d.t * σ := h.comm_of_mem_L hσL
  have hxD : σ * x * σ⁻¹ ∈ d.D := (mem_normalizer_iff.mp (h.X₄_le_normalizer_D hσX) x).mp hx
  rw [← h.D_inf_H]
  refine mem_inf.mpr ⟨mul_mem hxD (inv_mem hx), ?_⟩
  change σ * x * σ⁻¹ * x⁻¹ ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq,
    h.crossed_U₄_mul (h.D_le_U₄ hxD) (inv_mem (h.D_le_U₄ hx)), crossed_conj hσt,
    h.crossed_U₄_inv (h.D_le_U₄ hx)]
  have hc := h.crossed_X₄ (D_le_X₄ hx)
  rw [← mem_centralizer_iff.mp hσA _ hc]
  group

theorem Sig_comm_mod [Finite G] {σ x : G} (hσ : σ ∈ d.Sig) (hx : x ∈ d.D) :
    σ * x * σ⁻¹ * x⁻¹ ∈ d.A₄ := by
  have hσL := h.Sig_le_L hσ
  have hσA := h.Sig_le_cent_A₄ hσ
  have hσX : σ ∈ d.X₄ := CA₄_le_X₄ ⟨hσA, h.L_le_H hσL⟩
  have hσt : σ * d.t = d.t * σ := h.comm_of_mem_L hσL
  let K : Subgroup G :=
    { carrier := {y | y ∈ d.D ∧ σ * y * σ⁻¹ * y⁻¹ ∈ d.A₄}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro y z ⟨hy, hyc⟩ ⟨hz, hzc⟩
        refine ⟨mul_mem hy hz, ?_⟩
        have e : σ * (y * z) * σ⁻¹ * (y * z)⁻¹ =
            (σ * y * σ⁻¹ * y⁻¹) * (y * (σ * z * σ⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [e]
        exact mul_mem hyc ((h.conj_mem_A₄_iff (D_le_X₄ hy)).mpr hzc)
      inv_mem' := by
        rintro y ⟨hy, hyc⟩
        refine ⟨inv_mem hy, ?_⟩
        have e : σ * y⁻¹ * σ⁻¹ * y⁻¹⁻¹ = y⁻¹ * (σ * y * σ⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [e]
        have := (h.conj_mem_A₄_iff (inv_mem (D_le_X₄ hy))).mpr (inv_mem hyc)
        simpa using this }
  have hT : d.withT d.A₄ ≤ K := by
    intro w hw
    refine ⟨h.withT_A₄_le_D hw, ?_⟩
    have hσw : σ * w = w * σ := by
      have hσc : σ ∈ centralizer ((d.withT d.A₄ : Subgroup G) : Set G) := by
        refine mem_centralizer_sup hσA ?_
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
        exact Commute.zpow_left (show Commute d.t σ from hσt.symm) k
      exact (mem_centralizer_iff.mp hσc w hw).symm
    rw [hσw]
    simp
  have hC : ⁅d.Λ, d.D⁆ ≤ K := by
    rw [commutator_le]
    intro l hl y hy
    refine ⟨h.comm_Λ_D_le_D (commutator_mem_commutator hl hy), ?_⟩
    set k := σ * y * σ⁻¹ * y⁻¹ with hk
    have hkT : k ∈ d.withT d.A₄ := h.conj_comm_mem_withT hσL hσA hy
    have hlσ : l * σ = σ * l := h.Λ_comm_Sig l hl σ hσ
    set g := l * y * l⁻¹ * y⁻¹ with hg
    have hgD : g ∈ d.D := h.comm_Λ_D_le_D (commutator_mem_commutator hl hy)
    have e : σ * ⁅l, y⁆ * σ⁻¹ * ⁅l, y⁆⁻¹ = (l * k * l⁻¹) * (g * k⁻¹ * g⁻¹) := by
      rw [commutatorElement_def, hk, hg]
      calc σ * (l * y * l⁻¹ * y⁻¹) * σ⁻¹ * (l * y * l⁻¹ * y⁻¹)⁻¹
          = (σ * l) * y * (σ * l)⁻¹ * σ * y⁻¹ * σ⁻¹ * (l * y * l⁻¹ * y⁻¹)⁻¹ := by group
        _ = (l * σ) * y * (l * σ)⁻¹ * σ * y⁻¹ * σ⁻¹ * (l * y * l⁻¹ * y⁻¹)⁻¹ := by rw [hlσ]
        _ = _ := by group
    rw [e]
    have hlX := h.Λ_le_X₄ hl
    have hlk : l * k * l⁻¹ ∈ d.withT d.A₄ := (mem_normalizer_iff.mp hlX k).mp hkT
    have hgk : g * k⁻¹ * g⁻¹ ∈ d.withT d.A₄ :=
      (mem_normalizer_iff.mp (D_le_X₄ hgD) _).mp (inv_mem hkT)
    refine h.mul_mem_A₄_of_same hlk hgk ?_
    rw [h.conj_mem_A₄_iff hlX, h.conj_mem_A₄_iff (D_le_X₄ hgD)]
    exact ⟨fun h1 => inv_mem h1, fun h1 => by simpa using inv_mem h1⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := h.exists_mul_comm_Λ_D hx
  exact (mul_mem (hT hw) (hC hy)).2

theorem D₄_eq [Finite G] : d.D₄ = ⁅d.Λ, d.D⁆ := by
  refine le_antisymm ?_ (commutator_mono h.Λ_le_NLA₃ le_rfl)
  set D₄' := ⁅d.Λ, d.D⁆ with hD₄'
  have hND : ∀ x ∈ d.X₄, x ∈ normalizer (d.D : Set G) := fun x hx => h.X₄_le_normalizer_D hx
  have hΛ : d.Λ ≤ actTriv d.D D₄' := fun l hl =>
    ⟨hND l (h.Λ_le_X₄ hl), le_normalizer_commutator_left _ _ hl, fun x hx => by
      rw [← commutatorElement_def]; exact commutator_mem_commutator hl hx⟩
  have hSig : d.Sig ≤ actTriv d.D D₄' := by
    intro σ hσ
    have hσX : σ ∈ d.X₄ := CA₄_le_X₄ ⟨h.Sig_le_cent_A₄ hσ, h.L_le_H (h.Sig_le_L hσ)⟩
    refine ⟨hND σ hσX, ?_, fun x hx => h.A₄_le_comm_Λ_D (h.Sig_comm_mod hσ hx)⟩
    apply mem_normalizer_of_conj_mem
    have hle : D₄' ≤ D₄'.comap (MulAut.conj σ).toMonoidHom := by
      rw [hD₄', commutator_le]
      intro l hl x hx
      change σ * ⁅l, x⁆ * σ⁻¹ ∈ ⁅d.Λ, d.D⁆
      have hlσ : l * σ = σ * l := h.Λ_comm_Sig l hl σ hσ
      have e : σ * ⁅l, x⁆ * σ⁻¹ = ⁅l, σ * x * σ⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc σ * (l * x * l⁻¹ * x⁻¹) * σ⁻¹ = (σ * l) * x * (σ * l)⁻¹ * σ * x⁻¹ * σ⁻¹ := by
              group
          _ = (l * σ) * x * (l * σ)⁻¹ * σ * x⁻¹ * σ⁻¹ := by rw [hlσ]
          _ = l * (σ * x * σ⁻¹) * l⁻¹ * (σ * x * σ⁻¹)⁻¹ := by group
      rw [e]
      exact commutator_mem_commutator hl ((mem_normalizer_iff.mp (hND σ hσX) x).mp hx)
    exact fun y hy => hle hy
  have hA₃ : d.A₃ ≤ actTriv d.D D₄' := by
    intro a ha
    have hac : ∀ x ∈ d.D, a * x = x * a := fun x hx =>
      (mem_centralizer_iff.mp (h.D_le_cent_A₃ hx) a ha)
    refine ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => (hac x hx).symm),
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
        (hac x (h.comm_Λ_D_le_D hx)).symm), fun x hx => ?_⟩
    rw [hac x hx]
    simp
  have hN : d.NLA₃ ≤ actTriv d.D D₄' := h.NLA₃_le_gen.trans (sup_le (sup_le hΛ hSig) hA₃)
  rw [Data.D₄, commutator_le]
  intro n hn x hx
  rw [commutatorElement_def]
  exact (hN hn).2.2 x hx

theorem t_mem_D [Finite G] : d.t ∈ d.D := h.withT_A₄_le_D (t_mem_withT _)

theorem t_mem_X₄ [Finite G] : d.t ∈ d.X₄ := D_le_X₄ h.t_mem_D

theorem t_not_mem_D₄ [Finite G] : d.t ∉ d.D₄ := by
  classical
  have ha₀ := h.a₀_mem
  have hA₄ := h.A₄_le_closure
  set a₀ := d.a₀
  obtain ⟨d₀, hd₀, hd₀t⟩ := h.exists_D_conj ha₀
  have hX₁X : ∀ x ∈ d.X₁, x ∈ d.X₄ := fun x hx => h.Λ_le_X₄ (h.X₁_le_Λ hx)
  have : Fintype (d.X₁ : Set G) := Fintype.ofFinite _
  set S : Finset G := (d.X₁ : Set G).toFinset.image (fun x => x * d₀ * x⁻¹) with hS
  have hSmem : ∀ s, s ∈ S ↔ ∃ x ∈ d.X₁, x * d₀ * x⁻¹ = s := by
    intro s; simp [hS]
  have hSD : ∀ s ∈ S, s ∈ d.D := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := (hSmem s).mp hs
    exact (mem_normalizer_iff.mp (h.X₄_le_normalizer_D (hX₁X x hx)) d₀).mp hd₀
  set C := d.A₄ ⊔ closure (S : Set G) with hC
  have hCD : C ≤ d.D := sup_le h.A₄_le_D ((closure_le _).mpr fun s hs => hSD s hs)
  have hcardS : S.card ≤ 4 := by
    refine Finset.card_image_le.trans ?_
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact h.card_X₁.le
  have hcardC : Nat.card C ≤ 2 ^ 8 := by
    refine (card_sup_closure_le S (fun s hs => h.X₄_le_normalizer_A₄ (D_le_X₄ (hSD s hs)))
      (fun s hs => h.D_sq (hSD s hs))
      (fun s hs s' hs' => h.D_comm_mod (hSD s hs) (hSD s' hs'))).trans ?_
    rw [h.card_A₄]
    calc 2 ^ 4 * 2 ^ S.card ≤ 2 ^ 4 * 2 ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hcardS)
      _ = 2 ^ 8 := by norm_num
  have hcrC : ∀ a ∈ d.A₄, ∃ c ∈ C, c⁻¹ * d.t * c = a * d.t := by
    let R : Subgroup G :=
      { carrier := {b | ∃ c ∈ C, c⁻¹ * d.t * c * d.t = b}
        one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
        mul_mem' := by
          rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
          exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul (h.D_le_U₄ (hCD hp))
            (h.D_le_U₄ (hCD hq))⟩
        inv_mem' := by
          rintro _ ⟨p, hp, rfl⟩
          exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv (h.D_le_U₄ (hCD hp))⟩ }
    have horb : (fun x => x * a₀ * x⁻¹) '' (d.X₁ : Set G) ⊆ R := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x * d₀ * x⁻¹, mem_sup_right (subset_closure ((hSmem _).mpr ⟨x, hx, rfl⟩)), ?_⟩
      have hxt : x * d.t = d.t * x := h.comm_of_mem_L (h.Λ_le_L (h.X₁_le_Λ hx))
      rw [crossed_conj hxt, hd₀t, mul_assoc _ d.t d.t, h.t_sq, mul_one]
    intro a ha
    obtain ⟨c, hc, hca⟩ := (closure_le R |>.mpr horb) (hA₄ ha)
    exact ⟨c, hc, by rw [← hca, mul_assoc _ d.t d.t, h.t_sq, mul_one]⟩
  have htC : d.t ∉ C := by
    intro htC
    have hcardeq := card_eq_of_crossed_onto h.t_sq (fun c hc => h.D_le_cent_A₄ (hCD hc))
      (fun c hc => h.crossed_X₄ (D_le_X₄ (hCD hc))) (fun a ha => by
        obtain ⟨c, hc, hct⟩ := hcrC a ha
        exact ⟨c, hc, by rw [hct, mul_assoc, h.t_sq, mul_one]⟩)
    have hle : d.withT d.A₄ ≤ C ⊓ d.H :=
      le_inf (sup_le le_sup_left (zpowers_le.mpr htC)) (h.withT_le_H h.A₄_le_L)
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card_withT h.A₄_le_L, h.card_A₄] at h1
    change Nat.card C = Nat.card (C ⊓ d.H : Subgroup G) * Nat.card d.A₄ at hcardeq
    rw [h.card_A₄] at hcardeq
    have : 2 ^ 9 ≤ Nat.card C := by rw [hcardeq]; nlinarith
    omega
  have htnorm : ∀ c ∈ C, d.t * c * d.t ∈ C := by
    have hle : C ≤ C.comap (MulAut.conj d.t).toMonoidHom := by
      refine sup_le (fun a ha => ?_) ((closure_le _).mpr fun s hs => ?_)
      · change d.t * a * d.t⁻¹ ∈ C
        exact mem_sup_left ((mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ h.t_mem_X₄) a).mp ha)
      · change d.t * s * d.t⁻¹ ∈ C
        have e : d.t * s * d.t⁻¹ = s * (s⁻¹ * d.t * s * d.t) := by rw [h.t_inv]; group
        rw [e]
        exact mul_mem (mem_sup_right (subset_closure hs))
          (mem_sup_left (h.crossed_X₄ (D_le_X₄ (hSD s hs))))
    intro c hc
    have := hle hc
    simpa [h.t_inv] using this
  have hdich : ∀ x ∈ d.D, x ∉ C → d.t * x ∈ C := by
    intro x hx hxC
    obtain ⟨c, hc, hct⟩ := hcrC _ (h.crossed_X₄ (D_le_X₄ hx))
    have hxc : x * c⁻¹ ∈ d.withT d.A₄ := by
      rw [← h.D_inf_H]
      refine mem_inf.mpr ⟨mul_mem hx (inv_mem (hCD hc)), ?_⟩
      change x * c⁻¹ ∈ centralizer ({d.t} : Set G)
      rw [mem_centralizer_singleton_iff]
      have e1 : x⁻¹ * d.t * x = c⁻¹ * d.t * c := by
        rw [hct, mul_assoc _ d.t d.t, h.t_sq, mul_one]
      calc x * c⁻¹ * d.t = x * (c⁻¹ * d.t * c) * c⁻¹ := by group
        _ = x * (x⁻¹ * d.t * x) * c⁻¹ := by rw [e1]
        _ = d.t * (x * c⁻¹) := by group
    rcases (h.mem_withT_iff h.A₄_le_L).mp hxc with ha | ha
    · exact absurd (by simpa using mul_mem (mem_sup_left ha : x * c⁻¹ ∈ C) hc) hxC
    · have hat : (x * c⁻¹ * d.t) * d.t = d.t * (x * c⁻¹ * d.t) :=
        h.comm_of_mem_L (h.A₄_le_L ha)
      have e : d.t * x = (x * c⁻¹ * d.t) * c := by
        calc d.t * x = d.t * (x * c⁻¹ * d.t) * d.t * c := by
              rw [show d.t * (x * c⁻¹ * d.t) * d.t * c = d.t * x * c⁻¹ * (d.t * d.t) * c by group,
                h.t_sq]; group
          _ = (x * c⁻¹ * d.t) * (d.t * d.t) * c := by rw [← hat]; group
          _ = (x * c⁻¹ * d.t) * c := by rw [h.t_sq, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left ha) hc
  let f₀ : G → ZMod 2 := fun x => if x ∈ C then 0 else 1
  have hf₀ : ∀ x ∈ d.D, ∀ y ∈ d.D, f₀ (x * y) = f₀ x + f₀ y := by
    intro x hx y hy
    by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
    · simp [f₀, hxC, hyC, mul_mem hxC hyC]
    · have : x * y ∉ C := fun hm => hyC (by simpa using mul_mem (inv_mem hxC) hm)
      simp [f₀, hxC, hyC, this]
    · have : x * y ∉ C := fun hm => hxC (by simpa using mul_mem hm (inv_mem hyC))
      simp [f₀, hxC, hyC, this]
    · have hxt := hdich x hx hxC
      have hyt := hdich y hy hyC
      have : x * y ∈ C := by
        have e : x * y = (d.t * (d.t * x) * d.t) * (d.t * y) := by
          rw [show (d.t * (d.t * x) * d.t) * (d.t * y) = (d.t * d.t) * x * (d.t * d.t) * y by
            group, h.t_sq]; group
        rw [e]
        exact mul_mem (htnorm _ hxt) hyt
      simp only [f₀, hxC, hyC, this, ite_true, ite_false]
      decide
  have hf₀X₁ : ∀ p ∈ d.X₁, ∀ x ∈ d.D, f₀ (p⁻¹ * x * p) = f₀ x := by
    intro p hp x _
    have hpC : p⁻¹ ∈ normalizer (C : Set G) := by
      apply mem_normalizer_of_conj_mem
      have hle : C ≤ C.comap (MulAut.conj p⁻¹).toMonoidHom := by
        refine sup_le (fun a ha => ?_) ((closure_le _).mpr fun s hs => ?_)
        · change p⁻¹ * a * p⁻¹⁻¹ ∈ C
          exact mem_sup_left ((mem_normalizer_iff.mp
            (h.X₄_le_normalizer_A₄ (inv_mem (hX₁X p hp))) a).mp ha)
        · change p⁻¹ * s * p⁻¹⁻¹ ∈ C
          obtain ⟨x, hx, rfl⟩ := (hSmem s).mp hs
          refine mem_sup_right (subset_closure ((hSmem _).mpr ⟨p⁻¹ * x, mul_mem (inv_mem hp) hx,
            by group⟩))
      exact fun c hc => hle hc
    have hiff : p⁻¹ * x * p ∈ C ↔ x ∈ C := by
      have := mem_normalizer_iff.mp hpC x
      rw [inv_inv] at this
      exact this.symm
    simp only [f₀, hiff]
  have hΛD : d.Λ ≤ normalizer (d.D : Set G) := fun l hl => h.X₄_le_normalizer_D (h.Λ_le_X₄ hl)
  obtain ⟨F, hFadd, hFΛ, hFfix⟩ := exists_invariant_of_odd_index h.odd_index_X₁ hΛD f₀ hf₀ hf₀X₁
  have hFt : F d.t = 1 := by
    rw [hFfix d.t h.t_mem_D fun l hl => h.comm_of_mem_L (h.Λ_le_L hl)]
    simp [f₀, htC]
  have hF1 : F 1 = 0 := by
    have := hFadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    have h2 : F 1 + F 1 = 0 := by
      generalize F 1 = a; fin_cases a <;> rfl
    rw [← this] at h2
    exact h2
  let K : Subgroup G :=
    { carrier := {x | x ∈ d.D ∧ F x = 0}
      one_mem' := ⟨one_mem _, hF1⟩
      mul_mem' := by
        rintro x y ⟨hx, hFx⟩ ⟨hy, hFy⟩
        exact ⟨mul_mem hx hy, by rw [hFadd x hx y hy, hFx, hFy, add_zero]⟩
      inv_mem' := by
        rintro x ⟨hx, hFx⟩
        refine ⟨inv_mem hx, ?_⟩
        have := hFadd x⁻¹ (inv_mem hx) x hx
        rw [inv_mul_cancel, hF1, hFx, add_zero] at this
        exact this.symm }
  have hle : ⁅d.Λ, d.D⁆ ≤ K := by
    rw [commutator_le]
    intro l hl y hy
    have hly : l * y * l⁻¹ ∈ d.D := (mem_normalizer_iff.mp (hΛD hl) y).mp hy
    refine ⟨h.comm_Λ_D_le_D (commutator_mem_commutator hl hy), ?_⟩
    rw [commutatorElement_def, hFadd _ hly _ (inv_mem hy)]
    have h1 : F (l * y * l⁻¹) = F y := by
      have := hFΛ l⁻¹ (inv_mem hl) y hy
      rwa [inv_inv] at this
    rw [h1, ← hFadd y hy y⁻¹ (inv_mem hy), mul_inv_cancel, hF1]
  intro htD₄
  rw [h.D₄_eq] at htD₄
  have := (hle htD₄).2
  rw [hFt] at this
  exact one_ne_zero this


theorem D₄_le_D [Finite G] : d.D₄ ≤ d.D := by rw [h.D₄_eq]; exact h.comm_Λ_D_le_D

theorem A₄_le_D₄ [Finite G] : d.A₄ ≤ d.D₄ := by rw [h.D₄_eq]; exact h.A₄_le_comm_Λ_D

theorem Λ_le_normalizer_D₄ [Finite G] : d.Λ ≤ normalizer (d.D₄ : Set G) := by
  rw [h.D₄_eq]; exact le_normalizer_commutator_left _ _

theorem D₄_inf_H [Finite G] : d.D₄ ⊓ d.H = d.A₄ := by
  refine le_antisymm ?_ (le_inf h.A₄_le_D₄ (h.A₄_le_L.trans h.L_le_H))
  intro x hx
  obtain ⟨hxD, hxH⟩ := mem_inf.mp hx
  have hxT : x ∈ d.withT d.A₄ := by
    rw [← h.D_inf_H]; exact mem_inf.mpr ⟨h.D₄_le_D hxD, hxH⟩
  rcases (h.mem_withT_iff h.A₄_le_L).mp hxT with ha | ha
  · exact ha
  · exfalso
    apply h.t_not_mem_D₄
    have e : d.t = x⁻¹ * (x * d.t) := by group
    rw [e]
    exact mul_mem (inv_mem hxD) (h.A₄_le_D₄ ha)

theorem exists_D₄_conj [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ y ∈ d.D₄, y⁻¹ * d.t * y = a * d.t := by
  rw [h.D₄_eq]; exact h.exists_comm_Λ_D_conj ha

theorem card_D₄ [Finite G] : Nat.card d.D₄ = 2 ^ 8 := by
  rw [card_eq_of_crossed_onto h.t_sq (fun c hc => h.D_le_cent_A₄ (h.D₄_le_D hc))
    (fun c hc => h.crossed_X₄ (D_le_X₄ (h.D₄_le_D hc))) (fun a ha => ?_)]
  · change Nat.card (d.D₄ ⊓ d.H : Subgroup G) * _ = _
    rw [h.D₄_inf_H, h.card_A₄]
    norm_num
  · obtain ⟨c, hc, hct⟩ := h.exists_D₄_conj ha
    exact ⟨c, hc, by rw [hct, mul_assoc, h.t_sq, mul_one]⟩

theorem withT_D₄ [Finite G] : d.withT d.D₄ = d.D := by
  refine le_antisymm (sup_le h.D₄_le_D (zpowers_le.mpr h.t_mem_D)) fun x hx => ?_
  obtain ⟨w, hw, y, hy, rfl⟩ := h.exists_mul_comm_Λ_D hx
  rw [← h.D₄_eq] at hy
  refine mul_mem ?_ (le_withT _ hy)
  exact (sup_le_sup_right h.A₄_le_D₄ _) hw

theorem eq_mul_of_crossed_eq [Finite G] {x y : G} (hx : x ∈ d.D₄) (hy : y ∈ d.D₄)
    (hxy : x⁻¹ * d.t * x * d.t = y⁻¹ * d.t * y * d.t) : x⁻¹ * y ∈ d.A₄ := by
  have hk : x * y⁻¹ ∈ d.A₄ := by
    rw [← h.D₄_inf_H]
    refine mem_inf.mpr ⟨mul_mem hx (inv_mem hy), ?_⟩
    change x * y⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have e1 : x⁻¹ * d.t * x = y⁻¹ * d.t * y := mul_right_cancel hxy
    calc x * y⁻¹ * d.t = x * (y⁻¹ * d.t * y) * y⁻¹ := by group
      _ = x * (x⁻¹ * d.t * x) * y⁻¹ := by rw [e1]
      _ = d.t * (x * y⁻¹) := by group
  have e : x⁻¹ * y = x⁻¹ * (x * y⁻¹)⁻¹ * x := by group
  rw [e]
  have := (mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ (inv_mem (D_le_X₄ (h.D₄_le_D hx)))) _).mp
    (inv_mem hk)
  simpa using this

theorem comm_mul_left [Finite G] {x y z : G} (hx : x ∈ d.D) (hy : y ∈ d.D) (hz : z ∈ d.D) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz : ⁅y, z⁆ ∈ d.A₄ := by rw [commutatorElement_def]; exact h.D_comm_mod hy hz
  have hxz : ⁅x, z⁆ ∈ d.A₄ := by rw [commutatorElement_def]; exact h.D_comm_mod hx hz
  have e : ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, ← h.A₄_comm_D hyz hx, show ⁅y, z⁆ * x * x⁻¹ * ⁅x, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ by group,
    h.A₄_comm hyz hxz]

theorem comm_mul_right [Finite G] {x y z : G} (hx : x ∈ d.D) (hy : y ∈ d.D) (hz : z ∈ d.D) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hxz : ⁅x, z⁆ ∈ d.A₄ := by rw [commutatorElement_def]; exact h.D_comm_mod hx hz
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, ← h.A₄_comm_D hxz hy, show ⁅x, y⁆ * (⁅x, z⁆ * y * y⁻¹) = ⁅x, y⁆ * ⁅x, z⁆ by group]

theorem D₄_comm [Finite G] {x y : G} (hx : x ∈ d.D₄) (hy : y ∈ d.D₄) : x * y = y * x := by
  have hlift : ∀ a ∈ d.A₄, ∃ z ∈ d.D₄, z⁻¹ * d.t * z * d.t = a := fun a ha => by
    obtain ⟨z, hz, hzt⟩ := h.exists_D₄_conj ha
    exact ⟨z, hz, by rw [hzt, mul_assoc, h.t_sq, mul_one]⟩
  choose! s hsD hscr using hlift
  have hDD : ∀ {z}, z ∈ d.D₄ → z ∈ d.D := fun hz => h.D₄_le_D hz
  have hU : ∀ {z}, z ∈ d.D₄ → z ∈ d.U₄ := fun hz => h.D_le_U₄ (hDD hz)
  have hcr : ∀ {z}, z ∈ d.D₄ → z⁻¹ * d.t * z * d.t ∈ d.A₄ := fun hz =>
    h.crossed_X₄ (D_le_X₄ (hDD hz))
  have hcomm_eq : ∀ {z₁ z₂ w₁ w₂ : G}, z₁ ∈ d.D₄ → z₂ ∈ d.D₄ → w₁ ∈ d.D₄ → w₂ ∈ d.D₄ →
      z₁⁻¹ * d.t * z₁ * d.t = w₁⁻¹ * d.t * w₁ * d.t →
      z₂⁻¹ * d.t * z₂ * d.t = w₂⁻¹ * d.t * w₂ * d.t → ⁅z₁, z₂⁆ = ⁅w₁, w₂⁆ := by
    intro z₁ z₂ w₁ w₂ hz₁ hz₂ hw₁ hw₂ h1 h2
    have hk₁ := h.eq_mul_of_crossed_eq hw₁ hz₁ h1.symm
    have hk₂ := h.eq_mul_of_crossed_eq hw₂ hz₂ h2.symm
    obtain ⟨k₁, hk₁', rfl⟩ : ∃ k ∈ d.A₄, z₁ = w₁ * k := ⟨_, hk₁, by group⟩
    obtain ⟨k₂, hk₂', rfl⟩ : ∃ k ∈ d.A₄, z₂ = w₂ * k := ⟨_, hk₂, by group⟩
    have z1 : ∀ {a b : G}, a ∈ d.A₄ → b ∈ d.D → ⁅a, b⁆ = 1 := fun ha hb => by
      rw [commutatorElement_def, h.A₄_comm_D ha hb]; group
    have z2 : ∀ {a b : G}, a ∈ d.D → b ∈ d.A₄ → ⁅a, b⁆ = 1 := fun ha hb => by
      rw [commutatorElement_def, ← h.A₄_comm_D hb ha]; group
    rw [h.comm_mul_left (hDD hw₁) (h.A₄_le_D hk₁') (mul_mem (hDD hw₂) (h.A₄_le_D hk₂')),
      h.comm_mul_right (hDD hw₁) (hDD hw₂) (h.A₄_le_D hk₂'),
      z2 (hDD hw₁) hk₂', z1 hk₁' (mul_mem (hDD hw₂) (h.A₄_le_D hk₂'))]
    simp
  have hsU : ∀ {a}, a ∈ d.A₄ → s a ∈ d.U₄ := fun ha => hU (hsD _ ha)
  have hmulcr : ∀ {a b}, a ∈ d.A₄ → b ∈ d.A₄ →
      (s a * s b)⁻¹ * d.t * (s a * s b) * d.t = (s (a * b))⁻¹ * d.t * s (a * b) * d.t := by
    intro a b ha hb
    rw [h.crossed_U₄_mul (hsU ha) (hsU hb), hscr a ha, hscr b hb, hscr _ (mul_mem ha hb)]
  have c1 : ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ⁅s a, s b⁆ ∈ d.A₄ := by
    intro a ha b hb
    rw [commutatorElement_def]
    exact h.D_comm_mod (hDD (hsD a ha)) (hDD (hsD b hb))
  have c2 : ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, ⁅s (a * b), s c⁆ = ⁅s a, s c⁆ * ⁅s b, s c⁆ := by
    intro a ha b hb c hc
    rw [hcomm_eq (hsD _ (mul_mem ha hb)) (hsD c hc) (mul_mem (hsD a ha) (hsD b hb)) (hsD c hc)
      (hmulcr ha hb).symm rfl, h.comm_mul_left (hDD (hsD a ha)) (hDD (hsD b hb))
      (hDD (hsD c hc))]
  have c3 : ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, ⁅s a, s (b * c)⁆ = ⁅s a, s b⁆ * ⁅s a, s c⁆ := by
    intro a ha b hb c hc
    rw [hcomm_eq (hsD a ha) (hsD _ (mul_mem hb hc)) (hsD a ha) (mul_mem (hsD b hb) (hsD c hc))
      rfl (hmulcr hb hc).symm, h.comm_mul_right (hDD (hsD a ha)) (hDD (hsD b hb))
      (hDD (hsD c hc))]
  have c4 : ∀ a ∈ d.A₄, ⁅s a, s a⁆ = 1 := fun a _ => commutatorElement_self _
  have c5 : ∀ l ∈ d.Λ, ∀ a ∈ d.A₄, ∀ b ∈ d.A₄,
      ⁅s (l * a * l⁻¹), s (l * b * l⁻¹)⁆ = l * ⁅s a, s b⁆ * l⁻¹ := by
    intro l hl a ha b hb
    have hlt : l * d.t = d.t * l := h.comm_of_mem_L (h.Λ_le_L hl)
    have hlN := h.Λ_le_normalizer_D₄ hl
    have hla : l * a * l⁻¹ ∈ d.A₄ := (mem_normalizer_iff.mp (h.Λ_le_normalizer hl) a).mp ha
    have hlb : l * b * l⁻¹ ∈ d.A₄ := (mem_normalizer_iff.mp (h.Λ_le_normalizer hl) b).mp hb
    have hsa : l * s a * l⁻¹ ∈ d.D₄ := (mem_normalizer_iff.mp hlN _).mp (hsD a ha)
    have hsb : l * s b * l⁻¹ ∈ d.D₄ := (mem_normalizer_iff.mp hlN _).mp (hsD b hb)
    rw [hcomm_eq (hsD _ hla) (hsD _ hlb) hsa hsb
      (by rw [hscr _ hla, crossed_conj hlt, hscr a ha])
      (by rw [hscr _ hlb, crossed_conj hlt, hscr b hb])]
    simp only [commutatorElement_def]
    group
  have hβ := h.hom_wedge_A₄ (fun a b => ⁅s a, s b⁆) c1 c2 c3 c4 c5
  have hxy : ⁅x, y⁆ = 1 := by
    rw [hcomm_eq hx hy (hsD _ (hcr hx)) (hsD _ (hcr hy)) (hscr _ (hcr hx)).symm
      (hscr _ (hcr hy)).symm]
    exact hβ _ (hcr hx) _ (hcr hy)
  rw [commutatorElement_def] at hxy
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hxy, one_mul]

theorem D_le_normalizer_D₄ [Finite G] : d.D ≤ normalizer (d.D₄ : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro z hz
  have e : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
  rw [e]
  exact mul_mem (h.A₄_le_D₄ (h.D_comm_mod hx (h.D₄_le_D hz))) hz

theorem X₄_le_normalizer_D₄ [Finite G] : d.X₄ ≤ normalizer (d.D₄ : Set G) := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := h.X₄_factor hx
  have hyX : x * c⁻¹ ∈ d.X₄ := mul_mem hx (inv_mem (C₄_le_X₄ hc))
  set y := x * c⁻¹ with hy
  have hyL := h.H_le_normalizer_L hxc
  have hyA := h.X₄_le_normalizer_A₃ hyX
  have hyD := h.X₄_le_normalizer_D hyX
  have hyN : y ∈ normalizer (d.D₄ : Set G) := by
    apply mem_normalizer_of_conj_mem
    have hle : d.D₄ ≤ d.D₄.comap (MulAut.conj y).toMonoidHom := by
      rw [Data.D₄, commutator_le]
      intro n hn z hz
      change y * ⁅n, z⁆ * y⁻¹ ∈ ⁅d.NLA₃, d.D⁆
      have e : y * ⁅n, z⁆ * y⁻¹ = ⁅y * n * y⁻¹, y * z * y⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine commutator_mem_commutator (mem_inf.mpr ⟨(mem_normalizer_iff.mp hyL n).mp hn.1, ?_⟩)
        ((mem_normalizer_iff.mp hyD z).mp hz)
      exact mul_mem (mul_mem hyA hn.2) (inv_mem hyA)
    exact fun z hz => hle hz
  have hcN : c ∈ normalizer (d.D₄ : Set G) := by
    obtain ⟨a, ha, x', hx', rfl⟩ := h.exists_mul_A₃_D hc
    refine mul_mem ?_ (h.D_le_normalizer_D₄ hx')
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_)
    exact (mem_centralizer_iff.mp (h.D_le_cent_A₃ (h.D₄_le_D hz)) a ha).symm
  have e : x = y * c := by rw [hy]; group
  rw [e]
  exact mul_mem hyN hcN

theorem t_mem_normalizer_D₄ [Finite G] : d.t ∈ normalizer (d.D₄ : Set G) :=
  h.X₄_le_normalizer_D₄ h.t_mem_X₄

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
