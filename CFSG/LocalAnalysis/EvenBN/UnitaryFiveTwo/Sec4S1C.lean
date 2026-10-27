module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1B
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
import all CFSG.Fischer.F4

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.Open CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem a₂Coord_conj_e₂SU {a : SU52} :
    a₂Coord (mat (e₂SU * a * e₂SU⁻¹)) = fun i => F4.ω * a₂Coord (mat a) i := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [bar_apply] <;> decide
  have hlam : bar F4.ω * (F4.ω)⁻¹ = F4.ω := by
    simp only [bar_apply]
    decide
  have hg : mat e₂SU = Matrix.diagonal ![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] := rfl
  funext i
  fin_cases i
  · change mat (e₂SU * a * e₂SU⁻¹) 2 1 = F4.ω * mat a 2 1
    rw [mat_conj_diag hd hg]
    change bar F4.ω * mat a 2 1 * (F4.ω)⁻¹ = _
    calc bar F4.ω * mat a 2 1 * (F4.ω)⁻¹ = (bar F4.ω * (F4.ω)⁻¹) * mat a 2 1 := by ring
      _ = F4.ω * mat a 2 1 := by rw [hlam]
  · change mat (e₂SU * a * e₂SU⁻¹) 2 0 = F4.ω * mat a 2 0
    rw [mat_conj_diag hd hg]
    change bar F4.ω * mat a 2 0 * (F4.ω)⁻¹ = _
    calc bar F4.ω * mat a 2 0 * (F4.ω)⁻¹ = (bar F4.ω * (F4.ω)⁻¹) * mat a 2 0 := by ring
      _ = F4.ω * mat a 2 0 := by rw [hlam]

theorem exists_conj_e₂_mem_Fsub {α : SU52} (hα : α ∈ A₂sub) :
    ∃ β ∈ A₂sub, α⁻¹ * (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) ∈ Fsub := by
  have hβ := nfA₂_mem (fun i => F4.ω * a₂Coord (mat α) i)
  have hconj : e₂SU * nfA₂ (fun i => F4.ω * a₂Coord (mat α) i) * e₂SU⁻¹ ∈ A₂sub :=
    DiagSub_conj_mem_A₂sub (Esub_le_DiagSub (mem_sup_right (mem_zpowers _))) hβ
  refine ⟨_, hβ, ?_⟩
  have hinv : a₂Coord (mat (nfA₂ (fun i => F4.ω * a₂Coord (mat α) i))⁻¹) =
      -(fun i => F4.ω * a₂Coord (mat α) i) := by
    have := a₂Coord_mul (inv_mem hβ) hβ
    rw [inv_mul_cancel, mat_one, a₂Coord_one, a₂Coord_nfA₂] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  rw [inv_mul_mem_Fsub_iff_a₂Coord hα (mul_mem (inv_mem hβ) hconj),
    a₂Coord_mul (inv_mem hβ) hconj, a₂Coord_conj_e₂SU, a₂Coord_nfA₂, hinv]
  funext i
  have key : ∀ x : F4, x = -(F4.ω * x) + F4.ω * (F4.ω * x) := by decide
  exact key _

theorem crossed_alg {G : Type*} [Group G] {A E c₀ Q w' : G} (hQ : Q * (A * c₀) * w' = 1)
    (hE : E * c₀ = c₀ * E) (hK : c₀ * (A⁻¹ * E * A * E⁻¹) = (A⁻¹ * E * A * E⁻¹) * c₀) :
    Q * (E * (A * c₀) * E⁻¹) = w'⁻¹ * (A⁻¹ * E * A * E⁻¹) := by
  have hQ' : Q = w'⁻¹ * c₀⁻¹ * A⁻¹ := by
    have : Q = (A * c₀ * w')⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      rw [← hQ]
      group
    rw [this]
    group
  have hEc' : E * c₀ * E⁻¹ = c₀ := by rw [hE]; group
  rw [hQ']
  calc w'⁻¹ * c₀⁻¹ * A⁻¹ * (E * (A * c₀) * E⁻¹) =
      w'⁻¹ * c₀⁻¹ * (A⁻¹ * E * A * E⁻¹) * (E * c₀ * E⁻¹) := by group
    _ = w'⁻¹ * c₀⁻¹ * (A⁻¹ * E * A * E⁻¹) * c₀ := by rw [hEc']
    _ = w'⁻¹ * (c₀⁻¹ * ((A⁻¹ * E * A * E⁻¹) * c₀)) := by group
    _ = w'⁻¹ * (c₀⁻¹ * (c₀ * (A⁻¹ * E * A * E⁻¹))) := by rw [hK]
    _ = w'⁻¹ * (A⁻¹ * E * A * E⁻¹) := by group

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem e₂_mem_NHA₂ (h : d.Hyp) : d.e₂ ∈ normalizer (d.A₂ : Set G) ⊓ d.H :=
  ⟨h.normalizer_withT_F_le h.e₂_mem_normalizer, h.L_le_H (d.ι_mem _)⟩

theorem e₂_mem_XC₀ (h : d.Hyp) : d.e₂ ∈ d.XC₀ := h.NHA₂_le_XC₀ h.e₂_mem_NHA₂

theorem Y_comm_e₂ (h : d.Hyp) {y : G} (hy : y ∈ d.Y) : y * d.e₂ = d.e₂ * y :=
  mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (h.E₂_le_U (h.Y_eq_E₂ ▸ hy))).2

theorem Y_le_D₂ (h : d.Hyp) : d.Y ≤ d.D₂ := fun y hy =>
  mem_D₂_iff.2 ⟨h.Y_le_UD₀ hy, fun y' hy' => h.Y_comm hy' hy⟩

theorem D₀_le_D₂ (h : d.Hyp) : d.D₀ ≤ d.D₂ := fun x hx =>
  mem_D₂_iff.2 ⟨h.C₀_le_UD₀ (h.D₀_le_C₀ hx), fun y hy => Y_comm_D₀ hy hx⟩

theorem conj_mem_D₂ (h : d.Hyp) {g u : G} (hg : g ∈ d.XC₀) (hu : u ∈ d.D₂) :
    g * u * g⁻¹ ∈ d.D₂ := by
  obtain ⟨huU, huC⟩ := mem_D₂_iff.1 hu
  refine mem_D₂_iff.2 ⟨h.conj_mem_UD₀ hg huU, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ d.Y := by
    have := h.conj_mem_Y_of_mem_XC₀ (inv_mem hg) hy
    rwa [inv_inv] at this
  have e := huC _ hy'
  calc y * (g * u * g⁻¹) = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
    _ = g * u * g⁻¹ * y := by group

theorem commutator_e₂_mem_D₂ (h : d.Hyp) {u : G} (hu : u ∈ d.UD₀) :
    d.e₂ * u * d.e₂⁻¹ * u⁻¹ ∈ d.D₂ := by
  refine mem_D₂_iff.2 ⟨mul_mem (h.conj_mem_UD₀ h.e₂_mem_XC₀ hu) (inv_mem hu), fun y hy => ?_⟩
  have hc := CFSG.LocalAnalysis.EvenBN.Common.commutator_le_centralizer_of_forall_conj_mem
    (X := zpowers d.e₂) (Y := d.UD₀) (z := y) (fun u' hu' => by
      have hw : u'⁻¹ * y * u' ∈ d.Y := by
        have := h.conj_mem_Y_of_mem_XC₀ (inv_mem (UD₀_le_XC₀ hu')) hy
        rwa [inv_inv] at this
      refine mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute d.e₂ (u'⁻¹ * y * u') from
        (h.Y_comm_e₂ hw).symm) k).eq)
  have hmem := hc (commutator_mem_commutator (mem_zpowers d.e₂) hu)
  rw [commutatorElement_def] at hmem
  exact (mem_centralizer_singleton_iff.1 hmem).symm

theorem crossed_inv_mem_Y (h : d.Hyp) {u : G} (hu : u ∈ d.UD₀) :
    (u⁻¹ * d.t * u⁻¹⁻¹ * d.t) * (u * d.t * u⁻¹ * d.t) ∈ d.Y := by
  obtain ⟨w, hw, e⟩ := h.crossed_mul_mem_UD₀ hu (inv_mem (UD₀_le_XC₀ hu))
  have e1 : u * u⁻¹ * d.t * (u * u⁻¹)⁻¹ * d.t = 1 := by
    rw [mul_inv_cancel, one_mul, inv_one, mul_one, h.t_mul_t]
  rw [e1] at e
  have : (u⁻¹ * d.t * u⁻¹⁻¹ * d.t) * (u * d.t * u⁻¹ * d.t) = w⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact e.symm
  rw [this]
  exact inv_mem hw

theorem crossed_mem_Y_of_mem_D₀ (h : d.Hyp) {x : G} (hx : x ∈ d.D₀) :
    x * d.t * x⁻¹ * d.t ∈ d.Y := by
  have := h.crossed_t_mem_Y (inv_mem hx)
  rwa [show x * d.t * x⁻¹ * d.t = (x⁻¹)⁻¹ * (d.t * x⁻¹ * d.t) by group]

theorem exists_mem_D₂_conj_t (h : d.Hyp) {a : G} (ha : a ∈ d.A₂) :
    ∃ u ∈ d.D₂, (a * d.t)⁻¹ * (u * d.t * u⁻¹) ∈ d.Y := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, hβF⟩ := exists_conj_e₂_mem_Fsub hα
  obtain ⟨u, hu, hθ⟩ := h.exists_mem_UD₀_conj_t (a := d.ι β) ⟨β, hβ, rfl⟩
  rw [h.coset_mem_Y_iff] at hθ
  refine ⟨_, h.commutator_e₂_mem_D₂ hu, (h.coset_mem_Y_iff _ _).2 ?_⟩
  obtain ⟨w₂, hw₂, e₂eq⟩ := h.crossed_mul_mem_UD₀ (h.conj_mem_UD₀ h.e₂_mem_XC₀ hu)
    (inv_mem (UD₀_le_XC₀ hu))
  rw [crossed_conj_of_mem_H (d := d) (g := d.e₂) (Subgroup.mem_inf.1 h.e₂_mem_NHA₂).2] at e₂eq
  obtain ⟨w', hw', hQ⟩ : ∃ w' ∈ d.Y, (u⁻¹ * d.t * u⁻¹⁻¹ * d.t) * (u * d.t * u⁻¹ * d.t) * w' = 1 :=
    ⟨_, inv_mem (h.crossed_inv_mem_Y hu), mul_inv_cancel _⟩
  obtain ⟨c₀, hc₀, hPc⟩ : ∃ c₀ ∈ d.Y, u * d.t * u⁻¹ * d.t = d.ι β * c₀ := ⟨_, hθ, by group⟩
  rw [hPc] at hQ e₂eq
  have hαD : d.ι α ∈ d.D₀ := h.A₂_le_D₀ ⟨α, hα, rfl⟩
  have hconjβ : e₂SU * β * e₂SU⁻¹ ∈ A₂sub :=
    DiagSub_conj_mem_A₂sub (Esub_le_DiagSub (mem_sup_right (mem_zpowers _))) hβ
  have hKe : (d.ι β)⁻¹ * d.e₂ * d.ι β * d.e₂⁻¹ = d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) := by
    simp only [map_mul, map_inv, Data.e₂]
    group
  have hKD : (d.ι β)⁻¹ * d.e₂ * d.ι β * d.e₂⁻¹ ∈ d.D₀ := by
    rw [hKe]
    exact h.A₂_le_D₀ ⟨_, mul_mem (inv_mem hβ) hconjβ, rfl⟩
  have key := crossed_alg (A := d.ι β) (E := d.e₂) (c₀ := c₀)
    (Q := u⁻¹ * d.t * u⁻¹⁻¹ * d.t) (w' := w') hQ (h.Y_comm_e₂ hc₀).symm (Y_comm_D₀ hc₀ hKD)
  rw [e₂eq, key, hKe]
  have hcomm : (d.ι α)⁻¹ * w'⁻¹ = w'⁻¹ * (d.ι α)⁻¹ :=
    (Y_comm_D₀ (inv_mem hw') (inv_mem hαD)).symm
  have hfin : (d.ι α)⁻¹ * (w'⁻¹ * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) * w₂) =
      w'⁻¹ * ((d.ι α)⁻¹ * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹))) * w₂ := by
    calc (d.ι α)⁻¹ * (w'⁻¹ * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) * w₂) =
        ((d.ι α)⁻¹ * w'⁻¹) * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) * w₂ := by group
      _ = (w'⁻¹ * (d.ι α)⁻¹) * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹)) * w₂ := by rw [hcomm]
      _ = w'⁻¹ * ((d.ι α)⁻¹ * d.ι (β⁻¹ * (e₂SU * β * e₂SU⁻¹))) * w₂ := by group
  rw [hfin]
  exact mul_mem (mul_mem (inv_mem hw') (h.F_le_Y ⟨_, hβF, by rw [map_mul, map_inv]⟩)) hw₂

theorem exists_mem_D₂_crossed_inv_mul_mem_Y (h : d.Hyp) {x : G} (hx : x ∈ d.XC₀) :
    ∃ u ∈ d.D₂, (u⁻¹ * x) * d.t * (u⁻¹ * x)⁻¹ * d.t ∈ d.Y := by
  obtain ⟨a, ha, e, he, hθ⟩ := (h.mem_A₂E₂_iff).1 (h.D₀_eq ▸ h.crossed_mem_D₀ hx)
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  obtain ⟨u, hu, hua⟩ := h.exists_mem_D₂_conj_t ha
  rw [h.coset_mem_Y_iff] at hua
  have huU := (mem_D₂_iff.1 hu).1
  obtain ⟨w, hw, ex⟩ := h.crossed_mul_mem_UD₀ (inv_mem huU) hx
  obtain ⟨e₁, he₁, hR⟩ : ∃ e₁ ∈ d.Y, u * d.t * u⁻¹ * d.t = a * e₁ := ⟨_, hua, by group⟩
  obtain ⟨y₂, hy₂, hQR⟩ : ∃ y₂ ∈ d.Y,
      (u⁻¹ * d.t * u⁻¹⁻¹ * d.t) * (u * d.t * u⁻¹ * d.t) = y₂ :=
    ⟨_, h.crossed_inv_mem_Y huU, rfl⟩
  rw [hR] at hQR
  have hQ' : u⁻¹ * d.t * u⁻¹⁻¹ * d.t = y₂ * (a * e₁)⁻¹ := by
    rw [← hQR]
    group
  refine ⟨u, hu, ?_⟩
  rw [ex, hθ, hQ']
  have hc : a * (e * y₂ * e₁⁻¹) = (e * y₂ * e₁⁻¹) * a :=
    (Y_comm_D₀ (mul_mem (mul_mem heY hy₂) (inv_mem he₁)) (h.A₂_le_D₀ ha)).symm
  have e2 : a * e * (y₂ * (a * e₁)⁻¹) * w = (a * (e * y₂ * e₁⁻¹)) * a⁻¹ * w := by group
  rw [e2, hc, mul_assoc (e * y₂ * e₁⁻¹) a a⁻¹, mul_inv_cancel, mul_one]
  exact mul_mem (mul_mem (mul_mem heY hy₂) (inv_mem he₁)) hw

theorem XC₀_eq_sup (h : d.Hyp) : d.XC₀ = (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.D₂ := by
  refine le_antisymm (fun x hx => ?_) (sup_le h.NHA₂_le_XC₀ D₂_le_XC₀)
  obtain ⟨u, hu, hmem⟩ := h.exists_mem_D₂_crossed_inv_mul_mem_Y hx
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
    h.NHA₂_le_normalizer_Y
  obtain ⟨n, hn, y, hy, e'⟩ : u⁻¹ * x ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) *
      (d.Y : Set G) := by
    rw [← hset]
    exact h.mem_NHA₂Y_of_crossed_mem (mul_mem (inv_mem (D₂_le_XC₀ hu)) hx) hmem
  have hx' : x = n * ((n⁻¹ * u * n) * y) := by
    have e'' : n * y = u⁻¹ * x := e'
    have : x = u * (u⁻¹ * x) := by group
    rw [this, ← e'']
    group
  rw [hx']
  refine mul_mem (mem_sup_left hn) (mem_sup_right (mul_mem ?_ (h.Y_le_D₂ hy)))
  have := h.conj_mem_D₂ (inv_mem (h.NHA₂_le_XC₀ hn)) hu
  rwa [inv_inv] at this

theorem mem_D₀_of_mem_D₂_of_crossed_mem (h : d.Hyp) {u : G} (hu : u ∈ d.D₂)
    (hθ : u * d.t * u⁻¹ * d.t ∈ d.Y) : u ∈ d.D₀ :=
  h.mem_D₀_of_mem_C₀_of_comm (h.mem_C₀_of_mem_UD₀_of_crossed_mem (mem_D₂_iff.1 hu).1 hθ)
    fun y hy => ((mem_D₂_iff.1 hu).2 y hy).symm

theorem D₂_inf_H (h : d.Hyp) : d.D₂ ⊓ d.H = d.A₂ := by
  refine le_antisymm (fun u hu => ?_) (le_inf (fun a ha => h.D₀_le_D₂ (h.A₂_le_D₀ ha))
    fun a ha => h.L_le_H (d.pull_le_L _ ha))
  obtain ⟨huD, huH⟩ := Subgroup.mem_inf.1 hu
  have hut : u * d.t = d.t * u := mem_centralizer_singleton_iff.1 huH
  have hθ : u * d.t * u⁻¹ * d.t ∈ d.Y := by
    rw [hut, mul_inv_cancel_right, h.t_mul_t]
    exact one_mem _
  have huD₀ := h.mem_D₀_of_mem_D₂_of_crossed_mem huD hθ
  rw [h.D₀_eq] at huD₀
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 huD₀
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have haH : a ∈ d.H := h.L_le_H (d.pull_le_L _ ha)
  have heH : e ∈ d.H := by
    have := mul_mem (inv_mem haH) huH
    rwa [inv_mul_cancel_left] at this
  exact mul_mem ha (d.F_le_A₂ ((h.mem_F_iff_Y e).2 ⟨heY, mem_centralizer_singleton_iff.1 heH⟩))

theorem card_D₂ (h : d.Hyp) : Nat.card d.D₂ = 2 ^ 16 := by
  have h16 := h.relIndex_normalizer_withT_Y (K := d.D₂) D₂_le_XC₀
    (fun c => h.exists_mem_D₂_conj_t ⟨_, nfA₂_mem c, rfl⟩)
  have e1 := Subgroup.relIndex_mul_card (normalizer ((d.withT d.Y : Subgroup G) : Set G)) d.D₂
  have hinf : normalizer ((d.withT d.Y : Subgroup G) : Set G) ⊓ d.D₂ = d.D₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (fun x hx => ?_) h.D₀_le_D₂)
    · obtain ⟨hxN, hxD⟩ := Subgroup.mem_inf.1 hx
      exact h.mem_D₀_of_mem_D₂_of_crossed_mem hxD
        ((h.mem_normalizer_withT_Y_iff (D₂_le_XC₀ hxD)).1 hxN)
    · exact (h.mem_normalizer_withT_Y_iff (h.D₀_le_XC₀ hx)).2 (h.crossed_mem_Y_of_mem_D₀ hx)
  rw [h16, hinf, h.card_D₀] at e1
  rw [← e1]
  norm_num

theorem t_mem_XC₀ (h : d.Hyp) : d.t ∈ d.XC₀ := C₀_le_XC₀ h.t_mem_C₀

theorem sec4_15_2 (h : d.Hyp) :
    (∀ u ∈ d.D₂, u * d.t * u⁻¹ * d.t ∈ d.D₀) ∧
      (∀ a ∈ d.D₀, ∃ u ∈ d.D₂, ∃ w ∈ d.Y, u * d.t * u⁻¹ * d.t = a * w) ∧
      (∀ u ∈ d.D₂, (u * d.t * u⁻¹ * d.t ∈ d.Y ↔ u ∈ d.D₀)) ∧
      (∀ u₁ ∈ d.D₂, ∀ u₂ ∈ d.D₂, ∃ w ∈ d.Y, u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
        (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * w) ∧
      (∀ g ∈ normalizer (d.A₂ : Set G) ⊓ d.H, ∀ u : G,
        g * u * g⁻¹ * d.t * (g * u * g⁻¹)⁻¹ * d.t = g * (u * d.t * u⁻¹ * d.t) * g⁻¹) ∧
      (∀ g ∈ normalizer (d.A₂ : Set G) ⊓ d.H, ∀ u ∈ d.D₂, g * u * g⁻¹ ∈ d.D₂) ∧
      Nat.card d.D₂ = 2 ^ 16 := by
  refine ⟨fun u hu => h.crossed_mem_D₀ (D₂_le_XC₀ hu), fun a ha => ?_,
    fun u hu => ⟨fun hθ => h.mem_D₀_of_mem_D₂_of_crossed_mem hu hθ,
      fun hu₀ => h.crossed_mem_Y_of_mem_D₀ hu₀⟩,
    fun u₁ hu₁ u₂ hu₂ => h.crossed_mul_mem_UD₀ (mem_D₂_iff.1 hu₁).1 (D₂_le_XC₀ hu₂),
    fun g hg _ => crossed_conj_of_mem_H (Subgroup.mem_inf.1 hg).2,
    fun g hg u hu => h.conj_mem_D₂ (h.NHA₂_le_XC₀ hg) hu, h.card_D₂⟩
  rw [h.D₀_eq] at ha
  obtain ⟨a₁, ha₁, y₁, hy₁, rfl⟩ := (h.mem_A₂E₂_iff).1 ha
  have hy₁Y : y₁ ∈ d.Y := h.Y_eq_E₂ ▸ hy₁
  obtain ⟨u, hu, hθ⟩ := h.exists_mem_D₂_conj_t ha₁
  rw [h.coset_mem_Y_iff] at hθ
  refine ⟨u, hu, y₁⁻¹ * (a₁⁻¹ * (u * d.t * u⁻¹ * d.t)), mul_mem (inv_mem hy₁Y) hθ, ?_⟩
  have hc : a₁ * y₁⁻¹ = y₁⁻¹ * a₁ := (Y_comm_D₀ (inv_mem hy₁Y) (h.A₂_le_D₀ ha₁)).symm
  calc u * d.t * u⁻¹ * d.t = a₁ * (a₁⁻¹ * (u * d.t * u⁻¹ * d.t)) := by group
    _ = a₁ * y₁ * (y₁⁻¹ * (a₁⁻¹ * (u * d.t * u⁻¹ * d.t))) := by group

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
