module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem mem_Fsub_of_mul_self_eq_one {a : SU52} (ha : a ∈ A₂sub) (h2 : a * a = 1) :
    a ∈ Fsub := by
  rw [mem_A₂sub_iff_ρ] at ha
  rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  exact CFSG.RankThree.PartOne.U5K.Hyp.mem_Vsub_of_sq ha (by rw [← map_mul, h2, map_one])

@[expose] def Data.XC₀ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  normalizer (d.C₀ : Set G)

theorem Data.conj_mem_Y_aux {G : Type} [Group G] (d : Data G) {x : G}
    (hx : ∀ a ∈ d.D₀, a⁻¹ * x * a * x⁻¹ ∈ d.Y ∧ a⁻¹ * x⁻¹ * a * x ∈ d.Y) {w : G}
    (hw : w ∈ d.Y) : x * w * x⁻¹ ∈ d.Y ∧ x⁻¹ * w * x ∈ d.Y := by
  have hwD : w ∈ d.D₀ := (inf_le_right : d.Y ≤ d.D₀) hw
  obtain ⟨h1, h2⟩ := hx w hwD
  refine ⟨?_, ?_⟩
  · rw [show x * w * x⁻¹ = w * (w⁻¹ * x * w * x⁻¹) by group]
    exact mul_mem hw h1
  · rw [show x⁻¹ * w * x = w * (w⁻¹ * x⁻¹ * w * x) by group]
    exact mul_mem hw h2

@[expose] def Data.UD₀ {G : Type} [Group G] (d : Data G) : Subgroup G where
  carrier := {x | x ∈ d.XC₀ ∧ ∀ a ∈ d.D₀, a⁻¹ * x * a * x⁻¹ ∈ d.Y ∧ a⁻¹ * x⁻¹ * a * x ∈ d.Y}
  one_mem' := ⟨one_mem _, fun _ _ => ⟨by simp, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hxa⟩ ⟨hy, hya⟩
    refine ⟨mul_mem hx hy, fun a ha => ⟨?_, ?_⟩⟩
    · rw [show a⁻¹ * (x * y) * a * (x * y)⁻¹ =
        (a⁻¹ * x * a * x⁻¹) * (x * (a⁻¹ * y * a * y⁻¹) * x⁻¹) by group]
      exact mul_mem (hxa a ha).1 (d.conj_mem_Y_aux hxa (hya a ha).1).1
    · rw [show a⁻¹ * (x * y)⁻¹ * a * (x * y) =
        (a⁻¹ * y⁻¹ * a * y) * (y⁻¹ * (a⁻¹ * x⁻¹ * a * x) * y) by group]
      exact mul_mem (hya a ha).2 (d.conj_mem_Y_aux hya (hxa a ha).2).2
  inv_mem' := by
    rintro x ⟨hx, hxa⟩
    refine ⟨inv_mem hx, fun a ha => ⟨?_, ?_⟩⟩
    · rw [inv_inv]
      exact (hxa a ha).2
    · rw [inv_inv]
      exact (hxa a ha).1

@[expose] def Data.D₂ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.UD₀ ⊓ centralizer (d.Y : Set G)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem mem_UD₀_iff {x : G} : x ∈ d.UD₀ ↔
    x ∈ d.XC₀ ∧ ∀ a ∈ d.D₀, a⁻¹ * x * a * x⁻¹ ∈ d.Y ∧ a⁻¹ * x⁻¹ * a * x ∈ d.Y :=
  Iff.rfl

omit [Finite G] in
theorem UD₀_le_XC₀ : d.UD₀ ≤ d.XC₀ := fun _ hx => hx.1

omit [Finite G] in
theorem D₂_le_UD₀ : d.D₂ ≤ d.UD₀ := inf_le_left

omit [Finite G] in
theorem D₂_le_XC₀ : d.D₂ ≤ d.XC₀ := D₂_le_UD₀.trans UD₀_le_XC₀

omit [Finite G] in
theorem mem_D₂_iff {x : G} : x ∈ d.D₂ ↔ x ∈ d.UD₀ ∧ ∀ y ∈ d.Y, y * x = x * y := by
  rw [Data.D₂, Subgroup.mem_inf, mem_centralizer_iff]
  exact Iff.rfl

omit [Finite G] in
theorem Y_le_D₀ : d.Y ≤ d.D₀ := inf_le_right

omit [Finite G] in
theorem Y_comm_D₀ {y a : G} (hy : y ∈ d.Y) (ha : a ∈ d.D₀) : y * a = a * y :=
  (mem_centralizer_iff.1 ((inf_le_left : d.Y ≤ centralizer (d.D₀ : Set G)) hy) a ha).symm

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_Y_of_mul_self_eq_one (h : d.Hyp) {x : G} (hx : x ∈ d.D₀) (h2 : x * x = 1) :
    x ∈ d.Y := by
  rw [h.D₀_eq] at hx
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hx
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have hea : e * a = a * e := Y_comm_D₀ heY (h.A₂_le_D₀ ha)
  have haa : a * a = 1 := by
    have h1 : a * e * (a * e) = (a * a) * (e * e) := by
      rw [show a * e * (a * e) = a * (e * a) * e by group, hea]
      group
    rw [h1, h.Y_sq heY, mul_one] at h2
    exact h2
  obtain ⟨α, hα, rfl⟩ := ha
  have hα2 : α * α = 1 := d.ι_injective (by rw [map_mul, haa, map_one])
  have haF : d.ι α ∈ d.F := ⟨α, mem_Fsub_of_mul_self_eq_one hα hα2, rfl⟩
  exact mul_mem (h.F_le_Y haF) heY

theorem A₂_inf_Y (h : d.Hyp) : d.A₂ ⊓ d.Y = d.F := by
  refine le_antisymm (fun x hx => ?_) (le_inf d.F_le_A₂ h.F_le_Y)
  obtain ⟨hxA, hxY⟩ := Subgroup.mem_inf.1 hx
  exact (h.mem_F_iff_Y x).2 ⟨hxY, mem_centralizer_singleton_iff.1
    (h.L_le_H (d.pull_le_L _ hxA))⟩

theorem card_D₀ (h : d.Hyp) : Nat.card d.D₀ = 2 ^ 12 := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.A₂ d.Y
    fun a ha y hy => (Y_comm_D₀ hy (h.A₂_le_D₀ ha)).symm).1
  rw [h.A₂_inf_Y, d.card_A₂, h.sec4_6.2.2.2.2.1, d.card_F, ← h.sec4_6.2.2.1] at hc
  norm_num at hc
  omega

theorem card_C₀ (h : d.Hyp) : Nat.card d.C₀ = 2 ^ 13 := by
  rw [h.C₀_eq_X₀]
  exact h.card_X₀

theorem D₀_le_C₀ (h : d.Hyp) : d.D₀ ≤ d.C₀ := by
  rw [h.sec4_6.1]
  exact le_sup_left

theorem Y_le_C₀ (h : d.Hyp) : d.Y ≤ d.C₀ := Y_le_D₀.trans h.D₀_le_C₀

theorem t_mem_C₀ (h : d.Hyp) : d.t ∈ d.C₀ := by
  rw [h.sec4_6.1]
  exact mem_sup_right (mem_zpowers _)

theorem t_not_mem_D₀ (h : d.Hyp) : d.t ∉ d.D₀ := h.sec4_6.2.1

theorem t_conj_mem_D₀ (h : d.Hyp) {x : G} (hx : x ∈ d.D₀) : d.t * x * d.t ∈ d.D₀ := by
  have hn : d.t ∈ normalizer (d.D₀ : Set G) := by
    rw [h.D₀_eq]
    exact h.t_mem_normalizer_A₂E₂
  have := (mem_normalizer_iff.1 hn x).1 hx
  rwa [h.t_inv] at this

theorem mem_C₀_iff (h : d.Hyp) {x : G} : x ∈ d.C₀ ↔ x ∈ d.D₀ ∨ x * d.t ∈ d.D₀ := by
  rw [h.sec4_6.1]
  exact mem_sup_zpowers_iff h.t_mul_t (fun k hk => h.t_conj_mem_D₀ hk)

theorem relIndex_D₀_C₀ (h : d.Hyp) : d.D₀.relIndex d.C₀ = 2 := by
  have e := Subgroup.relIndex_mul_card d.D₀ d.C₀
  rw [inf_of_le_left h.D₀_le_C₀, h.card_D₀, h.card_C₀] at e
  norm_num at e
  omega

theorem mem_D₀_of_mem_C₀_of_comm (h : d.Hyp) {x : G} (hx : x ∈ d.C₀)
    (hc : ∀ y ∈ d.Y, x * y = y * x) : x ∈ d.D₀ := by
  rcases (h.mem_C₀_iff).1 hx with hx | hx
  · exact hx
  · exfalso
    have hYF : d.Y ≤ d.F := fun y hy => (h.mem_F_iff_Y y).2 ⟨hy, by
      have hδ := Y_comm_D₀ hy hx
      have h1 : x * (y * d.t) = x * (d.t * y) := by
        calc x * (y * d.t) = (x * y) * d.t := by group
          _ = (y * x) * d.t := by rw [hc y hy]
          _ = y * (x * d.t) := by group
          _ = (x * d.t) * y := hδ
          _ = x * (d.t * y) := by group
      exact mul_left_cancel h1⟩
    have := Subgroup.card_le_of_le hYF
    rw [h.sec4_6.2.2.2.2.1, d.card_F] at this
    norm_num at this

theorem conj_mem_Y_of_mem_XC₀ (h : d.Hyp) {n : G} (hn : n ∈ d.XC₀) {y : G} (hy : y ∈ d.Y) :
    n * y * n⁻¹ ∈ d.Y := by
  have hnC : n ∈ normalizer (d.C₀ : Set G) := hn
  set E : Subgroup G := d.Y.map (MulAut.conj n).toMonoidHom with hE
  have hEC : E ≤ d.C₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hnC y).1 (h.Y_le_C₀ hy)
  have hEsq : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change n * y * n⁻¹ * (n * y * n⁻¹) = 1
    rw [show n * y * n⁻¹ * (n * y * n⁻¹) = n * (y * y) * n⁻¹ by group, h.Y_sq hy, mul_one,
      mul_inv_cancel]
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' =>
    comm_of_mul_self_of_mul_self (hEsq e he) (hEsq e' he') (hEsq _ (mul_mem he he'))
  have hED : E ≤ d.D₀ := by
    by_contra hnot
    obtain ⟨e, heE, heD⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
    have het : e * d.t ∈ d.D₀ := ((h.mem_C₀_iff).1 (hEC heE)).resolve_left heD
    have hEF : d.D₀ ⊓ E ≤ d.F := by
      intro x hx
      obtain ⟨hxD, hxE⟩ := Subgroup.mem_inf.1 hx
      have hxY : x ∈ d.Y := h.mem_Y_of_mul_self_eq_one hxD (hEsq x hxE)
      refine (h.mem_F_iff_Y x).2 ⟨hxY, ?_⟩
      have hex := hEcomm e heE x hxE
      have hu : d.t * x * d.t ∈ d.Y := h.t_conj_mem_Y hxY
      set δ := e * d.t with hδ
      have hδt : e = δ * d.t := by rw [hδ, mul_assoc, h.t_mul_t, mul_one]
      have hxδ : x * δ = δ * x := Y_comm_D₀ hxY het
      have key : δ * (d.t * x * d.t) * d.t = δ * x * d.t := by
        calc δ * (d.t * x * d.t) * d.t = (δ * d.t) * x := by
              rw [show δ * (d.t * x * d.t) * d.t = δ * d.t * x * (d.t * d.t) by group,
                h.t_mul_t, mul_one]
          _ = e * x := by rw [← hδt]
          _ = x * e := hex
          _ = x * (δ * d.t) := by rw [← hδt]
          _ = (x * δ) * d.t := by group
          _ = δ * x * d.t := by rw [hxδ]
      have hu1 : d.t * x * d.t = x := mul_left_cancel (mul_right_cancel key)
      calc x * d.t = (d.t * x * d.t) * d.t := by rw [hu1]
        _ = d.t * x := by rw [mul_assoc (d.t * x), h.t_mul_t, mul_one]
    have hrel : d.D₀.relIndex E ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right hEC (by rw [h.relIndex_D₀_C₀]; norm_num)
      rwa [h.relIndex_D₀_C₀] at this
    have hcardE := Subgroup.relIndex_mul_card d.D₀ E
    have hcE : Nat.card E = 2 ^ 8 := by
      rw [hE, Subgroup.card_map_of_injective (MulAut.conj n).injective, h.sec4_6.2.2.2.2.1]
    have hle : Nat.card (d.D₀ ⊓ E : Subgroup G) ≤ 2 ^ 4 := by
      have := Subgroup.card_le_of_le hEF
      rwa [d.card_F] at this
    have h3 : Nat.card E ≤ 2 * 2 ^ 4 := by
      rw [← hcardE]
      exact Nat.mul_le_mul hrel hle
    rw [hcE] at h3
    norm_num at h3
  exact h.mem_Y_of_mul_self_eq_one (hED ⟨y, hy, rfl⟩) (hEsq _ ⟨y, hy, rfl⟩)

theorem XC₀_le_normalizer_Y (h : d.Hyp) : d.XC₀ ≤ normalizer (d.Y : Set G) := fun _ hn =>
  mem_normalizer_fintype fun _ hy => h.conj_mem_Y_of_mem_XC₀ hn hy

theorem normalizer_C₀_le_normalizer_D₀ (h : d.Hyp) :
    normalizer (d.C₀ : Set G) ≤ normalizer (d.D₀ : Set G) := fun n hn => by
  refine mem_normalizer_fintype fun x hx => ?_
  refine h.mem_D₀_of_mem_C₀_of_comm ((mem_normalizer_iff.1 hn x).1 (h.D₀_le_C₀ hx))
    fun y hy => ?_
  have hy' : n⁻¹ * y * n ∈ d.Y := by
    have := h.conj_mem_Y_of_mem_XC₀ (inv_mem (show n ∈ d.XC₀ from hn)) hy
    rwa [inv_inv] at this
  have e := Y_comm_D₀ hy' hx
  calc n * x * n⁻¹ * y = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by rw [← e]
    _ = y * (n * x * n⁻¹) := by group

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
