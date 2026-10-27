module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1Def
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSFour
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R3Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem C₀_le_XC₀ : d.C₀ ≤ d.XC₀ := d.C₀.le_normalizer

theorem D₀_le_XC₀ (h : d.Hyp) : d.D₀ ≤ d.XC₀ := h.D₀_le_C₀.trans C₀_le_XC₀

theorem Y_le_XC₀ (h : d.Hyp) : d.Y ≤ d.XC₀ := Y_le_D₀.trans h.D₀_le_XC₀

theorem NHA₂_le_XC₀ (h : d.Hyp) : normalizer (d.A₂ : Set G) ⊓ d.H ≤ d.XC₀ := fun g hg => by
  have hgF := h.NHA₂_le_normalizer_withT_F hg
  exact mem_normalizer_fintype fun x hx => conj_mem_oTwo hgF hx

theorem NHA₂Y_le_XC₀ (h : d.Hyp) : (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y ≤ d.XC₀ :=
  sup_le h.NHA₂_le_XC₀ h.Y_le_XC₀

theorem crossed_mem_D₀ (h : d.Hyp) {x : G} (hx : x ∈ d.XC₀) :
    x * d.t * x⁻¹ * d.t ∈ d.D₀ := by
  have hxt : x * d.t * x⁻¹ ∈ d.C₀ := (mem_normalizer_iff.1 hx _).1 h.t_mem_C₀
  rcases (h.mem_C₀_iff).1 hxt with hD | hD
  · exfalso
    apply h.t_not_mem_D₀
    have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_C₀_le_normalizer_D₀ hx)) _).1 hD
    rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
  · exact hD

theorem mem_normalizer_withT_Y_iff (h : d.Hyp) {x : G} (hx : x ∈ d.XC₀) :
    x ∈ normalizer ((d.withT d.Y : Subgroup G) : Set G) ↔ x * d.t * x⁻¹ * d.t ∈ d.Y := by
  constructor
  · intro hxN
    have hm : x * d.t * x⁻¹ ∈ d.withT d.Y := (mem_normalizer_iff.1 hxN _).1
      (mem_sup_right (mem_zpowers _))
    rcases (h.mem_withT_Y_iff).1 hm with hY | hY
    · exfalso
      apply h.t_not_mem_Y
      have := h.conj_mem_Y_of_mem_XC₀ (inv_mem hx) hY
      rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
    · exact hY
  · intro hθ
    have hxY : x ∈ normalizer (d.Y : Set G) := h.XC₀_le_normalizer_Y hx
    have hle : d.withT d.Y ≤ (d.withT d.Y).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => mem_sup_left ((mem_normalizer_iff.1 hxY y).1 hy)) ?_
      rw [zpowers_le]
      change x * d.t * x⁻¹ ∈ d.withT d.Y
      rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t) * d.t by
        rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
      exact mul_mem (mem_sup_left hθ) (mem_sup_right (mem_zpowers _))
    exact mem_normalizer_fintype fun k hk => hle hk

theorem mem_NHA₂Y_of_crossed_mem (h : d.Hyp) {x : G} (hx : x ∈ d.XC₀)
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.Y) : x ∈ (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y := by
  rw [← h.sec4_7]
  exact (h.mem_normalizer_withT_Y_iff hx).2 hθ

theorem crossed_mem_Y_of_mem_NHA₂Y (h : d.Hyp) {x : G}
    (hx : x ∈ (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y) : x * d.t * x⁻¹ * d.t ∈ d.Y := by
  have hx' : x ∈ d.XC₀ := h.NHA₂Y_le_XC₀ hx
  rw [← h.sec4_7] at hx
  exact (h.mem_normalizer_withT_Y_iff hx').1 hx

theorem mem_A₂_of_comm_F {s : G} (hs : s ∈ d.S) (hc : ∀ f ∈ d.F, s * f = f * s) :
    s ∈ d.A₂ := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  refine ⟨σ, mem_A₂sub_of_comm_Fsub hσ fun z hz => d.ι_injective ?_, rfl⟩
  rw [map_mul, map_mul]
  exact hc _ ⟨z, hz, rfl⟩

theorem D₀_eq_RY_inf_centralizer (h : d.Hyp) :
    d.D₀ = (d.R ⊔ d.Y) ⊓ centralizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) := by
  refine le_antisymm (le_inf ?_ fun x hx => mem_centralizer_iff.2 fun z hz => ?_) fun c hc => ?_
  · rw [h.sec4_6.2.2.1]
    exact sup_le (fun a ha => mem_sup_left (mem_sup_left (d.A₂_le_S ha))) le_sup_right
  · exact Y_comm_D₀ (h.FV₂_le_Y hz) hx
  obtain ⟨hcRY, hcC⟩ := Subgroup.mem_inf.1 hc
  have hset := coe_mul_of_left_le_normalizer_right d.R d.Y h.R_le_normalizer_Y
  obtain ⟨r, hr, y, hy, rfl⟩ : c ∈ (d.R : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact hcRY
  have hrC : ∀ z ∈ d.F ⊔ d.V₂, z * r = r * z := fun z hz => by
    have hz1 := mem_centralizer_iff.1 hcC z hz
    have hzy : z * y = y * z := h.Y_comm (h.FV₂_le_Y hz) hy
    have : z * r * y = r * z * y := by
      calc z * r * y = z * (r * y) := by group
        _ = (r * y) * z := hz1
        _ = r * (y * z) := by group
        _ = r * (z * y) := by rw [hzy]
        _ = r * z * y := by group
    exact mul_right_cancel this
  have hSt : ∀ s ∈ d.S, d.t * s * d.t ∈ d.S := fun s hs => by
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hs), mul_assoc, h.t_mul_t, mul_one]
    exact hs
  rcases (mem_sup_zpowers_iff h.t_mul_t hSt).1 hr with hrS | hrS
  · have hrA : r ∈ d.A₂ := mem_A₂_of_comm_F hrS fun f hf => (hrC f (mem_sup_left hf)).symm
    rw [h.sec4_6.2.2.1]
    exact mul_mem (mem_sup_left hrA) (mem_sup_right hy)
  · exfalso
    have hsA : r * d.t ∈ d.A₂ := mem_A₂_of_comm_F hrS fun f hf => by
      calc r * d.t * f = r * (d.t * f) := by group
        _ = r * (f * d.t) := by rw [← h.t_comm_F hf]
        _ = (r * f) * d.t := by group
        _ = (f * r) * d.t := by rw [hrC f (mem_sup_left hf)]
        _ = f * (r * d.t) := by group
    have hV : ¬ d.V₂ ≤ d.F := fun hle => by
      have := Subgroup.card_le_of_le hle
      rw [h.card_V₂, d.card_F] at this
      norm_num at this
    obtain ⟨v, hvV, hvF⟩ := IsConcreteLE.not_le_iff_exists.1 hV
    have hvY : v ∈ d.Y := h.V₂_le_Y hvV
    have ht1 : d.t * v * d.t ∈ d.F ⊔ d.V₂ := h.t_conj_mem_FV₂ v (mem_sup_right hvV)
    have e1 : r * (d.t * v * d.t) = (d.t * v * d.t) * r := (hrC _ ht1).symm
    have e2 : (r * d.t) * v = v * (r * d.t) := (Y_comm_D₀ hvY (h.A₂_le_D₀ hsA)).symm
    have e3 : r * (d.t * v * d.t) = v * r := by
      calc r * (d.t * v * d.t) = ((r * d.t) * v) * d.t := by group
        _ = (v * (r * d.t)) * d.t := by rw [e2]
        _ = v * r * (d.t * d.t) := by group
        _ = v * r := by rw [h.t_mul_t, mul_one]
    have e4 : d.t * v * d.t = v := mul_right_cancel (e1.symm.trans e3)
    exact hvF ((h.mem_F_iff_Y v).2 ⟨hvY, by
      calc v * d.t = (d.t * v * d.t) * d.t := by rw [e4]
        _ = d.t * v := by rw [mul_assoc (d.t * v), h.t_mul_t, mul_one]⟩)

theorem D₃_le_normalizer_D₀ (h : d.Hyp) : d.D₃ ≤ normalizer (d.D₀ : Set G) := fun u hu => by
  have huN := (Subgroup.mem_inf.1 hu).1
  have h1 := h.D₃_le_normalizer_RY hu
  have h2 := h.normalizer_R₂_le_normalizer_FV₂ huN
  rw [h.D₀_eq_RY_inf_centralizer]
  refine mem_normalizer_fintype fun c hc => ?_
  obtain ⟨hcRY, hcC⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 h1 c).1 hcRY, mem_centralizer_iff.2 fun z hz => ?_⟩
  have hz' : u⁻¹ * z * u ∈ d.F ⊔ d.V₂ := by
    have := (mem_normalizer_iff.1 (inv_mem h2) z).1 hz
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hcC _ hz'
  calc z * (u * c * u⁻¹) = u * ((u⁻¹ * z * u) * c) * u⁻¹ := by group
    _ = u * (c * (u⁻¹ * z * u)) * u⁻¹ := by rw [e]
    _ = u * c * u⁻¹ * z := by group

theorem D₃_le_XC₀ (h : d.Hyp) : d.D₃ ≤ d.XC₀ := fun u hu => by
  have huD := h.D₃_le_normalizer_D₀ hu
  have hθD : u * d.t * u⁻¹ * d.t ∈ d.D₀ := by
    have hX : (d.X₃ ⊔ d.X₄) ⊔ d.W ≤ d.D₀ := sup_le
      (X₃₄_le_XF.trans (XF_le_A₂.trans h.A₂_le_D₀)) (d.W_le_Y.trans Y_le_D₀)
    exact hX (h.crossed_mem_of_mem_D₃ hu)
  have hle : d.C₀ ≤ d.C₀.comap (MulAut.conj u).toMonoidHom := by
    rw [h.sec4_6.1]
    refine sup_le (fun x hx => mem_sup_left ((mem_normalizer_iff.1 huD x).1 hx)) ?_
    rw [zpowers_le]
    change u * d.t * u⁻¹ ∈ d.D₀ ⊔ zpowers d.t
    rw [show u * d.t * u⁻¹ = (u * d.t * u⁻¹ * d.t) * d.t by
      rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
    exact mul_mem (mem_sup_left hθD) (mem_sup_right (mem_zpowers _))
  exact mem_normalizer_fintype fun x hx => hle hx

theorem exists_mem_XC₀_crossed_not_mem_Y (h : d.Hyp) :
    ∃ x ∈ d.XC₀, x * d.t * x⁻¹ * d.t ∉ d.Y := by
  have hX₄ : d.ι (x₄SU 1 F4.ω one_omega_rel) ∈ d.X₄ := ⟨_, x₄SU_mem _ _ _, rfl⟩
  obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₃_conj_t (mem_sup_right hX₄)
  refine ⟨u, h.D₃_le_XC₀ hu, fun hY => ?_⟩
  rw [e] at hY
  have haY : d.ι (x₄SU 1 F4.ω one_omega_rel) ∈ d.Y := by
    have := mul_mem hY (inv_mem (d.W_le_Y hw))
    rwa [mul_inv_cancel_right] at this
  have haF : d.ι (x₄SU 1 F4.ω one_omega_rel) ∈ d.F := by
    rw [← h.A₂_inf_Y]
    exact Subgroup.mem_inf.2 ⟨⟨_, X₄sub_le_A₂sub (x₄SU_mem _ _ _), rfl⟩, haY⟩
  have h0 := (mem_Fsub_iff_a₂Coord (X₄sub_le_A₂sub (x₄SU_mem _ _ _))).1
    (d.ι_mem_pull_iff.1 haF)
  have h1 := congrFun h0 1
  simp [a₂Coord, mat_x₄SU, x₄Mat] at h1

theorem exists_mem_XC₀_conj_t (h : d.Hyp) {a : G} (ha : a ∈ d.A₂) :
    ∃ x ∈ d.XC₀, (a * d.t)⁻¹ * (x * d.t * x⁻¹) ∈ d.Y := by
  by_cases haF : a ∈ d.F
  · refine ⟨1, one_mem _, ?_⟩
    have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
    rw [hat, mul_inv_rev, one_mul, inv_one, mul_one, inv_mul_cancel_right]
    exact inv_mem (h.F_le_Y haF)
  obtain ⟨x₀, hx₀, hθ₀⟩ := h.exists_mem_XC₀_crossed_not_mem_Y
  obtain ⟨a₀, ha₀, y₀, hy₀, e₀⟩ := (h.mem_A₂E₂_iff).1 (h.D₀_eq ▸ h.crossed_mem_D₀ hx₀)
  have hy₀Y : y₀ ∈ d.Y := h.Y_eq_E₂ ▸ hy₀
  have ha₀F : a₀ ∉ d.F := fun hF => hθ₀ (by rw [e₀]; exact mul_mem (h.F_le_Y hF) hy₀Y)
  obtain ⟨α₀, hα₀, rfl⟩ := ha₀
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨n, hn, hnF⟩ := exists_K₂sub_conj_mem hα₀ (fun hF => ha₀F ⟨α₀, hF, rfl⟩) hα
    (fun hF => haF ⟨α, hF, rfl⟩)
  have hmN : d.ι n ∈ normalizer (d.A₂ : Set G) ⊓ d.H :=
    ⟨ι_mem_normalizer_pull (K₂sub_le_normalizer_A₂sub hn), h.L_le_H (d.ι_mem n)⟩
  have hmX : d.ι n ∈ d.XC₀ := h.NHA₂_le_XC₀ hmN
  refine ⟨d.ι n * x₀ * (d.ι n)⁻¹, mul_mem (mul_mem hmX hx₀) (inv_mem hmX), ?_⟩
  have hc := crossed_conj_of_mem_H (d := d) (g := d.ι n) (u := x₀) hmN.2
  have hP : d.ι n * x₀ * (d.ι n)⁻¹ * d.t * (d.ι n * x₀ * (d.ι n)⁻¹)⁻¹ =
      (d.ι n * (x₀ * d.t * x₀⁻¹ * d.t) * (d.ι n)⁻¹) * d.t := by
    rw [← hc, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  rw [hP]
  have hθ₀' : d.ι n * (x₀ * d.t * x₀⁻¹ * d.t) * (d.ι n)⁻¹ =
      d.ι (n * α₀ * n⁻¹) * (d.ι n * y₀ * (d.ι n)⁻¹) := by
    rw [e₀, map_mul, map_mul, map_inv]
    group
  have hmem : (d.ι α)⁻¹ * (d.ι n * (x₀ * d.t * x₀⁻¹ * d.t) * (d.ι n)⁻¹) ∈ d.Y := by
    rw [hθ₀', ← mul_assoc, ← map_inv, ← map_mul]
    exact mul_mem (h.F_le_Y ⟨_, hnF, rfl⟩) ((mem_normalizer_iff.1 (h.NHA₂_le_normalizer_Y hmN) y₀).1 hy₀Y)
  rw [show (d.ι α * d.t)⁻¹ * ((d.ι n * (x₀ * d.t * x₀⁻¹ * d.t) * (d.ι n)⁻¹) * d.t) =
    d.t * ((d.ι α)⁻¹ * (d.ι n * (x₀ * d.t * x₀⁻¹ * d.t) * (d.ι n)⁻¹)) * d.t by
      rw [mul_inv_rev, h.t_inv]
      group]
  exact h.t_conj_mem_Y hmem

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
