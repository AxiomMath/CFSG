module

public import CFSG.ClassicalInvolution.Phan.PhanS5D1Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

theorem bf_tauV_left (x y : Vec K) : bf M (tauV M x) y = M.τ (her M x y) := by
  have := bf_tauV M x (tauV M y)
  rwa [tauV_tauV] at this

theorem bf_tauV_right (x y : Vec K) : bf M x (tauV M y) = her M x y := rfl

theorem bf_zero_left (y : Vec K) : bf M 0 y = 0 := by
  simpa using bf_smul_left M 0 0 y

theorem bf_sum_left {ι : Type} [Fintype ι] (g : ι → K) (u : ι → Vec K) (z : Vec K) :
    bf M (∑ i, g i • u i) z = ∑ i, g i * bf M (u i) z := by
  simp only [← bfL_apply]
  rw [map_sum, LinearMap.sum_apply]
  simp

@[expose] def u8 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : Fin 8 → Vec K :=
  ![a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]

omit [Field K] in
theorem u8_0 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 0 = a₀ := rfl
omit [Field K] in
theorem u8_1 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 1 = a₁ := rfl
omit [Field K] in
theorem u8_2 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 2 = a₂ := rfl
omit [Field K] in
theorem u8_3 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 3 = a₃ := rfl
omit [Field K] in
theorem u8_4 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 4 = a₄ := rfl
omit [Field K] in
theorem u8_5 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 5 = a₅ := rfl
omit [Field K] in
theorem u8_6 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 6 = a₆ := rfl
omit [Field K] in
theorem u8_7 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Vec K) : u8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ 7 = a₇ := rfl

structure HypTriple (c₀ e f w : Vec K) : Prop where
  e_c : bf M e c₀ = 0
  e_sc : bf M e (tauV M c₀) = 0
  f_c : bf M f c₀ = 0
  f_sc : bf M f (tauV M c₀) = 0
  w_c : bf M w c₀ = 0
  w_sc : bf M w (tauV M c₀) = 0
  ee : bf M e e = 0
  ff : bf M f f = 0
  ef : bf M e f = 1
  we : bf M w e = 0
  wf : bf M w f = 0
  ww : bf M w w ≠ 0

variable {M}

theorem eight_linearIndependent {c₀ e f w : Vec K} (hc : IsFF M c₀) (H : HypTriple M c₀ e f w)
    (h₁ : her M e e = 0) (h₂ : her M e f = 0) (h₃ : her M e w = 0) (h₄ : her M f e = 0)
    (h₅ : her M f f = 0) (h₆ : her M f w = 0) (h₇ : her M w e = 0) (h₈ : her M w f = 0)
    (h₉ : her M w w = 0) :
    LinearIndependent K (u8 e f w (tauV M e) (tauV M f) (tauV M w) c₀ (tauV M c₀)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ z, ∑ i, g i * bf M (u8 e f w (tauV M e) (tauV M f) (tauV M w) c₀
      (tauV M c₀) i) z = 0 := fun z => by
    rw [← bf_sum_left, hg, bf_zero_left]
  have hec : her M e c₀ = 0 := H.e_sc
  have hfc : her M f c₀ = 0 := H.f_sc
  have hwc : her M w c₀ = 0 := H.w_sc
  have hce : her M c₀ e = 0 := by rw [her_conj_symm, hec, map_zero]
  have hcf : her M c₀ f = 0 := by rw [her_conj_symm, hfc, map_zero]
  have hcw : her M c₀ w = 0 := by rw [her_conj_symm, hwc, map_zero]
  have hfe : bf M f e = 1 := by rw [bf_comm, H.ef]
  have hcc : bf M c₀ c₀ = 0 := hc.1
  have hh : her M c₀ c₀ ≠ 0 := hc.2
  have ce : bf M c₀ e = 0 := by rw [bf_comm, H.e_c]
  have cf : bf M c₀ f = 0 := by rw [bf_comm, H.f_c]
  have cw : bf M c₀ w = 0 := by rw [bf_comm, H.w_c]
  have sce : bf M (tauV M c₀) e = 0 := by rw [bf_comm, H.e_sc]
  have scf : bf M (tauV M c₀) f = 0 := by rw [bf_comm, H.f_sc]
  have scw : bf M (tauV M c₀) w = 0 := by rw [bf_comm, H.w_sc]
  have hsc : bf M (tauV M c₀) c₀ = her M c₀ c₀ := by rw [bf_tauV_left, tau_her_self]
  have hcs : bf M c₀ (tauV M c₀) = her M c₀ c₀ := rfl
  have hscsc : bf M (tauV M c₀) (tauV M c₀) = 0 := by rw [bf_tauV, hcc, map_zero]
  have hwe' : bf M e w = 0 := by rw [bf_comm, H.we]
  have hwf' : bf M f w = 0 := by rw [bf_comm, H.wf]
  have k0 := key c₀
  have k1 := key (tauV M c₀)
  have k2 := key e
  have k3 := key f
  have k4 := key w
  have k5 := key (tauV M e)
  have k6 := key (tauV M f)
  have k7 := key (tauV M w)
  simp only [Fin.sum_univ_eight, u8_0, u8_1, u8_2, u8_3, u8_4, u8_5, u8_6,
    u8_7] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [bf_tauV] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [bf_tauV_left, bf_tauV_right, H.e_c, H.f_c, H.w_c, H.e_sc, H.f_sc, H.w_sc, H.ee, H.ff,
    H.ef, H.we, H.wf, hfe, hcc, hsc, ce, cf, cw, sce, scf, scw, hec, hfc, hwc, hce, hcf, hcw, h₁,
    h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, hwe', hwf', map_zero, map_one, mul_zero, zero_add, add_zero,
    mul_one] at k0 k1 k2 k3 k4 k5 k6 k7
  have g7 : g 7 = 0 := (mul_eq_zero.mp k0).resolve_right hh
  have g6 : g 6 = 0 := (mul_eq_zero.mp k1).resolve_right hh
  have g2 : g 2 = 0 := (mul_eq_zero.mp k4).resolve_right H.ww
  have g5 : g 5 = 0 := (mul_eq_zero.mp k7).resolve_right (tau_ne_zero M H.ww)
  intro i
  fin_cases i <;> simp_all

theorem exists_her_ne_zero {c₀ e f w : Vec K} (hc : IsFF M c₀) (H : HypTriple M c₀ e f w) :
    her M e e ≠ 0 ∨ her M e f ≠ 0 ∨ her M e w ≠ 0 ∨ her M f e ≠ 0 ∨ her M f f ≠ 0 ∨
      her M f w ≠ 0 ∨ her M w e ≠ 0 ∨ her M w f ≠ 0 ∨ her M w w ≠ 0 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hcon
  have hli := eight_linearIndependent hc H h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  have := hli.fintype_card_le_finrank
  rw [finrank_vec, Fintype.card_fin] at this
  omega

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
