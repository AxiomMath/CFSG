module

public import CFSG.GH74.GLS.Stage4.HexCV24
public import CFSG.GH74.GLS.Stage4.HexCData

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

structure MuData (D : HexData root F) (μ : G → F) : Prop where
  add : ∀ u ∈ root 3, ∀ v ∈ root 3, μ (u * v) = μ u + μ v
  r1 : ∀ s, ∀ u ∈ root 3, ⁅D.p1 s, u⁆ = D.p2 (s * μ u)
  r5 : ∀ t, ∀ u ∈ root 3, ⁅D.p5 t, u⁆ = D.p4 (t * μ u)

theorem map_zero_of_add' {f : F → G} (h : ∀ c d, f (c + d) = f c * f d) : f 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_left_cancel (a := f 0) (by rw [mul_one]; exact this)).symm

section Mu

variable (R : RGD2 6 H r₁ r₂ U root) (D : HexData root F)

include R in
theorem comm13_mem {s : F} {u : G} (hu : u ∈ root 3) : ⁅D.p1 s, u⁆ ∈ root 2 := by
  have h := rgd2_octComm R 1 3 (by norm_num) (by norm_num) (by norm_num) _ (D.p1_mem s) u hu
  refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 3, root k) ≤ root 2) h
  have := Set.mem_Ioo.1 hk
  have hk2 : k = 2 := by omega
  subst hk2; exact le_rfl

include R in
theorem comm53_mem {t : F} {u : G} (hu : u ∈ root 3) : ⁅D.p5 t, u⁆ ∈ root 4 := by
  have h := rgd2_octComm R 3 5 (by norm_num) (by norm_num) (by norm_num) u hu _ (D.p5_mem t)
  have h4 : ⁅u, D.p5 t⁆ ∈ root 4 := by
    refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (3 : ℤ) 5, root k) ≤ root 4) h
    have := Set.mem_Ioo.1 hk
    have hk2 : k = 4 := by omega
    subst hk2; exact le_rfl
  rw [← commutatorElement_inv]; exact (root 4).inv_mem h4

end Mu

section Mu2

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)

include R hC in
theorem exists_mu : ∃ μ : G → F, MuData D μ := by
  classical
  have hp10 : D.p1 0 = 1 := map_zero_of_add' D.p1_add
  have hp20 : D.p2 0 = 1 := map_zero_of_add' D.p2_add
  have hp40 : D.p4 0 = 1 := map_zero_of_add' D.p4_add
  have hp50 : D.p5 0 = 1 := map_zero_of_add' D.p5_add
  have hc1 : ∀ u ∈ root 3, ∃ e, D.p2 e = ⁅D.p1 1, u⁆ := fun u hu =>
    D.p2_surj _ (comm13_mem R D hu)
  let μ : G → F := fun u => if hu : u ∈ root 3 then Classical.choose (hc1 u hu) else 0
  have hμ : ∀ u (hu : u ∈ root 3), D.p2 (μ u) = ⁅D.p1 1, u⁆ := by
    intro u hu
    simp only [μ, hu, dite_true]
    exact Classical.choose_spec (hc1 u hu)
  have hTu : ∀ (t : Fˣ) u, u ∈ root 3 → D.T t * u * (D.T t)⁻¹ = u := by
    intro t u hu
    rw [mul_inv_eq_iff_eq_mul, D.T_eq]
    exact D.cent3 _ u hu
  have hr1 : ∀ s, ∀ u ∈ root 3, ⁅D.p1 s, u⁆ = D.p2 (s * μ u) := by
    intro s u hu
    by_cases hs : s = 0
    · subst hs
      simp [hp10, hp20]
    · obtain ⟨es, hes⟩ := D.p2_surj _ (comm13_mem R D (s := s) hu)
      have e1 : D.T (Units.mk0 s hs) * ⁅D.p1 s, u⁆ * (D.T (Units.mk0 s hs))⁻¹ = ⁅D.p1 1, u⁆ := by
        have : D.T (Units.mk0 s hs) * ⁅D.p1 s, u⁆ * (D.T (Units.mk0 s hs))⁻¹ =
            ⁅D.T (Units.mk0 s hs) * D.p1 s * (D.T (Units.mk0 s hs))⁻¹,
              D.T (Units.mk0 s hs) * u * (D.T (Units.mk0 s hs))⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this, D.w1, hTu _ u hu]
        have h1 : ((Units.mk0 s hs : Fˣ) : F)⁻¹ * s = 1 := by simp [hs]
        rw [h1]
      rw [← hes, D.w2] at e1
      have e2 : ((Units.mk0 s hs : Fˣ) : F)⁻¹ * es = μ u := D.p2_inj (e1.trans (hμ u hu).symm)
      have e3 : es = s * μ u := by
        rw [← e2]
        simp [hs]
      rw [← hes, e3]
  have hadd : ∀ u ∈ root 3, ∀ v ∈ root 3, μ (u * v) = μ u + μ v := by
    intro u hu v hv
    have huv : u * v ∈ root 3 := (root 3).mul_mem hu hv
    have h1 : ⁅D.p1 1, v⁆ ∈ root 2 := comm13_mem R D hv
    have hcm : u * ⁅D.p1 1, v⁆ = ⁅D.p1 1, v⁆ * u := (hC.c23 _ h1 u hu).symm
    have key : ⁅D.p1 1, u * v⁆ = ⁅D.p1 1, u⁆ * ⁅D.p1 1, v⁆ := by
      have : ⁅D.p1 1, u * v⁆ = ⁅D.p1 1, u⁆ * (u * ⁅D.p1 1, v⁆ * u⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this, hcm]; group
    rw [← hμ _ huv, ← hμ _ hu, ← hμ _ hv, ← D.p2_add] at key
    exact D.p2_inj key
  have hν : ∀ u ∈ root 3, ⁅D.p5 1, u⁆ = D.p4 (μ u) := by
    intro u hu
    obtain ⟨g, hg⟩ := D.p4_surj _ (comm53_mem R D (t := 1) hu)
    have hm := D.rel_short 1 1
    rw [one_mul] at hm
    have hw : ⁅D.p6 1, D.p1 1⁆ = D.p5 1 * ((D.p5 1)⁻¹ * ⁅D.p6 1, D.p1 1⁆) := by
      rw [mul_inv_cancel_left]
    set m := (D.p5 1)⁻¹ * ⁅D.p6 1, D.p1 1⁆ with hmdef
    have hgu : D.p6 1 * u * (D.p6 1)⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]; exact (hC.o36 u hu _ (D.p6_mem 1)).symm
    have lhs : D.p6 1 * ⁅D.p1 1, u⁆ * (D.p6 1)⁻¹ = D.p4 (1 * μ u) * D.p2 (μ u) := by
      rw [← hμ u hu, ← D.rel_long 1 (μ u)]
      simp only [commutatorElement_def]; group
    have hconj : D.p6 1 * D.p1 1 * (D.p6 1)⁻¹ = D.p5 1 * m * D.p1 1 := by
      have : D.p6 1 * D.p1 1 * (D.p6 1)⁻¹ = ⁅D.p6 1, D.p1 1⁆ * D.p1 1 := by
        simp only [commutatorElement_def]; group
      rw [this, hw]
    have hxy : ∀ y ∈ Vsub root 2 4, ⁅y, u⁆ = 1 := fun y hy =>
      commutatorElement_eq_one_iff_mul_comm.2
        (V24_comm R hC hy (root_le_Vsub (by norm_num) (by norm_num) hu))
    have hmN : m ∈ Vsub root 2 4 := hm
    have rhs : D.p6 1 * ⁅D.p1 1, u⁆ * (D.p6 1)⁻¹ = D.p2 (μ u) * ⁅D.p5 1, u⁆ := by
      have e : D.p6 1 * ⁅D.p1 1, u⁆ * (D.p6 1)⁻¹ = ⁅D.p6 1 * D.p1 1 * (D.p6 1)⁻¹, u⁆ := by
        calc D.p6 1 * ⁅D.p1 1, u⁆ * (D.p6 1)⁻¹ =
            ⁅D.p6 1 * D.p1 1 * (D.p6 1)⁻¹, D.p6 1 * u * (D.p6 1)⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = _ := by rw [hgu]
      rw [e, hconj]
      have hI : ⁅D.p5 1 * m * D.p1 1, u⁆ = (D.p5 1 * m) * ⁅D.p1 1, u⁆ * (D.p5 1 * m)⁻¹ *
          (D.p5 1 * ⁅m, u⁆ * (D.p5 1)⁻¹ * ⁅D.p5 1, u⁆) := by
        simp only [commutatorElement_def]; group
      rw [hI, hxy m hmN, ← hμ u hu]
      have hc25 : D.p5 1 * D.p2 (μ u) = D.p2 (μ u) * D.p5 1 :=
        (hC.o25 _ (D.p2_mem _) _ (D.p5_mem 1)).symm
      have hcm : m * D.p2 (μ u) = D.p2 (μ u) * m :=
        V24_comm R hC hmN (root_le_Vsub (by norm_num) (by norm_num) (D.p2_mem _))
      have h1 : m * D.p2 (μ u) * m⁻¹ = D.p2 (μ u) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hcm
      have h2 : D.p5 1 * D.p2 (μ u) * (D.p5 1)⁻¹ = D.p2 (μ u) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hc25
      have : D.p5 1 * m * D.p2 (μ u) * (D.p5 1 * m)⁻¹ = D.p2 (μ u) := by
        calc D.p5 1 * m * D.p2 (μ u) * (D.p5 1 * m)⁻¹ =
            D.p5 1 * (m * D.p2 (μ u) * m⁻¹) * (D.p5 1)⁻¹ := by group
          _ = D.p5 1 * D.p2 (μ u) * (D.p5 1)⁻¹ := by rw [h1]
          _ = D.p2 (μ u) := h2
      rw [this]; group
    rw [lhs] at rhs
    have hc24 : D.p4 (1 * μ u) * D.p2 (μ u) = D.p2 (μ u) * D.p4 (1 * μ u) :=
      (hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)).symm
    rw [hc24, ← hg] at rhs
    have h3 : D.p4 (1 * μ u) = D.p4 g := mul_left_cancel rhs
    have hg' : 1 * μ u = g := D.p4_inj h3
    rw [← hg, ← hg', one_mul]
  have hr5 : ∀ t, ∀ u ∈ root 3, ⁅D.p5 t, u⁆ = D.p4 (t * μ u) := by
    intro t u hu
    by_cases ht : t = 0
    · subst ht
      simp [hp50, hp40]
    · have e1 : D.T (Units.mk0 t ht) * ⁅D.p5 1, u⁆ * (D.T (Units.mk0 t ht))⁻¹ = ⁅D.p5 t, u⁆ := by
        have : D.T (Units.mk0 t ht) * ⁅D.p5 1, u⁆ * (D.T (Units.mk0 t ht))⁻¹ =
            ⁅D.T (Units.mk0 t ht) * D.p5 1 * (D.T (Units.mk0 t ht))⁻¹,
              D.T (Units.mk0 t ht) * u * (D.T (Units.mk0 t ht))⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this, D.w5, hTu _ u hu]
        simp
      rw [← e1, hν u hu, D.w4]
      simp
  exact ⟨μ, ⟨hadd, hr1, hr5⟩⟩

end Mu2

end CFSG.GH74.GLS.Stage4.Hex
