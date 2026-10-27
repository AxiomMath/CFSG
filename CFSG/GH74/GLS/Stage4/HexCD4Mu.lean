module

public import CFSG.GH74.GLS.Stage4.HexCD4Data
public import CFSG.GH74.GLS.Stage4.HexCMu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

structure PairData (D : HexData4 root F K) (β : K → G → F) : Prop where
  add_u : ∀ s, ∀ u ∈ root 3, ∀ v ∈ root 3, β s (u * v) = β s u + β s v
  add_s : ∀ s s', ∀ u ∈ root 3, β (s + s') u = β s u + β s' u
  lin : ∀ (c : F) s, ∀ u ∈ root 3, β (D.θ c * s) u = c * β s u
  r1 : ∀ s, ∀ u ∈ root 3, ⁅D.p1 s, u⁆ = D.p2 (β s u)
  r5 : ∀ t, ∀ u ∈ root 3, ⁅D.p5 t, u⁆ = D.p4 (β t u)

section Pair

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)

include R in
theorem comm13_mem4 {s : K} {u : G} (hu : u ∈ root 3) : ⁅D.p1 s, u⁆ ∈ root 2 := by
  have h := rgd2_octComm R 1 3 (by norm_num) (by norm_num) (by norm_num) _ (D.p1_mem s) u hu
  refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 3, root k) ≤ root 2) h
  have := Set.mem_Ioo.1 hk
  have hk2 : k = 2 := by omega
  subst hk2; exact le_rfl

include R in
theorem comm53_mem4 {t : K} {u : G} (hu : u ∈ root 3) : ⁅D.p5 t, u⁆ ∈ root 4 := by
  have h := rgd2_octComm R 3 5 (by norm_num) (by norm_num) (by norm_num) u hu _ (D.p5_mem t)
  have h4 : ⁅u, D.p5 t⁆ ∈ root 4 := by
    refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (3 : ℤ) 5, root k) ≤ root 4) h
    have := Set.mem_Ioo.1 hk
    have hk2 : k = 4 := by omega
    subst hk2; exact le_rfl
  rw [← commutatorElement_inv]; exact (root 4).inv_mem h4

include R hC in
theorem exists_pair : ∃ β : K → G → F, PairData D β := by
  classical
  have hp10 : D.p1 0 = 1 := map_zero_of_add' D.p1_add
  have hp20 : D.p2 0 = 1 := map_zero_of_add' D.p2_add
  have hc1 : ∀ s, ∀ u ∈ root 3, ∃ e, D.p2 e = ⁅D.p1 s, u⁆ := fun s u hu =>
    D.p2_surj _ (comm13_mem4 R D hu)
  let β : K → G → F := fun s u => if hu : u ∈ root 3 then Classical.choose (hc1 s u hu) else 0
  have hβ : ∀ s u (hu : u ∈ root 3), D.p2 (β s u) = ⁅D.p1 s, u⁆ := by
    intro s u hu
    simp only [β, hu, dite_true]
    exact Classical.choose_spec (hc1 s u hu)
  have hTu : ∀ (t : Fˣ) u, u ∈ root 3 → D.T t * u * (D.T t)⁻¹ = u := by
    intro t u hu
    rw [mul_inv_eq_iff_eq_mul, D.T_eq]
    exact D.cent3 _ u hu
  have hadd_u : ∀ s, ∀ u ∈ root 3, ∀ v ∈ root 3, β s (u * v) = β s u + β s v := by
    intro s u hu v hv
    have huv : u * v ∈ root 3 := (root 3).mul_mem hu hv
    have h1 : ⁅D.p1 s, v⁆ ∈ root 2 := comm13_mem4 R D hv
    have hcm : u * ⁅D.p1 s, v⁆ = ⁅D.p1 s, v⁆ * u := (hC.c23 _ h1 u hu).symm
    have key : ⁅D.p1 s, u * v⁆ = ⁅D.p1 s, u⁆ * ⁅D.p1 s, v⁆ := by
      have : ⁅D.p1 s, u * v⁆ = ⁅D.p1 s, u⁆ * (u * ⁅D.p1 s, v⁆ * u⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this, hcm]; group
    rw [← hβ _ _ huv, ← hβ _ _ hu, ← hβ _ _ hv, ← D.p2_add] at key
    exact D.p2_inj key
  have hadd_s : ∀ s s', ∀ u ∈ root 3, β (s + s') u = β s u + β s' u := by
    intro s s' u hu
    have h1 : ⁅D.p1 s', u⁆ ∈ root 2 := comm13_mem4 R D hu
    have hcm : D.p1 s * ⁅D.p1 s', u⁆ = ⁅D.p1 s', u⁆ * D.p1 s := hC.c12 _ (D.p1_mem s) _ h1
    have key : ⁅D.p1 (s + s'), u⁆ = ⁅D.p1 s', u⁆ * ⁅D.p1 s, u⁆ := by
      have : ⁅D.p1 (s + s'), u⁆ = D.p1 s * ⁅D.p1 s', u⁆ * (D.p1 s)⁻¹ * ⁅D.p1 s, u⁆ := by
        rw [D.p1_add]; simp only [commutatorElement_def]; group
      rw [this]
      have : D.p1 s * ⁅D.p1 s', u⁆ * (D.p1 s)⁻¹ = ⁅D.p1 s', u⁆ := by
        rw [mul_inv_eq_iff_eq_mul]; exact hcm
      rw [this]
    rw [← hβ _ _ hu, ← hβ _ _ hu, ← hβ _ _ hu, ← D.p2_add] at key
    exact (D.p2_inj key).trans (add_comm _ _)
  have hlin : ∀ (c : F) s, ∀ u ∈ root 3, β (D.θ c * s) u = c * β s u := by
    intro c s u hu
    by_cases hc : c = 0
    · subst hc
      simp only [map_zero, zero_mul]
      have h0 : D.p2 (β 0 u) = 1 := by
        rw [hβ _ _ hu, hp10]; simp [commutatorElement_def]
      have := D.p2_inj (h0.trans hp20.symm)
      exact this
    · set τ : Fˣ := Units.mk0 c⁻¹ (inv_ne_zero hc) with hτ
      have e1 : D.T τ * ⁅D.p1 s, u⁆ * (D.T τ)⁻¹ = ⁅D.p1 (D.θ c * s), u⁆ := by
        have : D.T τ * ⁅D.p1 s, u⁆ * (D.T τ)⁻¹ =
            ⁅D.T τ * D.p1 s * (D.T τ)⁻¹, D.T τ * u * (D.T τ)⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this, D.w1, hTu _ u hu]
        have h1 : (D.θ ((τ : Fˣ) : F))⁻¹ = D.θ c := by
          simp [hτ]
        rw [h1]
      rw [← hβ _ _ hu, D.w2, ← hβ _ _ hu] at e1
      have e2 := D.p2_inj e1
      rw [← e2]
      simp [hτ]
  have hν : ∀ t, ∀ u ∈ root 3, ⁅D.p5 t, u⁆ = D.p4 (β t u) := by
    intro t u hu
    obtain ⟨g, hg⟩ := D.p4_surj _ (comm53_mem4 R D (t := t) hu)
    have hm := D.rel_short 1 t
    rw [map_one, one_mul] at hm
    have hw : ⁅D.p6 1, D.p1 t⁆ = D.p5 t * ((D.p5 t)⁻¹ * ⁅D.p6 1, D.p1 t⁆) := by
      rw [mul_inv_cancel_left]
    set m := (D.p5 t)⁻¹ * ⁅D.p6 1, D.p1 t⁆ with hmdef
    have hgu : D.p6 1 * u * (D.p6 1)⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]; exact (hC.o36 u hu _ (D.p6_mem 1)).symm
    have lhs : D.p6 1 * ⁅D.p1 t, u⁆ * (D.p6 1)⁻¹ = D.p4 (1 * β t u) * D.p2 (β t u) := by
      rw [← hβ t u hu, ← D.rel_long 1 (β t u)]
      simp only [commutatorElement_def]; group
    have hconj : D.p6 1 * D.p1 t * (D.p6 1)⁻¹ = D.p5 t * m * D.p1 t := by
      have : D.p6 1 * D.p1 t * (D.p6 1)⁻¹ = ⁅D.p6 1, D.p1 t⁆ * D.p1 t := by
        simp only [commutatorElement_def]; group
      rw [this, hw]
    have hxy : ∀ y ∈ Vsub root 2 4, ⁅y, u⁆ = 1 := fun y hy =>
      commutatorElement_eq_one_iff_mul_comm.2
        (V24_comm R hC hy (root_le_Vsub (by norm_num) (by norm_num) hu))
    have hmN : m ∈ Vsub root 2 4 := hm
    have rhs : D.p6 1 * ⁅D.p1 t, u⁆ * (D.p6 1)⁻¹ = D.p2 (β t u) * ⁅D.p5 t, u⁆ := by
      have e : D.p6 1 * ⁅D.p1 t, u⁆ * (D.p6 1)⁻¹ = ⁅D.p6 1 * D.p1 t * (D.p6 1)⁻¹, u⁆ := by
        calc D.p6 1 * ⁅D.p1 t, u⁆ * (D.p6 1)⁻¹ =
            ⁅D.p6 1 * D.p1 t * (D.p6 1)⁻¹, D.p6 1 * u * (D.p6 1)⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = _ := by rw [hgu]
      rw [e, hconj]
      have hI : ⁅D.p5 t * m * D.p1 t, u⁆ = (D.p5 t * m) * ⁅D.p1 t, u⁆ * (D.p5 t * m)⁻¹ *
          (D.p5 t * ⁅m, u⁆ * (D.p5 t)⁻¹ * ⁅D.p5 t, u⁆) := by
        simp only [commutatorElement_def]; group
      rw [hI, hxy m hmN, ← hβ t u hu]
      have hc25 : D.p5 t * D.p2 (β t u) = D.p2 (β t u) * D.p5 t :=
        (hC.o25 _ (D.p2_mem _) _ (D.p5_mem t)).symm
      have hcm : m * D.p2 (β t u) = D.p2 (β t u) * m :=
        V24_comm R hC hmN (root_le_Vsub (by norm_num) (by norm_num) (D.p2_mem _))
      have h1 : m * D.p2 (β t u) * m⁻¹ = D.p2 (β t u) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hcm
      have h2 : D.p5 t * D.p2 (β t u) * (D.p5 t)⁻¹ = D.p2 (β t u) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hc25
      have : D.p5 t * m * D.p2 (β t u) * (D.p5 t * m)⁻¹ = D.p2 (β t u) := by
        calc D.p5 t * m * D.p2 (β t u) * (D.p5 t * m)⁻¹ =
            D.p5 t * (m * D.p2 (β t u) * m⁻¹) * (D.p5 t)⁻¹ := by group
          _ = D.p5 t * D.p2 (β t u) * (D.p5 t)⁻¹ := by rw [h1]
          _ = D.p2 (β t u) := h2
      rw [this]; group
    rw [lhs] at rhs
    have hc24 : D.p4 (1 * β t u) * D.p2 (β t u) = D.p2 (β t u) * D.p4 (1 * β t u) :=
      (hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)).symm
    rw [hc24, ← hg] at rhs
    have h3 : D.p4 (1 * β t u) = D.p4 g := mul_left_cancel rhs
    have hg' : 1 * β t u = g := D.p4_inj h3
    rw [← hg, ← hg', one_mul]
  exact ⟨β, ⟨hadd_u, hadd_s, hlin, fun s u hu => (hβ s u hu).symm, hν⟩⟩

end Pair

end CFSG.GH74.GLS.Stage4.Hex
