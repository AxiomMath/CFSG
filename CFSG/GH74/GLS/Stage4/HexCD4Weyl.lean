module

public import CFSG.GH74.GLS.Stage4.HexCD4Act
public import CFSG.GH74.GLS.Stage4.HexCWeylId
public import CFSG.GH74.GLS.Stage4.HexCWeyl

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

theorem weyl_coords4 (D : HexData4 root F K) {n : G} (hn : ActsPos 6 root n (fun q => 4 - q)) :
    (∃ f : K → K, ∀ d, n * D.p1 d * n⁻¹ = D.p5 (f d)) ∧
      (∃ f : K → K, ∀ d, n * D.p5 d * n⁻¹ = D.p1 (f d)) ∧
      (∃ f : F → F, ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f d)) ∧
      (∃ f : F → F, ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f d)) := by
  have h1 : ∀ d, ∃ c, D.p5 c = n * D.p1 d * n⁻¹ := fun d =>
    D.p5_surj _ (by simpa using weyl_mem hn (i := 1) (by norm_num) (by norm_num) (D.p1_mem d))
  have h5 : ∀ d, ∃ c, D.p1 c = n * D.p5 d * n⁻¹ := fun d =>
    D.p1_surj _ (by simpa using weyl_mem hn (i := 5) (by norm_num) (by norm_num) (D.p5_mem d))
  have h2 : ∀ d, ∃ c, D.p4 c = n * D.p2 d * n⁻¹ := fun d =>
    D.p4_surj _ (by simpa using weyl_mem hn (i := 2) (by norm_num) (by norm_num) (D.p2_mem d))
  have h4 : ∀ d, ∃ c, D.p2 c = n * D.p4 d * n⁻¹ := fun d =>
    D.p2_surj _ (by simpa using weyl_mem hn (i := 4) (by norm_num) (by norm_num) (D.p4_mem d))
  choose f1 hf1 using h1
  choose f5 hf5 using h5
  choose f2 hf2 using h2
  choose f4 hf4 using h4
  exact ⟨⟨f1, fun d => (hf1 d).symm⟩, ⟨f5, fun d => (hf5 d).symm⟩, ⟨f2, fun d => (hf2 d).symm⟩,
    ⟨f4, fun d => (hf4 d).symm⟩⟩

theorem weyl_sq4 (D : HexData4 root F K) {n : G} (hn : n = D.φ (sl2W F)) : n * n = D.T (-1) := by
  rw [hn, ← map_mul, sl2W_mul_self, D.T_eq]

theorem weyl_BR4 (D : HexData4 root F K) {n : G} (hn : n = D.φ (sl2W F)) :
    n * D.p6 1 * n⁻¹ = (D.p6 1)⁻¹ * n * (D.p6 1)⁻¹ := by
  have h := congrArg D.φ (sl2_BR (F := F))
  simpa [map_mul, map_inv, hn, D.p6_eq] using h

theorem sl2W_mul_sl2D (t : Fˣ) : sl2W F * sl2D t = sl2D t⁻¹ * sl2W F := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_f2_lin (D : HexData4 root F K) {n : G} (hn : n = D.φ (sl2W F)) {f₂ : F → F}
    (hf2 : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f₂ d)) (d : F) : f₂ d = d * f₂ 1 := by
  have hT : ∀ t : Fˣ, n * D.T t * n⁻¹ = D.T t⁻¹ := fun t => by
    rw [mul_inv_eq_iff_eq_mul, hn, D.T_eq, D.T_eq, ← map_mul, ← map_mul, sl2W_mul_sl2D]
  by_cases hd : d = 0
  · subst hd
    have h0 := hf2 0
    rw [map_zero_of_add' D.p2_add, mul_one, mul_inv_cancel] at h0
    have : D.p4 (f₂ 0) = D.p4 0 := by rw [← h0, map_zero_of_add' D.p4_add]
    rw [D.p4_inj this, zero_mul]
  · have ht : (Units.mk0 d⁻¹ (inv_ne_zero hd) : F)⁻¹ = d := by simp
    set t : Fˣ := Units.mk0 d⁻¹ (inv_ne_zero hd) with htdef
    have h1 : n * (D.T t * D.p2 1 * (D.T t)⁻¹) * n⁻¹ = D.T t⁻¹ * D.p4 (f₂ 1) * (D.T t⁻¹)⁻¹ := by
      rw [← hf2 1, ← hT t]
      group
    rw [D.w2 t 1, hf2, D.w4, ht, mul_one] at h1
    have h2 := D.p4_inj h1
    rw [h2]
    simp [t]

section Slot

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)

include hC in
theorem weyl_conj_Nel4 {n : G} {f₂ f₄ : F → F}
    (hf2 : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f₂ d)) (hf4 : ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f₄ d))
    (e f : F) {v : G} (hv : n * v * n⁻¹ ∈ root 3) :
    n * Nel4 D e v f * n⁻¹ = Nel4 D (f₄ f) (n * v * n⁻¹) (f₂ e) := by
  unfold Nel4
  have hA : D.p4 (f₂ e) * (n * v * n⁻¹) = (n * v * n⁻¹) * D.p4 (f₂ e) :=
    (hC.c34 _ hv _ (D.p4_mem _)).symm
  have hB : D.p4 (f₂ e) * D.p2 (f₄ f) = D.p2 (f₄ f) * D.p4 (f₂ e) :=
    (hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)).symm
  have hC' : (n * v * n⁻¹) * D.p2 (f₄ f) = D.p2 (f₄ f) * (n * v * n⁻¹) :=
    (hC.c23 _ (D.p2_mem _) _ hv).symm
  calc n * (D.p2 e * v * D.p4 f) * n⁻¹
      = (n * D.p2 e * n⁻¹) * (n * v * n⁻¹) * (n * D.p4 f * n⁻¹) := by group
    _ = D.p4 (f₂ e) * (n * v * n⁻¹) * D.p2 (f₄ f) := by rw [hf2, hf4]
    _ = D.p2 (f₄ f) * (n * v * n⁻¹) * D.p4 (f₂ e) := by
      rw [hA, mul_assoc, hB, ← mul_assoc, hC']

include R in
theorem weyl_cmp4 {VL VR : G} (hVL : VL ∈ Vsub root 2 4) (hVR : VR ∈ Vsub root 2 4)
    {a a' b b' : K} (hK : ⁅D.p1 a', D.p5 b'⁆ ∈ Vsub root 2 4)
    (h : VL * D.p1 a * D.p5 b = VR * D.p5 b' * D.p1 a') : a = a' ∧ b = b' := by
  obtain ⟨K', hK'⟩ : ∃ K', K' = ⁅D.p5 b', D.p1 a'⁆ := ⟨_, rfl⟩
  have hK'mem : K' ∈ Vsub root 2 4 := by
    rw [hK', ← commutatorElement_inv]; exact (Vsub root 2 4).inv_mem hK
  have hcomm : D.p5 b' * D.p1 a' = K' * (D.p1 a' * D.p5 b') := by
    rw [hK']; simp only [commutatorElement_def]; group
  rw [mul_assoc VR, hcomm] at h
  obtain ⟨P, hP⟩ : ∃ P, P = VL⁻¹ * (VR * K') := ⟨_, rfl⟩
  have hPmem : P ∈ Vsub root 2 4 := by
    rw [hP]
    exact (Vsub root 2 4).mul_mem ((Vsub root 2 4).inv_mem hVL)
      ((Vsub root 2 4).mul_mem hVR hK'mem)
  have h1 : D.p1 a * D.p5 b = P * (D.p1 a' * D.p5 b') := by
    calc D.p1 a * D.p5 b = VL⁻¹ * (VL * D.p1 a * D.p5 b) := by group
      _ = VL⁻¹ * (VR * (K' * (D.p1 a' * D.p5 b'))) := by rw [h]
      _ = P * (D.p1 a' * D.p5 b') := by rw [hP]; group
  have hx : (D.p1 a')⁻¹ * D.p1 a ∈ root 1 :=
    (root 1).mul_mem ((root 1).inv_mem (D.p1_mem _)) (D.p1_mem _)
  have hy : D.p5 b * (D.p5 b')⁻¹ ∈ root 5 :=
    (root 5).mul_mem (D.p5_mem _) ((root 5).inv_mem (D.p5_mem _))
  have hP' : (D.p1 a')⁻¹ * P * D.p1 a' ∈ Vsub root 2 4 := by
    have := root1_norm R ((root 1).inv_mem (D.p1_mem a')) hPmem
    simpa using this
  have h2 : ((D.p1 a')⁻¹ * D.p1 a) * (D.p5 b * (D.p5 b')⁻¹) ∈ Vsub root 2 4 := by
    have e : ((D.p1 a')⁻¹ * D.p1 a) * (D.p5 b * (D.p5 b')⁻¹) = (D.p1 a')⁻¹ * P * D.p1 a' := by
      calc _ = (D.p1 a')⁻¹ * (D.p1 a * D.p5 b) * (D.p5 b')⁻¹ := by group
        _ = (D.p1 a')⁻¹ * (P * (D.p1 a' * D.p5 b')) * (D.p5 b')⁻¹ := by rw [h1]
        _ = _ := by group
    rw [e]; exact hP'
  obtain ⟨hx1, hy1⟩ := rgd2_unique_15 R hx hy h2
  exact ⟨D.p1_inj (inv_mul_eq_one.1 hx1).symm, D.p5_inj (mul_inv_eq_one.1 hy1)⟩

variable {a2 a4 : K → K → F} {L : K → K → G} (hcd : CommData4 D a2 a4 L)
  {A2 A4 : F → K → F} {g3 : F → K → G} (had : ActData4 D A2 A4 g3)
  {n : G} (hnφ : n = D.φ (sl2W F)) (hnact : ActsPos 6 root n (fun q => 4 - q))
  {f₁ f₅ : K → K} {f₂ f₄ : F → F} (hf1 : ∀ d, n * D.p1 d * n⁻¹ = D.p5 (f₁ d))
  (hf5 : ∀ d, n * D.p5 d * n⁻¹ = D.p1 (f₅ d)) (hf2 : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f₂ d))
  (hf4 : ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f₄ d))

include R hC hcd had hnφ hnact hf1 hf5 hf2 hf4 in
theorem weyl_slot4 (s : K) : f₂ (A2 1 s) + a4 (-s) s = A4 (-1) (-s) := by
  have hu : (D.p6 1)⁻¹ = D.p6 (-1) := by
    have h0 : D.p6 0 = 1 := map_zero_of_add' D.p6_add
    have := D.p6_add 1 (-1)
    rw [add_neg_cancel, h0] at this
    exact inv_eq_of_mul_eq_one_right this.symm
  have hz : n * D.p5 (f₁ s) * n⁻¹ = D.p1 (-s) := by
    rw [← hf1 s]
    have e : n * (n * D.p1 s * n⁻¹) * n⁻¹ = (n * n) * D.p1 s * (n * n)⁻¹ := by group
    rw [e, weyl_sq4 D hnφ, D.w1 (-1) s]
    simp
  have hy : D.p6 1 * D.p5 (f₁ s) = D.p5 (f₁ s) * D.p6 1 :=
    (hC.c56 _ (D.p5_mem _) _ (D.p6_mem 1)).symm
  have hid := weyl_aux (weyl_BR4 D hnφ) (hf1 s) hy hz
  have hv : n * g3 1 s * n⁻¹ ∈ root 3 := by
    simpa using weyl_mem hnact (i := 3) (by norm_num) (by norm_num) (had.g3_mem 1 s)
  have hL1 : D.p6 1 * D.p1 s * (D.p6 1)⁻¹ =
      Nel4 D (A2 1 s) (g3 1 s) (A4 1 s) * D.p5 (D.θ 1 * s) * D.p1 s := by
    rw [← had.eq 1 s]; simp only [commutatorElement_def]; group
  have hL2 : n * (D.p6 1 * D.p1 s * (D.p6 1)⁻¹) * n⁻¹ =
      Nel4 D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) * D.p1 (f₅ (D.θ 1 * s)) *
        D.p5 (f₁ s) := by
    rw [hL1]
    calc n * (Nel4 D (A2 1 s) (g3 1 s) (A4 1 s) * D.p5 (D.θ 1 * s) * D.p1 s) * n⁻¹
        = (n * Nel4 D (A2 1 s) (g3 1 s) (A4 1 s) * n⁻¹) * (n * D.p5 (D.θ 1 * s) * n⁻¹) *
          (n * D.p1 s * n⁻¹) := by group
      _ = _ := by rw [weyl_conj_Nel4 hC D hf2 hf4 _ _ hv, hf5, hf1]
  have hR1 : (D.p6 1)⁻¹ * D.p1 (-s) * D.p6 1 =
      Nel4 D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) * D.p5 (D.θ (-1) * -s) * D.p1 (-s) := by
    rw [← had.eq (-1) (-s), ← hu]
    simp only [commutatorElement_def]; group
  have hE := hL2.symm.trans (hid.trans hR1)
  have hVL := Nel4_mem D (e := f₄ (A4 1 s)) (f := f₂ (A2 1 s)) hv
  have hVR := Nel4_mem D (e := A2 (-1) (-s)) (f := A4 (-1) (-s)) (had.g3_mem (-1) (-s))
  have hK : ⁅D.p1 (-s), D.p5 (D.θ (-1) * -s)⁆ ∈ Vsub root 2 4 := by
    rw [hcd.eq]; exact Nel4_mem D (hcd.L_mem _ _)
  obtain ⟨ha, hb⟩ := weyl_cmp4 R D hVL hVR hK hE
  rw [ha, hb] at hE
  have hcm : Nel4 D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) *
      ⁅D.p1 (-s), D.p5 (D.θ (-1) * -s)⁆ =
      Nel4 D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) := by
    calc _ = (Nel4 D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) * D.p1 (-s) *
          D.p5 (D.θ (-1) * -s)) * (D.p1 (-s))⁻¹ * (D.p5 (D.θ (-1) * -s))⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (Nel4 D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) * D.p5 (D.θ (-1) * -s) *
          D.p1 (-s)) * (D.p1 (-s))⁻¹ * (D.p5 (D.θ (-1) * -s))⁻¹ := by rw [hE]
      _ = _ := by group
  have eqc : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  rw [eqc, Nel4_mul hC D hv (hcd.L_mem _ _)] at hcm
  have key := Nel4_inj R D ((root 3).mul_mem hv (hcd.L_mem _ _)) (had.g3_mem _ _) hcm
  have h4 := key.2.2
  have hb' : D.θ (-1) * -s = s := by rw [map_neg, map_one]; ring
  rw [hb'] at h4
  exact h4

end Slot

end CFSG.GH74.GLS.Stage4.Hex
