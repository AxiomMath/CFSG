module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5ClsData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Cov
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5R4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.ClsK

open CFSG.CosetTable PkG CovK CFSG.EvenSmallLie.SympSix CFSG.LieType.Multipliers
  CFSG.RankThree.PerfectCover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false

section Cert

@[expose] noncomputable def LG2 : ℕ → Equiv.Perm (Fin 240) := LG letterWords2 LGl

theorem prepL2 (l : ℕ) : Rep 256 240 (GL2.getD l (one 256 240)) (LG2 l) := by
  have := prep_LG (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) (GB := LGl) (baseGl := GLt)
    prepL letterWords2 l
  rwa [GL2_eq] at this

theorem invL2_fix : ∀ l, 29 ≤ l → invL2 l = l := fun l hl => by
  unfold invL2
  exact getD_default' _ _ _ (by simpa using hl)

theorem hIL2 : ∀ l, LG2 (invL2 l) = (LG2 l)⁻¹ := by
  refine LG_inv (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) (GB := LGl) (baseGl := GLt)
    prepL letterWords2 (invL := invL2) 29 (by decide) invL2_fix ?_
  intro l hl
  have h := List.all_eq_true.1 invChk2_true l (List.mem_range.2 hl)
  rw [beq_iff_eq] at h
  rw [GL2_eq]
  exact h

theorem LG2_mem (l : ℕ) : LG2 l ∈ ySub := permW_mem LGl LGl_mem _

@[expose] noncomputable def Z2 (l : ℕ) : ↥ySub := ⟨LG2 l, LG2_mem l⟩

@[expose] noncomputable def zY : ↥ySub := hY [12]

theorem Z2_inv (l : ℕ) : Z2 (invL2 l) = (Z2 l)⁻¹ := Subtype.ext (hIL2 l)

theorem zY_val : (zY : Equiv.Perm (Fin 240)) = LGl 12 := by
  show permW LGl [12] = _
  rw [permW_single]

theorem Z2_val_base {l : ℕ} (hl : l < 13) : LG2 l = LGl l := by
  show permW LGl (letterWords2.getD l []) = _
  have : letterWords2.getD l [] = [l] := by
    have : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 ∨ l = 8 ∨ l = 9 ∨ l = 10 ∨
        l = 11 ∨ l = 12 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  rw [this, permW_single]

theorem Z2_eight_sq : Z2 8 * Z2 8 = zY := by
  have h := sqChk_true
  simp only [sqChk, Bool.and_eq_true, beq_iff_eq] at h
  apply Subtype.ext
  have a := (prepL2 8).comp (by norm_num : 0 < 256) (prepL2 8)
  rw [h.1] at a
  have hz : Rep 256 240 zp (LG2 12) := by
    have := prepL2 12
    have e : GL2.getD 12 (one 256 240) = zp := by decide +kernel
    rwa [e] at this
  have := Rep.unique a hz
  show LG2 8 * LG2 8 = _
  rw [this, zY_val]
  exact Z2_val_base (by norm_num)

theorem zp_rep : Rep 256 240 zp (LG2 12) := by
  have := prepL2 12
  have e : GL2.getD 12 (one 256 240) = zp := by decide +kernel
  rwa [e] at this

theorem Z2_seventeen_sq : Z2 17 * Z2 17 = zY := by
  have h := sqChk_true
  simp only [sqChk, Bool.and_eq_true, beq_iff_eq] at h
  apply Subtype.ext
  have a := (prepL2 17).comp (by norm_num : 0 < 256) (prepL2 17)
  rw [h.2] at a
  have := Rep.unique a zp_rep
  show LG2 17 * LG2 17 = _
  rw [this, zY_val]
  exact Z2_val_base (by norm_num)

theorem Z2_conj1 : Z2 25 * Z2 15 * Z2 26 = Z2 19 := by
  have h := conjChk2_true
  simp only [conjChk2, Bool.and_eq_true, beq_iff_eq] at h
  apply Subtype.ext
  have a := (((prepL2 25).comp (by norm_num : 0 < 256) (prepL2 15)).comp
    (by norm_num : 0 < 256) (prepL2 26))
  rw [h.1] at a
  exact Rep.unique a (prepL2 19)

theorem Z2_conj2 : Z2 27 * Z2 19 * Z2 28 = Z2 19 * zY := by
  have h := conjChk2_true
  simp only [conjChk2, Bool.and_eq_true, beq_iff_eq] at h
  apply Subtype.ext
  have a := (((prepL2 27).comp (by norm_num : 0 < 256) (prepL2 19)).comp
    (by norm_num : 0 < 256) (prepL2 28))
  rw [h.2] at a
  have b := (prepL2 19).comp (by norm_num : 0 < 256) zp_rep
  have := Rep.unique a b
  show LG2 27 * LG2 19 * LG2 28 = LG2 19 * (zY : Equiv.Perm (Fin 240))
  rw [this, zY_val]
  rw [Z2_val_base (l := 12) (by norm_num)]

theorem GL2_19_arr : arrChk (GL2.getD 19 (one 256 240)) tA = true := by decide +kernel

theorem Z2_nineteen : Z2 19 = Sp6Cover.tY := by
  apply Subtype.ext
  have h1 : Rep 256 240 (GL2.getD 19 (one 256 240)) Sp6Cover.tP :=
    rep_of_arrChk (by decide +kernel) GL2_19_arr t_data.1
  exact Rep.unique (prepL2 19) h1

theorem zY_central (y : ↥ySub) : zY * y = y * zY := z_central y

theorem zY_ne_one : zY ≠ 1 := by
  intro h
  have h1 : (zY : Equiv.Perm (Fin 240)) = 1 := by rw [h]; rfl
  rw [zY_val] at h1
  have hz : Rep 256 240 zp (LGl 12) := by
    have := prepL 12
    have e : GLt.getD 12 (one 256 240) = zp := rfl
    rwa [e] at this
  rw [h1] at hz
  have h2 := Rep.inj (by norm_num) hz (Rep.one (by norm_num) (by norm_num))
  have h3 := zChk_true
  simp only [zChk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h3
  exact h3.1.2 h2

theorem qYc_zY : qYc zY = 1 := by
  have hc : qYc zY ∈ Subgroup.center ModSp0 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := qYc_surjective g
    rw [← map_mul, ← map_mul, zY_central]
  have : Subgroup.center ModSp0 = ⊥ := co3X36_center
  rw [this, Subgroup.mem_bot] at hc
  exact hc

theorem card_ker_qY : Nat.card qYc.ker = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup qYc.ker
  have h2 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qYc qYc_surjective).toEquiv
  rw [card_ySub, h2] at h1
  have h3 : Nat.card ModSp0 = 1451520 := card_co3X36
  rw [h3] at h1
  omega

theorem eq_of_card_two {α : Type} (h : Nat.card α = 2) (u v : α) (huv : u ≠ v) (x : α) :
    x = u ∨ x = v := by
  obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ y : α, y = a ∨ y = b := fun y => by
    have : y ∈ ({a, b} : Set α) := by rw [hall]; trivial
    simpa using this
  rcases hmem u with rfl | rfl <;> rcases hmem v with rfl | rfl <;> rcases hmem x with rfl | rfl <;>
    simp_all

theorem ker_qY {x : ↥ySub} (hx : qYc x = 1) : x = 1 ∨ x = zY := by
  have hne : (⟨zY, MonoidHom.mem_ker.2 qYc_zY⟩ : qYc.ker) ≠ 1 := by
    intro h
    exact zY_ne_one (congrArg Subtype.val h)
  have := eq_of_card_two card_ker_qY _ _ hne (⟨x, MonoidHom.mem_ker.2 hx⟩ : qYc.ker)
  rcases this with h | h
  · right; exact congrArg Subtype.val h
  · left; exact congrArg Subtype.val h

theorem wordPerm_append (u v : List (Fin 3 × Bool)) : wordPerm (u ++ v) = wordPerm u * wordPerm v := by
  simp [wordPerm]

theorem wordPerm_invRev (u : List (Fin 3 × Bool)) :
    wordPerm (FreeGroup.invRev u) = (wordPerm u)⁻¹ := by
  rw [← lift_sympGen_mk, ← lift_sympGen_mk, ← FreeGroup.inv_mk, map_inv]

theorem wordPerm_expandW : ∀ codes : List ℤ, (∀ c ∈ codes, c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2) →
    wordPerm (expandW codes) = evalCodes sp6Gens codes
  | [], _ => by simp [expandW, wordPerm, evalCodes]
  | c :: cs, h => by
    have hcs := wordPerm_expandW cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have hB : wordPerm wordSB = sp6B := model_facts.2.2
    simp only [expandW, wordPerm_append, hcs, evalCodes]
    rcases h c (List.mem_cons_self ..) with rfl | rfl | rfl | rfl
    · simp [wordPerm, sympGen, sympT, sp6Gens]
    · simp [hB, sp6Gens]
    · simp [wordPerm, sympGen, sympT, sp6Gens]
    · simp [wordPerm_invRev, hB, sp6Gens]

@[expose] noncomputable def lft (codes : List ℤ) : ↥ySub :=
  FreeGroup.lift e3 (FreeGroup.mk (expandW codes))

theorem qYc_lift_free (x : FreeGroup (Fin 3)) : qYc (FreeGroup.lift e3 x) = FreeGroup.lift sympGenX x := by
  have h : qYc.comp (FreeGroup.lift e3 : FreeGroup (Fin 3) →* ↥ySub) = FreeGroup.lift sympGenX :=
    FreeGroup.ext_hom _ _ fun i => by simp [qYc_e3]
  exact DFunLike.congr_fun h x

theorem qYc_lft {codes : List ℤ} (h : ∀ c ∈ codes, c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2) :
    ((qYc (lft codes) : ModSp0) : Equiv.Perm (Fin 36)) = evalCodes sp6Gens codes := by
  rw [lft, qYc_lift_free, coe_lift_sympGenX, lift_sympGen_mk, wordPerm_expandW codes h]

theorem lft_eq_Z2_15 : lft [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] = Z2 15 := by
  apply Subtype.ext
  rw [lft, coe_lift_e3]
  show _ = permW LGl (letterWords2.getD 15 [])
  rw [ell2_words]

theorem lft_eq_Z2_17 : lft [1, 2, 1, -2] = Z2 17 := by
  apply Subtype.ext
  rw [lft, coe_lift_e3]
  show _ = permW LGl (letterWords2.getD 17 [])
  rw [ell3_words]

theorem lft_one : lft [1] = Z2 8 := by
  apply Subtype.ext
  rw [lft, coe_lift_e3]
  show _ = LG2 8
  rw [Z2_val_base (by norm_num)]
  show permW LGl (toLetters (expandW [1])) = _
  show permW LGl [8] = _
  rw [permW_single]

theorem zY_sq : zY * zY = 1 := by
  have h := zChk_true
  simp only [zChk, Bool.and_eq_true, beq_iff_eq] at h
  apply Subtype.ext
  have a := zp_rep'.comp (by norm_num : 0 < 256) zp_rep'
  rw [h.1.1] at a
  have := Rep.unique a (Rep.one (by norm_num) (by norm_num))
  show (zY : Equiv.Perm (Fin 240)) * zY = 1
  rw [zY_val]
  rw [← Z2_val_base (l := 12) (by norm_num)]
  exact this
where
  zp_rep' : Rep 256 240 zp (LG2 12) := zp_rep

theorem w_central {w : ↥ySub} (hw : w = 1 ∨ w = zY) (x : ↥ySub) : w * x = x * w := by
  rcases hw with rfl | rfl
  · simp
  · exact zY_central x

theorem classify_inv {t : ↥ySub} (ht : t * t = 1) (hne : t ≠ 1)
    (hnc : ¬ ∀ x : ↥ySub, x * t = t * x) (hsq : ∃ i : ↥ySub, i * i = t) :
    ∃ g : ↥ySub, g * t * g⁻¹ = Sp6Cover.tY := by
  obtain ⟨i, hi⟩ := hsq
  have hq1 : qYc t ≠ 1 := by
    intro h
    rcases ker_qY h with h1 | h1
    · exact hne h1
    · apply hnc
      intro x
      rw [h1]
      exact (zY_central x).symm
  have hv2 : orderOf ((qYc t : ModSp0) : Equiv.Perm (Fin 36)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h : qYc t * qYc t = 1 := by rw [← map_mul, ht, map_one]
      have := congrArg (fun y : ModSp0 => (y : Equiv.Perm (Fin 36))) h
      simpa [sq] using this
    · intro h
      apply hq1
      exact Subtype.ext h
  obtain ⟨r, hr, c, hc, hvc⟩ := co3X36_involution_centralizers.1 _ (qYc t).2 hv2
  obtain ⟨g, hg⟩ := qYc_surjective ⟨c, hc⟩
  have step : ∀ ℓ : ↥ySub, ((qYc ℓ : ModSp0) : Equiv.Perm (Fin 36)) = r →
      ∃ w, (w = 1 ∨ w = zY) ∧ t = g * ℓ * g⁻¹ * w := by
    intro ℓ hℓ
    have h1 : qYc (g * ℓ * g⁻¹) = qYc t := by
      apply Subtype.ext
      simp only [map_mul, map_inv, hg]
      show c * ((qYc ℓ : ModSp0) : Equiv.Perm (Fin 36)) * c⁻¹ = _
      rw [hℓ]
      exact hvc.symm
    refine ⟨(g * ℓ * g⁻¹)⁻¹ * t, ker_qY ?_, by group⟩
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have hsq' : ∀ ℓ w : ↥ySub, (w = 1 ∨ w = zY) → ℓ * ℓ = zY → t = g * ℓ * g⁻¹ * w → False := by
    intro ℓ w hw hℓ ht'
    have hww : w * w = 1 := by
      rcases hw with rfl | rfl
      · simp
      · exact zY_sq
    have hcomm : ∀ x, w * x = x * w := w_central hw
    exfalso
    have e : t * t = g * (ℓ * ℓ) * g⁻¹ * (w * w) := by
      calc t * t = (g * ℓ * g⁻¹ * w) * (g * ℓ * g⁻¹ * w) := by rw [← ht']
        _ = (g * ℓ * g⁻¹) * (g * ℓ * g⁻¹) * (w * w) := by
          rw [mul_assoc (g * ℓ * g⁻¹) w, ← mul_assoc w, hcomm, mul_assoc, mul_assoc]
          group
        _ = g * (ℓ * ℓ) * g⁻¹ * (w * w) := by group
    rw [ht, hℓ, hww] at e
    have e2 : g * zY * g⁻¹ = zY := by
      rw [← zY_central g]; group
    rw [e2] at e
    exact zY_ne_one (by simpa using e.symm)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨w, hw, ht'⟩ := step (lft [1]) (by
      rw [qYc_lft (by decide)]; rfl)
    exact (hsq' _ w hw (by rw [lft_one]; exact Z2_eight_sq) ht').elim
  · obtain ⟨w, hw, ht'⟩ := step (lft [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]) (by
      rw [qYc_lft (by decide)]; rfl)
    rw [lft_eq_Z2_15] at ht'
    have c1 : Z2 25 * Z2 15 * (Z2 25)⁻¹ = Sp6Cover.tY := by
      rw [← Z2_nineteen, ← Z2_conj1]
      have : Z2 26 = (Z2 25)⁻¹ := Z2_inv 25
      rw [this]
    have c2 : Z2 27 * Sp6Cover.tY * (Z2 27)⁻¹ = Sp6Cover.tY * zY := by
      rw [← Z2_nineteen, ← Z2_conj2]
      have : Z2 28 = (Z2 27)⁻¹ := Z2_inv 27
      rw [this]
    rcases hw with rfl | rfl
    · refine ⟨(g * (Z2 25)⁻¹)⁻¹, ?_⟩
      rw [ht', ← c1]
      group
    · refine ⟨(g * (Z2 25)⁻¹ * Z2 27)⁻¹, ?_⟩
      have e1 : t = g * (Z2 25)⁻¹ * (Z2 25 * Z2 15 * (Z2 25)⁻¹) * ((Z2 25) * g⁻¹) * zY := by
        rw [ht']; group
      rw [c1] at e1
      have e2 : g * (Z2 25)⁻¹ * Sp6Cover.tY * (Z2 25 * g⁻¹) * zY =
          g * (Z2 25)⁻¹ * (Sp6Cover.tY * zY) * (Z2 25 * g⁻¹) := by
        have := zY_central (Z2 25 * g⁻¹)
        calc _ = g * (Z2 25)⁻¹ * Sp6Cover.tY * ((Z2 25 * g⁻¹) * zY) := by group
          _ = g * (Z2 25)⁻¹ * Sp6Cover.tY * (zY * (Z2 25 * g⁻¹)) := by rw [this]
          _ = _ := by group
      rw [e2, ← c2] at e1
      rw [e1]
      group
  · obtain ⟨w, hw, ht'⟩ := step (lft [1, 2, 1, -2]) (by
      rw [qYc_lft (by decide)]; rfl)
    exact (hsq' _ w hw (by rw [lft_eq_Z2_17]; exact Z2_seventeen_sq) ht').elim
  · exfalso
    have hi' : qYc i * qYc i = qYc t := by rw [← map_mul, hi]
    have h1 := congrArg (fun y : ModSp0 => (y : Equiv.Perm (Fin 36))) hi'
    simp only [Subgroup.coe_mul] at h1
    have h2 : ((c⁻¹ * (qYc i : ModSp0) * c : Equiv.Perm (Fin 36)) *
        (c⁻¹ * (qYc i : ModSp0) * c)) = sp6Rep4 := by
      calc _ = c⁻¹ * ((qYc i : ModSp0) * (qYc i : ModSp0)) * c := by group
        _ = c⁻¹ * ((qYc t : ModSp0) : Equiv.Perm (Fin 36)) * c := by rw [h1]
        _ = sp6Rep4 := by rw [hvc]; group
    exact R4K.no_sqrt_r4 (co3X36.mul_mem (co3X36.mul_mem (co3X36.inv_mem hc) (qYc i).2) hc) h2

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.ClsK
