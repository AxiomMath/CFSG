module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Borel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Weyl

theorem mat_mul_of_perm {x y : hypSU h 2 1} {π ρ : HypIndex 2 1 → HypIndex 2 1}
    (hx : ∀ a b, mat x a b = if π a = b then 1 else 0)
    (hy : ∀ a b, mat y a b = if ρ a = b then 1 else 0) (a b : HypIndex 2 1) :
    mat (x * y) a b = if ρ (π a) = b then 1 else 0 := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single (π a)]
  · rw [hx, hy, ite_eq_left rfl, one_mul]
  · intro c _ hc
    rw [hx, ite_eq_right (Ne.symm hc), zero_mul]
  · simp

theorem mat_rSU_mul_sSU (a b : HypIndex 2 1) :
    mat (rSU h * sSU h) a b = if σs (σr a) = b then 1 else 0 :=
  mat_mul_of_perm mat_rSU mat_sSU a b

theorem rSU_mul_sSU_pow_four : (rSU h * sSU h) ^ 4 = 1 := by
  have h2 := mat_mul_of_perm (mat_rSU_mul_sSU (h := h)) mat_rSU_mul_sSU
  have h3 := mat_mul_of_perm h2 mat_rSU_mul_sSU
  have h4 := mat_mul_of_perm h3 mat_rSU_mul_sSU
  have hperm : ∀ a, σs (σr (σs (σr (σs (σr (σs (σr a))))))) = a := by decide
  apply mat_injective
  ext a b
  rw [show (rSU h * sSU h) ^ 4 = rSU h * sSU h * (rSU h * sSU h) * (rSU h * sSU h) *
    (rSU h * sSU h) by simp only [pow_succ, pow_zero, one_mul], h4, mat_one, one_apply, hperm]

end Weyl

section A₃N₁

theorem sSU_inv_eq : (sSU h)⁻¹ = sSU h := inv_eq_of_mul_eq_one_right sSU_mul_self

theorem rSU_inv_eq : (rSU h)⁻¹ = rSU h := inv_eq_of_mul_eq_one_right rSU_mul_self

theorem patSub_sI₁_le_N₁sub : patSub h sI₁ isPattern_sI₁ ≤ N₁sub h := fun u hu => by
  rw [eq_uSU_of_mem hu]
  exact uSU_mem_N₁sub _

theorem A₂sub_inf_conj_rSU :
    A₂sub h ⊓ (A₂sub h).map (MulAut.conj (rSU h)).toMonoidHom = patSub h sI₄ isPattern_sI₄ := by
  refine le_antisymm (fun x ⟨hx, y, hy, hyx⟩ => ?_) (le_inf (patSub_mono _ _ (by decide))
    fun x hx => ⟨rSU h * x * (rSU h)⁻¹, ?_, ?_⟩)
  · change rSU h * y * (rSU h)⁻¹ = x at hyx
    have hyU := A₂sub_le_U hy
    obtain ⟨-, y1, y2, y3⟩ := mem_A₂sub.1 hy
    obtain ⟨hxU, x1, x2, x3⟩ := mem_A₂sub.1 hx
    have hr : ∀ a b, mat x a b = mat y (σr a) (σr b) := fun a b => by
      rw [← hyx, conj_rSU_apply]
    refine mem_patSub_sI₄.2 ⟨hxU, ?_, ?_, ?_, ?_, x1, x2, x3, ?_⟩
    · rw [hr]
      exact U_lower hyU (by decide)
    · rw [hr]
      exact U_lower hyU (by decide)
    · rw [hr]
      exact y1
    · rw [hr]
      exact y2
    · rw [hr]
      exact y3
  · exact patSub_mono _ isPattern_sA₂ (by decide)
      (conj_perm_mem_patSub σr_σr σr_partner mat_rSU isPattern_sI₄ isPattern_sI₄ (by decide) hx)
  · change rSU h * (rSU h * x * (rSU h)⁻¹) * (rSU h)⁻¹ = x
    rw [rSU_inv_eq, ← mul_assoc, ← mul_assoc, rSU_mul_self, one_mul, mul_assoc, rSU_mul_self,
      mul_one]

theorem leviSU_sl2Upper (c : K) : UnitaryHigher.leviSU h 1 (sl2Upper K c) = uSU h c :=
  (lev_eq_leviSU (sl2Upper K c) (isUnit_det_upper c)).symm

theorem leviSU_sl2Lower (c : K) :
    UnitaryHigher.leviSU h 1 (sl2Lower K c) = rSU h * uSU h c * rSU h := by
  have := h.charP
  rw [← leviSU_sl2Upper, rSU_eq_leviSU, ← map_mul, ← map_mul]
  congr 1
  have e : (sl2Lower K c : Matrix (Fin 2) (Fin 2) K) =
      (swapSL h : Matrix (Fin 2) (Fin 2) K) * (sl2Upper K c : Matrix (Fin 2) (Fin 2) K) *
        (swapSL h : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapSL, swapM, sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]; exact e)

theorem Ssub_sup_N₁sub_eq : Ssub h ⊔ N₁sub h = A₂sub h ⊔
    (A₂sub h ⊓ (A₂sub h).map (MulAut.conj (rSU h)).toMonoidHom).map
      (MulAut.conj (rSU h * sSU h)).toMonoidHom := by
  set R := A₂sub h ⊔ (A₂sub h ⊓ (A₂sub h).map (MulAut.conj (rSU h)).toMonoidHom).map
    (MulAut.conj (rSU h * sSU h)).toMonoidHom with hR
  have hUN : hypUnitriangular h 2 1 ≤ Ssub h ⊔ N₁sub h := by
    rw [U_eq_sup_Ssub_I₁.1]
    exact sup_le_sup_left patSub_sI₁_le_N₁sub _
  have hlow : ∀ c : K, rSU h * uSU h c * rSU h ∈ R := fun c => by
    refine mem_sup_right ⟨sSU h * uSU h c * (sSU h)⁻¹, ?_, ?_⟩
    · rw [A₂sub_inf_conj_rSU]
      exact conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₁ isPattern_sI₄
        (by decide) (uSU_mem_patSub c)
    · change rSU h * sSU h * (sSU h * uSU h c * (sSU h)⁻¹) * (rSU h * sSU h)⁻¹ = _
      rw [sSU_inv_eq, _root_.mul_inv_rev, sSU_inv_eq, rSU_inv_eq]
      calc rSU h * sSU h * (sSU h * uSU h c * sSU h) * (sSU h * rSU h)
          = rSU h * (sSU h * sSU h) * uSU h c * (sSU h * sSU h) * rSU h := by group
        _ = rSU h * uSU h c * rSU h := by rw [sSU_mul_self, mul_one, mul_one]
  have hN : N₁sub h ≤ R := by
    rintro _ ⟨A, rfl⟩
    have hA : A ∈ closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) := by
      rw [sl2_closure_upper_lower]
      exact mem_top A
    have := Subgroup.mem_map_of_mem (UnitaryHigher.leviSU h 1) hA
    rw [MonoidHom.map_closure] at this
    refine (closure_le R).2 ?_ this
    rintro _ ⟨B, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · rw [leviSU_sl2Upper]
      exact mem_sup_left (patSub_I₁_le_A₂sub (uSU_mem_patSub c))
    · rw [leviSU_sl2Lower]
      exact hlow c
  have hr : rSU h ∈ R := hN rSU_mem_N₁sub
  refine le_antisymm (sup_le ?_ hN) (sup_le (A₂sub_le_U.trans hUN) ?_)
  · rw [Ssub_eq_sup_I₂.1]
    refine sup_le (inf_le_left.trans le_sup_left) fun g hg => ?_
    have hg' : rSU h * g * (rSU h)⁻¹ ∈ A₂sub h :=
      (patSub_I₅_le_A₂sub_inf_Ssub (conj_perm_mem_patSub σr_σr σr_partner mat_rSU isPattern_sI₂
        isPattern_sI₅ (by decide) hg)).1
    rw [show g = (rSU h)⁻¹ * (rSU h * g * (rSU h)⁻¹) * rSU h by group]
    exact mul_mem (mul_mem (inv_mem hr) (mem_sup_left hg')) hr
  · rintro _ ⟨x, hx, rfl⟩
    rw [A₂sub_inf_conj_rSU] at hx
    have hsx : sSU h * x * (sSU h)⁻¹ ∈ N₁sub h :=
      patSub_sI₁_le_N₁sub (conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₄
        isPattern_sI₁ (by decide) hx)
    refine mem_sup_right ?_
    change rSU h * sSU h * x * (rSU h * sSU h)⁻¹ ∈ N₁sub h
    rw [show rSU h * sSU h * x * (rSU h * sSU h)⁻¹ =
      rSU h * (sSU h * x * (sSU h)⁻¹) * (rSU h)⁻¹ by group]
    exact mul_mem (mul_mem rSU_mem_N₁sub hsx) (inv_mem rSU_mem_N₁sub)

end A₃N₁

section Faithful

theorem N₂sub_inv_conj_e₁ {g x : hypSU h 2 1} (hg : g ∈ N₂sub h) {b : HypIndex 2 1}
    (hb₁ : b ≠ ιe₁) (hb₂ : b ≠ ιf₁) :
    mat (g⁻¹ * x * g) ιe₁ b = mat x ιe₁ ιe₂ * mat g ιe₂ b + mat x ιe₁ ιz * mat g ιz b +
      mat x ιe₁ ιf₂ * mat g ιf₂ b := by
  have hrow : ∀ l, mat (g⁻¹ * x) ιe₁ l = mat x ιe₁ l := fun l => by
    rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by
      rw [(N₂sub_rows (inv_mem hg) k).1, one_apply_ne (Ne.symm hk), zero_mul]) (by simp),
      (N₂sub_rows (inv_mem hg) _).1, one_apply_eq, one_mul]
  rw [mat_mul, Matrix.mul_apply, sum_hypIndex_two]
  simp only [hrow]
  rw [(N₂sub_rows hg b).1, (N₂sub_rows hg b).2, one_apply_ne (Ne.symm hb₁),
    one_apply_ne (Ne.symm hb₂)]
  ring

theorem eq_of_N₂sub_inv_conj {g g' : hypSU h 2 1} (hg : g ∈ N₂sub h) (hg' : g' ∈ N₂sub h)
    (H : ∀ x ∈ A₂sub h, mat (g⁻¹ * x * g) ιe₁ ιe₂ = mat (g'⁻¹ * x * g') ιe₁ ιe₂ ∧
      mat (g⁻¹ * x * g) ιe₁ ιz = mat (g'⁻¹ * x * g') ιe₁ ιz ∧
      mat (g⁻¹ * x * g) ιe₁ ιf₂ = mat (g'⁻¹ * x * g') ιe₁ ιf₂) : g = g' := by
  have key : ∀ a b c : K, ∀ l, l ≠ ιe₁ → l ≠ ιf₁ →
      a * mat g ιe₂ l + b * mat g ιz l + c * mat g ιf₂ l =
        a * mat g' ιe₂ l + b * mat g' ιz l + c * mat g' ιf₂ l := by
    intro a b c l hl₁ hl₂
    obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h a b c
    obtain ⟨H1, H2, H3⟩ := H x hx
    have e : mat (g⁻¹ * x * g) ιe₁ l = mat (g'⁻¹ * x * g') ιe₁ l := by
      rcases l with i | k | i <;> (try fin_cases i) <;> (try fin_cases k)
      · exact absurd rfl hl₁
      · exact H1
      · exact H2
      · exact absurd rfl hl₂
      · exact H3
    rwa [N₂sub_inv_conj_e₁ hg hl₁ hl₂, N₂sub_inv_conj_e₁ hg' hl₁ hl₂, x1, x2, x3] at e
  have k1 : ∀ l, l ≠ ιe₁ → l ≠ ιf₁ → mat g ιe₂ l = mat g' ιe₂ l := fun l h1 h2 => by
    simpa using key 1 0 0 l h1 h2
  have k2 : ∀ l, l ≠ ιe₁ → l ≠ ιf₁ → mat g ιz l = mat g' ιz l := fun l h1 h2 => by
    simpa using key 0 1 0 l h1 h2
  have k3 : ∀ l, l ≠ ιe₁ → l ≠ ιf₁ → mat g ιf₂ l = mat g' ιf₂ l := fun l h1 h2 => by
    simpa using key 0 0 1 l h1 h2
  obtain ⟨c1, c2⟩ := mem_N₂sub.1 hg
  obtain ⟨c1', c2'⟩ := mem_N₂sub.1 hg'
  apply mat_injective
  ext a b
  by_cases ha₁ : a = ιe₁
  · rw [ha₁, (N₂sub_rows hg b).1, (N₂sub_rows hg' b).1]
  by_cases ha₂ : a = ιf₁
  · rw [ha₂, (N₂sub_rows hg b).2, (N₂sub_rows hg' b).2]
  by_cases hb₁ : b = ιe₁
  · rw [hb₁, c1, c1']
  by_cases hb₂ : b = ιf₁
  · rw [hb₂, c2, c2']
  rcases a with i | k | i <;> (try fin_cases i) <;> (try fin_cases k)
  · exact absurd rfl ha₁
  · exact k1 b hb₁ hb₂
  · exact k2 b hb₁ hb₂
  · exact absurd rfl ha₂
  · exact k3 b hb₁ hb₂

theorem A₂_inv_conj_torus {t x : hypSU h 2 1} (ht : t ∈ Isub h) (ht1 : mat t ιe₁ ιe₁ = 1)
    (b : HypIndex 2 1) : mat (t⁻¹ * x * t) ιe₁ b = mat x ιe₁ b * mat t b b := by
  have := torus_conj_apply (inv_mem ht) x ιe₁ b
  rw [inv_inv, torus_inv_apply ht, torus_inv_apply ht, ht1, inv_inv, inv_one, one_mul] at this
  exact this

end Faithful

section Generation

theorem root_mul_conj_root_eq_sSU {x : hypSU h 2 1} (hx : x ∈ patSub h sI₂ isPattern_sI₂)
    (h1 : mat x ιe₂ ιz = 0) (h2 : mat x ιe₂ ιf₂ = 1) :
    x * (sSU h * x * (sSU h)⁻¹) * x = sSU h := by
  have := h.charP
  have hxN := patSub_sI₂_le_N₂sub hx
  have hs : ∀ y, (sSU h)⁻¹ * y * sSU h = sSU h * y * (sSU h)⁻¹ := fun y => by rw [sSU_inv_eq]
  refine eq_of_N₂sub_inv_conj (mul_mem (mul_mem hxN (mul_mem (mul_mem sSU_mem_N₂sub hxN)
    (inv_mem sSU_mem_N₂sub))) hxN) sSU_mem_N₂sub fun y hy => ?_
  have e : (x * (sSU h * x * (sSU h)⁻¹) * x)⁻¹ * y * (x * (sSU h * x * (sSU h)⁻¹) * x) =
      x⁻¹ * (sSU h * (x⁻¹ * ((sSU h)⁻¹ * (x⁻¹ * y * x) * sSU h) * x) * (sSU h)⁻¹) * x := by
    group
  obtain ⟨hy1, p1, p2, p3⟩ := A₂_conj_rootI₂ hx hy
  obtain ⟨hy2, q1, q2, q3⟩ := A₂_conj_sSU hy1
  obtain ⟨hy3, r1, r2, r3⟩ := A₂_conj_rootI₂ hx hy2
  obtain ⟨hy4, s1, s2, s3⟩ := A₂_conj_sSU hy3
  obtain ⟨-, t1, t2, t3⟩ := A₂_conj_rootI₂ hx hy4
  obtain ⟨-, u1, u2, u3⟩ := A₂_conj_sSU hy
  rw [e, hs, hs]
  simp only [t1, t2, t3, s1, s2, s3, r1, r2, r3, q1, q2, q3, p1, p2, p3, u1, u2, u3, h1, h2,
    map_zero]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (CharTwo.two_eq_zero (R := K)) * (mat y ιe₁ ιe₂)
  · ring
  · linear_combination (CharTwo.two_eq_zero (R := K)) * (mat y ιe₁ ιf₂ + mat y ιe₁ ιe₂)

theorem exists_torus_eq_mul_root (h : UnitaryFieldData 2 f K) {w : K} (hw : w ≠ 0) :
    ∃ t ∈ Isub h, mat t ιe₁ ιe₁ = 1 ∧ mat t ιe₂ ιe₂ = w ∧
      ∃ X₁ ∈ patSub h sI₂ isPattern_sI₂, ∃ X ∈ patSub h sI₂ isPattern_sI₂,
        ∃ X₂ ∈ patSub h sI₂ isPattern_sI₂, t = sSU h * X₁ * sSU h * X * sSU h * X₂ := by
  have := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hW : h.bar w ≠ 0 := (map_ne_zero h.bar).2 hw
  obtain ⟨u, hu⟩ := h.normHom_surjective ⟨w + h.bar w, by
    rw [UnitaryFieldData.mem_fixedField, map_add, h.bar_bar, add_comm]⟩
  have huw : w + h.bar w = u * h.bar u := by
    have := congrArg Subtype.val hu
    simp only [UnitaryFieldData.normHom, UnitaryFieldData.norm, MonoidHom.coe_mk,
      OneHom.coe_mk] at this
    exact this.symm
  set v := w⁻¹ with hvdef
  set V := (h.bar w)⁻¹ with hVdef
  have hv : w * v = 1 := mul_inv_cancel₀ hw
  have hV : h.bar w * V = 1 := mul_inv_cancel₀ hW
  have hbV : h.bar V = v := by rw [hVdef, map_inv₀, h.bar_bar]
  have hbv : h.bar v = V := by rw [hvdef, map_inv₀]
  have hroot : V + h.bar V = u * V * h.bar (u * V) := by
    rw [hbV, map_mul, hbV]
    linear_combination (V * v) * huw - v * hV - V * hv
  have hroot₂ : V + h.bar V = u * v * h.bar (u * v) := by
    rw [hbV, map_mul, hbv]
    linear_combination (V * v) * huw - v * hV - V * hv
  obtain ⟨X₁, hX₁, a1, b1⟩ := exists_rootI₂ h hroot
  obtain ⟨X, hX, a0, b0⟩ := exists_rootI₂ h huw
  obtain ⟨X₂, hX₂, a2, b2⟩ := exists_rootI₂ h hroot₂
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus h one_ne_zero hw
  rw [map_one, one_mul, one_mul] at e3
  rw [map_one, inv_one] at e4
  refine ⟨t, ht, e1, e2, X₁, hX₁, X, hX, X₂, hX₂, ?_⟩
  have hX₁N := patSub_sI₂_le_N₂sub hX₁
  have hXN := patSub_sI₂_le_N₂sub hX
  have hX₂N := patSub_sI₂_le_N₂sub hX₂
  have hsN := sSU_mem_N₂sub (h := h)
  have hs : ∀ y, (sSU h)⁻¹ * y * sSU h = sSU h * y * (sSU h)⁻¹ := fun y => by rw [sSU_inv_eq]
  refine eq_of_N₂sub_inv_conj (mem_N₂sub_of_torus ht e1 e4)
    (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hsN hX₁N) hsN) hXN) hsN) hX₂N) fun y hy => ?_
  have e : (sSU h * X₁ * sSU h * X * sSU h * X₂)⁻¹ * y * (sSU h * X₁ * sSU h * X * sSU h * X₂) =
      X₂⁻¹ * ((sSU h)⁻¹ * (X⁻¹ * ((sSU h)⁻¹ * (X₁⁻¹ * ((sSU h)⁻¹ * y * sSU h) * X₁) *
        sSU h) * X) * sSU h) * X₂ := by
    group
  rw [e, hs, hs, hs]
  obtain ⟨ha, p1, p2, p3⟩ := A₂_conj_sSU hy
  obtain ⟨hb, q1, q2, q3⟩ := A₂_conj_rootI₂ hX₁ ha
  obtain ⟨hc, r1, r2, r3⟩ := A₂_conj_sSU hb
  obtain ⟨hd, s1, s2, s3⟩ := A₂_conj_rootI₂ hX hc
  obtain ⟨he, t1, t2, t3⟩ := A₂_conj_sSU hd
  obtain ⟨-, u1, u2, u3⟩ := A₂_conj_rootI₂ hX₂ he
  rw [A₂_inv_conj_torus ht e1, A₂_inv_conj_torus ht e1, A₂_inv_conj_torus ht e1, e2, e3, e5]
  simp only [u1, u2, u3, t1, t2, t3, s1, s2, s3, r1, r2, r3, q1, q2, q3, p1, p2, p3, a1, b1,
    a0, b0, a2, b2, map_mul, hbV, hbv]
  set α := mat y ιe₁ ιe₂
  set β := mat y ιe₁ ιz
  set c := mat y ιe₁ ιf₂
  set ub := h.bar u
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -(β * ub) * hv - c * hV + (c * V) * huw - (β * ub + c + c * V * w) * h2
  · linear_combination -(β + α * u + u * v * β * ub) * hv - (u * v * c) * hV +
      (β * v + u * v * c * V) * huw -
      (β + α * u + c * u * V + u * v * (β * ub + c + c * V * w)) * h2
  · linear_combination -(2 * β * ub * V) * hv - (α + β * ub * v + V * c) * hV +
      (α * V + β * ub * v * V + c * V ^ 2) * huw -
      (α * (1 + w * V) + β * ub * (v + V) + c * u * ub * V ^ 2 +
        V * (β * ub + c + c * V * w)) * h2

theorem Isub_ext {t t' : hypSU h 2 1} (ht : t ∈ Isub h) (ht' : t' ∈ Isub h)
    (h1 : mat t ιe₁ ιe₁ = mat t' ιe₁ ιe₁) (h2 : mat t ιe₂ ιe₂ = mat t' ιe₂ ιe₂) : t = t' := by
  have hz : ∀ s ∈ Isub h, mat s ιz ιz * (mat s ιe₁ ιe₁ / h.bar (mat s ιe₁ ιe₁)) *
      (mat s ιe₂ ιe₂ / h.bar (mat s ιe₂ ιe₂)) = 1 := by
    rintro s ⟨a, d, -, hp, hm⟩
    have e : mat s = diagonal (torusEntries h a d) := hm
    simp only [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one] at hp
    rw [e]
    simp only [diagonal_apply_eq, torusEntries]
    linear_combination hp
  have hz' : mat t ιz ιz = mat t' ιz ιz := by
    have e := hz t ht
    have e' := hz t' ht'
    rw [h1, h2] at e
    have h0 : mat t' ιe₁ ιe₁ / h.bar (mat t' ιe₁ ιe₁) *
        (mat t' ιe₂ ιe₂ / h.bar (mat t' ιe₂ ιe₂)) ≠ 0 := by
      have := torus_ne_zero ht' ιe₁
      have := torus_ne_zero ht' ιe₂
      have : h.bar (mat t' ιe₁ ιe₁) ≠ 0 := (map_ne_zero h.bar).2 (torus_ne_zero ht' ιe₁)
      have : h.bar (mat t' ιe₂ ιe₂) ≠ 0 := (map_ne_zero h.bar).2 (torus_ne_zero ht' ιe₂)
      positivity
    exact mul_right_cancel₀ h0 (by rw [← mul_assoc, ← mul_assoc, e, e'])
  have hf : ∀ i : Fin 2, mat t (.inr (.inr i)) (.inr (.inr i)) =
      mat t' (.inr (.inr i)) (.inr (.inr i)) := by
    intro i
    have e := torus_bar_mul ht (.inl i)
    have e' := torus_bar_mul ht' (.inl i)
    have hi : mat t (.inl i) (.inl i) = mat t' (.inl i) (.inl i) := by
      fin_cases i
      · exact h1
      · exact h2
    rw [hi] at e
    simp only [hypPartner_inl] at e e'
    exact mul_left_cancel₀ ((map_ne_zero h.bar).2 (torus_ne_zero ht' _)) (e.trans e'.symm)
  apply mat_injective
  rw [torus_mat ht, torus_mat ht']
  congr 1
  funext a
  rcases a with i | k | i <;> (try fin_cases i) <;> (try fin_cases k)
  · exact h1
  · exact h2
  · exact hz'
  · exact hf 0
  · exact hf 1

theorem Isub_le_of_U_le {H : Subgroup (hypSU h 2 1)} (hU : hypUnitriangular h 2 1 ≤ H)
    (hr : rSU h ∈ H) (hs : sSU h ∈ H) : Isub h ≤ H := by
  have hmem : ∀ {w : K}, w ≠ 0 → ∃ t ∈ Isub h, mat t ιe₁ ιe₁ = 1 ∧ mat t ιe₂ ιe₂ = w ∧ t ∈ H := by
    intro w hw
    obtain ⟨t, ht, e1, e2, X₁, hX₁, X, hX, X₂, hX₂, rfl⟩ := exists_torus_eq_mul_root h hw
    refine ⟨_, ht, e1, e2, ?_⟩
    have := fun Y (hY : Y ∈ patSub h sI₂ isPattern_sI₂) => hU (patSub_le_U _ _ hY)
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hs (this _ hX₁)) hs) (this _ hX)) hs)
      (this _ hX₂)
  intro t ht
  obtain ⟨ta, hta, a1, a2, haH⟩ := hmem (torus_ne_zero ht ιe₁)
  obtain ⟨tb, htb, b1, b2, hbH⟩ := hmem (torus_ne_zero ht ιe₂)
  have hra : rSU h * ta * (rSU h)⁻¹ ∈ Isub h := by
    rw [← map_conj_rSU_Isub]
    exact ⟨ta, hta, rfl⟩
  have e : t = rSU h * ta * (rSU h)⁻¹ * tb := by
    refine Isub_ext ht (mul_mem hra htb) ?_ ?_
    · rw [torus_mul_apply hra htb, conj_rSU_apply, b1, mul_one]
      exact a2.symm
    · rw [torus_mul_apply hra htb, conj_rSU_apply, b2]
      change _ = mat ta ιe₁ ιe₁ * _
      rw [a1, one_mul]
  rw [e]
  exact mul_mem (mul_mem (mul_mem hr haH) (inv_mem hr)) hbH

theorem one_mem_traceZero_two (h : UnitaryFieldData 2 f K) : (1 : K) ∈ h.traceZero := by
  have := h.charP
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one,
    CharTwo.add_self_eq_zero]

theorem uWeylRep_zero_eq_rSU :
    UnitaryHigher.uWeylRep 1 h (0 : Fin 2) 1 (one_mem_traceZero_two h) = rSU h := by
  have := h.charP
  apply mat_injective
  unfold UnitaryHigher.uWeylRep
  rw [dite_eq_left (by decide)]
  unfold UnitaryHigher.uWeylRepShort
  rw [mat_mul, mat_mul]
  simp only [mat, UnitaryHigher.coe_uRootElt]
  rw [UnitaryHigher.simpleSnd_of_lt (by decide)]
  simp only [UnitaryHigher.uRootMat_inl_inl]
  ext a b
  rw [← mat, mat_rSU]
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply, one_apply,
      σr, Equiv.swap_apply_def, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem uWeylRep_one_eq_sSU :
    UnitaryHigher.uWeylRep 1 h (1 : Fin 2) 1 (one_mem_traceZero_two h) = sSU h := by
  have := h.charP
  apply mat_injective
  unfold UnitaryHigher.uWeylRep
  rw [dite_eq_right (by decide)]
  unfold UnitaryHigher.uWeylRepLong
  rw [mat_mul, mat_mul]
  simp only [mat, UnitaryHigher.coe_uRootElt, UnitaryHigher.uRootMat_inl_inr_self,
    UnitaryHigher.uRootMat_inr_inl_self]
  ext a b
  rw [← mat, mat_sSU]
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply, one_apply,
      σs, Equiv.swap_apply_def, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem eq_top_of_U_le {H : Subgroup (hypSU h 2 1)} (hU : hypUnitriangular h 2 1 ≤ H)
    (hr : rSU h ∈ H) (hs : sSU h ∈ H) : H = ⊤ := by
  have hB : hypBorel h 2 1 ≤ H :=
    (CFSG.RankThree.CentralLiftU.hypBorel_le_sup le_rfl (by norm_num)).trans
      (sup_le hU (Isub_le_of_U_le hU hr hs))
  have hcuts : UnitaryHigher.overgroupCuts 1 h 1 (one_mem_traceZero_two h) H = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun i hi => ?_
    obtain ⟨k, -, hk⟩ := hi
    refine hk ?_
    fin_cases k
    · exact uWeylRep_zero_eq_rSU (h := h) ▸ hr
    · exact uWeylRep_one_eq_sSU (h := h) ▸ hs
  rw [UnitaryHigher.eq_flagStabilizer_overgroupCuts h (by norm_num) le_rfl
    (one_mem_traceZero_two h) one_ne_zero H hB, hcuts, UnitaryHigher.flagStabilizer_empty]

theorem A₃N₁_sup_conj_sSU_eq_top :
    (Ssub h ⊔ N₁sub h) ⊔ (Ssub h ⊔ N₁sub h).map (MulAut.conj (sSU h)).toMonoidHom = ⊤ := by
  have := h.charP
  have hUN : hypUnitriangular h 2 1 ≤ Ssub h ⊔ N₁sub h := by
    rw [U_eq_sup_Ssub_I₁.1]
    exact sup_le_sup_left patSub_sI₁_le_N₁sub _
  refine eq_top_of_U_le (hUN.trans le_sup_left) (mem_sup_left (mem_sup_right rSU_mem_N₁sub)) ?_
  obtain ⟨x, hx, x1, x2⟩ := exists_rootI₂ h (u := 0) (c := 1)
    (by rw [map_one, map_zero, mul_zero, CharTwo.add_self_eq_zero])
  have hxU := patSub_le_U _ _ hx
  have hmem : x * (sSU h * x * (sSU h)⁻¹) * x ∈
      (Ssub h ⊔ N₁sub h) ⊔ (Ssub h ⊔ N₁sub h).map (MulAut.conj (sSU h)).toMonoidHom :=
    mul_mem (mul_mem (mem_sup_left (hUN hxU)) (mem_sup_right ⟨x, hUN hxU, rfl⟩))
      (mem_sup_left (hUN hxU))
  rwa [root_mul_conj_root_eq_sSU hx x1 x2] at hmem

end Generation

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem r_mul_s_pow_four : (d.r * d.s) ^ 4 = 1 := by
  rw [r, s, ← map_mul, ← map_pow, rSU_mul_sSU_pow_four, map_one]

theorem eq_of_η_eq {x y : hypSU h 2 1} (e : d.η x = d.η y) (hx : mat x ιe₁ ιe₁ = 1)
    (hy : mat y ιe₁ ιe₁ = 1) : x = y := by
  have hz : x⁻¹ * y ∈ hypScalars h 2 1 :=
    (d.η_eq_one_iff _).1 (by rw [map_mul, map_inv, e, inv_mul_cancel])
  obtain ⟨c, -, hcm⟩ := exists_scalar_of_mem_hypScalars hz
  have hy' : mat y = mat x * mat (x⁻¹ * y) := by rw [← mat_mul, mul_inv_cancel_left]
  have h1 : c = 1 := by
    have := congrFun (congrFun hy' ιe₁) ιe₁
    rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by
      rw [hcm, ite_eq_right hk, mul_zero]) (by simp), hcm, ite_eq_left rfl, hx, hy, one_mul] at this
    exact this.symm
  have h2 : x⁻¹ * y = 1 := by
    apply mat_injective
    ext a b
    rw [hcm, h1, mat_one, one_apply]
  rw [← mul_inv_cancel_left x y, h2, mul_one]

theorem A₂_inf_conj_r :
    d.A₂ ⊓ d.A₂.map (MulAut.conj d.r).toMonoidHom = d.pull (patSub h sI₄ isPattern_sI₄) := by
  rw [← A₂sub_inf_conj_rSU]
  refine le_antisymm ?_ (le_inf (d.pull_mono inf_le_left)
    (by rw [Data.r, Data.A₂, ← d.pull_conj]; exact d.pull_mono inf_le_right))
  rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
  rw [Data.r, Data.A₂, ← d.pull_conj] at hb
  obtain ⟨b, ⟨b', hb', rfl⟩, e⟩ := hb
  have hb'U := A₂sub_le_U hb'
  have hrb : mat (rSU h * b' * (rSU h)⁻¹) ιe₁ ιe₁ = 1 := by
    rw [conj_rSU_apply]
    exact U_diag hb'U _
  have hab := d.eq_of_η_eq e hrb (U_diag (A₂sub_le_U ha) _)
  exact ⟨a, ⟨ha, hab ▸ ⟨b', hb', rfl⟩⟩, rfl⟩

theorem A₃_sup_N₁_eq : d.A₃ ⊔ d.N₁ = d.A₂ ⊔ (d.A₂ ⊓ d.A₂.map (MulAut.conj d.r).toMonoidHom).map
    (MulAut.conj (d.r * d.s)).toMonoidHom := by
  have e : ∀ X Y : Subgroup (hypSU h 2 1), d.pull X ⊔ d.pull Y = d.pull (X ⊔ Y) := fun X Y =>
    (Subgroup.map_sup X Y d.η).symm
  rw [d.A₂_inf_conj_r, ← A₂sub_inf_conj_rSU, show d.r * d.s = d.η (rSU h * sSU h) from
    (map_mul _ _ _).symm, ← d.pull_conj, Data.A₃, Data.N₁, Data.A₂, e, e, Ssub_sup_N₁sub_eq]

theorem A₃N₁_sup_conj_s_eq_L :
    (d.A₃ ⊔ d.N₁) ⊔ (d.A₃ ⊔ d.N₁).map (MulAut.conj d.s).toMonoidHom = d.L := by
  have e1 : d.A₃ ⊔ d.N₁ = d.pull (Ssub h ⊔ N₁sub h) := (Subgroup.map_sup _ _ _).symm
  rw [e1, Data.s, ← d.pull_conj, pull, pull, ← Subgroup.map_sup, A₃N₁_sup_conj_sSU_eq_top,
    ← MonoidHom.range_eq_map, d.range_η]

end Data

end CFSG.LocalAnalysis.EvenBN.U5
