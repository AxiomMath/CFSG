module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelFiveTwo
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismCover

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] {H : Subgroup G}

theorem conj_mem_commutator_self {n k : G} (hn : n ∈ H) (hk : k ∈ ⁅H, H⁆) :
    n * k * n⁻¹ ∈ ⁅H, H⁆ := by
  have hH : H.map (MulAut.conj n).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hn hy) (inv_mem hn)
    · intro hx
      exact ⟨n⁻¹ * x * n, mul_mem (mul_mem (inv_mem hn) hx) hn, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
  have : n * k * n⁻¹ ∈ (⁅H, H⁆).map (MulAut.conj n).toMonoidHom := ⟨k, hk, rfl⟩
  rwa [Subgroup.map_commutator, hH] at this

theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  (Subgroup.commutator_le).2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem inv_mul_conj_mem_commutator {x t : G} (hx : x ∈ H) (ht : t ∈ H) :
    x⁻¹ * (t * x * t⁻¹) ∈ ⁅H, H⁆ := by
  have := Subgroup.commutator_mem_commutator (inv_mem hx) ht
  rw [commutatorElement_def, inv_inv] at this
  rwa [← mul_assoc, ← mul_assoc]

end Generic

section Perfect

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem commutator_N₁sub : ⁅N₁sub h, N₁sub h⁆ = N₁sub h := by
  have := h.finite
  have hcard : 4 ≤ Nat.card K := by
    rw [h.card_eq_sq]
    have : 2 ≤ 2 ^ f := (Nat.pow_le_pow_right (by norm_num) h.one_le).trans_eq' (by norm_num)
    nlinarith
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hcard
  rw [N₁sub, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem commutator_N₂sub (hf : 2 ≤ f) : ⁅N₂sub h, N₂sub h⁆ = N₂sub h := by
  have hq : 2 < 2 ^ f := (Nat.pow_le_pow_right (by norm_num) hf).trans_lt' (by norm_num)
  have := CFSG.ShultStronglyClosedTI.UnitaryAutomorphism.isPerfect_hypSU h hq
  rw [← range_embSU, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

end Perfect

section A₂N₂

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem ZPsub_le_commutator_A₂sub : ZPsub h ≤ ⁅A₂sub h, A₂sub h⁆ := by
  have := h.charP
  intro z hz
  have hzf : h.bar (mat z ιe₁ ιf₁) = mat z ιe₁ ιf₁ := by
    obtain ⟨hzU, e1, -, e3, -, -, -, e7, -, -⟩ := mem_ZPsub.1 hz
    obtain ⟨-, -, -, -, -, r6⟩ := U_rel hzU
    rw [e1, e3, e7] at r6
    exact bar_eq_of_add_eq_zero h (by simpa using r6)
  obtain ⟨d, hd⟩ := trace_surj (hK := h) hzf
  obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h 1 0 0
  obtain ⟨y, hy, y1, y2, y3⟩ := exists_A₂sub_coord h 0 0 d
  have hk : ⁅x, y⁆ ∈ ZPsub h := elemAbMod_ZPsub_A₂sub.2 x hx y hy
  have hmem := Subgroup.commutator_mem_commutator hx hy
  have e : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  have h1 := (A₂_mul hx hy).2.2.2
  have h2 := (A₂_mul hy hx).2.2.2
  have h3 := (mul_ZPsub_entries hk (mul_mem (A₂sub_le_U hy) (A₂sub_le_U hx))).2
  rw [← e, h1, h2] at h3
  rw [x1, x2, x3, y1, y2, y3, map_zero, map_one] at h3
  have hkz : mat ⁅x, y⁆ ιe₁ ιf₁ = mat z ιe₁ ιf₁ := by
    rw [← hd]
    linear_combination -h3 - d * (CharTwo.two_eq_zero (R := K))
  rwa [← eq_of_mem_ZPsub hk hz hkz]

theorem commutator_A₂sub_sup_N₂sub (hf : 2 ≤ f) :
    ⁅A₂sub h ⊔ N₂sub h, A₂sub h ⊔ N₂sub h⁆ = A₂sub h ⊔ N₂sub h := by
  have := h.charP
  have := h.finite
  set H := A₂sub h ⊔ N₂sub h with hH
  set C := ⁅H, H⁆ with hC
  refine le_antisymm (commutator_le_self' H) (sup_le ?_ ?_)
  ·
    have hZ : ZPsub h ≤ C ⊓ A₂sub h :=
      le_inf (ZPsub_le_commutator_A₂sub.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
        (ZPsub_le_Z₂Psub.trans Z₂Psub_le_A₂sub)
    have hinv : ∀ n ∈ N₂sub h, ∀ x ∈ C ⊓ A₂sub h, n * x * n⁻¹ ∈ C ⊓ A₂sub h :=
      fun n hn x hx => ⟨conj_mem_commutator_self (mem_sup_right hn) hx.1,
        (mem_normalizer_iff.1 (N₂sub_sup_Isub_le_normalizer_A₂sub (mem_sup_left hn)) x).1 hx.2⟩
    rcases A₂sub_irreducible hZ inf_le_right hinv with e | e
    · exfalso
      obtain ⟨a, ha⟩ := h.exists_bar_ne
      have ha0 : a ≠ 0 := fun e => ha (by rw [e, map_zero])
      have ha1 : a ≠ 1 := fun e => ha (by rw [e, map_one])
      obtain ⟨t, htN, -, ht⟩ := exists_torus_N₂sub h ha0
      obtain ⟨x, hx, x1, -, -⟩ := exists_A₂sub_coord h 1 0 0
      obtain ⟨htx, t1, -, -⟩ := ht x hx
      have hk : x⁻¹ * (t * x * t⁻¹) ∈ C ⊓ A₂sub h :=
        Subgroup.mem_inf.2 ⟨inv_mul_conj_mem_commutator (mem_sup_left hx) (mem_sup_right htN),
          mul_mem (inv_mem hx) htx⟩
      rw [e] at hk
      have hα := (A₂_inv_mul hx htx).1
      rw [t1, x1, one_mul, (mem_ZPsub.1 hk).2.1] at hα
      apply ha1
      have : a⁻¹ = 1 := by linear_combination -hα - CharTwo.two_eq_zero (R := K)
      exact inv_eq_one.1 this
    · rw [← e]
      exact inf_le_left
  · rw [← commutator_N₂sub hf]
    exact Subgroup.commutator_mono le_sup_right le_sup_right

end A₂N₂

section A₃N₁

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem exists_not_fixed_norm_ne_one (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    ∃ α : K, α ≠ 0 ∧ h.bar α ≠ α ∧ α * h.bar α ≠ 1 := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := (Nat.pow_le_pow_right (by norm_num) hf).trans_eq' (by norm_num)
  have hQ : 4 * q ≤ q * q := Nat.mul_le_mul_right _ hq4
  have hbar : h.bar (ω : K) = ((ω ^ q : Kˣ) : K) := by
    rw [UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val]
  refine ⟨ω, ω.ne_zero, fun e => ?_, fun e => ?_⟩
  · have e' : ω ^ q = ω := Units.ext (by rw [← hbar]; exact e)
    have h1 : ω ^ (q - 1) = 1 := by
      have : ω ^ (q - 1) * ω = 1 * ω := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), e', one_mul]
      exact mul_right_cancel this
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hω, sq] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    generalize q * q = Q at hle hQ
    omega
  · have h1 : ω ^ (q + 1) = 1 := by
      apply Units.ext
      rw [pow_succ', Units.val_mul, Units.val_one, ← hbar]
      exact e
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hω, sq] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    generalize q * q = Q at hle hQ
    omega

theorem mat_dHom_e₂e₂ (α : Kˣ) : mat (dHom h α) ιe₂ ιe₂ = ((α⁻¹ : Kˣ) : K) := by
  rw [dHom_apply, mat_lev]
  rfl

theorem exists_torus_N₁sub (h : UnitaryFieldData 2 f K) {α : K} (hα : α ≠ 0) :
    ∃ t ∈ N₁sub h, t ∈ Isub h ∧ mat t ιe₁ ιe₁ = α ∧ mat t ιe₂ ιe₂ = α⁻¹ ∧ mat t ιz ιz = 1 ∧
      mat t ιf₁ ιf₁ = (h.bar α)⁻¹ ∧ mat t ιf₂ ιf₂ = h.bar α := by
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus h hα (inv_ne_zero hα)
  have hbα : h.bar α ≠ 0 := (map_ne_zero h.bar).2 hα
  refine ⟨t, ?_, ht, e1, e2, ?_, e4, ?_⟩
  · have e : t = dHom h (Units.mk0 α hα) := Isub_ext ht (dHom_mem_Isub _)
      (by rw [e1, mat_dHom_e₁e₁, Units.val_mk0])
      (by rw [e2, mat_dHom_e₂e₂, Units.val_inv_eq_inv_val, Units.val_mk0])
    rw [e]
    exact dHom_mem_N₁sub _
  · rw [e3, map_inv₀]
    field_simp
  · rw [e5, map_inv₀, inv_inv]

theorem eq_of_mem_patSub_sI₆ {g g' : hypSU h 2 1} (hg : g ∈ patSub h sI₆ isPattern_sI₆)
    (hg' : g' ∈ patSub h sI₆ isPattern_sI₆) (e : mat g ιe₂ ιf₂ = mat g' ιe₂ ιf₂) : g = g' := by
  obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_patSub_sI₆.1 hg
  obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := mem_patSub_sI₆.1 hg'
  exact eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all))

theorem commutator_Ssub_sup_N₁sub (hf : 2 ≤ f) :
    ⁅Ssub h ⊔ N₁sub h, Ssub h ⊔ N₁sub h⁆ = Ssub h ⊔ N₁sub h := by
  have := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set H := Ssub h ⊔ N₁sub h with hH
  set C := ⁅H, H⁆ with hC
  obtain ⟨α, hα0, hαb, hαN⟩ := exists_not_fixed_norm_ne_one h hf
  obtain ⟨t, htN, ht, e1, e2, e3, e4, e5⟩ := exists_torus_N₁sub h hα0
  have hbα : h.bar α ≠ 0 := (map_ne_zero h.bar).2 hα0
  have htH : t ∈ H := mem_sup_right htN
  have hUH : hypUnitriangular h 2 1 ≤ H := by
    rw [U_eq_sup_Ssub_I₁.1]
    exact sup_le_sup_left patSub_sI₁_le_N₁sub _
  have hk : ∀ x ∈ hypUnitriangular h 2 1, x⁻¹ * (t * x * t⁻¹) ∈ C := fun x hx =>
    inv_mul_conj_mem_commutator (hUH hx) htH
  have hZ : ZPsub h ≤ C := by
    intro z hz
    have hcb : h.bar (mat z ιe₁ ιf₁) = mat z ιe₁ ιf₁ := by
      obtain ⟨hzU, z1, -, z3, -, -, -, z7, -, -⟩ := mem_ZPsub.1 hz
      obtain ⟨-, -, -, -, -, r6⟩ := U_rel hzU
      rw [z1, z3, z7] at r6
      exact bar_eq_of_add_eq_zero h (by simpa using r6)
    have hN : 1 + α * h.bar α ≠ 0 := fun e => hαN (by linear_combination e - h2)
    have hNb : h.bar (α * h.bar α) = α * h.bar α := by rw [map_mul, h.bar_bar, mul_comm]
    have hc'b : h.bar (mat z ιe₁ ιf₁ / (1 + α * h.bar α)) =
        mat z ιe₁ ιf₁ / (1 + α * h.bar α) := by rw [map_div₀, map_add, map_one, hNb, hcb]
    obtain ⟨x, hx, xc⟩ := exists_rootZP h hc'b
    have htx := torus_conj_mem_patSub isPattern_sZP ht hx
    have e := (mul_ZPsub_entries (inv_mem hx) (ZPsub_le_U htx)).2
    rw [torus_conj_apply ht, mat_inv_apply, e1, e4, inv_inv] at e
    simp only [hypPartner_inl, hypPartner_inr_inr] at e
    rw [xc, hc'b] at e
    have hxz : x⁻¹ * (t * x * t⁻¹) = z := eq_of_mem_ZPsub (mul_mem (inv_mem hx) htx) hz (by
      rw [e]
      field_simp)
    rw [← hxz]
    exact hk x (ZPsub_le_U hx)
  have hI₄ : patSub h sI₄ isPattern_sI₄ ≤ C := by
    intro y hy
    have hr : h.bar α + α ≠ 0 := fun e => hαb (by linear_combination e - α * h2)
    obtain ⟨x, hx, xb⟩ := exists_rootI₄ h (mat y ιe₁ ιf₂ * h.bar α / (h.bar α + α))
    have hxU := patSub_le_U _ _ hx
    have htx := torus_conj_mem_patSub isPattern_sI₄ ht hx
    have hinv := inv_mem hx
    obtain ⟨-, i1, -, i3, -, -, -, -, -⟩ := mem_patSub_sI₄.1 hinv
    obtain ⟨-, x1, -, x3, -, x5, -, -, -⟩ := mem_patSub_sI₄.1 hx
    have hxr := (U_rel hxU).2.2.2.1
    rw [x1, x3, x5, map_zero, zero_mul, zero_mul, add_zero, add_zero] at hxr
    have e := mul_e₁f₂ (patSub_le_U _ _ hinv) (patSub_le_U _ _ htx)
    rw [i1, i3, zero_mul, zero_mul, add_zero, add_zero, torus_conj_apply ht, e1, e5,
      mat_inv_apply] at e
    simp only [hypPartner_inl, hypPartner_inr_inr] at e
    rw [hxr, h.bar_bar, xb] at e
    have hxy : x⁻¹ * (t * x * t⁻¹) = y := eq_of_mem_patSub_I₄ (mul_mem hinv htx) hy (by
      rw [e]
      field_simp)
    rw [← hxy]
    exact hk x hxU
  have hI₆ : patSub h sI₆ isPattern_sI₆ ≤ C := by
    intro y hy
    have hcb : h.bar (mat y ιe₂ ιf₂) = mat y ιe₂ ιf₂ := by
      have r := (U_rel (patSub_le_U _ _ hy)).2.2.2.2.1
      rw [(mem_patSub_sI₆.1 hy).2.2.2.2.2.1, zero_mul] at r
      exact bar_eq_of_add_eq_zero h r
    have hN : α * h.bar α + 1 ≠ 0 := fun e => hαN (by linear_combination e - h2)
    have hNb : h.bar (α * h.bar α) = α * h.bar α := by rw [map_mul, h.bar_bar, mul_comm]
    have hc'b : h.bar (mat y ιe₂ ιf₂ * (α * h.bar α) / (α * h.bar α + 1)) =
        mat y ιe₂ ιf₂ * (α * h.bar α) / (α * h.bar α + 1) := by
      rw [map_div₀, map_mul, map_add, map_one, hNb, hcb]
    obtain ⟨x, hx, xc⟩ := exists_rootI₆ h hc'b
    have htx := torus_conj_mem_patSub isPattern_sI₆ ht hx
    have hinv := inv_mem hx
    have e := mul_e₂f₂ (patSub_le_U _ _ hinv) (patSub_le_U _ _ htx)
    rw [(mem_patSub_sI₆.1 hinv).2.2.2.2.2.1, zero_mul, add_zero, torus_conj_apply ht, e2, e5,
      mat_inv_apply] at e
    simp only [hypPartner_inl, hypPartner_inr_inr] at e
    rw [xc, hc'b] at e
    have hxy : x⁻¹ * (t * x * t⁻¹) = y := eq_of_mem_patSub_sI₆ (mul_mem hinv htx) hy (by
      rw [e]
      field_simp)
    rw [← hxy]
    exact hk x (patSub_le_U _ _ hx)
  have hI₅ : patSub h sI₅ isPattern_sI₅ ≤ C := by
    intro y hy
    have h1α : 1 + α ≠ 0 := fun e => hαb (by
      have : α = 1 := by linear_combination e - h2
      rw [this, map_one])
    obtain ⟨c', hc'⟩ := trace_surj (hK := h)
      (a := mat y ιe₁ ιz / (1 + α) * h.bar (mat y ιe₁ ιz / (1 + α)))
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨x, hx, xu, -⟩ := exists_rootI₅ h hc'
    have hxU := patSub_le_U _ _ hx
    have htx := torus_conj_mem_patSub isPattern_sI₅ ht hx
    have hinv := inv_mem hx
    have hkx := mul_mem hinv htx
    obtain ⟨-, i1, -, -, -, -, -, -⟩ := mem_patSub_sI₅.1 hinv
    obtain ⟨-, x1, -, x3, -, -, -, -⟩ := mem_patSub_sI₅.1 hx
    have hxr := (U_rel hxU).2.2.1
    rw [x1, x3, map_zero, zero_mul, add_zero] at hxr
    have e := mul_e₁z (patSub_le_U _ _ hinv) (patSub_le_U _ _ htx)
    rw [i1, zero_mul, add_zero, torus_conj_apply ht, e1, e3, inv_one, mul_one, mat_inv_apply] at e
    simp only [hypPartner_inl, hypPartner_inr_inl] at e
    rw [hxr, h.bar_bar, xu] at e
    set k := x⁻¹ * (t * x * t⁻¹) with hkdef
    have hyk := mul_mem (inv_mem hy) hkx
    obtain ⟨hykU, j1, j2, j3, j4, j5, j6, j7⟩ := mem_patSub_sI₅.1 hyk
    obtain ⟨-, w1, -, -, -, -, -, -⟩ := mem_patSub_sI₅.1 (inv_mem hy)
    have hz1 : mat (y⁻¹ * k) ιe₁ ιz = 0 := by
      rw [mul_e₁z (patSub_le_U _ _ (inv_mem hy)) (patSub_le_U _ _ hkx), w1, zero_mul, add_zero,
        e, mat_inv_apply]
      simp only [hypPartner_inl, hypPartner_inr_inl]
      have hyr := (U_rel (patSub_le_U _ _ hy)).2.2.1
      obtain ⟨-, y1, -, y3, -, -, -, -⟩ := mem_patSub_sI₅.1 hy
      rw [y1, y3, map_zero, zero_mul, add_zero] at hyr
      rw [hyr, h.bar_bar]
      field_simp
      linear_combination (mat y ιe₁ ιz) * h2
    have hzr := (U_rel hykU).2.2.1
    rw [hz1, j1, map_zero, zero_mul, add_zero] at hzr
    have hzP : y⁻¹ * k ∈ ZPsub h := mem_ZPsub.2 ⟨hykU, j1, j2, hz1, hzr, j3, j4, j5, j6, j7⟩
    rw [show y = k * (y⁻¹ * k)⁻¹ by group]
    exact mul_mem (hk x hxU) (inv_mem (hZ hzP))
  have hI₂ : patSub h sI₂ isPattern_sI₂ ≤ C := by
    intro y hy
    have hry : rSU h * y * (rSU h)⁻¹ ∈ C := hI₅ (conj_perm_mem_patSub σr_σr σr_partner mat_rSU
      isPattern_sI₂ isPattern_sI₅ (by decide) hy)
    have hrH : (rSU h)⁻¹ ∈ H := inv_mem (mem_sup_right rSU_mem_N₁sub)
    have := conj_mem_commutator_self hrH hry
    rwa [show (rSU h)⁻¹ * (rSU h * y * (rSU h)⁻¹) * (rSU h)⁻¹⁻¹ = y by group] at this
  refine le_antisymm (commutator_le_self' H) (sup_le ?_ ?_)
  · rw [Ssub_eq_sup_Vsub, Vsub_eq_sup_I₆.1, Z₂Psub_eq_sup_I₄.1]
    exact sup_le (sup_le (sup_le (sup_le hZ hI₄) hI₆) hI₂) hI₅
  · rw [← commutator_N₁sub (h := h)]
    exact Subgroup.commutator_mono le_sup_right le_sup_right

end A₃N₁

end CFSG.LocalAnalysis.EvenBN.U5
