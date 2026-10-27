module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightTri

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure AltSetup (E : Subgroup Γ) (n : ℕ) where
  W : Subgroup Γ
  hWE : W ≤ E
  hEW : E ≤ Subgroup.normalizer (W : Set Γ)
  hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  hW2 : IsPGroup 2 ↥W
  hn3 : 3 ≤ n
  βe : ↥W ≃* ↥(coreMod n)
  Ψ : ↥E →* Equiv.Perm (Fin n)
  hΨ : ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
    βe ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = coreAct n (Ψ e) (βe w)
  hker : ∀ e : ↥E, Ψ e = 1 → (e : Γ) ∈ W

namespace AltSetup

variable {E : Subgroup Γ} {n : ℕ} (M : AltSetup E n)

theorem conj_mem (e : ↥E) {w : Γ} (hw : w ∈ M.W) : (e : Γ) * w * (e : Γ)⁻¹ ∈ M.W :=
  (Subgroup.mem_normalizer_iff.mp (M.hEW e.2) w).mp hw

@[expose] noncomputable def conjW (e : ↥E) (w : ↥M.W) : ↥M.W :=
  ⟨(e : Γ) * w * (e : Γ)⁻¹, M.conj_mem e w.2⟩

theorem βe_conjW (e : ↥E) (w : ↥M.W) : M.βe (M.conjW e w) = coreAct n (M.Ψ e) (M.βe w) :=
  M.hΨ e w _

theorem Ψ_eq_one_of_mem {w : Γ} (hw : w ∈ M.W) : M.Ψ ⟨w, M.hWE hw⟩ = 1 := by
  apply coreAct_injective M.hn3
  rw [map_one]
  refine MulEquiv.ext fun v => ?_
  obtain ⟨w', rfl⟩ := M.βe.surjective v
  have h1 := M.hΨ ⟨w, M.hWE hw⟩ w' (M.conj_mem _ w'.2)
  have h2 : (⟨(w : Γ) * (w' : Γ) * (w : Γ)⁻¹, M.conj_mem ⟨w, M.hWE hw⟩ w'.2⟩ : ↥M.W) = w' := by
    apply Subtype.ext
    show (w : Γ) * (w' : Γ) * (w : Γ)⁻¹ = w'
    rw [M.hWab w hw w' w'.2]
    group
  rw [h2] at h1
  exact h1.symm

theorem mem_W_iff (e : ↥E) : (e : Γ) ∈ M.W ↔ M.Ψ e = 1 :=
  ⟨fun h => M.Ψ_eq_one_of_mem h, M.hker e⟩

@[expose] def wSub (p : Fin 3 → Fin n) : Subgroup Γ where
  carrier := {w | ∃ hw : w ∈ M.W, M.βe ⟨w, hw⟩ ∈ suppSub (triSet p)}
  one_mem' := ⟨M.W.one_mem, by
    have : M.βe ⟨1, M.W.one_mem⟩ = 1 := map_one M.βe
    rw [this]
    exact (suppSub (triSet p)).one_mem⟩
  mul_mem' := fun {x y} ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨M.W.mul_mem hx hy, by
    have : M.βe ⟨x * y, M.W.mul_mem hx hy⟩ = M.βe ⟨x, hx⟩ * M.βe ⟨y, hy⟩ :=
      map_mul M.βe (⟨x, hx⟩ : ↥M.W) ⟨y, hy⟩
    rw [this]
    exact (suppSub (triSet p)).mul_mem hx' hy'⟩
  inv_mem' := fun {x} ⟨hx, hx'⟩ => ⟨M.W.inv_mem hx, by
    have : M.βe ⟨x⁻¹, M.W.inv_mem hx⟩ = (M.βe ⟨x, hx⟩)⁻¹ := map_inv M.βe (⟨x, hx⟩ : ↥M.W)
    rw [this]
    exact (suppSub (triSet p)).inv_mem hx'⟩

variable {M} {p : Fin 3 → Fin n}

theorem wSub_le_W : M.wSub p ≤ M.W := fun _ hw => hw.1

theorem wSub_le_E : M.wSub p ≤ E := fun _ hw => M.hWE hw.1

theorem conj_mem_wSub (e : ↥E) (he : M.Ψ e ∈ setStab (triSet p)) {w : Γ} (hw : w ∈ M.wSub p) :
    (e : Γ) * w * (e : Γ)⁻¹ ∈ M.wSub p := by
  obtain ⟨hwW, hwv⟩ := hw
  refine ⟨M.conj_mem e hwW, ?_⟩
  have h1 := M.βe_conjW e ⟨w, hwW⟩
  have h2 : (M.conjW e ⟨w, hwW⟩ : ↥M.W) =
      ⟨(e : Γ) * w * (e : Γ)⁻¹, M.conj_mem e hwW⟩ := rfl
  rw [h2] at h1
  rw [h1]
  exact coreAct_mem_suppSub he hwv

theorem exists_lift_cube_one {d : Equiv.Perm (Fin n)} (hd : d.IsThreeCycle) {e₀ : ↥E}
    (he₀ : M.Ψ e₀ = d) : ∃ g : ↥E, g ^ 3 = 1 ∧ M.Ψ g = d := by
  have hd3 : d ^ 3 = 1 := by
    rw [← hd.orderOf]
    exact pow_orderOf_eq_one d
  have hW3 : ((e₀ ^ 3 : ↥E) : Γ) ∈ M.W := by
    apply M.hker
    rw [map_pow, he₀, hd3]
  obtain ⟨k, hk⟩ := M.hW2 (⟨((e₀ ^ 3 : ↥E) : Γ), hW3⟩ : ↥M.W)
  have hk' : (e₀ ^ 3) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg (fun x : ↥M.W => ((x : ↥M.W) : Γ)) hk
    simpa using this
  refine ⟨e₀ ^ 4 ^ k, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, show 4 ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num,
      pow_mul, hk', one_pow]
  · rw [map_pow, he₀, ← pow_mod_orderOf, hd.orderOf]
    have : 4 ^ k % 3 = 1 := by simp [Nat.pow_mod]
    rw [this, pow_one]

theorem Ψ_conj {y : Γ} (hyW : y ∈ Subgroup.normalizer (M.W : Set Γ)) {s : Equiv.Perm (Fin n)}
    (hs : ∀ (w : ↥M.W) (hw : y * (w : Γ) * y⁻¹ ∈ M.W),
      M.βe ⟨y * (w : Γ) * y⁻¹, hw⟩ = coreAct n s (M.βe w)) (e : ↥E)
    (he' : y * (e : Γ) * y⁻¹ ∈ E) :
    M.Ψ ⟨y * (e : Γ) * y⁻¹, he'⟩ = s * M.Ψ e * s⁻¹ := by
  apply coreAct_injective M.hn3
  refine MulEquiv.ext fun v => ?_
  obtain ⟨w, rfl⟩ := M.βe.surjective v
  have hyi : y⁻¹ ∈ Subgroup.normalizer (M.W : Set Γ) := (Subgroup.normalizer _).inv_mem hyW
  have hw₁ : y⁻¹ * (w : Γ) * y⁻¹⁻¹ ∈ M.W :=
    (Subgroup.mem_normalizer_iff.mp hyi (w : Γ)).mp w.2
  set w₁ : ↥M.W := ⟨y⁻¹ * (w : Γ) * y⁻¹⁻¹, hw₁⟩ with hw₁def
  have hs₁ := hs w₁ (by
    have := (Subgroup.mem_normalizer_iff.mp hyW (w₁ : Γ)).mp w₁.2
    exact this)
  have hyw₁ : (⟨y * (w₁ : Γ) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyW (w₁ : Γ)).mp w₁.2⟩ :
      ↥M.W) = w := by
    apply Subtype.ext
    show y * (y⁻¹ * (w : Γ) * y⁻¹⁻¹) * y⁻¹ = w
    group
  rw [hyw₁] at hs₁
  have hw₁β : M.βe w₁ = coreAct n s⁻¹ (M.βe w) := by
    rw [hs₁, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hw₂ := M.βe_conjW e w₁
  have hs₂ := hs (M.conjW e w₁) (by
    have := (Subgroup.mem_normalizer_iff.mp hyW ((M.conjW e w₁ : ↥M.W) : Γ)).mp
      (M.conjW e w₁).2
    exact this)
  have hconj : (⟨y * ((M.conjW e w₁ : ↥M.W) : Γ) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyW
      ((M.conjW e w₁ : ↥M.W) : Γ)).mp (M.conjW e w₁).2⟩ : ↥M.W) =
      M.conjW ⟨y * (e : Γ) * y⁻¹, he'⟩ w := by
    apply Subtype.ext
    show y * ((e : Γ) * (y⁻¹ * (w : Γ) * y⁻¹⁻¹) * (e : Γ)⁻¹) * y⁻¹ =
      y * (e : Γ) * y⁻¹ * (w : Γ) * (y * (e : Γ) * y⁻¹)⁻¹
    group
  rw [hconj] at hs₂
  have h3 := M.βe_conjW ⟨y * (e : Γ) * y⁻¹, he'⟩ w
  rw [h3] at hs₂
  rw [hs₂, hw₂, hw₁β]
  simp [MulAut.mul_apply, map_mul]

theorem eq_of_βe_eq {w w' : Γ} (hw : w ∈ M.W) (hw' : w' ∈ M.W)
    (h : M.βe ⟨w, hw⟩ = M.βe ⟨w', hw'⟩) : w = w' :=
  congrArg Subtype.val (M.βe.injective h)

theorem exists_wSub_of_mem_suppSub {p : Fin 3 → Fin n} {v : ↥(coreMod n)}
    (hv : v ∈ suppSub (triSet p)) :
    ∃ (w : Γ) (hw : w ∈ M.W), w ∈ M.wSub p ∧ M.βe ⟨w, hw⟩ = v := by
  have h1 : M.βe (M.βe.symm v) = v := M.βe.apply_symm_apply v
  refine ⟨((M.βe.symm v : ↥M.W) : Γ), (M.βe.symm v).2, ⟨(M.βe.symm v).2, ?_⟩, h1⟩
  have : (⟨((M.βe.symm v : ↥M.W) : Γ), (M.βe.symm v).2⟩ : ↥M.W) = M.βe.symm v := rfl
  rw [this, h1]
  exact hv

end AltSetup

end CFSG.CGT.PushingUpLit.BHS6
