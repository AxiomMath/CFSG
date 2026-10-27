module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Linear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Setup

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

structure i285_Setup (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] where
  X : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)
  φ : Module.Dual (ZMod 2) M
  a : M
  hφa : φ a = 0
  hφ : φ ≠ 0
  ha : a ≠ 0
  hτX : tv φ a hφa ∈ X
  hO2 : ∀ K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M), K ≤ X →
    (∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) → (∀ k ∈ K, k ^ 4 = 1) → K = ⊥

namespace i285_Setup

variable (S : i285_Setup M)

@[expose] def τ : 𝔾 := tv S.φ S.a S.hφa

@[expose] def D : Set 𝔾 := {τ' | ∃ g ∈ S.X, τ' = g⁻¹ * S.τ * g}

@[expose] def W : Subgroup 𝔾 := Subgroup.closure S.D

@[expose] def P : Submodule (ZMod 2) M :=
  Submodule.span (ZMod 2) {v | ∃ g ∈ S.X, v = (g : M →ₗ[ZMod 2] M) S.a}

@[expose] def Q : Submodule (ZMod 2) M where
  carrier := {v | ∀ g ∈ S.X, S.φ ((g : M →ₗ[ZMod 2] M) v) = 0}
  add_mem' {u v} hu hv g hg := by rw [map_add, map_add, hu g hg, hv g hg, add_zero]
  zero_mem' g _ := by rw [map_zero, map_zero]
  smul_mem' c v hv g hg := by rw [map_smul, map_smul, hv g hg, smul_zero]

theorem τ_apply (v : M) : (S.τ : M →ₗ[ZMod 2] M) v = v + S.φ v • S.a := tv_apply _ _ _ v

theorem τ_ne_one : S.τ ≠ 1 := tv_ne_one S.hφa S.hφ S.ha

theorem τ_mem_D : S.τ ∈ S.D := ⟨1, S.X.one_mem, by group⟩

theorem τ_mem_W : S.τ ∈ S.W := Subgroup.subset_closure S.τ_mem_D

theorem conj_apply (g : 𝔾) (v : M) :
    ((g⁻¹ * S.τ * g : 𝔾) : M →ₗ[ZMod 2] M) v =
      v + S.φ ((g : M →ₗ[ZMod 2] M) v) • ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) S.a := by
  rw [i285_mul_apply, i285_mul_apply, τ_apply, map_add, map_smul, i285_inv_apply_apply]

theorem D_subset_X : S.D ⊆ S.X := by
  rintro _ ⟨g, hg, rfl⟩
  exact S.X.mul_mem (S.X.mul_mem (S.X.inv_mem hg) S.hτX) hg

theorem W_le_X : S.W ≤ S.X := (Subgroup.closure_le _).2 S.D_subset_X

theorem conj_mem_D {x : 𝔾} (hx : x ∈ S.X) {d : 𝔾} (hd : d ∈ S.D) : x * d * x⁻¹ ∈ S.D := by
  obtain ⟨g, hg, rfl⟩ := hd
  exact ⟨g * x⁻¹, S.X.mul_mem hg (S.X.inv_mem hx), by group⟩

theorem conj_mem_W {x : 𝔾} (hx : x ∈ S.X) {w : 𝔾} (hw : w ∈ S.W) : x * w * x⁻¹ ∈ S.W := by
  induction hw using Subgroup.closure_induction with
  | mem d hd => exact Subgroup.subset_closure (S.conj_mem_D hx hd)
  | one => simp
  | mul u w _ _ hu hw =>
    have := S.W.mul_mem hu hw
    convert this using 1
    group
  | inv u _ hu =>
    have := S.W.inv_mem hu
    rwa [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc] at this

theorem D_mul_self {d : 𝔾} (hd : d ∈ S.D) : d * d = 1 := by
  obtain ⟨g, hg, rfl⟩ := hd
  have : S.τ * S.τ = 1 := tv_mul_self _ _ _
  calc g⁻¹ * S.τ * g * (g⁻¹ * S.τ * g) = g⁻¹ * (S.τ * S.τ) * g := by group
    _ = 1 := by rw [this]; group

theorem apply_a_mem_P {g : 𝔾} (hg : g ∈ S.X) : (g : M →ₗ[ZMod 2] M) S.a ∈ S.P :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem X_le_stab_P : S.X ≤ i285_stab S.P := by
  apply i285_le_stab
  intro x hx v hv
  have : S.P.map (x : M →ₗ[ZMod 2] M) ≤ S.P := by
    rw [P, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact S.apply_a_mem_P (S.X.mul_mem hx hg)
  exact this ⟨v, hv, rfl⟩

theorem X_le_stab_Q : S.X ≤ i285_stab S.Q := by
  apply i285_le_stab
  intro x hx v hv g hg
  exact hv (g * x) (S.X.mul_mem hg hx)

theorem D_subset_triv_P : S.D ⊆ i285_triv S.P := by
  rintro _ ⟨g, hg, rfl⟩ v
  rw [S.conj_apply, add_sub_cancel_left]
  exact S.P.smul_mem _ (S.apply_a_mem_P (S.X.inv_mem hg))

theorem D_subset_fix_Q : S.D ⊆ i285_fix S.Q := by
  rintro _ ⟨g, hg, rfl⟩ v hv
  rw [S.conj_apply, hv g hg, zero_smul, add_zero]

theorem W_le_triv_P : S.W ≤ i285_triv S.P := (Subgroup.closure_le _).2 S.D_subset_triv_P

theorem W_le_fix_Q : S.W ≤ i285_fix S.Q := (Subgroup.closure_le _).2 S.D_subset_fix_Q

theorem W_le_stab_P : S.W ≤ i285_stab S.P := S.W_le_triv_P.trans (i285_triv_le_stab _)

theorem le_ker_of_not_mem {T : Submodule (ZMod 2) M}
    (hT : ∀ v ∈ T, (S.τ : M →ₗ[ZMod 2] M) v ∈ T) (ha : S.a ∉ T) {v : M} (hv : v ∈ T) :
    S.φ v = 0 := by
  rcases zmod2_eq_zero_or_one (S.φ v) with h | h
  · exact h
  · exfalso
    apply ha
    have := T.sub_mem (hT v hv) hv
    rwa [S.τ_apply, add_sub_cancel_left, h, one_smul] at this

theorem le_Q_of_le_ker {T : Submodule (ZMod 2) M} (hT : S.X ≤ i285_stab T)
    (h : ∀ v ∈ T, S.φ v = 0) : T ≤ S.Q := by
  intro v hv g hg
  exact h _ ((hT hg v).2 hv)

theorem not_P_le_Q : ¬ S.P ≤ S.Q := by
  intro hPQ
  have hU : S.W ≤ i285_U3 S.P S.Q := by
    intro w hw
    refine ⟨S.W_le_triv_P hw, fun v hv => ?_, S.W_le_fix_Q hw⟩
    rw [S.W_le_fix_Q hw v (hPQ hv), sub_self]
    exact S.Q.zero_mem
  have hbot := S.hO2 S.W S.W_le_X (fun x hx w hw => S.conj_mem_W hx hw)
    (fun k hk => i285_pow_four (hU hk))
  apply S.τ_ne_one
  have := S.τ_mem_W
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem a_not_mem_Q : S.a ∉ S.Q := by
  intro haQ
  apply S.not_P_le_Q
  rw [P, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  exact (S.X_le_stab_Q hg _).2 haQ

theorem apply_a_not_mem_Q {g : 𝔾} (hg : g ∈ S.X) : (g : M →ₗ[ZMod 2] M) S.a ∉ S.Q := fun h =>
  S.a_not_mem_Q ((S.X_le_stab_Q hg _).1 h)

theorem eq_of_stab {T : Submodule (ZMod 2) M} (hT : S.X ≤ i285_stab T) (h1 : S.P ⊓ S.Q ≤ T)
    (h2 : T ≤ S.P) : T = S.P ⊓ S.Q ∨ T = S.P := by
  by_cases haT : S.a ∈ T
  · right
    refine le_antisymm h2 ?_
    rw [P, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact (hT hg _).2 haT
  · left
    refine le_antisymm (le_inf h2 (S.le_Q_of_le_ker hT fun v hv => ?_)) h1
    exact S.le_ker_of_not_mem (fun u hu => (hT S.hτX u).2 hu) haT hv

theorem U3_conj {x : 𝔾} (hx : x ∈ S.X) {k : 𝔾} (hk : k ∈ i285_U3 S.P S.Q) :
    x * k * x⁻¹ ∈ i285_U3 S.P S.Q := by
  obtain ⟨h1, h2, h3⟩ := hk
  have hP := S.X_le_stab_P hx
  have hQ := S.X_le_stab_Q hx
  have e : ∀ v, ((x * k * x⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v - v =
      (x : M →ₗ[ZMod 2] M) ((k : M →ₗ[ZMod 2] M) (((x⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v) -
        ((x⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v) := by
    intro v
    rw [map_sub, i285_apply_inv_apply]
    rfl
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [e]
    exact (hP _).2 (h1 _)
  · rw [e]
    exact (hQ _).2 (h2 _ ((S.X_le_stab_P (S.X.inv_mem hx) _).2 hv))
  · change (x : M →ₗ[ZMod 2] M) ((k : M →ₗ[ZMod 2] M) (((x⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v)) = v
    rw [h3 _ ((S.X_le_stab_Q (S.X.inv_mem hx) _).2 hv), i285_apply_inv_apply]

theorem faithful {w : 𝔾} (hw : w ∈ S.W) (h : ∀ v ∈ S.P, (w : M →ₗ[ZMod 2] M) v - v ∈ S.Q) :
    w = 1 := by
  have hK := S.hO2 (S.W ⊓ i285_U3 S.P S.Q) (inf_le_left.trans S.W_le_X)
    (fun x hx k hk => ⟨S.conj_mem_W hx hk.1, S.U3_conj hx hk.2⟩)
    (fun k hk => i285_pow_four hk.2)
  have : w ∈ S.W ⊓ i285_U3 S.P S.Q := ⟨hw, S.W_le_triv_P hw, h, S.W_le_fix_Q hw⟩
  rw [hK] at this
  exact Subgroup.mem_bot.1 this

@[expose] def IsMin (R : Submodule (ZMod 2) M) : Prop :=
  S.W ≤ i285_stab R ∧ S.P ⊓ S.Q < R ∧ R ≤ S.P ∧
    ∀ T : Submodule (ZMod 2) M, S.W ≤ i285_stab T → S.P ⊓ S.Q < T → T ≤ R → T = R

theorem exists_isMin [Finite M] : ∃ R, S.IsMin R := by
  have : Finite (Submodule (ZMod 2) M) :=
    Finite.of_injective (fun T : Submodule (ZMod 2) M => (T : Set M)) SetLike.coe_injective
  obtain ⟨R, ⟨hR1, hR2, hR3⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {R : Submodule (ZMod 2) M | S.W ≤ i285_stab R ∧ S.P ⊓ S.Q < R ∧ R ≤ S.P}
    ⟨S.P, S.W_le_stab_P, inf_lt_left.2 S.not_P_le_Q, le_rfl⟩
  refine ⟨R, hR1, hR2, hR3, fun T hT1 hT2 hT3 => ?_⟩
  by_contra hne
  exact hmin T ⟨hT1, hT2, hT3.trans hR3⟩ (lt_of_le_of_ne hT3 hne)

theorem map_inf_PQ {x : 𝔾} (hx : x ∈ S.X) :
    (S.P ⊓ S.Q).map (x : M →ₗ[ZMod 2] M) = S.P ⊓ S.Q :=
  i285_map_eq_of_stab (i285_stab_inf (S.X_le_stab_P hx) (S.X_le_stab_Q hx))

theorem W_le_stab_map {x : 𝔾} (hx : x ∈ S.X) {T : Submodule (ZMod 2) M}
    (hT : S.W ≤ i285_stab T) : S.W ≤ i285_stab (T.map (x : M →ₗ[ZMod 2] M)) := fun w hw =>
  i285_mem_stab_map (hT (by simpa using S.conj_mem_W (S.X.inv_mem hx) hw))

theorem isMin_map {R : Submodule (ZMod 2) M} (hR : S.IsMin R) {x : 𝔾} (hx : x ∈ S.X) :
    S.IsMin (R.map (x : M →ₗ[ZMod 2] M)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  have hxi := S.X.inv_mem hx
  refine ⟨S.W_le_stab_map hx h1, ?_, ?_, fun T hT1 hT2 hT3 => ?_⟩
  · rw [← S.map_inf_PQ hx]
    exact (i285_map_lt_map_iff x).2 h2
  · rw [← i285_map_eq_of_stab (S.X_le_stab_P hx)]
    exact Submodule.map_mono h3
  · have hTx : T.map ((x⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) = R := by
      refine h4 _ (S.W_le_stab_map hxi hT1) ?_ ?_
      · rw [← S.map_inf_PQ hxi]
        exact (i285_map_lt_map_iff _).2 hT2
      · rw [← i285_map_inv_map x R]
        exact Submodule.map_mono hT3
    rw [← hTx, i285_map_map_inv]

theorem isMin_inf_eq {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (hne : R ≠ R') : R ⊓ R' = S.P ⊓ S.Q := by
  have hle : S.P ⊓ S.Q ≤ R ⊓ R' := le_inf hR.2.1.le hR'.2.1.le
  refine (eq_of_le_of_not_lt hle fun hlt => hne ?_).symm
  have hW : S.W ≤ i285_stab (R ⊓ R') := fun w hw => i285_stab_inf (hR.1 hw) (hR'.1 hw)
  rw [← hR.2.2.2 _ hW hlt inf_le_left, hR'.2.2.2 _ hW hlt inf_le_right]

theorem isMin_iSup_map {R : Submodule (ZMod 2) M} (hR : S.IsMin R) :
    (⨆ x : ↥S.X, R.map ((x : 𝔾) : M →ₗ[ZMod 2] M)) = S.P := by
  set T := ⨆ x : ↥S.X, R.map ((x : 𝔾) : M →ₗ[ZMod 2] M) with hT
  have hRT : R ≤ T := by
    have := le_iSup (fun x : ↥S.X => R.map ((x : 𝔾) : M →ₗ[ZMod 2] M)) ⟨1, S.X.one_mem⟩
    rwa [i285_map_one] at this
  have hstab : S.X ≤ i285_stab T := by
    apply i285_le_stab
    intro y hy v hv
    have : T.map (y : M →ₗ[ZMod 2] M) ≤ T := by
      rw [hT, Submodule.map_iSup]
      refine iSup_le fun x => ?_
      rw [← i285_map_mul]
      exact le_iSup_of_le ⟨y * x, S.X.mul_mem hy x.2⟩ le_rfl
    exact this ⟨v, hv, rfl⟩
  have hTP : T ≤ S.P := iSup_le fun x => by
    rw [← i285_map_eq_of_stab (S.X_le_stab_P x.2)]
    exact Submodule.map_mono hR.2.2.1
  rcases S.eq_of_stab hstab (hR.2.1.le.trans hRT) hTP with h | h
  · exact absurd (h ▸ hRT) (not_le_of_gt hR.2.1)
  · exact h

@[expose] def T (R : Submodule (ZMod 2) M) : Set 𝔾 :=
  {d | d ∈ S.D ∧ ∃ v ∈ R, (d : M →ₗ[ZMod 2] M) v ≠ v}

@[expose] def H (R : Submodule (ZMod 2) M) : Subgroup 𝔾 := Subgroup.closure (S.T R)

theorem T_subset_D (R : Submodule (ZMod 2) M) : S.T R ⊆ S.D := fun _ hd => hd.1

theorem H_le_W (R : Submodule (ZMod 2) M) : S.H R ≤ S.W := Subgroup.closure_mono (S.T_subset_D R)

theorem H_le_X (R : Submodule (ZMod 2) M) : S.H R ≤ S.X := (S.H_le_W R).trans S.W_le_X

theorem center_mem {g : 𝔾} {R : Submodule (ZMod 2) M}
    (hR : ∀ v ∈ R, ((g⁻¹ * S.τ * g : 𝔾) : M →ₗ[ZMod 2] M) v ∈ R)
    (hv : ∃ v ∈ R, ((g⁻¹ * S.τ * g : 𝔾) : M →ₗ[ZMod 2] M) v ≠ v) :
    ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) S.a ∈ R := by
  obtain ⟨v, hvR, hne⟩ := hv
  have h1 : S.φ ((g : M →ₗ[ZMod 2] M) v) = 1 := by
    rcases zmod2_eq_zero_or_one (S.φ ((g : M →ₗ[ZMod 2] M) v)) with h | h
    · exfalso
      apply hne
      rw [S.conj_apply, h, zero_smul, add_zero]
    · exact h
  have := R.sub_mem (hR v hvR) hvR
  rwa [S.conj_apply, add_sub_cancel_left, h1, one_smul] at this

theorem fix_of_ne {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (hne : R ≠ R') {d : 𝔾} (hd : d ∈ S.T R) : ∀ v ∈ R', (d : M →ₗ[ZMod 2] M) v = v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨g, hg, rfl⟩, hv⟩ := hd
  have hdW : g⁻¹ * S.τ * g ∈ S.W := Subgroup.subset_closure ⟨g, hg, rfl⟩
  have h1 := S.center_mem (fun v hv => (hR.1 hdW v).2 hv) hv
  have h2 := S.center_mem (fun v hv => (hR'.1 hdW v).2 hv) hcon
  have h3 : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) S.a ∈ R ⊓ R' := ⟨h1, h2⟩
  rw [S.isMin_inf_eq hR hR' hne] at h3
  exact S.apply_a_not_mem_Q (S.X.inv_mem hg) h3.2

theorem H_le_fix {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (hne : R ≠ R') : S.H R ≤ i285_fix R' :=
  (Subgroup.closure_le _).2 fun _ hd => S.fix_of_ne hR hR' hne hd

theorem T_comm {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (hne : R ≠ R') {d e : 𝔾} (hd : d ∈ S.T R) (he : e ∈ S.T R') : d * e = e * d := by
  have hdfix := S.fix_of_ne hR hR' hne hd
  have hefix := S.fix_of_ne hR' hR (Ne.symm hne) he
  obtain ⟨⟨g, hg, rfl⟩, hdv⟩ := hd
  obtain ⟨⟨h, hh, rfl⟩, hev⟩ := he
  have hdW : g⁻¹ * S.τ * g ∈ S.W := Subgroup.subset_closure ⟨g, hg, rfl⟩
  have heW : h⁻¹ * S.τ * h ∈ S.W := Subgroup.subset_closure ⟨h, hh, rfl⟩
  have hα := S.center_mem (fun v hv => (hR.1 hdW v).2 hv) hdv
  have hβ := S.center_mem (fun v hv => (hR'.1 heW v).2 hv) hev
  exact i285_comm_of_fix (S.conj_apply g) (S.conj_apply h) (hdfix _ hβ) (hefix _ hα)

theorem H_le_centralizer {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R')
    (hne : R ≠ R') : S.H R ≤ Subgroup.centralizer (S.H R' : Set 𝔾) :=
  i285_closure_le_centralizer fun _ hd _ he => S.T_comm hR hR' hne hd he

theorem D_mem_stab {d : 𝔾} (hd : d ∈ S.D) {T' : Submodule (ZMod 2) M}
    (h : ∀ v ∈ T', (d : M →ₗ[ZMod 2] M) v ∈ T') : d ∈ i285_stab T' := by
  intro v
  refine ⟨fun hv => ?_, h v⟩
  have := h _ hv
  rwa [← i285_mul_apply, S.D_mul_self hd, i285_one_apply] at this

theorem W_le_stab_of_H {R T' : Submodule (ZMod 2) M} (hT' : T' ≤ R)
    (h : ∀ g ∈ S.H R, ∀ v ∈ T', (g : M →ₗ[ZMod 2] M) v ∈ T') : S.W ≤ i285_stab T' := by
  rw [W, Subgroup.closure_le]
  intro d hd
  apply S.D_mem_stab hd
  by_cases hdT : d ∈ S.T R
  · exact h d (Subgroup.subset_closure hdT)
  · intro v hv
    have : ∀ u ∈ R, (d : M →ₗ[ZMod 2] M) u = u := by
      by_contra hcon
      push Not at hcon
      exact hdT ⟨hd, hcon⟩
    rw [this v (hT' hv)]
    exact hv

theorem exists_mem_T {R : Submodule (ZMod 2) M} (hR : S.IsMin R) {d : 𝔾} (hd : d ∈ S.D) :
    ∃ x ∈ S.X, d ∈ S.T (R.map (x : M →ₗ[ZMod 2] M)) := by
  by_contra hcon
  push Not at hcon
  have hfix : S.P ≤ i285_fixSub d := by
    rw [← S.isMin_iSup_map hR]
    refine iSup_le fun x => ?_
    intro v hv
    rw [i285_mem_fixSub]
    by_contra hne
    exact hcon x x.2 ⟨hd, v, hv, hne⟩
  obtain ⟨g, hg, rfl⟩ := hd
  apply S.not_P_le_Q
  have hker : ∀ v ∈ S.P, S.φ v = 0 := by
    intro v hv
    have hv' : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v ∈ S.P := (S.X_le_stab_P (S.X.inv_mem hg) v).2 hv
    have := i285_mem_fixSub.1 (hfix hv')
    rw [S.conj_apply, i285_apply_inv_apply, add_eq_left] at this
    rcases zmod2_eq_zero_or_one (S.φ v) with h | h
    · exact h
    · exfalso
      rw [h, one_smul] at this
      apply S.ha
      have := congrArg (g : M →ₗ[ZMod 2] M) this
      rwa [i285_apply_inv_apply, map_zero] at this
  exact S.le_Q_of_le_ker S.X_le_stab_P hker

theorem T_conj {g : 𝔾} (hg : g ∈ S.X) (R : Submodule (ZMod 2) M) :
    (MulAut.conj g⁻¹) '' S.T R = S.T (R.map ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M)) := by
  ext e
  constructor
  · rintro ⟨d, ⟨hd, v, hv, hne⟩, rfl⟩
    rw [MulAut.conj_apply]
    refine ⟨by simpa using S.conj_mem_D (S.X.inv_mem hg) hd, ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v,
      ⟨v, hv, rfl⟩, ?_⟩
    rw [inv_inv, i285_mul_apply, i285_mul_apply, i285_apply_inv_apply]
    intro heq
    apply hne
    have := congrArg (g : M →ₗ[ZMod 2] M) heq
    rwa [i285_apply_inv_apply, i285_apply_inv_apply] at this
  · rintro ⟨he, u, hu, hne⟩
    refine ⟨g * e * g⁻¹, ⟨S.conj_mem_D hg he, (g : M →ₗ[ZMod 2] M) u, ?_, ?_⟩, ?_⟩
    · rw [i285_mem_map, inv_inv] at hu
      exact hu
    · rw [i285_mul_apply, i285_mul_apply, i285_inv_apply_apply]
      intro heq
      apply hne
      have := congrArg ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) heq
      rwa [i285_inv_apply_apply, i285_inv_apply_apply] at this
    · rw [MulAut.conj_apply]
      group

theorem H_conj {g : 𝔾} (hg : g ∈ S.X) (R : Submodule (ZMod 2) M) :
    CFSG.Open.GLBConj g (S.H R) = S.H (R.map ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M)) := by
  rw [CFSG.Open.GLBConj, H, H, MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, S.T_conj hg]

theorem conj_fix_iff {g : 𝔾} (v : M) :
    ((g⁻¹ * S.τ * g : 𝔾) : M →ₗ[ZMod 2] M) v = v ↔ S.φ ((g : M →ₗ[ZMod 2] M) v) = 0 := by
  rw [S.conj_apply, add_eq_left, smul_eq_zero]
  refine ⟨fun h => h.resolve_right fun h0 => S.ha ?_, Or.inl⟩
  have := congrArg (g : M →ₗ[ZMod 2] M) h0
  rwa [i285_apply_inv_apply, map_zero] at this

theorem T_nonempty {R : Submodule (ZMod 2) M} (hR : S.IsMin R) : (S.T R).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  apply not_le_of_gt hR.2.1
  refine le_inf hR.2.2.1 fun v hv g hg => ?_
  rw [← S.conj_fix_iff]
  by_contra hne
  have : g⁻¹ * S.τ * g ∈ S.T R := ⟨⟨g, hg, rfl⟩, v, hv, hne⟩
  rw [hcon] at this
  exact this

theorem H_le_stab_R {R : Submodule (ZMod 2) M} (hR : S.IsMin R) : S.H R ≤ i285_stab R :=
  (S.H_le_W R).trans hR.1

theorem H_le_stab_Q (R : Submodule (ZMod 2) M) : S.H R ≤ i285_stab S.Q :=
  (S.H_le_W R).trans (S.W_le_fix_Q.trans (i285_fix_le_stab _))

@[expose] def ρ {R : Submodule (ZMod 2) M} (hR : S.IsMin R) :
    ↥(S.H R) →* LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ S.Q.comap R.subtype) :=
  i285_secHom (S.H_le_stab_R hR) (S.H_le_stab_Q R)

theorem ρ_injective {R : Submodule (ZMod 2) M} (hR : S.IsMin R) : Function.Injective (S.ρ hR) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hrel : ∀ v ∈ R, ((h : 𝔾) : M →ₗ[ZMod 2] M) v - v ∈ S.Q := by
    intro v hv
    have := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ S.Q.comap R.subtype) =>
      (f : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype))
        (Submodule.Quotient.mk ⟨v, hv⟩)) hh
    rw [ρ, i285_secHom_mk] at this
    change _ = Submodule.Quotient.mk _ at this
    rw [Submodule.Quotient.eq] at this
    exact this
  have hP : S.P ≤ i285_relSub (h : 𝔾) S.Q := by
    rw [← S.isMin_iSup_map hR]
    refine iSup_le fun x => ?_
    intro v hv
    rw [i285_mem_relSub]
    by_cases hx : R.map ((x : 𝔾) : M →ₗ[ZMod 2] M) = R
    · rw [hx] at hv
      exact hrel v hv
    · rw [S.H_le_fix hR (S.isMin_map hR x.2) (Ne.symm hx) h.2 v hv, sub_self]
      exact S.Q.zero_mem
  have := S.faithful (S.H_le_W R h.2) fun v hv => i285_mem_relSub.1 (hP hv)
  exact Subtype.ext this

theorem ρ_transvection {R : Submodule (ZMod 2) M} (hR : S.IsMin R) {d : 𝔾} (hd : d ∈ S.T R) :
    IsF2Transvection (S.ρ hR ⟨d, Subgroup.subset_closure hd⟩) := by
  obtain ⟨⟨g, hg, rfl⟩, v₀, hv₀, hne⟩ := hd
  have hdW : g⁻¹ * S.τ * g ∈ S.W := Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hα : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) S.a ∈ R :=
    S.center_mem (fun v hv => (hR.1 hdW v).2 hv) ⟨v₀, hv₀, hne⟩
  set Z := S.Q.comap R.subtype
  let abar : ↥R ⧸ Z := Submodule.Quotient.mk ⟨_, hα⟩
  have hZker : Z ≤ LinearMap.ker ((S.φ ∘ₗ (g : M →ₗ[ZMod 2] M)) ∘ₗ R.subtype) := by
    intro v hv
    rw [LinearMap.mem_ker]
    exact hv g hg
  let φ' : Module.Dual (ZMod 2) (↥R ⧸ Z) := Z.liftQ _ hZker
  have hφ'mk : ∀ v : ↥R, φ' (Submodule.Quotient.mk v) = S.φ ((g : M →ₗ[ZMod 2] M) v) :=
    fun v => rfl
  have hφ'a : φ' abar = 0 := by
    rw [hφ'mk]
    change S.φ ((g : M →ₗ[ZMod 2] M) (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) S.a)) = 0
    rw [i285_apply_inv_apply]
    exact S.hφa
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    apply hne
    rw [S.conj_fix_iff, ← hφ'mk ⟨v₀, hv₀⟩, h0]
    rfl
  have hane : abar ≠ 0 := by
    intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact S.apply_a_not_mem_Q (S.X.inv_mem hg) h0
  refine (isF2Transvection_iff _).2 ⟨φ', abar, hφ'a, hφ'ne, hane, tv_ext fun w => ?_⟩
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective Z w
  rw [tv_apply, hφ'mk, ρ, i285_secHom_mk]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul]
  exact S.conj_apply g v

theorem ρ_irred {R : Submodule (ZMod 2) M} (hR : S.IsMin R)
    (U : Submodule (ZMod 2) (↥R ⧸ S.Q.comap R.subtype))
    (hU : ∀ g ∈ (S.ρ hR).range, ∀ w ∈ U,
      (g : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) w ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  let T' : Submodule (ZMod 2) M := (U.comap (S.Q.comap R.subtype).mkQ).map R.subtype
  have hmemT' : ∀ v : ↥R, (v : M) ∈ T' ↔ Submodule.Quotient.mk v ∈ U := by
    intro v
    constructor
    · rintro ⟨y, hy, hyv⟩
      have : y = v := Subtype.ext hyv
      rw [← this]
      exact hy
    · intro h
      exact ⟨v, h, rfl⟩
  have hT'R : T' ≤ R := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hH : ∀ h ∈ S.H R, ∀ v ∈ T', (h : M →ₗ[ZMod 2] M) v ∈ T' := by
    rintro h hh _ ⟨y, hy, rfl⟩
    have hy' : Submodule.Quotient.mk y ∈ U := hy
    have := hU _ ⟨⟨h, hh⟩, rfl⟩ _ hy'
    rw [ρ, i285_secHom_mk] at this
    exact (hmemT' _).2 this
  have hW := S.W_le_stab_of_H hT'R hH
  have hPQ : S.P ⊓ S.Q ≤ T' := by
    intro v hv
    have hvR : v ∈ R := hR.2.1.le hv
    refine (hmemT' ⟨v, hvR⟩).2 ?_
    rw [(Submodule.Quotient.mk_eq_zero (S.Q.comap R.subtype)).2 hv.2]
    exact U.zero_mem
  by_cases hlt : S.P ⊓ S.Q < T'
  · right
    have hTR := hR.2.2.2 T' hW hlt hT'R
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (S.Q.comap R.subtype) w
    refine (hmemT' v).1 ?_
    rw [hTR]
    exact v.2
  · left
    have hTeq : T' = S.P ⊓ S.Q := (eq_of_le_of_not_lt hPQ hlt).symm
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (S.Q.comap R.subtype) w
    have hv := (hmemT' v).2 hw
    rw [hTeq] at hv
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hv.2

theorem ρ_range {R : Submodule (ZMod 2) M} (hR : S.IsMin R) :
    (S.ρ hR).range = Subgroup.closure ((S.ρ hR) '' (Subtype.val ⁻¹' S.T R)) := by
  rw [MonoidHom.range_eq_map, ← MonoidHom.map_closure]
  congr 1
  exact (Subgroup.closure_closure_coe_preimage (k := S.T R)).symm

end i285_Setup

end Setup

end CFSG.HardMathSupport.Solomon.Coordinator
