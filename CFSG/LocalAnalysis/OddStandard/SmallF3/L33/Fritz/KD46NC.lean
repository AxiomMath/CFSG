module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NQ0T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NQ1N

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S} {H : Hyp S R}

theorem mem_closure_t_ki_iff (I : Inst S) {x : X} :
    x ∈ closure {t, I.ki} ↔ ∃ a b : Fin 2, x = I.wV (0, 0, a, b) := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, 0, by simp [wV]⟩
      · exact ⟨0, 1, by simp [wV]⟩
    | one => exact ⟨0, 0, by simp [wV]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, rfl⟩ := hy
      obtain ⟨a', b', rfl⟩ := hz
      exact ⟨a + a', b + b', by rw [← I.wV_add]; simp [addV]⟩
    | inv y _ hy =>
      obtain ⟨a, b, rfl⟩ := hy
      exact ⟨a, b, I.wV_inv _⟩
  · rintro ⟨a, b, rfl⟩
    simp only [wV, Fin.val_zero, pow_zero, one_mul]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

theorem card_closure_t_ki (I : Inst S) : Nat.card (closure {t, I.ki}) = 4 := by
  let f : Fin 2 × Fin 2 → closure {t, I.ki} :=
    fun p => ⟨I.wV (0, 0, p.1, p.2), (I.mem_closure_t_ki_iff).mpr ⟨_, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · have := I.wV_injective (congrArg Subtype.val h)
      simp only [Prod.mk.injEq] at this
      exact Prod.ext this.2.2.1 this.2.2.2
    · obtain ⟨a, b, hab⟩ := (I.mem_closure_t_ki_iff).mp x.2
      exact ⟨(a, b), Subtype.ext hab.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

namespace Data6

variable (D : I.Data6 H)

theorem Q₁_mat {x : X} (hx : x ∈ D.Q₁) : ∃ a b c : Fin 2, I.Mat x (gC D.ε a b c) := by
  obtain ⟨ε', hε', -, hcl⟩ := I.exists_setup H
  rw [eps_eq hε' D.hε] at hcl
  have hxK : x ∈ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) := (mem_inf.mp hx).2
  rw [I.oddTwoCoreIn_eq H] at hxK
  obtain ⟨n, hn, rfl⟩ := hxK
  obtain ⟨a, b, c, hc⟩ := I.cols_of_mem_Pre H D.ε hcl hn
  exact ⟨a, b, c, n.2, hc⟩

theorem v_sq : ∃ j : Fin 2, D.v ^ 2 = I.wV (0, 0, 0, j) := by
  obtain ⟨p, hp⟩ := I.eq_wV D.v_sq_E
  have hd : lin dCols p = p := by
    apply I.wV_injective
    rw [← D.d_mat.conj, ← hp]
    have : D.d * D.v ^ 2 = D.v ^ 2 * D.d := (Commute.pow_left D.v_d 2).eq.symm
    rw [this]; group
  have hv : lin vC p = p := by
    apply I.wV_injective
    rw [← D.v_mat.conj, ← hp]
    group
  obtain ⟨h1, h2, h3⟩ := dvC_fix p hd hv
  obtain ⟨a, b, c, e⟩ := p
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨e, hp⟩

theorem t_comm_d : t * D.d = D.d * t := (mem_centralizer_singleton_iff.mp D.d_mem_C_t).symm

theorem ki_comm_d : I.ki * D.d = D.d * I.ki := by
  have h := D.d_mat.conj_ki
  rw [show I.wV (dCols 3) = I.ki by simp [dCols, sigCols, wV]] at h
  calc I.ki * D.d = D.d * (D.d⁻¹ * I.ki * D.d) := by group
    _ = D.d * I.ki := by
        congr 1
        calc D.d⁻¹ * I.ki * D.d = D.d⁻¹ * (D.d * I.ki * D.d⁻¹) * D.d := by rw [h]
          _ = I.ki := by group

theorem v_conj_t : D.v * t * D.v⁻¹ = t * I.ki := by
  rw [D.v_mat.conj_t]; simp [vC, wV, I.comm I.t_mem_E I.ki_mem_E]

theorem v_conj_ki : D.v * I.ki * D.v⁻¹ = I.ki := by
  rw [D.v_mat.conj_ki]; simp [vC, wV]

theorem C_eq : D.Q₁ ⊓ centralizer (zpowers D.d : Set X) = closure {t, I.ki, D.v} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, hxd⟩ := mem_inf.mp hx
    rw [mem_centralizer_zpowers_iff] at hxd
    obtain ⟨a, b, c, hxM⟩ := D.Q₁_mat hxQ
    have hcd : comp (gC D.ε a b c) dCols = comp dCols (gC D.ε a b c) := by
      have h1 := hxM.mul D.d_mat
      have h2 := D.d_mat.mul hxM
      rw [hxd] at h1
      exact h1.unique h2
    obtain ⟨rfl, rfl⟩ := gC_comm_d D.ε a b c hcd
    rw [gC_zero] at hxM
    have hy : (D.v ^ (c : ℕ))⁻¹ * x ∈ I.E :=
      D.mem_E_of_mem_Q₁ (mul_mem (inv_mem (pow_mem D.v_Q₁ _)) hxQ)
        ((D.v_mat.pw c).inv_mul_mem_centralizer hxM)
    obtain ⟨p, hp⟩ := I.eq_wV hy
    have hpd : lin dCols p = p := by
      apply I.wV_injective
      rw [← D.d_mat.conj, ← hp]
      have hA : D.d * (D.v ^ (c : ℕ))⁻¹ = (D.v ^ (c : ℕ))⁻¹ * D.d :=
        ((Commute.pow_left D.v_d _).inv_left).eq.symm
      calc D.d * ((D.v ^ (c : ℕ))⁻¹ * x) * D.d⁻¹ = (D.d * (D.v ^ (c : ℕ))⁻¹) * x * D.d⁻¹ := by
            group
        _ = (D.v ^ (c : ℕ))⁻¹ * (D.d * x) * D.d⁻¹ := by rw [hA]; group
        _ = (D.v ^ (c : ℕ))⁻¹ * x := by rw [← hxd]; group
    obtain ⟨h1, h2⟩ := dCols_fix p hpd
    obtain ⟨p1, p2, p3, p4⟩ := p
    simp only at h1 h2
    subst h1 h2
    have hx : x = D.v ^ (c : ℕ) * (t ^ (p3 : ℕ) * I.ki ^ (p4 : ℕ)) := by
      have : x = D.v ^ (c : ℕ) * ((D.v ^ (c : ℕ))⁻¹ * x) := by group
      rw [this, hp]; simp [wV]
    rw [hx]
    exact mul_mem (pow_mem (subset_closure (by simp)) _)
      (mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _))
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_inf, mem_centralizer_zpowers_iff]
    rcases hg with rfl | rfl | rfl
    · exact ⟨D.E_le_Q₁ I.t_mem_E, D.t_comm_d⟩
    · exact ⟨D.E_le_Q₁ I.ki_mem_E, D.ki_comm_d⟩
    · exact ⟨D.v_Q₁, D.v_d⟩

theorem closure_t_ki_v : closure {t, I.ki, D.v} = closure {t, I.ki} ⊔ zpowers D.v := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (Subgroup.closure_mono ?_) (zpowers_le.mpr (subset_closure (by simp)))
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto

theorem card_C : Nat.card (D.Q₁ ⊓ centralizer (zpowers D.d : Set X) : Subgroup X) = 8 := by
  rw [D.C_eq, D.closure_t_ki_v]
  have hvN : D.v ∈ normalizer (closure {t, I.ki} : Set X) :=
    mem_normalizer_of_conj_mem fun x hx => conj_mem_closure (fun g hg => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [D.v_conj_t]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · rw [D.v_conj_ki]; exact subset_closure (by simp)) hx
  have hv2 : D.v ^ 2 ∈ closure {t, I.ki} := by
    obtain ⟨j, hj⟩ := D.v_sq
    rw [hj]; exact (I.mem_closure_t_ki_iff).mpr ⟨0, j, rfl⟩
  have hvC : D.v ∉ closure {t, I.ki} := fun h => by
    obtain ⟨a, b, hab⟩ := (I.mem_closure_t_ki_iff).mp h
    have hC : D.v ∈ centralizer (I.E : Set X) := by
      rw [hab]; exact I.E_le_centralizer (I.wV_mem _)
    exact vC_ne_bas (D.v_mat.unique (Mat.of_mem_centralizer hC))
  rw [card_sup_zpowers hvN hv2 hvC, I.card_closure_t_ki]

@[expose] noncomputable def c₁ : X := t ^ (D.α : ℕ) * D.v

@[expose] noncomputable def C₁ : Subgroup X := closure {I.ki, D.c₁}

theorem c₁_mat : I.Mat D.c₁ vC := D.v_mat.central_mul (I.E_le_centralizer (pow_mem I.t_mem_E _))

theorem c₁_mem_C : D.c₁ ∈ closure {t, I.ki, D.v} :=
  mul_mem (pow_mem (subset_closure (by simp)) _) (subset_closure (by simp))

theorem C₁_le : D.C₁ ≤ D.Q₁ ⊓ centralizer (zpowers D.d : Set X) := by
  rw [D.C_eq, C₁, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact subset_closure (by simp)
  · exact D.c₁_mem_C

theorem C₁_sup : D.C₁ ⊔ zpowers t = D.Q₁ ⊓ centralizer (zpowers D.d : Set X) := by
  apply le_antisymm
  · exact sup_le D.C₁_le (zpowers_le.mpr (by rw [D.C_eq]; exact subset_closure (by simp)))
  · rw [D.C_eq, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (subset_closure (by simp))
    · have e : D.v = (t ^ (D.α : ℕ))⁻¹ * D.c₁ := by rw [c₁]; group
      rw [e]
      exact mul_mem (inv_mem (pow_mem (mem_sup_right (mem_zpowers _)) _))
        (mem_sup_left (subset_closure (by simp)))

theorem c₁_sq_mem : D.c₁ ^ 2 ∈ zpowers I.ki := by
  obtain ⟨j, hj⟩ := D.v_sq
  have hki : I.wV (0, 0, 0, j) = I.ki ^ (j : ℕ) := by simp [wV]
  rw [hki] at hj
  have htv : D.v * t = t * I.ki * D.v := by rw [← D.v_conj_t]; group
  rcases Fin.exists_fin_two.mp ⟨D.α, rfl⟩ with h | h
  · rw [c₁, h]
    simp only [Fin.val_zero, pow_zero, one_mul]
    rw [hj]; exact pow_mem (mem_zpowers _) _
  · rw [c₁, h]
    simp only [Fin.val_one, pow_one]
    have e : (t * D.v) ^ 2 = I.ki * D.v ^ 2 := by
      have htk : t * I.ki = I.ki * t := I.comm I.t_mem_E I.ki_mem_E
      calc (t * D.v) ^ 2 = t * (D.v * t) * D.v := by rw [pow_two]; group
        _ = t * (t * I.ki * D.v) * D.v := by rw [htv]
        _ = (t * t) * I.ki * (D.v * D.v) := by group
        _ = I.ki * D.v ^ 2 := by rw [← pow_two t, (t_sq' (A := A)), one_mul, pow_two]
    rw [e, hj]
    exact mul_mem (mem_zpowers _) (pow_mem (mem_zpowers _) _)

theorem card_C₁ : Nat.card D.C₁ = 4 := by
  have hk1 : I.ki ≠ 1 := I.ki_ne_one
  have hC₁ : D.C₁ = zpowers I.ki ⊔ zpowers D.c₁ := by
    apply le_antisymm
    · rw [C₁, closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact mem_sup_left (mem_zpowers _)
      · exact mem_sup_right (mem_zpowers _)
    · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
        (zpowers_le.mpr (subset_closure (by simp)))
  have hkc : D.c₁ * I.ki = I.ki * D.c₁ := by
    have h := D.c₁_mat.conj_ki
    rw [show I.wV (vC 3) = I.ki by simp [vC, wV]] at h
    calc D.c₁ * I.ki = D.c₁ * I.ki * D.c₁⁻¹ * D.c₁ := by group
      _ = I.ki * D.c₁ := by rw [h]
  have hN : D.c₁ ∈ normalizer (zpowers I.ki : Set X) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨n, rfl⟩ := hx
    simp only
    rw [show D.c₁ * I.ki ^ n * D.c₁⁻¹ = I.ki ^ n by
      rw [(Commute.zpow_right hkc n).eq]; group]
    exact ⟨n, rfl⟩
  have hc2 : D.c₁ ^ 2 ∈ zpowers I.ki := D.c₁_sq_mem
  have hcK : D.c₁ ∉ zpowers I.ki := fun h => by
    have hE : D.c₁ ∈ I.E := (zpowers_le.mpr I.ki_mem_E) h
    exact vC_ne_bas (D.c₁_mat.unique (Mat.of_mem_centralizer (I.E_le_centralizer hE)))
  rw [hC₁, card_sup_zpowers hN hc2 hcK, Nat.card_zpowers,
    orderOf_eq_prime (by rw [I.ki_sq]) hk1]

variable (Rl : D.Rel)

include Rl in
theorem C₁_comm : ∀ c ∈ D.C₁, ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂, c * q = q * c := by
  have hkcen : ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂, I.ki * q = q * I.ki := by
    refine Rl.rel.central_of_gens (I.comm I.ki_mem_E I.z_mem_E) (I.comm I.ki_mem_E I.yi_mem_E) rfl
      ?_ ?_
    · have := commute_of_fix Rl.rel.m1 (M1C_ki D.ε 1)
      simp only [show I.wV (0, 0, 0, 1) = I.ki by simp [wV]] at this
      exact this.symm
    · have := commute_of_fix Rl.rel.m2 (M2C_ki D.ε 1)
      simp only [show I.wV (0, 0, 0, 1) = I.ki by simp [wV]] at this
      exact this.symm
  have hE0c : ∀ {e : X}, e ∈ I.E → (∀ a b d : Fin 2, lin vC (a, b, 0, d) = (a, b, 0, d)) →
      D.c₁ * e = e * D.c₁ → True := fun _ _ _ => trivial
  have hcz : ∀ p : V4, p.2.2.1 = 0 → D.c₁ * I.wV p = I.wV p * D.c₁ := by
    intro p hp
    obtain ⟨a, b, c, d⟩ := p
    simp only at hp
    subst hp
    exact commute_of_fix D.c₁_mat (vC_E0_fix a b d)
  have htw : ∀ {w : X} {c : Fin 4 → V4} {p : V4}, I.Mat w c → c 2 = addV (0, 0, 1, 0) p →
      w * t * w⁻¹ * t⁻¹ = I.wV p := by
    intro w c p hw hc
    rw [hw.conj_t, hc, I.wV_add, show I.wV (0, 0, 1, 0) = t by simp [wV], I.comm I.t_mem_E
      (I.wV_mem p)]
    group
  have hc1 : D.c₁ * D.w₁ = D.w₁ * D.c₁ := by
    have h1 : D.w₁ * t * D.w₁⁻¹ * t⁻¹ = I.wV (1, 0, 0, D.ε) :=
      htw D.w₁_mat (by rw [M1C_two]; simp [addV])
    have key : D.c₁ * D.w₁ * D.c₁⁻¹ * D.w₁⁻¹ = 1 := by
      rw [c₁]
      rcases Fin.exists_fin_two.mp ⟨D.α, rfl⟩ with h | h
      · have hv := D.v_w₁
        rw [h] at hv ⊢
        simp only [Fin.val_zero, pow_zero, one_mul, mul_zero] at hv ⊢
        rw [hv, I.wV_zero]
      · have hv := D.v_w₁
        rw [h] at hv ⊢
        simp only [Fin.val_one, pow_one, mul_one] at hv ⊢
        have e : t * D.v * D.w₁ * (t * D.v)⁻¹ * D.w₁⁻¹ =
            t * (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹) * t⁻¹ * (D.w₁ * t * D.w₁⁻¹ * t⁻¹)⁻¹ := by
          group
        rw [e, hv, h1, I.wV_inv]
        have ht : t * I.wV (1, 0, 0, D.ε) * t⁻¹ = I.wV (1, 0, 0, D.ε) := by
          rw [I.comm I.t_mem_E (I.wV_mem _)]; group
        rw [ht, ← I.wV_add]
        simp [addV, fin2_add_self, I.wV_zero]
    calc D.c₁ * D.w₁ = (D.c₁ * D.w₁ * D.c₁⁻¹ * D.w₁⁻¹) * D.w₁ * D.c₁ := by group
      _ = D.w₁ * D.c₁ := by rw [key, one_mul]
  have hc2 : D.c₁ * D.w₂ = D.w₂ * D.c₁ := by
    have h1 : D.w₂ * t * D.w₂⁻¹ * t⁻¹ = I.wV (0, 1, 0, D.ε) :=
      htw D.w₂_mat (by rw [M2C_two]; simp [addV])
    have key : D.c₁ * D.w₂ * D.c₁⁻¹ * D.w₂⁻¹ = 1 := by
      rw [c₁]
      have hv := D.v_w₂
      rw [dCols_cvw] at hv
      rcases Fin.exists_fin_two.mp ⟨D.α, rfl⟩ with h | h
      · rw [h] at hv ⊢
        simp only [Fin.val_zero, pow_zero, one_mul, mul_zero] at hv ⊢
        rw [hv, I.wV_zero]
      · rw [h] at hv ⊢
        simp only [Fin.val_one, pow_one, mul_one] at hv ⊢
        have e : t * D.v * D.w₂ * (t * D.v)⁻¹ * D.w₂⁻¹ =
            t * (D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹) * t⁻¹ * (D.w₂ * t * D.w₂⁻¹ * t⁻¹)⁻¹ := by
          group
        rw [e, hv, h1, I.wV_inv]
        have ht : t * I.wV (0, 1, 0, D.ε) * t⁻¹ = I.wV (0, 1, 0, D.ε) := by
          rw [I.comm I.t_mem_E (I.wV_mem _)]; group
        rw [ht, ← I.wV_add]
        simp [addV, fin2_add_self, I.wV_zero]
    calc D.c₁ * D.w₂ = (D.c₁ * D.w₂ * D.c₁⁻¹ * D.w₂⁻¹) * D.w₂ * D.c₁ := by group
      _ = D.w₂ * D.c₁ := by rw [key, one_mul]
  have hc₁cen : ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂, D.c₁ * q = q * D.c₁ :=
    Rl.rel.central_of_gens (by simpa [wV] using hcz (1, 0, 0, 0) rfl)
      (by simpa [wV] using hcz (0, 1, 0, 0) rfl) (by simpa [wV] using hcz (0, 0, 0, 1) rfl)
      hc1 hc2
  intro c hc q hq
  have hle : D.C₁ ≤ centralizer ({q} : Set X) := by
    rw [C₁, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl
    · exact hkcen q hq
    · exact hc₁cen q hq
  exact mem_centralizer_singleton_iff.mp (hle hc)

theorem w₁_comm_C : ∀ c ∈ D.Q₁ ⊓ centralizer (zpowers D.d : Set X),
    D.w₁ * c * D.w₁⁻¹ * c⁻¹ ∈ closure {I.wV (1, 0, 0, D.ε)} := by
  rw [D.C_eq]
  have hcen : ∀ y ∈ closure {t, I.ki, D.v},
      y * I.wV (1, 0, 0, D.ε) = I.wV (1, 0, 0, D.ε) * y := by
    intro y hy
    have hle : closure {t, I.ki, D.v} ≤ centralizer ({I.wV (1, 0, 0, D.ε)} : Set X) := by
      rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl
      · exact I.comm I.t_mem_E (I.wV_mem _)
      · exact I.comm I.ki_mem_E (I.wV_mem _)
      · exact commute_of_fix D.v_mat (vC_E0_fix 1 0 D.ε)
    exact mem_centralizer_singleton_iff.mp (hle hy)
  refine comm_mem_closure_right (fun y hy => mem_normalizer_of_conj_mem fun x hx => ?_) ?_
  · rw [← zpowers_eq_closure] at hx ⊢
    obtain ⟨n, rfl⟩ := hx
    refine ⟨n, ?_⟩
    simp only
    rw [(Commute.zpow_right (hcen y hy) n).eq]; group
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg <;> rw [hg]
    · rw [D.w₁_mat.conj_t, M1C_two]
      have e : I.wV (1, 0, 1, D.ε) * t⁻¹ = I.wV (1, 0, 0, D.ε) := by
        rw [show ((1, 0, 1, D.ε) : V4) = addV (1, 0, 0, D.ε) (0, 0, 1, 0) by simp [addV],
          I.wV_add, show I.wV (0, 0, 1, 0) = t by simp [wV]]
        group
      rw [e]; exact subset_closure rfl
    · have := commute_of_fix D.w₁_mat (M1C_ki D.ε 1)
      simp only [show I.wV (0, 0, 0, 1) = I.ki by simp [wV]] at this
      rw [this]; group; exact one_mem _
    · have e : D.w₁ * D.v * D.w₁⁻¹ * D.v⁻¹ = (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹)⁻¹ := by group
      rw [e, D.v_w₁, I.wV_inv]
      rcases Fin.exists_fin_two.mp ⟨D.α, rfl⟩ with h | h <;> rw [h]
      · simp only [mul_zero]; rw [I.wV_zero]; exact one_mem _
      · simp only [mul_one]; exact subset_closure rfl

theorem u_comm_C : ∀ c ∈ D.Q₁ ⊓ centralizer (zpowers D.d : Set X), D.u * c = c * D.u := by
  rw [D.C_eq]
  have huT : D.u ∈ S.TE := by
    rcases D.u_eq with h | h <;> rw [h]
    · exact I.ui_mem_TE
    · exact mul_mem (t_mem_TE S) I.ui_mem_TE
  intro c hc
  have hle : closure {t, I.ki, D.v} ≤ centralizer ({D.u} : Set X) := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · exact ((comm_tE S) huT).symm
    · exact (KD46.central_of_mem_B S) I.ki_mem_B huT
    · exact D.u_v.symm
  exact (mem_centralizer_singleton_iff.mp (hle hc)).symm

end Data6

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
