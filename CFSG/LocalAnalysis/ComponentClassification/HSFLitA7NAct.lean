module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NInst

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem SubConj.symm {X : Type} [Group X] {P Q : Subgroup X} (h : SubConj P Q) :
    SubConj Q P := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, Subgroup.map_map]
  ext a
  simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  · intro ha
    exact ⟨a, ha, by group⟩

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

structure Sec6Hyp (T₁ : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 T₁
  le : S.data.T ≤ T₁
  le_normalizer : T₁ ≤ normalizer (S.data.T : Set X)
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.data.T : Set X) →
    Q = T₁
  card : Nat.card T₁ = 4 * Nat.card S.data.T
  fus : S.Fus
  not_conj : ¬ SubConj (S.E (S.x * S.y)) (S.E S.y)

variable {S}

theorem Sec6Hyp.of_sec4 {F : S.Frame} {T₁ : Subgroup X} (h4 : S.Sec4 F T₁) (hF : F.Normal)
    (hnc : ¬ SubConj F.E₁ F.E₂) : S.Sec6Hyp T₁ := by
  obtain ⟨hx, hy, hk⟩ := hF
  refine ⟨h4.isPGroup, h4.le, h4.le_normalizer, h4.maximal, h4.card, fun b hb => ?_, ?_⟩
  · rw [h4.fusion b hb, hk]
  · have h1 : F.E₁ = S.E (S.x * S.y) := by rw [Frame.E₁, hy]
    have h2 : F.E₂ = S.E S.y := by rw [Frame.E₂, hx, hy, inv_mul_cancel_left]
    rwa [h1, h2] at hnc

namespace Inst

variable (I : S.Inst) {T₁ : Subgroup X}

include I in
theorem T₁_le (H : S.Sec6Hyp T₁) : T₁ ≤ normalizer (I.E : Set X) := by
  intro g hg
  have hgN := H.le_normalizer hg
  have hel : ElemAbelianTwo I.E := ⟨fun a ha b hb => I.comm ha hb, fun a ha => I.sq_eq_one ha⟩
  have hmap : I.E.map (MulAut.conj g).toMonoidHom ≤ S.data.T := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.mp hgN e).mp (I.E_le_T he)
  have hel' : ElemAbelianTwo (I.E.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hel.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hel.sq_eq_one a ha, map_one]
  have hc16 : Nat.card (I.E.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective, E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  have hIE : I.E = S.E I.yi := rfl
  have hfix : I.E.map (MulAut.conj g).toMonoidHom = I.E := by
    rcases S.eq_E_of_elem hmap hel' hc16 with h | h <;> rcases I.yi_or with hy | hy
    · rw [h, hIE, hy]
    · exfalso
      apply H.not_conj
      rw [hIE, hy] at h
      exact ⟨g, h⟩
    · exfalso
      apply H.not_conj
      rw [hIE, hy] at h
      exact SubConj.symm ⟨g, h⟩
    · rw [h, hIE, hy]
  refine mem_normalizer_of_conj_mem fun e he => ?_
  have : g * e * g⁻¹ ∈ I.E.map (MulAut.conj g).toMonoidHom := ⟨e, he, rfl⟩
  rwa [hfix] at this

theorem conj_ki_of_mem_NC {n : X}
    (hn : n ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X)) : n * I.ki * n⁻¹ = I.ki := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact S.conj_k_eq_of_mem_normalizer hn
  · exact S.conj_zk_eq_of_mem_normalizer hn

theorem ψ_yi_ki : ∃ σy σk : Perm (Fin 7),
    S.data.ψ ⟨I.yi, I.yi_mem.1⟩ = σy ∧ S.data.ψ ⟨I.ki, I.E_le_T I.ki_mem_E⟩ = σk ∧
      ((σy = rho0 * (c0 * b0) ∧ σk = c0) ∨ (σy = c0 * b0 ∧ σk = a0 ^ 2 * c0)) := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, Or.inl ⟨?_, S.ψ_k⟩⟩
    have : (⟨S.x * S.y, S.xy_mem.1⟩ : S.data.T) = ⟨S.x, S.x_mem.1⟩ * ⟨S.y, S.y_mem.1⟩ := rfl
    rw [this, map_mul, S.ψ_x, S.ψ_y]
  · refine ⟨_, _, rfl, rfl, Or.inr ⟨S.ψ_y, ?_⟩⟩
    have : (⟨S.z * S.k, mul_mem S.z_mem.1 S.k_mem⟩ : S.data.T) =
        ⟨S.z, S.z_mem.1⟩ * ⟨S.k, S.k_mem⟩ :=
      rfl
    rw [this, map_mul, S.ψ_z, S.ψ_k]

theorem ψ_wV (v : V4) : ∃ σy σk : Perm (Fin 7),
    S.data.ψ ⟨I.wV v, I.E_le_T (I.wV_mem v)⟩ =
      (a0 ^ 2) ^ (v.1 : ℕ) * σy ^ (v.2.1 : ℕ) * σk ^ (v.2.2.2 : ℕ) ∧
      ((σy = rho0 * (c0 * b0) ∧ σk = c0) ∨ (σy = c0 * b0 ∧ σk = a0 ^ 2 * c0)) := by
  obtain ⟨σy, σk, hy, hk, hσ⟩ := I.ψ_yi_ki
  refine ⟨σy, σk, ?_, hσ⟩
  have e : (⟨I.wV v, I.E_le_T (I.wV_mem v)⟩ : S.data.T) =
      (⟨S.z, S.z_mem.1⟩ : S.data.T) ^ (v.1 : ℕ) * (⟨I.yi, I.yi_mem.1⟩ : S.data.T) ^ (v.2.1 : ℕ) *
        (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (v.2.2.1 : ℕ) *
        (⟨I.ki, I.E_le_T I.ki_mem_E⟩ : S.data.T) ^ (v.2.2.2 : ℕ) := rfl
  rw [e, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, S.ψ_z, hy, S.ψ_t, hk,
    one_pow, mul_one]

theorem wV_d_eq_zero_of_mem_L (v : V4) (h : I.wV v ∈ S.L) : v.2.2.2 = 0 := by
  obtain ⟨a, b, c, d⟩ := v
  simp only
  rcases Fin.exists_fin_two.mp ⟨d, rfl⟩ with rfl | rfl
  · rfl
  exfalso
  have hzyL : S.z ^ (a : ℕ) * I.yi ^ (b : ℕ) ∈ S.L :=
    mul_mem (pow_mem S.z_mem.2 _) (pow_mem I.yi_mem.2 _)
  have htkL : S.t ^ (c : ℕ) * I.ki ∈ S.L := by
    have e : S.t ^ (c : ℕ) * I.ki = (S.z ^ (a : ℕ) * I.yi ^ (b : ℕ))⁻¹ * I.wV (a, b, c, 1) := by
      simp only [Inst.wV, Fin.val_one, pow_one]
      group
    rw [e]
    exact mul_mem (inv_mem hzyL) h
  have hkL : S.t ^ (c : ℕ) * S.k ∈ S.L := by
    rcases I.ki_eq with hk | hk
    · rwa [hk] at htkL
    · rw [hk] at htkL
      have hzt : S.z * S.t ^ (c : ℕ) = S.t ^ (c : ℕ) * S.z :=
        S.z_comm_of_mem_T (pow_mem S.data.t_mem_T _)
      have e : S.t ^ (c : ℕ) * S.k = S.z⁻¹ * (S.t ^ (c : ℕ) * (S.z * S.k)) := by
        calc S.t ^ (c : ℕ) * S.k = S.z⁻¹ * (S.z * S.t ^ (c : ℕ)) * S.k := by group
          _ = S.z⁻¹ * (S.t ^ (c : ℕ) * S.z) * S.k := by rw [hzt]
          _ = S.z⁻¹ * (S.t ^ (c : ℕ) * (S.z * S.k)) := by group
      rw [e]
      exact mul_mem (inv_mem S.z_mem.2) htkL
  have hkT : S.t ^ (c : ℕ) * S.k ∈ S.data.T := mul_mem (pow_mem S.data.t_mem_T _) S.k_mem
  have hA := S.data.ψ_mem_alternatingGroup ⟨_, hkT⟩ hkL
  have hψ : S.data.ψ ⟨S.t ^ (c : ℕ) * S.k, hkT⟩ = c0 := by
    have e : (⟨S.t ^ (c : ℕ) * S.k, hkT⟩ : S.data.T) =
        (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (c : ℕ) * ⟨S.k, S.k_mem⟩ := rfl
    rw [e, map_mul, map_pow, S.ψ_t, one_pow, one_mul, S.ψ_k]
  rw [hψ] at hA
  exact c0_not_mem_alternating hA

theorem conj_mem_three (hO : S.Fus) {n : X}
    (hn : n ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X)) {e : X}
    (he : e = S.z ∨ e = I.yi ∨ e = S.z * I.yi) :
    n * e * n⁻¹ = S.z ∨ n * e * n⁻¹ = I.yi ∨ n * e * n⁻¹ = S.z * I.yi := by
  have heE : e ∈ I.E := by
    rcases he with rfl | rfl | rfl
    · exact I.z_mem_E
    · exact I.yi_mem_E
    · exact mul_mem I.z_mem_E I.yi_mem_E
  obtain ⟨w, hw⟩ := I.eq_wV heE
  have hw' : w = (1, 0, 0, 0) ∨ w = (0, 1, 0, 0) ∨ w = (1, 1, 0, 0) := by
    have e1 : S.z = I.wV (1, 0, 0, 0) := by simp [Inst.wV]
    have e2 : I.yi = I.wV (0, 1, 0, 0) := by simp [Inst.wV]
    have e3 : S.z * I.yi = I.wV (1, 1, 0, 0) := by simp [Inst.wV]
    rcases he with rfl | rfl | rfl
    · exact Or.inl (I.wV_injective (hw.symm.trans e1))
    · exact Or.inr (Or.inl (I.wV_injective (hw.symm.trans e2)))
    · exact Or.inr (Or.inr (I.wV_injective (hw.symm.trans e3)))
  have hneE : n * e * n⁻¹ ∈ I.E := (mem_normalizer_iff.mp hn.1 _).mp heE
  obtain ⟨v, hv⟩ := I.eq_wV hneE
  have heL : e ∈ S.L := by
    rcases he with rfl | rfl | rfl
    · exact S.z_mem.2
    · exact I.yi_mem.2
    · exact mul_mem S.z_mem.2 I.yi_mem.2
  have hneL : n * e * n⁻¹ ∈ S.L :=
    (mem_normalizer_iff.mp (S.data.config.le_normalizer hn.2) e).mp heL
  have hd := I.wV_d_eq_zero_of_mem_L v (hv ▸ hneL)
  have hnc : ¬ ConjTo S.t (I.wV v) := by
    rw [← hv, conjTo_conj_iff, hw, I.conjTo_wV_iff hO]
    rcases hw' with rfl | rfl | rfl <;> decide
  rw [I.conjTo_wV_iff hO] at hnc
  have hne1 : I.wV v ≠ 1 := by
    rw [← hv]
    intro h1
    have he1 : e = 1 := by
      calc e = n⁻¹ * (n * e * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨σy, σk, hψ, hσ⟩ := I.ψ_wV w
    have h1' : S.data.ψ ⟨I.wV w, I.E_le_T (I.wV_mem w)⟩ = 1 := by
      have : (⟨I.wV w, I.E_le_T (I.wV_mem w)⟩ : S.data.T) = 1 := Subtype.ext (hw ▸ he1)
      rw [this, map_one]
    rw [hψ] at h1'
    clear hψ hv hneE hneL hnc
    rcases hw' with rfl | rfl | rfl <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact absurd h1' (by decide)
  obtain ⟨a, b, c, d⟩ := v
  simp only at hd hnc
  have hc : c = 0 := by
    rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
    · rfl
    · exact absurd rfl hnc
  subst hc hd
  rw [hv]
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · exact absurd (by simp [Inst.wV]) hne1
  · right; left; simp [Inst.wV]
  · left; simp [Inst.wV]
  · right; right; simp [Inst.wV]

theorem exists_d : ∃ d ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X),
    d * S.z * d⁻¹ = I.yi ∧ d * I.yi * d⁻¹ = S.z * I.yi := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨d, hdC, hdN, hdz, hdxy, -⟩ := S.exists_d_xy
    exact ⟨d, ⟨hdN, hdC⟩, hdz, hdxy⟩
  · obtain ⟨d, hdC, hdN, hdz, hdy, -⟩ := S.exists_d_y
    refine ⟨d⁻¹, mem_inf.mpr ⟨inv_mem hdN, inv_mem hdC⟩, ?_, ?_⟩
    · rw [inv_inv]
      calc d⁻¹ * S.z * d = d⁻¹ * (d * S.y * d⁻¹) * d := by rw [hdy]
        _ = S.y := by group
    · rw [inv_inv]
      have hzy : S.z * S.y = S.y * S.z := S.z_comm_of_mem_T S.y_mem.1
      have hdzy : d * (S.z * S.y) * d⁻¹ = S.y := by
        calc d * (S.z * S.y) * d⁻¹ = d * S.z * d⁻¹ * (d * S.y * d⁻¹) := by group
          _ = S.y * (S.z * S.z) := by rw [hdz, hdy, hzy, mul_assoc]
          _ = S.y := by rw [← pow_two, S.z_sq, mul_one]
      calc d⁻¹ * S.y * d = d⁻¹ * (d * (S.z * S.y) * d⁻¹) * d := by rw [hdzy]
        _ = S.z * S.y := by group

theorem ui_mem_T : I.ui ∈ S.data.T := by
  rcases I.spec with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact S.y_mem.1
  · exact mul_mem S.z_mem.1 S.xy_mem.1

theorem ui_sq : I.ui ^ 2 = 1 := by
  rcases I.spec with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact S.y_sq
  · exact S.E_sq S.xy_mem S.xy_sq (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))

theorem x_conj_y : S.x * S.y * S.x⁻¹ = S.z * S.y := by
  calc S.x * S.y * S.x⁻¹ = S.x * (S.y * S.x * S.y⁻¹)⁻¹ * S.y := by group
    _ = S.z * S.y := by rw [S.y_x_y, inv_inv, ← pow_two]; rfl

theorem x_conj_xy : S.x * (S.x * S.y) * S.x⁻¹ = S.z * (S.x * S.y) := by
  calc S.x * (S.x * S.y) * S.x⁻¹ = S.x * (S.x * S.y * S.x⁻¹) := by group
    _ = S.x * (S.z * S.y) := by rw [x_conj_y]
    _ = S.z * (S.x * S.y) := by
        rw [← mul_assoc, ← mul_assoc, ← S.z_comm_of_mem_T S.x_mem.1]

theorem x_conj_yi : S.x * I.yi * S.x⁻¹ = S.z * I.yi := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact x_conj_y
  · exact x_conj_xy

theorem ui_conj_yi : I.ui * I.yi * I.ui⁻¹ = S.z * I.yi := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show S.y * (S.x * S.y) * S.y⁻¹ = S.z * (S.x * S.y)
    have hx3 : S.x⁻¹ = S.x ^ 3 :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, S.x_pow_four])).symm
    calc S.y * (S.x * S.y) * S.y⁻¹ = S.y * S.x * S.y⁻¹ * S.y := by group
      _ = S.x ^ 3 * S.y := by rw [S.y_x_y, hx3]
      _ = S.z * (S.x * S.y) := by rw [show S.z = S.x ^ 2 from rfl]; group
  · show S.z * (S.x * S.y) * S.y * (S.z * (S.x * S.y))⁻¹ = S.z * S.y
    have hzy : S.z * S.y = S.y * S.z := S.z_comm_of_mem_T S.y_mem.1
    have hzi : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right (by rw [← pow_two, S.z_sq])
    calc S.z * (S.x * S.y) * S.y * (S.z * (S.x * S.y))⁻¹ =
          S.z * (S.x * S.y * S.x⁻¹) * S.z⁻¹ := by group
      _ = S.z * (S.z * S.y) * S.z := by rw [x_conj_y, hzi]
      _ = S.z * S.y := by
          rw [show S.z * (S.z * S.y) * S.z = (S.z * S.z) * (S.y * S.z) by group, ← pow_two,
            S.z_sq, one_mul, ← hzy]

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
