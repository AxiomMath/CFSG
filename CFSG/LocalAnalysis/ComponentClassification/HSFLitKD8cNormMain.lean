module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cNorm

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8

theorem mc_pcX : MC.PcX MC.w₂ MC.u MC.w₁ MC.v MC.z MC.y MC.t MC.k := by
  constructor <;> decide +kernel

theorem z_eq : MC.z = MC.u * MC.y * MC.u⁻¹ * MC.y⁻¹ := by decide +kernel

theorem k_eq : MC.k = MC.z * (MC.w₁⁻¹ * MC.v⁻¹ * MC.w₁ * MC.v) := by decide +kernel

@[expose] def inZ (x : MC) : Bool := inE 0 x && inE 3 x

@[expose] def Zl : List MC := [1, MC.z, MC.k, MC.z * MC.k]

theorem inZ_iff : ∀ x : MC, inZ x = true ↔ x ∈ Zl := by decide +kernel

@[expose] def Cover4 (a b c d e : MC) : Prop :=
  a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → e = a ∨ e = b ∨ e = c ∨ e = d

instance (a b c d e : MC) : Decidable (Cover4 a b c d e) := by unfold Cover4; infer_instance

theorem four_cover : ∀ a ∈ Zl, ∀ b ∈ Zl, ∀ c ∈ Zl, ∀ d ∈ Zl, ∀ e ∈ Zl, Cover4 a b c d e := by
  decide +kernel

theorem cand_t : ∀ a : MC, a * a = 1 → inE 3 a = true → inE 5 a = true → inZ a = false →
    a ∈ Ct := by decide +kernel

theorem cand_y : ∀ a : MC, a * a = 1 → inE 3 a = true → inE 7 a = true → inZ a = false →
    a ∈ Cy := by decide +kernel

theorem cand_u : ∀ a : MC, a * a = 1 → inE 5 a = true → inE 4 a = true → inZ a = false →
    a ∈ Cu := by decide +kernel

theorem cand_v : ∀ a : MC, a * a = 1 → inE 4 a = true → inE 7 a = true → inZ a = false →
    a ∈ Cv := by decide +kernel

theorem cand_w : ∀ a : MC, a * a = 1 → inE 0 a = true → inE 6 a = true → inZ a = false →
    a ∈ Cw := by decide +kernel

theorem cand_inv : ∀ a : MC, a * a = 1 → a ≠ 1 → ∃ n : Fin 71, invList.getD n 1 = a := by
  decide +kernel

theorem idx_C : ∀ l ∈ [Ct, Cy, Cu, Cv, Cw], ∀ a ∈ l, ∃ i : Fin 4, l.getD i 1 = a := by
  decide +kernel

namespace Antipodal

variable {φ : MC → MC}

@[expose] noncomputable def hom (h : Antipodal φ) : MC →* MC := MonoidHom.mk' φ h.map_mul

theorem map_one (h : Antipodal φ) : φ 1 = 1 := _root_.map_one h.hom

theorem inZ_map (h : Antipodal φ) {x : MC} (hx : inZ x = true) : inZ (φ x) = true := by
  simp only [inZ, Bool.and_eq_true] at hx ⊢
  exact ⟨h.ant 3 x hx.2, h.ant 0 x hx.1⟩

theorem inZ_of_map (h : Antipodal φ) {x : MC} (hx : inZ (φ x) = true) : inZ x = true := by
  have hm : ∀ g : MC, inZ g = true → φ g ∈ Zl := fun g hg => (inZ_iff _).mp (h.inZ_map hg)
  have ne : ∀ a b : MC, a ≠ b → φ a ≠ φ b := fun a b hab e => hab (h.injective e)
  rcases four_cover _ (hm 1 (by decide +kernel)) _ (hm MC.z (by decide +kernel)) _
    (hm MC.k (by decide +kernel)) _ (hm (MC.z * MC.k) (by decide +kernel)) _ ((inZ_iff _).mp hx)
    (ne _ _ (by decide +kernel)) (ne _ _ (by decide +kernel)) (ne _ _ (by decide +kernel))
    (ne _ _ (by decide +kernel)) (ne _ _ (by decide +kernel)) (ne _ _ (by decide +kernel)) with
    e | e | e | e <;> rw [h.injective e] <;> decide +kernel

theorem inZ_map_false (h : Antipodal φ) {x : MC} (hx : inZ x = false) : inZ (φ x) = false := by
  cases hh : inZ (φ x)
  · rfl
  · rw [h.inZ_of_map hh] at hx
    exact hx

theorem inv_map (h : Antipodal φ) {g : MC} (hg : g * g = 1) : φ g * φ g = 1 := by
  rw [← h.map_mul, hg, h.map_one]

end Antipodal

theorem w2Rel_map (ψ : MC →* MC) : W2Rel (MC.gens.map ψ) := by
  have hp := mc_pcX
  simp only [W2Rel, MC.gens, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hp.w₂_sq, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_u, map_mul, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_w₁, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_v, map_mul, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_z, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_y]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_t, map_mul, map_mul]
  · rw [← map_inv, ← map_mul, ← map_mul, hp.w₂_k]

theorem exists_norm {φ : MC → MC} (h : Antipodal φ) :
    ∃ m : MC, inR1 m = true ∧ ∃ j : Fin 8, ∀ g ∈ MC.gens, m * φ g * m⁻¹ = phiR j g := by
  have hnz : ∀ g : MC, inZ g = false → inZ (φ g) = false := fun g hg => h.inZ_map_false hg
  have ht := cand_t (φ MC.t) (h.inv_map (g := MC.t) (by decide +kernel))
    (h.ant 0 MC.t (by decide +kernel)) (h.ant 1 MC.t (by decide +kernel))
    (hnz MC.t (by decide +kernel))
  have hy := cand_y (φ MC.y) (h.inv_map (g := MC.y) (by decide +kernel))
    (h.ant 0 MC.y (by decide +kernel)) (h.ant 6 MC.y (by decide +kernel))
    (hnz MC.y (by decide +kernel))
  have hu := cand_u (φ MC.u) (h.inv_map (g := MC.u) (by decide +kernel))
    (h.ant 1 MC.u (by decide +kernel)) (h.ant 2 MC.u (by decide +kernel))
    (hnz MC.u (by decide +kernel))
  have hv := cand_v (φ MC.v) (h.inv_map (g := MC.v) (by decide +kernel))
    (h.ant 2 MC.v (by decide +kernel)) (h.ant 6 MC.v (by decide +kernel))
    (hnz MC.v (by decide +kernel))
  have hw := cand_w (φ MC.w₁) (h.inv_map (g := MC.w₁) (by decide +kernel))
    (h.ant 3 MC.w₁ (by decide +kernel)) (h.ant 7 MC.w₁ (by decide +kernel))
    (hnz MC.w₁ (by decide +kernel))
  obtain ⟨i₁, hi₁⟩ := idx_C _ (by simp) _ ht
  obtain ⟨i₂, hi₂⟩ := idx_C _ (by simp) _ hy
  obtain ⟨i₃, hi₃⟩ := idx_C _ (by simp) _ hu
  obtain ⟨i₄, hi₄⟩ := idx_C _ (by simp) _ hv
  obtain ⟨i₅, hi₅⟩ := idx_C _ (by simp) _ hw
  obtain ⟨hm₁, hr, e₁, e₂, e₃, e₄, e₅⟩ := stageA i₁ i₂ i₃ i₄ i₅
  rw [hi₁] at e₁
  rw [hi₂] at e₂
  rw [hi₃] at e₃
  rw [hi₄] at e₄
  rw [hi₅] at e₅
  set m₁ := ofCode (tget mATab 8 (256 * i₁.val + 64 * i₂.val + 16 * i₃.val + 4 * i₄.val +
    i₅.val)) with hm₁def
  set r := tget rATab 5 (256 * i₁.val + 64 * i₂.val + 16 * i₃.val + 4 * i₄.val + i₅.val)
    with hrdef
  set ψ : MC →* MC := (MulAut.conj m₁).toMonoidHom.comp h.hom with hψ
  have hψa : ∀ x, ψ x = m₁ * φ x * m₁⁻¹ := fun x => rfl
  have hw₂ : ψ MC.w₂ * ψ MC.w₂ = 1 := by
    rw [← map_mul, show MC.w₂ * MC.w₂ = 1 by decide +kernel, map_one]
  have hw₂1 : ψ MC.w₂ ≠ 1 := by
    intro e
    rw [hψa] at e
    have e' : φ MC.w₂ = φ 1 := by
      rw [h.map_one]
      calc φ MC.w₂ = m₁⁻¹ * (m₁ * φ MC.w₂ * m₁⁻¹) * m₁ := by group
        _ = 1 := by rw [e]; group
    exact absurd (h.injective e') (by decide +kernel)
  obtain ⟨n, hn⟩ := cand_inv _ hw₂ hw₂1
  have himgs : imgs (rep r 0) (rep r 1) (rep r 2) (rep r 3) (rep r 4) (invList.getD n 1) =
      MC.gens.map ψ := by
    rw [← e₁, ← e₂, ← e₃, ← e₄, ← e₅, hn]
    simp only [imgs, MC.gens, List.map_cons, List.map_nil, ← hψa, ← map_inv, ← map_mul,
      ← z_eq, ← k_eq]
  have hrel := himgs ▸ w2Rel_map ψ
  obtain ⟨hm₂, hj, hmap⟩ := stageB ⟨r, hr⟩ n hrel
  rw [himgs, List.map_map] at hmap
  set m₂ := ofCode (tget sBTab 12 (71 * (⟨r, hr⟩ : Fin 32).val + n.val) / 2 % 256) with hm₂def
  refine ⟨m₂ * m₁, inR1_mul _ _ hm₂ hm₁,
    ⟨tget sBTab 12 (71 * (⟨r, hr⟩ : Fin 32).val + n.val) / 512 % 8, Nat.mod_lt _ (by norm_num)⟩,
    fun g hg => ?_⟩
  have := (List.map_inj_left.mp hmap) g hg
  simp only [Function.comp_apply] at this
  rw [← this, hψa]
  group

end CFSG.ComponentClassification.HSFLit.KD8c
