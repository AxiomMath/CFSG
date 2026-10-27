module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Hyp

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def rep (v : V4) : V4 :=
  if v.1 = 0 ∧ v.2.1 = 0 then (0, 0, 1, v.2.2.2) else (1, 0, 1, v.2.2.2)

theorem rep_cases : ∀ v : V4, v.2.2.1 = 1 →
    v = rep v ∨ v = lin dCols (rep v) ∨ v = lin dCols (lin dCols (rep v)) := by decide

theorem rep_cases' : ∀ v : V4, v.2.2.1 = 1 →
    rep v = v ∨ rep v = lin dCols v ∨ rep v = lin dCols (lin dCols v) := by decide

theorem rep_eq : ∀ v : V4, rep v = ((rep v).1, 0, 1, (rep v).2.2.2) := by decide

theorem card_shape : ∀ a e : Fin 2, (a, e) ≠ (0, 0) →
    (Finset.univ.filter (fun v : V4 => v.2.2.1 = 1 ∧
      (((rep v).1, (rep v).2.2.2) = (0, 0) ∨ ((rep v).1, (rep v).2.2.2) = (a, e)))).card =
      if a = 0 then 2 else 4 := by decide

theorem rep_tz : ∀ v : V4, (v.2.2.1 = 1 ∧ (((rep v).1, (rep v).2.2.2) = (0, 0) ∨
    ((rep v).1, (rep v).2.2.2) = (1, 0))) ↔ (v.2.2.1 = 1 ∧ v.2.2.2 = 0) := by decide

theorem card_tz : (Finset.univ.filter (fun v : V4 => v.2.2.1 = 1 ∧ v.2.2.2 = 0)).card = 4 := by
  decide

theorem card_three : (Finset.univ.filter (fun v : V4 =>
    v = (1, 0, 0, 0) ∨ v = (0, 1, 0, 0) ∨ v = (1, 1, 0, 0))).card = 3 := by decide

theorem card_two : (Finset.univ.filter (fun v : V4 =>
    v = (0, 1, 0, 0) ∨ v = (1, 1, 0, 0))).card = 2 := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Inst

variable (I : S.Inst)

@[expose] def orbitN : Set X := {e | ∃ n ∈ normalizer (I.E : Set X), n * S.t * n⁻¹ = e}

theorem wV_injective' : Function.Injective I.wV := fun _ _ h => I.wV_injective h

theorem ncard_image_wV (P : V4 → Prop) [DecidablePred P] :
    (I.wV '' {v | P v}).ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_image_of_injective _ I.wV_injective', ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem t_eq_wV : S.t = I.wV (0, 0, 1, 0) := by simp [wV]

theorem z_eq_wV : S.z = I.wV (1, 0, 0, 0) := by simp [wV]

theorem yi_eq_wV : I.yi = I.wV (0, 1, 0, 0) := by simp [wV]

theorem zyi_eq_wV : S.z * I.yi = I.wV (1, 1, 0, 0) := by simp [wV]

theorem orbit_z (hO : S.Fus) :
    {y | ∃ g ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X), g * S.z * g⁻¹ = y} =
      I.wV '' {v | v = (1, 0, 0, 0) ∨ v = (0, 1, 0, 0) ∨ v = (1, 1, 0, 0)} := by
  obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases I.conj_mem_three hO hg (Or.inl rfl) with h | h | h
    · exact ⟨(1, 0, 0, 0), Or.inl rfl, by rw [h, I.z_eq_wV]⟩
    · exact ⟨(0, 1, 0, 0), Or.inr (Or.inl rfl), by rw [h, I.yi_eq_wV]⟩
    · exact ⟨(1, 1, 0, 0), Or.inr (Or.inr rfl), by rw [h, I.zyi_eq_wV]⟩
  · rintro ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [I.z_eq_wV]; group⟩
    · exact ⟨d, hd, by rw [hdz, I.yi_eq_wV]⟩
    · refine ⟨d * d, mul_mem hd hd, ?_⟩
      calc d * d * S.z * (d * d)⁻¹ = d * (d * S.z * d⁻¹) * d⁻¹ := by group
        _ = I.wV (1, 1, 0, 0) := by rw [hdz, hdy, I.zyi_eq_wV]

theorem orbit_yi (hO : S.Fus) :
    {y | ∃ g ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X) ⊓
        centralizer ({S.z} : Set X), g * I.yi * g⁻¹ = y} =
      I.wV '' {v | v = (0, 1, 0, 0) ∨ v = (1, 1, 0, 0)} := by
  have hxN : S.x ∈ normalizer (I.E : Set X) := S.T_le_normalizer_E I.yi_mem S.x_mem.1
  have hxt : S.x ∈ centralizer ({S.t} : Set X) := S.data.T_le_centralizer S.x_mem.1
  have hxz : S.x ∈ centralizer ({S.z} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    exact (S.z_comm_of_mem_T S.x_mem.1).symm
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hg1, hgz⟩ := mem_inf.mp hg
    have hgz' : g * S.z * g⁻¹ = S.z := by
      rw [mem_centralizer_singleton_iff.mp hgz]; group
    rcases I.conj_mem_three hO hg1 (Or.inr (Or.inl rfl)) with h | h | h
    · exfalso
      have : I.yi = S.z := by
        calc I.yi = g⁻¹ * (g * I.yi * g⁻¹) * g := by group
          _ = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [h, hgz']
          _ = S.z := by group
      rw [I.yi_eq_wV, I.z_eq_wV] at this
      exact absurd (I.wV_injective this) (by decide)
    · exact ⟨(0, 1, 0, 0), Or.inl rfl, by rw [h, I.yi_eq_wV]⟩
    · exact ⟨(1, 1, 0, 0), Or.inr rfl, by rw [h, I.zyi_eq_wV]⟩
  · rintro ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl
    · exact ⟨1, one_mem _, by rw [I.yi_eq_wV]; group⟩
    · exact ⟨S.x, mem_inf.mpr ⟨mem_inf.mpr ⟨hxN, hxt⟩, hxz⟩, by rw [I.x_conj_yi, I.zyi_eq_wV]⟩

theorem stab_eq :
    normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X) ⊓ centralizer ({S.z} : Set X) ⊓
      centralizer ({I.yi} : Set X) = centralizer (I.E : Set X) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨⟨hgN, hgt⟩, hgz⟩, hgy⟩ := mem_inf.mp hg
    have hgk : g * I.ki * g⁻¹ = I.ki := I.conj_ki_of_mem_NC (mem_inf.mpr ⟨hgN, hgt⟩)
    have hz : Commute g S.z := mem_centralizer_singleton_iff.mp hgz
    have hy : Commute g I.yi := mem_centralizer_singleton_iff.mp hgy
    have ht : Commute g S.t := mem_centralizer_singleton_iff.mp hgt
    have hk : Commute g I.ki := by
      show g * I.ki = I.ki * g
      calc g * I.ki = g * I.ki * g⁻¹ * g := by group
        _ = I.ki * g := by rw [hgk]
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨v, rfl⟩ := I.eq_wV he
    have hc : Commute g (I.wV v) := by
      simp only [wV]
      exact (((hz.pow_right _).mul_right (hy.pow_right _)).mul_right (ht.pow_right _)).mul_right
        (hk.pow_right _)
    exact hc.eq.symm
  · intro c hc
    have hcN := I.centralizer_le_normalizer hc
    have hcm : ∀ {e : X}, e ∈ I.E → c ∈ centralizer ({e} : Set X) := fun he => by
      rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hc) _ he).symm
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨hcN, hcm I.t_mem_E⟩, hcm I.z_mem_E⟩,
      hcm I.yi_mem_E⟩

theorem card_normalizer_eq (hO : S.Fus) :
    Nat.card (normalizer (I.E : Set X)) =
      I.orbitN.ncard * (6 * Nat.card (centralizer (I.E : Set X))) := by
  set N := normalizer (I.E : Set X) with hN
  set G₁ := N ⊓ centralizer ({S.t} : Set X) with hG₁
  set G₂ := G₁ ⊓ centralizer ({S.z} : Set X) with hG₂
  set C := centralizer (I.E : Set X) with hC
  have h1 : G₁.relIndex N = I.orbitN.ncard := relIndex_inf_centralizer_eq_ncard N S.t
  have h2 : G₂.relIndex G₁ = 3 := by
    rw [hG₂, relIndex_inf_centralizer_eq_ncard G₁ S.z, I.orbit_z hO, I.ncard_image_wV,
      card_three]
  have h3 : C.relIndex G₂ = 2 := by
    rw [hC, ← I.stab_eq, relIndex_inf_centralizer_eq_ncard G₂ I.yi, I.orbit_yi hO,
      I.ncard_image_wV, card_two]
  have hCG₂ : C ≤ G₂ := by rw [hC, ← I.stab_eq]; exact inf_le_left
  have hG₂G₁ : G₂ ≤ G₁ := inf_le_left
  have hG₁N : G₁ ≤ N := inf_le_left
  have hrel : C.relIndex N = 2 * 3 * I.orbitN.ncard := by
    rw [← Subgroup.relIndex_mul_relIndex C G₂ N hCG₂ (hG₂G₁.trans hG₁N),
      ← Subgroup.relIndex_mul_relIndex G₂ G₁ N hG₂G₁ hG₁N, h1, h2, h3]
    ring
  have hcard : C.relIndex N * Nat.card C = Nat.card N := by
    have := relIndex_mul_card (H := C) (K := N)
    rwa [inf_of_le_left (hCG₂.trans (hG₂G₁.trans hG₁N))] at this
  rw [← hcard, hrel]
  ring

theorem conj_mem_orbitN {n e : X} (hn : n ∈ normalizer (I.E : Set X)) (he : e ∈ I.orbitN) :
    n * e * n⁻¹ ∈ I.orbitN := by
  obtain ⟨m, hm, rfl⟩ := he
  exact ⟨n * m, mul_mem hn hm, by group⟩

theorem eq_wV_of_mem_orbitN (hO : S.Fus) {e : X} (he : e ∈ I.orbitN) :
    ∃ v : V4, v.2.2.1 = 1 ∧ e = I.wV v := by
  obtain ⟨n, hn, rfl⟩ := he
  obtain ⟨a, b, d, h⟩ := I.conj_t_eq hO hn
  refine ⟨(a, b, 1, d), rfl, ?_⟩
  rw [h, show ((a, b, (1 : Fin 2), d) : V4) = addV (0, 0, 1, 0) (a, b, 0, d) by simp [addV],
    I.wV_add, ← I.t_eq_wV]

theorem mem_orbitN_iff_rep {v : V4} (hv : v.2.2.1 = 1) :
    I.wV v ∈ I.orbitN ↔ I.wV (rep v) ∈ I.orbitN := by
  obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
  have hdM : I.Mat d dCols := ⟨hd.1, hdc⟩
  have hcl : ∀ w : V4, I.wV w ∈ I.orbitN → I.wV (lin dCols w) ∈ I.orbitN := fun w hw => by
    rw [← hdM.conj]
    exact I.conj_mem_orbitN hd.1 hw
  constructor
  · intro h
    rcases rep_cases' v hv with h' | h' | h' <;> rw [h']
    · exact h
    · exact hcl _ h
    · exact hcl _ (hcl _ h)
  · intro h
    rcases rep_cases v hv with h' | h' | h' <;> rw [h']
    · exact h
    · exact hcl _ h
    · exact hcl _ (hcl _ h)

theorem orbitN_eq (hO : S.Fus) {a₀ e₀ : Fin 2}
    (hB : ∀ a e : Fin 2, I.wV (a, 0, 1, e) ∈ I.orbitN ↔ (a, e) = (0, 0) ∨ (a, e) = (a₀, e₀)) :
    I.orbitN = I.wV '' {v | v.2.2.1 = 1 ∧
      (((rep v).1, (rep v).2.2.2) = (0, 0) ∨ ((rep v).1, (rep v).2.2.2) = (a₀, e₀))} := by
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, rfl⟩ := I.eq_wV_of_mem_orbitN hO hy
    have h1 := (I.mem_orbitN_iff_rep hv).mp hy
    rw [rep_eq v] at h1
    exact ⟨v, ⟨hv, (hB _ _).mp h1⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hc⟩, rfl⟩
    have h1 := (hB _ _).mpr hc
    rw [← rep_eq v] at h1
    exact (I.mem_orbitN_iff_rep hv).mpr h1

theorem ncard_orbitN (hO : S.Fus) {a₀ e₀ : Fin 2} (h0 : (a₀, e₀) ≠ (0, 0))
    (hB : ∀ a e : Fin 2, I.wV (a, 0, 1, e) ∈ I.orbitN ↔ (a, e) = (0, 0) ∨ (a, e) = (a₀, e₀)) :
    I.orbitN.ncard = if a₀ = 0 then 2 else 4 := by
  rw [I.orbitN_eq hO hB, I.ncard_image_wV, card_shape a₀ e₀ h0]

end Inst

omit [Finite X] in
theorem map_centralizer_le (P : Subgroup X) (g : X) :
    (centralizer (P : Set X)).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨p, hp, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hc) p hp]

theorem card_normalizer_map (P : Subgroup X) (g : X) :
    Nat.card (normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) =
      Nat.card (normalizer (P : Set X)) := by
  apply le_antisymm
  · have h := Subgroup.le_normalizer_map (H := P.map (MulAut.conj g).toMonoidHom)
      (MulAut.conj g⁻¹).toMonoidHom
    rw [map_conj_inv rfl] at h
    have := Subgroup.card_le_of_le h
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at this
  · have := Subgroup.card_le_of_le (Subgroup.le_normalizer_map (H := P)
      (MulAut.conj g).toMonoidHom)
    rwa [card_map_of_injective (MulAut.conj g).injective] at this

theorem card_centralizer_map (P : Subgroup X) (g : X) :
    Nat.card (centralizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) =
      Nat.card (centralizer (P : Set X)) := by
  apply le_antisymm
  · have h := map_centralizer_le (P.map (MulAut.conj g).toMonoidHom) g⁻¹
    rw [map_conj_inv rfl] at h
    have := Subgroup.card_le_of_le h
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at this
  · have := Subgroup.card_le_of_le (map_centralizer_le P g)
    rwa [card_map_of_injective (MulAut.conj g).injective] at this

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem mem_orbitN_B (I : S.Inst) {w₀ : X} (hw₀ : w₀ ∈ S.T₂of T₁) (hw₀T : w₀ ∉ S.data.T)
    {b : X} (hb : b ∈ S.B) : b ∈ I.orbitN ↔ b = S.t ∨ b = w₀ * S.t * w₀⁻¹ := by
  have hw₀N₁ : w₀ ∈ normalizer (S.E (S.x * S.y) : Set X) := (mem_inf.mp hw₀).2
  have hw₀N₂ : w₀ ∈ normalizer (S.E S.y : Set X) := H.T₂of_le_normalizer_E₂ hw₀
  have hw₀N : w₀ ∈ normalizer (I.E : Set X) := by
    rcases I.yi_or with h | h
    · show w₀ ∈ normalizer (S.E I.yi : Set X)
      rw [h]; exact hw₀N₂
    · show w₀ ∈ normalizer (S.E I.yi : Set X)
      rw [h]; exact hw₀N₁
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨h, hh, hht⟩ := H.exists_conj_T₁ hb ⟨n, rfl⟩
    by_cases hhT : h ∈ S.T₂of T₁
    · rw [← hht]
      exact (H.mem_T₂_iff hw₀ hw₀T hh).mp hhT
    · exfalso
      have hhN : h ∉ normalizer (S.E (S.x * S.y) : Set X) := fun h' =>
        hhT (mem_inf.mpr ⟨hh, h'⟩)
      obtain ⟨h1, h2⟩ := H.swap_of_not_mem hh hhN
      rcases I.yi_or with hI | hI
      ·
        have hnN : n ∈ normalizer (S.E S.y : Set X) := by
          have : n ∈ normalizer (S.E I.yi : Set X) := hn
          rwa [hI] at this
        refine S.not_conj_E_y_E_xy (g := h⁻¹ * n) ?_ fun e he => ?_
        · rw [mem_centralizer_singleton_iff]
          calc h⁻¹ * n * S.t = h⁻¹ * (n * S.t * n⁻¹) * n := by group
            _ = h⁻¹ * (h * S.t * h⁻¹) * n := by rw [hht]
            _ = S.t * (h⁻¹ * n) := by group
        · have h3 : n * e * n⁻¹ ∈ S.E S.y := (mem_normalizer_iff.mp hnN e).mp he
          have h4 : h⁻¹ * (n * e * n⁻¹) * h⁻¹⁻¹ ∈ S.E (S.x * S.y) := by
            rw [← map_conj_inv h1]
            exact ⟨_, h3, rfl⟩
          simpa [mul_assoc] using h4
      ·
        have hnN : n ∈ normalizer (S.E (S.x * S.y) : Set X) := by
          have : n ∈ normalizer (S.E I.yi : Set X) := hn
          rwa [hI] at this
        refine S.not_conj_E_y_E_xy (g := n⁻¹ * h) ?_ fun e he => ?_
        · rw [mem_centralizer_singleton_iff]
          calc n⁻¹ * h * S.t = n⁻¹ * (h * S.t * h⁻¹) * h := by group
            _ = n⁻¹ * (n * S.t * n⁻¹) * h := by rw [hht]
            _ = S.t * (n⁻¹ * h) := by group
        · have h3 : h * e * h⁻¹ ∈ S.E (S.x * S.y) := by
            rw [← h2]
            exact ⟨e, he, rfl⟩
          have h4 := (mem_normalizer_iff.mp (inv_mem hnN) _).mp h3
          simpa [mul_assoc] using h4
  · rintro (rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · exact ⟨w₀, hw₀N, rfl⟩

theorem ncard_orbitN_eq : S.inst₁.orbitN.ncard = S.inst₂.orbitN.ncard := by
  obtain ⟨g₀, -, -, hg₀⟩ := H.exists_g₀
  have h1 := S.inst₁.card_normalizer_eq H.fus
  have h2 := S.inst₂.card_normalizer_eq H.fus
  have hE₂ : S.inst₂.E = S.inst₁.E.map (MulAut.conj g₀).toMonoidHom := hg₀.symm
  rw [hE₂, card_normalizer_map, card_centralizer_map, h1] at h2
  have hpos : 0 < 6 * Nat.card (centralizer (S.inst₁.E : Set X)) :=
    Nat.mul_pos (by norm_num) Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h2

omit H in
theorem wV₁ (a e : Fin 2) : S.inst₁.wV (a, 0, 1, e) = S.t * S.z ^ (a : ℕ) * S.k ^ (e : ℕ) := by
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    simp [Inst.wV, inst₁, hzt]

omit H in
theorem wV₂ (a e : Fin 2) :
    S.inst₂.wV (a, 0, 1, e) = S.t * S.z ^ ((a + e : Fin 2) : ℕ) * S.k ^ (e : ℕ) := by
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hzz : S.z * S.z = 1 := by rw [← pow_two, S.z_sq]
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with rfl | rfl
  · simp [Inst.wV, inst₂]
  · simp [Inst.wV, inst₂, mul_assoc]
  · simp [Inst.wV, inst₂, hzt]
  · simp only [Inst.wV, inst₂]
    simp only [Fin.isValue, Fin.val_one, pow_one, Fin.val_zero, pow_zero, mul_one]
    rw [show (1 + 1 : Fin 2) = 0 from rfl]
    simp only [Fin.val_zero, pow_zero, mul_one]
    calc S.z * S.t * (S.z * S.k) = S.t * S.z * (S.z * S.k) := by rw [hzt]
      _ = S.t * (S.z * S.z) * S.k := by group
      _ = S.t * S.k := by rw [hzz, mul_one]

theorem conj_w₀_t {w₀ : X} (hw₀ : w₀ ∈ S.T₂of T₁) (hw₀T : w₀ ∉ S.data.T) :
    w₀ * S.t * w₀⁻¹ = S.t * S.z := by
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hb : w₀ * S.t * w₀⁻¹ ∈ S.B := S.conj_mem_B (H.le_normalizer (T₂of_le hw₀)) htB
  have hne : w₀ * S.t * w₀⁻¹ ≠ S.t := by
    intro h
    exact hw₀T (by
      have hc := (H.mem_T₂_iff hw₀ hw₀T (T₂of_le hw₀)).mpr (Or.inl h)
      have hC : w₀ ∈ centralizer ({S.t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        calc w₀ * S.t = w₀ * S.t * w₀⁻¹ * w₀ := by group
          _ = S.t * w₀ := by rw [h]
      have : w₀ ∈ T₁ ⊓ centralizer ({S.t} : Set X) := mem_inf.mpr ⟨T₂of_le hw₀, hC⟩
      rw [H.inf_centralizer] at this
      exact this)
  have hcases := (H.fus _ hb).mp ⟨w₀, rfl⟩
  have hB₁ : ∀ a₀ e₀ : Fin 2, w₀ * S.t * w₀⁻¹ = S.t * S.z ^ (a₀ : ℕ) * S.k ^ (e₀ : ℕ) →
      ∀ a e : Fin 2, S.inst₁.wV (a, 0, 1, e) ∈ S.inst₁.orbitN ↔
        (a, e) = (0, 0) ∨ (a, e) = (a₀, e₀) := by
    intro a₀ e₀ ht a e
    rw [H.mem_orbitN_B S.inst₁ hw₀ hw₀T ((S.inst₁.wV_mem_B_iff _).mpr rfl), ht, ← wV₁ a₀ e₀,
      show S.t = S.inst₁.wV (0, 0, 1, 0) by simp [Inst.wV]]
    constructor
    · rintro (h | h)
      · have := S.inst₁.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inl (Prod.ext this.1 this.2.2.2)
      · have := S.inst₁.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inr (Prod.ext this.1 this.2.2.2)
    · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> rw [h.1, h.2]
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hB₂ : ∀ a₀ e₀ : Fin 2,
      w₀ * S.t * w₀⁻¹ = S.t * S.z ^ ((a₀ + e₀ : Fin 2) : ℕ) * S.k ^ (e₀ : ℕ) →
      ∀ a e : Fin 2, S.inst₂.wV (a, 0, 1, e) ∈ S.inst₂.orbitN ↔
        (a, e) = (0, 0) ∨ (a, e) = (a₀, e₀) := by
    intro a₀ e₀ ht a e
    rw [H.mem_orbitN_B S.inst₂ hw₀ hw₀T ((S.inst₂.wV_mem_B_iff _).mpr rfl), ht, ← wV₂ a₀ e₀,
      show S.t = S.inst₂.wV (0, 0, 1, 0) by simp [Inst.wV]]
    constructor
    · rintro (h | h)
      · have := S.inst₂.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inl (Prod.ext this.1 this.2.2.2)
      · have := S.inst₂.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inr (Prod.ext this.1 this.2.2.2)
    · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> rw [h.1, h.2]
      · exact Or.inl rfl
      · exact Or.inr rfl
  have heq := H.ncard_orbitN_eq
  rcases hcases with h | h | h | h
  · exact absurd h hne
  · exact h
  ·
    exfalso
    have h1 := S.inst₁.ncard_orbitN H.fus (a₀ := 0) (e₀ := 1) (by decide)
      (hB₁ 0 1 (by rw [h]; simp))
    have h2 := S.inst₂.ncard_orbitN H.fus (a₀ := 1) (e₀ := 1) (by decide)
      (hB₂ 1 1 (by rw [h]; simp))
    rw [h1, h2] at heq
    simp at heq
  ·
    exfalso
    have h1 := S.inst₁.ncard_orbitN H.fus (a₀ := 1) (e₀ := 1) (by decide)
      (hB₁ 1 1 (by rw [h]; simp))
    have h2 := S.inst₂.ncard_orbitN H.fus (a₀ := 0) (e₀ := 1) (by decide)
      (hB₂ 0 1 (by rw [h]; simp))
    rw [h1, h2] at heq
    simp at heq

theorem mem_orbitN_iff (I : S.Inst) (v : V4) :
    I.wV v ∈ I.orbitN ↔ v.2.2.1 = 1 ∧ v.2.2.2 = 0 := by
  obtain ⟨w₀, hw₀, hw₀T⟩ := H.exists_w₀
  have hB : ∀ a e : Fin 2, I.wV (a, 0, 1, e) ∈ I.orbitN ↔ (a, e) = (0, 0) ∨ (a, e) = (1, 0) := by
    intro a e
    rw [H.mem_orbitN_B I hw₀ hw₀T ((I.wV_mem_B_iff _).mpr rfl), H.conj_w₀_t hw₀ hw₀T,
      show S.t * S.z = I.wV (1, 0, 1, 0) by
        simp [Inst.wV, S.z_comm_of_mem_T S.data.t_mem_T],
      show S.t = I.wV (0, 0, 1, 0) by simp [Inst.wV]]
    constructor
    · rintro (h | h)
      · have := I.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inl (Prod.ext this.1 this.2.2.2)
      · have := I.wV_injective h
        simp only [Prod.mk.injEq] at this
        exact Or.inr (Prod.ext this.1 this.2.2.2)
    · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> rw [h.1, h.2]
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [I.orbitN_eq H.fus hB]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [← I.wV_injective hwv]
    exact (rep_tz w).mp hw
  · intro hv
    exact ⟨v, (rep_tz v).mpr hv, rfl⟩

theorem ncard_orbitN_four (I : S.Inst) : I.orbitN.ncard = 4 := by
  have heq : I.orbitN = I.wV '' {v | v.2.2.1 = 1 ∧ v.2.2.2 = 0} := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, -, rfl⟩ := I.eq_wV_of_mem_orbitN H.fus hy
      exact ⟨v, (H.mem_orbitN_iff I v).mp hy, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (H.mem_orbitN_iff I v).mpr hv
  rw [heq, I.ncard_image_wV, card_tz]

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
