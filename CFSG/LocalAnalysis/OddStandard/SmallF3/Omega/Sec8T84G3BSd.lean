module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g3b_mem_sup_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [(h a' ha' b hb).symm]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 := congrArg (fun x => x⁻¹) (h a ha b hb)
        simpa [mul_inv_rev] using h1 }
  have hle : A ⊔ B ≤ S := sup_le
    (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

theorem sec8t84g3b_mem_normalizer_of_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) ?_
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm.le

theorem sec8t84g3b_conj_sup {G : Type} [Group G] {A B C : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ C) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ C) :
    ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ C := by
  have h : A ⊔ B ≤ C.comap (MulAut.conj g).toMonoidHom := sup_le hA hB
  exact fun x hx => h hx

theorem sec8t84g3b_pow_sq {G : Type} [Group G] {x w : G} {Y : Subgroup G} (hw : w ∈ Y)
    (hxx : x * x = w * w) (hodd : Odd (orderOf x)) : x ∈ Y := by
  obtain ⟨m, hm⟩ := hodd
  have hx1 : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have hxpow : x = (x * x) ^ (m + 1) := by
    calc x = x ^ (2 * m + 1) * x := by rw [hx1, one_mul]
      _ = x ^ (2 * m + 1 + 1) := (pow_succ x (2 * m + 1)).symm
      _ = x ^ (2 * (m + 1)) := by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
      _ = (x * x) ^ (m + 1) := by rw [pow_mul, pow_two]
  rw [hxpow, hxx]
  exact Y.pow_mem (Y.mul_mem hw hw) _

structure Sec8T84G3BSide (G : Type) [Group G] [Finite G]
    (E E0 Y Y' V V' F F' P H : Subgroup G) : Prop where
  Y_le : Y ≤ normalizer (E : Set G)
  Y'_le : Y' ≤ normalizer (E : Set G)
  ydata : Sec8T84YData G Y (oddCoreIn (normalizer (E : Set G))) V H
  P_syl : IsSylow2Of P Y
  F_le_P : F ≤ P
  F_e16 : IsElemAb2 F 4
  F_ne : F ≠ V
  F'_le : F' ≤ Y'
  V_eq : V = E ⊓ Y
  V'_eq : V' = E ⊓ Y'
  E0_eq : E0 = F ⊔ F'
  FF'_comm : ∀ f ∈ F, ∀ f' ∈ F', f * f' = f' * f
  N_le' : oddCoreIn (normalizer (E : Set G)) ≤ Y'
  comm : ∀ a ∈ Y, ∀ b ∈ Y', a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G))
  inf : Y ⊓ Y' ≤ oddCoreIn (normalizer (E : Set G))
  odd_mem : ∀ x ∈ normalizer (E : Set G), Odd (orderOf x) → ∃ a ∈ Y, ∃ b ∈ Y', x = a * b
  cent' : Y' ⊓ centralizer (V' : Set G) ≤ V' ⊔ oddCoreIn (normalizer (E : Set G))
  Y_cent' : ∀ y ∈ Y, ∀ v ∈ V', y * v = v * y
  N_cent' : ∀ v ∈ V', ∀ o ∈ oddCoreIn (normalizer (E : Set G)), v * o = o * v
  V'_sq : ∀ v ∈ V', v * v = 1
  W_inf : (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥
  O_eq : oddCoreIn (sec8t84g_Q E E0) = sec8t84g_Q E E0 ⊓ oddCoreIn (normalizer (E : Set G))
  frattini : ∀ x ∈ normalizer (E : Set G),
    x ∈ normalizer ((E0 ⊔ oddCoreIn (normalizer (E : Set G)) : Subgroup G) : Set G) →
      ∃ n ∈ oddCoreIn (normalizer (E : Set G)), x * n ∈ sec8t84g_Q E E0
  U_le_Q : V ⊔ F ≤ sec8t84g_Q E E0
  UU'_comm : ∀ u ∈ V ⊔ F, ∀ u' ∈ V' ⊔ F', u * u' = u' * u

variable {G : Type} [Group G] [Finite G] {E E0 Y Y' V V' F F' P H : Subgroup G}

namespace Sec8T84G3BSide

theorem F_le_Y (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : F ≤ Y :=
  S.F_le_P.trans S.P_syl.1

theorem V_le_E (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V ≤ E := S.V_eq ▸ inf_le_left

theorem V'_le_E (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V' ≤ E :=
  S.V'_eq ▸ inf_le_left

theorem V'_le_Y' (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V' ≤ Y' :=
  S.V'_eq ▸ inf_le_right

theorem F_le_E0 (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : F ≤ E0 :=
  S.E0_eq ▸ le_sup_left

theorem F'_le_E0 (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : F' ≤ E0 :=
  S.E0_eq ▸ le_sup_right

theorem U_le_W (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V ⊔ F ≤ E ⊔ E0 :=
  sup_le_sup S.V_le_E S.F_le_E0

theorem U'_le_W (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V' ⊔ F' ≤ E ⊔ E0 :=
  sup_le_sup S.V'_le_E S.F'_le_E0

theorem U'_le_Y' (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V' ⊔ F' ≤ Y' :=
  sup_le S.V'_le_Y' S.F'_le

theorem U_le_Y (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : V ⊔ F ≤ Y :=
  sup_le S.ydata.V_le S.F_le_Y

theorem N_le (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) :
    oddCoreIn (normalizer (E : Set G)) ≤ Y := S.ydata.O_le

theorem E0_inf (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) : E0 ⊓ Y ≤ F := by
  intro x hx
  have hx0 : x ∈ F ⊔ F' := S.E0_eq ▸ hx.1
  obtain ⟨f, hf, f', hf', rfl⟩ := sec8t84g3b_mem_sup_comm S.FF'_comm hx0
  have hf'Y : f' ∈ Y := by
    have h1 := Y.mul_mem (Y.inv_mem (S.F_le_Y hf)) hx.2
    simpa using h1
  have hf'N : f' ∈ oddCoreIn (normalizer (E : Set G)) := S.inf ⟨hf'Y, S.F'_le hf'⟩
  have hf'W : f' ∈ E ⊔ E0 := Subgroup.mem_sup_right (S.F'_le_E0 hf')
  have h2 : f' ∈ (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨hf'W, hf'N⟩
  rw [S.W_inf, Subgroup.mem_bot] at h2
  rw [h2, mul_one]
  exact hf

theorem conj_F (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {y : G} (hy : y ∈ Y)
    (hy0 : y ∈ normalizer (E0 : Set G)) : ∀ f ∈ F, y * f * y⁻¹ ∈ F := by
  intro f hf
  have h1 : y * f * y⁻¹ ∈ E0 := (Subgroup.mem_normalizer_iff.mp hy0 f).mp (S.F_le_E0 hf)
  have h2 : y * f * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy (S.F_le_Y hf)) (Y.inv_mem hy)
  exact S.E0_inf ⟨h1, h2⟩

theorem conj_V (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {y : G} (hy : y ∈ Y) :
    ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
  intro v hv
  have hvE : v ∈ E := S.V_le_E hv
  have hvY : v ∈ Y := S.ydata.V_le hv
  have h1 : y * v * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (S.Y_le hy) v).mp hvE
  have h2 : y * v * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hvY) (Y.inv_mem hy)
  rw [S.V_eq]
  exact ⟨h1, h2⟩

theorem odd_Y (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {x : G}
    (hx : x ∈ normalizer (E : Set G)) (hodd : Odd (orderOf x))
    (hxc : ∀ v ∈ V', x * v = v * x) : x ∈ Y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := S.odd_mem x hx hodd
  have hbc : b ∈ centralizer (V' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : a * b * v = v * (a * b) := (hxc v hv)
    have h2 : a * v = v * a := S.Y_cent' a ha v hv
    have h3 : a * (b * v) = a * (v * b) := by
      calc a * (b * v) = a * b * v := by group
        _ = v * (a * b) := h1
        _ = (v * a) * b := by group
        _ = (a * v) * b := by rw [h2]
        _ = a * (v * b) := by group
    exact (mul_left_cancel h3).symm
  obtain ⟨v, hv, n, hn, rfl⟩ := sec8t84g3b_mem_sup_comm (fun v hv n hn => S.N_cent' v hv n hn)
    (S.cent' ⟨hb, hbc⟩)
  have hvn : v * n = n * v := S.N_cent' v hv n hn
  set a' : G := a * n with ha'
  have ha'Y : a' ∈ Y := Y.mul_mem ha (S.N_le hn)
  have hxe : a * (v * n) = a' * v := by
    calc a * (v * n) = a * (n * v) := by rw [hvn]
      _ = a' * v := by rw [ha']; group
  have hva : v * a' = a' * v := by
    calc v * a' = v * a * n := by rw [ha']; group
      _ = a * v * n := by rw [S.Y_cent' a ha v hv]
      _ = a * (v * n) := by group
      _ = a * (n * v) := by rw [hvn]
      _ = a' * v := by rw [ha']; group
  have hsq : (a * (v * n)) * (a * (v * n)) = a' * a' := by
    rw [hxe]
    calc a' * v * (a' * v) = a' * (v * a') * v := by group
      _ = a' * (a' * v) * v := by rw [hva]
      _ = a' * a' * (v * v) := by group
      _ = a' * a' := by rw [S.V'_sq v hv, mul_one]
  exact sec8t84g3b_pow_sq ha'Y hsq hodd

end Sec8T84G3BSide

end CFSG.OddStandard.SmallF3.Omega
