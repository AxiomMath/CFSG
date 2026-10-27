module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4WCyc

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped Pointwise

theorem klein_v_facts {G : Type*} [Group G] {Y : Subgroup G} {A B C x : G}
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y) (hx : x ∈ Y)
    (hA : ∀ y ∈ Y, A * y * A⁻¹ ∈ Y) (hB : ∀ y ∈ Y, B * y * B⁻¹ ∈ Y)
    (hAA : A * A = 1) (hBA : B * A = C) :
    A * (x * (A * x * A⁻¹)) * A⁻¹ = x * (A * x * A⁻¹) ∧
    B * (x * (A * x * A⁻¹)) * B⁻¹ =
      (x * (A * x * A⁻¹))⁻¹ * (x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹)) ∧
    (x * (A * x * A⁻¹)) * B * (x * (A * x * A⁻¹))⁻¹ =
      (x * (A * x * A⁻¹)) * (x * (A * x * A⁻¹)) *
        (x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹))⁻¹ * B ∧
    ((x * (A * x * A⁻¹)) * (x * (A * x * A⁻¹))) * B *
        ((x * (A * x * A⁻¹)) * (x * (A * x * A⁻¹)))⁻¹ * B⁻¹ =
      ((x * (A * x * A⁻¹)) * (x * (A * x * A⁻¹))) * ((x * (A * x * A⁻¹)) * (x * (A * x * A⁻¹))) *
        ((x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹)) *
          (x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹)))⁻¹ := by
  have hxA := hA x hx
  have hxB := hB x hx
  have hxC : C * x * C⁻¹ ∈ Y := by
    have := hB _ hxA
    rwa [show B * (A * x * A⁻¹) * B⁻¹ = B * A * x * (B * A)⁻¹ by group, hBA] at this
  generalize hN : x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹) = N
  have hNv : N = x * (A * x * A⁻¹) * ((B * x * B⁻¹) * (C * x * C⁻¹)) := by rw [← hN]; group
  have hNY : N ∈ Y := hN ▸ mul_mem (mul_mem (mul_mem hx hxA) hxB) hxC
  generalize hv : x * (A * x * A⁻¹) = v at hNv ⊢
  have hvY : v ∈ Y := hv ▸ mul_mem hx hxA
  have h1 : A * v * A⁻¹ = v := by
    rw [← hv]
    calc A * (x * (A * x * A⁻¹)) * A⁻¹ = (A * x * A⁻¹) * ((A * A) * x * (A * A)⁻¹) := by group
      _ = (A * x * A⁻¹) * x := by rw [hAA]; group
      _ = x * (A * x * A⁻¹) := hY _ hxA _ hx
  have h2 : B * v * B⁻¹ = v⁻¹ * N := by
    rw [hNv, ← hv]
    calc B * (x * (A * x * A⁻¹)) * B⁻¹ = (B * x * B⁻¹) * ((B * A) * x * (B * A)⁻¹) := by group
      _ = (B * x * B⁻¹) * (C * x * C⁻¹) := by rw [hBA]
      _ = _ := by group
  have hvN : v * N⁻¹ = N⁻¹ * v := hY _ hvY _ (inv_mem hNY)
  have h3 : v * B * v⁻¹ = v * v * N⁻¹ * B := by
    calc v * B * v⁻¹ = v * (B * v * B⁻¹)⁻¹ * B := by group
      _ = v * (v⁻¹ * N)⁻¹ * B := by rw [h2]
      _ = v * (N⁻¹ * v) * B := by group
      _ = v * v * N⁻¹ * B := by rw [← hvN]; group
  refine ⟨h1, h2, h3, ?_⟩
  calc v * v * B * (v * v)⁻¹ * B⁻¹ = v * v * ((B * v * B⁻¹)⁻¹ * (B * v * B⁻¹)⁻¹) := by group
    _ = v * v * ((v⁻¹ * N)⁻¹ * (v⁻¹ * N)⁻¹) := by rw [h2]
    _ = v * v * ((N⁻¹ * v) * (N⁻¹ * v)) := by group
    _ = v * v * ((v * N⁻¹) * (v * N⁻¹)) := by rw [hvN]
    _ = v * v * (v * (N⁻¹ * v) * N⁻¹) := by group
    _ = v * v * (v * (v * N⁻¹) * N⁻¹) := by rw [← hvN]
    _ = v * v * (v * v) * (N * N)⁻¹ := by group

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem z_mem_W
    (h : d.Hyp) :
    d.z ∈ d.W := by
  have := z_mem_ZX₄ (d := d)
  rw [← h.W_inf_H] at this
  exact (Subgroup.mem_inf.1 this).1

theorem conj_mem_W_of_mem_normalizer_ZR
    (h : d.Hyp) (hc : d.CycW) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) {w : G} (hw : w ∈ d.W) : g * w * g⁻¹ ∈ d.W := by
  have hm := h.conj_mem_withT_W hg (mem_sup_left hw : w ∈ d.withT d.W)
  have htW : ∀ k ∈ d.W, d.t * k * d.t ∈ d.W := fun k hk => by
    rw [h.t_conj_W_of_cyc hc hk]
    exact inv_mem hk
  rcases (mem_sup_zpowers_iff h.t_mul_t htW).1 hm with hm | hm
  · exact hm
  · have hsq1 : g * w * g⁻¹ * (g * w * g⁻¹) = 1 := by
      have e := h.mul_t_mul_self_of_cyc hc (one_mem d.A₁) hm
      simp only [one_mul, mul_one] at e
      rwa [mul_assoc (g * w * g⁻¹) d.t d.t, h.t_mul_t, mul_one] at e
    have hww : w * w = 1 := by
      have e : g * (w * w) * g⁻¹ = 1 := by rw [← hsq1]; group
      calc w * w = g⁻¹ * (g * (w * w) * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    by_cases hwz : w ∈ d.ZX₄
    · rcases eq_one_or_eq_z hwz with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [(h.conj_of_mem_normalizer_ZR hg).2, mul_inv_cancel_right]
        exact h.z_mem_W
    · exact absurd ((h.W_sq_of_cyc hc hw hwz).symm.trans hww) z_ne_one

theorem mem_XW_of_comm_z
    (h : d.Hyp)
    (hc : d.CycW) {k : G} (hkH : k ∈ d.H) (hkz : k * d.z = d.z * k) : k ∈ d.XW := by
  have hkN := h.mem_normalizer_ZR_of_comm_z hkH hkz
  have hW : k ∈ normalizer (d.W : Set G) :=
    mem_normalizer_fintype fun w hw => h.conj_mem_W_of_mem_normalizer_ZR hc hkN hw
  refine Subgroup.mem_inf.2 ⟨mem_normalizer_fintype fun y hy => ?_, hW⟩
  have hle : d.AWT ≤ d.AWT.comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact mem_sup_left (mem_sup_left (h.conj_mem_A₁_of_comm_z hkH hkz ha))
    · intro w hw
      exact mem_sup_left (mem_sup_right (h.conj_mem_W_of_mem_normalizer_ZR hc hkN hw))
    · rw [zpowers_le]
      change k * d.t * k⁻¹ ∈ d.AWT
      rw [mem_centralizer_singleton_iff.1 hkH, mul_inv_cancel_right]
      exact mem_sup_right (mem_zpowers _)
  exact hle hy

theorem ι_mem_XW_of_mem_CzSub
    (h : d.Hyp)
    (hc : d.CycW) {α : SU52} (hα : α ∈ CzSub) : d.ι α ∈ d.XW :=
  h.mem_XW_of_comm_z hc (h.L_le_H (d.ι_mem α)) (by
    rw [Data.z, ← map_mul, ← map_mul, comm_of_mem_CzSub hα])

theorem exists_v
    (h : d.Hyp) :
    ∃ v ∈ d.XW, v⁻¹ * d.t * v = d.ι b₀SU * d.t := by
  have hYE := h.Y_eq_E₂
  obtain ⟨x, hx, hxt⟩ := h.exists_E₂_crossed_eq
    (d.ι_mem_pull_iff.2 (genFSU_mem 0) : d.ι (x₁SU 0 1 zero_one_rel) ∈ d.F)
  have hxY : x ∈ d.Y := hYE ▸ hx
  have hX : ∀ c : F4, d.ι (x₂SU c) ∈ d.Lev := fun c => X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩
  have hconjY : ∀ c : F4, ∀ y ∈ d.Y, d.ι (x₂SU c) * y * (d.ι (x₂SU c))⁻¹ ∈ d.Y :=
    fun c y hy => hYE ▸ (mem_normalizer_iff.1 ((h.le_normalizer_E₂).1 (hX c)) y).1 (hYE ▸ hy)
  have hsq : ∀ c : F4, d.ι (x₂SU c) * d.ι (x₂SU c) = 1 := fun c => by
    rw [← map_mul, x₂SU_mul, CharTwo.add_self_eq_zero,
      show x₂SU 0 = 1 from ext_mat (by rw [mat_x₂SU, x₂Mat_zero, mat_one]), map_one]
  have hab : d.ι (x₂SU 1) * d.ι (x₂SU F4.ω) = d.ι (x₂SU (F4.ω + 1)) := by
    rw [← map_mul, x₂SU_mul, add_comm]
  have hba : d.ι (x₂SU F4.ω) * d.ι (x₂SU 1) = d.ι (x₂SU (F4.ω + 1)) := by
    rw [← map_mul, x₂SU_mul]
  have hYc : ∀ y ∈ d.Y, ∀ z ∈ d.Y, y * z = z * y := fun y hy z hz => h.Y_comm hy hz
  have hU : ∀ {y}, y ∈ d.Y → y ∈ d.U := fun hy => h.E₂_le_U (hYE ▸ hy)
  have hvt : (x * (d.ι (x₂SU 1) * x * (d.ι (x₂SU 1))⁻¹))⁻¹ * d.t *
      (x * (d.ι (x₂SU 1) * x * (d.ι (x₂SU 1))⁻¹)) * d.t = d.ι b₀SU := by
    rw [crossed_mul h.t_mul_t
        (h.U_comm_F (hU (hconjY 1 x hxY)) (h.U_crossed_mem_F (hU hxY))).symm,
      hxt, crossed_conj (h.Lev_comm_t (hX 1)), hxt, b₀SU_eq, map_mul, ← x₁_eq_conjX₁, conjX₁,
      map_mul, map_mul, map_inv]
  have hA1 : d.ι (x₂SU 1) ∈ d.A₁ := d.pull_mono X₂sub_le_A₁sub ⟨_, x₂SU_mem 1, rfl⟩
  have hBA1 : d.ι (x₂SU F4.ω) ∈ d.A₁ := d.pull_mono X₂sub_le_A₁sub ⟨_, x₂SU_mem F4.ω, rfl⟩
  have hβF : d.ι b₀SU ∈ d.F := ⟨b₀SU, b₀SU_mem_Fsub, rfl⟩
  have hβA : d.ι b₀SU ∈ d.A₁ := ⟨b₀SU, b₀SU_mem_A₁sub, rfl⟩
  have hconjA := hconjY 1
  have hconjB := hconjY F4.ω
  have hsA := hsq 1
  generalize hA : d.ι (x₂SU 1) = A at hab hba hvt hA1 hconjA hsA
  generalize hB : d.ι (x₂SU F4.ω) = B at hab hba hBA1 hconjB
  generalize hC : d.ι (x₂SU (F4.ω + 1)) = C at hab hba
  have hsB : B * B = 1 := by rw [← hB]; exact hsq F4.ω
  obtain ⟨hNY, hNa, hNb⟩ := klein_norm_comm hYc hxY hconjA hconjB hsA hsB hab hba
  obtain ⟨hvA, -, hvB, hv2B⟩ := klein_v_facts hYc hxY hconjA hconjB hsA hba
  have hNW : x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹) ∈ d.W := by
    refine h.mem_W_of_comm hNY ?_ ?_
    · rw [hA]
      exact hNa.symm
    · rw [hB]
      exact hNb.symm
  generalize hN : x * (A * x * A⁻¹) * (B * x * B⁻¹) * (C * x * C⁻¹) = N at hNW hvB hv2B
  have hvY : x * (A * x * A⁻¹) ∈ d.Y := mul_mem hxY (hconjA x hxY)
  generalize hv : x * (A * x * A⁻¹) = v at hvA hvB hv2B hvt hvY
  have hAv : A * v = v * A := by
    calc A * v = A * v * A⁻¹ * A := by group
      _ = v * A := by rw [hvA]
  have hv2A : v * v ∈ d.A₁ := by
    obtain ⟨f, hf, hfv⟩ := h.U_sq (hU hvY)
    have hv4 := h.F_sq (h.U_sq (hU hvY))
    have hNN := h.W_sq_mem hNW
    refine ⟨f, mem_A₁sub_of_comm_x₂ hf ?_ ?_, hfv⟩
    · have e1 : f * x₂SU 1 * f⁻¹ * (x₂SU 1)⁻¹ = 1 := d.ι_injective (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfv, hA, map_one,
          show v * v * A = A * (v * v) by
            rw [mul_assoc, ← hAv, ← mul_assoc, ← hAv, mul_assoc]]
        group)
      rw [e1]
      exact one_mem _
    · rw [← d.ι_mem_pull_iff, ← Data.ZX₄, map_mul, map_mul, map_mul, map_inv, map_inv, hfv,
        hB, hv2B, hv4, one_mul]
      exact inv_mem hNN
  have hvW : ∀ w ∈ d.W, v * w * v⁻¹ = w := fun w hw => by
    rw [hYc v hvY w (d.W_le_Y hw), mul_inv_cancel_right]
  have hvβ : v * d.ι b₀SU = d.ι b₀SU * v := h.U_comm_F (hU hvY) hβF
  have e : v⁻¹ * d.t * v = d.ι b₀SU * d.t := by
    calc v⁻¹ * d.t * v = (v⁻¹ * d.t * v * d.t) * d.t := by
          rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
      _ = d.ι b₀SU * d.t := by rw [hvt]
  have hvt' : v * d.t * v⁻¹ = (d.ι b₀SU)⁻¹ * d.t := by
    have e2 : d.ι b₀SU * (v * d.t * v⁻¹) = d.t := by
      calc d.ι b₀SU * (v * d.t * v⁻¹) = (d.ι b₀SU * v) * d.t * v⁻¹ := by group
        _ = (v * d.ι b₀SU) * d.t * v⁻¹ := by rw [← hvβ]
        _ = v * (d.ι b₀SU * d.t) * v⁻¹ := by group
        _ = v * (v⁻¹ * d.t * v) * v⁻¹ := by rw [e]
        _ = d.t := by group
    calc v * d.t * v⁻¹ = (d.ι b₀SU)⁻¹ * (d.ι b₀SU * (v * d.t * v⁻¹)) := by group
      _ = (d.ι b₀SU)⁻¹ * d.t := by rw [e2]
  have hA₁ : ∀ a ∈ d.A₁, v * a * v⁻¹ ∈ d.AW := by
    have hP : d.A₁ ≤ d.AW.comap (MulAut.conj v).toMonoidHom := by
      rw [Data.A₁, Data.pull, A₁sub, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine (map_mono X₂sub_le_closure).trans ?_
        rw [MonoidHom.map_closure, Set.image_pair, closure_le]
        rintro _ (rfl | rfl)
        · change v * d.ι (x₂SU 1) * v⁻¹ ∈ d.AW
          rw [hA, ← hAv, mul_inv_cancel_right]
          exact mem_sup_left hA1
        · change v * d.ι (x₂SU F4.ω) * v⁻¹ ∈ d.AW
          rw [hB, hvB]
          exact mul_mem (mul_mem (mem_sup_left hv2A) (mem_sup_right (inv_mem hNW)))
            (mem_sup_left hBA1)
      · rintro _ ⟨α, hα, rfl⟩
        change v * d.ι α * v⁻¹ ∈ d.AW
        rw [← h.Y_comm_A₂ hvY (d.pull_mono (le_sup_right.trans le_sup_left : X₃sub ≤ A₂sub)
          ⟨α, hα, rfl⟩), mul_inv_cancel_right]
        exact mem_sup_left (d.pull_mono X₃sub_le_A₁sub ⟨α, hα, rfl⟩)
      · rintro _ ⟨α, hα, rfl⟩
        change v * d.ι α * v⁻¹ ∈ d.AW
        rw [← h.Y_comm_A₂ hvY (d.pull_mono (le_sup_right : X₄sub ≤ A₂sub) ⟨α, hα, rfl⟩),
          mul_inv_cancel_right]
        exact mem_sup_left (d.pull_mono X₄sub_le_A₁sub' ⟨α, hα, rfl⟩)
    exact fun a ha => hP ha
  have hvAWT : v ∈ normalizer (d.AWT : Set G) := mem_normalizer_fintype fun y hy => by
    have hle : d.AWT ≤ d.AWT.comap (MulAut.conj v).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        exact mem_sup_left (hA₁ a ha)
      · intro w hw
        change v * w * v⁻¹ ∈ d.AWT
        rw [hvW w hw]
        exact mem_sup_left (mem_sup_right hw)
      · rw [zpowers_le]
        change v * d.t * v⁻¹ ∈ d.AWT
        rw [hvt']
        exact mul_mem (mem_sup_left (mem_sup_left (inv_mem hβA))) (mem_sup_right (mem_zpowers _))
    exact hle hy
  exact ⟨v, Subgroup.mem_inf.2 ⟨hvAWT, mem_normalizer_fintype fun w hw => by
    rw [hvW w hw]
    exact hw⟩, e⟩

omit [Finite G] in
theorem tW_mem_OmW : d.t • (d.W : Set G) ∈ d.OmW :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem ι_comm_t (h : d.Hyp) (α : SU52) : d.ι α * d.t = d.t * d.ι α :=
  h.t_comm_of_mem_L (d.ι_mem α)

theorem ptW_mem_OmW
    (h : d.Hyp)
    (hc : d.CycW) (k : Fin 27) : d.ptW k ∈ d.OmW := by
  obtain ⟨v, hv, hvt⟩ := h.exists_v
  have hk := h.ι_mem_XW_of_mem_CzSub hc (orbSU_mem_CzSub k)
  refine ⟨d.ι (orbSU k) * v⁻¹, mul_mem hk (inv_mem hv), ?_⟩
  have hkt' : (d.ι (orbSU k))⁻¹ * d.t = d.t * (d.ι (orbSU k))⁻¹ :=
    (Commute.inv_left (show Commute (d.ι (orbSU k)) d.t from h.ι_comm_t _)).eq
  rw [Data.ptW]
  congr 1
  calc d.ι (orbSU k * b₀SU * (orbSU k)⁻¹) * d.t =
        d.ι (orbSU k) * d.ι b₀SU * ((d.ι (orbSU k))⁻¹ * d.t) := by
        rw [map_mul, map_mul, map_inv]
        group
    _ = d.ι (orbSU k) * d.ι b₀SU * (d.t * (d.ι (orbSU k))⁻¹) := by rw [hkt']
    _ = d.ι (orbSU k) * (d.ι b₀SU * d.t) * (d.ι (orbSU k))⁻¹ := by group
    _ = d.ι (orbSU k) * (v⁻¹ * d.t * v) * (d.ι (orbSU k))⁻¹ := by rw [hvt]
    _ = d.ι (orbSU k) * v⁻¹ * d.t * (d.ι (orbSU k) * v⁻¹)⁻¹ := by group

theorem mem_OmW_iff
    (h : d.Hyp)
    (hc : d.CycW) {S : Set G} : S ∈ d.OmW ↔ S = d.t • (d.W : Set G) ∨ ∃ k, S = d.ptW k := by
  constructor
  · intro hS
    obtain ⟨a, ha, ha2, rfl⟩ := h.exists_of_mem_OmW hc hS
    rcases h.coset_cases ha ha2 with e | ⟨k, e⟩
    · exact Or.inl e
    · exact Or.inr ⟨k, e⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact tW_mem_OmW
    · exact h.ptW_mem_OmW hc k

@[expose] def _root_.CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Data.omPt (d : Data G) :
    Option (Fin 27) → Set G
  | none => d.t • (d.W : Set G)
  | some k => d.ptW k

theorem card_OmW
    (h : d.Hyp)
    (hc : d.CycW) : Nat.card d.OmW = 28 := by
  have hmem : ∀ o, d.omPt o ∈ d.OmW := fun o => by
    cases o with
    | none => exact tW_mem_OmW
    | some k => exact h.ptW_mem_OmW hc k
  let f : Option (Fin 27) → d.OmW := fun o => ⟨d.omPt o, hmem o⟩
  have hf : Function.Bijective f := by
    refine ⟨fun o o' e => ?_, fun S => ?_⟩
    · have e' : d.omPt o = d.omPt o' := congrArg Subtype.val e
      cases o with
      | none =>
        cases o' with
        | none => rfl
        | some k' => exact absurd e'.symm (h.ptW_ne_tW k')
      | some k =>
        cases o' with
        | none => exact absurd e' (h.ptW_ne_tW k)
        | some k' => exact congrArg some (h.ptW_injective e')
    · rcases (h.mem_OmW_iff hc).1 S.2 with e | ⟨k, e⟩
      · exact ⟨none, Subtype.ext e.symm⟩
      · exact ⟨some k, Subtype.ext e.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_fin]

end Data.Hyp

namespace Data

variable {G : Type} [Group G] (d : Data G)

theorem conj_mem_OmW {x : G} (hx : x ∈ d.XW) {S : Set G} (hS : S ∈ d.OmW) :
    (fun g => x * g * x⁻¹) '' S ∈ d.OmW := by
  obtain ⟨y, hy, rfl⟩ := hS
  refine ⟨x * y, mul_mem hx hy, ?_⟩
  rw [conj_image_smul_coset (Subgroup.mem_inf.1 hx).2]
  congr 1
  group

@[expose] def omegaConjW (x : d.XW) : Equiv.Perm d.OmW where
  toFun S := ⟨(fun g => (x : G) * g * (x : G)⁻¹) '' S, d.conj_mem_OmW x.2 S.2⟩
  invFun S := ⟨(fun g => (x : G)⁻¹ * g * (x : G)⁻¹⁻¹) '' S, d.conj_mem_OmW (inv_mem x.2) S.2⟩
  left_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])
  right_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])

@[expose] def omegaPermW : d.XW →* Equiv.Perm d.OmW where
  toFun := d.omegaConjW
  map_one' := Equiv.ext fun S => Subtype.ext (by simp [omegaConjW])
  map_mul' x y := Equiv.ext fun S => Subtype.ext (by
    simp [omegaConjW, Set.image_image, mul_assoc])

theorem omegaPermW_apply (x : d.XW) (S : d.OmW) :
    ((d.omegaPermW x S : d.OmW) : Set G) = (fun g => (x : G) * g * (x : G)⁻¹) '' S := rfl

end Data

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
