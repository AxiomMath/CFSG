module

public import CFSG.CGT.Foote81L6.TStruct.Lemma2One
public import CFSG.CGT.Foote81L6.TStruct.SDFour
public import CFSG.CGT.Foote81L6.TStruct.DihSub

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem conj_mem_T₁ {g x : G} (hg : g ∈ T) (hx : x ∈ D.T₁) : g * x * g⁻¹ ∈ D.T₁ := by
  have hle : D.T₁.map (MulAut.conj g).toMonoidHom ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg (D.T₁_le_T hy)) (inv_mem hg)
  have heq := D.map_T₁_eq (MulAut.conj g).injective hle
  have : g * x * g⁻¹ ∈ D.T₁.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [heq] at this

theorem T₁_inf_B : D.T₁ ⊓ D.B = D.B₀ ⊔ D.B₁ := by
  apply le_antisymm
  · rintro x ⟨hx1, hxB⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx1
    have hyB : y ∈ D.B := by
      have : y = (y * w) * w⁻¹ := by group
      rw [this]
      exact mul_mem hxB (inv_mem (D.B₀B₁_le_B hw))
    have hy1 : y = 1 := by
      have : y ∈ D.A ⊓ D.B := ⟨hy, hyB⟩
      rwa [D.A_inf_B, mem_bot] at this
    rw [hy1, one_mul]
    exact hw
  · exact le_inf D.B₀B₁_le_T₁ D.B₀B₁_le_B

theorem conj_mem_B₀B₁ {g w : G} (hg : g ∈ T) (hw : w ∈ D.B₀ ⊔ D.B₁) :
    g * w * g⁻¹ ∈ D.B₀ ⊔ D.B₁ := by
  rw [← D.T₁_inf_B]
  refine ⟨D.conj_mem_T₁ hg (D.B₀B₁_le_T₁ hw), ?_⟩
  exact (mem_normalizer_iff.1 (D.T_le_normalizer_B hg) w).1 (D.B₀B₁_le_B hw)

theorem t_mem_normalizer_B₀B₁ : D.t ∈ normalizer ((D.B₀ ⊔ D.B₁ : Subgroup G) : Set G) :=
  mem_normalizer_of_involution D.t_mul_t fun _ hw => D.conj_mem_B₀B₁ D.t_mem_T hw

theorem conj_mem_B₀_of_mem_B₀B₁ {w x : G} (hw : w ∈ D.B₀ ⊔ D.B₁) (hx : x ∈ D.B₀) :
    w * x * w⁻¹ ∈ D.B₀ := by
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have h1 : w₁ * x = x * w₁ := (D.B₀_comm_B₁ x hx w₁ hw₁).symm
  have e : w₀ * w₁ * x * (w₀ * w₁)⁻¹ = w₀ * x * w₀⁻¹ := by
    calc w₀ * w₁ * x * (w₀ * w₁)⁻¹ = w₀ * (w₁ * x) * w₁⁻¹ * w₀⁻¹ := by group
      _ = w₀ * (x * w₁) * w₁⁻¹ * w₀⁻¹ := by rw [h1]
      _ = w₀ * x * w₀⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hw₀ hx) (inv_mem hw₀)

theorem b₀_comm_B₀B₁ {w : G} (hw : w ∈ D.B₀ ⊔ D.B₁) : w * D.b₀ = D.b₀ * w := by
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have h1 := D.b₀_comm w₀ hw₀
  have h2 : w₁ * D.b₀ = D.b₀ * w₁ := (D.B₀_comm_B₁ D.b₀ D.b₀_mem w₁ hw₁).symm
  calc w₀ * w₁ * D.b₀ = w₀ * (D.b₀ * w₁) := by rw [mul_assoc, h2]
    _ = D.b₀ * (w₀ * w₁) := by rw [← mul_assoc, h1, mul_assoc]

theorem b₁_comm_B₀B₁ {w : G} (hw : w ∈ D.B₀ ⊔ D.B₁) : w * D.b₁ = D.b₁ * w := by
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have h1 := D.b₁_comm w₁ hw₁
  have h2 : w₀ * D.b₁ = D.b₁ * w₀ := D.B₀_comm_B₁ w₀ hw₀ D.b₁ D.b₁_mem
  calc w₀ * w₁ * D.b₁ = w₀ * (D.b₁ * w₁) := by rw [mul_assoc, h1]
    _ = D.b₁ * (w₀ * w₁) := by rw [← mul_assoc, h2, mul_assoc]

theorem eq_of_comm_B₀B₁ {z : G} (hz : z ∈ D.B₀ ⊔ D.B₁)
    (hc : ∀ w ∈ D.B₀ ⊔ D.B₁, w * z = z * w) : z = 1 ∨ z = D.b₀ ∨ z = D.b₁ ∨ z = D.b := by
  obtain ⟨z₀, hz₀, z₁, hz₁, rfl⟩ := D.mem_B₀B₁_iff.1 hz
  have h₀ : ∀ y ∈ D.B₀, y * z₀ = z₀ * y := by
    intro y hy
    have h1 := hc y (mem_sup_left hy)
    have h2 : y * z₁ = z₁ * y := D.B₀_comm_B₁ y hy z₁ hz₁
    have : y * z₀ * z₁ = z₀ * y * z₁ := by
      calc y * z₀ * z₁ = y * (z₀ * z₁) := mul_assoc _ _ _
        _ = z₀ * z₁ * y := h1
        _ = z₀ * (z₁ * y) := mul_assoc _ _ _
        _ = z₀ * (y * z₁) := by rw [h2]
        _ = z₀ * y * z₁ := (mul_assoc _ _ _).symm
    exact mul_right_cancel this
  have h₁ : ∀ y ∈ D.B₁, y * z₁ = z₁ * y := by
    intro y hy
    have h1 := hc y (mem_sup_right hy)
    have h2 : z₀ * y = y * z₀ := D.B₀_comm_B₁ z₀ hz₀ y hy
    have : z₀ * (y * z₁) = z₀ * (z₁ * y) := by
      calc z₀ * (y * z₁) = (z₀ * y) * z₁ := (mul_assoc _ _ _).symm
        _ = (y * z₀) * z₁ := by rw [h2]
        _ = y * (z₀ * z₁) := mul_assoc _ _ _
        _ = z₀ * z₁ * y := h1
        _ = z₀ * (z₁ * y) := mul_assoc _ _ _
    exact mul_left_cancel this
  rcases D.eq_one_or_b₀_of_comm hz₀ h₀ with rfl | rfl <;>
    rcases D.eq_one_or_b₁_of_comm hz₁ h₁ with rfl | rfl
  · exact Or.inl (mul_one 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul _)))
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem conj_t_b : D.t * D.b * D.t⁻¹ = D.b := by
  rw [D.b_comm_T D.t_mem_T, mul_inv_cancel_right]

theorem b₀_ne_b₁ : D.b₀ ≠ D.b₁ := by
  intro h
  have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := ⟨D.b₀_mem, h ▸ D.b₁_mem⟩
  rw [D.B₀_inf_B₁, mem_bot] at this
  exact D.b₀_ne_one this

theorem b₀_mul_b : D.b₀ * D.b = D.b₁ := by
  rw [FooteCore.b, ← mul_assoc, D.b₀_mul_b₀, one_mul]

theorem conj_t_b₀ : D.t * D.b₀ * D.t⁻¹ = D.b₁ := by
  have hmem : D.t * D.b₀ * D.t⁻¹ ∈ D.B₀ ⊔ D.B₁ :=
    D.conj_mem_B₀B₁ D.t_mem_T (mem_sup_left D.b₀_mem)
  have hcen : ∀ w ∈ D.B₀ ⊔ D.B₁, w * (D.t * D.b₀ * D.t⁻¹) = (D.t * D.b₀ * D.t⁻¹) * w := by
    intro w hw
    have hw' : D.t⁻¹ * w * D.t ∈ D.B₀ ⊔ D.B₁ := by
      have := D.conj_mem_B₀B₁ (inv_mem D.t_mem_T) hw
      rwa [inv_inv] at this
    have h := D.b₀_comm_B₀B₁ hw'
    calc w * (D.t * D.b₀ * D.t⁻¹) = D.t * ((D.t⁻¹ * w * D.t) * D.b₀) * D.t⁻¹ := by group
      _ = D.t * (D.b₀ * (D.t⁻¹ * w * D.t)) * D.t⁻¹ := by rw [h]
      _ = (D.t * D.b₀ * D.t⁻¹) * w := by group
  rcases D.eq_of_comm_B₀B₁ hmem hcen with h | h | h | h
  · exfalso
    apply D.b₀_ne_one
    have : D.b₀ = D.t⁻¹ * (D.t * D.b₀ * D.t⁻¹) * D.t := by group
    rw [this, h]
    group
  · exfalso
    have htb₀ : D.b₀ * D.t = D.t * D.b₀ := by
      calc D.b₀ * D.t = (D.t * D.b₀ * D.t⁻¹) * D.t := by rw [h]
        _ = D.t * D.b₀ := by group
    have htb₁ : D.b₁ * D.t = D.t * D.b₁ := by
      have hb := D.b_comm_T D.t_mem_T
      rw [← D.b₀_mul_b]
      calc D.b₀ * D.b * D.t = D.b₀ * (D.t * D.b) := by rw [mul_assoc, ← hb]
        _ = D.t * (D.b₀ * D.b) := by rw [← mul_assoc, htb₀, mul_assoc]
    set V := zpowers D.b₀ ⊔ zpowers D.b₁
    have hb₀b₁ : D.b₀ * D.b₁ = D.b₁ * D.b₀ := D.B₀_comm_B₁ _ D.b₀_mem _ D.b₁_mem
    have hVP : V ≤ D.B ⊓ centralizer ({D.t} : Set G) := sup_le
      (zpowers_le.2 ⟨D.b₀_mem_B, mem_centralizer_singleton_iff.2 htb₀⟩)
      (zpowers_le.2 ⟨D.b₁_mem_B, mem_centralizer_singleton_iff.2 htb₁⟩)
    have hV2 : ∀ x ∈ V, x * x = 1 :=
      fun x hx => mul_self_of_mem_zpowers_sup_zpowers D.b₀_mul_b₀ D.b₁_mul_b₁ hb₀b₁ hx
    have hV4 : Nat.card V = 4 :=
      card_zpowers_sup_zpowers D.b₀_mul_b₀ D.b₁_mul_b₁ D.b₀_ne_one D.b₁_ne_one D.b₀_ne_b₁ hb₀b₁
    have hVcen : ∀ v ∈ V, v ∈ D.B₀ ⊔ D.B₁ ∧ ∀ w ∈ D.B₀ ⊔ D.B₁, w * v = v * w := by
      intro v hv
      refine ⟨(sup_le (zpowers_le.2 (mem_sup_left D.b₀_mem))
        (zpowers_le.2 (mem_sup_right D.b₁_mem))) hv, fun w hw => ?_⟩
      exact comm_of_mem_sup (fun x hx => by
          rcases eq_one_or_eq_of_mem_zpowers D.b₀_mul_b₀ hx with rfl | rfl
          · rw [mul_one, one_mul]
          · exact (D.b₀_comm_B₀B₁ hw).symm)
        (fun x hx => by
          rcases eq_one_or_eq_of_mem_zpowers D.b₁_mul_b₁ hx with rfl | rfl
          · rw [mul_one, one_mul]
          · exact (D.b₁_comm_B₀B₁ hw).symm) hv |>.symm
    have hBV : ∀ g ∈ D.B, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
      intro g hg v hv
      obtain ⟨hvB, hvc⟩ := hVcen v hv
      have hmem' := D.conj_mem_B₀B₁ (D.B_le_T hg) hvB
      have hcen' : ∀ w ∈ D.B₀ ⊔ D.B₁, w * (g * v * g⁻¹) = (g * v * g⁻¹) * w := by
        intro w hw
        have hw' : g⁻¹ * w * g ∈ D.B₀ ⊔ D.B₁ := by
          have := D.conj_mem_B₀B₁ (inv_mem (D.B_le_T hg)) hw
          rwa [inv_inv] at this
        have h := hvc _ hw'
        calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
          _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
          _ = (g * v * g⁻¹) * w := by group
      rcases D.eq_of_comm_B₀B₁ hmem' hcen' with h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers _)
      · exact mem_sup_right (mem_zpowers _)
      · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
    have hPN : D.B ⊓ centralizer ({D.t} : Set G) ≤
        D.B ⊓ centralizer ({D.t} : Set G) ⊓ normalizer (V : Set G) := by
      intro g hg
      refine ⟨hg, mem_normalizer_iff.2 fun v => ⟨fun hv => hBV g hg.1 v hv, fun hv => ?_⟩⟩
      have := hBV g⁻¹ (inv_mem hg.1) _ hv
      rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this
    obtain ⟨e⟩ := D.CBt_iso
    have h8 := card_inf_normalizer_le_of_semidihedral (by have := D.three_le_n; omega) e hVP hV2
      hV4
    haveI hPf : Finite ↥(D.B ⊓ centralizer ({D.t} : Set G)) :=
      Nat.finite_of_card_ne_zero (by rw [D.card_CBt]; positivity)
    haveI : Finite ↥(D.B ⊓ centralizer ({D.t} : Set G) ⊓ normalizer (V : Set G)) :=
      Finite.of_injective _ (inclusion_injective (inf_le_left :
        D.B ⊓ centralizer ({D.t} : Set G) ⊓ normalizer (V : Set G) ≤
          D.B ⊓ centralizer ({D.t} : Set G)))
    have hle := card_le_of_le hPN
    rw [D.card_CBt] at hle
    have : 2 ^ 4 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := D.three_le_n; omega)
    omega
  · exact h
  · exfalso
    apply D.b₁_ne_one
    have h1 : D.t * D.b₁ * D.t⁻¹ = 1 := by
      rw [← D.b₀_mul_b]
      calc D.t * (D.b₀ * D.b) * D.t⁻¹ = (D.t * D.b₀ * D.t⁻¹) * (D.t * D.b * D.t⁻¹) := by group
        _ = 1 := by rw [h, D.conj_t_b, D.b_mul_b]
    have : D.b₁ = D.t⁻¹ * (D.t * D.b₁ * D.t⁻¹) * D.t := by group
    rw [this, h1]
    group

theorem conj_t_b₁ : D.t * D.b₁ * D.t⁻¹ = D.b₀ := by
  rw [← D.conj_t_b₀, D.t_inv]
  calc D.t * (D.t * D.b₀ * D.t) * D.t = (D.t * D.t) * D.b₀ * (D.t * D.t) := by group
    _ = D.b₀ := by rw [D.t_mul_t, one_mul, mul_one]

@[expose] def B₀t : Subgroup G := D.B₀.map (MulAut.conj D.t).toMonoidHom

theorem mem_B₀t_iff {x : G} : x ∈ D.B₀t ↔ D.t * x * D.t⁻¹ ∈ D.B₀ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [D.t_inv]
    have : D.t * (D.t * y * D.t) * D.t = (D.t * D.t) * y * (D.t * D.t) := by group
    rw [this, D.t_mul_t, one_mul, mul_one]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [D.t_inv]
    have : D.t * (D.t * x * D.t) * D.t = (D.t * D.t) * x * (D.t * D.t) := by group
    rw [this, D.t_mul_t, one_mul, mul_one]

theorem conj_t_mem_B₀t {y : G} (hy : y ∈ D.B₀) : D.t * y * D.t⁻¹ ∈ D.B₀t := ⟨y, hy, rfl⟩

theorem B₀t_le_B₀B₁ : D.B₀t ≤ D.B₀ ⊔ D.B₁ := by
  rintro _ ⟨y, hy, rfl⟩
  exact D.conj_mem_B₀B₁ D.t_mem_T (mem_sup_left hy)

theorem b₀_mem_of_normal {X : Subgroup G} (hX : X ≤ D.B₀)
    (hn : ∀ h ∈ D.B₀, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hne : X ≠ ⊥) : D.b₀ ∈ X := by
  obtain ⟨e⟩ := D.B₀_iso
  have hn2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  haveI := lowerSub_normal e hn
  obtain ⟨x, hxX, hx1⟩ := (Subgroup.bot_or_exists_ne_one X).resolve_left hne
  have hxl : e ⟨x, hX hxX⟩ ∈ lowerSub e X := by
    rw [mem_lowerSub, MulEquiv.symm_apply_apply]
    exact hxX
  have hne1 : e ⟨x, hX hxX⟩ ≠ 1 := by
    intro h
    apply hx1
    have := e.injective (h.trans e.map_one.symm)
    exact congrArg Subtype.val this
  have hzc := zc_mem_of_normal hn2 (lowerSub e X) hxl hne1
  rw [mem_lowerSub] at hzc
  rwa [symm_zc_eq e hn2 D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy] at hzc

theorem B₀_inf_B₀t : D.B₀ ⊓ D.B₀t = ⊥ := by
  by_contra hne
  have hle : D.B₀ ⊓ D.B₀t ≤ D.B₀ := inf_le_left
  have hn : ∀ h ∈ D.B₀, ∀ x ∈ D.B₀ ⊓ D.B₀t, h * x * h⁻¹ ∈ D.B₀ ⊓ D.B₀t := by
    intro h hh x hx
    refine mem_inf.2 ⟨mul_mem (mul_mem hh hx.1) (inv_mem hh), ?_⟩
    rw [mem_B₀t_iff]
    have hx' := (D.mem_B₀t_iff).1 hx.2
    have hth : D.t * h * D.t⁻¹ ∈ D.B₀ ⊔ D.B₁ := D.conj_mem_B₀B₁ D.t_mem_T (mem_sup_left hh)
    have e : D.t * (h * x * h⁻¹) * D.t⁻¹ =
        (D.t * h * D.t⁻¹) * (D.t * x * D.t⁻¹) * (D.t * h * D.t⁻¹)⁻¹ := by group
    rw [e]
    exact D.conj_mem_B₀_of_mem_B₀B₁ hth hx'
  have hb := D.b₀_mem_of_normal hle hn hne
  have h1 := (D.mem_B₀t_iff).1 hb.2
  rw [D.conj_t_b₀] at h1
  exact D.b₀_ne_b₁ (by
    have : D.b₁ ∈ D.B₀ ⊓ D.B₁ := ⟨h1, D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact absurd this D.b₁_ne_one)

theorem B₀_comm_B₀t {x y : G} (hx : x ∈ D.B₀) (hy : y ∈ D.B₀t) : x * y = y * x := by
  have hyB : y ∈ D.B₀ ⊔ D.B₁ := D.B₀t_le_B₀B₁ hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ D.B₀ := by
    have := D.conj_mem_B₀_of_mem_B₀B₁ hyB (inv_mem hx)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem hx this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ D.B₀t := by
    rw [mem_B₀t_iff]
    have hy' := (D.mem_B₀t_iff).1 hy
    have hxt : D.t * x * D.t⁻¹ ∈ D.B₀ ⊔ D.B₁ := D.conj_mem_B₀B₁ D.t_mem_T (mem_sup_left hx)
    have e : D.t * (x * y * x⁻¹ * y⁻¹) * D.t⁻¹ =
        ((D.t * x * D.t⁻¹) * (D.t * y * D.t⁻¹) * (D.t * x * D.t⁻¹)⁻¹) *
          (D.t * y * D.t⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (D.conj_mem_B₀_of_mem_B₀B₁ hxt hy') (inv_mem hy')
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ D.B₀ ⊓ D.B₀t := ⟨h1, h2⟩
  rw [D.B₀_inf_B₀t, mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem B₀_comm_conj_t : ∀ x ∈ D.B₀, ∀ y ∈ D.B₀, x * (D.t * y * D.t⁻¹) = (D.t * y * D.t⁻¹) * x :=
  fun _ hx _ hy => D.B₀_comm_B₀t hx (D.conj_t_mem_B₀t hy)

theorem card_B₀t : Nat.card D.B₀t = 2 ^ n := by
  rw [B₀t, card_map_of_injective (MulAut.conj D.t).injective, D.card_B₀]

theorem B₀_sup_B₀t : D.B₀ ⊔ D.B₀t = D.B₀ ⊔ D.B₁ := by
  have hle : D.B₀ ⊔ D.B₀t ≤ D.B₀ ⊔ D.B₁ := sup_le le_sup_left D.B₀t_le_B₀B₁
  haveI : Finite ↥(D.B₀ ⊔ D.B₁) := Nat.finite_of_card_ne_zero (by rw [D.card_B₀B₁]; positivity)
  refine eq_of_le_of_card_ge hle ?_
  rw [D.card_B₀B₁, card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy =>
    D.B₀_comm_B₀t hx hy) D.B₀_inf_B₀t, D.card_B₀, D.card_B₀t, ← pow_add, two_mul]

theorem exists_At_conj_A {x : G} (hx : x ∈ T) :
    ∃ α ∈ D.A ⊔ zpowers D.t, (∀ u ∈ D.A, x * u * x⁻¹ = α * u * α⁻¹) ∧ (α ∈ D.A ↔ x ∈ D.T₀) := by
  by_cases h0 : x ∈ D.T₀
  · obtain ⟨y, hy, w, hw, rfl⟩ := D.mem_T₀_iff.1 h0
    refine ⟨y, mem_sup_left hy, fun u hu => ?_, iff_of_true hy h0⟩
    have hwu : w * u = u * w := (D.A_comm_B u hu w hw).symm
    calc y * w * u * (y * w)⁻¹ = y * (w * u) * w⁻¹ * y⁻¹ := by group
      _ = y * (u * w) * w⁻¹ * y⁻¹ := by rw [hwu]
      _ = y * u * y⁻¹ := by group
  · have hxt : x * D.t ∈ D.T₀ := (D.mem_T_iff.1 hx).resolve_left h0
    obtain ⟨y, hy, w, hw, hyw⟩ := D.mem_T₀_iff.1 hxt
    have hx' : x = y * w * D.t := by
      calc x = x * D.t * D.t := by rw [mul_assoc, D.t_mul_t, mul_one]
        _ = y * w * D.t := by rw [hyw]
    refine ⟨y * D.t, mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers _)),
      fun u hu => ?_, iff_of_false (fun h => D.t_not_mem_A ?_) h0⟩
    · have htu : D.t * u * D.t⁻¹ ∈ D.A := D.conj_t_A u hu
      have hwu : w * (D.t * u * D.t⁻¹) = (D.t * u * D.t⁻¹) * w :=
        (D.A_comm_B _ htu w hw).symm
      rw [hx']
      calc y * w * D.t * u * (y * w * D.t)⁻¹ = y * (w * (D.t * u * D.t⁻¹)) * w⁻¹ * y⁻¹ := by
            group
        _ = y * ((D.t * u * D.t⁻¹) * w) * w⁻¹ * y⁻¹ := by rw [hwu]
        _ = y * D.t * u * (y * D.t)⁻¹ := by group
    · have : D.t = y⁻¹ * (y * D.t) := by group
      rw [this]
      exact mul_mem (inv_mem hy) h

theorem conj_t_mem_T₁ {x : G} (hx : x ∈ D.T₀) : D.t * x * D.t⁻¹ * x⁻¹ ∈ D.T₁ := by
  rcases D.mem_T₁_or_mul_s_mem_T₁ hx with h | h
  · exact mul_mem (D.conj_mem_T₁ D.t_mem_T h) (inv_mem h)
  ·
    have hts : D.t * D.s * D.t⁻¹ * D.s⁻¹ ∈ D.T₁ := by
      have h1 : D.t * D.s * D.t⁻¹ ∈ D.T₀ :=
        (mem_normalizer_iff.1 (D.T_le_normalizer_T₀ D.t_mem_T) D.s).1 (D.B_le_T₀ D.s_mem_B)
      rcases D.mem_T₁_or_mul_s_mem_T₁ h1 with h2 | h2
      · exfalso
        apply D.s_not_mem_T₁
        have := D.conj_mem_T₁ (inv_mem D.t_mem_T) h2
        rwa [show D.t⁻¹ * (D.t * D.s * D.t⁻¹) * D.t⁻¹⁻¹ = D.s by group] at this
      · rwa [D.s_inv]
    set y := x * D.s
    have hxy : x = y * D.s := by rw [show y = x * D.s from rfl, mul_assoc, D.s_mul_s, mul_one]
    rw [hxy]
    have e : D.t * (y * D.s) * D.t⁻¹ * (y * D.s)⁻¹ =
        (D.t * y * D.t⁻¹) * (D.t * D.s * D.t⁻¹ * D.s⁻¹) * y⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (D.conj_mem_T₁ D.t_mem_T h) hts) (inv_mem h)

theorem no_involution_T₁st {y : G} (hy : y ∈ D.T₁) :
    y * D.s * D.t * (y * D.s * D.t) ≠ 1 := by
  intro h2
  have hyT : y * D.s * D.t ∈ T :=
    mul_mem (mul_mem (D.T₁_le_T hy) (D.B_le_T D.s_mem_B)) D.t_mem_T
  have hy0 : y * D.s * D.t ∉ D.T₀ := by
    intro h
    apply D.t_not_mem_T₀
    have : D.t = (y * D.s)⁻¹ * (y * D.s * D.t) := by group
    rw [this]
    exact mul_mem (inv_mem (mul_mem (D.T₁_le_T₀ hy) (D.B_le_T₀ D.s_mem_B))) h
  obtain ⟨h, hh, hht⟩ := D.exists_conj_t hyT hy0 h2
  have h1 : y * D.s ∈ D.T₁ := by
    have hc := D.conj_t_mem_T₁ (inv_mem hh)
    have e : y * D.s = h * (D.t * h⁻¹ * D.t⁻¹ * h⁻¹⁻¹) * h⁻¹ := by
      calc y * D.s = (y * D.s * D.t) * D.t⁻¹ := by group
        _ = h * D.t * h⁻¹ * D.t⁻¹ := by rw [← hht]
        _ = h * (D.t * h⁻¹ * D.t⁻¹ * h⁻¹⁻¹) * h⁻¹ := by group
    rw [e]
    exact D.conj_mem_T₁ (D.T₀_le_T hh) hc
  apply D.s_not_mem_T₁
  have : D.s = y⁻¹ * (y * D.s) := by group
  rw [this]
  exact mul_mem (inv_mem hy) h1

end FooteCore

end CFSG.CGT.Foote81L6
