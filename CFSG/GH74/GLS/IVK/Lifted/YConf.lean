module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Pair
public import CFSG.GH74.GLS.IVK.Lifted.CentralProd

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section Swap

variable {H : Type} [Group H]

@[expose] def swapSub (A : Subgroup H) (τ : H) : Subgroup H := A.comap (MulAut.conj τ).toMonoidHom

theorem mem_swapSub {A : Subgroup H} {τ x : H} : x ∈ swapSub A τ ↔ τ * x * τ⁻¹ ∈ A := Iff.rfl

theorem mul_mem_swapSub_of_mem {A : Subgroup H} {τ x : H} (hτ : τ * τ = 1) (hx : x ∈ A) :
    τ * x * τ⁻¹ ∈ swapSub A τ := by
  rw [mem_swapSub]
  have : τ * (τ * x * τ⁻¹) * τ⁻¹ = x := by
    calc τ * (τ * x * τ⁻¹) * τ⁻¹ = (τ * τ) * x * (τ * τ)⁻¹ := by group
      _ = x := by rw [hτ]; group
  rw [this]
  exact hx

@[expose] def swapEquiv {τ : H} (hτ : τ * τ = 1) (A : Subgroup H) : ↥(swapSub A τ) ≃* ↥A where
  toFun x := ⟨τ * x * τ⁻¹, x.2⟩
  invFun y := ⟨τ * y * τ⁻¹, by
    rw [mem_swapSub]
    have : τ * (τ * (y : H) * τ⁻¹) * τ⁻¹ = y := by
      calc τ * (τ * (y : H) * τ⁻¹) * τ⁻¹ = (τ * τ) * (y : H) * (τ * τ)⁻¹ := by group
        _ = y := by rw [hτ]; group
    rw [this]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    show τ * (τ * (x : H) * τ⁻¹) * τ⁻¹ = x
    calc τ * (τ * (x : H) * τ⁻¹) * τ⁻¹ = (τ * τ) * (x : H) * (τ * τ)⁻¹ := by group
      _ = x := by rw [hτ]; group
  right_inv y := by
    apply Subtype.ext
    show τ * (τ * (y : H) * τ⁻¹) * τ⁻¹ = y
    calc τ * (τ * (y : H) * τ⁻¹) * τ⁻¹ = (τ * τ) * (y : H) * (τ * τ)⁻¹ := by group
      _ = y := by rw [hτ]; group
  map_mul' x y := by
    apply Subtype.ext
    show τ * ((x : H) * y) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * y * τ⁻¹)
    group

theorem mem_sup_of_commute {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : H}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup H :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        have h := hc a₂ ha₂ b₁ hb₁
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [h]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h := hc a⁻¹ (A.inv_mem ha) b hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have : a⁻¹ * b = b * a⁻¹ := h
            calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
              _ = a⁻¹ * b⁻¹ := by
                have h2 : (a * b) = (b * a) := hc a ha b hb
                calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h2]
                  _ = a⁻¹ * b⁻¹ := by group }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

end Swap

section SL2Facts

theorem sl2_noncomm (F : Type) [Field F] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  let a : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp⟩
  refine ⟨a, b, fun h => ?_⟩
  have h' : ((a * b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((b * a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [h]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h'
  simp [a, b, Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem sl2_center_unique {F : Type} [Field F] {x y : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx : x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F))
    (hy : y ∈ center (Matrix.SpecialLinearGroup (Fin 2) F))
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hx hy
  obtain ⟨r, hr, hrx⟩ := hx
  obtain ⟨s, hs, hsy⟩ := hy
  have hr' : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by
      have h2 : r ^ 2 = 1 := by simpa using hr
      linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hs' : s = 1 ∨ s = -1 := by
    have : (s - 1) * (s + 1) = 0 := by
      have h2 : s ^ 2 = 1 := by simpa using hs
      linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hxe : (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r := hrx.symm
  have hye : (y : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) s := hsy.symm
  rcases hr' with rfl | rfl
  · exact absurd (Subtype.ext (by rw [hxe]; simp)) hx1
  rcases hs' with rfl | rfl
  · exact absurd (Subtype.ext (by rw [hye]; simp)) hy1
  exact Subtype.ext (by rw [hxe, hye])

end SL2Facts

structure YConf (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (H : Type) [Group H] where
  A₁ : Subgroup H
  P₁ : Subgroup H
  τ : H
  ω : H
  ζ : H
  e : ↥A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F
  α : MulAut ↥A₁
  hτ : τ * τ = 1
  hω : ω * ω = 1
  hτω : τ * ω = ω * τ
  hα : ∀ a : ↥A₁, ((α a : ↥A₁) : H) = ω * (a : H) * ω⁻¹
  hcomm : ∀ a ∈ A₁, ∀ b ∈ swapSub A₁ τ, a * b = b * a
  hζ₁ : ζ ∈ A₁
  hζ₂ : ζ ∈ swapSub A₁ τ
  hζc : ∀ a ∈ A₁, a * ζ = ζ * a
  hζ1 : ζ ≠ 1
  hP₁ : IsSylowOf 2 P₁ A₁
  hωP : ∀ x ∈ P₁, ω * x * ω⁻¹ ∈ P₁
  hBY : (A₁ ⊔ swapSub A₁ τ) ⊓ (zpowers τ ⊔ zpowers ω) = ⊥
  hout : ω ≠ 1 → α ∉ innOf ↥A₁ ∧ (gammaOf hodd h3 (MulAut.congr e α)).right = 1

namespace YConf

variable {F : Type} [Field F] [Finite F] {hodd : Odd (Nat.card F)} {h3 : 3 < Nat.card F}
  {H : Type} [Group H] (c : YConf F hodd h3 H)

@[expose] def A₂ : Subgroup H := swapSub c.A₁ c.τ

@[expose] def B : Subgroup H := c.A₁ ⊔ c.A₂

@[expose] def P₂ : Subgroup H := swapSub c.P₁ c.τ

@[expose] def P : Subgroup H := c.P₁ ⊔ c.P₂

@[expose] def X : Subgroup H := c.B ⊔ zpowers c.τ ⊔ zpowers c.ω

theorem mem_A₂ {x : H} : x ∈ c.A₂ ↔ c.τ * x * c.τ⁻¹ ∈ c.A₁ := Iff.rfl

theorem P₁_le : c.P₁ ≤ c.A₁ := c.hP₁.le

theorem P₂_le : c.P₂ ≤ c.A₂ := fun _ hx => c.P₁_le hx

theorem A₁_le_B : c.A₁ ≤ c.B := le_sup_left

theorem A₂_le_B : c.A₂ ≤ c.B := le_sup_right

theorem P_le_B : c.P ≤ c.B :=
  sup_le (c.P₁_le.trans c.A₁_le_B) (c.P₂_le.trans c.A₂_le_B)

theorem noncomm : ∃ a b : ↥c.A₁, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := sl2_noncomm F
  refine ⟨c.e.symm a, c.e.symm b, fun h => hab ?_⟩
  have := congrArg c.e h
  simpa using this

theorem cen_unique {x y : ↥c.A₁} (hx : x ∈ center ↥c.A₁) (hy : y ∈ center ↥c.A₁) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  have hcen : ∀ z : ↥c.A₁, z ∈ center ↥c.A₁ → c.e z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := hz (c.e.symm g)
    have h2 := congrArg c.e this
    simpa using h2
  have := sl2_center_unique (hcen x hx) (hcen y hy) (fun h => hx1 (c.e.injective (by rw [h, map_one])))
    (fun h => hy1 (c.e.injective (by rw [h, map_one])))
  exact c.e.injective this

theorem mem_A₂_iff (x : ↥c.A₁) : (x : H) ∈ c.A₂ ↔ x ∈ center ↥c.A₁ := by
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (c.hcomm g g.2 x hx)
  · intro hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact c.A₂.one_mem
    · have hζc : (⟨c.ζ, c.hζ₁⟩ : ↥c.A₁) ∈ center ↥c.A₁ := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (c.hζc g g.2)
      have hζ1' : (⟨c.ζ, c.hζ₁⟩ : ↥c.A₁) ≠ 1 := fun h => c.hζ1 (congrArg Subtype.val h)
      have := c.cen_unique hx hζc hx1 hζ1'
      rw [this]
      exact c.hζ₂

theorem τ_fix {x : H} (hx₁ : x ∈ c.A₁) (hx₂ : x ∈ c.A₂) : c.τ * x * c.τ⁻¹ = x := by
  have hy₁ : c.τ * x * c.τ⁻¹ ∈ c.A₁ := hx₂
  have hy₂ : c.τ * x * c.τ⁻¹ ∈ c.A₂ := mul_mem_swapSub_of_mem c.hτ hx₁
  by_cases hx1 : x = 1
  · rw [hx1]
    group
  · have hxc : (⟨x, hx₁⟩ : ↥c.A₁) ∈ center ↥c.A₁ := (c.mem_A₂_iff _).1 hx₂
    have hyc : (⟨c.τ * x * c.τ⁻¹, hy₁⟩ : ↥c.A₁) ∈ center ↥c.A₁ := (c.mem_A₂_iff _).1 hy₂
    have hx1' : (⟨x, hx₁⟩ : ↥c.A₁) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hy1' : (⟨c.τ * x * c.τ⁻¹, hy₁⟩ : ↥c.A₁) ≠ 1 := fun h => hx1 (by
      have h1 : c.τ * x * c.τ⁻¹ = 1 := congrArg Subtype.val h
      have : x = c.τ⁻¹ * (c.τ * x * c.τ⁻¹) * c.τ := by group
      rw [this, h1]
      group)
    exact congrArg Subtype.val (c.cen_unique hyc hxc hy1' hx1')

theorem τ_ne : c.τ ≠ 1 := by
  intro h1
  obtain ⟨a, b, hab⟩ := c.noncomm
  apply hab
  apply Subtype.ext
  have hb : (b : H) ∈ c.A₂ := by
    rw [mem_A₂, h1]
    simp
  exact c.hcomm a a.2 b hb

theorem hBY' : c.B ⊓ (zpowers c.τ ⊔ zpowers c.ω) = ⊥ := c.hBY

theorem τ_notin_B : c.τ ∉ c.B := fun h => c.τ_ne (by
  have : c.τ ∈ c.B ⊓ (zpowers c.τ ⊔ zpowers c.ω) := ⟨h, mem_sup_left (mem_zpowers _)⟩
  rw [c.hBY'] at this
  exact Subgroup.mem_bot.1 this)

theorem τ_norm_B {n : H} (hn : n ∈ c.B) : c.τ * n * c.τ⁻¹ ∈ c.B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute c.hcomm hn
  have e : c.τ * (a * b) * c.τ⁻¹ = (c.τ * a * c.τ⁻¹) * (c.τ * b * c.τ⁻¹) := by group
  rw [e]
  exact mul_mem (c.A₂_le_B (mul_mem_swapSub_of_mem c.hτ ha)) (c.A₁_le_B hb)

theorem ω_norm_A₁ {a : H} (ha : a ∈ c.A₁) : c.ω * a * c.ω⁻¹ ∈ c.A₁ := by
  have := (c.α ⟨a, ha⟩).2
  rwa [c.hα] at this

theorem ω_norm_A₂ {b : H} (hb : b ∈ c.A₂) : c.ω * b * c.ω⁻¹ ∈ c.A₂ := by
  rw [mem_A₂]
  have h1 : c.τ * (c.ω * b * c.ω⁻¹) * c.τ⁻¹ = c.ω * (c.τ * b * c.τ⁻¹) * c.ω⁻¹ := by
    have hc : c.τ * c.ω = c.ω * c.τ := c.hτω
    calc c.τ * (c.ω * b * c.ω⁻¹) * c.τ⁻¹ = (c.τ * c.ω) * b * (c.τ * c.ω)⁻¹ := by group
      _ = (c.ω * c.τ) * b * (c.ω * c.τ)⁻¹ := by rw [hc]
      _ = c.ω * (c.τ * b * c.τ⁻¹) * c.ω⁻¹ := by group
  rw [h1]
  exact c.ω_norm_A₁ hb

theorem ω_norm_B {n : H} (hn : n ∈ c.B) : c.ω * n * c.ω⁻¹ ∈ c.B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute c.hcomm hn
  have e : c.ω * (a * b) * c.ω⁻¹ = (c.ω * a * c.ω⁻¹) * (c.ω * b * c.ω⁻¹) := by group
  rw [e]
  exact mul_mem (c.A₁_le_B (c.ω_norm_A₁ ha)) (c.A₂_le_B (c.ω_norm_A₂ hb))

theorem ω_notin (hω1 : c.ω ≠ 1) : c.ω ∉ c.B ⊔ zpowers c.τ := by
  intro h
  have hY : ∀ y, y ∈ c.B → y ∈ zpowers c.τ ⊔ zpowers c.ω → y = 1 := fun y hy hy' => by
    have h2 : y ∈ c.B ⊓ (zpowers c.τ ⊔ zpowers c.ω) := ⟨hy, hy'⟩
    rw [c.hBY'] at h2
    exact Subgroup.mem_bot.1 h2
  rcases mem_sup_zpowers_cases c.hτ (fun n hn => c.τ_norm_B hn) h with h0 | ⟨n, hn, hωn⟩
  · exact hω1 (hY _ h0 (mem_sup_right (mem_zpowers _)))
  · have hnτ : n = c.ω * c.τ := by
      calc n = n * (c.τ * c.τ) := by rw [c.hτ, mul_one]
        _ = (n * c.τ) * c.τ := by group
        _ = c.ω * c.τ := by rw [← hωn]
    have h1 : c.ω * c.τ = 1 := hY _ (hnτ ▸ hn)
      (mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _)))
    have hωτ : c.ω = c.τ := by
      calc c.ω = c.ω * (c.τ * c.τ) := by rw [c.hτ, mul_one]
        _ = (c.ω * c.τ) * c.τ := by group
        _ = c.τ := by rw [h1, one_mul]
    obtain ⟨a, b, hab⟩ := c.noncomm
    apply hab
    have hz : ∀ x : ↥c.A₁, x ∈ center ↥c.A₁ := by
      intro x
      rw [← c.mem_A₂_iff]
      have h1' : c.τ * (x : H) * c.τ⁻¹ ∈ c.A₁ := by
        rw [← hωτ]
        exact c.ω_norm_A₁ x.2
      have h2' : c.τ * (x : H) * c.τ⁻¹ ∈ c.A₂ := mul_mem_swapSub_of_mem c.hτ x.2
      have h3'' := c.τ_fix h1' h2'
      have hx_eq : (x : H) = c.τ * (x : H) * c.τ⁻¹ := by
        calc (x : H) = c.τ * (c.τ * (x : H) * c.τ⁻¹) * c.τ⁻¹ := by
              calc (x : H) = (c.τ * c.τ) * (x : H) * (c.τ * c.τ)⁻¹ := by rw [c.hτ]; group
                _ = c.τ * (c.τ * (x : H) * c.τ⁻¹) * c.τ⁻¹ := by group
          _ = c.τ * (x : H) * c.τ⁻¹ := h3''
      rw [hx_eq]
      exact h2'
    exact (Subgroup.mem_center_iff.1 (hz b) a)

theorem B_le_X : c.B ≤ c.X := le_sup_left.trans le_sup_left

theorem τ_mem_X : c.τ ∈ c.X := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem ω_mem_X : c.ω ∈ c.X := mem_sup_right (mem_zpowers _)

theorem ω_comm_τ : c.ω * c.τ * c.ω⁻¹ = c.τ := by
  rw [← c.hτω]
  group

theorem ω_norm_N {n : H} (hn : n ∈ c.B ⊔ zpowers c.τ) : c.ω * n * c.ω⁻¹ ∈ c.B ⊔ zpowers c.τ := by
  rcases mem_sup_zpowers_cases c.hτ (fun n hn => c.τ_norm_B hn) hn with h | ⟨b, hb, rfl⟩
  · exact mem_sup_left (c.ω_norm_B h)
  · have e : c.ω * (b * c.τ) * c.ω⁻¹ = (c.ω * b * c.ω⁻¹) * (c.ω * c.τ * c.ω⁻¹) := by group
    rw [e, c.ω_comm_τ]
    exact mul_mem (mem_sup_left (c.ω_norm_B hb)) (mem_sup_right (mem_zpowers _))

theorem α_sq : c.α * c.α = 1 := by
  ext a
  show ((c.α (c.α a) : ↥c.A₁) : H) = a
  rw [c.hα, c.hα]
  calc c.ω * (c.ω * (a : H) * c.ω⁻¹) * c.ω⁻¹ = (c.ω * c.ω) * (a : H) * (c.ω * c.ω)⁻¹ := by
        group
    _ = a := by rw [c.hω]; group

end YConf

theorem mulEquiv_mem_center {G G' : Type} [Group G] [Group G'] (η : G ≃* G') {x : G} :
    η x ∈ Subgroup.center G' ↔ x ∈ Subgroup.center G := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := h (η g)
    apply η.injective
    simpa using this
  · intro h g'
    obtain ⟨g, rfl⟩ := η.surjective g'
    rw [← map_mul, ← map_mul, h g]

section IsoB

variable {F : Type} [Field F] [Finite F] {hodd : Odd (Nat.card F)} {h3 : 3 < Nat.card F}
  {H H' : Type} [Group H] [Group H']

theorem yconf_iso_B (c : YConf F hodd h3 H) (c' : YConf F hodd h3 H') (hωω : c.ω = 1 ↔ c'.ω = 1) :
    ∃ θ : ↥c.B ≃* ↥c'.B,
      (∀ (n : ↥c.B) (h : c.τ * (n : H) * c.τ⁻¹ ∈ c.B),
        ((θ ⟨c.τ * (n : H) * c.τ⁻¹, h⟩ : ↥c'.B) : H') = c'.τ * ((θ n : ↥c'.B) : H') * c'.τ⁻¹) ∧
      (c.ω ≠ 1 → ∀ (n : ↥c.B) (h : c.ω * (n : H) * c.ω⁻¹ ∈ c.B),
        ((θ ⟨c.ω * (n : H) * c.ω⁻¹, h⟩ : ↥c'.B) : H') = c'.ω * ((θ n : ↥c'.B) : H') * c'.ω⁻¹) ∧
      (∀ x : ↥c.B, (x : H) ∈ c.P ↔ ((θ x : ↥c'.B) : H') ∈ c'.P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥c.A₁ := Finite.of_equiv _ c.e.symm.toEquiv
  have : Finite ↥c'.A₁ := Finite.of_equiv _ c'.e.symm.toEquiv
  obtain ⟨Q, hQ⟩ := c.hP₁.exists_sylow_eq_subgroupOf
  obtain ⟨Q', hQ'⟩ := c'.hP₁.exists_sylow_eq_subgroupOf
  have hQmem : ∀ x : ↥c.A₁, x ∈ (Q : Subgroup ↥c.A₁) ↔ (x : H) ∈ c.P₁ := fun x => by
    rw [hQ]
    exact Iff.rfl
  have hQ'mem : ∀ x : ↥c'.A₁, x ∈ (Q' : Subgroup ↥c'.A₁) ↔ (x : H') ∈ c'.P₁ := fun x => by
    rw [hQ']
    exact Iff.rfl
  obtain ⟨η, hηα, hηQ⟩ : ∃ η : ↥c.A₁ ≃* ↥c'.A₁,
      (c.ω ≠ 1 → ∀ x, η (c.α x) = c'.α (η x)) ∧
      ∀ x, x ∈ (Q : Subgroup ↥c.A₁) ↔ η x ∈ (Q' : Subgroup ↥c'.A₁) := by
    by_cases hω1 : c.ω = 1
    · obtain ⟨η, h⟩ := sl_sylow_iso c.e c'.e Q Q'
      exact ⟨η, fun h' => absurd hω1 h', h⟩
    · have hω1' : c'.ω ≠ 1 := fun h => hω1 (hωω.2 h)
      obtain ⟨hin, hf⟩ := c.hout hω1
      obtain ⟨hin', hf'⟩ := c'.hout hω1'
      obtain ⟨η, h1, h2⟩ := sl_pair_iso hodd h3 c.e c'.e c.α_sq c'.α_sq hin hin' hf hf' Q Q'
        (fun x hx => by
          rw [hQmem] at hx ⊢
          rw [c.hα]
          exact c.hωP _ hx)
        (fun x hx => by
          rw [hQ'mem] at hx ⊢
          rw [c'.hα]
          exact c'.hωP _ hx)
      exact ⟨η, fun _ => h1, h2⟩
  have hηP : ∀ x : ↥c.A₁, (x : H) ∈ c.P₁ ↔ ((η x : ↥c'.A₁) : H') ∈ c'.P₁ := fun x => by
    rw [← hQmem, ← hQ'mem]
    exact hηQ x
  let sw : ↥c.A₂ ≃* ↥c.A₁ := swapEquiv c.hτ c.A₁
  let sw' : ↥c'.A₂ ≃* ↥c'.A₁ := swapEquiv c'.hτ c'.A₁
  let η₂ : ↥c.A₂ ≃* ↥c'.A₂ := sw.trans (η.trans sw'.symm)
  have hsw : ∀ b : ↥c.A₂, ((sw b : ↥c.A₁) : H) = c.τ * (b : H) * c.τ⁻¹ := fun b => rfl
  have hη₂ : ∀ b : ↥c.A₂, ((η₂ b : ↥c'.A₂) : H') =
      c'.τ * ((η (sw b) : ↥c'.A₁) : H') * c'.τ⁻¹ := fun b => rfl
  have hcenη : ∀ x : ↥c.A₁, η x ∈ center ↥c'.A₁ ↔ x ∈ center ↥c.A₁ := fun x =>
    mulEquiv_mem_center η
  have hZ : ∀ (x : ↥c.A₁) (hx : (x : H) ∈ c.A₂),
      ((η₂ ⟨(x : H), hx⟩ : ↥c'.A₂) : H') = ((η x : ↥c'.A₁) : H') := by
    intro x hx
    have hsx : sw ⟨(x : H), hx⟩ = x := by
      apply Subtype.ext
      show c.τ * (x : H) * c.τ⁻¹ = x
      exact c.τ_fix x.2 hx
    rw [hη₂, hsx]
    have hxc : x ∈ center ↥c.A₁ := (c.mem_A₂_iff x).1 hx
    have hηxc : η x ∈ center ↥c'.A₁ := (hcenη x).2 hxc
    have hηx₂ : ((η x : ↥c'.A₁) : H') ∈ c'.A₂ := (c'.mem_A₂_iff _).2 hηxc
    exact c'.τ_fix (η x).2 hηx₂
  have hker : ∀ (a : ↥c.A₁) (b : ↥c.A₂),
      (a : H) * (b : H) = 1 ↔ ((η a : ↥c'.A₁) : H') * ((η₂ b : ↥c'.A₂) : H') = 1 := by
    intro a b
    constructor
    · intro hab
      have hb : (b : H) = (a : H)⁻¹ := eq_inv_of_mul_eq_one_right hab
      have hainv : ((a⁻¹ : ↥c.A₁) : H) ∈ c.A₂ := by
        have : ((a⁻¹ : ↥c.A₁) : H) = (b : H) := by rw [hb]; rfl
        rw [this]
        exact b.2
      have hb' : b = ⟨((a⁻¹ : ↥c.A₁) : H), hainv⟩ := Subtype.ext (by rw [hb]; rfl)
      rw [hb', hZ a⁻¹ hainv, map_inv]
      show ((η a : ↥c'.A₁) : H') * (((η a)⁻¹ : ↥c'.A₁) : H') = 1
      simp
    · intro h
      have hb : ((η₂ b : ↥c'.A₂) : H') = ((η a : ↥c'.A₁) : H')⁻¹ := eq_inv_of_mul_eq_one_right h
      have hηa₂ : ((η a : ↥c'.A₁) : H') ∈ c'.A₂ := by
        have h1 : ((η a : ↥c'.A₁) : H')⁻¹ ∈ c'.A₂ := by
          rw [← hb]
          exact (η₂ b).2
        have h2 := c'.A₂.inv_mem h1
        simpa using h2
      have hηac : η a ∈ center ↥c'.A₁ := (c'.mem_A₂_iff _).1 hηa₂
      have hac : a ∈ center ↥c.A₁ := (hcenη a).1 hηac
      have ha₂ : (a : H) ∈ c.A₂ := (c.mem_A₂_iff a).2 hac
      have hainv : ((a⁻¹ : ↥c.A₁) : H) ∈ c.A₂ := c.A₂.inv_mem ha₂
      have hb₀ : η₂ ⟨((a⁻¹ : ↥c.A₁) : H), hainv⟩ = η₂ b := by
        apply Subtype.ext
        rw [hZ a⁻¹ hainv, map_inv, hb]
        rfl
      have hbb : (⟨((a⁻¹ : ↥c.A₁) : H), hainv⟩ : ↥c.A₂) = b := η₂.injective hb₀
      have hb2 := congrArg Subtype.val hbb
      show (a : H) * (b : H) = 1
      rw [← hb2]
      show (a : H) * (a : H)⁻¹ = 1
      group
  obtain ⟨θ₀, hθA₁₀, hθA₂₀⟩ := exists_mulEquiv_sup_of_commute c.hcomm c'.hcomm η η₂ hker
  let θ : ↥c.B ≃* ↥c'.B := θ₀
  have hθA₁ : ∀ a : ↥c.A₁, ((θ ⟨(a : H), c.A₁_le_B a.2⟩ : ↥c'.B) : H') = ((η a : ↥c'.A₁) : H') :=
    hθA₁₀
  have hθA₂ : ∀ b : ↥c.A₂, ((θ ⟨(b : H), c.A₂_le_B b.2⟩ : ↥c'.B) : H') = ((η₂ b : ↥c'.A₂) : H') :=
    hθA₂₀
  have hθ_mul : ∀ (a : ↥c.A₁) (b : ↥c.A₂) (h : (a : H) * (b : H) ∈ c.B),
      ((θ ⟨(a : H) * (b : H), h⟩ : ↥c'.B) : H') =
        ((η a : ↥c'.A₁) : H') * ((η₂ b : ↥c'.A₂) : H') := by
    intro a b h
    have : (⟨(a : H) * (b : H), h⟩ : ↥c.B) =
        ⟨(a : H), c.A₁_le_B a.2⟩ * ⟨(b : H), c.A₂_le_B b.2⟩ := rfl
    rw [this, map_mul]
    show ((θ ⟨(a : H), c.A₁_le_B a.2⟩ : ↥c'.B) : H') * ((θ ⟨(b : H), c.A₂_le_B b.2⟩ : ↥c'.B) : H') = _
    rw [hθA₁ a, hθA₂ b]
  have hη₂swap : ∀ (a : ↥c.A₁) (h : c.τ * (a : H) * c.τ⁻¹ ∈ c.A₂),
      ((η₂ ⟨c.τ * (a : H) * c.τ⁻¹, h⟩ : ↥c'.A₂) : H') =
        c'.τ * ((η a : ↥c'.A₁) : H') * c'.τ⁻¹ := by
    intro a h
    rw [hη₂]
    have : sw ⟨c.τ * (a : H) * c.τ⁻¹, h⟩ = a := by
      apply Subtype.ext
      show c.τ * (c.τ * (a : H) * c.τ⁻¹) * c.τ⁻¹ = a
      calc c.τ * (c.τ * (a : H) * c.τ⁻¹) * c.τ⁻¹ = (c.τ * c.τ) * (a : H) * (c.τ * c.τ)⁻¹ := by group
        _ = a := by rw [c.hτ]; group
    rw [this]
  have hη₂conj : ∀ b : ↥c.A₂, c'.τ * ((η₂ b : ↥c'.A₂) : H') * c'.τ⁻¹ = ((η (sw b) : ↥c'.A₁) : H') := by
    intro b
    rw [hη₂]
    calc c'.τ * (c'.τ * ((η (sw b) : ↥c'.A₁) : H') * c'.τ⁻¹) * c'.τ⁻¹ =
        (c'.τ * c'.τ) * ((η (sw b) : ↥c'.A₁) : H') * (c'.τ * c'.τ)⁻¹ := by group
      _ = _ := by rw [c'.hτ]; group
  have hP1 : ∀ (n : ↥c.B) (h : c.τ * (n : H) * c.τ⁻¹ ∈ c.B),
      ((θ ⟨c.τ * (n : H) * c.τ⁻¹, h⟩ : ↥c'.B) : H') = c'.τ * ((θ n : ↥c'.B) : H') * c'.τ⁻¹ := by
    rintro ⟨g, hg⟩ h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute c.hcomm hg
    have hτa : c.τ * a * c.τ⁻¹ ∈ c.A₂ := mul_mem_swapSub_of_mem c.hτ ha
    have hτb : c.τ * b * c.τ⁻¹ ∈ c.A₁ := hb
    have hcm : (c.τ * b * c.τ⁻¹) * (c.τ * a * c.τ⁻¹) = (c.τ * a * c.τ⁻¹) * (c.τ * b * c.τ⁻¹) :=
      c.hcomm _ hτb _ hτa
    have e : c.τ * (a * b) * c.τ⁻¹ = (c.τ * b * c.τ⁻¹) * (c.τ * a * c.τ⁻¹) := by
      rw [hcm]
      group
    have h' : (c.τ * b * c.τ⁻¹) * (c.τ * a * c.τ⁻¹) ∈ c.B := e ▸ h
    have h1 := hθ_mul ⟨c.τ * b * c.τ⁻¹, hτb⟩ ⟨c.τ * a * c.τ⁻¹, hτa⟩ h'
    have h2 := hθ_mul ⟨a, ha⟩ ⟨b, hb⟩ hg
    have h3' := hη₂swap ⟨a, ha⟩ hτa
    have h4 : ((η ⟨c.τ * b * c.τ⁻¹, hτb⟩ : ↥c'.A₁) : H') = ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') := rfl
    have h5 := hη₂conj ⟨b, hb⟩
    have hcm' := c'.hcomm _ (η (sw ⟨b, hb⟩)).2 (c'.τ * ((η ⟨a, ha⟩ : ↥c'.A₁) : H') * c'.τ⁻¹)
      (mul_mem_swapSub_of_mem c'.hτ (η ⟨a, ha⟩).2)
    show ((θ ⟨c.τ * (a * b) * c.τ⁻¹, h⟩ : ↥c'.B) : H') =
      c'.τ * ((θ ⟨a * b, hg⟩ : ↥c'.B) : H') * c'.τ⁻¹
    have hsub : (⟨c.τ * (a * b) * c.τ⁻¹, h⟩ : ↥c.B) =
        ⟨(c.τ * b * c.τ⁻¹) * (c.τ * a * c.τ⁻¹), h'⟩ := Subtype.ext e
    rw [hsub, h1, h2, h4, h3']
    calc ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') * (c'.τ * ((η ⟨a, ha⟩ : ↥c'.A₁) : H') * c'.τ⁻¹) =
        (c'.τ * ((η ⟨a, ha⟩ : ↥c'.A₁) : H') * c'.τ⁻¹) * ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') := hcm'
      _ = c'.τ * (((η ⟨a, ha⟩ : ↥c'.A₁) : H') * ((η₂ ⟨b, hb⟩ : ↥c'.A₂) : H')) * c'.τ⁻¹ := by
        rw [← h5]
        group
  have hP2 : c.ω ≠ 1 → ∀ (n : ↥c.B) (h : c.ω * (n : H) * c.ω⁻¹ ∈ c.B),
      ((θ ⟨c.ω * (n : H) * c.ω⁻¹, h⟩ : ↥c'.B) : H') = c'.ω * ((θ n : ↥c'.B) : H') * c'.ω⁻¹ := by
    intro hω1
    rintro ⟨g, hg⟩ h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute c.hcomm hg
    have hωa : c.ω * a * c.ω⁻¹ ∈ c.A₁ := c.ω_norm_A₁ ha
    have hωb : c.ω * b * c.ω⁻¹ ∈ c.A₂ := c.ω_norm_A₂ hb
    have e : c.ω * (a * b) * c.ω⁻¹ = (c.ω * a * c.ω⁻¹) * (c.ω * b * c.ω⁻¹) := by group
    have h' : (c.ω * a * c.ω⁻¹) * (c.ω * b * c.ω⁻¹) ∈ c.B := e ▸ h
    have h1 := hθ_mul ⟨c.ω * a * c.ω⁻¹, hωa⟩ ⟨c.ω * b * c.ω⁻¹, hωb⟩ h'
    have h2 := hθ_mul ⟨a, ha⟩ ⟨b, hb⟩ hg
    have hα1 : ((η ⟨c.ω * a * c.ω⁻¹, hωa⟩ : ↥c'.A₁) : H') =
        c'.ω * ((η ⟨a, ha⟩ : ↥c'.A₁) : H') * c'.ω⁻¹ := by
      have : (⟨c.ω * a * c.ω⁻¹, hωa⟩ : ↥c.A₁) = c.α ⟨a, ha⟩ := Subtype.ext (c.hα ⟨a, ha⟩).symm
      rw [this, hηα hω1]
      exact c'.hα _
    have hα2 : ((η₂ ⟨c.ω * b * c.ω⁻¹, hωb⟩ : ↥c'.A₂) : H') =
        c'.ω * ((η₂ ⟨b, hb⟩ : ↥c'.A₂) : H') * c'.ω⁻¹ := by
      rw [hη₂, hη₂]
      have hsw1 : sw ⟨c.ω * b * c.ω⁻¹, hωb⟩ = c.α (sw ⟨b, hb⟩) := by
        apply Subtype.ext
        rw [c.hα]
        show c.τ * (c.ω * b * c.ω⁻¹) * c.τ⁻¹ = c.ω * (c.τ * b * c.τ⁻¹) * c.ω⁻¹
        calc c.τ * (c.ω * b * c.ω⁻¹) * c.τ⁻¹ = (c.τ * c.ω) * b * (c.τ * c.ω)⁻¹ := by group
          _ = (c.ω * c.τ) * b * (c.ω * c.τ)⁻¹ := by rw [c.hτω]
          _ = c.ω * (c.τ * b * c.τ⁻¹) * c.ω⁻¹ := by group
      rw [hsw1, hηα hω1, c'.hα]
      calc c'.τ * (c'.ω * ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') * c'.ω⁻¹) * c'.τ⁻¹ =
          (c'.τ * c'.ω) * ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') * (c'.τ * c'.ω)⁻¹ := by group
        _ = (c'.ω * c'.τ) * ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') * (c'.ω * c'.τ)⁻¹ := by rw [c'.hτω]
        _ = c'.ω * (c'.τ * ((η (sw ⟨b, hb⟩) : ↥c'.A₁) : H') * c'.τ⁻¹) * c'.ω⁻¹ := by group
    have hsub : (⟨c.ω * (a * b) * c.ω⁻¹, h⟩ : ↥c.B) =
        ⟨(c.ω * a * c.ω⁻¹) * (c.ω * b * c.ω⁻¹), h'⟩ := Subtype.ext e
    show ((θ ⟨c.ω * (a * b) * c.ω⁻¹, h⟩ : ↥c'.B) : H') =
      c'.ω * ((θ ⟨a * b, hg⟩ : ↥c'.B) : H') * c'.ω⁻¹
    rw [hsub, h1, h2, hα1, hα2]
    group
  have hηP₂ : ∀ b : ↥c.A₂, (b : H) ∈ c.P₂ ↔ ((η₂ b : ↥c'.A₂) : H') ∈ c'.P₂ := by
    intro b
    have h1 : (b : H) ∈ c.P₂ ↔ ((sw b : ↥c.A₁) : H) ∈ c.P₁ := Iff.rfl
    rw [h1, hηP (sw b)]
    show ((η (sw b) : ↥c'.A₁) : H') ∈ c'.P₁ ↔ c'.τ * ((η₂ b : ↥c'.A₂) : H') * c'.τ⁻¹ ∈ c'.P₁
    rw [hη₂conj b]
  have himg₁ : ∀ y : ↥c'.B, y ∈ (c.P₁.subgroupOf c.B).map θ.toMonoidHom ↔
      y ∈ c'.P₁.subgroupOf c'.B := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : H) ∈ c.P₁ := hx
      have hxA : (x : H) ∈ c.A₁ := c.P₁_le hxP
      have h1 := hθA₁ ⟨(x : H), hxA⟩
      show ((θ x : ↥c'.B) : H') ∈ c'.P₁
      have hxeq : x = ⟨(x : H), c.A₁_le_B hxA⟩ := rfl
      rw [hxeq, h1]
      exact (hηP ⟨(x : H), hxA⟩).1 hxP
    · intro hy
      have hyP : ((y : ↥c'.B) : H') ∈ c'.P₁ := hy
      have hyA : ((y : ↥c'.B) : H') ∈ c'.A₁ := c'.P₁_le hyP
      refine ⟨⟨((η.symm ⟨(y : H'), hyA⟩ : ↥c.A₁) : H), c.A₁_le_B (η.symm ⟨(y : H'), hyA⟩).2⟩, ?_, ?_⟩
      · show ((η.symm ⟨(y : H'), hyA⟩ : ↥c.A₁) : H) ∈ c.P₁
        rw [hηP]
        simpa using hyP
      · apply Subtype.ext
        show ((θ ⟨((η.symm ⟨(y : H'), hyA⟩ : ↥c.A₁) : H), _⟩ : ↥c'.B) : H') = (y : H')
        rw [hθA₁]
        simp
  have himg₂ : ∀ y : ↥c'.B, y ∈ (c.P₂.subgroupOf c.B).map θ.toMonoidHom ↔
      y ∈ c'.P₂.subgroupOf c'.B := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : H) ∈ c.P₂ := hx
      have hxA : (x : H) ∈ c.A₂ := c.P₂_le hxP
      have h1 := hθA₂ ⟨(x : H), hxA⟩
      show ((θ x : ↥c'.B) : H') ∈ c'.P₂
      have hxeq : x = ⟨(x : H), c.A₂_le_B hxA⟩ := rfl
      rw [hxeq, h1]
      exact (hηP₂ ⟨(x : H), hxA⟩).1 hxP
    · intro hy
      have hyP : ((y : ↥c'.B) : H') ∈ c'.P₂ := hy
      have hyA : ((y : ↥c'.B) : H') ∈ c'.A₂ := c'.P₂_le hyP
      refine ⟨⟨((η₂.symm ⟨(y : H'), hyA⟩ : ↥c.A₂) : H), c.A₂_le_B (η₂.symm ⟨(y : H'), hyA⟩).2⟩, ?_, ?_⟩
      · show ((η₂.symm ⟨(y : H'), hyA⟩ : ↥c.A₂) : H) ∈ c.P₂
        rw [hηP₂]
        simpa using hyP
      · apply Subtype.ext
        show ((θ ⟨((η₂.symm ⟨(y : H'), hyA⟩ : ↥c.A₂) : H), _⟩ : ↥c'.B) : H') = (y : H')
        rw [hθA₂]
        simp
  have hPmap : (c.P.subgroupOf c.B).map θ.toMonoidHom = c'.P.subgroupOf c'.B := by
    have e1 : c.P.subgroupOf c.B = c.P₁.subgroupOf c.B ⊔ c.P₂.subgroupOf c.B :=
      Subgroup.subgroupOf_sup (c.P₁_le.trans c.A₁_le_B) (c.P₂_le.trans c.A₂_le_B)
    have e2 : c'.P.subgroupOf c'.B = c'.P₁.subgroupOf c'.B ⊔ c'.P₂.subgroupOf c'.B :=
      Subgroup.subgroupOf_sup (c'.P₁_le.trans c'.A₁_le_B) (c'.P₂_le.trans c'.A₂_le_B)
    rw [e1, e2, Subgroup.map_sup]
    congr 1
    · ext y
      exact himg₁ y
    · ext y
      exact himg₂ y
  have hP3 : ∀ x : ↥c.B, (x : H) ∈ c.P ↔ ((θ x : ↥c'.B) : H') ∈ c'.P := by
    intro x
    have h1 : x ∈ c.P.subgroupOf c.B ↔ θ x ∈ c'.P.subgroupOf c'.B := by
      rw [← hPmap]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x', hx', hxx'⟩
        have : x' = x := θ.injective hxx'
        rw [← this]
        exact hx'
    exact h1
  exact ⟨θ, hP1, hP2, hP3⟩

theorem yconf_props (c : YConf F hodd h3 H) (c' : YConf F hodd h3 H') (θ : ↥c.B ≃* ↥c'.B)
    (hP3 : ∀ x : ↥c.B, (x : H) ∈ c.P ↔ ((θ x : ↥c'.B) : H') ∈ c'.P) (ψ : ↥c.X ≃* ↥c'.X)
    (hψ : ∀ n : ↥c.B, ((ψ ⟨(n : H), c.B_le_X n.2⟩ : ↥c'.X) : H') = ((θ n : ↥c'.B) : H')) :
    (∀ x : ↥c.X, (x : H) ∈ c.B ↔ ((ψ x : ↥c'.X) : H') ∈ c'.B) ∧
      (∀ x : ↥c.X, (x : H) ∈ c.P ↔ ((ψ x : ↥c'.X) : H') ∈ c'.P) := by
  have hB : ∀ x : ↥c.X, (x : H) ∈ c.B ↔ ((ψ x : ↥c'.X) : H') ∈ c'.B := by
    intro x
    constructor
    · intro hx
      have h1 := hψ ⟨(x : H), hx⟩
      have hxe : x = ⟨(x : H), c.B_le_X hx⟩ := rfl
      rw [hxe, h1]
      exact (θ ⟨(x : H), hx⟩).2
    · intro hy
      let n : ↥c.B := θ.symm ⟨((ψ x : ↥c'.X) : H'), hy⟩
      have h1 := hψ n
      have h2 : ((ψ ⟨(n : H), c.B_le_X n.2⟩ : ↥c'.X) : H') = ((ψ x : ↥c'.X) : H') := by
        rw [h1]
        simp [n]
      have h3' : (⟨(n : H), c.B_le_X n.2⟩ : ↥c.X) = x := ψ.injective (Subtype.ext h2)
      have h4 := congrArg Subtype.val h3'
      rw [← h4]
      exact n.2
  refine ⟨hB, fun x => ?_⟩
  constructor
  · intro hx
    have hxB : (x : H) ∈ c.B := c.P_le_B hx
    have h1 := hψ ⟨(x : H), hxB⟩
    have hxe : x = ⟨(x : H), c.B_le_X hxB⟩ := rfl
    rw [hxe, h1]
    exact (hP3 ⟨(x : H), hxB⟩).1 hx
  · intro hx
    have hxB' : ((ψ x : ↥c'.X) : H') ∈ c'.B := c'.P_le_B hx
    have hxB : (x : H) ∈ c.B := (hB x).2 hxB'
    have h1 := hψ ⟨(x : H), hxB⟩
    have hxe : x = ⟨(x : H), c.B_le_X hxB⟩ := rfl
    rw [hxe, h1] at hx
    exact (hP3 ⟨(x : H), hxB⟩).2 hx

theorem yconf_iso (c : YConf F hodd h3 H) (c' : YConf F hodd h3 H') (hωω : c.ω = 1 ↔ c'.ω = 1) :
    ∃ ψ : ↥c.X ≃* ↥c'.X,
      ((ψ ⟨c.τ, c.τ_mem_X⟩ : ↥c'.X) : H') = c'.τ ∧ ((ψ ⟨c.ω, c.ω_mem_X⟩ : ↥c'.X) : H') = c'.ω ∧
      (∀ x : ↥c.X, (x : H) ∈ c.B ↔ ((ψ x : ↥c'.X) : H') ∈ c'.B) ∧
      (∀ x : ↥c.X, (x : H) ∈ c.P ↔ ((ψ x : ↥c'.X) : H') ∈ c'.P) := by
  classical
  obtain ⟨θ, hP1, hP2, hP3⟩ := yconf_iso_B c c' hωω
  obtain ⟨θ₁, hθ₁B, hθ₁τ⟩ := exists_mulEquiv_sup_zpowers c.hτ c'.hτ (fun n hn => c.τ_norm_B hn)
    (fun n hn => c'.τ_norm_B hn) c.τ_notin_B c'.τ_notin_B θ (fun n h => hP1 n h)
  by_cases hω1 : c.ω = 1
  · have hω1' : c'.ω = 1 := hωω.1 hω1
    have hX : c.X = c.B ⊔ zpowers c.τ := by
      rw [YConf.X, hω1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    have hX' : c'.X = c'.B ⊔ zpowers c'.τ := by
      rw [YConf.X, hω1', Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    let ψ : ↥c.X ≃* ↥c'.X := (MulEquiv.subgroupCongr hX).trans (θ₁.trans (MulEquiv.subgroupCongr hX'.symm))
    have hψ : ∀ n : ↥c.B, ((ψ ⟨(n : H), c.B_le_X n.2⟩ : ↥c'.X) : H') = ((θ n : ↥c'.B) : H') := fun n =>
      hθ₁B n
    obtain ⟨hB, hP⟩ := yconf_props c c' θ hP3 ψ hψ
    refine ⟨ψ, hθ₁τ, ?_, hB, hP⟩
    have h1 : (⟨c.ω, c.ω_mem_X⟩ : ↥c.X) = 1 := Subtype.ext hω1
    rw [h1, map_one]
    exact hω1'.symm
  · have hω1' : c'.ω ≠ 1 := fun h => hω1 (hωω.2 h)
    obtain ⟨θ₂, hθ₂N, hθ₂ω⟩ := exists_mulEquiv_sup_zpowers c.hω c'.hω
      (fun n hn => c.ω_norm_N hn) (fun n hn => c'.ω_norm_N hn) (c.ω_notin hω1) (c'.ω_notin hω1') θ₁
      (by
        rintro ⟨g, hg⟩ h
        rcases mem_sup_zpowers_cases c.hτ (fun n hn => c.τ_norm_B hn) hg with hgB | ⟨b, hb, rfl⟩
        · have hωg : c.ω * g * c.ω⁻¹ ∈ c.B := c.ω_norm_B hgB
          have h1 := hθ₁B ⟨c.ω * g * c.ω⁻¹, hωg⟩
          have h2 := hθ₁B ⟨g, hgB⟩
          have h3' := hP2 hω1 ⟨g, hgB⟩ hωg
          show ((θ₁ ⟨c.ω * g * c.ω⁻¹, h⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') =
            c'.ω * ((θ₁ ⟨g, hg⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') * c'.ω⁻¹
          rw [h1, h2, h3']
        · have hωb : c.ω * b * c.ω⁻¹ ∈ c.B := c.ω_norm_B hb
          have e : c.ω * (b * c.τ) * c.ω⁻¹ = (c.ω * b * c.ω⁻¹) * c.τ := by
            have := c.ω_comm_τ
            calc c.ω * (b * c.τ) * c.ω⁻¹ = (c.ω * b * c.ω⁻¹) * (c.ω * c.τ * c.ω⁻¹) := by group
              _ = (c.ω * b * c.ω⁻¹) * c.τ := by rw [this]
          have hmem1 : (c.ω * b * c.ω⁻¹) * c.τ ∈ c.B ⊔ zpowers c.τ :=
            mul_mem (mem_sup_left hωb) (mem_sup_right (mem_zpowers _))
          have hmem2 : b * c.τ ∈ c.B ⊔ zpowers c.τ :=
            mul_mem (mem_sup_left hb) (mem_sup_right (mem_zpowers _))
          have hsub : (⟨c.ω * (b * c.τ) * c.ω⁻¹, h⟩ : ↥(c.B ⊔ zpowers c.τ)) =
              ⟨c.ω * b * c.ω⁻¹, mem_sup_left hωb⟩ * ⟨c.τ, mem_sup_right (mem_zpowers _)⟩ :=
            Subtype.ext e
          have hsub2 : (⟨b * c.τ, hg⟩ : ↥(c.B ⊔ zpowers c.τ)) =
              ⟨b, mem_sup_left hb⟩ * ⟨c.τ, mem_sup_right (mem_zpowers _)⟩ := rfl
          have h1 := hθ₁B ⟨c.ω * b * c.ω⁻¹, hωb⟩
          have h2 := hθ₁B ⟨b, hb⟩
          have h3' := hP2 hω1 ⟨b, hb⟩ hωb
          have hτω' : c'.ω * c'.τ * c'.ω⁻¹ = c'.τ := c'.ω_comm_τ
          show ((θ₁ ⟨c.ω * (b * c.τ) * c.ω⁻¹, h⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') =
            c'.ω * ((θ₁ ⟨b * c.τ, hg⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') * c'.ω⁻¹
          rw [hsub, hsub2, map_mul, map_mul]
          show ((θ₁ ⟨c.ω * b * c.ω⁻¹, _⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') *
              ((θ₁ ⟨c.τ, _⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') =
            c'.ω * (((θ₁ ⟨b, _⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H') *
              ((θ₁ ⟨c.τ, _⟩ : ↥(c'.B ⊔ zpowers c'.τ)) : H')) * c'.ω⁻¹
          rw [h1, h2, h3', hθ₁τ]
          calc c'.ω * ((θ ⟨b, hb⟩ : ↥c'.B) : H') * c'.ω⁻¹ * c'.τ =
              c'.ω * ((θ ⟨b, hb⟩ : ↥c'.B) : H') * c'.ω⁻¹ * (c'.ω * c'.τ * c'.ω⁻¹) := by rw [hτω']
            _ = c'.ω * (((θ ⟨b, hb⟩ : ↥c'.B) : H') * c'.τ) * c'.ω⁻¹ := by group)
    have hψ : ∀ n : ↥c.B, ((θ₂ ⟨(n : H), c.B_le_X n.2⟩ : ↥c'.X) : H') = ((θ n : ↥c'.B) : H') := by
      intro n
      have h1 := hθ₂N ⟨(n : H), mem_sup_left n.2⟩
      have h2 := hθ₁B n
      exact h1.trans h2
    obtain ⟨hB, hP⟩ := yconf_props c c' θ hP3 θ₂ hψ
    refine ⟨θ₂, ?_, hθ₂ω, hB, hP⟩
    have h1 := hθ₂N ⟨c.τ, mem_sup_right (mem_zpowers _)⟩
    exact h1.trans hθ₁τ

end IsoB

end CFSG.GH74.GLS.IVK.Lifted
