module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finite_linearEquiv_zmod_two [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective

theorem eq_of_add_eq_zero_zmod_two {v w : V} (h : v + w = 0) : v = w := by
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
  exact h

theorem mem_or_sub_mem_of_isCompl {z : V} {W : Submodule (ZMod 2) V}
    (hzW : IsCompl (Submodule.span (ZMod 2) {z}) W) (v : V) : v ∈ W ∨ v - z ∈ W := by
  have hv : v ∈ Submodule.span (ZMod 2) {z} ⊔ W := by rw [hzW.sup_eq_top]; trivial
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have key : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases key a with rfl | rfl
  · left; simpa using hw
  · right; simpa using hw

theorem eq_one_of_fixes_of_isCompl {z : V} {W : Submodule (ZMod 2) V}
    (hzW : IsCompl (Submodule.span (ZMod 2) {z}) W) {c : V ≃ₗ[ZMod 2] V} (hcz : c z = z)
    (hcW : ∀ w ∈ W, c w = w) : c = 1 := by
  ext v
  rcases mem_or_sub_mem_of_isCompl hzW v with hv | hv
  · exact hcW v hv
  · have h := hcW _ hv
    rw [map_sub, hcz, sub_left_inj] at h
    exact h

theorem card_inf_stabilizer_apply {P : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ a ∈ P, g * a * g⁻¹ ∈ P) (hg' : ∀ a ∈ P, g⁻¹ * a * g ∈ P) (v : V) :
    Nat.card (P ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) (g v) : Subgroup _) =
      Nat.card (P ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v : Subgroup _) := by
  have mem : ∀ {u : V} {a : V ≃ₗ[ZMod 2] V},
      a ∈ (P ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) u : Subgroup _) ↔ a ∈ P ∧ a u = u := by
    intro u a
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * x * g, mem.mpr ⟨hg' _ (mem.mp x.2).1, ?_⟩⟩
      invFun := fun x => ⟨g * x * g⁻¹, mem.mpr ⟨hg _ (mem.mp x.2).1, ?_⟩⟩
      left_inv := fun x => by ext1; simp [mul_assoc]
      right_inv := fun x => by ext1; simp [mul_assoc] }
  · simp [(mem.mp x.2).2]
  · simp [(mem.mp x.2).2]

theorem eq_one_of_mem_of_apply_eq_self [Finite V] {Y P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPnorm : ∀ g ∈ Y, ∀ a ∈ P, g * a * g⁻¹ ∈ P)
    (hYtrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ y ∈ Y, y v = w) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ P)
    {v : V} (hv : v ≠ 0) (hxv : x v = v) : x = 1 := by
  have := finite_linearEquiv_zmod_two (V := V)
  set A : V → Subgroup (V ≃ₗ[ZMod 2] V) := fun u => P ⊓ MulAction.stabilizer _ u with hA
  have memA : ∀ {u : V} {a : V ≃ₗ[ZMod 2] V}, a ∈ A u ↔ a ∈ P ∧ a u = u := by
    intro u a
    simp [hA, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  have hcard : ∀ u u' : V, u ≠ 0 → u' ≠ 0 → Nat.card (A u') = Nat.card (A u) := by
    intro u u' hu hu'
    obtain ⟨g, hg, rfl⟩ := hYtrans u u' hu hu'
    exact card_inf_stabilizer_apply (hPnorm g hg)
      (fun a ha => by simpa using hPnorm g⁻¹ (Y.inv_mem hg) a ha) u
  have heq : ∀ u u' : V, u ≠ 0 → u' ≠ 0 → A u = A u' := by
    intro u u' hu hu'
    by_contra hne
    have hboth : ∀ d : V, d ≠ 0 → (∀ a ∈ A u, a d = d) → (∀ b ∈ A u', b d = d) → False := by
      intro d hd hdu hdu'
      have h1 : A u = A d := Subgroup.eq_of_le_of_card_ge
        (fun a ha => memA.mpr ⟨(memA.mp ha).1, hdu a ha⟩) (hcard u d hu hd).le
      have h2 : A u' = A d := Subgroup.eq_of_le_of_card_ge
        (fun a ha => memA.mpr ⟨(memA.mp ha).1, hdu' a ha⟩) (hcard u' d hu' hd).le
      exact hne (h1.trans h2.symm)
    have hsum : u + u' ≠ 0 := fun h => hne (by rw [eq_of_add_eq_zero_zmod_two h])
    have hfix : ∀ y ∈ A (u + u'), y u = u ∧ y u' = u' := by
      intro y hy
      obtain ⟨hyP, hyu⟩ := memA.mp hy
      have hd : y u - u = u' - y u' := by
        rw [map_add] at hyu
        rw [sub_eq_sub_iff_add_eq_add, hyu, add_comm]
      by_contra hcon
      have hd0 : y u - u ≠ 0 := by
        intro h0
        rw [h0, eq_comm, sub_eq_zero] at hd
        exact hcon ⟨(sub_eq_zero.mp h0), hd.symm⟩
      refine hboth _ hd0 (fun a ha => ?_) (fun b hb => ?_)
      · obtain ⟨haP, hau⟩ := memA.mp ha
        have hay : a (y u) = y (a u) := by
          rw [← LinearEquiv.mul_apply, hPcomm a haP y hyP, LinearEquiv.mul_apply]
        rw [map_sub, hay, hau]
      · obtain ⟨hbP, hbu⟩ := memA.mp hb
        have hby : b (y u') = y (b u') := by
          rw [← LinearEquiv.mul_apply, hPcomm b hbP y hyP, LinearEquiv.mul_apply]
        rw [hd, map_sub, hby, hbu]
    have h1 : A (u + u') = A u := Subgroup.eq_of_le_of_card_ge
      (fun y hy => memA.mpr ⟨(memA.mp hy).1, (hfix y hy).1⟩) (hcard (u + u') u hsum hu).le
    have h2 : A (u + u') = A u' := Subgroup.eq_of_le_of_card_ge
      (fun y hy => memA.mpr ⟨(memA.mp hy).1, (hfix y hy).2⟩) (hcard (u + u') u' hsum hu').le
    exact hne (h1.symm.trans h2)
  ext w
  by_cases hw : w = 0
  · simp [hw]
  · have hxw : x ∈ A w := heq v w hv hw ▸ memA.mpr ⟨hx, hxv⟩
    exact (memA.mp hxw).2

theorem eq_one_of_commute_of_fixedPointFree {z : V} (hz : z ≠ 0) {W : Submodule (ZMod 2) V}
    (hzW : IsCompl (Submodule.span (ZMod 2) {z}) W) {C₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hC₀comm : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a) (hC₀z : ∀ c ∈ C₀, c z = z)
    (hC₀trans : ∀ w ∈ W, w ≠ 0 → ∀ w' ∈ W, w' ≠ 0 → ∃ c ∈ C₀, c w = w')
    {x : V ≃ₗ[ZMod 2] V} (hx : ∀ v, x v = v → v = 0) {c : V ≃ₗ[ZMod 2] V} (hc : c ∈ C₀)
    (hcx : c * x = x * c) : c = 1 := by
  by_cases hW : ∃ w ∈ W, w ≠ 0 ∧ c w = w
  · obtain ⟨w, hwW, hw0, hcw⟩ := hW
    refine eq_one_of_fixes_of_isCompl hzW (hC₀z c hc) fun w' hw'W => ?_
    by_cases hw' : w' = 0
    · rw [hw', map_zero]
    obtain ⟨c', hc', rfl⟩ := hC₀trans w hwW hw0 w' hw'W hw'
    rw [← LinearEquiv.mul_apply, hC₀comm c hc c' hc', LinearEquiv.mul_apply, hcw]
  · simp only [not_exists, not_and] at hW
    exfalso
    have hcxz : c (x z) = x z := by
      rw [← LinearEquiv.mul_apply, hcx, LinearEquiv.mul_apply, hC₀z c hc]
    rcases mem_or_sub_mem_of_isCompl hzW (x z) with h | h
    · have hxz0 : x z ≠ 0 := by
        intro h0
        exact hz (x.injective (h0.trans (map_zero x).symm))
      exact hW _ h hxz0 hcxz
    · have hd0 : x z - z ≠ 0 := fun h0 => hz (hx z (sub_eq_zero.mp h0))
      exact hW _ h hd0 (by rw [map_sub, hcxz, hC₀z c hc])

theorem card_add_one_le_card_of_conj_injective [Finite V] {Y P C₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPnorm : ∀ g ∈ Y, ∀ a ∈ P, g * a * g⁻¹ ∈ P) (hC₀Y : C₀ ≤ Y) {x : V ≃ₗ[ZMod 2] V}
    (hxP : x ∈ P) (hx1 : x ≠ 1) (hfaith : ∀ c ∈ C₀, c * x = x * c → c = 1) :
    Nat.card C₀ + 1 ≤ Nat.card P := by
  have := finite_linearEquiv_zmod_two (V := V)
  let f : Option C₀ → P := fun o => o.elim 1 fun c =>
    ⟨c * x * (c : V ≃ₗ[ZMod 2] V)⁻¹, hPnorm c (hC₀Y c.2) x hxP⟩
  have hne : ∀ c : C₀, (c : V ≃ₗ[ZMod 2] V) * x * (c : V ≃ₗ[ZMod 2] V)⁻¹ ≠ 1 := by
    intro c h
    rw [mul_inv_eq_one, mul_eq_left] at h
    exact hx1 h
  have hf : Function.Injective f := by
    rintro (_ | c₁) (_ | c₂) h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hne c₂)
    · exact absurd (congrArg Subtype.val h) (hne c₁)
    · have h' : (c₁ : V ≃ₗ[ZMod 2] V) * x * (c₁ : V ≃ₗ[ZMod 2] V)⁻¹ =
          c₂ * x * (c₂ : V ≃ₗ[ZMod 2] V)⁻¹ := congrArg Subtype.val h
      have hc : ((c₂⁻¹ * c₁ : C₀) : V ≃ₗ[ZMod 2] V) = 1 := by
        refine hfaith _ (c₂⁻¹ * c₁).2 ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (c₂ : V ≃ₗ[ZMod 2] V)⁻¹ * c₁ * x
            = (c₂ : V ≃ₗ[ZMod 2] V)⁻¹ * (c₁ * x * (c₁ : V ≃ₗ[ZMod 2] V)⁻¹) * c₁ := by group
          _ = (c₂ : V ≃ₗ[ZMod 2] V)⁻¹ * (c₂ * x * (c₂ : V ≃ₗ[ZMod 2] V)⁻¹) * c₁ := by rw [h']
          _ = x * ((c₂ : V ≃ₗ[ZMod 2] V)⁻¹ * c₁) := by group
      have : c₂⁻¹ * c₁ = 1 := Subtype.ext hc
      rw [inv_mul_eq_one] at this
      rw [this]
  have hle := Nat.card_le_card_of_injective f hf
  have := Fintype.ofFinite C₀
  rwa [Nat.card_eq_fintype_card (α := Option C₀), Fintype.card_option,
    ← Nat.card_eq_fintype_card] at hle

theorem exists_mem_apply_eq_of_card_le [Finite V] {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hfree : ∀ x ∈ P, ∀ v : V, v ≠ 0 → x v = v → x = 1)
    (hcard : Nat.card V ≤ 2 * Nat.card P) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x ∈ P, x v = w := by
  classical
  have := finite_linearEquiv_zmod_two (V := V)
  have := Fintype.ofFinite V
  have := Fintype.ofFinite P
  have hinj : ∀ u : V, u ≠ 0 → Function.Injective fun x : P => (x : V ≃ₗ[ZMod 2] V) u := by
    intro u hu x y hxy
    have h1 : ((y⁻¹ * x : P) : V ≃ₗ[ZMod 2] V) = 1 := by
      refine hfree _ (y⁻¹ * x).2 u hu ?_
      have hxy' : (x : V ≃ₗ[ZMod 2] V) u = (y : V ≃ₗ[ZMod 2] V) u := hxy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      exact (LinearEquiv.symm_apply_eq _).mpr hxy'
    have : y⁻¹ * x = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp this).symm
  set A := Finset.univ.image fun x : P => (x : V ≃ₗ[ZMod 2] V) v
  set B := Finset.univ.image fun x : P => (x : V ≃ₗ[ZMod 2] V) w
  have hA : A.card = Nat.card P := by
    rw [Finset.card_image_of_injective _ (hinj v hv), Finset.card_univ, Nat.card_eq_fintype_card]
  have hB : B.card = Nat.card P := by
    rw [Finset.card_image_of_injective _ (hinj w hw), Finset.card_univ, Nat.card_eq_fintype_card]
  have hsub : A ∪ B ⊆ Finset.univ.erase 0 := by
    intro u hu
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_union.mp hu with hu | hu <;>
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu <;>
      exact fun h => by
        first
        | exact hv (x.1.injective (h.trans (map_zero _).symm))
        | exact hw (x.1.injective (h.trans (map_zero _).symm))
  have hnd : ¬ Disjoint A B := by
    intro hdisj
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hA, hB] at h1
    have hV : 0 < Nat.card V := Nat.card_pos
    omega
  obtain ⟨u, huA, huB⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp huA
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp huB
  refine ⟨(y : V ≃ₗ[ZMod 2] V)⁻¹ * x, P.mul_mem (P.inv_mem y.2) x.2, ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.coe_inv, ← hy, LinearEquiv.symm_apply_apply]

end CFSG.ProperTwoGeneratedCore.Assembly
