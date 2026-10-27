module

public import CFSG.CGT.Foote81L6.TStruct.E64

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct DihedralGroup

namespace TStruct

variable {G : Type*} [Group G]

theorem mem_map_conj {X : Subgroup G} {g x : G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem conj_mem_map_conj {X : Subgroup G} {g x : G} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩

theorem map_conj_map_conj (X : Subgroup G) (g h : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      X.map (MulAut.conj (h * g)).toMonoidHom := by
  ext x
  rw [mem_map_conj, mem_map_conj, mem_map_conj, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem map_conj_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  rw [mem_map_conj]
  simp

theorem map_conj_inv_map_conj (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]

theorem map_conj_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : X.map (MulAut.conj g).toMonoidHom = X := by
  ext x
  rw [mem_map_conj]
  have h := (mem_normalizer_iff.1 (inv_mem hg)) x
  rw [inv_inv] at h
  exact h.symm

theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← h]
    exact conj_mem_map_conj hy
  · rw [← h, mem_map_conj] at hy
    simpa [mul_assoc] using hy

theorem map_conj_inf (X Y : Subgroup G) (g : G) :
    (X ⊓ Y).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj g).toMonoidHom ⊓ Y.map (MulAut.conj g).toMonoidHom :=
  map_inf_eq _ _ _ (MulAut.conj g).injective

theorem card_map_conj (X : Subgroup G) (g : G) :
    Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
  card_map_of_injective (MulAut.conj g).injective

theorem mul_self_map_conj {X : Subgroup G} (hX : ∀ x ∈ X, x * x = 1) (g : G) :
    ∀ x ∈ X.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, hX x hx, map_one]

theorem map_conj_le {X Y : Subgroup G} {g : G} (hXY : X ≤ Y)
    (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : X.map (MulAut.conj g).toMonoidHom ≤ Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact hY x (hXY hx)

theorem map_conj_eq_of_agree {X : Subgroup G} {y w : G}
    (h : ∀ v ∈ X, y * v * y⁻¹ = w * v * w⁻¹) :
    X.map (MulAut.conj y).toMonoidHom = X.map (MulAut.conj w).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (h v hv).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, h v hv⟩

theorem map_conj_eq_self_of_comm {X : Subgroup G} {g : G} (h : ∀ x ∈ X, g * x = x * g) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  have e : X.map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj (1 : G)).toMonoidHom :=
    map_conj_eq_of_agree fun v hv => by rw [h v hv, mul_inv_cancel_right, one_mul, inv_one, mul_one]
  rw [e, map_conj_one]

theorem inf_map_conj {E X : Subgroup G} {y : G} (hy : ∀ v ∈ X, y * v * y⁻¹ ∈ X)
    (hy' : ∀ v ∈ X, y⁻¹ * v * y ∈ X) :
    (E.map (MulAut.conj y).toMonoidHom) ⊓ X = (E ⊓ X).map (MulAut.conj y).toMonoidHom := by
  rw [map_conj_inf]
  congr 1
  ext v
  rw [mem_map_conj]
  constructor
  · exact hy' v
  · intro hv
    have := hy _ hv
    rwa [show y * (y⁻¹ * v * y) * y⁻¹ = v by group] at this

theorem conj_mem_normalizer_map_conj {X : Subgroup G} {g x : G}
    (hx : x ∈ normalizer (X : Set G)) :
    g * x * g⁻¹ ∈ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  refine mem_normalizer_iff.2 fun y => ?_
  rw [mem_map_conj, mem_map_conj, (mem_normalizer_iff.1 hx) (g⁻¹ * y * g)]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem conj_mem_normalizer_of_map_conj_eq {X Y : Subgroup G} {g x : G}
    (hY : X.map (MulAut.conj g).toMonoidHom = Y) (hx : x ∈ normalizer (X : Set G)) :
    g * x * g⁻¹ ∈ normalizer (Y : Set G) := by
  rw [← hY]
  exact conj_mem_normalizer_map_conj hx

theorem IsFourIn.finite {H V : Subgroup G} (hV : IsFourIn H V) : Finite V :=
  Nat.finite_of_card_ne_zero (by rw [hV.2.2]; norm_num)

theorem isFourIn_map_conj {H V : Subgroup G} (hV : IsFourIn H V) {g : G}
    (hg : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : IsFourIn H (V.map (MulAut.conj g).toMonoidHom) :=
  ⟨map_conj_le hV.1 hg, mul_self_map_conj hV.2.1 g, by rw [card_map_conj, hV.2.2]⟩

theorem mul_inv_mem_of_card_eq_two_mul {R V : Subgroup G} [Finite R] (hVR : V ≤ R)
    (hcard : Nat.card R = 2 * Nat.card V) {x y : G} (hx : x ∈ R) (hy : y ∈ R) (hxV : x ∉ V)
    (hyV : y ∉ V) : x * y⁻¹ ∈ V := by
  haveI : Finite V := Finite.of_injective _ (inclusion_injective hVR)
  have hidx : (V.subgroupOf R).index = 2 := by
    have h1 := (V.subgroupOf R).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card V := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm 2 _))
  have h := (mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y⁻¹, inv_mem hy⟩)).2
    (iff_of_false (fun h => hxV (mem_subgroupOf.1 h))
      (fun h => hyV (by simpa using inv_mem (mem_subgroupOf.1 h))))
  exact mem_subgroupOf.1 h

end TStruct

theorem IsE64.map_conj {G : Type*} [Group G] {T E : Subgroup G} (hE : IsE64 T E) {g : G}
    (hg : g ∈ T) : IsE64 T (E.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨map_conj_le hE.1 fun y hy => mul_mem (mul_mem hg hy) (inv_mem hg),
    isElemAbelian_two_iff.2 (mul_self_map_conj hE.mul_self g), ?_⟩
  rw [card_map_conj, hE.2.2]

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

@[expose] def sConj (X : Subgroup G) : Subgroup G := X.map (MulAut.conj D.s).toMonoidHom

theorem sConj_sConj (X : Subgroup G) : D.sConj (D.sConj X) = X := by
  rw [sConj, sConj, map_conj_map_conj, D.s_mul_s, map_conj_one]

theorem sConj_B₁ : D.sConj D.B₁ = D.B₀ := by
  rw [← D.conj_s_B₀]
  exact D.sConj_sConj D.B₀

theorem sConj_le_B₁ {V : Subgroup G} (hV : V ≤ D.B₀) : D.sConj V ≤ D.B₁ := by
  rintro _ ⟨v, hv, rfl⟩
  exact D.conj_s_mem_B₁ (hV hv)

theorem sConj_le_B₀ {V : Subgroup G} (hV : V ≤ D.B₁) : D.sConj V ≤ D.B₀ := by
  rintro _ ⟨v, hv, rfl⟩
  exact D.conj_s_mem_B₀ (hV hv)

theorem isFourIn_sConj₀ {V : Subgroup G} (hV : IsFourIn D.B₀ V) : IsFourIn D.B₁ (D.sConj V) :=
  ⟨D.sConj_le_B₁ hV.1, mul_self_map_conj hV.2.1 _, by rw [sConj, card_map_conj, hV.2.2]⟩

theorem isFourIn_sConj₁ {V : Subgroup G} (hV : IsFourIn D.B₁ V) : IsFourIn D.B₀ (D.sConj V) :=
  ⟨D.sConj_le_B₀ hV.1, mul_self_map_conj hV.2.1 _, by rw [sConj, card_map_conj, hV.2.2]⟩

include D in
theorem one_le_n_sub_one : 1 ≤ n - 1 := by have := D.three_le_n; omega

include D in
theorem two_le_n_sub_one : 2 ≤ n - 1 := by have := D.three_le_n; omega

@[expose] noncomputable def cls (V : Subgroup G) : ZMod 2 :=
  fourClass D.B₀_iso.some D.one_le_n_sub_one V

theorem cls_eq_iff {V V' : Subgroup G} (hV : IsFourIn D.B₀ V) (hV' : IsFourIn D.B₀ V') :
    D.cls V = D.cls V' ↔ ∃ h ∈ D.B₀, V.map (MulAut.conj h).toMonoidHom = V' :=
  (exists_conj_four_iff D.B₀_iso.some D.one_le_n_sub_one D.two_le_n_sub_one hV hV').symm

theorem cls_map_conj {V : Subgroup G} (hV : IsFourIn D.B₀ V) {h : G} (hh : h ∈ D.B₀) :
    D.cls (V.map (MulAut.conj h).toMonoidHom) = D.cls V :=
  fourClass_map_conj D.B₀_iso.some D.one_le_n_sub_one D.two_le_n_sub_one hV hh

@[expose] noncomputable def repW (i : ZMod 2) : Subgroup G :=
  liftSub D.B₀_iso.some (dihFour (n - 1) (if i = 0 then 0 else 1))

theorem isFourIn_repW (i : ZMod 2) : IsFourIn D.B₀ (D.repW i) :=
  isFourIn_liftSub_dihFour _ D.one_le_n_sub_one _

theorem cls_repW (i : ZMod 2) : D.cls (D.repW i) = i := by
  rw [cls, repW, fourClass_liftSub _ _ D.two_le_n_sub_one]
  have h01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  rcases h01 i with rfl | rfl
  · rw [if_pos rfl, map_zero]
  · rw [if_neg (by decide), map_one]

theorem cls_sConj_map_conj {V : Subgroup G} (hV : IsFourIn D.B₁ V) {h : G} (hh : h ∈ D.B₁) :
    D.cls (D.sConj (V.map (MulAut.conj h).toMonoidHom)) = D.cls (D.sConj V) := by
  have e : D.sConj (V.map (MulAut.conj h).toMonoidHom) =
      (D.sConj V).map (MulAut.conj (D.s * h * D.s⁻¹)).toMonoidHom := by
    rw [sConj, sConj, map_conj_map_conj, map_conj_map_conj,
      show D.s * h * D.s⁻¹ * D.s = D.s * h by group]
  rw [e, D.cls_map_conj (D.isFourIn_sConj₁ hV) (D.conj_s_mem_B₀ hh)]

@[expose] noncomputable def repU : Subgroup G := liftSub D.eAt (dihFour m (D.jt + 1))

theorem zpar_jt_add_one_sub : zpar m D.one_le_m (D.jt + 1 - D.jt) = 1 := by
  rw [add_sub_cancel_left, map_one]

theorem isFourIn_repU : IsFourIn D.A D.repU := by
  obtain ⟨-, h2, h4⟩ := isFourIn_liftSub_dihFour D.eAt D.one_le_m (D.jt + 1)
  refine ⟨fun x hx => ?_, h2, h4⟩
  obtain ⟨hxAt, hxV⟩ := (mem_liftSub D.eAt).1 hx
  have hmem := (D.mem_A_iff_eAt ⟨x, hxAt⟩).2
  rw [mem_dihFour D.one_le_m] at hxV
  rcases hxV with h | h | h | h
  · have : (⟨x, hxAt⟩ : ↥(D.A ⊔ zpowers D.t)) = 1 := D.eAt.injective (h.trans D.eAt.map_one.symm)
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1]
    exact one_mem _
  · have : (⟨x, hxAt⟩ : ↥(D.A ⊔ zpowers D.t)) = ⟨D.a, mem_sup_left D.a_mem⟩ :=
      D.eAt.injective (h.trans D.eAt_a.symm)
    have hx1 : x = D.a := congrArg Subtype.val this
    rw [hx1]
    exact D.a_mem
  · exact hmem (Or.inr ⟨_, h, D.zpar_jt_add_one_sub⟩)
  · refine hmem (Or.inr ⟨D.jt + 1 + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), ?_, ?_⟩)
    · rw [h, zc_eq_r D.one_le_m, sr_mul_r]
    · rw [show D.jt + 1 + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) - D.jt =
          1 + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) by ring, map_add, map_one,
        zpar_half D.one_le_m D.two_le_m, add_zero]

theorem repU_eq_A (hm : m = 2) : D.repU = D.A := by
  haveI := D.finite_A
  exact eq_of_le_of_card_ge D.isFourIn_repU.1 (by simp [D.isFourIn_repU.2.2, D.card_A, hm])

@[expose] noncomputable def Frep (i j : ZMod 2) : Subgroup G :=
  D.repU ⊔ (D.repW i ⊔ D.sConj (D.repW j))

theorem isE64_of_four {V V₀ V₁ : Subgroup G} (hV : IsFourIn D.A V) (hV₀ : IsFourIn D.B₀ V₀)
    (hV₁ : IsFourIn D.B₁ V₁) : IsE64 T (V ⊔ (V₀ ⊔ V₁)) := by
  obtain ⟨hle, hsq, hcard⟩ := D.elem64_of_four hV.1 hV₀.1 hV₁.1 hV.2.1 hV₀.2.1 hV₁.2.1 hV.2.2
    hV₀.2.2 hV₁.2.2
  exact ⟨hle.trans D.T₁_le_T, isElemAbelian_two_iff.2 hsq, hcard⟩

theorem isE64_Frep (i j : ZMod 2) : IsE64 T (D.Frep i j) :=
  D.isE64_of_four D.isFourIn_repU (D.isFourIn_repW i) (D.isFourIn_sConj₀ (D.isFourIn_repW j))

theorem inf_of_four {V V₀ V₁ : Subgroup G} (hV : IsFourIn D.A V) (hV₀ : IsFourIn D.B₀ V₀)
    (hV₁ : IsFourIn D.B₁ V₁) :
    (V ⊔ (V₀ ⊔ V₁)) ⊓ D.A = V ∧ (V ⊔ (V₀ ⊔ V₁)) ⊓ D.B₀ = V₀ ∧ (V ⊔ (V₀ ⊔ V₁)) ⊓ D.B₁ = V₁ := by
  have hE := D.isE64_of_four hV hV₀ hV₁
  obtain ⟨-, hA, hB₀, hB₁⟩ := D.E64_decomp hE
  haveI := hA.finite
  haveI := hB₀.finite
  haveI := hB₁.finite
  exact ⟨(eq_of_le_of_card_ge (le_inf le_sup_left hV.1) (hA.2.2.trans hV.2.2.symm).le).symm,
    (eq_of_le_of_card_ge (le_inf (le_sup_left.trans le_sup_right) hV₀.1)
      (hB₀.2.2.trans hV₀.2.2.symm).le).symm,
    (eq_of_le_of_card_ge (le_inf (le_sup_right.trans le_sup_right) hV₁.1)
      (hB₁.2.2.trans hV₁.2.2.symm).le).symm⟩

theorem Frep_inf_A (i j : ZMod 2) : D.Frep i j ⊓ D.A = D.repU :=
  (D.inf_of_four D.isFourIn_repU (D.isFourIn_repW i) (D.isFourIn_sConj₀ (D.isFourIn_repW j))).1

theorem Frep_inf_B₀ (i j : ZMod 2) : D.Frep i j ⊓ D.B₀ = D.repW i :=
  (D.inf_of_four D.isFourIn_repU (D.isFourIn_repW i) (D.isFourIn_sConj₀ (D.isFourIn_repW j))).2.1

theorem Frep_inf_B₁ (i j : ZMod 2) : D.Frep i j ⊓ D.B₁ = D.sConj (D.repW j) :=
  (D.inf_of_four D.isFourIn_repU (D.isFourIn_repW i) (D.isFourIn_sConj₀ (D.isFourIn_repW j))).2.2

theorem conj_mul_of_mem_A {α w₀ w₁ v : G} (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hv : v ∈ D.A) : α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = α * v * α⁻¹ := by
  have h : (w₀ * w₁) * v = v * (w₀ * w₁) :=
    (D.A_comm_B₀B₁ v hv _ (mul_mem (mem_sup_left hw₀) (mem_sup_right hw₁))).symm
  calc α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = α * ((w₀ * w₁) * v) * (w₀ * w₁)⁻¹ * α⁻¹ := by
        group
    _ = α * v * α⁻¹ := by rw [h]; group

theorem conj_mul_of_mem_B₀ {α w₀ w₁ v : G} (hα : α ∈ D.A) (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hv : v ∈ D.B₀) : α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = w₀ * v * w₀⁻¹ := by
  have h1 : w₁ * v = v * w₁ := (D.B₀_comm_B₁ v hv w₁ hw₁).symm
  have h2 : α * (w₀ * v * w₀⁻¹) = (w₀ * v * w₀⁻¹) * α :=
    D.A_comm_B α hα _ (D.B₀_le_B (mul_mem (mul_mem hw₀ hv) (inv_mem hw₀)))
  calc α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = α * w₀ * (w₁ * v) * w₁⁻¹ * w₀⁻¹ * α⁻¹ := by
        group
    _ = α * (w₀ * v * w₀⁻¹) * α⁻¹ := by rw [h1]; group
    _ = w₀ * v * w₀⁻¹ := by rw [h2, mul_inv_cancel_right]

theorem conj_mul_of_mem_B₁ {α w₀ w₁ v : G} (hα : α ∈ D.A) (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hv : v ∈ D.B₁) : α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = w₁ * v * w₁⁻¹ := by
  have h1 : w₀ * (w₁ * v * w₁⁻¹) = (w₁ * v * w₁⁻¹) * w₀ :=
    D.B₀_comm_B₁ w₀ hw₀ _ (mul_mem (mul_mem hw₁ hv) (inv_mem hw₁))
  have h2 : α * (w₁ * v * w₁⁻¹) = (w₁ * v * w₁⁻¹) * α :=
    D.A_comm_B α hα _ (D.B₁_le_B (mul_mem (mul_mem hw₁ hv) (inv_mem hw₁)))
  calc α * (w₀ * w₁) * v * (α * (w₀ * w₁))⁻¹ = α * (w₀ * (w₁ * v * w₁⁻¹)) * w₀⁻¹ * α⁻¹ := by
        group
    _ = α * (w₁ * v * w₁⁻¹) * α⁻¹ := by rw [h1]; group
    _ = w₁ * v * w₁⁻¹ := by rw [h2, mul_inv_cancel_right]

theorem exists_B₀_conj_of_mem_T₁ {y : G} (hy : y ∈ D.T₁) :
    ∃ w₀ ∈ D.B₀, ∃ w₁ ∈ D.B₁, (∀ v ∈ D.B₀, y * v * y⁻¹ = w₀ * v * w₀⁻¹) ∧
      ∀ v ∈ D.B₁, y * v * y⁻¹ = w₁ * v * w₁⁻¹ := by
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hy
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  exact ⟨w₀, hw₀, w₁, hw₁, fun v hv => D.conj_mul_of_mem_B₀ hα hw₀ hw₁ hv,
    fun v hv => D.conj_mul_of_mem_B₁ hα hw₀ hw₁ hv⟩

theorem B₀_normal_T₁ {y : G} (hy : y ∈ D.T₁) : ∀ v ∈ D.B₀, y * v * y⁻¹ ∈ D.B₀ := by
  intro v hv
  obtain ⟨w₀, hw₀, -, -, h₀, -⟩ := D.exists_B₀_conj_of_mem_T₁ hy
  rw [h₀ v hv]
  exact mul_mem (mul_mem hw₀ hv) (inv_mem hw₀)

theorem B₁_normal_T₁ {y : G} (hy : y ∈ D.T₁) : ∀ v ∈ D.B₁, y * v * y⁻¹ ∈ D.B₁ := by
  intro v hv
  obtain ⟨-, -, w₁, hw₁, -, h₁⟩ := D.exists_B₀_conj_of_mem_T₁ hy
  rw [h₁ v hv]
  exact mul_mem (mul_mem hw₁ hv) (inv_mem hw₁)

theorem A_normal_T {y : G} (hy : y ∈ T) : ∀ v ∈ D.A, y * v * y⁻¹ ∈ D.A :=
  fun v hv => (mem_normalizer_iff.1 (D.T_le_normalizer_A hy) v).1 hv

@[expose] noncomputable def typ (X : Subgroup G) : ZMod 2 × ZMod 2 :=
  (D.cls (X ⊓ D.B₀), D.cls (D.sConj (X ⊓ D.B₁)))

theorem typ_Frep (i j : ZMod 2) : D.typ (D.Frep i j) = (i, j) := by
  rw [typ, Frep_inf_B₀, Frep_inf_B₁, sConj_sConj, cls_repW, cls_repW]

theorem typ_map_conj_T₁ {X : Subgroup G} (h₀ : IsFourIn D.B₀ (X ⊓ D.B₀))
    (h₁ : IsFourIn D.B₁ (X ⊓ D.B₁)) {y : G} (hy : y ∈ D.T₁) :
    D.typ (X.map (MulAut.conj y).toMonoidHom) = D.typ X := by
  obtain ⟨w₀, hw₀, w₁, hw₁, hc₀, hc₁⟩ := D.exists_B₀_conj_of_mem_T₁ hy
  have hy' : y⁻¹ ∈ D.T₁ := inv_mem hy
  have e₀ : X.map (MulAut.conj y).toMonoidHom ⊓ D.B₀ =
      (X ⊓ D.B₀).map (MulAut.conj w₀).toMonoidHom := by
    rw [inf_map_conj (D.B₀_normal_T₁ hy) (fun v hv => by simpa using D.B₀_normal_T₁ hy' v hv)]
    exact map_conj_eq_of_agree fun v hv => hc₀ v (mem_inf.1 hv).2
  have e₁ : X.map (MulAut.conj y).toMonoidHom ⊓ D.B₁ =
      (X ⊓ D.B₁).map (MulAut.conj w₁).toMonoidHom := by
    rw [inf_map_conj (D.B₁_normal_T₁ hy) (fun v hv => by simpa using D.B₁_normal_T₁ hy' v hv)]
    exact map_conj_eq_of_agree fun v hv => hc₁ v (mem_inf.1 hv).2
  rw [typ, typ, e₀, e₁, D.cls_map_conj h₀ hw₀, D.cls_sConj_map_conj h₁ hw₁]

theorem typ_map_conj_s (X : Subgroup G) :
    D.typ (X.map (MulAut.conj D.s).toMonoidHom) = (D.typ X).swap := by
  have e₀ : X.map (MulAut.conj D.s).toMonoidHom ⊓ D.B₀ = D.sConj (X ⊓ D.B₁) := by
    rw [sConj, map_conj_inf]
    congr 1
    exact D.sConj_B₁.symm
  have e₁ : X.map (MulAut.conj D.s).toMonoidHom ⊓ D.B₁ = D.sConj (X ⊓ D.B₀) := by
    rw [sConj, map_conj_inf, D.conj_s_B₀]
  simp only [typ, e₀, e₁, sConj_sConj, Prod.swap_prod_mk]

theorem exists_conj_parts_of_typ_eq {X X' : Subgroup G} (h₀ : IsFourIn D.B₀ (X ⊓ D.B₀))
    (h₁ : IsFourIn D.B₁ (X ⊓ D.B₁)) (h₀' : IsFourIn D.B₀ (X' ⊓ D.B₀))
    (h₁' : IsFourIn D.B₁ (X' ⊓ D.B₁)) (h : D.typ X = D.typ X') :
    ∃ β₀ ∈ D.B₀, ∃ β₁ ∈ D.B₁, (X ⊓ D.B₀).map (MulAut.conj β₀).toMonoidHom = X' ⊓ D.B₀ ∧
      (X ⊓ D.B₁).map (MulAut.conj β₁).toMonoidHom = X' ⊓ D.B₁ := by
  rw [typ, typ, Prod.mk.injEq] at h
  obtain ⟨hc₀, hc₁⟩ := h
  obtain ⟨β₀, hβ₀, e₀⟩ := (D.cls_eq_iff h₀ h₀').1 hc₀
  obtain ⟨γ, hγ, e₁⟩ := (D.cls_eq_iff (D.isFourIn_sConj₁ h₁) (D.isFourIn_sConj₁ h₁')).1 hc₁
  refine ⟨β₀, hβ₀, D.s * γ * D.s, ?_, e₀, ?_⟩
  · have := D.conj_s_mem_B₁ hγ
    rwa [D.s_inv] at this
  · have h2 := congrArg D.sConj e₁
    rw [D.sConj_sConj] at h2
    rw [← h2]
    ext x
    simp only [sConj, mem_map_conj, mul_inv_rev, D.s_inv, mul_assoc]

theorem exists_conj_of_typ_eq {E E' : Subgroup G} (hE : IsE64 T E) (hE' : IsE64 T E')
    (hA : E ⊓ D.A = E' ⊓ D.A) (h : D.typ E = D.typ E') :
    ∃ β ∈ D.B₀ ⊔ D.B₁, E.map (MulAut.conj β).toMonoidHom = E' := by
  obtain ⟨hdec, -, hB₀, hB₁⟩ := D.E64_decomp hE
  obtain ⟨hdec', -, hB₀', hB₁'⟩ := D.E64_decomp hE'
  obtain ⟨β₀, hβ₀, β₁, hβ₁, e₀, e₁⟩ := D.exists_conj_parts_of_typ_eq hB₀ hB₁ hB₀' hB₁' h
  have hβ : β₀ * β₁ ∈ D.B₀ ⊔ D.B₁ := mul_mem (mem_sup_left hβ₀) (mem_sup_right hβ₁)
  refine ⟨β₀ * β₁, hβ, ?_⟩
  have eA : (E ⊓ D.A).map (MulAut.conj (β₀ * β₁)).toMonoidHom = E' ⊓ D.A := by
    rw [map_conj_eq_self_of_comm (X := E ⊓ D.A)
      fun x hx => (D.A_comm_B₀B₁ x (mem_inf.1 hx).2 _ hβ).symm, hA]
  have eB₀ : (E ⊓ D.B₀).map (MulAut.conj (β₀ * β₁)).toMonoidHom = E' ⊓ D.B₀ := by
    rw [← e₀]
    refine map_conj_eq_of_agree fun v hv => ?_
    have := D.conj_mul_of_mem_B₀ (one_mem D.A) hβ₀ hβ₁ (mem_inf.1 hv).2
    rwa [one_mul] at this
  have eB₁ : (E ⊓ D.B₁).map (MulAut.conj (β₀ * β₁)).toMonoidHom = E' ⊓ D.B₁ := by
    rw [← e₁]
    refine map_conj_eq_of_agree fun v hv => ?_
    have := D.conj_mul_of_mem_B₁ (one_mem D.A) hβ₀ hβ₁ (mem_inf.1 hv).2
    rwa [one_mul] at this
  conv_lhs => rw [hdec]
  conv_rhs => rw [hdec']
  rw [Subgroup.map_sup, Subgroup.map_sup, eA, eB₀, eB₁]

end FooteCore

end CFSG.CGT.Foote81L6
