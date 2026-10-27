module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Mod
public import CFSG.LocalAnalysis.OddStandard.Seitz77UElem

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
open scoped commutatorElement

section Diag

variable {G : Type} [Group G]

structure SwapPair (A B : Subgroup G) (t : G) : Prop where
  t_sq : t * t = 1
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  inf_eq : A ⊓ B = ⊥
  swap₁ : ∀ x ∈ A, t * x * t⁻¹ ∈ B
  swap₂ : ∀ x ∈ B, t * x * t⁻¹ ∈ A

namespace SwapPair

variable {A B : Subgroup G} {t : G} (P : SwapPair A B t)

include P

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right P.t_sq

theorem conj_conj (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have ht := P.t_inv
  rw [ht]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [P.t_sq]; group

theorem unique {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, by
    rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)⟩
  rw [P.inf_eq, Subgroup.mem_bot] at hmem
  have hae : a = a' := (inv_mul_eq_one.mp hmem).symm
  refine ⟨hae, ?_⟩
  rw [hae] at h
  exact mul_left_cancel h

theorem cs_le {X : Subgroup G} (hX : X ≤ A) : cs t X ≤ B := by
  intro y hy
  rw [mem_cs] at hy
  have h1 := P.swap₁ _ (hX hy)
  have h2 : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
  rwa [h2] at h1

theorem comm_X_cs {X : Subgroup G} (hX : X ≤ A) {x y : G} (hx : x ∈ X) (hy : y ∈ cs t X) :
    x * y = y * x :=
  P.comm x (hX hx) y (P.cs_le hX hy)

theorem inf_X_cs {X : Subgroup G} (hX : X ≤ A) : X ⊓ cs t X = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  have : g ∈ A ⊓ B := ⟨hX hg.1, P.cs_le hX hg.2⟩
  rwa [P.inf_eq] at this

theorem mem_sup_cs {X : Subgroup G} (hX : X ≤ A) {g : G} :
    g ∈ X ⊔ cs t X ↔ ∃ x ∈ X, ∃ y ∈ X, g = x * (t * y * t⁻¹) := by
  constructor
  · intro hg
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_sup_of_forall_comm (fun x hx y hy => P.comm_X_cs hX hx hy) hg
    rw [mem_cs] at hz
    refine ⟨x, hx, t⁻¹ * z * t, hz, ?_⟩
    have : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
    rw [this]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_cs_iff.mpr hy))

omit P in
theorem isElemAbelian_cs {X : Subgroup G} (hX : IsElemAbelian 2 X) (g : G) :
    IsElemAbelian 2 (cs g X) := by
  refine isElemAbelian_of_forall_two (fun y hy y' hy' => ?_) (fun y hy => ?_)
  · rw [mem_cs] at hy hy'
    have h := comm_of_isElemAbelian_two hX hy hy'
    calc y * y' = g * ((g⁻¹ * y * g) * (g⁻¹ * y' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y' * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = y' * y := by group
  · rw [mem_cs] at hy
    have h := mul_self_of_isElemAbelian_two hX hy
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [h]; group

omit P in
theorem isElemAbelian_sup_of_comm {X Y : Subgroup G} (hX : IsElemAbelian 2 X)
    (hY : IsElemAbelian 2 Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    IsElemAbelian 2 (X ⊔ Y) := CFSG.Open.IsElemAbelian.sup_of_commute hX hY hc

theorem card_sup_cs {X : Subgroup G} (hX : X ≤ A) :
    Nat.card ↥(X ⊔ cs t X) = Nat.card ↥X * Nat.card ↥X := by
  have e := supEquivProd X (cs t X) (fun x hx y hy => P.comm_X_cs hX hx hy)
    (disjoint_iff.mpr (P.inf_X_cs hX))
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, nat_card_cs]

theorem diag_comm_t {a : G} (ha : a ∈ A) : a * (t * a * t⁻¹) * t = t * (a * (t * a * t⁻¹)) := by
  have hc : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := P.comm a ha _ (P.swap₁ a ha)
  have ht := P.t_inv
  calc a * (t * a * t⁻¹) * t = (t * a * t⁻¹) * a * t := by rw [hc]
    _ = t * (a * (t * a * t⁻¹)) := by rw [ht]; group

theorem comm_diag {X : Subgroup G} (hXA : X ≤ A) (hX : IsElemAbelian 2 X) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) :
    ⁅x * (t * y * t⁻¹), t⁆ = (x * y⁻¹) * (t * (x * y⁻¹) * t⁻¹) := by
  have hx2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (mul_self_of_isElemAbelian_two hX hx)
  have hy2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (mul_self_of_isElemAbelian_two hX hy)
  have hxy : x * y = y * x := comm_of_isElemAbelian_two hX hx hy
  have hc : y * x⁻¹ = x * y⁻¹ := by rw [hx2, hy2, hxy]
  have key : ∀ z : G, t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := fun z => by group
  have e1 : t * (t * y * t⁻¹)⁻¹ * t⁻¹ = y⁻¹ := by
    rw [key, P.conj_conj]
  have hcomm : (t * y * t⁻¹) * y⁻¹ = y⁻¹ * (t * y * t⁻¹) :=
    (P.comm y⁻¹ (hXA (X.inv_mem hy)) _ (P.swap₁ y (hXA hy))).symm
  calc ⁅x * (t * y * t⁻¹), t⁆
      = x * (t * y * t⁻¹) * (t * (t * y * t⁻¹)⁻¹ * t⁻¹) * (t * x⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]; group
    _ = x * ((t * y * t⁻¹) * y⁻¹) * (t * x⁻¹ * t⁻¹) := by rw [e1]; group
    _ = x * (y⁻¹ * (t * y * t⁻¹)) * (t * x⁻¹ * t⁻¹) := by rw [hcomm]
    _ = (x * y⁻¹) * (t * (y * x⁻¹) * t⁻¹) := by group
    _ = (x * y⁻¹) * (t * (x * y⁻¹) * t⁻¹) := by rw [hc]

theorem diag_facts {X R : Subgroup G} (hXA : X ≤ A) (hX : IsElemAbelian 2 X)
    (hR : ∀ v, v ∈ R ↔ ∃ a ∈ X, v = a * (t * a * t⁻¹)) :
    IsElemAbelian 2 (X ⊔ cs t X) ∧ Nat.card ↥(X ⊔ cs t X) = Nat.card ↥X * Nat.card ↥X ∧
      R ≤ X ⊔ cs t X ∧ X ⊔ cs t X ≤ centralizer (R : Set G) ∧
      (X ⊔ cs t X) ⊓ centralizer ({t} : Set G) = R ∧ ⁅X ⊔ cs t X, zpowers t⁆ = R := by
  have hD : IsElemAbelian 2 (X ⊔ cs t X) :=
    isElemAbelian_sup_of_comm hX (isElemAbelian_cs hX t) fun x hx y hy => P.comm_X_cs hXA hx hy
  have hRD : R ≤ X ⊔ cs t X := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (hR v).mp hv
    exact (P.mem_sup_cs hXA).mpr ⟨a, ha, a, ha, rfl⟩
  have ht := P.t_inv
  refine ⟨hD, P.card_sup_cs hXA, hRD, ?_, ?_, ?_⟩
  · intro g hg
    rw [mem_centralizer_iff]
    intro v hv
    exact (comm_of_isElemAbelian_two hD hg (hRD hv)).symm
  · refine le_antisymm ?_ (le_inf hRD ?_)
    · rintro g ⟨hgD, hgt⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (P.mem_sup_cs hXA).mp hgD
      have hgt' : t * (x * (t * y * t⁻¹)) * t⁻¹ = x * (t * y * t⁻¹) := by
        have := mem_centralizer_singleton_iff.mp hgt
        calc t * (x * (t * y * t⁻¹)) * t⁻¹ = (x * (t * y * t⁻¹) * t) * t⁻¹ := by rw [this]
          _ = x * (t * y * t⁻¹) := by group
      have h2 : t * (x * (t * y * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * y := by
        calc t * (x * (t * y * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹) := by group
          _ = (t * x * t⁻¹) * y := by rw [P.conj_conj]
      have h3 : (t * x * t⁻¹) * y = y * (t * x * t⁻¹) :=
        (P.comm y (hXA hy) _ (P.swap₁ x (hXA hx))).symm
      have h4 : x * (t * y * t⁻¹) = y * (t * x * t⁻¹) := by rw [← h3, ← h2, hgt']
      obtain ⟨hxy, -⟩ := P.unique (hXA hx) (hXA hy) (P.swap₁ y (hXA hy)) (P.swap₁ x (hXA hx)) h4
      rw [hR]
      exact ⟨x, hx, by rw [hxy]⟩
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := (hR v).mp hv
      exact mem_centralizer_singleton_iff.mpr (P.diag_comm_t (hXA ha))
  · refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro d hd s hs
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hpow : t ^ n = 1 ∨ t ^ n = t := by
        have h2 : t ^ (2 : ℤ) = 1 := (zpow_two t).trans P.t_sq
        obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
        · left
          rw [zpow_mul, h2, one_zpow]
        · right
          rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
      rcases hpow with h | h
      · rw [h]
        simp only [commutatorElement_one_right]
        exact R.one_mem
      · rw [h]
        obtain ⟨x, hx, y, hy, rfl⟩ := (P.mem_sup_cs hXA).mp hd
        rw [hR]
        exact ⟨x * y⁻¹, X.mul_mem hx (X.inv_mem hy), (P.comm_diag hXA hX hx hy)⟩
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := (hR v).mp hv
      have ha2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (mul_self_of_isElemAbelian_two hX ha)
      have e : a * (t * a * t⁻¹) = ⁅a, t⁆ := by
        rw [commutatorElement_def, ha2]
        group
      rw [e]
      exact commutator_mem_commutator ((P.mem_sup_cs hXA).mpr ⟨a, ha, 1, X.one_mem, by
        simp⟩) (mem_zpowers t)

end SwapPair

end Diag

end CFSG.OddStandard.Seitz77
