module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.AGLEmbedding.RankRefinedAux

public section

namespace CFSG.AGLEmbedding

section Action

variable {Γ : Type} [Group Γ]

theorem forall_conj_inv_eq {L : Subgroup Γ} {w x : Γ}
    (hx : x ∈ Subgroup.normalizer (L : Set Γ)) (h : ∀ y ∈ L, w * y * w⁻¹ = x * y * x⁻¹) :
    ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x := by
  intro y hy
  have hy' : x⁻¹ * y * x ∈ L := (Subgroup.mem_normalizer_iff''.mp hx y).mp hy
  have h1 := h _ hy'
  rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h1
  calc w⁻¹ * y * w = w⁻¹ * (w * (x⁻¹ * y * x) * w⁻¹) * w := by rw [h1]
    _ = x⁻¹ * y * x := by group

theorem forall_conj_pow_eq {L : Subgroup Γ} {w x : Γ}
    (hx : x ∈ Subgroup.normalizer (L : Set Γ)) (h : ∀ y ∈ L, w * y * w⁻¹ = x * y * x⁻¹)
    (n : ℕ) : ∀ y ∈ L, w ^ n * y * (w ^ n)⁻¹ = x ^ n * y * (x ^ n)⁻¹ := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hyn : x ^ n * y * (x ^ n)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hx n) y).mp hy
    calc w ^ (n + 1) * y * (w ^ (n + 1))⁻¹ = w * (w ^ n * y * (w ^ n)⁻¹) * w⁻¹ := by
          rw [pow_succ']; group
      _ = w * (x ^ n * y * (x ^ n)⁻¹) * w⁻¹ := by rw [ih y hy]
      _ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := h _ hyn
      _ = x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ := by rw [pow_succ']; group

theorem forall_conj_commutator_eq {L : Subgroup Γ} {w w' x x' : Γ}
    (hx : x ∈ Subgroup.normalizer (L : Set Γ)) (hx' : x' ∈ Subgroup.normalizer (L : Set Γ))
    (h : ∀ y ∈ L, w * y * w⁻¹ = x * y * x⁻¹) (h' : ∀ y ∈ L, w' * y * w'⁻¹ = x' * y * x'⁻¹) :
    ∀ y ∈ L, (w * w' * w⁻¹ * w'⁻¹) * y * (w * w' * w⁻¹ * w'⁻¹)⁻¹ =
      (x * x' * x⁻¹ * x'⁻¹) * y * (x * x' * x⁻¹ * x'⁻¹)⁻¹ := by
  intro y hy
  have hconj : ∀ g ∈ Subgroup.normalizer (L : Set Γ), ∀ y ∈ L, g * y * g⁻¹ ∈ L :=
    fun g hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hconj' : ∀ g ∈ Subgroup.normalizer (L : Set Γ), ∀ y ∈ L, g⁻¹ * y * g ∈ L :=
    fun g hg y hy => (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  set y₁ := x'⁻¹ * y * x' with hy₁
  have h₁ : w'⁻¹ * y * w' = y₁ := forall_conj_inv_eq hx' h' y hy
  have hy₁L : y₁ ∈ L := hconj' x' hx' y hy
  set y₂ := x⁻¹ * y₁ * x with hy₂
  have h₂ : w⁻¹ * y₁ * w = y₂ := forall_conj_inv_eq hx h y₁ hy₁L
  have hy₂L : y₂ ∈ L := hconj' x hx y₁ hy₁L
  set y₃ := x' * y₂ * x'⁻¹ with hy₃
  have h₃ : w' * y₂ * w'⁻¹ = y₃ := h' y₂ hy₂L
  have hy₃L : y₃ ∈ L := hconj x' hx' y₂ hy₂L
  calc (w * w' * w⁻¹ * w'⁻¹) * y * (w * w' * w⁻¹ * w'⁻¹)⁻¹
      = w * (w' * (w⁻¹ * (w'⁻¹ * y * w') * w) * w'⁻¹) * w⁻¹ := by group
    _ = w * y₃ * w⁻¹ := by rw [h₁, h₂, h₃]
    _ = x * y₃ * x⁻¹ := h y₃ hy₃L
    _ = (x * x' * x⁻¹ * x'⁻¹) * y * (x * x' * x⁻¹ * x'⁻¹)⁻¹ := by
        rw [hy₃, hy₂, hy₁]; group

theorem mem_centralizer_of_forall_conj_eq_self {L : Subgroup Γ} {g : Γ}
    (h : ∀ y ∈ L, g * y * g⁻¹ = y) : g ∈ Subgroup.centralizer (L : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := h y hy
  calc y * g = g * y * g⁻¹ * g := by rw [h1]
    _ = g * y := by group

theorem sup_centralizer_self_le_normalizer (L : Subgroup Γ) :
    L ⊔ Subgroup.centralizer (L : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)

theorem sup_centralizer_self_le_normalizer_centralizer (L : Subgroup Γ) :
    L ⊔ Subgroup.centralizer (L : Set Γ) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Γ) : Set Γ) := by
  have hNC : Subgroup.normalizer (L : Set Γ) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Γ) : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  exact sup_le (Subgroup.le_normalizer.trans hNC) Subgroup.le_normalizer

theorem exists_forall_conj_eq_of_mem_sup {L X : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Γ) : Set Γ)) {w : Γ}
    (hw : w ∈ X ⊔ Subgroup.centralizer (L : Set Γ)) :
    ∃ x ∈ X, ∀ y ∈ L, w * y * w⁻¹ = x * y * x⁻¹ := by
  have hw' : w ∈ ((X ⊔ Subgroup.centralizer (L : Set Γ) : Subgroup Γ) : Set Γ) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _ hX] at hw'
  obtain ⟨x, hx, c, hc, rfl⟩ := hw'
  refine ⟨x, hx, fun y hy => ?_⟩
  have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc y hy
  calc x * c * y * (x * c)⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ := by group
    _ = x * (y * c) * c⁻¹ * x⁻¹ := by rw [hcy]
    _ = x * y * x⁻¹ := by group

theorem pow_mem_centralizer_of_mem_sup {L X : Subgroup Γ} {p : ℕ}
    (hXL : X ≤ L ⊔ Subgroup.centralizer (L : Set Γ)) (hXp : ∀ x ∈ X, x ^ p = 1) {w : Γ}
    (hw : w ∈ X ⊔ Subgroup.centralizer (L : Set Γ)) :
    w ^ p ∈ Subgroup.centralizer (L : Set Γ) := by
  obtain ⟨x, hx, hwx⟩ := exists_forall_conj_eq_of_mem_sup
    (hXL.trans (sup_centralizer_self_le_normalizer_centralizer L)) hw
  have hxN := hXL.trans (sup_centralizer_self_le_normalizer L) hx
  refine mem_centralizer_of_forall_conj_eq_self fun y hy => ?_
  rw [forall_conj_pow_eq hxN hwx p y hy, hXp x hx]
  group

theorem commutator_mem_centralizer_of_mem_sup {L X : Subgroup Γ}
    (hXL : X ≤ L ⊔ Subgroup.centralizer (L : Set Γ)) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    {w w' : Γ} (hw : w ∈ X ⊔ Subgroup.centralizer (L : Set Γ))
    (hw' : w' ∈ X ⊔ Subgroup.centralizer (L : Set Γ)) :
    w * w' * w⁻¹ * w'⁻¹ ∈ Subgroup.centralizer (L : Set Γ) := by
  have hXC := hXL.trans (sup_centralizer_self_le_normalizer_centralizer L)
  obtain ⟨x, hx, hwx⟩ := exists_forall_conj_eq_of_mem_sup hXC hw
  obtain ⟨x', hx', hwx'⟩ := exists_forall_conj_eq_of_mem_sup hXC hw'
  have hxN := hXL.trans (sup_centralizer_self_le_normalizer L)
  refine mem_centralizer_of_forall_conj_eq_self fun y hy => ?_
  rw [forall_conj_commutator_eq (hxN hx) (hxN hx') hwx hwx' y hy, hXab x hx x' hx']
  group

theorem relIndex_sup_right_eq_of_le_normalizer {X C : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (C : Set Γ)) : C.relIndex (X ⊔ C) = C.relIndex X := by
  set N := Subgroup.normalizer (C : Set Γ)
  have hCN : C ≤ N := Subgroup.le_normalizer
  have : (C.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := Subgroup.relIndex_sup_right (X.subgroupOf N) (C.subgroupOf N)
  rwa [← Subgroup.subgroupOf_sup hX hCN, Subgroup.relIndex_subgroupOf (sup_le hX hCN),
    Subgroup.relIndex_subgroupOf hX] at h

end Action

section Sylow

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_isPGroup_pow_le_relIndex {p : ℕ} [hp : Fact p.Prime] {V C : Subgroup Γ} {a : ℕ}
    (h : C.relIndex V = p ^ a) : ∃ B : Subgroup Γ, B ≤ V ∧ IsPGroup p B ∧ p ^ a ≤ C.relIndex B := by
  obtain ⟨T⟩ : Nonempty (Sylow p ↥V) := inferInstance
  set B : Subgroup Γ := (T : Subgroup ↥V).map V.subtype with hB
  have hBV : B ≤ V := Subgroup.map_subtype_le _
  have hBp : IsPGroup p B := T.isPGroup'.map _
  refine ⟨B, hBV, hBp, ?_⟩
  set v := (Nat.card (C ⊓ V : Subgroup Γ)).factorization p with hv
  have hV : C.relIndex V * Nat.card (C ⊓ V : Subgroup Γ) = Nat.card V :=
    Subgroup.relIndex_mul_card C V
  have hfac : (Nat.card V).factorization p = a + v := by
    rw [← hV, h, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same]
  have hBcard : Nat.card B = p ^ (a + v) := by
    rw [hB, Subgroup.card_map_of_injective V.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (hBp.to_le (inf_le_right : C ⊓ B ≤ B))
  have hcv : c ≤ v := by
    have hdvd : p ^ c ∣ Nat.card (C ⊓ V : Subgroup Γ) :=
      hc ▸ Subgroup.card_dvd_of_le (inf_le_inf_left C hBV)
    exact (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  have hB' : C.relIndex B * p ^ c = p ^ (a + v) := by
    rw [← hc, ← hBcard]
    exact Subgroup.relIndex_mul_card C B
  refine Nat.le_of_mul_le_mul_right (c := p ^ c) ?_ (pow_pos hp.out.pos c)
  rw [hB', ← pow_add]
  exact Nat.pow_le_pow_right hp.out.pos (by omega)

theorem exists_isPGroup_le_inf_sup_centralizer {p : ℕ} [Fact p.Prime] {L X : Subgroup Γ}
    (hXL : X ≤ L ⊔ Subgroup.centralizer (L : Set Γ)) (hX : IsPGroup p X) :
    ∃ B : Subgroup Γ, B ≤ L ⊓ (X ⊔ Subgroup.centralizer (L : Set Γ)) ∧ IsPGroup p B ∧
      (Subgroup.centralizer (L : Set Γ)).relIndex X ≤
        (Subgroup.centralizer (L : Set Γ)).relIndex B := by
  set C := Subgroup.centralizer (L : Set Γ) with hC
  have hLN : L ≤ Subgroup.normalizer (C : Set Γ) :=
    le_sup_left.trans (sup_centralizer_self_le_normalizer_centralizer L)
  have hXN : X ≤ Subgroup.normalizer (C : Set Γ) :=
    hXL.trans (sup_centralizer_self_le_normalizer_centralizer L)
  set V := L ⊓ (X ⊔ C) with hV
  have hVC : V ⊔ C = X ⊔ C := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) (sup_le (fun x hx => ?_) le_sup_right)
    have hx' : x ∈ ((L ⊔ C : Subgroup Γ) : Set Γ) := hXL hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C hLN] at hx'
    obtain ⟨l, hl, c, hc, rfl⟩ := hx'
    have hlW : l ∈ X ⊔ C := by
      have := (X ⊔ C).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (C.inv_mem hc))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hl, hlW⟩) (Subgroup.mem_sup_right hc)
  have hidx : C.relIndex V = C.relIndex X := by
    rw [← relIndex_sup_right_eq_of_le_normalizer (inf_le_left.trans hLN), hVC,
      relIndex_sup_right_eq_of_le_normalizer hXN]
  obtain ⟨a, ha⟩ := exists_relIndex_eq_pow_of_isPGroup (H := C) hX
  obtain ⟨B, hBV, hBp, hBidx⟩ := exists_isPGroup_pow_le_relIndex (hidx.trans ha)
  exact ⟨B, hBV, hBp, ha ▸ hBidx⟩

end Sylow

end CFSG.AGLEmbedding
