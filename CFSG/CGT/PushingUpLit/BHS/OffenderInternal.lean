module

public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.Quasithin.Background.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] noncomputable def wtG (V A : Subgroup G) : ℕ :=
  (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))

@[expose] def IsOffG (V A : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (V : Set G) ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) ∧
    (∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ a ∈ A, a ^ 2 ∈ Subgroup.centralizer (V : Set G)) ∧
    ∀ B : Subgroup G, B ≤ A → wtG V B ≤ wtG V A

theorem isElemAbelian_of_forall' {E : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h2 : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h2⟩

theorem isElemAbelian_comm' {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem isElemAbelian_mono' {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem isElemAbelian_sup' {X Y : Subgroup G} (hX : IsElemAbelian 2 X) (hY : IsElemAbelian 2 Y)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : IsElemAbelian 2 (X ⊔ Y) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hX hY hXY

section Lemma28e

variable [Finite G]

theorem isOffG_of_isMaxElemAbelian {V S A : Subgroup G} (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hSN : S ≤ Subgroup.normalizer (V : Set G)) (hA : IsMaxElemAbelian S A)
    (hne : ¬ A ≤ Subgroup.centralizer (V : Set G)) : IsOffG V A := by
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAS : A ≤ S := hA.1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => isElemAbelian_comm' hAe ha hb
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hC
  set D : Subgroup G := A ⊓ C with hD
  refine ⟨hAS.trans hSN, hne, fun a ha b hb => ?_, fun a ha => ?_, fun B hBA => ?_⟩
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (hcomm a ha b hb)]
    exact C.one_mem
  · rw [hAe.2 a ha]
    exact C.one_mem
  · have hBS : B ≤ S := hBA.trans hAS
    have hBe : IsElemAbelian 2 B := isElemAbelian_mono' hAe hBA
    have hDA : D ≤ A := inf_le_left
    have hBDA : B ⊔ D ≤ A := sup_le hBA hDA
    have hBD : ∀ x ∈ B, ∀ y ∈ D, x * y = y * x := fun x hx y hy => hcomm x (hBA hx) y hy.1
    have hcard := card_sup_mul_card_inf' hBD
    have hBC : B ⊓ C = B ⊓ D := by
      ext x
      simp only [Subgroup.mem_inf, hD]
      exact ⟨fun h => ⟨h.1, hBA h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hrB := Subgroup.relIndex_mul_card (B ⊓ C) B
    rw [inf_of_le_left inf_le_left, hBC] at hrB
    have hrA := Subgroup.relIndex_mul_card D A
    rw [inf_of_le_left hDA] at hrA
    have hpos : 0 < Nat.card ↥(B ⊓ D) := Nat.card_pos
    have hsup : Nat.card ↥(B ⊔ D) = (B ⊓ C).relIndex B * Nat.card D := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hcard, ← hrB, hBC]
      ring
    have hcentV : V ⊓ Subgroup.centralizer ((B ⊔ D : Subgroup G) : Set G) =
        V ⊓ Subgroup.centralizer (B : Set G) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hxV, hx⟩
        exact ⟨hxV, fun b hb => hx b ((le_sup_left : B ≤ B ⊔ D) hb)⟩
      · rintro ⟨hxV, hx⟩
        refine ⟨hxV, fun g hg => ?_⟩
        obtain ⟨b, hb, d, hd, rfl⟩ := exists_mul_of_mem_sup' hBD hg
        have hdx : d * x = x * d := (hd.2 x hxV).symm
        have hbx : b * x = x * b := hx b hb
        calc b * d * x = b * (d * x) := by group
          _ = b * (x * d) := by rw [hdx]
          _ = (b * x) * d := by group
          _ = (x * b) * d := by rw [hbx]
          _ = x * (b * d) := by group
    set X : Subgroup G := B ⊔ D with hX
    set Y : Subgroup G := V ⊓ Subgroup.centralizer (X : Set G) with hY
    have hXe : IsElemAbelian 2 X := isElemAbelian_mono' hAe hBDA
    have hYe : IsElemAbelian 2 Y := isElemAbelian_mono' hV inf_le_left
    have hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp hy.2 x hx
    have hEe : IsElemAbelian 2 (X ⊔ Y) := isElemAbelian_sup' hXe hYe hXY
    have hES : X ⊔ Y ≤ S := sup_le (hBDA.trans hAS) (inf_le_left.trans hVS)
    have hEA : Nat.card ↥(X ⊔ Y) ≤ Nat.card A := hA.2.2 _ hES hEe
    have hcard2 := card_sup_mul_card_inf' hXY
    have hXYle : X ⊓ Y ≤ V ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hx.2.1, Subgroup.mem_centralizer_iff.mpr fun a ha => (hcomm x (hBDA hx.1) a ha).symm⟩
    have hI : Nat.card ↥X * Nat.card ↥Y ≤
        Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [← hcard2]
      exact Nat.mul_le_mul hEA (Subgroup.card_le_of_le hXYle)
    unfold wtG
    rw [hcentV] at hI
    rw [hsup, ← hrA] at hI
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have : Nat.card D * ((B ⊓ C).relIndex B * Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G))) ≤
        Nat.card D * ((A ⊓ C).relIndex A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
      calc _ = (B ⊓ C).relIndex B * Nat.card D *
            Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) := by ring
        _ ≤ D.relIndex A * Nat.card D *
            Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hI
        _ = _ := by rw [hD]; ring
    exact Nat.le_of_mul_le_mul_left this hDpos

end Lemma28e

end CFSG.CGT.PushingUpLit.BHS
