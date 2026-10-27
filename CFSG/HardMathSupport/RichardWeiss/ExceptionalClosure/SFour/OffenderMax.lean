module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.Quasithin.H13.A7Nat1238QZ

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS

variable {G : Type} [Group G]

theorem relIndex_le_of_isMaxElemAbelian [Finite G] {S A V : Subgroup G}
    (hA : IsMaxElemAbelian S A) (hV : IsElemAbelian 2 V) (hVS : V ≤ S) :
    (Subgroup.centralizer (A : Set G)).relIndex V ≤
      (Subgroup.centralizer (V : Set G)).relIndex A := by
  classical
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCA : C ≤ A := inf_le_left
  have hCel : IsElemAbelian 2 C := isElemAbelian_mono' hA.2.1 hCA
  have hcomm : ∀ x ∈ C, ∀ v ∈ V, x * v = v * x := fun x hx v hv =>
    (Subgroup.mem_centralizer_iff.1 hx.2 v hv).symm
  have hB := isElemAbelian_sup' hCel hV hcomm
  have hcardB : Nat.card (C ⊔ V : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ (sup_le (hCA.trans hA.1) hVS) hB
  have hprod := CFSG.Quasithin.H13.A7.card_sup_mul_card_inf_of_commute (X := C) (Y := V) hcomm
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (V : Set G)) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G)) (K := V)
  rw [inf_comm] at h1
  rw [← hC] at h1
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCVle : Nat.card (C ⊓ V : Subgroup G) ≤
      Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := by
    apply Subgroup.card_le_of_le
    refine inf_le_inf ?_ le_rfl
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun a ha =>
      isElemAbelian_comm' hA.2.1 ha (hCA hx)
  set x := (Subgroup.centralizer (A : Set G)).relIndex V
  set y := (Subgroup.centralizer (V : Set G)).relIndex A
  have h3 : Nat.card C * Nat.card V ≤ y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := by
    rw [← hprod]
    calc Nat.card (C ⊔ V : Subgroup G) * Nat.card (C ⊓ V : Subgroup G)
        ≤ Nat.card A * Nat.card (C ⊓ V : Subgroup G) := Nat.mul_le_mul_right _ hcardB
      _ = y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := by rw [← h1]
  have h4 : Nat.card V ≤ y * Nat.card (C ⊓ V : Subgroup G) := by
    have : Nat.card C * Nat.card V ≤ Nat.card C * (y * Nat.card (C ⊓ V : Subgroup G)) := by
      calc Nat.card C * Nat.card V ≤ y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := h3
        _ = Nat.card C * (y * Nat.card (C ⊓ V : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left this hCpos
  have hposW : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := Nat.card_pos
  have h5 : x * Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) ≤
      y * Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := by
    rw [h2]
    exact h4.trans (Nat.mul_le_mul_left _ hCVle)
  exact Nat.le_of_mul_le_mul_right h5 hposW

theorem mem_of_commute_isMaxElemAbelian [Finite G] {S A : Subgroup G} (hA : IsMaxElemAbelian S A)
    {z : G} (hzS : z ∈ S) (hz2 : z ^ 2 = 1) (hzA : ∀ a ∈ A, a * z = z * a) : z ∈ A := by
  have hZe : IsElemAbelian 2 (Subgroup.zpowers z) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := x.2
      obtain ⟨n, hn⟩ := y.2
      refine Subtype.ext ?_
      show (x : G) * y = y * x
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self z m n).eq
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hel := isElemAbelian_sup' hA.2.1 hZe fun a ha y hy => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute a z := hzA a ha
    exact (hc.zpow_right m).eq
  have hle : Nat.card (A ⊔ Subgroup.zpowers z : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ (sup_le hA.1 ((Subgroup.zpowers_le).2 hzS)) hel
  have heq : A ⊔ Subgroup.zpowers z = A := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  exact heq ▸ (le_sup_right : Subgroup.zpowers z ≤ A ⊔ Subgroup.zpowers z) (Subgroup.mem_zpowers z)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
