module

public import CFSG.CGT.PushingUpLit.T2K.Offender

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

structure Hyp45 (L M T A : Subgroup G) (n : ℕ) : Prop where
  block : NatBlock L n
  le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  max : IsMaxElemAbelian T A
  nontriv : ¬ A ≤ Subgroup.centralizer (blockU L : Set G)

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem A_le_T : A ≤ T := H.max.1

theorem A_le_M : A ≤ M := H.A_le_T.trans H.sylow.le

theorem M_le_normalizer_V : M ≤ Subgroup.normalizer (blockU L : Set G) :=
  NatBlock.le_normalizer_blockU_of_le H.normal

theorem V_le_T : blockU L ≤ T := NatBlock.blockU_le_sylow H.le H.normal H.sylow

theorem A_isElemAbelian : IsElemAbelian 2 A := H.max.2.1

theorem A_comm {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  isElemAbelian_comm' H.A_isElemAbelian ha hb

theorem offender_data :
    (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A = 2 ^ n ∧
      (blockU L ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU L) = 2 ^ n ∧
      ∀ a ∈ A, ∃ l ∈ L, ∀ v ∈ blockU L, a * v * a⁻¹ = l * v * l⁻¹ :=
  H.block.offender H.le H.normal H.sylow H.max H.nontriv

theorem index_centralizer :
    (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A = 2 ^ n := H.offender_data.1

theorem acts_as (a : G) (ha : a ∈ A) : ∃ l ∈ L, ∀ v ∈ blockU L, a * v * a⁻¹ = l * v * l⁻¹ :=
  H.offender_data.2.2 a ha

theorem centralizer_blockU_eq :
    blockU L ⊓ Subgroup.centralizer (A : Set G) = blockU L ⊓ A := by
  apply le_antisymm
  · intro x ⟨hxV, hxC⟩
    refine ⟨hxV, ?_⟩
    have hx2 : x ^ 2 = 1 := H.block.sq_eq_one_of_mem_blockU hxV
    have hZ : IsElemAbelian 2 (Subgroup.zpowers x) := by
      refine isElemAbelian_of_forall' (fun a ha b hb => ?_) (fun a ha => ?_)
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow_self x i j).eq
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
    have hcomm : ∀ a ∈ A, ∀ y ∈ Subgroup.zpowers x, a * y = y * a := by
      intro a ha y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have h1 : a * x = x * a := Subgroup.mem_centralizer_iff.1 hxC a ha
      exact ((Commute.zpow_right (show Commute a x from h1) i)).eq
    have hAx := isElemAbelian_sup' H.A_isElemAbelian hZ hcomm
    have hle : A ⊔ Subgroup.zpowers x ≤ T :=
      sup_le H.A_le_T ((Subgroup.zpowers_le).2 (H.V_le_T hxV))
    have hcard := H.max.2.2 _ hle hAx
    have heq : A ⊔ Subgroup.zpowers x = A := by
      symm
      exact Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    have : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [heq] at this
  · intro x ⟨hxV, hxA⟩
    exact ⟨hxV, Subgroup.mem_centralizer_iff.2 fun a ha => H.A_comm ha hxA⟩

theorem blockU_le_centralizer : blockU L ≤ Subgroup.centralizer (blockU L : Set G) :=
  fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw => H.block.blockU_comm w hw v hv

theorem card_blockU_inf : 2 ^ n * Nat.card ↥(blockU L ⊓ A) = Nat.card ↥(blockU L) := by
  have h1 := Subgroup.relIndex_mul_card (blockU L ⊓ Subgroup.centralizer (A : Set G))
    (blockU L)
  rw [H.offender_data.2.1, inf_of_le_left inf_le_left, H.centralizer_blockU_eq] at h1
  exact h1

theorem card_inf_centralizer :
    2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) = Nat.card ↥A := by
  have h1 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (blockU L : Set G)) A
  rw [inf_of_le_left inf_le_left, H.index_centralizer] at h1
  exact h1

@[expose] def bGrp (L A : Subgroup G) : Subgroup G :=
  (A ⊓ Subgroup.centralizer (blockU L : Set G)) ⊔ blockU L

theorem B_isElemAbelian : IsElemAbelian 2 (bGrp L A) := by
  refine isElemAbelian_sup' (isElemAbelian_mono' H.A_isElemAbelian inf_le_left)
    H.block.isElemAbelian_blockU fun x hx y hy => ?_
  exact (Subgroup.mem_centralizer_iff.1 hx.2 y hy).symm

theorem B_le_T : bGrp L A ≤ T :=
  sup_le (inf_le_left.trans H.A_le_T) H.V_le_T

theorem card_B : Nat.card ↥(bGrp L A) = Nat.card ↥A := by
  have hcomm : ∀ x ∈ A ⊓ Subgroup.centralizer (blockU L : Set G), ∀ y ∈ blockU L,
      x * y = y * x := fun x hx y hy => (Subgroup.mem_centralizer_iff.1 hx.2 y hy).symm
  have h1 := card_sup_mul_card_inf' hcomm
  have hinf : (A ⊓ Subgroup.centralizer (blockU L : Set G)) ⊓ blockU L = blockU L ⊓ A := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, H.blockU_le_centralizer h.1⟩, h.1⟩⟩
  rw [hinf] at h1
  have h2 := H.card_blockU_inf
  have h3 := H.card_inf_centralizer
  have hpos : 0 < Nat.card ↥(blockU L ⊓ A) := Nat.card_pos
  have : Nat.card ↥(bGrp L A) * Nat.card ↥(blockU L ⊓ A) =
      Nat.card ↥A * Nat.card ↥(blockU L ⊓ A) := by
    show Nat.card ↥((A ⊓ Subgroup.centralizer (blockU L : Set G)) ⊔ blockU L) * _ = _
    rw [h1, ← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem isMaxElemAbelian_B : IsMaxElemAbelian T (bGrp L A) :=
  ⟨H.B_le_T, H.B_isElemAbelian, fun B' hB'T hB' => by
    rw [H.card_B]
    exact H.max.2.2 B' hB'T hB'⟩

theorem V_le_P : blockU L ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
  le_inf H.V_le_T H.blockU_le_centralizer

theorem B_le_P : bGrp L A ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
  sup_le (le_inf (inf_le_left.trans H.A_le_T) inf_le_right) H.V_le_P

theorem isMaxElemAbelian_B_P :
    IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) (bGrp L A) :=
  ⟨H.B_le_P, H.B_isElemAbelian, fun B' hB'P hB' => by
    rw [H.card_B]
    exact H.max.2.2 B' (hB'P.trans inf_le_left) hB'⟩

theorem le_normalizer_of_isMaxElemAbelian_P {D : Subgroup G}
    (hD : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D) :
    L ≤ Subgroup.normalizer (D : Set G) := by
  have hDP : D ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) := hD.1
  have hDU : ∀ d ∈ D, d ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := fun d hd =>
    ⟨H.sylow.le (hDP hd).1, (hDP hd).2⟩
  have hVD : blockU L ≤ D := by
    have hcomm : ∀ v ∈ blockU L, ∀ d ∈ D, v * d = d * v := fun v hv d hd =>
      Subgroup.mem_centralizer_iff.1 (hDP hd).2 v hv
    have hsup := isElemAbelian_sup' H.block.isElemAbelian_blockU hD.2.1 hcomm
    have hle : blockU L ⊔ D ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
      sup_le H.V_le_P hDP
    have hcard := hD.2.2 _ hle hsup
    have heq : D = blockU L ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
    exact le_sup_left.trans heq.ge
  have key : ∀ l ∈ L, ∀ d ∈ D, l * d * l⁻¹ ∈ D := by
    intro l hl d hd
    have h1 : ⁅l, d⁆ ∈ blockU L := by
      have := H.block.comm_centralizer_mem_blockU H.normal (hDU d hd) l hl
      have h2 := (blockU L).inv_mem this
      rwa [commutatorElement_inv] at h2
    have e : l * d * l⁻¹ = ⁅l, d⁆ * d := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact D.mul_mem (hVD h1) hd
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key l hl d, fun hd => ?_⟩
  have := key l⁻¹ (L.inv_mem hl) _ hd
  simpa [mul_assoc] using this

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
