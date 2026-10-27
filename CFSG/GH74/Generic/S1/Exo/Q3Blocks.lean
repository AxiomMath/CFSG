module

public import CFSG.GH74.Generic.S1.Exo.Q3Core
public import CFSG.GH74.Generic.S1.Exo.Q3SL2

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

section Blocks3

variable {y c : G} (D : LayerData y (StatedSL 4 F))

@[expose] noncomputable def blkA3 : Subgroup G := (blkLin (F := F) 0 1).map D.ι

@[expose] noncomputable def blkB3 : Subgroup G := (blkLin (F := F) 2 3).map D.ι

omit [Finite F] in
theorem blkA3_comm_blkB3 : ∀ a ∈ blkA3 D, ∀ b ∈ blkB3 D, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, blkLin_commute 0 1 2 3 (by decide) (by decide) (by decide) (by decide) a ha b hb]

omit [Finite F] in
theorem blkA3_le_cent (hDc : D.ι (linZ0 F) = c) : blkA3 D ≤ centralizer ({c} : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_singleton_iff, ← hDc, ← map_mul, ← map_mul, linZ0_comm a ha]

omit [Finite F] in
theorem blkB3_le_cent (hDc : D.ι (linZ0 F) = c) : blkB3 D ≤ centralizer ({c} : Set G) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_singleton_iff, ← hDc, ← map_mul, ← map_mul,
    blkLin_commute 2 3 0 1 (by decide) (by decide) (by decide) (by decide) b hb (linZ0 F) linZ0_mem_blkLin]

omit [Finite F] in
theorem blkA3_le_centY : blkA3 D ≤ centralizer ({y} : Set G) := by
  rintro _ ⟨a, -, rfl⟩
  exact D.ι_mem_cent a

omit [Finite F] in
theorem blkB3_le_centY : blkB3 D ≤ centralizer ({y} : Set G) := by
  rintro _ ⟨a, -, rfl⟩
  exact D.ι_mem_cent a

omit [Finite F] in
theorem c_mem_blkA3 (hDc : D.ι (linZ0 F) = c) : c ∈ blkA3 D := ⟨linZ0 F, linZ0_mem_blkLin, hDc⟩

theorem yc_mem_blkB3 (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) (hy : orderOf y = 2)
    (hyK : xbar y ∈ D.K) : y * c ∈ blkB3 D := by
  have hF4 : Nat.card F % 4 = 3 := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  refine ⟨linNeg F * linZ0 F, ?_, ?_⟩
  · exact neg_mul_mem_lin hF4 h2 (a := 2) (b := 3) (c := 0) (d := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((linNeg_center hF4 _).2 (Or.inr rfl))
      (linNeg_ne_one h2) linZ0_mem_blkLin linZ0_mul_self (linZ0_ne_one h2)
  · have hneg : D.ι (linNeg F) = y := ι_neg_eq_core (linModelCore hF4) D hy hyK
    rw [map_mul, hneg, hDc]

theorem blkLin_center_card (hF : Nat.card F = 3) (a b : Fin 4) (hab : a ≠ b) :
    Nat.card (center ↥(blkLin (F := F) a b)) = 2 := by
  obtain ⟨e⟩ := blkLin_equiv (F := F) a b hab
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  rw [← natCard_center_eq_of_mulEquiv e]
  exact natCard_center_sl2_eq_two h2

omit [Finite G] [Finite F] in
noncomputable def blkEquiv3 (D : LayerData y (StatedSL 4 F)) (a b : Fin 4) :
    ↥(blkLin (F := F) a b) ≃* ↥((blkLin (F := F) a b).map D.ι) :=
  (blkLin (F := F) a b).equivMapOfInjective D.ι D.ι_injective

theorem blkA3_center_card (hF : Nat.card F = 3) : Nat.card (center ↥(blkA3 D)) = 2 := by
  change Nat.card (center ↥((blkLin (F := F) 0 1).map D.ι)) = 2
  rw [← natCard_center_eq_of_mulEquiv (blkEquiv3 D 0 1)]
  exact blkLin_center_card hF 0 1 (by decide)

theorem blkB3_center_card (hF : Nat.card F = 3) : Nat.card (center ↥(blkB3 D)) = 2 := by
  change Nat.card (center ↥((blkLin (F := F) 2 3).map D.ι)) = 2
  rw [← natCard_center_eq_of_mulEquiv (blkEquiv3 D 2 3)]
  exact blkLin_center_card hF 2 3 (by decide)

omit [Finite F] in
theorem c_mem_center_blkA3 (hDc : D.ι (linZ0 F) = c) :
    (⟨c, c_mem_blkA3 D hDc⟩ : ↥(blkA3 D)) ∈ center ↥(blkA3 D) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨a, ha, rfl⟩⟩
  apply Subtype.ext
  change D.ι a * c = c * D.ι a
  rw [← hDc, ← map_mul, ← map_mul, linZ0_comm a ha]

theorem blkA3_center_eq (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) (hc1 : c ≠ 1) :
    center ↥(blkA3 D) = zpowers (⟨c, c_mem_blkA3 D hDc⟩ : ↥(blkA3 D)) :=
  center_eq_zpowers_of_card_two (blkA3_center_card D hF) (c_mem_center_blkA3 D hDc)
    (fun h => hc1 (congrArg Subtype.val h))

theorem yc_mem_center_blkB3 (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) (hy : orderOf y = 2)
    (hyK : xbar y ∈ D.K) :
    (⟨y * c, yc_mem_blkB3 D hF hDc hy hyK⟩ : ↥(blkB3 D)) ∈ center ↥(blkB3 D) := by
  have hF4 : Nat.card F % 4 = 3 := by omega
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨b, hb, rfl⟩⟩
  apply Subtype.ext
  change D.ι b * (y * c) = (y * c) * D.ι b
  have hneg : D.ι (linNeg F) = y := ι_neg_eq_core (linModelCore hF4) D hy hyK
  have hyc : y * c = D.ι (linNeg F * linZ0 F) := by rw [map_mul, hneg, hDc]
  rw [hyc, ← map_mul, ← map_mul]
  congr 1
  have h1 := Subgroup.mem_center_iff.1 ((linNeg_center hF4 (linNeg F)).2 (Or.inr rfl)) b
  have h2 := blkLin_commute 2 3 0 1 (by decide) (by decide) (by decide) (by decide) b hb (linZ0 F)
    linZ0_mem_blkLin
  calc b * (linNeg F * linZ0 F) = (b * linNeg F) * linZ0 F := by rw [mul_assoc]
    _ = (linNeg F * b) * linZ0 F := by rw [h1]
    _ = linNeg F * (b * linZ0 F) := by rw [mul_assoc]
    _ = linNeg F * (linZ0 F * b) := by rw [h2]
    _ = (linNeg F * linZ0 F) * b := by rw [mul_assoc]

theorem blkB3_center_eq (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) (hy : orderOf y = 2)
    (hyK : xbar y ∈ D.K) (hyc1 : y * c ≠ 1) :
    center ↥(blkB3 D) = zpowers (⟨y * c, yc_mem_blkB3 D hF hDc hy hyK⟩ : ↥(blkB3 D)) :=
  center_eq_zpowers_of_card_two (blkB3_center_card D hF) (yc_mem_center_blkB3 D hF hDc hy hyK)
    (fun h => hyc1 (congrArg Subtype.val h))

noncomputable def blkA3_equiv : SL(2, F) ≃* ↥(blkA3 D) :=
  (blkLin_equiv (F := F) 0 1 (by decide)).some.trans (blkEquiv3 D 0 1)

noncomputable def blkB3_equiv : SL(2, F) ≃* ↥(blkB3 D) :=
  (blkLin_equiv (F := F) 2 3 (by decide)).some.trans (blkEquiv3 D 2 3)

theorem blkA3_odd_free (hF : Nat.card F = 3) :
    ∀ N : Subgroup ↥(blkA3 D), N.Normal → Odd (Nat.card N) → N = ⊥ :=
  fun N _hN hodd => sl23_no_odd_normal hF (blkA3_equiv D) N hodd

theorem blkB3_odd_free (hF : Nat.card F = 3) :
    ∀ N : Subgroup ↥(blkB3 D), N.Normal → Odd (Nat.card N) → N = ⊥ :=
  fun N _hN hodd => sl23_no_odd_normal hF (blkB3_equiv D) N hodd

theorem blkA3_proj_inj (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) :
    Function.Injective ((proj c).comp (Subgroup.inclusion (blkA3_le_cent D hDc))) :=
  proj_injective_of_odd_free (blkA3_le_cent D hDc) (blkA3_odd_free D hF)

theorem blkB3_proj_inj (hF : Nat.card F = 3) (hDc : D.ι (linZ0 F) = c) :
    Function.Injective ((proj c).comp (Subgroup.inclusion (blkB3_le_cent D hDc))) :=
  proj_injective_of_odd_free (blkB3_le_cent D hDc) (blkB3_odd_free D hF)

end Blocks3

end CFSG.GH74.Generic.S1.Exo
