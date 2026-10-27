module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def FGKind2D (hQ : Q.Nondegenerate) (g : OGroup Q) : Subgroup (OGroup Q) :=
  omegaGroup hQ ⊓ centralizer ({g} : Set (OGroup Q))

theorem fg_kind2_D_le_range (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1) :
    FGKind2D hQ g ≤ (blockHom hgg).range := by
  rw [range_blockHom hQ hgg]
  exact inf_le_right

@[expose] noncomputable def FGKind2Chi (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1) :
    ↥(FGKind2D hQ g) →* OGroup (Q.restrict (commSp g)) :=
  (MonoidHom.snd _ _).comp
    ((MonoidHom.ofInjective (blockHom_injective hgg)).symm.toMonoidHom.comp
      (Subgroup.inclusion (fg_kind2_D_le_range hQ hgg)))

theorem fg_kind2_chi_blockHom (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    (a : OGroup (Q.restrict (fixSp g))) (b : OGroup (Q.restrict (commSp g)))
    (h : blockHom hgg (a, b) ∈ FGKind2D hQ g) :
    FGKind2Chi hQ hgg ⟨blockHom hgg (a, b), h⟩ = b := by
  have h1 : (MonoidHom.ofInjective (blockHom_injective hgg)).symm
      (Subgroup.inclusion (fg_kind2_D_le_range hQ hgg) ⟨blockHom hgg (a, b), h⟩) = (a, b) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  change ((MonoidHom.ofInjective (blockHom_injective hgg)).symm
      (Subgroup.inclusion (fg_kind2_D_le_range hQ hgg) ⟨blockHom hgg (a, b), h⟩)).2 = b
  rw [h1]

theorem fg_kind2_exists_blockHom (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    (x : ↥(FGKind2D hQ g)) :
    ∃ a : OGroup (Q.restrict (fixSp g)),
      blockHom hgg (a, FGKind2Chi hQ hgg x) = (x : OGroup Q) := by
  let y := (MonoidHom.ofInjective (blockHom_injective hgg)).symm
    (Subgroup.inclusion (fg_kind2_D_le_range hQ hgg) x)
  refine ⟨y.1, ?_⟩
  have h1 : blockHom hgg y = (x : OGroup Q) := by
    have h2 := (MonoidHom.ofInjective (blockHom_injective hgg)).apply_symm_apply
      (Subgroup.inclusion (fg_kind2_D_le_range hQ hgg) x)
    exact congrArg Subtype.val h2
  rw [← h1]
  exact congrArg (blockHom hgg) (Prod.ext rfl rfl)

theorem fg_kind2_chi_piOrth (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    (hπ : piOrth Q ∈ FGKind2D hQ g) :
    FGKind2Chi hQ hgg ⟨piOrth Q, hπ⟩ = piOrth (Q.restrict (commSp g)) := by
  have hb : blockHom hgg (piOrth (Q.restrict (fixSp g)), piOrth (Q.restrict (commSp g))) ∈
      FGKind2D hQ g := by
    rw [blockHom_piOrth_piOrth hgg]
    exact hπ
  have h := fg_kind2_chi_blockHom hQ hgg _ _ hb
  rw [← h]
  congr 1
  exact Subtype.ext (blockHom_piOrth_piOrth hgg).symm

theorem fg_kind2_chi_piOrth_ne_one (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    (hπ : piOrth Q ∈ FGKind2D hQ g) (hpos : 0 < Module.finrank (ZMod 3) (commSp g)) :
    FGKind2Chi hQ hgg ⟨piOrth Q, hπ⟩ ≠ 1 := by
  rw [fg_kind2_chi_piOrth hQ hgg hπ]
  exact piOrth_ne_one hpos

theorem fg_kind2_mul_eq_one_of_ne_one {H : Type*} [Group H] (h2 : Nat.card H = 2) {u v : H}
    (hu : u ≠ 1) (hv : v ≠ 1) : u * v = 1 := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hord : ∀ x : H, x ≠ 1 → orderOf x = 2 := fun x hx => by
    have hd : orderOf x ∣ 2 := h2 ▸ orderOf_dvd_natCard x
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun h1 => hx (orderOf_eq_one_iff.mp h1))
  have huv : v ∈ Subgroup.zpowers u := by
    have htop : Subgroup.zpowers u = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord u hu, h2]
    rw [htop]
    exact Subgroup.mem_top v
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp huv
  have hu2 : u ^ 2 = 1 := by rw [← hord u hu]; exact pow_orderOf_eq_one u
  have hk : u ^ k = 1 ∨ u ^ k = u := by
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · left; rw [hm, zpow_mul]; simp [hu2]
    · right; rw [hm, zpow_add, zpow_mul]; simp [hu2]
  rcases hk with hk | hk
  · exact absurd hk hv
  · rw [hk]; rw [← pow_two]; exact hu2

end CFSG.OddStandard.SmallF3.Omega
