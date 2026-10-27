module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Sing
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Semi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELoc
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commute_of_block_singer {U W Z D₁ B' : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a ^ 2 = 1)
    (hWU : W ≤ U) (hZW : Z ≤ W)
    (hDW : ∀ d ∈ D₁, ∀ w ∈ W, d * w * d⁻¹ ∈ W)
    (hDZ : ∀ d ∈ D₁, ∀ z ∈ Z, d * z = z * d)
    (hDcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b = b * a)
    (hfpf : ∀ d ∈ D₁, d ≠ 1 → ∀ u ∈ U, d * u * d⁻¹ * u⁻¹ ∈ Z → u ∈ Z)
    (hDcard : Nat.card D₁ = 2 ^ n - 1) (hWZ : Z.relIndex W = 2 ^ n)
    (hD₁B : D₁ ≤ B') (hBD : B' ≤ Subgroup.normalizer (D₁ : Set G))
    (hBW : B' ≤ Subgroup.normalizer (W : Set G)) {d' : G} (hd' : d' ∈ B')
    (hcomm : ∀ d ∈ D₁, d' * (d * d' * d⁻¹ * d'⁻¹) = (d * d' * d⁻¹ * d'⁻¹) * d') :
    ∀ d ∈ D₁, d * d' = d' * d := by
  obtain ⟨hZ'W, hZ'c, hZ'2, hZ'card, -, hreg⟩ :=
    exists_singer hn hUc hU2 hWU hZW hDW hDZ hDcomm hfpf hDcard hWZ
  have hZ'N : B' ≤ Subgroup.normalizer ((⁅W, D₁⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [← conjR_eq_self_iff]
    show conjSubgroup ⁅W, D₁⁆ b = _
    rw [C5.conjSubgroup_commutator]
    have h1 : conjSubgroup W b = W := C5.conjSubgroup_eq_self (hBW hb)
    have h2 : conjSubgroup D₁ b = D₁ := C5.conjSubgroup_eq_self (hBD hb)
    rw [h1, h2]
  refine commute_of_singer_comm (Z := ⁅W, D₁⁆) (D := D₁) (B := B') (e := n)
    (by omega) ⟨⟨⟨fun a b => Subtype.ext (hZ'c a.1 a.2 b.1 b.2)⟩⟩, hZ'2⟩ hZ'card hZ'N hD₁B
    ?_ hDcomm hreg hDcard hd' hcomm
  intro b hb d hd
  have := (Subgroup.mem_normalizer_iff.1 (hBD hb) d).1 hd
  exact this

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [← conjR_eq_self_iff]
  show conjSubgroup ⁅A, B⁆ g = _
  rw [C5.conjSubgroup_commutator, C5.conjSubgroup_eq_self hA, C5.conjSubgroup_eq_self hB]

theorem relIndex_Z_W_eq {Lb Wb Qb R : Subgroup G} {n q : ℕ} (hlin : IsLin2Type Lb n)
    (hloc : AppE.Loc R Lb (blockU Lb) Qb Wb q) (hZW : blockZ Lb ≤ Wb) :
    q = 2 ^ n ∧ (blockZ Lb).relIndex Wb = 2 ^ n := by
  have h2 : (blockZ Lb).relIndex (blockU Lb) = q ^ 2 := hloc.hZ
  have hq : q = 2 ^ n := by
    have h1 := Subgroup.relIndex_mul_card (H := blockZ Lb) (K := blockU Lb)
    rw [inf_eq_left.mpr (blockZ_le_blockU Lb)] at h1
    have h3 := lin2_card_U hlin
    have hZpos : 0 < Nat.card (blockZ Lb) := Nat.card_pos
    have h4 : q ^ 2 = (2 ^ n) ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hZpos
      rw [← h2, h1, h3, ← pow_mul, mul_comm n 2, pow_mul]
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h4
  refine ⟨hq, ?_⟩
  have h5 := Subgroup.relIndex_mul_relIndex (blockZ Lb) Wb (blockU Lb) hZW hloc.rk.W_le_U
  rw [hloc.rk.idx_W, h2] at h5
  have hqpos : 0 < q := Nat.pos_of_ne_zero hloc.rk.q_ne_zero
  rw [← hq]
  exact Nat.eq_of_mul_eq_mul_right hqpos (by rw [h5]; ring)

theorem commute_of_block {Lb Rb Qb Wb R D₁ B' : Subgroup G} {n q : ℕ} (hn : 2 ≤ n)
    (hLb : IsShort2 Lb) (hlin : IsLin2Type Lb n)
    (hloc : AppE.Loc R Lb (blockU Lb) Qb Wb q) (hZW : blockZ Lb ≤ Wb)
    (hT : BlockTorus Lb Rb D₁ n) (hD₁R : D₁ ≤ Subgroup.normalizer (R : Set G))
    (hD₁B : D₁ ≤ B') (hBD : B' ≤ Subgroup.normalizer (D₁ : Set G))
    (hBW : B' ≤ Subgroup.normalizer (Wb : Set G)) {d' : G} (hd' : d' ∈ B')
    (hcomm : ∀ d ∈ D₁, d' * (d * d' * d⁻¹ * d'⁻¹) = (d * d' * d⁻¹ * d'⁻¹) * d') :
    ∀ d ∈ D₁, d * d' = d' * d := by
  have hD₁L : D₁ ≤ Lb := hT.le_borel.trans inf_le_left
  have hD₁U : D₁ ≤ Subgroup.normalizer (blockU Lb : Set G) := fun d hd =>
    C1.mem_normalizer_blockU (Subgroup.le_normalizer (hD₁L hd))
  obtain ⟨-, hWZ⟩ := relIndex_Z_W_eq hlin hloc hZW
  have hDW : ∀ d ∈ D₁, ∀ w ∈ Wb, d * w * d⁻¹ ∈ Wb := by
    intro d hd w hw
    have hdN : d ∈ Subgroup.normalizer (Wb : Set G) := by
      have := mem_normalizer_commutator (hD₁U hd) (hD₁R hd)
      rwa [hloc.rk.comm_UB] at this
    exact (Subgroup.mem_normalizer_iff.1 hdN w).1 hw
  have hDZ : ∀ d ∈ D₁, ∀ z ∈ blockZ Lb, d * z = z * d := fun d hd z hz =>
    Subgroup.mem_centralizer_iff.1 hz.2 d (hD₁L hd)
  have hDcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b = b * a := fun a ha b hb =>
    haveI := hT.cyclic
    congrArg Subtype.val ((IsCyclic.commGroup (α := D₁)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact commute_of_block_singer hn hloc.rk.U_comm (C1.blockU_sq hLb) hloc.rk.W_le_U hZW hDW hDZ hDcomm
    hT.fpf_U hT.card hWZ hD₁B hBD hBW hd' hcomm

end CFSG.QuasithinUnique.Lin2
