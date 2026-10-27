module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEDbl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Natural

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] def H1 (S L : Subgroup G) : Subgroup G := L ⊔ R1 S L

omit [Finite G] in
theorem R1_le_normalizer_L : R1 S L ≤ normalizer (L : Set G) := inf_le_right

omit [Finite G] in
theorem L_le_H1 : L ≤ H1 S L := le_sup_left

omit [Finite G] in
theorem R1_le_H1 : R1 S L ≤ H1 S L := le_sup_right

omit [Finite G] in
theorem H1_le_normalizer_L : H1 S L ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer R1_le_normalizer_L

omit [Finite G] in
theorem mem_H1_iff {x : G} : x ∈ H1 S L ↔ ∃ r ∈ R1 S L, ∃ l ∈ L, x = r * l := by
  constructor
  · intro hx
    rw [H1, sup_comm] at hx
    exact C5.mem_sup_of_le_normalizer R1_le_normalizer_L hx
  · rintro ⟨r, hr, l, hl, rfl⟩
    exact (H1 S L).mul_mem (R1_le_H1 hr) (L_le_H1 hl)

omit [Finite G] in
theorem L_inf_R1 : L ⊓ R1 S L = S ⊓ L := by
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hL, hR⟩
    exact ⟨R1_le_S hR, hL⟩
  · rintro ⟨hS, hL⟩
    exact ⟨hL, hS, Subgroup.le_normalizer hL⟩

namespace Dbl

variable {n : ℕ} {t : G} (D : Dbl T M H S L n t)
include D

theorem H1_le_H : H1 S L ≤ H :=
  sup_le (C56.le_H D.hcs) (R1_le_S.trans D.hcs.sylow.le)

theorem S_le_M : S ≤ M := (D.hcs.sylow_inf.1).trans inf_le_right

theorem isSylow_S_inf_L : IsSylowTwoOf (S ⊓ L) L :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal D.hcs.sylow (C56.le_H D.hcs) D.hcs.block.1.2.2

theorem isSylowTwoOf_R1_H1 : IsSylowTwoOf (R1 S L) (H1 S L) := by
  have hS2 : IsPGroup 2 S := D.hcs.sylow.isPGroup
  refine ⟨R1_le_H1, hS2.to_le R1_le_S, ?_⟩
  have hsyl := D.isSylow_S_inf_L
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer (A := R1 S L) (B := L)
    R1_le_normalizer_L
  rw [sup_comm, ← H1, inf_comm, L_inf_R1] at h1
  have h2 := C5.card_eq_card_mul_relIndex (R1_le_H1 : R1 S L ≤ H1 S L)
  have h3 := C5.card_eq_card_mul_relIndex (inf_le_right : S ⊓ L ≤ L)
  have hpos : 0 < Nat.card ↥(S ⊓ L) := Nat.card_pos
  have hposR : 0 < Nat.card ↥(R1 S L) := Nat.card_pos
  have hodd := hsyl.2.2
  show ¬ 2 ∣ (R1 S L).relIndex (H1 S L)
  have e : (R1 S L).relIndex (H1 S L) = (S ⊓ L).relIndex L := by
    rw [h2, h3] at h1
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hposR hpos) ?_
    calc Nat.card ↥(R1 S L) * Nat.card ↥(S ⊓ L) * (R1 S L).relIndex (H1 S L)
        = Nat.card ↥(R1 S L) * (R1 S L).relIndex (H1 S L) * Nat.card ↥(S ⊓ L) := by ring
      _ = Nat.card ↥(R1 S L) * (Nat.card ↥(S ⊓ L) * (S ⊓ L).relIndex L) := h1
      _ = Nat.card ↥(R1 S L) * Nat.card ↥(S ⊓ L) * (S ⊓ L).relIndex L := by ring
  rw [e]
  exact hodd

theorem not_le_normalizer_R1 : ¬ H1 S L ≤ normalizer (R1 S L : Set G) := by
  intro h
  have hLN : L ≤ normalizer (R1 S L : Set G) := L_le_H1.trans h
  have hth := D.hcs.thompson
  have hLR : L ≤ R1 S L := by
    conv_lhs => rw [← hth]
    rw [Subgroup.commutator_le]
    intro l hl j hj
    have hjR : j ∈ R1 S L := D.thompsonJ_le_R1 hj
    have h1 : l * j * l⁻¹ ∈ R1 S L := (Subgroup.mem_normalizer_iff.1 (hLN hl) j).1 hjR
    have : ⁅l, j⁆ = (l * j * l⁻¹) * j⁻¹ := commutatorElement_def l j
    rw [this]
    exact (R1 S L).mul_mem h1 ((R1 S L).inv_mem hjR)
  exact D.hcs.not_le ((hLR.trans R1_le_S).trans D.S_le_M)

theorem conjR_Y_of_mem_R1 {Y : Subgroup G} (hY : ∀ r ∈ R1 S L, conjR Y r = Y) {g : G}
    (hg : g ∈ S) :
    (g ∈ R1 S L → conjR Y g = Y ∧ conjR (conjR Y t) g = conjR Y t) ∧
      (g ∉ R1 S L → conjR Y g = conjR Y t ∧ conjR (conjR Y t) g = Y) := by
  have hinv : ∀ X : Subgroup G, ∀ a : G, conjR (conjR X a) a⁻¹ = X := fun X a => by
    rw [conjR_conjR, mul_inv_cancel]; exact conjSubgroup_one _
  constructor
  · intro hgR
    refine ⟨hY g hgR, ?_⟩
    have hconj : t * g * t⁻¹ ∈ R1 S L := D.R1_normal D.ht hgR
    have e : t * g = (t * g * t⁻¹) * t := by group
    rw [conjR_conjR, e, ← conjR_conjR, hY _ hconj]
  · intro hgR
    have hgt : conjR L g = conjR L t := D.conjR_eq_t_of_not_mem hg hgR
    have hr' : g * t⁻¹ ∈ R1 S L := by
      rw [mem_R1_iff]
      refine ⟨S.mul_mem hg (S.inv_mem D.ht), ?_⟩
      rw [← conjR_conjR, hgt]
      exact hinv L t
    have e1 : g = (g * t⁻¹) * t := by group
    refine ⟨?_, ?_⟩
    · rw [e1, ← conjR_conjR, hY _ hr']
    · have hconj : t * (g * t⁻¹) * t⁻¹ ∈ R1 S L := D.R1_normal D.ht hr'
      have e2 : t * g = (t * (g * t⁻¹) * t⁻¹) * (t * t) := by group
      rw [conjR_conjR, e2, ← conjR_conjR, hY _ hconj, hY _ D.t_sq_mem]

theorem unique_max {X : Subgroup G} (hRX : R1 S L ≤ X) (hXlt : X < H1 S L) : X ≤ M := by
  classical
  have hS2 : IsPGroup 2 S := D.hcs.sylow.isPGroup
  set Y₁ : Subgroup G := X ⊓ L with hY₁
  set Y₂ : Subgroup G := conjR Y₁ t with hY₂
  have hXdec : ∀ x ∈ X, ∃ r ∈ R1 S L, ∃ l ∈ Y₁, x = r * l := by
    intro x hx
    obtain ⟨r, hr, l, hl, rfl⟩ := mem_H1_iff.1 (hXlt.le hx)
    refine ⟨r, hr, l, ⟨?_, hl⟩, rfl⟩
    have := X.mul_mem (X.inv_mem (hRX hr)) hx
    simpa using this
  have hY₁ne : Y₁ ≠ L := by
    intro h
    have hLX : L ≤ X := fun l hl => (h ▸ hl : l ∈ Y₁).1
    exact hXlt.2 (sup_le hLX hRX)
  have hYR : ∀ r ∈ R1 S L, conjR Y₁ r = Y₁ := by
    intro r hr
    have h1 : r ∈ normalizer (X : Set G) := Subgroup.le_normalizer (hRX hr)
    have h2 : r ∈ normalizer (L : Set G) := R1_le_normalizer_L hr
    show conjSubgroup (X ⊓ L) r = X ⊓ L
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self h1, C5.conjSubgroup_eq_self h2]
  have hSN : ∀ g ∈ S, conjR (Y₁ ⊔ Y₂) g = Y₁ ⊔ Y₂ := by
    intro g hg
    by_cases hgR : g ∈ R1 S L
    · obtain ⟨h1, h2⟩ := (D.conjR_Y_of_mem_R1 hYR hg).1 hgR
      show conjSubgroup (Y₁ ⊔ Y₂) g = Y₁ ⊔ Y₂
      rw [C5.conjSubgroup_sup]
      exact congrArg₂ (· ⊔ ·) h1 h2
    · obtain ⟨h1, h2⟩ := (D.conjR_Y_of_mem_R1 hYR hg).2 hgR
      show conjSubgroup (Y₁ ⊔ Y₂) g = Y₁ ⊔ Y₂
      rw [C5.conjSubgroup_sup]
      show conjR Y₁ g ⊔ conjR Y₂ g = _
      rw [h1, h2, sup_comm]
  have hSNorm : S ≤ normalizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) := fun g hg =>
    conjSubgroup_eq_iff_mem_normalizer.1 (hSN g hg)
  have hY₁L : Y₁ ≤ L := inf_le_right
  have hY₂L₂ : Y₂ ≤ conjR L t := C5.conjSubgroup_mono hY₁L t
  have hN'K : Y₁ ⊔ Y₂ ≤ conjJoin S L :=
    sup_le (hY₁L.trans (L_le_K (S := S))) (hY₂L₂.trans D.L₂_le_K)
  have hLnot : ¬ L ≤ (Y₁ ⊔ Y₂) ⊔ S := by
    intro hL
    have hLN' : L ≤ Y₁ ⊔ Y₂ := C56.le_of_le_sup_isPGroup D.hL hS2 hSNorm hL
    apply hY₁ne
    refine le_antisymm hY₁L fun l hl => ?_
    have hl' : l ∈ Y₁ ⊔ Y₂ := hLN' hl
    obtain ⟨a, ha, b, hb, hab⟩ := C5.mem_sup_of_le_normalizer
      (C5.le_normalizer_of_commute (fun u hu v hv => D.comm_elem u (hY₁L hu) v (hY₂L₂ hv))) hl'
    have hbL : b ∈ L := by
      have : b = a⁻¹ * l := by rw [hab]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hY₁L ha)) hl
    have hbL₂ : b ∈ conjR L t := hY₂L₂ hb
    have hbQ : b ∈ blockQ L :=
      mem_blockQ_of_comm_lin2 D.hn D.hlin hbL fun y hy => by
        have : b * y = y * b := D.comm_elem y hy b hbL₂ |>.symm
        have e : b * y * b⁻¹ * y⁻¹ = 1 := by
          rw [this]; group
        rw [e]
        exact (blockQ L).one_mem
    have hQT : blockQ L ≤ S ⊓ L :=
      D.isSylow_S_inf_L.le_of_normalizes (C1.blockQ_le L) (C1.le_normalizer_blockQ L)
        (C1.blockQ_isPGroup L)
    have hbS : b ∈ R1 S L := by
      refine ⟨(hQT hbQ).1, ?_⟩
      exact Subgroup.le_normalizer hbL
    have hbY : b ∈ Y₁ := ⟨hRX hbS, hbL⟩
    have : l = a * b := hab
    rw [this]
    exact Y₁.mul_mem ha hbY
  have hlt : (Y₁ ⊔ Y₂) ⊔ S < H := by
    refine lt_of_le_of_ne (sup_le (hN'K.trans ?_) D.hcs.sylow.le) fun h => hLnot ?_
    · rw [D.hcs.eq_join]; exact le_sup_left
    · rw [h]; exact C56.le_H D.hcs
  have hM := D.hcs.maxInf _ le_sup_right hlt
  intro x hx
  obtain ⟨r, hr, l, hl, rfl⟩ := hXdec x hx
  exact hM ((Y₁ ⊔ Y₂ ⊔ S).mul_mem (le_sup_right (a := Y₁ ⊔ Y₂) (R1_le_S hr))
    (le_sup_left (b := S) (le_sup_left (b := Y₂) hl)))

theorem isMinimalParabolic : IsMinimalParabolic (R1 S L) (H1 S L) := by
  refine ⟨D.isSylowTwoOf_R1_H1, D.not_le_normalizer_R1, H1 S L ⊓ M,
    le_inf R1_le_H1 (R1_le_S.trans D.S_le_M), ?_,
    fun X hRX hX => le_inf hX.le (D.unique_max hRX hX)⟩
  refine lt_of_le_of_ne inf_le_left fun h => D.hcs.not_le ?_
  intro l hl
  have hl' : l ∈ H1 S L ⊓ M := by rw [h]; exact L_le_H1 hl
  exact hl'.2

theorem isChi0Block_H1 : IsChi0Block (H1 S L) L :=
  ⟨⟨D.hL, L_le_H1,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer L_le_H1).mpr H1_le_normalizer_L).isSubnormal⟩,
    Or.inl ⟨n, by have := D.hn; omega, D.hlin⟩⟩

theorem isMaxElemAbelian_R1_iff {A : Subgroup G} :
    IsMaxElemAbelian (R1 S L) A ↔ IsMaxElemAbelian S A := by
  constructor
  · rintro ⟨hAR, hAe, hmax⟩
    refine ⟨hAR.trans R1_le_S, hAe, fun B hBS hBe => ?_⟩
    obtain ⟨B₀, hB₀⟩ := GammaExtra.exists_isMaxElemAbelian S
    have hB₀R : B₀ ≤ R1 S L := (GammaExtra.le_thompsonJ hB₀).trans D.thompsonJ_le_R1
    exact (hB₀.2.2 B hBS hBe).trans (hmax B₀ hB₀R hB₀.2.1)
  · intro hA
    exact ⟨(GammaExtra.le_thompsonJ hA).trans D.thompsonJ_le_R1, hA.2.1,
      fun B hBR hBe => hA.2.2 B (hBR.trans R1_le_S) hBe⟩

theorem thompsonJ_R1 : thompsonJ (R1 S L) = thompsonJ S := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => ?_
    exact le_iSup₂_of_le A (D.isMaxElemAbelian_R1_iff.1 hA) le_rfl
  · refine iSup₂_le fun A hA => ?_
    exact le_iSup₂_of_le A (D.isMaxElemAbelian_R1_iff.2 hA) le_rfl

theorem baum_R1 : baum (R1 S L) = baum S ⊓ R1 S L := by
  unfold baum
  rw [D.thompsonJ_R1]
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hR, hC⟩
    exact ⟨⟨R1_le_S hR, hC⟩, hR⟩
  · rintro ⟨⟨-, hC⟩, hR⟩
    exact ⟨hR, hC⟩

theorem thompson_R1 : ⁅L, thompsonJ (R1 S L)⁆ = L := by
  rw [D.thompsonJ_R1]
  exact D.hcs.thompson

end Dbl

end CFSG.QuasithinUnique.AppE
