module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Clauses

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.U_le_normalizer_R : thompsonJ S ≤ Subgroup.normalizer (blockU L : Set G) :=
  (dat.R_le_L h).trans (le_normalizer_blockU L)

theorem Lin2Data.U_elem : IsElemAbelian 2 (blockU L) := by
  have := dat.Q_max.2.1
  rwa [dat.Q_eq_U h] at this

theorem Lin2Data.D₀_le_U : blockD S L ≤ blockU L := by
  rw [dat.D₀_eq_Z h]
  exact blockZ_le_blockU L

theorem Lin2Data.R_eq_U_sup {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    thompsonJ S = blockU L ⊔ conjR (blockU L) x := by
  rw [dat.R_eq x hx hxS, sup_eq_right.2 (dat.D₀_le_U h)]

theorem Lin2Data.R_le_normalizer_conjU {x : G} (hx : x ∈ T) :
    thompsonJ S ≤ Subgroup.normalizer ((conjR (blockU L) x : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjR_eq_self_iff]
  have hxR := dat.x_normalizer_R h hx
  have hg' : x * g * x⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 hxR g).1 hg
  have hU : x * g * x⁻¹ ∈ Subgroup.normalizer (blockU L : Set G) := dat.U_le_normalizer_R h hg'
  have e : x * g = (x * g * x⁻¹) * x := by group
  rw [conjR_conjR, e, conjR_mul, conjR_eq_of_mem_normalizer hU]

theorem Lin2Data.U_le_normalizer_conjU {x : G} (hx : x ∈ T) :
    blockU L ≤ Subgroup.normalizer ((conjR (blockU L) x : Subgroup G) : Set G) :=
  (dat.U_le_R h).trans (dat.R_le_normalizer_conjU h hx)

theorem Lin2Data.conjU_le_R {x : G} (hx : x ∈ T) : conjR (blockU L) x ≤ thompsonJ S := by
  calc conjR (blockU L) x ≤ conjR (thompsonJ S) x := conjR_mono (dat.U_le_R h) x
    _ = thompsonJ S := conjR_eq_of_mem_normalizer (dat.x_normalizer_R h hx)

theorem Lin2Data.not_conjU_le_U {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    ¬ conjR (blockU L) x ≤ blockU L := by
  intro hle
  have hR : thompsonJ S ≤ blockU L := by
    rw [dat.R_eq_U_sup h hx hxS]
    exact sup_le le_rfl hle
  have h1 : (pCoreOf 2 H).relIndex (thompsonJ S) = 1 := by
    rw [dat.Q_eq_U h]
    exact Subgroup.relIndex_eq_one.2 hR
  rw [dat.RQ_index] at h1
  have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.one_lt; omega)
  omega

theorem Lin2Data.exists_W {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    ∃ W : Subgroup G, W = blockU L ⊓ conjR (blockU L) x ∧
      (∀ y ∈ thompsonJ S, y ∉ blockU L → ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)) ∧
      Nat.card W * 2 ^ n = Nat.card (blockU L) ∧ W ≤ blockU L := by
  obtain ⟨W, hW1, hW2, hW3⟩ := dat.W_data
  have hQU := dat.Q_eq_U h
  have hWU : W ≤ blockU L := by
    rw [← hW1, Subgroup.commutator_le]
    intro u hu r hr
    have hr' := dat.U_le_normalizer_R h hr
    have : ⁅u, r⁆ = u * (r * u⁻¹ * r⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem _ hu ((Subgroup.mem_normalizer_iff.1 hr' u⁻¹).1 (Subgroup.inv_mem _ hu))
  have hcardW : Nat.card W * 2 ^ n = Nat.card (blockU L) := by
    have := Subgroup.relIndex_mul_card (H := W) (K := blockU L)
    rw [inf_eq_left.mpr hWU, hW2] at this
    rw [mul_comm]
    exact this
  have hW3' : ∀ y ∈ thompsonJ S, y ∉ blockU L → ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u) := by
    intro y hy hyU u hu
    exact hW3 y hy (by rw [hQU]; exact hyU) u hu
  have hex : ∃ y ∈ conjR (blockU L) x, y ∉ blockU L := by
    by_contra hcon
    push Not at hcon
    exact dat.not_conjU_le_U h hx hxS hcon
  obtain ⟨y₀, hy₀, hy₀U⟩ := hex
  have hUWle : blockU L ⊓ conjR (blockU L) x ≤ W := by
    rintro z ⟨hzU, hzU'⟩
    have hy₀R : y₀ ∈ thompsonJ S := dat.conjU_le_R h hx hy₀
    refine (hW3' y₀ hy₀R hy₀U z hzU).2 ?_
    have hE := isElemAbelian_conjR_iff (blockU L) x |>.2 (dat.U_elem h)
    exact IsElemAbelian.comm hE hzU' hy₀
  have hRcard : Nat.card (thompsonJ S) = 2 ^ n * Nat.card (blockU L) := by
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 H) (K := thompsonJ S)
    rw [inf_eq_left.mpr (dat.Q_le_R h), dat.RQ_index, hQU] at this
    exact this.symm
  have hc := card_sup_mul_card_inf (dat.U_le_normalizer_conjU h hx)
  rw [← dat.R_eq_U_sup h hx hxS, card_conjR, hRcard] at hc
  have hUpos : 0 < Nat.card (blockU L) := Nat.card_pos
  have hcard' : Nat.card (blockU L ⊓ conjR (blockU L) x : Subgroup G) = Nat.card W := by
    have h2n : 0 < 2 ^ n := by positivity
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos h2n hUpos)
    calc 2 ^ n * Nat.card (blockU L) * Nat.card (blockU L ⊓ conjR (blockU L) x : Subgroup G)
        = Nat.card (blockU L) * Nat.card (blockU L) := hc
      _ = 2 ^ n * Nat.card (blockU L) * Nat.card W := by
          rw [← hcardW]; ring
  have hWeq : W = blockU L ⊓ conjR (blockU L) x :=
    (Subgroup.eq_of_le_of_card_ge hUWle hcard'.ge).symm
  exact ⟨W, hWeq, hW3', hcardW, hWU⟩

end Clauses

end CFSG.QuasithinUnique.Lin2
