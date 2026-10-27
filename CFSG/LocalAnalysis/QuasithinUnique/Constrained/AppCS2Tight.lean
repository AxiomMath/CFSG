module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Max

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem offender_tight (P : PiData L) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAS₁ : A ≤ s2SI S L) (hAP : Nat.card ↥(pCoreOf 2 H) ≤ Nat.card A) :
    Nat.card A * Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) =
      16 * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := by
  have h1 := one_block P hA (hAS₁.trans s2SI_le_normalizer)
  have h2 := D.one_block_conj P hA hAS₁
  have hf := D.card_cent_U0_le hAS₁
  have hga := D.aU_spec P hA hAS₁
  set K₁ := A ⊓ centralizer (blockU L : Set G) with hK₁
  set K₂ := A ⊓ centralizer (blockU2 L t : Set G) with hK₂
  set K := A ⊓ centralizer ((U0 L t : Subgroup G) : Set G) with hK
  have hKeq : K₁ ⊓ K₂ = K := by
    rw [hK₁, hK₂, hK, D.centralizer_U0]
    ext y
    simp only [Subgroup.mem_inf]
    tauto
  have hcommK : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hA ha.1 hb.1
  have h3 := B2F.card_sup_mul_card_inf_of_commute hcommK
  rw [hKeq] at h3
  have h4 : Nat.card ↥(K₁ ⊔ K₂) ≤ Nat.card A :=
    Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hk : Nat.card ↥K₁ * Nat.card ↥K₂ ≤ Nat.card A * Nat.card ↥K := by
    rw [← h3]
    exact Nat.mul_le_mul_right _ h4
  have hcomm : ∀ k ∈ K, ∀ u ∈ U0 L t, k * u = u * k := fun k hk' u hu =>
    (Subgroup.mem_centralizer_iff.1 hk'.2 u hu).symm
  have h5 := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [D.card_U0 P] at h5
  have hKP : Nat.card ↥(K ⊔ U0 L t) ≤ Nat.card ↥(pCoreOf 2 H) := Subgroup.card_le_of_le hga.2.2.1
  have h6 : Nat.card ↥(K ⊓ U0 L t) ≤ Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun y hy => ⟨hy.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hy.1.1
  set a := Nat.card A
  set f₁ := Nat.card ↥(blockU L ⊓ centralizer (A : Set G))
  set f₂ := Nat.card ↥(blockU2 L t ⊓ centralizer (A : Set G))
  set f₀ := Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G))
  set k₁ := Nat.card ↥K₁
  set k₂ := Nat.card ↥K₂
  set k := Nat.card ↥K
  set c := Nat.card ↥(K ⊔ U0 L t)
  set b := Nat.card ↥(K ⊓ U0 L t)
  set p := Nat.card ↥(pCoreOf 2 H)
  have hapos : 0 < a := Nat.card_pos
  have hf₁pos : 0 < f₁ := Nat.card_pos
  have hf₂pos : 0 < f₂ := Nat.card_pos
  have hkpos : 0 < k := Nat.card_pos
  have e1 : k * 256 ≤ a * (f₁ * f₂) := by
    calc k * 256 = c * b := h5.symm
      _ ≤ p * b := Nat.mul_le_mul_right _ hKP
      _ ≤ a * b := Nat.mul_le_mul_right _ hAP
      _ ≤ a * f₀ := Nat.mul_le_mul_left _ h6
      _ ≤ a * (f₁ * f₂) := Nat.mul_le_mul_left _ hf
  have e2 : a * (f₁ * f₂) ≤ 256 * k := by
    have h7 : (a * f₁) * (a * f₂) ≤ (16 * k₁) * (16 * k₂) := Nat.mul_le_mul h1 h2
    have h8 : a * (a * (f₁ * f₂)) ≤ a * (256 * k) := by
      calc a * (a * (f₁ * f₂)) = (a * f₁) * (a * f₂) := by ring
        _ ≤ (16 * k₁) * (16 * k₂) := h7
        _ = 256 * (k₁ * k₂) := by ring
        _ ≤ 256 * (a * k) := Nat.mul_le_mul_left _ hk
        _ = a * (256 * k) := by ring
    exact Nat.le_of_mul_le_mul_left h8 hapos
  have e3 : a * (f₁ * f₂) = 256 * k := le_antisymm e2 (by linarith)
  have e4 : (a * f₁) * (a * f₂) = (16 * k₁) * (16 * k₂) := by
    have h9 : 256 * (k₁ * k₂) ≤ 256 * (a * k) := Nat.mul_le_mul_left _ hk
    have h10 : (a * f₁) * (a * f₂) = a * (a * (f₁ * f₂)) := by ring
    have h11 : (16 * k₁) * (16 * k₂) = 256 * (k₁ * k₂) := by ring
    have h12 : (a * f₁) * (a * f₂) ≤ (16 * k₁) * (16 * k₂) := Nat.mul_le_mul h1 h2
    have h13 : a * (a * (f₁ * f₂)) = a * (256 * k) := by rw [e3]
    have h14 : a * (256 * k) = 256 * (a * k) := by ring
    omega
  by_contra hne
  have hlt : a * f₁ < 16 * k₁ := lt_of_le_of_ne h1 hne
  have hpos2 : 0 < a * f₂ := Nat.mul_pos hapos hf₂pos
  have : (a * f₁) * (a * f₂) < (16 * k₁) * (a * f₂) := Nat.mul_lt_mul_of_pos_right hlt hpos2
  have : (16 * k₁) * (a * f₂) ≤ (16 * k₁) * (16 * k₂) := Nat.mul_le_mul_left _ h2
  omega

end Dbl

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem blockD_comm_baum {c b : G} (hc : c ∈ blockD S L) (hb : b ∈ baum S) : c * b = b * c := by
  have hD := X.C.D
  obtain ⟨w₁, hw₁, w₂, hw₂, d, hd, rfl⟩ := X.B_decomp hb
  have h1 : ∀ w ∈ blockU L ⊔ conjR (blockU L) x, w * c = c * w :=
    fun w hw => comm_sup_left (A₁ := blockU L) (A₂ := conjR (blockU L) x) (B := blockD S L)
      (fun a ha b hb => blockD_comm_L hb (hD.blockU_le_L ha))
      (fun a ha b hb => (X.blockD_comm_V₁ hb ha).symm) w hw c hc
  have h2 : ∀ w ∈ blockU2 L t ⊔ conjR (blockU2 L t) x, w * c = c * w :=
    fun w hw => comm_sup_left (A₁ := blockU2 L t) (A₂ := conjR (blockU2 L t) x) (B := blockD S L)
      (fun a ha b hb => hD.blockD_comm_L₂ hb (hD.blockU2_le_L₂ ha))
      (fun a ha b hb => (X.blockD_comm_V₂ hb ha).symm) w hw c hc
  have hdD : d ∈ blockD S L := by rwa [X.baumD_eq_blockD] at hd
  have h3 : d * c = c * d :=
    (B2F.isElemAbelian_comm X.blockD_isElemAbelian hdD hc)
  have c1 : Commute c w₁ := (h1 w₁ hw₁).symm
  have c2 : Commute c w₂ := (h2 w₂ hw₂).symm
  have c3 : Commute c d := h3.symm
  exact ((c1.mul_right c2).mul_right c3).eq

theorem le_baum_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ baum S := by
  have := GammaExtra.le_thompsonJ hA
  rwa [X.thompsonJ_eq_baum] at this

theorem card_eq_pCoreOf {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    Nat.card A = Nat.card ↥(pCoreOf 2 H) :=
  le_antisymm (X.pCoreOf_isMax.2.2 A hA.1 hA.2.1)
    (hA.2.2 _ X.C.D.Q_le_S X.pCoreOf_isElemAbelian)

end Two

end CFSG.QuasithinUnique.AppCS2
