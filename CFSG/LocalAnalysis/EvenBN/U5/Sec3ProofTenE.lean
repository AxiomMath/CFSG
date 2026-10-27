module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineSylow

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s4b1_card_sup_mul_card_inf_normal {α : Type*} [Group α] (A L : Subgroup α) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup α) * Nat.card (A ⊓ L : Subgroup α) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem s4b1_card_sup_mul_card_inf {α : Type*} [Group α] {A B : Subgroup α}
    (hB : B ≤ Subgroup.normalizer (A : Set α)) :
    Nat.card (A ⊔ B : Subgroup α) * Nat.card (A ⊓ B : Subgroup α) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set α)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := s4b1_card_sup_mul_card_inf_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup α, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem s4b1_card_sup_eq_mul {α : Type*} [Group α] {A B : Subgroup α}
    (hB : B ≤ Subgroup.normalizer (A : Set α)) (hAB : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup α) = Nat.card A * Nat.card B := by
  have h := s4b1_card_sup_mul_card_inf hB
  rw [hAB, Subgroup.card_bot, mul_one] at h
  exact h

theorem s4b1_eq_sup_of_card {α : Type*} [Group α] [Finite α] {S A B : Subgroup α}
    (hA : A ≤ S) (hB : B ≤ S) (hBn : B ≤ Subgroup.normalizer (A : Set α)) (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card S ≤ Nat.card A * Nat.card B) : S = A ⊔ B := by
  have hc := s4b1_card_sup_eq_mul hBn hAB
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hA hB) (by rw [hc]; exact hcard)).symm

theorem s4b1_le_normalizer_inf {α : Type*} [Group α] {S E D : Subgroup α}
    (hE : S ≤ Subgroup.normalizer (E : Set α)) (hD : S ≤ Subgroup.normalizer (D : Set α)) :
    S ≤ Subgroup.normalizer ((E ⊓ D : Subgroup α) : Set α) := by
  intro x hx
  have hxE := Subgroup.mem_normalizer_iff.1 (hE hx)
  have hxD := Subgroup.mem_normalizer_iff.1 (hD hx)
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact and_congr (hxE n) (hxD n)

theorem s4b1_card_inf_ED {α : Type*} [Group α] {q : ℕ} (hq : 0 < q)
    {S E D : Subgroup α} (hSED : S = E ⊔ D)
    (hS : Nat.card S = q ^ 20) (hE : Nat.card E = q ^ 14) (hD : Nat.card D = q ^ 16)
    (hDn : D ≤ Subgroup.normalizer (E : Set α)) :
    Nat.card (E ⊓ D : Subgroup α) = q ^ 10 := by
  have h := s4b1_card_sup_mul_card_inf hDn
  rw [← hSED, hS, hE, hD] at h
  have h2 : q ^ 20 * Nat.card (E ⊓ D : Subgroup α) = q ^ 20 * q ^ 10 := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq 20) h2

theorem s4b1_eq_sup_of_inf_card_le {α : Type*} [Group α] [Finite α] {q : ℕ} (hq : 0 < q)
    {X A B : Subgroup α} (hAX : A ≤ X) (hBX : B ≤ X)
    (hBn : B ≤ Subgroup.normalizer (A : Set α))
    (hXc : Nat.card X = q ^ 10) (hAc : Nat.card A = q ^ 6) (hBc : Nat.card B = q ^ 6)
    (hi : Nat.card (A ⊓ B : Subgroup α) ≤ q ^ 2) : X = A ⊔ B := by
  have hj := s4b1_card_sup_mul_card_inf hBn
  rw [hAc, hBc] at hj
  have hle : A ⊔ B ≤ X := sup_le hAX hBX
  have hcardX : Nat.card X ≤ Nat.card (A ⊔ B : Subgroup α) := by
    rw [hXc]
    by_contra hlt
    push_neg at hlt
    have h1 : Nat.card (A ⊔ B : Subgroup α) * Nat.card (A ⊓ B : Subgroup α) ≤
        Nat.card (A ⊔ B : Subgroup α) * q ^ 2 := Nat.mul_le_mul le_rfl hi
    have h2 : Nat.card (A ⊔ B : Subgroup α) * q ^ 2 < q ^ 10 * q ^ 2 :=
      mul_lt_mul_of_pos_right hlt (pow_pos hq 2)
    have h3 : q ^ 10 * q ^ 2 = q ^ 6 * q ^ 6 := by ring
    linarith
  exact (Subgroup.eq_of_le_of_card_ge hle hcardX).symm

theorem s4b1_le_normalizer_of_normal_map {α : Type*} [Group α] (S W : Subgroup α)
    (Z : Subgroup ↥S) (hZ : Z.Normal) (hW : Z.map S.subtype = W) :
    S ≤ Subgroup.normalizer (W : Set α) := by
  have hconj : ∀ x ∈ S, ∀ y ∈ W, x * y * x⁻¹ ∈ W := by
    intro x hx y hy
    rw [← hW] at hy ⊢
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, hZ.conj_mem z hz ⟨x, hx⟩, ?_⟩
    simp
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj x hx y, fun hxy => ?_⟩
  have h := hconj x⁻¹ (inv_mem hx) (x * y * x⁻¹) hxy
  simpa [mul_assoc] using h

theorem sec3101E_of_hyp (hp : d.CaseHyp) (k : d.Know93) (h2 : d.Sec3_10_two)
    (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hO : d.Sec3101Orders S)
    (ha : d.Sec3101A S) : d.Sec3101E S := by
  have hGMS := hp.gms
  have hd : d.Hyp := hp.hyp
  have h91 := k.s9_1 S hS hP
  have h92 := k.s9_2 S hS hP
  have h39a := k.s9a S hS hP
  have h39e := k.s9e
  have hSED : S = d.E ⊔ d.D := h91.1
  have hEchar : (d.E.subgroupOf S).Characteristic := h91.2.1
  have hDchar : (d.D.subgroupOf S).Characteristic := h91.2.2
  have hES : d.E ≤ S := by rw [hSED]; exact le_sup_left
  have hDS : d.D ≤ S := by rw [hSED]; exact le_sup_right
  have hEN : (d.E.subgroupOf S).Normal := by
    haveI := hEchar
    infer_instance
  have hDN : (d.D.subgroupOf S).Normal := by
    haveI := hDchar
    infer_instance
  have hSNE : S ≤ Subgroup.normalizer (d.E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hES).1 hEN
  have hSND : S ≤ Subgroup.normalizer (d.D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDS).1 hDN
  have hNZ : (Subgroup.upperCentralSeries (↥S) 2).Normal := inferInstance
  have hWS : S ≤ Subgroup.normalizer (d.W : Set G) :=
    s4b1_le_normalizer_of_normal_map S d.W (Subgroup.upperCentralSeries (↥S) 2) hNZ h92.2.1
  have hFD : d.F ≤ d.D := by
    have hc : CFSG.centerIn d.D = d.F := h92.2.2.2.1
    rw [← hc]
    exact inf_le_left
  have hWF : d.W ≤ d.F := hd.W_le_F hGMS
  have hWE : d.W ≤ d.E := d.W_le_E
  have hWED : d.W ≤ d.E ⊓ d.D := le_inf hWE (hWF.trans hFD)
  have hC4W : d.F ⊓ centralizer (d.I₄ : Set G) ≤ d.W := by
    rw [hd.W_eq hGMS]
    exact le_sup_right
  have hsN : d.s ∈ Subgroup.normalizer (d.E : Set G) := d.N₂_le_normalizer_E d.s_mem_N₂
  have hconjE : ∀ x : G, d.s * x * d.s ∈ d.E ↔ x ∈ d.E := by
    intro x
    have hk := Subgroup.mem_normalizer_iff.1 hsN x
    rw [d.s_inv] at hk
    exact hk.symm
  have hV₁E : d.V₁ ≤ d.E := fun x hx =>
    (hconjE x).1 (hWE (hC4W (mem_map_conj_s.1
      (show x ∈ (d.F ⊓ centralizer (d.I₄ : Set G)).map (MulAut.conj d.s).toMonoidHom from hx))))
  have hWsE : d.W.map (MulAut.conj d.s).toMonoidHom ≤ d.E :=
    fun x hx => (hconjE x).1 (hWE (mem_map_conj_s.1 hx))
  have hV₁Ws : d.V₁ ≤ d.W.map (MulAut.conj d.s).toMonoidHom := by
    show (d.F ⊓ centralizer (d.I₄ : Set G)).map (MulAut.conj d.s).toMonoidHom ≤ _
    exact Subgroup.map_mono hC4W
  have hEc : Nat.card d.E = (2 ^ f) ^ 14 := hd.card_E hGMS
  have hDc : Nat.card d.D = (2 ^ f) ^ 16 := h39e.card_D
  have hSc : Nat.card S = (2 ^ f) ^ 20 := hO.card_S
  have hWc : Nat.card d.W = (2 ^ f) ^ 6 := hd.card_W hGMS
  have hV₁c : Nat.card d.V₁ = (2 ^ f) ^ 4 := hd.card_V₁ hGMS
  have hq : 0 < 2 ^ f := by positivity
  have hEDc : Nat.card (d.E ⊓ d.D : Subgroup G) = (2 ^ f) ^ 10 :=
    s4b1_card_inf_ED hq hSED hSc hEc hDc (hDS.trans hSNE)
  have hC₁c : Nat.card (S ⊓ centralizer (d.I₁ : Set G) : Subgroup G) = (2 ^ f) ^ 4 := hO.c₁
  have hV₁I₁ : d.V₁ ≤ S ⊓ centralizer (d.I₁ : Set G) :=
    le_inf (hV₁E.trans hES) d.V₁_le_centralizer_I₁
  have hC₁eq : d.V₁ = S ⊓ centralizer (d.I₁ : Set G) :=
    Subgroup.eq_of_le_of_card_ge hV₁I₁ (le_of_eq (by rw [hC₁c, hV₁c]))
  have hC₁E : S ⊓ centralizer (d.I₁ : Set G) ≤ d.E := by
    rw [← hC₁eq]
    exact hV₁E
  have hEI₁ : (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₁ : Set G)) = ⊥ := by
    have h1 : (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₁ : Set G)) ≤
        d.D ⊓ centralizer (d.I₁ : Set G) :=
      inf_le_inf inf_le_right inf_le_right
    rw [h39e.centralizer_I₁] at h1
    exact eq_bot_iff.2 h1
  have hEsup : d.E = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₁ : Set G)) :=
    s4b1_eq_sup_of_card (S := d.E) (A := d.E ⊓ d.D) (B := S ⊓ centralizer (d.I₁ : Set G))
      inf_le_left hC₁E (inf_le_left.trans (s4b1_le_normalizer_inf hSNE hSND)) hEI₁
      (le_of_eq (by rw [hEc, hEDc, hC₁c]; ring))
  have hC₅c : Nat.card (S ⊓ centralizer (d.I₅ : Set G) : Subgroup G) = (2 ^ f) ^ 6 := hO.c₅
  have h39₅ : (2 ^ f) ^ 6 ≤ Nat.card (d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) :=
    hd.s39a1_card_centralizer_E hGMS
  have hC₅eq : d.E ⊓ centralizer (d.I₅ : Set G) = S ⊓ centralizer (d.I₅ : Set G) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf hES le_rfl) (by rw [hC₅c]; exact h39₅)
  have hC₅E : S ⊓ centralizer (d.I₅ : Set G) ≤ d.E := by
    rw [← hC₅eq]
    exact inf_le_left
  have hC₅D : S ⊓ centralizer (d.I₅ : Set G) ≤ d.D := by
    rw [← h39a.cD₅]
    exact inf_le_left
  have hC₅ED : S ⊓ centralizer (d.I₅ : Set G) ≤ d.E ⊓ d.D := le_inf hC₅E hC₅D
  have hWC₅F : d.W ⊓ (S ⊓ centralizer (d.I₅ : Set G)) ≤
      d.F ⊓ centralizer (d.I₅ : Set G) :=
    le_inf (inf_le_left.trans hWF) (inf_le_right.trans inf_le_right)
  have hi : Nat.card (d.W ⊓ (S ⊓ centralizer (d.I₅ : Set G)) : Subgroup G) ≤ (2 ^ f) ^ 2 :=
    (Subgroup.card_le_of_le hWC₅F).trans (le_of_eq hO.cF₅)
  have hEDeq : d.E ⊓ d.D = d.W ⊔ (S ⊓ centralizer (d.I₅ : Set G)) :=
    s4b1_eq_sup_of_inf_card_le hq hWED hC₅ED (inf_le_left.trans hWS) hEDc hWc hC₅c hi
  have hEJ : d.E = d.W ⊔ d.W.map (MulAut.conj d.s).toMonoidHom ⊔
      (S ⊓ centralizer (d.I₅ : Set G)) := by
    apply le_antisymm
    · refine le_trans (le_of_eq hEsup) (sup_le ?_ ?_)
      · rw [hEDeq]
        exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
      · rw [← hC₁eq]
        exact hV₁Ws.trans (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le hWE hWsE) hC₅E
  exact ⟨⟨hEsup, hEI₁⟩, hEJ, hEDeq⟩

end Data

namespace CaseBParts

theorem sec3101E : Sec3101EStatement :=
  fun _ _ _ _ _ _ _ _ hp k h2 S hS hP hO ha => Data.sec3101E_of_hyp hp k h2 S hS hP hO ha

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
