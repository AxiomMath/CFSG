module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoRoot
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRankSix

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo)
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type*} [Group G] {t : G}

theorem range_diagonalHom_le_of_le {A B : Subgroup G} (hBA : B ≤ A)
    (hA : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hB : ⁅B, B.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom B t hB).range ≤ (Common.diagonalHom A t hA).range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b, hBA b.2⟩, rfl⟩

theorem range_diagonalHom_sup_le {B C : Subgroup G}
    (hA : ⁅B ⊔ C, (B ⊔ C).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hB : ⁅B, B.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hC : ⁅C, C.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (B ⊔ C) t hA).range ≤
      (Common.diagonalHom B t hB).range ⊔ (Common.diagonalHom C t hC).range := by
  have hle : B ⊔ C ≤ (((Common.diagonalHom B t hB).range ⊔
      (Common.diagonalHom C t hC).range).comap (Common.diagonalHom (B ⊔ C) t hA)).map
        (B ⊔ C).subtype :=
    sup_le (fun b hb => ⟨⟨b, mem_sup_left hb⟩, mem_sup_left ⟨⟨b, hb⟩, rfl⟩, rfl⟩)
      (fun c hc => ⟨⟨c, mem_sup_right hc⟩, mem_sup_right ⟨⟨c, hc⟩, rfl⟩, rfl⟩)
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb, hba⟩ := hle a.2
  rw [show b = a from Subtype.ext hba] at hb
  exact hb

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓻₂" => miyamotoR2G h L η

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚


theorem range_diagonalHom_eq_A2G_sup_N2G [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    (Common.diagonalHom D t hcomm).range = miyamotoA2G h L η ⊔ miyamotoN2G h L η := by
  have : CharP K 2 := h.charP
  refine le_antisymm hδ ?_
  rw [miyamotoA2G_sup_N2G_eq, MonoidHom.range_eq_map]
  exact sup_le ((hS.PG_le_map_diagonalHom hk hψA hψt hZ hWD hcomm hinf).trans (map_mono le_top))
    ((hS.inf_le_map_diagonalHom_V2' hk hψt hZ hWD hr₂ hcomm hinf).trans (map_mono le_top))

theorem commutator_D_self [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    ⁅D, D⁆ = D := by
  have : CharP K 2 := h.charP
  have hrange := hS.range_diagonalHom_eq_A2G_sup_N2G hk hψA hψt hZ hWD hr₂ hcomm hinf hδ
  refine le_antisymm ?_ (le_of_range_diagonalHom_le hcomm hinf ?_)
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc (Common.diagonalHom D t hcomm).range =
          ⁅(Common.diagonalHom D t hcomm).range, (Common.diagonalHom D t hcomm).range⁆ := by
          rw [hrange, commutator_miyamotoA2G_sup_N2G h L η hS.two_le]
      _ ≤ _ := by
          rw [commutator_le]
          rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
          exact ⟨⁅a, b⁆, commutator_mem_commutator a.2 b.2, map_commutatorElement _ _ _⟩

theorem D_le_centralizer_map_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    D ≤ centralizer (((𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) :
      Set G) := by
  have hmain := hS.map_conj_D_le_centralizer_K1' hk hψA hψt hZ hWD hr₂ hcomm hinf hδ
  have ht := hS.t_mul_t
  intro d hd
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have h1 := mem_centralizer_iff.1 (hmain (Common.conj_mem_map_conj_inv t hd)) x hx
  rw [hS.t_inv] at h1 ⊢
  calc t * x * t * d = t * (x * (t * d * t)) * t := by
        rw [show t * (x * (t * d * t)) * t = t * x * t * d * (t * t) by group, ht, mul_one]
    _ = t * (t * d * t * x) * t := by rw [h1]
    _ = (t * t) * d * (t * x * t) := by group
    _ = d * (t * x * t) := by rw [ht, one_mul]

theorem commutator_G1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    ⁅𝓚 ⊔ D, (𝓚 ⊔ D).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [Subgroup.map_sup, commutator_eq_bot_iff_le_centralizer]
  refine sup_le (le_centralizer_iff.2 (sup_le ?_ ?_)) (le_centralizer_iff.2 (sup_le ?_ ?_))
  · exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1
      (hS.commutator_K1'_map_conj_inv hk hψA hψt))
  · exact hS.map_conj_D_le_centralizer_K1' hk hψA hψt hZ hWD hr₂ hcomm hinf hδ
  · exact le_centralizer_iff.1 (hS.D_le_centralizer_map_K1' hk hψA hψt hZ hWD hr₂ hcomm hinf hδ)
  · exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm)

theorem range_diagonalHom_G1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η)
    (hc : ⁅𝓚 ⊔ D, (𝓚 ⊔ D).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (𝓚 ⊔ D) t hc).range = L := by
  have : CharP K 2 := h.charP
  have hcK := hS.commutator_K1'_map_conj_inv hk hψA hψt
  have hK := hS.range_diagonalHom_K1' hk hψA hψt hZ hcK
  have hD := hS.range_diagonalHom_eq_A2G_sup_N2G hk hψA hψt hZ hWD hr₂ hcomm hinf hδ
  refine le_antisymm ((range_diagonalHom_sup_le hc hcK hcomm).trans ?_)
    ((miyamoto_generationG h L η).ge.trans (sup_le ?_ ?_))
  · rw [hK, hD]
    exact sup_le (sup_le (miyamotoPull_le h L η _) (miyamotoPull_le h L η _))
      (sup_le (miyamotoPull_le h L η _) (miyamotoPull_le h L η _))
  · exact hK.ge.trans (range_diagonalHom_le_of_le le_sup_left hc hcK)
  · exact hD.ge.trans (range_diagonalHom_le_of_le le_sup_right hc hcomm)

theorem false_of_D [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    False := by
  have hc := hS.commutator_G1 hk hψA hψt hZ hWD hr₂ hcomm hinf hδ
  have hperf : ⁅𝓚 ⊔ D, 𝓚 ⊔ D⁆ = 𝓚 ⊔ D := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rw [commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · calc 𝓚 = ⁅𝓚, 𝓚⁆ := (hS.commutator_K1' hk hψA hψt hZ).symm
        _ ≤ _ := commutator_mono le_sup_left le_sup_left
    · calc D = ⁅D, D⁆ := (hS.commutator_D_self hk hψA hψt hZ hWD hr₂ hcomm hinf hδ).symm
        _ ≤ _ := commutator_mono le_sup_right le_sup_right
  have hE : miyamotoEG h L η Q ≤ (𝓚 ⊔ D) ⊔ (𝓚 ⊔ D).map (MulAut.conj t⁻¹).toMonoidHom := by
    refine hS.E_le_F1.trans ((hS.sec5_1_one hk hψt hZ).2.1.le.trans (sup_le ?_ ?_))
    · refine le_sup_of_le_right ?_
      rw [hS.t_inv]
      calc (𝓨 : Subgroup G) = (𝓨t : Subgroup G).map (MulAut.conj t).toMonoidHom :=
            (map_conj_map_conj_of_mul_self hS.t_mul_t _).symm
        _ ≤ _ := map_mono (le_sup_left.trans le_sup_left)
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (hS.E_inf_Yt_ne_bot hk hψA hψt hZ)
  obtain ⟨hzE, hzY⟩ := mem_inf.1 hz
  refine hS.false_of_diagonal_swap_of_E hperf hc
    (hS.range_diagonalHom_G1 hk hψA hψt hZ hWD hr₂ hcomm hinf hδ hc) hE
    (mem_sup_left (mem_sup_left hzY)) (fun hzC => hz1 (Subtype.ext ?_)) hzE
  have hzK : z ∈ 𝓚 ⊓ centralizer ((𝓚 : Subgroup G) : Set G) :=
    mem_inf.2 ⟨mem_sup_left hzY, centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hzC⟩
  rw [hS.K1'_inf_centralizer hk hψA hψt hZ, mem_bot] at hzK
  exact hzK

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
