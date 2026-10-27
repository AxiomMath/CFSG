module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoThree

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)
open scoped MatrixGroups Pointwise

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨


theorem RG_le_normalizer_Yt [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    miyamotoRG h L η t Q ≤ normalizer ((𝓨t : Subgroup G) : Set G) := by
  intro r hr
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  refine mul_mem ?_ (hS.le_normalizer_of_le_F1 hS.Yt_le_F1 le_rfl hy)
  rw [← (hS.W_eq_sup (ψ := ψ) hk).1] at hw
  have hle : (𝓦 ⊓ prodFactorOne ψ) ⊔ (𝓦 ⊓ prodFactorTwo ψ) ≤
      normalizer ((𝓨t : Subgroup G) : Set G) :=
    sup_le (fun x hx => hS.X1_le_normalizer_Yt hψt (mem_inf.1 hx).2) fun x hx =>
      mem_normalizer_of_mem_centralizer' (hS.X2_le_centralizer_Yt hk hψA hψt (mem_inf.1 hx).2)
  exact hle hw

theorem E_inf_Yt_ne_bot [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoEG h L η Q ⊓ 𝓨t ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := miyamotoRG h L η t Q with hRdef
  have hYtR : (𝓨t : Subgroup G) ≤ R :=
    hS.Yt_le_F1.trans (le_sup_left.trans hS.P1_le_miyamotoRG)
  have hN : ((𝓨t : Subgroup G).subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYtR).2 (hS.RG_le_normalizer_Yt hk hψA hψt)
  have : Group.IsNilpotent R := hS.isPGroup_RG.isNilpotent
  have hne : (𝓨t : Subgroup G).subgroupOf R ≠ ⊥ := by
    intro h0
    apply hS.Y_ne_bot hZ
    have hYt0 : (𝓨t : Subgroup G) = ⊥ := by
      have := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h0)
      rwa [inf_eq_left.2 hYtR] at this
    have e := map_conj_map_conj_of_mul_self hS.t_mul_t (𝓨 : Subgroup G)
    rw [hYt0, Subgroup.map_bot] at e
    exact e.symm
  obtain ⟨⟨⟨x, hxR⟩, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hxY, hxZ⟩ := mem_inf.1 hx
  have hxE : x ∈ miyamotoEG h L η Q := by
    rw [← hS.centerIn_RG]
    refine mem_inf.2 ⟨hxR, mem_centralizer_iff.2 fun r hr => ?_⟩
    have := congrArg Subtype.val (mem_center_iff.1 hxZ ⟨r, hr⟩)
    exact this
  refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨x, mem_inf.2 ⟨hxE, hxY⟩⟩, fun e => hx1 ?_⟩
  have e' : x = 1 := congrArg Subtype.val e
  subst e'
  rfl

theorem F1_inf_K1' (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    miyamotoF1G h L η t ⊓ (𝓨t ⊔ prodFactorOne ψ) = 𝓨t := by
  refine le_antisymm (fun z hz => ?_) (le_inf hS.Yt_le_F1 le_sup_left)
  obtain ⟨hzF, hzK⟩ := mem_inf.1 hz
  have e1 : ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) =
      ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (hS.X1_le_normalizer_Yt hψt)
  have hz' : z ∈ ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) := by
    rw [← e1]; exact hzK
  obtain ⟨a, ha, x, hx, rfl⟩ := hz'
  have hxF : x ∈ miyamotoF1G h L η t := by
    have := mul_mem (inv_mem (hS.Yt_le_F1 ha)) hzF
    simpa using this
  have hx1 : x = 1 := by
    have := mem_inf.2 ⟨hxF, hS.M1_le_centralizer_I1 (Common.prodFactorOne_le ψ hx)⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  simp only [hx1, mul_one]
  exact ha

theorem mem_centralizer_K1'_of_mem_J2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    (hJV : miyamotoJ2G h L η t Q ≤
      normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :
        Subgroup G) : Set G))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hjX : j ∈ centralizer (prodFactorOne ψ : Set G)) :
    j ∈ centralizer ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) := by
  obtain ⟨hJE, -, -, hJF1, -, -, -⟩ := hS.J2_le hJV
  have hjX' : j ∈ normalizer (prodFactorOne ψ : Set G) := mem_normalizer_of_mem_centralizer' hjX
  have hjK : j ∈ normalizer ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) := by
    rw [← hS.commutator_K1 hk hψA hψt hZ]
    have hjK1 := mem_normalizer_sup (hJF1 hj) hjX'
    exact mem_normalizer_commutator hjK1 hjK1
  have hjY : j ∈ normalizer ((𝓨t : Subgroup G) : Set G) := by
    rw [← hS.F1_inf_K1' hψt]
    exact mem_normalizer_inf (hJF1 hj) hjK
  set V₀ := (𝓨t : Subgroup G) ⊓ centralizer ({j} : Set G) with hV₀
  have hKV : miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤ normalizer (V₀ : Set G) := by
    refine sup_le (hS.le_normalizer_of_le_F1 (inf_le_left.trans hS.Yt_le_F1) le_rfl) ?_
    intro x hx
    refine mem_normalizer_inf (hS.X1_le_normalizer_Yt hψt hx) (le_normalizer ?_)
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hjX x hx)
  rcases (hS.sec5_1_two hk hψA hψt hZ).2 V₀ inf_le_left hKV with h0 | h1
  · exfalso
    apply hS.E_inf_Yt_ne_bot hk hψA hψt hZ
    refine eq_bot_iff.2 fun e he => ?_
    rw [← h0]
    refine mem_inf.2 ⟨(mem_inf.1 he).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact mem_centralizer_iff.1 (hJE hj) e (mem_inf.1 he).1
  · have hYC : (𝓨t : Subgroup G) ≤ centralizer ({j} : Set G) := by
      rw [← h1]; exact inf_le_right
    have hle : 𝓨t ⊔ prodFactorOne ψ ≤ centralizer ({j} : Set G) := by
      refine sup_le hYC fun x hx => ?_
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hjX x hx)
    exact mem_centralizer_iff.2 fun y hy => (mem_centralizer_singleton_iff.1 (hle hy))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
