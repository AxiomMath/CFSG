module

import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ
public import CFSG.GH74.GLS.C3.Layer1.EvenSE413
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RJ
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

namespace Frame39

variable {x y : G} {K T V W S P₀ : Subgroup G} {f z a f₁ : G}
  (F : Frame39 x y K T V W f z S a P₀ f₁)

include F

section Fin

variable [Finite G]

theorem false_of_third (h38 : B_thm1_L38_rel) (h3rd : B_thm1_L39_third_rel)
    (hL32 : B_thm1_L32'_rel) (hG : C3Hyp G) (hN : NoV2Fine G)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5))
    (hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hKnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z)
    (hlt : layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁) < pumpJ K f₁)
    {w₁ : G} (hw₁ : Is2TerminalU2Triple f₁ w₁ (pumpJ K f₁))
    (h5J : ¬ HasL2Model (kBar (pumpJ K f₁)) (fun q => q = 5))
    (hcard : Nat.card (kBar (pumpJ K f₁)) = Nat.card (kBar K)) : False := by
  have cfg2 := F.cfg₂
  obtain ⟨hJc, hJn, r, hrodd, -, hI, -⟩ := hL32 G hG hN x y K f₁ cfg2.fmax h5
  obtain ⟨x₃, hconj, hmem₃⟩ := h3rd G hG hN x y K T (v₁ T f a) S f₁ z cfg2 hlt w₁ hw₁ hcard hnotA7 h5
  have hCN : centralizer ({f₁} : Set G) ≤ normalizer ((pumpJ K f₁ : Subgroup G) : Set G) :=
    fun c hc => Thm1L3.mem_normalizer_of_conj_le (hJn c hc)
  have hNxK : NxK f₁ (pumpJ K f₁) = centralizer ({f₁} : Set G) := by
    unfold NxK
    exact inf_eq_left.2 hCN
  have hset : Setup1D f₁ (pumpJ K f₁) (v₁ T f a) :=
    ⟨cfg2.sylowV, by rw [hNxK, inf_eq_left.2 F.v₁_le_C]; exact cfg2.sylowV⟩
  have hCT : IsPGroup 2 ↥(v₁ T f a ⊓ centralizer ({x₃} : Set G)) :=
    cfg2.sylowV.isPGroup.to_inf_left
  obtain ⟨V'', hV''le, hV''N, hV''p, hV''idx⟩ :=
    P34.exists_sylow_ge (N := centralizer ({x₃} : Set G)) inf_le_right hCT
  have hV'' : IsSylowOf 2 V'' (centralizer ({x₃} : Set G)) :=
    isSylowOf_iff.2 ⟨hV''N, hV''p, hV''idx⟩
  obtain ⟨W'', hW''le, -, hW''p, hW''idx⟩ :=
    P34.exists_sylow_ge (N := (⊤ : Subgroup G)) le_top hV''.isPGroup
  have hW'' : IsSylowOf 2 W'' ⊤ := isSylowOf_iff.2 ⟨le_top, hW''p, hW''idx⟩
  have hcen : twoPartCard (centralizer ({x₃} : Set G)) = Nat.card ↥T := by
    have h1 : Nat.card ↥(centralizer ({x} : Set G)) = Nat.card ↥(centralizer ({x₃} : Set G)) :=
      card_centralizer_eq_of_isConj' hconj
    have h2 := F.cfg.setup.sylowT.card_eq
    unfold twoPartCard
    rw [← h1]
    exact h2.symm
  have hF3 : FMax3 f₁ w₁ (pumpJ K f₁) x₃ := by
    have hfu : IsFU2 f₁ w₁ (pumpJ K f₁) x₃ := ⟨hw₁, v₁ T f a, hset, hmem₃⟩
    have hF1 : FMax1 f₁ w₁ (pumpJ K f₁) x₃ := ⟨hfu, fun x' y' K' f' h' => by
      rw [hcard]
      exact F.cfg.fmax.1.1.2 x' y' K' f' h'⟩
    have hF2 : FMax2 f₁ w₁ (pumpJ K f₁) x₃ := ⟨hF1, fun x' y' K' f'' h' => by
      rw [F.twoPart_f₁]
      have h1 := F.cfg.fmax.1.2 x' y' K' f'' h'
      have h2 : twoPartCard (centralizer ({x} : Set G)) = Nat.card ↥T :=
        F.cfg.setup.sylowT.card_eq.symm
      omega⟩
    refine ⟨hF2, fun x' y' K' f'' h' => ?_⟩
    have h1 := F.cfg.fmax.2 x' y' K' f'' h'
    rw [F.twoPart_f] at h1
    rw [hcen]
    exact h1.trans F.hle
  have hPsyl : IsSylowOf 2 (T ⊓ K) K :=
    F.cfg.setup.sylowT.inf_of_le_normalizer F.cfg.hKx
      (fun c hc => Thm1L3.mem_normalizer_of_conj_le (hKnorm c hc))
  have hzJ : z ∈ layerI K f₁ :=
    Thm1.z_mem_layerI hPsyl F.isFMember_f₁.2.2.1 hI hrodd hzu
  have hz₃ : z ∈ v₁ T f a ⊓ pumpJ K f₁ ∧ orderOf z = 2 ∧ ∀ t ∈ v₁ T f a, t * z = z * t := by
    have hzc : v₁ T f a ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun c hc => mem_centralizer_singleton_iff.2 (F.cfg.z_mem.2.2 c hc.1))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 F.haz)))
    have hzV : z ∈ v₁ T f a := Subgroup.mem_sup_left
      ⟨F.cfg.z_mem.1.1, mem_centralizer_singleton_iff.2 (F.cfg.mem.2.2.1 z F.cfg.z_mem.1).symm⟩
    exact ⟨⟨hzV, Thm1.layerI_le_pumpJ K f₁ hzJ⟩, F.cfg.z_mem.2.1,
      fun t ht => mem_centralizer_singleton_iff.1 (hzc ht)⟩
  have cfg3 : Cfg3 f₁ w₁ (pumpJ K f₁) (v₁ T f a) V'' W'' x₃ z :=
    { fmax := hF3
      setup := hset
      mem := hmem₃
      z_mem := hz₃
      sylowV := hV''
      CTf_le := fun t ht hc => hV''le ⟨ht, mem_centralizer_singleton_iff.2 hc.symm⟩
      sylowW := hW''
      V_le_W := hW''le }
  have hVW : V'' ≠ W'' := by
    intro h
    have h1 : Nat.card ↥V'' = Nat.card ↥T := by
      rw [hV''.card_eq]
      exact hcen
    have h2 : Nat.card ↥W'' = Nat.card ↥S := by rw [hW''.card_eq, F.hS.card_eq]
    have h3 : Nat.card ↥T < Nat.card ↥S :=
      lt_of_le_of_ne (Subgroup.card_le_of_le F.hTS)
        (fun h => F.hTne (Subgroup.eq_of_le_of_card_ge F.hTS h.ge))
    have h4 : Nat.card ↥V'' = Nat.card ↥W'' := by rw [h]
    omega
  obtain ⟨a₃, ha₃S, ha₃N, ha₃T, ha₃2⟩ := exists_a₀ F.hS.isPGroup F.v₁_le_S F.v₁_ne_S
  obtain ⟨-, ⟨hPgen₃, hnn₃⟩, -⟩ := h38 G hG hN f₁ w₁ (pumpJ K f₁) (v₁ T f a) V'' W'' x₃ z cfg3
    hVW S a₃ F.hS F.v₁_le_S ha₃S ha₃N ha₃T ha₃2 h5J
  have hrankG : CFSG.pRank 2 G = 4 := hG.pRank_eq_four
  have hrankC : CFSG.pRank 2 ↥(centralizer ({x} : Set G)) = 4 := by
    rw [← hrankG]
    exact F.cfg.hu2.2.2.1.2
  have hJJ : thompsonJ2 T ≤ thompsonJ2 (v₁ T f a) :=
    thompsonJ2_le_thompsonJ2 F.J_le_v₁ (exists_ea_card_sixteen F.cfg.setup.sylowT hrankC)
      (fun B hB => card_le_sixteen_of_pRank hrankG hB)
  have hPP : T ⊓ K ≤ v₁ T f a ⊓ pumpJ K f₁ := by
    rw [F.hPgen, hPgen₃]
    exact closure_mono fun u hu => ⟨hJJ hu.1, hu.2⟩
  have hP'syl : IsSylowOf 2 (v₁ T f a ⊓ pumpJ K f₁) (pumpJ K f₁) :=
    cfg2.sylowV.inf_of_le_normalizer hJc.1 hCN
  have hPcard : Nat.card ↥(v₁ T f a ⊓ pumpJ K f₁) = Nat.card ↥(T ⊓ K) := by
    have h1 : Nat.card ↥(T ⊓ K) = twoPartCard K := hPsyl.card_eq
    have h2 : Nat.card ↥(v₁ T f a ⊓ pumpJ K f₁) = twoPartCard (pumpJ K f₁) := hP'syl.card_eq
    rw [h1, h2, Th2.L625.twoPartCard_eq_of_card_kBar (pumpJ K f₁) rfl,
      Th2.L625.twoPartCard_eq_of_card_kBar K rfl, hcard]
  have hPeq : T ⊓ K = v₁ T f a ⊓ pumpJ K f₁ := Subgroup.eq_of_le_of_card_ge hPP hPcard.le
  refine hnn₃ P₀ (by rw [← hPeq]; exact F.hP₀) fun t ht p hp => ?_
  exact (Subgroup.mem_normalizer_iff.1 (F.v₁_le_normalizer ht) p).1 hp

end Fin

end Frame39

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
