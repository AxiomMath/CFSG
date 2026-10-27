module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWACent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWZero

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def LFiveMovesTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ c : Fin 5, ∃ g ∈ normalizer ((modelToG e (pointRadical c) ⊔ zpowers t : Subgroup G) :
      Set G), g * t * g⁻¹ ≠ t

@[expose] def PointRadicalLeviInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K], Nat.card K = 2 → ∀ c : Fin n,
    blockSL (K := K) ({c}ᶜ : Finset (Fin n)) ≤
        normalizer (pointRadical (K := K) c : Set (LinearFlag.projectiveSL n K)) ∧
      (∀ v ∈ pointRadical (K := K) c, ∀ w ∈ pointRadical (K := K) c, v ≠ 1 → w ≠ 1 →
        ∃ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)), l * v * l⁻¹ = w) ∧
      (∀ f : pointRadical (K := K) c ≃* pointRadical (K := K) c,
        ∃ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)), ∀ v : pointRadical (K := K) c,
          ((f v : pointRadical (K := K) c) : LinearFlag.projectiveSL n K) = l * v * l⁻¹) ∧
      ∀ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)),
        (∀ v ∈ pointRadical (K := K) c, l * v * l⁻¹ = v) → l = 1

@[expose] def WOneOfXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V L₁ : Subgroup G) (t : G),
    Nat.card V = 2 ^ 4 → (∀ v ∈ V, v * v = 1) → t * t = 1 → (∀ v ∈ V, v * t = t * v) →
    t ∉ V → centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t →
    (∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v) →
    (∀ x ∈ seitzRadX V t, x * x ∈ V) →
    (∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V) →
    L₁ ≤ centralizer ({t} : Set G) → L₁ ≤ normalizer (V : Set G) →
    (∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹) →
    (∀ l ∈ L₁, (∀ v ∈ V, l * v * l⁻¹ = v) → l = 1) →
    ∃ W₁ : Subgroup G, W₁ ≤ seitzRadX V t ∧ Nat.card W₁ = 2 ^ 8 ∧
      (∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v) ∧ (∀ w ∈ W₁, w * w ∈ V) ∧
      W₁ ⊓ centralizer ({t} : Set G) = V ∧ t ∈ normalizer (W₁ : Set G) ∧
      L₁ ≤ normalizer (W₁ : Set G)

@[expose] def HomocyclicExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W V L₁ : Subgroup G),
    (∀ v ∈ W, ∀ w ∈ W, v * w = w * v) → Nat.card W = 2 ^ 8 → V ≤ W → Nat.card V = 2 ^ 4 →
    (∀ v ∈ V, v * v = 1) → (∀ w ∈ W, w * w ∈ V) →
    L₁ ≤ normalizer (W : Set G) → L₁ ≤ normalizer (V : Set G) →
    (∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹) →
    (∀ l ∈ L₁, (∀ v ∈ V, l * v * l⁻¹ = v) → l = 1) →
    ∀ w ∈ W, w * w = 1

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

@[expose] noncomputable def linearModelToGEquiv (A : Subgroup (LinearFlag.projectiveSL n K)) :
    A ≃* modelToG e A :=
  (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
    ((A.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)

theorem coe_linearModelToGEquiv_apply (A : Subgroup (LinearFlag.projectiveSL n K)) (a : A) :
    ((linearModelToGEquiv e A a : modelToG e A) : G) = ((e.symm a : L) : G) :=
  rfl

theorem modelToG_le_normalizer {A B : Subgroup (LinearFlag.projectiveSL n K)}
    (h : B ≤ normalizer (A : Set (LinearFlag.projectiveSL n K))) :
    modelToG e B ≤ normalizer (modelToG e A : Set G) :=
  (modelToG_mono e h).trans ((map_mono (le_normalizer_map _)).trans (le_normalizer_map _))

theorem exists_mem_modelToG_of_forall_mulEquiv {A B : Subgroup (LinearFlag.projectiveSL n K)}
    (h : ∀ f : A ≃* A, ∃ l ∈ B, ∀ v : A, ((f v : A) : LinearFlag.projectiveSL n K) = l * v * l⁻¹)
    (f : modelToG e A ≃* modelToG e A) :
    ∃ l ∈ modelToG e B, ∀ v : modelToG e A, ((f v : modelToG e A) : G) = l * v * l⁻¹ := by
  obtain ⟨l, hl, hlf⟩ := h ((linearModelToGEquiv e A).trans (f.trans (linearModelToGEquiv e A).symm))
  refine ⟨((e.symm l : L) : G), symm_mem_modelToG e hl, fun v => ?_⟩
  obtain ⟨a, rfl⟩ := (linearModelToGEquiv e A).surjective v
  have h2 : f (linearModelToGEquiv e A a) = linearModelToGEquiv e A
      (((linearModelToGEquiv e A).trans (f.trans (linearModelToGEquiv e A).symm)) a) := by
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [h2, coe_linearModelToGEquiv_apply, coe_linearModelToGEquiv_apply, hlf a, map_mul, map_mul, map_inv]
  rfl

end Transport

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem lFiveWOneInput_of (hmove : LFiveMovesTInput) (hlevi : PointRadicalLeviInput)
    (hX : WOneOfXInput) (hhom : HomocyclicExclusionInput) : LFiveWOneInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c
  set V : Subgroup G := modelToG e (pointRadical c) with hVdef
  set L₁ : Subgroup G := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁def
  obtain ⟨hnorm, htrans₀, haut₀, hfaith₀⟩ := hlevi 5 K hK c
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have htV : ∀ v ∈ V, v * t = t * v := fun v hv =>
    (mem_centralizer_iff.1 htC) v (modelToG_le e _ hv)
  have hV2 : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hv
    rw [← L.coe_mul, ← map_mul, pointRadOn_mul_self c _ ha, map_one, L.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hVcard : Nat.card V = 2 ^ 4 := by
    rw [hVdef, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have htnV : t ∉ V := fun h =>
    not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h)
  have hconj : ∀ v ∈ V, ∃ g : G, g⁻¹ * t * g = t * v := fun v hv =>
    exists_conj_eq_mul_of_mem_pointRadical hset (by norm_num) hK e htC ht c hv
  have hnot : ∀ g : G, ∀ v ∈ V, g⁻¹ * t * g ≠ v := fun g v hv =>
    conj_ne_of_mem_pointRadical hset (by norm_num) hK e htC ht c hv g
  have hker := centralizer_pointRadical_inf_le hset (by norm_num) hK e ht hKt c
  have hL₁t : L₁ ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l (modelToG_le e _ hl))
  have hL₁V : L₁ ≤ normalizer (V : Set G) := modelToG_le_normalizer e hnorm
  have hautall := exists_mem_modelToG_of_forall_mulEquiv e haut₀
  have haut : ∀ g ∈ normalizer (V : Set G), ∃ l ∈ L₁, ∀ v ∈ V, g * v * g⁻¹ = l * v * l⁻¹ := by
    intro g hg
    obtain ⟨l, hl, hlf⟩ := hautall (conjAutOfMemNormalizer hg)
    exact ⟨l, hl, fun v hv => (coe_conjAutOfMemNormalizer_apply hg ⟨v, hv⟩).symm.trans
      (hlf ⟨v, hv⟩)⟩
  have htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L₁, l * v * l⁻¹ = w := by
    intro v hv w hw hv1 hw1
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hv
    obtain ⟨b, hb, rfl⟩ := (mem_modelToG e).1 hw
    have ha1 : a ≠ 1 := fun h => hv1 (by rw [h, map_one, L.coe_one])
    have hb1 : b ≠ 1 := fun h => hw1 (by rw [h, map_one, L.coe_one])
    obtain ⟨B, hB, hBab⟩ := htrans₀ a ha b hb ha1 hb1
    refine ⟨((e.symm B : L) : G), symm_mem_modelToG e hB, ?_⟩
    rw [← hBab, map_mul, map_mul, map_inv]
    rfl
  have hfaith : ∀ l ∈ L₁, (∀ v ∈ V, l * v * l⁻¹ = v) → l = 1 := by
    intro l hl hlv
    obtain ⟨B, hB, rfl⟩ := (mem_modelToG e).1 hl
    have hB1 : B = 1 := hfaith₀ B hB fun a ha => by
      apply e.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv]
      exact hlv _ (symm_mem_modelToG e ha)
    rw [hB1, map_one, L.coe_one]
  have hsurj := exists_mem_seitzRadX_tcomm_eq ht2 htV hconj hnot hL₁t hL₁V htrans haut
    (hmove G L hset K hK e t ht hKt c)
  obtain ⟨hsq, hcomm⟩ := mul_self_mem_and_commutator_mem_of_mem_seitzRadX hV2 ht2 htV htnV hker
    hsurj hL₁t hL₁V htrans (by rw [hVcard]; norm_num)
  obtain ⟨W₁, -, hW₁c, hW₁ab, hW₁sq, hW₁t, htW₁, hL₁W₁⟩ :=
    hX G V L₁ t hVcard hV2 ht2 htV htnV hker hsurj hsq hcomm hL₁t hL₁V hautall hfaith
  have hVW : V ≤ W₁ := by rw [← hW₁t]; exact inf_le_left
  have hW₁2 := hhom G W₁ V L₁ hW₁ab hW₁c hVW hVcard hV2 hW₁sq hL₁W₁ hL₁V hautall hfaith
  exact ⟨W₁, hW₁c, hW₁2, hW₁t, htW₁, hL₁W₁⟩

end Assembly

end CFSG.SeitzReduction.LinearPilot
