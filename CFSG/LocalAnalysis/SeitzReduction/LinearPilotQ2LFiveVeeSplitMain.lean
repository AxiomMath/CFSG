module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSplitTheta
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveQuaMain
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeNorm

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

@[expose] def veeFrobEquiv : F4 ≃+* F4 :=
  { veeFrobHom with
    invFun := veeFrobHom
    left_inv := veeFrobHom_veeFrobHom
    right_inv := veeFrobHom_veeFrobHom }

theorem veeFrobEquiv_apply (x : F4) : veeFrobEquiv x = veeFrobHom x := rfl

theorem veeFrobEquiv_ne_refl : veeFrobEquiv ≠ RingEquiv.refl F4 := by
  intro h
  have h1 := congrArg (fun σ : F4 ≃+* F4 => σ F4.ω) h
  simp only [veeFrobEquiv_apply, RingEquiv.refl_apply] at h1
  revert h1
  decide

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_wOne_rowCoordinates
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc) :
    ∃ (D : seitzTilde W₁ Kc →* SpecialLinearGroup (Fin 4) F4) (β : W₁ → (Fin 4 → F4)),
      Function.Surjective D ∧ (∀ n, D n = 1 ↔ (n : G) ∈ W₁) ∧
      (∀ n m : seitzTilde W₁ Kc, (m : G) = t * n * t⁻¹ → D m = veeFrob (D n)) ∧
      Function.Bijective β ∧ (∀ v w : W₁, β (v * w) = β v + β w) ∧
      (∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
        β v = β w ᵥ* ((D n)⁻¹ : SpecialLinearGroup (Fin 4) F4)) ∧
      ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = veeFrobHom ∘ β w := by
  obtain ⟨ψ, β, hψs, hψk, hψt, hβb, hβa, hβc, hβt⟩ :=
    exists_wOne_coordinates hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  rcases hβc with h | h
  ·
    refine ⟨(slGraphAut 4 F4).toMonoidHom.comp ψ, β,
      (slGraphAut 4 F4).surjective.comp hψs, fun n => ?_, fun n m hm => ?_, hβb, hβa,
      fun n w v hv => ?_, hβt⟩
    · change slGraphAut 4 F4 (ψ n) = 1 ↔ _
      rw [← hψk n]
      exact (slGraphAut 4 F4).map_eq_one_iff
    · change slGraphAut 4 F4 (ψ m) = veeFrob (slGraphAut 4 F4 (ψ n))
      rw [hψt n m hm]
      ext i j
      change (((veeFrob (ψ n))⁻¹ : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4)ᵀ i j =
        ((((ψ n)⁻¹ : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4)ᵀ.map veeFrobHom) i j
      rw [← map_inv, coe_veeFrob, Matrix.transpose_map]
    · rw [h n w v hv]
      have h1 : (((slGraphAut 4 F4 (ψ n))⁻¹ : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4) = ((ψ n : SpecialLinearGroup (Fin 4) F4) :
            Matrix (Fin 4) (Fin 4) F4)ᵀ := by
        rw [← map_inv]
        change (((ψ n)⁻¹⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)ᵀ = _
        rw [inv_inv]
      change _ = β w ᵥ* (((slGraphAut 4 F4 (ψ n))⁻¹ : SpecialLinearGroup (Fin 4) F4) :
        Matrix (Fin 4) (Fin 4) F4)
      rw [h1, vecMul_transpose]
  ·
    refine ⟨ψ, β, hψs, hψk, hψt, hβb, hβa, fun n w v hv => ?_, hβt⟩
    rw [h n w v hv, mulVec_transpose]

theorem exists_wOne_normCoordinates
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} (hS₀ : IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀) :
    ∃ (D : seitzTilde W₁ Kc →* SpecialLinearGroup (Fin 4) F4) (β : W₁ → (Fin 4 → F4)),
      Function.Surjective D ∧ (∀ n, D n = 1 ↔ (n : G) ∈ W₁) ∧
      (∀ n m : seitzTilde W₁ Kc, (m : G) = t * n * t⁻¹ → D m = veeFrob (D n)) ∧
      (∀ n : seitzTilde W₁ Kc, (n : G) ∈ S₀ ↔ D n ∈ unitriangular 4 F4) ∧
      Function.Bijective β ∧ (∀ v w : W₁, β (v * w) = β v + β w) ∧
      (∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
        β v = β w ᵥ* ((D n)⁻¹ : SpecialLinearGroup (Fin 4) F4)) ∧
      ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = veeFrobHom ∘ β w := by
  obtain ⟨D, β, hDs, hDk, hDt, hβb, hβa, hβc, hβt⟩ :=
    exists_wOne_rowCoordinates hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hV : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, card_modelToG_pointRadical hK e c]
  obtain ⟨g, hgσ, hgS⟩ := exists_conj_unitriangular_of_sylow htC hW₁c hV D hDk hDt hS₀
  let D' : seitzTilde W₁ Kc →* SpecialLinearGroup (Fin 4) F4 :=
    (MulAut.conj g⁻¹).toMonoidHom.comp D
  have hD' : ∀ n, D' n = g⁻¹ * D n * g := fun n => by
    change g⁻¹ * D n * g⁻¹⁻¹ = g⁻¹ * D n * g
    rw [inv_inv]
  have hD's : Function.Surjective D' := (MulAut.conj g⁻¹).surjective.comp hDs
  have hD'k : ∀ n, D' n = 1 ↔ (n : G) ∈ W₁ := fun n => by
    rw [hD', ← hDk n]
    constructor
    · intro h
      calc D n = g * (g⁻¹ * D n * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hD't : ∀ n m : seitzTilde W₁ Kc, (m : G) = t * n * t⁻¹ → D' m = veeFrob (D' n) := by
    intro n m hm
    rw [hD', hD', hDt n m hm, map_mul, map_mul, map_inv, hgσ]
  have hS₀U : ∀ n : seitzTilde W₁ Kc, (n : G) ∈ S₀ ↔ D' n ∈ unitriangular 4 F4 := fun n => by
    rw [hD']
    exact hgS n
  let gm : Matrix (Fin 4) (Fin 4) F4 :=
    ((g : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
  let gim : Matrix (Fin 4) (Fin 4) F4 :=
    ((g⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
  have hggi : gm * gim = 1 := by
    change ((g * g⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hgig : gim * gm = 1 := by
    change ((g⁻¹ * g : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  let β' : W₁ → (Fin 4 → F4) := fun w => β w ᵥ* gm
  have hβ'b : Function.Bijective β' := by
    have hvb : Function.Bijective fun v : Fin 4 → F4 => v ᵥ* gm := by
      refine Function.bijective_iff_has_inverse.2 ⟨fun v => v ᵥ* gim, fun v => ?_, fun v => ?_⟩
      · change v ᵥ* gm ᵥ* gim = v
        rw [vecMul_vecMul, hggi, vecMul_one]
      · change v ᵥ* gim ᵥ* gm = v
        rw [vecMul_vecMul, hgig, vecMul_one]
    exact hvb.comp hβb
  have hβ'a : ∀ v w, β' (v * w) = β' v + β' w := fun v w => by
    change β (v * w) ᵥ* gm = β v ᵥ* gm + β w ᵥ* gm
    rw [hβa, add_vecMul]
  have hβ'c : ∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
      β' v = β' w ᵥ* ((D' n)⁻¹ : SpecialLinearGroup (Fin 4) F4) := by
    intro n w v hv
    change β v ᵥ* gm = (β w ᵥ* gm) ᵥ* (((D' n)⁻¹ : SpecialLinearGroup (Fin 4) F4) :
      Matrix (Fin 4) (Fin 4) F4)
    rw [hβc n w v hv, hD', _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, vecMul_vecMul,
      vecMul_vecMul]
    congr 1
    simp only [Matrix.SpecialLinearGroup.coe_mul, gm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    change _ = gm * gim * _ * gm
    rw [hggi, Matrix.one_mul]
  have hβ't : ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β' v = veeFrobHom ∘ β' w := by
    intro w v hv
    change β v ᵥ* gm = veeFrobHom ∘ (β w ᵥ* gm)
    rw [hβt w v hv, veeFrobHom_comp_vecMul]
    congr 1
    change gm = ((veeFrob g : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
    rw [hgσ]
  exact ⟨D', β', hD's, hD'k, hD't, hS₀U, hβ'b, hβ'a, hβ'c, hβ't⟩

theorem lFiveFieldSylowModelInput_of_split
    (hsplit : LFiveFieldSylowSplitInput) : LFiveFieldSylowModelInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt _ c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨C, hCS, hCW, hWC, htCn⟩ :=
    hsplit G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨D, β, hDs, hDk, hDt, hS₀U, hβb, hβa, hβc, hβt⟩ :=
    exists_wOne_normCoordinates hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hS₀
  obtain ⟨Θ, hΘW, hΘt⟩ := exists_mulEquiv_unitriangularFive_of_complement hW₁c
    (seitzTilde_le_normalizer W₁ Kc) D hDs hDk hDt hS₀.2.1 hS₀U β hβb hβa hβc hβt hCS
    hCW hWC htCn
  refine ⟨F4, inferInstance, inferInstance, inferInstance, veeFrobEquiv,
    by rw [Nat.card_eq_fintype_card, F4.card], veeFrobEquiv_ne_refl, Θ, fun x => ?_,
    fun x y hy => hΘt x y hy⟩
  rw [hΘW x, mem_uFiveRow_iff_lt]

end CFSG.SeitzReduction.LinearPilot
