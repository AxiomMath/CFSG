module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSplitBlock
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer

theorem veeFrobHom_comp_vecMul (v : Fin 4 → F4) (N : Matrix (Fin 4) (Fin 4) F4) :
    veeFrobHom ∘ (v ᵥ* N) = (veeFrobHom ∘ v) ᵥ* (N.map veeFrobHom) := by
  funext i
  simp only [Function.comp_apply, vecMul, dotProduct, Matrix.map_apply, map_sum, map_mul]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mulEquiv_unitriangularFive_of_complement {W₁ Nt S₀ C : Subgroup G} {t : G}
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hNtW : Nt ≤ normalizer (W₁ : Set G))
    (D : Nt →* SpecialLinearGroup (Fin 4) F4) (hDs : Function.Surjective D)
    (hDk : ∀ n, D n = 1 ↔ (n : G) ∈ W₁)
    (hDt : ∀ n m : Nt, (m : G) = t * n * t⁻¹ → D m = veeFrob (D n))
    (hS₀N : S₀ ≤ Nt) (hS₀U : ∀ n : Nt, (n : G) ∈ S₀ ↔ D n ∈ unitriangular 4 F4)
    (β : W₁ → (Fin 4 → F4)) (hβb : Function.Bijective β) (hβa : ∀ v w, β (v * w) = β v + β w)
    (hβc : ∀ (n : Nt) (w v : W₁), (v : G) = n * w * n⁻¹ →
      β v = β w ᵥ* ((D n)⁻¹ : SpecialLinearGroup (Fin 4) F4))
    (hβt : ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = veeFrobHom ∘ β w)
    (hCS : C ≤ S₀) (hCW : C ⊓ W₁ = ⊥) (hWC : W₁ ⊔ C = S₀) (htC : t ∈ normalizer (C : Set G)) :
    ∃ Θ : S₀ ≃* unitriangular 5 F4,
      (∀ x : S₀, (x : G) ∈ W₁ ↔ ∀ i j : Fin 5, 0 < i → i < j → ypsMat (Θ x) i j = 0) ∧
        ∀ x y : S₀, (y : G) = t * x * t⁻¹ → ypsMat (Θ y) = (ypsMat (Θ x)).map veeFrobHom := by
  classical
  have hWS : W₁ ≤ S₀ := hWC ▸ le_sup_left
  have hdec : ∀ x ∈ S₀, ∃ w ∈ W₁, ∃ c ∈ C, x = w * c := by
    let WC : Subgroup G :=
      { carrier := {x | ∃ w ∈ W₁, ∃ c ∈ C, x = w * c}
        mul_mem' := by
          rintro _ _ ⟨w, hw, c, hc, rfl⟩ ⟨w', hw', c', hc', rfl⟩
          have hcN : c ∈ normalizer (W₁ : Set G) := hNtW (hS₀N (hCS hc))
          refine ⟨w * (c * w' * c⁻¹), mul_mem hw ((mem_normalizer_iff.1 hcN w').1 hw'), c * c',
            mul_mem hc hc', by group⟩
        one_mem' := ⟨1, one_mem _, 1, one_mem _, by group⟩
        inv_mem' := by
          rintro _ ⟨w, hw, c, hc, rfl⟩
          have hcN : c⁻¹ ∈ normalizer (W₁ : Set G) := inv_mem (hNtW (hS₀N (hCS hc)))
          refine ⟨c⁻¹ * w⁻¹ * c⁻¹⁻¹, (mem_normalizer_iff.1 hcN _).1 (inv_mem hw), c⁻¹,
            inv_mem hc, by group⟩ }
    have hle : S₀ ≤ WC := by
      rw [← hWC]
      exact sup_le (fun w hw => ⟨w, hw, 1, one_mem _, by group⟩)
        (fun c hc => ⟨1, one_mem _, c, hc, by group⟩)
    intro x hx
    exact hle hx
  have hcex : ∀ x : S₀, ∃ c : C, D ⟨c, hS₀N (hCS c.2)⟩ = D ⟨x, hS₀N x.2⟩ := by
    intro x
    obtain ⟨w, hw, c, hc, hx⟩ := hdec x x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    have h1 : (⟨x, hS₀N x.2⟩ : Nt) = ⟨w, hS₀N (hWS hw)⟩ * ⟨c, hS₀N (hCS hc)⟩ :=
      Subtype.ext hx
    rw [h1, map_mul, (hDk ⟨w, hS₀N (hWS hw)⟩).2 hw, one_mul]
  have hcuniq : ∀ c c' : C, D ⟨c, hS₀N (hCS c.2)⟩ = D ⟨c', hS₀N (hCS c'.2)⟩ → c = c' := by
    intro c c' h
    have h1 : D (⟨c, hS₀N (hCS c.2)⟩⁻¹ * ⟨c', hS₀N (hCS c'.2)⟩) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (hDk _).1 h1
    have h3 : (c : G)⁻¹ * c' ∈ C ⊓ W₁ := mem_inf.2 ⟨mul_mem (inv_mem c.2) c'.2, h2⟩
    rw [hCW, mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  choose cf hcf using hcex
  let nN : S₀ → Nt := fun x => ⟨x, hS₀N x.2⟩
  have hnNmul : ∀ x y : S₀, nN (x * y) = nN x * nN y := fun x y => rfl
  let nC : C → Nt := fun c => ⟨c, hS₀N (hCS c.2)⟩
  have hnCmul : ∀ c c' : C, nC (c * c') = nC c * nC c' := fun c c' => rfl
  have hcf' : ∀ x, D (nC (cf x)) = D (nN x) := hcf
  let A : S₀ → unitriangular 4 F4 := fun x => ⟨D (nN x), (hS₀U _).1 x.2⟩
  have hAm : ∀ x, ((A x : unitriangular 4 F4) : SpecialLinearGroup (Fin 4) F4) = D (nN x) :=
    fun x => rfl
  have hcfmul : ∀ x y : S₀, cf (x * y) = cf x * cf y := by
    intro x y
    apply hcuniq
    change D (nC (cf (x * y))) = D (nC (cf x * cf y))
    rw [hcf', hnCmul, map_mul, hcf', hcf', hnNmul, map_mul]
  have hwmem : ∀ x : S₀, (x : G) * ((cf x : C) : G)⁻¹ ∈ W₁ := by
    intro x
    have h1 : D (nN x * (nC (cf x))⁻¹) = 1 := by rw [map_mul, map_inv, hcf', mul_inv_cancel]
    exact (hDk _).1 h1
  let wf : S₀ → W₁ := fun x => ⟨(x : G) * ((cf x : C) : G)⁻¹, hwmem x⟩
  have hβ1 : β 1 = 0 := by
    have h := hβa 1 1
    rw [mul_one] at h
    exact (add_eq_left.1 h.symm)
  have hβw : ∀ x y : S₀, β (wf (x * y)) = β (wf x) + β (wf y) ᵥ*
      ((D (nN x))⁻¹ : SpecialLinearGroup (Fin 4) F4) := by
    intro x y
    have hcN : ((cf x : C) : G) ∈ normalizer (W₁ : Set G) := hNtW (hS₀N (hCS (cf x).2))
    have hconj : ((cf x : C) : G) * (wf y : G) * ((cf x : C) : G)⁻¹ ∈ W₁ :=
      (mem_normalizer_iff.1 hcN _).1 (wf y).2
    have hsplit : wf (x * y) = wf x * ⟨_, hconj⟩ := by
      apply Subtype.ext
      change (x : G) * y * ((cf (x * y) : C) : G)⁻¹ =
        (x : G) * ((cf x : C) : G)⁻¹ * (((cf x : C) : G) * ((y : G) * ((cf y : C) : G)⁻¹) *
          ((cf x : C) : G)⁻¹)
      rw [hcfmul]
      simp only [Subgroup.coe_mul]
      group
    rw [hsplit, hβa, hβc (nC (cf x)) (wf y) ⟨_, hconj⟩ rfl, hcf']
  let rf : S₀ → (Fin 4 → F4) := fun x =>
    β (wf x) ᵥ* ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
  have hrf : ∀ x y : S₀, rf (x * y) = rf y + rf x ᵥ*
      ((D (nN y) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := by
    intro x y
    have hinv : (((D (nN x))⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *
        ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    change β (wf (x * y)) ᵥ* ((D (nN (x * y)) : SpecialLinearGroup (Fin 4) F4) :
        Matrix (Fin 4) (Fin 4) F4) =
      β (wf y) ᵥ* ((D (nN y) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) +
        (β (wf x) ᵥ* ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)) ᵥ*
          ((D (nN y) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
    rw [hβw, hnNmul, map_mul, Matrix.SpecialLinearGroup.coe_mul, add_vecMul]
    simp only [vecMul_vecMul]
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul, add_comm]
  have hc1 : cf 1 = 1 := hcuniq _ _ (by
    change D (nC (cf 1)) = D (nC 1)
    rw [hcf']
    rfl)
  have hw1 : wf 1 = 1 := Subtype.ext (by
    change ((1 : S₀) : G) * ((cf 1 : C) : G)⁻¹ = 1
    rw [hc1]
    simp)
  have hr1 : rf 1 = 0 := by
    change β (wf 1) ᵥ* _ = 0
    rw [hw1, hβ1, zero_vecMul]
  let Θh : S₀ →* unitriangular 5 F4 :=
    { toFun := fun x => veeBlockFiveU (rf x) (A x)
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change veeBlockFive (rf 1) ((D (nN 1) : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4) = 1
        rw [hr1, show nN 1 = 1 from rfl, map_one, Matrix.SpecialLinearGroup.coe_one,
          veeBlockFive_zero_one]
      map_mul' := fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        change veeBlockFive (rf (x * y)) ((D (nN (x * y)) : SpecialLinearGroup (Fin 4) F4) :
            Matrix (Fin 4) (Fin 4) F4) =
          veeBlockFive (rf x) ((D (nN x) : SpecialLinearGroup (Fin 4) F4) :
            Matrix (Fin 4) (Fin 4) F4) *
          veeBlockFive (rf y) ((D (nN y) : SpecialLinearGroup (Fin 4) F4) :
            Matrix (Fin 4) (Fin 4) F4)
        rw [veeBlockFive_mul, hrf, hnNmul, map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  have hΘmat : ∀ x, ypsMat (Θh x) = veeBlockFive (rf x)
      ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := fun x => rfl
  have hinj : Function.Injective Θh := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmat : veeBlockFive (rf x) ((D (nN x) : SpecialLinearGroup (Fin 4) F4) :
        Matrix (Fin 4) (Fin 4) F4) = 1 := by
      rw [← hΘmat, hx]
      rfl
    have hD1 : ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1 := by
      ext k l
      have h1 := congrFun (congrFun hmat k.succ) l.succ
      rw [veeBlockFive_succ_succ] at h1
      rw [h1]
      by_cases hkl : k = l
      · rw [hkl, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hkl, Matrix.one_apply_ne (fun h => hkl (Fin.succ_inj.1 h))]
    have hxW : (x : G) ∈ W₁ := (hDk _).1 (Subtype.ext hD1)
    have hc : cf x = 1 := hcuniq _ _ (by
      change D (nC (cf x)) = D (nC 1)
      rw [hcf', (hDk _).2 hxW]
      exact (map_one D).symm)
    have hr0 : rf x = 0 := by
      funext j
      have h1 := congrFun (congrFun hmat 0) j.succ
      rw [veeBlockFive_zero_succ, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm] at h1
      exact h1
    have hβ0 : β (wf x) = 0 := by
      have h1 : rf x = β (wf x) ᵥ* ((D (nN x) : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4) := rfl
      rw [h1, hD1, vecMul_one] at hr0
      exact hr0
    have hwx : wf x = 1 := hβb.1 (hβ0.trans hβ1.symm)
    apply Subtype.ext
    have h2 : (x : G) * ((cf x : C) : G)⁻¹ = 1 := congrArg Subtype.val hwx
    rw [hc] at h2
    simpa using h2
  let Ah : S₀ →* unitriangular 4 F4 :=
    { toFun := A
      map_one' := Subtype.ext (map_one D)
      map_mul' := fun x y => Subtype.ext (map_mul D (nN x) (nN y)) }
  have hAhs : Function.Surjective Ah := by
    intro u
    obtain ⟨n, hn⟩ := hDs (u : SpecialLinearGroup (Fin 4) F4)
    have hnS : (n : G) ∈ S₀ := (hS₀U n).2 (hn ▸ u.2)
    exact ⟨⟨n, hnS⟩, Subtype.ext hn⟩
  have hAhk : Nat.card Ah.ker = 2 ^ 8 := by
    rw [← hW₁c]
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : S₀) : G), (hDk _).1 (congrArg Subtype.val x.2)⟩
        invFun := fun w => ⟨⟨w, hWS w.2⟩, Subtype.ext ((hDk ⟨w, hS₀N (hWS w.2)⟩).2 w.2)⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  have hcardS : Nat.card S₀ = 2 ^ 20 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Ah.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Ah hAhs).toEquiv, hAhk,
      card_unitriangular, Nat.card_eq_fintype_card (α := F4), F4.card] at h1
    rw [h1]
    norm_num
  have hcardU : Nat.card (unitriangular 5 F4) = 2 ^ 20 := by
    rw [card_unitriangular, Nat.card_eq_fintype_card (α := F4), F4.card]
    norm_num
  have hbij : Function.Bijective Θh :=
    hinj.bijective_of_nat_card_le (by rw [hcardS, hcardU])
  refine ⟨MulEquiv.ofBijective Θh hbij, fun x => ?_, fun x y hy => ?_⟩
  ·
    change (x : G) ∈ W₁ ↔ ∀ i j : Fin 5, 0 < i → i < j → ypsMat (Θh x) i j = 0
    rw [hΘmat, veeBlockFive_lower_eq_zero_iff (A x).2.1 (A x).2.2]
    constructor
    · intro hx
      change ((D (nN x) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = 1
      rw [(hDk (nN x)).2 hx, Matrix.SpecialLinearGroup.coe_one]
    · intro h
      exact (hDk (nN x)).1 (Subtype.ext h)
  ·
    change ypsMat (Θh y) = (ypsMat (Θh x)).map veeFrobHom
    have hDy : D (nN y) = veeFrob (D (nN x)) := hDt (nN x) (nN y) hy
    have htcx : (t : G) * ((cf x : C) : G) * t⁻¹ ∈ C := (mem_normalizer_iff.1 htC _).1 (cf x).2
    have hcy : cf y = ⟨_, htcx⟩ := hcuniq _ _ (by
      change D (nC (cf y)) = D ⟨(t : G) * ((cf x : C) : G) * t⁻¹, hS₀N (hCS htcx)⟩
      rw [hcf', hDy, ← hcf' x]
      exact (hDt (nC (cf x)) _ rfl).symm)
    have hwy : ((wf y : W₁) : G) = t * (wf x : G) * t⁻¹ := by
      change (y : G) * ((cf y : C) : G)⁻¹ = t * ((x : G) * ((cf x : C) : G)⁻¹) * t⁻¹
      rw [hcy, hy]
      change t * (x : G) * t⁻¹ * (t * ((cf x : C) : G) * t⁻¹)⁻¹ = _
      group
    have hβy := hβt (wf x) (wf y) hwy
    have hry : rf y = veeFrobHom ∘ rf x := by
      change β (wf y) ᵥ* ((D (nN y) : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
        veeFrobHom ∘ (β (wf x) ᵥ* ((D (nN x) : SpecialLinearGroup (Fin 4) F4) :
          Matrix (Fin 4) (Fin 4) F4))
      rw [hβy, hDy, coe_veeFrob, veeFrobHom_comp_vecMul]
    rw [hΘmat, hΘmat, hry, hDy, coe_veeFrob, veeBlockFive_map]

end CFSG.SeitzReduction.LinearPilot
