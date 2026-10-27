module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7F
public import Certificates.Data.A5

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
  Equiv

@[expose] def v4pred (σ : Perm (Fin 4)) : Prop := σ = tv (σ 0)

instance : DecidablePred v4pred := fun σ => inferInstanceAs (Decidable (σ = tv (σ 0)))

theorem v4pred_mul : ∀ a b : Perm (Fin 4), v4pred a → v4pred b → v4pred (a * b) := by
  decide +kernel

theorem v4pred_one : v4pred 1 := by decide +kernel

theorem v4pred_inv : ∀ a : Perm (Fin 4), v4pred a → v4pred a⁻¹ := by decide +kernel

@[expose] def kleinV4 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | v4pred σ}
  mul_mem' := fun {a b} ha hb => v4pred_mul a b ha hb
  one_mem' := v4pred_one
  inv_mem' := fun {a} ha => v4pred_inv a ha

@[expose] def cThree : Perm (Fin 4) := swap 0 1 * swap 1 2

theorem cThree_pow : cThree ^ 3 = 1 := by decide +kernel

theorem cThree_ne : cThree ≠ 1 := by decide +kernel

theorem cThree_order : orderOf cThree = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime cThree_pow cThree_ne

theorem cThree_sign : Perm.sign cThree = 1 := by decide +kernel

theorem v4_sq : ∀ σ : Perm (Fin 4), v4pred σ → σ ^ 2 = 1 := by decide +kernel

theorem v4_comm : ∀ a b : Perm (Fin 4), v4pred a → v4pred b → a * b = b * a := by decide +kernel

theorem v4_sign : ∀ σ : Perm (Fin 4), v4pred σ → Perm.sign σ = 1 := by decide +kernel

theorem alt4_center : ∀ g : Perm (Fin 4), Perm.sign g = 1 →
    (∀ l : Perm (Fin 4), Perm.sign l = 1 → g * l = l * g) → g = 1 := by decide +kernel

theorem cThree_norm :
    ∀ σ : Perm (Fin 4), v4pred σ ↔ v4pred (cThree * σ * cThree⁻¹) := by decide +kernel

theorem cThree_fpf :
    ∀ σ : Perm (Fin 4), v4pred σ → σ ≠ 1 → cThree * σ * cThree⁻¹ ≠ σ := by decide +kernel

theorem alt4_cover : ∀ σ : Perm (Fin 4), Perm.sign σ = 1 →
    v4pred σ ∨ v4pred (σ * cThree⁻¹) ∨ v4pred (σ * (cThree⁻¹ * cThree⁻¹)) := by decide +kernel

theorem card_kleinV4 : Nat.card ↥kleinV4 = 4 := by
  let f : Fin 4 → ↥kleinV4 := fun i => ⟨tv i, by
    show v4pred (tv i)
    revert i
    decide +kernel⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have h : tv i = tv j := congrArg Subtype.val hij
      revert i j
      decide +kernel
    · rintro ⟨σ, hσ⟩
      refine ⟨σ 0, Subtype.ext ?_⟩
      exact (show σ = tv (σ 0) from hσ).symm
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem card_alt4 : Nat.card ↥(alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem isA4Block_alt4 : IsA4Block (alternatingGroup (Fin 4)) kleinV4 := by
  have hV4A : kleinV4 ≤ alternatingGroup (Fin 4) := fun σ hσ =>
    Perm.mem_alternatingGroup.mpr (v4_sign σ hσ)
  have hcA : cThree ∈ alternatingGroup (Fin 4) := Perm.mem_alternatingGroup.mpr cThree_sign
  refine ⟨card_kleinV4, fun σ hσ => v4_sq σ hσ, fun a ha b hb => v4_comm a b ha hb, card_alt4,
    ?_, cThree, hcA, cThree_order, ?_, ?_, ?_⟩
  · intro g hg hcomm
    exact alt4_center g (Perm.mem_alternatingGroup.mp hg) fun l hl =>
      hcomm l (Perm.mem_alternatingGroup.mpr hl)
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    exact cThree_norm x
  · intro σ hσ h1
    exact cThree_fpf σ hσ h1
  · apply le_antisymm
    · intro σ hσ
      have hs : Perm.sign σ = 1 := Perm.mem_alternatingGroup.mp hσ
      have hσ' : σ = (σ * cThree⁻¹) * cThree := by group
      have hσ'' : σ = (σ * (cThree⁻¹ * cThree⁻¹)) * cThree ^ 2 := by
        rw [pow_two]
        group
      rcases alt4_cover σ hs with h | h | h
      · exact Subgroup.mem_sup_left h
      · rw [hσ']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers cThree))
      · rw [hσ'']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
          (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers cThree) 2))
    · exact sup_le hV4A (Subgroup.zpowers_le.mpr hcA)

theorem bv_even : ∀ i, isEven (bv i) := by decide +kernel

theorem rmul_rone_ptab_v4 : ∀ σ : Perm (Fin 4), v4pred σ →
    rmul (dtab 1) (ptab σ) = (bv (σ 0), 1) := by decide +kernel

theorem bv_tv3 : bv ((swap (0 : Fin 4) 3 * swap (1 : Fin 4) 2 : Perm (Fin 4)) 0) = g23 := by
  decide +kernel

theorem v4pred_tv3 : v4pred (swap (0 : Fin 4) 3 * swap (1 : Fin 4) 2 : Perm (Fin 4)) := by
  decide +kernel

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] noncomputable def fHu : Perm (Fin 4) →* G :=
  H.subtype.comp (X.huHom.comp (MonoidHom.inr (DihedralGroup 4) (Perm (Fin 4))))

theorem fHu_injective : Function.Injective X.fHu :=
  Subtype.val_injective.comp (X.huHom_inj.comp fun _ _ h => (Prod.mk.inj h).2)

theorem fHu_apply
    (σ : Perm (Fin 4)) : X.fHu σ = ((X.huHom (1, σ) : ↥H) : G) := rfl

@[expose] noncomputable def V4W : Subgroup G := kleinV4.map X.fHu

theorem isA4Block_A4W : IsA4Block X.A4W X.V4W :=
  isA4Block_alt4.map_of_injective X.fHu X.fHu_injective

theorem fHu_v4 {σ : Perm (Fin 4)} (hσ : v4pred σ) :
    X.fHu σ = ((C.iV ⟨bv (σ 0), bv_even _⟩ : ↥H) : G) := by
  rw [fHu_apply, X.huHom_apply]
  have h1 : X.embR (rmul (dtab 1) (ptab σ)) (isEven_rmul (dtab_fix 1).2 (ptab_fix σ).2) =
      X.embR (bv (σ 0), 1) (bv_even _) :=
    X.embR_congr (rmul_rone_ptab_v4 σ hσ) _ _
  rw [h1]
  show ((X.emb ⟨bv (σ 0), bv_even _⟩ 1 : ↥H) : G) = _
  rw [Sec.emb, map_one, mul_one]

theorem V4W_le_U : X.V4W ≤ blockU L := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [X.fHu_v4 hσ]
  exact C.iV_mem_U _

theorem uz_mem_V4W : C.u0 * C.zU ∈ X.V4W := by
  refine ⟨swap (0 : Fin 4) 3 * swap (1 : Fin 4) 2, v4pred_tv3, ?_⟩
  rw [X.fHu_v4 v4pred_tv3, C.u0_mul_zU']
  exact congrArg (fun w => ((C.iV w : ↥H) : G)) (Subtype.ext bv_tv3)

end Sec

end CFSG.QuasithinUnique.A5
