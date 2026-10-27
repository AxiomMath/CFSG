module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorModel
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModule

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Module Matrix Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule

section Minimal

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (τ : Representation (ZMod 2) K M)

theorem minimal_block {U : Submodule (ZMod 2) M} (hU : IsInv τ U) (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule (ZMod 2) M, IsInv τ U' → U' ≤ U → U' = ⊥ ∨ U' = U) :
    ∃ i j : Fin 4, finrank (ZMod 2) U = labelDim i * labelDim j ∧
      (i = 0 → ∀ g : S, ∀ x ∈ U, τ (g, 1) x = x) ∧ (j = 0 → ∀ h : S, ∀ x ∈ U, τ (1, h) x = x) := by
  have hirr := isIrreducible_subrepOf hU hU0 hmin
  obtain ⟨⟨i, j⟩, ⟨e⟩⟩ := exists_equiv_blockRepK _ hirr
  refine ⟨i, j, e.toLinearEquiv.finrank_eq.trans (finrank_block (i, j)), ?_, ?_⟩
  · rintro rfl g x hx
    have h1 := Equiv.map_apply e (g, 1) ⟨x, hx⟩
    rw [show blockRepK (0, j) (g, 1) (e ⟨x, hx⟩) = e ⟨x, hx⟩ from
      Subtype.ext (repK_left_of_mem_block j g (e ⟨x, hx⟩).2)] at h1
    exact congrArg Subtype.val (e.toLinearEquiv.injective h1)
  · rintro rfl h x hx
    have h1 := Equiv.map_apply e (1, h) ⟨x, hx⟩
    rw [show blockRepK (i, 0) (1, h) (e ⟨x, hx⟩) = e ⟨x, hx⟩ from
      Subtype.ext (repK_right_of_mem_block i h (e ⟨x, hx⟩).2)] at h1
    exact congrArg Subtype.val (e.toLinearEquiv.injective h1)

theorem labelDim_mul_ne_twelve (i j : Fin 4) : labelDim i * labelDim j ≠ 12 := by
  fin_cases i <;> fin_cases j <;> decide

theorem labelDim_mul_lt_nine (i j : Fin 4) (h : labelDim i * labelDim j < 9) : i = 0 ∨ j = 0 := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

theorem minimal_one_sided {U : Submodule (ZMod 2) M} (hU : IsInv τ U) (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule (ZMod 2) M, IsInv τ U' → U' ≤ U → U' = ⊥ ∨ U' = U)
    (h9 : finrank (ZMod 2) U < 9) :
    (∀ g : S, ∀ x ∈ U, τ (g, 1) x = x) ∨ (∀ h : S, ∀ x ∈ U, τ (1, h) x = x) := by
  obtain ⟨i, j, hdim, hi, hj⟩ := minimal_block τ hU hU0 hmin
  rcases labelDim_mul_lt_nine i j (hdim ▸ h9) with rfl | rfl
  · exact Or.inl (hi rfl)
  · exact Or.inr (hj rfl)

omit [FiniteDimensional (ZMod 2) M] in
theorem finrank_eq_one_of_trivial {U : Submodule (ZMod 2) M} (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule (ZMod 2) M, IsInv τ U' → U' ≤ U → U' = ⊥ ∨ U' = U)
    (htriv : ∀ k : K, ∀ x ∈ U, τ k x = x) : finrank (ZMod 2) U = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hspan : IsInv τ (Submodule.span (ZMod 2) {x}) := fun k y hy => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_smul, htriv k x hx]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
  rcases hmin _ hspan ((Submodule.span_singleton_le_iff_mem x U).2 hx) with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.1 h) hx0
  · rw [← h, finrank_span_singleton hx0]

end Minimal

section Cocycle

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) K W)

theorem rep_comm_apply (g h : S) (w : W) : ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := by
  rw [← rep_mul_apply, ← rep_mul_apply,
    show ((g, 1) : K) * (1, h) = (1, h) * (g, 1) from Prod.ext (by simp) (by simp)]

theorem fst_sub_mem_of_snd_sub_mem {u : W}
    (hu : ∀ h : S, ρ (1, h) u - u ∈ fixSnd ρ ⊔ fixFst ρ) (g : S) :
    ρ (g, 1) u - u ∈ fixSnd ρ := by
  set Z₂ := fixFst ρ
  have hP : ∀ p ∈ fixSnd ρ ⊔ fixFst ρ, ∀ h : S, ρ (1, h) p - p ∈ Z₂ := fun p hp h => by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hp
    rw [map_add, hx h, show x + ρ (1, h) y - (x + y) = ρ (1, h) y - y by abel]
    exact Z₂.sub_mem (rep_mem_fixFst ρ _ hy) hy
  let c : S → W ⧸ Z₂ := fun h => Submodule.Quotient.mk (ρ (1, h) u - u)
  have hc : ∀ h h', c (h * h') = c h + c h' := fun h h' => by
    simp only [c]
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    have e : ρ (1, h * h') u - u - (ρ (1, h) u - u + (ρ (1, h') u - u)) =
        ρ (1, h) (ρ (1, h') u - u) - (ρ (1, h') u - u) := by
      rw [show ((1, h * h') : K) = (1, h) * (1, h') from Prod.ext (mul_one 1).symm rfl,
        rep_mul_apply, map_sub]
      abel
    rw [e]
    exact hP _ (hu h') h
  let ψ : S →* Multiplicative (W ⧸ Z₂) :=
    { toFun := fun h => Multiplicative.ofAdd (c h)
      map_one' := by
        simp only [c]
        rw [show ((1, 1) : K) = 1 from rfl, map_one, Module.End.one_apply, sub_self,
          Submodule.Quotient.mk_zero]
        rfl
      map_mul' := fun h h' => by rw [hc, ofAdd_add] }
  have hψ := eq_one_of_commute ψ fun h h' => mul_comm _ _
  have hy : ∀ h : S, ρ (1, h) u - u ∈ Z₂ := fun h => by
    have h1 : c h = 0 := Multiplicative.ofAdd.injective (hψ h)
    exact (Submodule.Quotient.mk_eq_zero _).1 h1
  intro h
  have e : ρ (1, h) (ρ (g, 1) u - u) =
      ρ (g, 1) u - u + (ρ (g, 1) (ρ (1, h) u - u) - (ρ (1, h) u - u)) := by
    rw [map_sub, map_sub, rep_comm_apply]
    abel
  rw [e, hy h g, sub_self, add_zero]

end Cocycle

section Alike

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) K W)
  (σ : W →ₗ[ZMod 2] W) (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))

include hσσ hσρ in
theorem diag_sub_mem_of_sigma {U : Submodule (ZMod 2) W} (hUinv : ∀ k, ∀ w ∈ U, ρ k w ∈ U)
    (hσU : ∀ w, σ w + w ∈ U) (g : S) (w : W) : ρ (g, g) w - w ∈ U := by
  have hswap : ∀ (h : S) (x : W), ρ (1, h) x + ρ (h, 1) x ∈ U := fun h x => by
    have h1 : ρ (1, h) x = σ (ρ (h, 1) (σ x)) := by rw [hσρ, hσσ]; rfl
    rw [h1, show σ (ρ (h, 1) (σ x)) + ρ (h, 1) x =
      (σ (ρ (h, 1) (σ x)) + ρ (h, 1) (σ x)) + ρ (h, 1) (σ x + x) by
        rw [map_add, show ∀ a b c : W, a + b + (b + c) = a + c + (b + b) from fun a b c => by abel,
          ZModModule.add_self, add_zero]]
    exact U.add_mem (hσU _) (hUinv _ _ (hσU x))
  let ψ : S →* Module.End (ZMod 2) (W ⧸ U) :=
    { toFun := fun g => U.mapQ U (ρ (g, 1)) fun w hw => hUinv _ w hw
      map_one' := by
        ext w
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
          Submodule.mapQ_apply, Module.End.one_apply]
        rw [show ((1, 1) : K) = 1 from rfl, map_one]
        rfl
      map_mul' := fun g h => by
        ext w
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
          Submodule.mapQ_apply, Module.End.mul_apply]
        rw [show ((g * h, 1) : K) = (g, 1) * (h, 1) from Prod.ext rfl (mul_one 1).symm,
          rep_mul_apply] }
  have hψ : ∀ g h, ψ g * ψ h = ψ h * ψ g := fun g h => by
    ext w
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Module.End.mul_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, sub_eq_add_neg, ZModModule.neg_eq_self]
    have e1 : ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := rep_comm_apply ρ g h w
    rw [show ρ (g, 1) (ρ (h, 1) w) + ρ (h, 1) (ρ (g, 1) w) =
      ρ (g, 1) (ρ (h, 1) w + ρ (1, h) w) + (ρ (1, h) (ρ (g, 1) w) + ρ (h, 1) (ρ (g, 1) w)) by
        rw [map_add, e1, show ∀ a b c : W, a + c = a + b + (b + c) from fun a b c => by
          rw [show a + b + (b + c) = a + c + (b + b) by abel, ZModModule.add_self, add_zero]]]
    exact U.add_mem (hUinv _ _ (by rw [add_comm]; exact hswap h w)) (hswap h _)
  have hfirst : ∀ (g : S) (w : W), ρ (g, 1) w + w ∈ U := fun g w => by
    have h1 := LinearMap.congr_fun (eq_one_of_commute ψ hψ g) (Submodule.Quotient.mk w)
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
      Module.End.one_apply] at h1
    rw [Submodule.Quotient.eq, sub_eq_add_neg, ZModModule.neg_eq_self] at h1
    exact h1
  rw [sub_eq_add_neg, ZModModule.neg_eq_self,
    show ((g, g) : K) = (g, 1) * (1, g) from Prod.ext (mul_one g).symm (one_mul g).symm,
    rep_mul_apply,
    show ρ (g, 1) (ρ (1, g) w) + w = (ρ (g, 1) (ρ (1, g) w) + ρ (1, g) w) +
      (ρ (1, g) w + ρ (g, 1) w) + (ρ (g, 1) w + w) by
        rw [show ∀ a b c d : W, a + b + (b + c) + (c + d) = a + d + (b + b) + (c + c) from
          fun a b c d => by abel, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]]
  exact U.add_mem (U.add_mem (hfirst _ _) (hswap _ _)) (hfirst _ _)

end Alike

theorem finrank_of_congr_invariant (V' : Submodule (ZMod 2) Sym3)
    (hV' : ∀ (g : S), ∀ B ∈ V', symThreeCongr g B ∈ V') :
    finrank (ZMod 2) V' = 0 ∨ finrank (ZMod 2) V' = 3 ∨ finrank (ZMod 2) V' = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := card_of_invariant V'.toAddSubgroup hV'
  have hp := FiniteField.pow_finrank_eq_natCard 2 V'
  change Nat.card V' = 1 ∨ Nat.card V' = 8 ∨ Nat.card V' = 64 at hc
  rw [← hp] at hc
  rcases hc with h | h | h
  · left
    exact Nat.pow_right_injective le_rfl (h.trans (pow_zero 2).symm)
  · right; left
    exact Nat.pow_right_injective le_rfl (h.trans (by norm_num))
  · right; right
    exact Nat.pow_right_injective le_rfl (h.trans (by norm_num))

theorem finrank_sym3 : finrank (ZMod 2) Sym3 = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := FiniteField.pow_finrank_eq_natCard 2 Sym3
  rw [card_symThree] at hp
  exact Nat.pow_right_injective le_rfl (hp.trans (by norm_num))

section Main

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) K W) (σ : W →ₗ[ZMod 2] W)
  (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))
  (A : Submodule (ZMod 2) W) (hA : ∀ w, w ∈ A ↔ σ w = w)
  (β : Sym3 ≃ₗ[ZMod 2] A) (hβ : ∀ (g : S) (B : Sym3), ρ (g, g) (β B : W) = β (symThreeCongr g B))

omit [FiniteDimensional (ZMod 2) W] in
include hσσ hA in
theorem sigma_add_mem (w : W) : σ w + w ∈ A := by
  rw [hA, map_add, hσσ, add_comm]

omit [FiniteDimensional (ZMod 2) W] in
include hσρ in
theorem sigma_diag (g : S) (w : W) : σ (ρ (g, g) w) = ρ (g, g) (σ w) := hσρ (g, g) w

omit [FiniteDimensional (ZMod 2) W] in
include hA in
theorem mem_A_iff_add (w : W) : w ∈ A ↔ σ w + w = 0 := by
  rw [hA]
  constructor
  · intro h
    rw [h, ZModModule.add_self]
  · intro h
    have := congrArg (· + w) h
    simpa [add_assoc, ZModModule.add_self] using this

omit [FiniteDimensional (ZMod 2) W] in
include hβ in
theorem finrank_inf_A (U : Submodule (ZMod 2) W) (hU : ∀ (g : S), ∀ u ∈ U, ρ (g, g) u ∈ U) :
    finrank (ZMod 2) ↥(U ⊓ A) = 0 ∨ finrank (ZMod 2) ↥(U ⊓ A) = 3 ∨
      finrank (ZMod 2) ↥(U ⊓ A) = 6 := by
  set V' : Submodule (ZMod 2) Sym3 := ((U ⊓ A).comap A.subtype).map β.symm.toLinearMap with hV'
  have hmem : ∀ B : Sym3, B ∈ V' ↔ (β B : W) ∈ U := fun B => by
    rw [hV', Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact (Submodule.mem_inf.1 ha).1
    · intro hB
      exact ⟨β B, Submodule.mem_inf.2 ⟨hB, (β B).2⟩, by simp⟩
  have hinv : ∀ (g : S), ∀ B ∈ V', symThreeCongr g B ∈ V' := fun g B hB => by
    rw [hmem] at hB ⊢
    rw [← hβ]
    exact hU g _ hB
  have heq : finrank (ZMod 2) V' = finrank (ZMod 2) ↥(U ⊓ A) := by
    rw [hV', LinearEquiv.finrank_map_eq]
    have hle : U ⊓ A ≤ A := inf_le_right
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [← heq]
  exact finrank_of_congr_invariant V' hinv

include hσσ hσρ hA hβ in
theorem three_dvd_finrank (U : Submodule (ZMod 2) W) (hU : ∀ (g : S), ∀ u ∈ U, ρ (g, g) u ∈ U) :
    3 ∣ finrank (ZMod 2) U := by
  set f : U →ₗ[ZMod 2] W := (σ + LinearMap.id).domRestrict U with hf
  have hker : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) ↥(U ⊓ A) := by
    have e : LinearMap.ker f ≃ₗ[ZMod 2] ↥(U ⊓ A) :=
      { toFun := fun x => ⟨(x : U), Submodule.mem_inf.2 ⟨(x : U).2, (mem_A_iff_add σ A hA _).2
          (LinearMap.mem_ker.1 x.2)⟩⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl
        invFun := fun y => ⟨⟨y, (Submodule.mem_inf.1 y.2).1⟩, LinearMap.mem_ker.2
          ((mem_A_iff_add σ A hA _).1 (Submodule.mem_inf.1 y.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    exact e.finrank_eq
  have hrange : ∀ g : S, ∀ u ∈ LinearMap.range f, ρ (g, g) u ∈ LinearMap.range f := by
    rintro g _ ⟨x, rfl⟩
    refine ⟨⟨ρ (g, g) x, hU g _ x.2⟩, ?_⟩
    simp only [hf, LinearMap.domRestrict_apply, LinearMap.add_apply, LinearMap.id_apply]
    rw [map_add, sigma_diag ρ σ hσρ]
  have hrA : LinearMap.range f ≤ A := by
    rintro _ ⟨x, rfl⟩
    simpa [hf] using sigma_add_mem σ hσσ A hA (x : W)
  have hr := finrank_inf_A ρ A β hβ (LinearMap.range f) hrange
  rw [inf_of_le_left hrA] at hr
  have hk := finrank_inf_A ρ A β hβ U hU
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at hsum
  omega

omit [FiniteDimensional (ZMod 2) W] in
include hβ in
theorem A_le_of_comm (V : Submodule (ZMod 2) W) (hV : ∀ (g : S), ∀ v ∈ V, ρ (g, g) v ∈ V)
    (hc : ∀ (g : S), ∀ a ∈ A, ρ (g, g) a - a ∈ V) : A ≤ V := by
  set V' : AddSubgroup Sym3 :=
    { carrier := {B | (β B : W) ∈ V}
      add_mem' := fun {B B'} hB hB' => by
        change ((β (B + B') : A) : W) ∈ V
        rw [map_add, Submodule.coe_add]
        exact V.add_mem hB hB'
      zero_mem' := by
        change ((β 0 : A) : W) ∈ V
        rw [map_zero, Submodule.coe_zero]
        exact V.zero_mem
      neg_mem' := fun {B} hB => by
        change ((β (-B) : A) : W) ∈ V
        rw [map_neg, Submodule.coe_neg]
        exact V.neg_mem hB } with hV'
  have hinv : ∀ (g : S), ∀ B ∈ V', symThreeCongr g B ∈ V' := fun g B hB => by
    change ((β (symThreeCongr g B) : A) : W) ∈ V
    rw [← hβ]
    exact hV g _ hB
  have hcomm : ∀ (g : S) (B : Sym3), symThreeCongr g B - B ∈ V' := fun g B => by
    change ((β (symThreeCongr g B - B) : A) : W) ∈ V
    rw [map_sub, Submodule.coe_sub, ← hβ]
    exact hc g _ (β B).2
  have htop := eq_top_of_invariant_of_comm V' hinv hcomm
  intro a ha
  have h1 : β.symm ⟨a, ha⟩ ∈ V' := htop ▸ AddSubgroup.mem_top _
  change ((β (β.symm ⟨a, ha⟩) : A) : W) ∈ V at h1
  rwa [LinearEquiv.apply_symm_apply] at h1

omit [FiniteDimensional (ZMod 2) W] in
include hσσ hσρ hA hβ in
theorem eq_top_of_comm (hAr : ∀ a ∈ A, ∃ w, σ w + w = a) (U : Submodule (ZMod 2) W)
    (hU : ∀ (g : S), ∀ u ∈ U, ρ (g, g) u ∈ U) (hc : ∀ (g : S) (w : W), ρ (g, g) w - w ∈ U) :
    U = ⊤ := by
  have hAU : A ≤ U := A_le_of_comm ρ A β hβ U hU fun g a _ => hc g a
  set U₂ := U.map (σ + LinearMap.id) with hU₂
  have hU₂inv : ∀ (g : S), ∀ v ∈ U₂, ρ (g, g) v ∈ U₂ := by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨ρ (g, g) u, hU g u hu, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply]
    rw [map_add, sigma_diag ρ σ hσρ]
  have hAU₂ : A ≤ U₂ := A_le_of_comm ρ A β hβ U₂ hU₂inv fun g a ha => by
    obtain ⟨w, rfl⟩ := hAr a ha
    refine ⟨ρ (g, g) w - w, hc g w, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_sub, map_add,
      sigma_diag ρ σ hσρ]
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, hu, hwu⟩ := hAU₂ (sigma_add_mem σ hσσ A hA w)
  simp only [LinearMap.add_apply, LinearMap.id_apply] at hwu
  have hd : w - u ∈ A := by
    rw [mem_A_iff_add σ A hA, map_sub, show σ w - σ u + (w - u) = σ w + w - (σ u + u) by abel,
      hwu, sub_self]
  have := U.add_mem (hAU hd) hu
  rwa [sub_add_cancel] at this

include hσσ hσρ hA hβ in
theorem eq_zero_of_diag_fixed (w : W) (hw : ∀ g : S, ρ (g, g) w = w) : w = 0 := by
  have hinv : ∀ (g : S), ∀ u ∈ Submodule.span (ZMod 2) {w},
      ρ (g, g) u ∈ Submodule.span (ZMod 2) {w} :=
    fun g u hu => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [map_smul, hw g]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
  have h3 := three_dvd_finrank ρ σ hσσ hσρ A hA β hβ _ hinv
  by_contra hw0
  rw [finrank_span_singleton hw0] at h3
  omega

include hσσ hσρ hA hβ in
theorem finrank_lt_nine_of_minimal (hAr : ∀ a ∈ A, ∃ w, σ w + w = a)
    (hW : finrank (ZMod 2) W = 12) {U : Submodule (ZMod 2) W} (hU : IsInv ρ U) (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule (ZMod 2) W, IsInv ρ U' → U' ≤ U → U' = ⊥ ∨ U' = U) :
    finrank (ZMod 2) U < 9 := by
  by_contra h9
  push Not at h9
  obtain ⟨i, j, hdim, -, -⟩ := minimal_block ρ hU hU0 hmin
  let σe : W ≃ₗ[ZMod 2] W := LinearEquiv.ofInvolutive σ hσσ
  set U' := U.map σe.toLinearMap with hU'
  have hmemU' : ∀ w, w ∈ U' ↔ σ w ∈ U := fun w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change σ (σ u) ∈ U
      rwa [hσσ]
    · intro hw
      exact ⟨σ w, hw, hσσ w⟩
  have hU'inv : IsInv ρ U' := fun k w hw => by
    rw [hmemU'] at hw ⊢
    rw [hσρ]
    exact hU _ _ hw
  have hfinU' : finrank (ZMod 2) U' = finrank (ZMod 2) U := LinearEquiv.finrank_map_eq σe U
  have hinvI : IsInv ρ (U ⊓ U') := fun k w hw => ⟨hU k w hw.1, hU'inv k w hw.2⟩
  rcases hmin _ hinvI inf_le_left with h | h
  ·
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U U'
    rw [h, finrank_bot, add_zero, hfinU'] at hsum
    have hle := Submodule.finrank_le (U ⊔ U')
    omega
  ·
    have hσU : ∀ u ∈ U, σ u ∈ U := fun u hu => by
      have hu' : u ∈ U ⊓ U' := by rw [h]; exact hu
      exact (hmemU' u).1 hu'.2
    set f : U →ₗ[ZMod 2] W := (σ + LinearMap.id).domRestrict U with hf
    have hker : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) ↥(U ⊓ A) := by
      have e : LinearMap.ker f ≃ₗ[ZMod 2] ↥(U ⊓ A) :=
        { toFun := fun x => ⟨(x : U), Submodule.mem_inf.2 ⟨(x : U).2, (mem_A_iff_add σ A hA _).2
            (LinearMap.mem_ker.1 x.2)⟩⟩
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl
          invFun := fun y => ⟨⟨y, (Submodule.mem_inf.1 y.2).1⟩, LinearMap.mem_ker.2
            ((mem_A_iff_add σ A hA _).1 (Submodule.mem_inf.1 y.2).2)⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      exact e.finrank_eq
    have hrange : LinearMap.range f ≤ U ⊓ A := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.mem_inf.2 ⟨U.add_mem (hσU _ x.2) x.2, sigma_add_mem σ hσσ A hA (x : W)⟩
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    have hr := Submodule.finrank_mono hrange
    have hdA : finrank (ZMod 2) A = 6 := by rw [← β.finrank_eq, finrank_sym3]
    have hUA := finrank_inf_A ρ A β hβ U fun g u hu => hU (g, g) u hu
    have hUA6 : finrank (ZMod 2) ↥(U ⊓ A) = 6 := by omega
    have hAU : A ≤ U := by
      have heq : U ⊓ A = A := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hUA6, hdA])
      rw [← heq]
      exact inf_le_left
    have hdiag := diag_sub_mem_of_sigma ρ σ hσσ hσρ (fun k w hw => hU k w hw)
      fun w => hAU (sigma_add_mem σ hσσ A hA w)
    have htop := eq_top_of_comm ρ σ hσσ hσρ A hA β hβ hAr U (fun g u hu => hU (g, g) u hu) hdiag
    rw [htop, finrank_top, hW] at hdim
    exact labelDim_mul_ne_twelve i j hdim.symm

omit [FiniteDimensional (ZMod 2) W] in
theorem fixSnd_comp_swap :
    fixSnd (ρ.comp (MulEquiv.prodComm : K ≃* K).toMonoidHom) = fixFst ρ := rfl

omit [FiniteDimensional (ZMod 2) W] in
theorem fixFst_comp_swap :
    fixFst (ρ.comp (MulEquiv.prodComm : K ≃* K).toMonoidHom) = fixSnd ρ := rfl

include hσσ hσρ hA hβ in
theorem fixSnd_sup_fixFst (hAr : ∀ a ∈ A, ∃ w, σ w + w = a) (hW : finrank (ZMod 2) W = 12) :
    fixSnd ρ ⊔ fixFst ρ = ⊤ ∧ fixFst ρ ⊓ fixSnd ρ = ⊥ := by
  have hfix := eq_zero_of_diag_fixed ρ σ hσσ hσρ A hA β hβ
  have hinf : fixFst ρ ⊓ fixSnd ρ = ⊥ := fixFst_inf_fixSnd ρ hfix
  refine ⟨?_, hinf⟩
  have h3 : ∀ U : Submodule (ZMod 2) W, (∀ k, ∀ u ∈ U, ρ k u ∈ U) → 3 ∣ finrank (ZMod 2) U :=
    fun U hU => three_dvd_finrank ρ σ hσσ hσρ A hA β hβ U fun g u hu => hU (g, g) u hu
  have hW0 : (⊤ : Submodule (ZMod 2) W) ≠ ⊥ := fun h => by
    have := finrank_top (ZMod 2) W
    rw [h, finrank_bot, hW] at this
    omega
  obtain ⟨U, -, hU, hU0, hmin⟩ := exists_minimal ρ (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top) hW0
  have h9 := finrank_lt_nine_of_minimal ρ σ hσσ hσρ A hA β hβ hAr hW hU hU0 hmin
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hZ1 : fixSnd ρ ≠ ⊥ := by
    intro hbot
    rcases minimal_one_sided ρ hU hU0 hmin h9 with h | h
    · have h1 : σ x ∈ fixSnd ρ := σ_mem_fixSnd ρ σ hσρ (fun g => h g x hx)
      rw [hbot, Submodule.mem_bot] at h1
      exact hx0 (by rw [← hσσ x, h1, map_zero])
    · have h1 : x ∈ fixSnd ρ := fun h' => h h' x hx
      rw [hbot, Submodule.mem_bot] at h1
      exact hx0 h1
  have heq := finrank_fixFst_eq ρ σ hσσ hσρ
  have hZ3 := h3 (fixSnd ρ) fun k u hu => rep_mem_fixSnd ρ k hu
  have hZpos : 0 < finrank (ZMod 2) (fixSnd ρ) := Submodule.one_le_finrank_iff.2 hZ1
  set P := fixSnd ρ ⊔ fixFst ρ with hPdef
  have hPinv : ∀ k, ∀ w ∈ P, ρ k w ∈ P := fun k w hw => by
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (rep_mem_fixSnd ρ k hz₁) (rep_mem_fixFst ρ k hz₂)
  have hPdim : finrank (ZMod 2) P = 2 * finrank (ZMod 2) (fixSnd ρ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSnd ρ) (fixFst ρ)
    rw [inf_comm, hinf, finrank_bot, add_zero, heq, ← hPdef] at h
    omega
  have hP3 := h3 P hPinv
  by_contra hP
  have hle : ∀ k, P ≤ P.comap (ρ k) := fun k w hw => hPinv k w hw
  set ρQ := ρ.quotient P hle with hρQ
  have hρQ_mk : ∀ (k : K) (u : W), ρQ k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (ρ k u) := fun k u => rfl
  have hQ0 : (⊤ : Submodule (ZMod 2) (W ⧸ P)) ≠ ⊥ := fun h => hP (by
    rw [eq_top_iff]
    intro w _
    have : Submodule.Quotient.mk (p := P) w ∈ (⊥ : Submodule (ZMod 2) (W ⧸ P)) :=
      h ▸ Submodule.mem_top
    exact (Submodule.Quotient.mk_eq_zero P).1 ((Submodule.mem_bot _).1 this))
  obtain ⟨Ū, -, hŪ, hŪ0, hŪmin⟩ := exists_minimal ρQ (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top) hQ0
  have hdimQ := Submodule.finrank_quotient_add_finrank P
  rw [hW] at hdimQ
  have hŪle := Submodule.finrank_le Ū
  have hŪ9 : finrank (ZMod 2) Ū < 9 := by omega
  have hmk : ∀ (k : K) (u : W), ρQ k (Submodule.Quotient.mk u) = Submodule.Quotient.mk u ↔
      ρ k u - u ∈ P := fun k u => by
    rw [hρQ_mk, Submodule.Quotient.eq]
  have htriv : ∀ k : K, ∀ y ∈ Ū, ρQ k y = y := by
    have hboth : (∀ g : S, ∀ y ∈ Ū, ρQ (g, 1) y = y) ∧ (∀ h : S, ∀ y ∈ Ū, ρQ (1, h) y = y) := by
      rcases minimal_one_sided ρQ hŪ hŪ0 hŪmin hŪ9 with h | h
      · refine ⟨h, fun h' y hy => ?_⟩
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective P y
        have hu : ∀ g : S, (ρ.comp (MulEquiv.prodComm : K ≃* K).toMonoidHom) (1, g) u - u ∈
            fixSnd (ρ.comp (MulEquiv.prodComm : K ≃* K).toMonoidHom) ⊔
              fixFst (ρ.comp (MulEquiv.prodComm : K ≃* K).toMonoidHom) := fun g => by
          rw [fixSnd_comp_swap, fixFst_comp_swap, sup_comm]
          exact (hmk (g, 1) u).1 (h g _ hy)
        have h1 := fst_sub_mem_of_snd_sub_mem _ hu h'
        rw [fixSnd_comp_swap] at h1
        exact (hmk (1, h') u).2 (Submodule.mem_sup_right h1)
      · refine ⟨fun g y hy => ?_, h⟩
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective P y
        have h1 := fst_sub_mem_of_snd_sub_mem ρ (fun h' => (hmk (1, h') u).1 (h h' _ hy)) g
        exact (hmk (g, 1) u).2 (Submodule.mem_sup_left h1)
    intro k y hy
    rw [show k = (k.1, 1) * (1, k.2) from Prod.ext (mul_one _).symm (one_mul _).symm, map_mul,
      Module.End.mul_apply, hboth.2 _ y hy, hboth.1 _ y hy]
  have h1 := finrank_eq_one_of_trivial ρQ hŪ0 hŪmin htriv
  set U₁ := Ū.comap P.mkQ with hU₁
  have hPU : P ≤ U₁ := fun w hw => by
    change Submodule.Quotient.mk w ∈ Ū
    rw [(Submodule.Quotient.mk_eq_zero P).2 hw]
    exact Ū.zero_mem
  have hU₁inv : ∀ k, ∀ u ∈ U₁, ρ k u ∈ U₁ := fun k u hu => by
    change Submodule.Quotient.mk (ρ k u) ∈ Ū
    rw [← hρQ_mk]
    exact hŪ k _ hu
  have hU₁dim : finrank (ZMod 2) U₁ = finrank (ZMod 2) P + 1 := by
    set f := P.mkQ.domRestrict U₁ with hf
    have hrange : LinearMap.range f = Ū := by
      rw [hf, LinearMap.range_domRestrict, hU₁, Submodule.map_comap_eq_of_surjective
        (Submodule.mkQ_surjective P)]
    have hker : LinearMap.ker f = P.comap U₁.subtype := by
      rw [hf, LinearMap.ker_domRestrict, Submodule.ker_mkQ]
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, hker, h1, (Submodule.comapSubtypeEquivOfLe hPU).finrank_eq] at hsum
    omega
  have hU₁3 := h3 U₁ hU₁inv
  omega

include hσσ hσρ hA hβ in
theorem exists_model_equiv (hAr : ∀ a ∈ A, ∃ w, σ w + w = a) (hW : finrank (ZMod 2) W = 12) :
    ∃ Φ : (Sym3 × Sym3) ≃ₗ[ZMod 2] W,
      (∀ (k : K) (x : Sym3 × Sym3), ρ k (Φ x) = Φ (repK12 k x)) ∧
        ∀ x : Sym3 × Sym3, σ (Φ x) = Φ x.swap := by
  obtain ⟨hsup, hinf⟩ := fixSnd_sup_fixFst ρ σ hσσ hσρ A hA β hβ hAr hW
  set Z₁ := fixSnd ρ with hZ₁
  set Z₂ := fixFst ρ with hZ₂
  have heq : finrank (ZMod 2) Z₂ = finrank (ZMod 2) Z₁ := finrank_fixFst_eq ρ σ hσσ hσρ
  have hdim : finrank (ZMod 2) Z₁ = 6 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Z₁ Z₂
    rw [inf_comm, hinf, finrank_bot, add_zero, hsup, finrank_top, hW] at h
    omega
  have hdA : finrank (ZMod 2) A = 6 := by rw [← β.finrank_eq, finrank_sym3]
  have hinfZ : ∀ w, w ∈ Z₁ → w ∈ Z₂ → w = 0 := fun w h1 h2 => by
    have : w ∈ Z₂ ⊓ Z₁ := ⟨h2, h1⟩
    rw [hinf, Submodule.mem_bot] at this
    exact this
  let f₁ : Z₁ →ₗ[ZMod 2] A := ((σ + LinearMap.id).domRestrict Z₁).codRestrict A fun z => by
    simpa using sigma_add_mem σ hσσ A hA (z : W)
  have hf₁ : ∀ z : Z₁, (f₁ z : W) = σ z + z := fun z => rfl
  have hf₁inj : Function.Injective f₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have h1 : σ z + z = 0 := by rw [← hf₁, hz]; rfl
    have h2 : σ (z : W) = z := by
      have := congrArg (· + (z : W)) h1
      simpa [add_assoc, ZModModule.add_self] using this
    have h3 : (z : W) ∈ Z₂ := h2 ▸ σ_mem_fixFst ρ σ hσρ z.2
    exact (Submodule.mem_bot _).2 (Subtype.ext (hinfZ _ z.2 h3))
  have hf₁bij : Function.Bijective f₁ :=
    ⟨hf₁inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim.trans hdA.symm)).1 hf₁inj⟩
  let ζ : Z₁ ≃ₗ[ZMod 2] A := LinearEquiv.ofBijective f₁ hf₁bij
  have hζ : ∀ z : Z₁, (ζ z : W) = σ z + z := fun z => rfl
  have hdiagZ : ∀ (g h : S), ∀ z ∈ Z₁, ρ (g, h) z = ρ (g, g) z := fun g h z hz => by
    rw [show ((g, h) : K) = (g, 1) * (1, h) from Prod.ext (mul_one g).symm (one_mul h).symm,
      show ((g, g) : K) = (g, 1) * (1, g) from Prod.ext (mul_one g).symm (one_mul g).symm,
      rep_mul_apply, rep_mul_apply, hz h, hz g]
  set ψ : Sym3 → W := fun B => ((ζ.symm (β B) : Z₁) : W) with hψ
  have hψZ : ∀ B, ψ B ∈ Z₁ := fun B => (ζ.symm (β B)).2
  have hψeq : ∀ (g : S) (B : Sym3), ρ (g, g) (ψ B) = ψ (symThreeCongr g B) := fun g B => by
    set z := ζ.symm (β B) with hz
    have hgz : ρ (g, g) (z : W) ∈ Z₁ := rep_mem_fixSnd ρ _ z.2
    have h1 : ζ ⟨ρ (g, g) z, hgz⟩ = β (symThreeCongr g B) := by
      apply Subtype.ext
      rw [hζ, ← hβ]
      change σ (ρ (g, g) z) + ρ (g, g) z = _
      rw [sigma_diag ρ σ hσρ, ← map_add, ← hζ z, hz, LinearEquiv.apply_symm_apply]
    have h2 := congrArg (fun a => ((ζ.symm a : Z₁) : W)) h1
    simp only [LinearEquiv.symm_apply_apply] at h2
    exact h2
  have hψadd : ∀ B B', ψ (B + B') = ψ B + ψ B' := fun B B' => by
    simp only [hψ, map_add, Submodule.coe_add]
  have hψsmul : ∀ (c : ZMod 2) B, ψ (c • B) = c • ψ B := fun c B => by
    simp only [hψ, map_smul, Submodule.coe_smul]
  let Φ₀ : (Sym3 × Sym3) →ₗ[ZMod 2] W :=
    { toFun := fun x => ψ x.1 + σ (ψ x.2)
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, hψadd, map_add]
        abel
      map_smul' := fun c x => by
        simp only [Prod.smul_fst, Prod.smul_snd, hψsmul, map_smul, smul_add, RingHom.id_apply] }
  have hΦ₀ : ∀ x, Φ₀ x = ψ x.1 + σ (ψ x.2) := fun x => rfl
  have hΦ₀inj : Function.Injective Φ₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, hΦ₀] at hx
    have h1 : ψ x.1 = σ (ψ x.2) := by
      have := congrArg (· + σ (ψ x.2)) hx
      simpa [add_assoc, ZModModule.add_self] using this
    have h2 : ψ x.1 = 0 := hinfZ _ (hψZ _) (h1 ▸ σ_mem_fixFst ρ σ hσρ (hψZ _))
    have h3 : σ (ψ x.2) = 0 := h1 ▸ h2
    have h4 : ψ x.2 = 0 := by rw [← hσσ (ψ x.2), h3, map_zero]
    have hψinj : ∀ B, ψ B = 0 → B = 0 := fun B hB => by
      have : ζ.symm (β B) = 0 := Subtype.ext hB
      rw [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at this
      exact this
    rw [Submodule.mem_bot]
    exact Prod.ext (hψinj _ h2) (hψinj _ h4)
  have hfin : finrank (ZMod 2) (Sym3 × Sym3) = finrank (ZMod 2) W := by
    rw [Module.finrank_prod, finrank_sym3, hW]
  let Φ : (Sym3 × Sym3) ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective Φ₀
    ⟨hΦ₀inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hΦ₀inj⟩
  refine ⟨Φ, fun k x => ?_, fun x => ?_⟩
  · obtain ⟨g, h⟩ := k
    change ρ (g, h) (Φ₀ x) = Φ₀ (repK12 (g, h) x)
    have e2 : ρ (g, h) (σ (ψ x.2)) = σ (ψ (symThreeCongr h x.2)) := by
      have h1 := hσρ (h, g) (ψ x.2)
      change σ (ρ (h, g) (ψ x.2)) = ρ (g, h) (σ (ψ x.2)) at h1
      rw [← h1, hdiagZ h g _ (hψZ _), hψeq]
    rw [hΦ₀, hΦ₀, repK12_apply, map_add, e2, hdiagZ g h _ (hψZ _), hψeq]
  · change σ (Φ₀ x) = Φ₀ x.swap
    rw [hΦ₀, hΦ₀, map_add, hσσ, add_comm]
    rfl

end Main

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
