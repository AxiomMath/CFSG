module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Words

variable {τ : Tag} {F : Type} [Field F]

variable (τ F) in
@[expose] noncomputable def simpleWordElt (l : List (Fin τ.rank)) : ModGL τ F :=
  (l.map fun j => weylElt τ F j 1).prod

variable (τ) in
@[expose] def simpleWordAct (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  l.foldr (fun j w => reflect τ j w) v

theorem simpleWordElt_nil : simpleWordElt τ F [] = 1 := rfl

theorem simpleWordElt_cons (j : Fin τ.rank) (l : List (Fin τ.rank)) :
    simpleWordElt τ F (j :: l) = weylElt τ F j 1 * simpleWordElt τ F l := by
  rw [simpleWordElt, List.map_cons, List.prod_cons]
  rfl

theorem simpleWordAct_cons (j : Fin τ.rank) (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    simpleWordAct τ (j :: l) v = reflect τ j (simpleWordAct τ l v) := rfl

theorem isRoot_simpleWordAct (l : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    IsRoot τ (simpleWordAct τ l α) := by
  induction l with
  | nil => exact hα
  | cons j l ih => exact IsRoot.reflect j ih

theorem simpleWordElt_conj_pinnedX (l : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : F, ε * ε = 1 ∧ ∀ c : F, simpleWordElt τ F l * pinnedX τ F α c * (simpleWordElt τ F l)⁻¹ =
      pinnedX τ F (simpleWordAct τ l α) (ε * c) := by
  induction l with
  | nil => exact ⟨1, by simp, fun c => by simp [simpleWordElt_nil, simpleWordAct]⟩
  | cons j l ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := ih
    obtain ⟨ε₂, hε₂, h₂⟩ := weylElt_mul_pinnedX_mul_inv F j (isRoot_simpleWordAct l hα)
    refine ⟨ε₂ * ε₁, by linear_combination (ε₂ * ε₂) * hε₁ + hε₂, fun c => ?_⟩
    rw [simpleWordElt_cons, simpleWordAct_cons]
    calc weylElt τ F j 1 * simpleWordElt τ F l * pinnedX τ F α c *
          (weylElt τ F j 1 * simpleWordElt τ F l)⁻¹ =
        weylElt τ F j 1 * (simpleWordElt τ F l * pinnedX τ F α c * (simpleWordElt τ F l)⁻¹) *
          (weylElt τ F j 1)⁻¹ := by group
      _ = _ := by rw [h₁, h₂, mul_assoc]

theorem simpleWordElt_mem_monomialSubgroup (l : List (Fin τ.rank)) :
    simpleWordElt τ F l ∈ monomialSubgroup τ F :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup j

theorem simpleWordElt_mem_adjointGroup (l : List (Fin τ.rank)) :
    simpleWordElt τ F l ∈ adjointGroup τ F :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    rw [← simpleRootSL2_WSL]
    exact simpleRootSL2_mem_adjointGroup j _

theorem wordProd_smul_eq_simpleWordAct (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = simpleWordAct τ l v := by
  induction l with
  | nil => simp [simpleWordAct]
  | cons j l ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simpleWordAct_cons]
    exact simple_smul j _

theorem weylQuotientHom_simpleWordElt (l : List (Fin τ.rank)) :
    weylQuotientHom τ F ⟨simpleWordElt τ F l, simpleWordElt_mem_monomialSubgroup l⟩ =
      (coxeterSystem τ).wordProd l :=
  weylQuotientHom_eq (mapsRootLines_list_prod l)

end Words

section Swap

variable {τ : Tag} {F : Type} [Field F]

theorem uvu_apply_zero_one (a b : F) :
    ((uSL a * vSL b * uSL a : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 = a * (2 + a * b) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem vuv_apply_zero_one (a b : F) :
    ((vSL b * uSL a * vSL b : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 = a := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem uSL_one_mul_vSL_neg_one_mul_uSL_one :
    (uSL (1 : F) * vSL (-1) * uSL 1 : SL2 F) = vSL (-1) * uSL 1 * vSL (-1) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_inv_of_conj_swap (hF : ringChar F ≠ 2) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {g : ModGL τ F} {μ μ' : F} (hμ' : μ' ≠ 0)
    (h1 : ∀ c : F, g * pinnedX τ F β c * g⁻¹ = pinnedX τ F (-β) (μ * c))
    (h2 : ∀ c : F, g * pinnedX τ F (-β) c * g⁻¹ = pinnedX τ F β (μ' * c)) : μ * μ' = 1 := by
  set ρ := rootSL2 τ F β with hρ
  have hinj : Function.Injective ρ :=
    ((exceptional_Lang_root_rank_one_data τ F β).2.2.2.2.2.2.2.1 hF).1
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := F) hβ
  obtain ⟨s, hs, hu⟩ : ∃ s : F, s * s = 1 ∧ ∀ z : F, ρ (uSL z) = pinnedX τ F β (s * z) := by
    refine ⟨(((pinnedData τ β).2.2 : ℤ) : F), ?_, fun z => ?_⟩
    · rcases pinnedSign_eq τ β with h | h <;> simp [h]
    · rw [hρ, rootSL2_uSL_eq, zsmul_eq_mul]
  have hX : ∀ c : F, pinnedX τ F β c = ρ (uSL (s * c)) := fun c => by
    rw [hu, ← mul_assoc, hs, one_mul]
  have hY : ∀ c : F, pinnedX τ F (-β) c = ρ (vSL (ε * c)) := fun c => by
    rw [hv, ← mul_assoc, hε, one_mul]
  have hbr := congrArg ρ (uSL_one_mul_vSL_neg_one_mul_uSL_one (F := F))
  rw [map_mul, map_mul, map_mul, map_mul, hu, hv] at hbr
  have hconj := congrArg (fun x => g * x * g⁻¹) hbr
  have e1 : ∀ x y z : ModGL τ F, g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) *
      (g * z * g⁻¹) := fun x y z => by group
  rw [e1, e1, h1, h2] at hconj
  simp only [hX, hY] at hconj
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at hconj
  have hm := hinj hconj
  have h12 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hm
  simp only [vuv_apply_zero_one, uvu_apply_zero_one] at h12
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have ha : s * (μ' * (ε * -1)) ≠ 0 := by
    simp [hs0, hμ', hε0]
  have h3 : s * (μ' * (ε * -1)) * (1 + s * (μ' * (ε * -1)) * (ε * (μ * (s * 1)))) = 0 := by
    linear_combination -h12
  have h4 := (mul_eq_zero.1 h3).resolve_left ha
  linear_combination (-1 : F) * h4 - (μ * μ' * (ε * ε)) * hs - (μ * μ') * hε

end Swap

section Hom

variable {F : Type} [Field F] {H : Type*} [Group H]

theorem hom_ext_sl3_tv {f g : SL(3, F) →* H} (h01 : ∀ c, f (tv 0 1 c) = g (tv 0 1 c))
    (h10 : ∀ c, f (tv 1 0 c) = g (tv 1 0 c)) (h12 : ∀ c, f (tv 1 2 c) = g (tv 1 2 c))
    (h21 : ∀ c, f (tv 2 1 c) = g (tv 2 1 c)) : f = g := by
  refine hom_ext_sl3 (hom_ext_sl2 (fun c => ?_) (fun c => ?_))
    (hom_ext_sl2 (fun c => ?_) (fun c => ?_))
  · change f (blk F 0 (tv 0 1 c)) = g (blk F 0 (tv 0 1 c))
    rw [blk_zero_tv01]
    exact h01 c
  · change f (blk F 0 (tv 1 0 c)) = g (blk F 0 (tv 1 0 c))
    rw [blk_zero_tv10]
    exact h10 c
  · change f (blk F 1 (tv 0 1 c)) = g (blk F 1 (tv 0 1 c))
    rw [blk_one_tv01]
    exact h12 c
  · change f (blk F 1 (tv 1 0 c)) = g (blk F 1 (tv 1 0 c))
    rw [blk_one_tv10]
    exact h21 c

end Hom

section Torus

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_unit_pow_eq (x : kˣ) {n : ℕ} (hn : 0 < n) : ∃ z : kˣ, z ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : k) hn
  have hz0 : z ≠ 0 := fun h => by
    rw [h, zero_pow hn.ne'] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

theorem exists_torus_pow (r₁ r₂ : kˣ) {n : ℕ} (hn : 0 < n) :
    ∃ a b : kˣ, (a ^ 2 * b⁻¹) ^ n = r₁ ∧ (a⁻¹ * b ^ 2) ^ n = r₂ := by
  obtain ⟨x, hx⟩ := exists_unit_pow_eq (r₁ ^ 2 * r₂) (n := 3) (by norm_num)
  obtain ⟨a, ha⟩ := exists_unit_pow_eq x hn
  obtain ⟨b, hb⟩ := exists_unit_pow_eq (x ^ 2 * r₁⁻¹) hn
  refine ⟨a, b, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm 2 n, pow_mul, ha, hb]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have := r₁.ne_zero
    have := x.ne_zero
    field_simp
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm 2 n, pow_mul, ha, hb]
    have h3 : (x : k) ^ 3 = (r₁ : k) ^ 2 * (r₂ : k) := by
      have := congrArg Units.val hx
      simpa using this
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have := r₁.ne_zero
    have := x.ne_zero
    field_simp
    linear_combination h3

end Torus

section Monomial

variable {τ : Tag} {K : Type} [Field K]

theorem rootWeylSL2_one_eq (β : Fin τ.rank → ℤ) :
    rootWeylSL2 τ K β 1 = rootSL2 τ K β WSL := by
  show rootSL2 τ K β (nSL 1) = _
  rw [nSL_one]

theorem rootSL2_WSL_mem_monomialSubgroup {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootSL2 τ K β WSL ∈ monomialSubgroup τ K := by
  obtain ⟨h, -⟩ := (exceptional_Lang_root_rank_one_torus_transport τ K hβ).2.2.1 1
  rwa [rootWeylSL2_one_eq] at h

theorem mapsRootLines_rootSL2_WSL {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    MapsRootLines (rootSL2 τ K β WSL) (rootReflection β) := by
  obtain ⟨h, hq⟩ := (exceptional_Lang_root_rank_one_torus_transport τ K hβ).2.2.1 1
  have h' := rootSL2_WSL_mem_monomialSubgroup (K := K) hβ
  have := mapsRootLines_weylQuotientHom (τ := τ) (R := K) ⟨_, h⟩
  rw [hq] at this
  have h2 : MapsRootLines (rootWeylSL2 τ K β 1) (rootReflection β) := this
  rwa [rootWeylSL2_one_eq] at h2

theorem rootSL2_WSL_conj_pinnedX {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) :
    ∃ μ : Kˣ, ∀ c : K, rootSL2 τ K β WSL * pinnedX τ K γ c * (rootSL2 τ K β WSL)⁻¹ =
      pinnedX τ K (γ - (2 * iform β γ / iform β β) • β) (μ * c) := by
  have hm := rootSL2_WSL_mem_monomialSubgroup (K := K) hβ
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hm hγ
  refine ⟨μ, fun c => ?_⟩
  rw [hμ]
  obtain ⟨h, hq⟩ := (exceptional_Lang_root_rank_one_torus_transport τ K hβ).2.2.1 1
  have hq' : weylQuotientHom τ K ⟨rootSL2 τ K β WSL, hm⟩ = rootReflection β := by
    have e : (⟨rootSL2 τ K β WSL, hm⟩ : monomialSubgroup τ K) = ⟨rootWeylSL2 τ K β 1, h⟩ :=
      Subtype.ext (rootWeylSL2_one_eq β).symm
    rw [e, hq]
  rw [hq', (exceptional_Lang_root_rank_one_torus_transport τ K hβ).2.2.2.1 γ |>.1]

theorem monomial_comm_rootDiagUnit {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K)
    {w : WeylGroup τ} (hw : MapsRootLines n w) {a : Fin τ.rank → Kˣ}
    (hwa : w ∈ rootCharStabilizer a) : rootDiagUnit τ a * n = n * rootDiagUnit τ a := by
  obtain ⟨w', h, hh, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  have hw' : MapsRootLines (h * canonicalRep (coxeterSystem τ) K w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w')
  have hww : w' = w := MapsRootLines.unique hw' hw
  subst hww
  have hc := (conj_canonicalRep_eq_iff (K := K) a w').2 hwa
  rw [mul_inv_eq_iff_eq_mul] at hc
  rw [← mul_assoc, rootDiagUnit_mul_comm_of_mem_torusGroup a hh, mul_assoc, hc, mul_assoc]

end Monomial

section DiagAct

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_one' (v : Fin τ.rank → ℤ) :
    rootChar (1 : Fin τ.rank → Kˣ) v = 1 := by
  simp [rootChar]

theorem rootChar_neg' (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  have h := rootChar_add a v (-v)
  rw [add_neg_cancel, rootChar_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

variable (τ K) in
@[expose] def diagActSubgroup (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ K) where
  carrier := {g | ∃ a : Fin τ.rank → Kˣ, ∀ γ ∈ S, IsRoot τ γ → ∀ c : K,
    g * pinnedX τ K γ c * g⁻¹ = pinnedX τ K γ ((rootChar a γ : K) * c)}
  mul_mem' := by
    rintro g₁ g₂ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
    refine ⟨a₁ * a₂, fun γ hγ hr c => ?_⟩
    calc g₁ * g₂ * pinnedX τ K γ c * (g₁ * g₂)⁻¹ =
        g₁ * (g₂ * pinnedX τ K γ c * g₂⁻¹) * g₁⁻¹ := by group
      _ = _ := by
        rw [h₂ γ hγ hr, h₁ γ hγ hr, rootChar_mul, Units.val_mul, mul_assoc]
  one_mem' := ⟨1, fun γ _ _ c => by simp [rootChar_one']⟩
  inv_mem' := by
    rintro g ⟨a, h⟩
    refine ⟨a⁻¹, fun γ hγ hr c => ?_⟩
    have h1 := h γ hγ hr ((((rootChar a γ)⁻¹ : Kˣ) : K) * c)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
    rw [rootChar_inv_apply, inv_inv]
    calc g⁻¹ * pinnedX τ K γ c * g =
        g⁻¹ * (g * pinnedX τ K γ ((((rootChar a γ)⁻¹ : Kˣ) : K) * c) * g⁻¹) * g := by rw [h1]
      _ = _ := by group

end DiagAct

end CFSG.ClassicalInvolution.ModelFacts.Levi
