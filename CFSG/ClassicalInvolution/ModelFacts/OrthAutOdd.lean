module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutRoot
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiagC

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section OddFacts

variable {F : Type} [Field F]

theorem odd_hker2 (h2 : (2 : F) ≠ 0) (m : ℕ) :
    ∀ x ∈ (spinAction (quadOdd m F)).ker, x * x = 1 := fun x hx => by
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one_odd m F h2 x (MonoidHom.mem_ker.mp hx) with
    h | h
  · exact spin_mul_self_eq_one (Or.inl (Subtype.ext h))
  · exact spin_mul_self_eq_one (Or.inr h)

theorem odd_orth_eq_smul_z (m : ℕ) {y : Fin m ⊕ Fin m ⊕ Unit → F}
    (hy : ∀ a r, polar (quadOdd m F) y ((oddFrame m F).vec a r) = 0) :
    ∃ c : F, y = c • (oddFrame m F).z := by
  refine ⟨y (.inr (.inr ())), ?_⟩
  ext x
  rcases x with j | j | ⟨⟩
  · have h := hy j false
    simp only [oddFrame_vec, oddVec_false, polar_quadOdd_single_inr_inl] at h
    simp [oddFrame_z, oddZ, h]
  · have h := hy j true
    simp only [oddFrame_vec, oddVec_true, polar_quadOdd_single_inl] at h
    simp [oddFrame_z, oddZ, h]
  · simp [oddFrame_z, oddZ]

variable [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem odd_center_facts (hp2 : p ≠ 2) {m : ℕ} (hn : 3 ≤ m) :
    (∀ ζ ∈ Subgroup.center (spinGroup (quadOdd m F)), ζ ^ p = 1 → ζ = 1) ∧
    (∀ ζ ∈ Subgroup.center (spinGroup (quadOdd m F)),
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, spinAction (quadOdd m F) ζ x = η • x) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have : Finite (spinGroup (quadOdd m F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Nonempty (Fin m ⊕ Fin m ⊕ Unit) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadOdd h2 hn
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd m F))) :=
    not_dvd_card_center_spin (quadOdd m F) (range_spinMatrix_quadOdd h2 hn) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2
  refine ⟨fun ζ hζ hp1 => ?_, fun ζ hζ => ?_⟩
  · by_contra hne
    have h1 : orderOf ζ ∣ p := orderOf_dvd_of_pow_eq_one hp1
    have h2 : orderOf ζ = p := by
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    exact hC (h2 ▸ Subgroup.orderOf_dvd_natCard _ hζ)
  · have hζ' : ζ ∈ (StatedScalars _ F).comap (spinMatrix (quadOdd m F)) := by
      rw [← hcomap, hZ]
      exact hζ
    obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hζ'
    have hact : ∀ x, spinAction (quadOdd m F) ζ x = (c : F) • x := fun x => by
      rw [← spinMatrix_mulVec, ← hc]
      ext i
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
    refine ⟨(c : F), ?_, hact⟩
    have h1 := map_spinAction (quadOdd m F) ζ (oddZ m F)
    rw [hact, QuadraticMap.map_smul, quadOdd_oddZ] at h1
    have h2 : (c : F) * (c : F) = 1 := by simpa using h1
    exact mul_self_eq_one_iff.mp h2

end OddFacts

section Lift

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_isConj_lift_odd (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (θ : spinGroup (quadOdd n F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd n F))) (σ : X ≃* X)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range) :
    ∃ (α : spinGroup (quadOdd n F) ≃* spinGroup (quadOdd n F)) (g : SemiSim (quadOdd n F)),
      (∀ x, θ (α x) = σ (θ x)) ∧ IsConj α g := by
  have hσR : ∀ r ∈ θ.range, σ r ∈ θ.range := by
    rintro r ⟨k, rfl⟩
    exact hσr k
  let σR : θ.range ≃* θ.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : X) (b : X)) }
  have hkerR : θ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadOdd n F)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, hα, A, φ, μ, hQ, hA⟩ := spinOdd_exists_lift_similarity hp2 hn hf hF θ.rangeRestrict
    θ.rangeRestrict_surjective hkerR σR
  exact ⟨α, SemiSim.ofMatrix _ A φ μ hQ, fun x => congrArg Subtype.val (hα x),
    isConj_ofMatrix A φ μ hQ hA⟩

end Lift


section CharB

variable {m : ℕ} {F : Type} [Field F]

@[expose] def charPsiB (a : Fin m → Fˣ) : Multiplicative (Fin m → ℤ) →* Fˣ where
  toFun γ := ∏ k, a k ^ toStdB m (Multiplicative.toAdd γ) k
  map_one' := by simp [toStdB_zero]
  map_mul' γ δ := by
    simp only [toAdd_mul, toStdB_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem charPsiB_apply (a : Fin m → Fˣ) (γ : Fin m → ℤ) :
    charPsiB a (Multiplicative.ofAdd γ) = ∏ k, a k ^ toStdB m γ k := rfl

theorem prod_zpow_single (a : Fin m → Fˣ) (n : Fin m) (x : ℤ) :
    ∏ k, a k ^ (Pi.single n x : Fin m → ℤ) k = a n ^ x := by
  classical
  rw [Finset.prod_eq_single n (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem charPsiB_long (a : Fin m → Fˣ) {γ : Fin m → ℤ} {i j : Fin m} (s t : Bool)
    (h : toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    charPsiB a (Multiplicative.ofAdd γ) = a i ^ boolSign s * a j ^ boolSign t := by
  rw [charPsiB_apply, h]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, prod_zpow_single]

theorem charPsiB_short (a : Fin m → Fˣ) {γ : Fin m → ℤ} {i : Fin m} (s : Bool)
    (h : toStdB m γ = Pi.single i (boolSign s)) :
    charPsiB a (Multiplicative.ofAdd γ) = a i ^ boolSign s := by
  rw [charPsiB_apply, h, prod_zpow_single]

theorem odd_root_cases {γ : Fin m → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB m) ∅) :
    (∃ (i j : Fin m) (_ : i ≠ j) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) ∨
    (∃ (i : Fin m) (s : Bool), toStdB m γ = Pi.single i (boolSign s)) := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
    exact Or.inl ⟨i, j, hij, s', t', h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    exact Or.inr ⟨i, s', h⟩

end CharB


section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] [Finite F] in
theorem shortRoot_pow_char {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {m : ℕ} (Fr : OddFrame Q m) (i : Fin m) (s : Bool) (c : F) :
    (Fr.shortRoot i s (.ofAdd c)) ^ p = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_zero_of_charP, ofAdd_zero, map_one]

theorem toralNormal_odd (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ Nat.card F) {m : ℕ} (hm : 4 ≤ m) {X : Type} [Group X]
    (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool) (k : spinGroup (quadOdd m F))
    (H1 : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ (t : Bool) (u : Fˣ),
      σ (θ (k * (oddFrame m F).longTorus hij true t u * k⁻¹)) =
        θ (k * (oddFrame m F).longTorus hij true t u * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
        ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hZ, hcent⟩ := odd_center_facts (F := F) hp2 hm3
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_odd hp2 hm3 hf hF θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd m F)) := isPerfect_spinGroup_quadOdd h2 hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadOdd m F) →* _).comp
      (α : spinGroup (quadOdd m F) →* _)) (MonoidHom.id (spinGroup (quadOdd m F))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hcen : ∀ y, σ (θ y) = θ y → α y * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd m F)) :=
    fun y hy => hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hy, mul_inv_cancel])
  obtain ⟨u, hu1, hu2⟩ := exists_unit_ne_one_ne_neg_one hq
  obtain ⟨κ, lam, hφ, hprod, hg₂, hCpres, hdiag, -⟩ := exists_diag_form_compl
    (oddFrame m F).toHypFrame h01 s₀ t₀ hm h2 hp2 (odd_hker2 h2 m) hZ hcent hu1 hu2 hα hα2 k
    (fun c => hcen _ (H1 c)) (fun c => hcen _ (H1' c))
    (fun i j hij hi0 hi1 hj0 hj1 t => hcen _ (H2 i j hij hi0 hi1 hj0 hj1 t u))
  set Fr := oddFrame m F with hFr
  have hzorth : ∀ a r, polar (quadOdd m F) Fr.z (Fr.vec a r) = 0 := fun a r => by
    rw [polar_comm]
    exact Fr.polar_vec_z a r
  obtain ⟨ζ, hζ⟩ := odd_orth_eq_smul_z m (fun a r => hCpres Fr.z hzorth a r)
  have hζ2 : ζ * ζ = (g.μ : F) := by
    have h1 := (g.conjSpin κ).map_Q Fr.z
    rw [hζ, QuadraticMap.map_smul, Fr.map_z] at h1
    change (ζ * ζ) • (1 : F) = (g.μ : F) * g.φ 1 at h1
    simpa using h1
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hζ0 : ζ ≠ 0 := fun h0 => hμ0 (by rw [← hζ2, h0, zero_mul])
  have hlam2 : ∀ k s, lam k (!s) * lam k s = (g.μ : F) := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ0 (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true / ζ) (div_ne_zero (hlam0 k true) hζ0)
  have hlamζ : ∀ k s, lam k s = ζ * (a k : F) ^ boolSign s := by
    intro k s
    have h0 := hlam0 k true
    cases s
    · simp only [boolSign_false, a, Units.val_mk0, zpow_neg, zpow_one]
      have hp := hprod k
      rw [← hζ2] at hp
      field_simp
      linear_combination hp
    · simp only [boolSign_true, a, Units.val_mk0, zpow_one]
      field_simp
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hA2 : ∀ y, A (A y) = y := conjTwist_sq α hα2 κ
  have hAlong : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      A (Fr.longRoot hij s t (.ofAdd c)) =
        Fr.longRoot hij s t (.ofAdd ((lam j t * ((g.μ : F)⁻¹ * lam i s)) * c)) := by
    intro i j hij s t c
    have h1 := hdiag i j hij s t c
    rw [hA] at h1
    rw [mul_left_cancel (mul_right_cancel h1)]
    congr 2
    ring
  have hα₂c : IsConj A (g.conjSpin κ) := hα.conjSpin κ
  have hAshort : ∀ (i : Fin m) (s : Bool) (c : F),
      A (Fr.shortRoot i s (.ofAdd c)) =
        Fr.shortRoot i s (.ofAdd ((lam i s * ((g.μ : F)⁻¹ * ζ)) * c)) := by
    intro i s c
    have h3 := IsConj.shortRoot_eq hp2 (odd_hker2 h2 m) Fr hα₂c lam (fun _ s => s) hg₂ ζ hζ i s c
    have hφc : (g.conjSpin κ).φ c = c := hφ c
    have hμc : (((g.conjSpin κ).μ : Fˣ) : F) = (g.μ : F) := rfl
    rw [h3, hφc, hμc]
    congr 2
    ring
  have hχL2 : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool),
      (lam j t * ((g.μ : F)⁻¹ * lam i s)) * (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 :=
    fun i j hij s t => sq_eq_one_of_scalar A hA2 (Fr.longRoot hij s t)
      (Fr.longRoot_injective hij s t) _ (hAlong i j hij s t)
  have hχS2 : ∀ (i : Fin m) (s : Bool),
      (lam i s * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 :=
    fun i s => sq_eq_one_of_scalar A hA2 (Fr.shortRoot i s) (Fr.shortRoot_injective i s) _
      (hAshort i s)
  have hψlong : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam j t * ((g.μ : F)⁻¹ * lam i s) := by
    intro γ i j s t h
    rw [charPsiB_long a s t h, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, hlamζ i s, hlamζ j t, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    have haj : (a j : F) ≠ 0 := (a j).ne_zero
    field_simp
  have hψshort : ∀ (γ : Fin m → ℤ) (i : Fin m) (s : Bool),
      toStdB m γ = Pi.single i (boolSign s) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam i s * ((g.μ : F)⁻¹ * ζ) := by
    intro γ i s h
    rw [charPsiB_short a s h, Units.val_zpow_eq_zpow_val, hlamζ i s, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    field_simp
  have hψ1 : ∀ a₀ : Fin m, charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = 1 ∨
      charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = -1 := by
    intro a₀
    by_cases hlt : a₀.val + 1 < m
    · have hkj : a₀ ≠ ⟨a₀.val + 1, hlt⟩ := Fin.ne_of_val_ne (by simp)
      have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) +
          Pi.single (⟨a₀.val + 1, hlt⟩ : Fin m) (boolSign false) := by
        rw [toStdB_single_of_lt m hlt, boolSign_true, boolSign_false, Pi.single_neg,
          sub_eq_add_neg]
      have h1 := hψlong _ _ _ true false hrep
      have h2' := hχL2 _ _ hkj true false
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
    · have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) := by
        rw [toStdB_single_of_not_lt m hlt, boolSign_true]
      have h1 := hψshort _ _ true hrep
      have h2' := hχS2 a₀ true
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  obtain ⟨v, hv⟩ := exists_vec_of_hom h2 (charPsiB a) hψ1
  refine ⟨κ, v, fun γ hγ => ?_⟩
  rcases odd_root_cases hγ with ⟨i, j, hij, s, t, hstd⟩ | ⟨i, s, hstd⟩
  · have hX1 : (oddDatum m F).rootGroup γ = (Fr.longRoot hij s t).range :=
      oddRootGroup_eq_long hij s t hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]
    have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
      oddRootGroup_eq_long hij (!s) (!t) hstd'
    rw [hX1, hX2]
    have hχ : lam j t * ((g.μ : F)⁻¹ * lam i s) = 1 →
        lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s)) = 1 := by
      intro h1
      have hprod' : (lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s))) *
          (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 := by
        calc _ = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) *
              ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by ring
          _ = (g.μ : F) * (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by rw [hlam2, hlam2]
          _ = 1 := by field_simp
      rw [h1, mul_one] at hprod'
      exact hprod'
    have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
      (Fr.longRoot hij s t) (Fr.longRoot hij (!s) (!t)) (Fr.longRoot_injective hij s t)
      (fun c => longRoot_pow_char Fr.toHypFrame hij s t c) _ _ (hAlong i j hij s t)
      (hAlong i j hij (!s) (!t)) hχ
    refine ⟨hmain.1, ?_⟩
    rw [hmain.2, ← hv γ, Units.ext_iff, hψlong γ i j s t hstd, Units.val_one]
  · have hX1 : (oddDatum m F).rootGroup γ = (Fr.shortRoot i s).range :=
      oddRootGroup_eq_short i s hstd
    have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) := by
      have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
      rw [e, hstd, boolSign_not, Pi.single_neg]
    have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.shortRoot i (!s)).range :=
      oddRootGroup_eq_short i (!s) hstd'
    rw [hX1, hX2]
    have hχ : lam i s * ((g.μ : F)⁻¹ * ζ) = 1 → lam i (!s) * ((g.μ : F)⁻¹ * ζ) = 1 := by
      intro h1
      have hprod' : (lam i (!s) * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 := by
        calc _ = (lam i (!s) * lam i s) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (ζ * ζ) := by ring
          _ = (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (g.μ : F) := by rw [hlam2, hζ2]
          _ = 1 := by field_simp
      rw [h1, mul_one] at hprod'
      exact hprod'
    have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
      (Fr.shortRoot i s) (Fr.shortRoot i (!s)) (Fr.shortRoot_injective i s)
      (fun c => shortRoot_pow_char Fr i s c) _ _ (hAshort i s) (hAshort i (!s)) hχ
    refine ⟨hmain.1, ?_⟩
    rw [hmain.2, ← hv γ, Units.ext_iff, hψshort γ i s hstd, Units.val_one]


theorem toralNormal_odd_of_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ Nat.card F) {m : ℕ} (hm : 4 ≤ m) {X : Type} [Group X]
    (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) {s₀ t₀ : Bool} {γ₀ : Fin m → ℤ}
    (hγ₀ : toStdB m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (k : spinGroup (quadOdd m F))
    (H1 : ∀ y ∈ (((oddDatum m F).rootGroup γ₀ ⊔ (oddDatum m F).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (T : Subgroup (spinGroup (quadOdd m F)))
    (hT : ∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ (t : Bool) (u : Fˣ),
      (oddFrame m F).longTorus hij true t u ∈ T)
    (H2 : ∀ t ∈ T, σ (θ (k * t * k⁻¹)) = θ (k * t * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
        ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hX1 : (oddDatum m F).rootGroup γ₀ = ((oddFrame m F).longRoot h01 s₀ t₀).range :=
    oddRootGroup_eq_long h01 s₀ t₀ hγ₀
  have hstd' : toStdB m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdB m (-γ₀) = -toStdB m γ₀ := toStdB_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (oddDatum m F).rootGroup (-γ₀) =
      ((oddFrame m F).longRoot h01.symm (!t₀) (!s₀)).range :=
    oddRootGroup_eq_long h01.symm (!t₀) (!s₀) hstd'
  refine toralNormal_odd hp2 hf hF hq hm θ hker σ hσ2 hσr h01 s₀ t₀ k (fun c => ?_)
    (fun c => ?_) (fun i j hij hi0 hi1 hj0 hj1 t u => H2 _ (hT i j hij hi0 hi1 hj0 hj1 t u))
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
