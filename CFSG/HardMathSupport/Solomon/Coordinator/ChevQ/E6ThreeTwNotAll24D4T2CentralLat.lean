module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass
public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.SeitzGeneration.ExcHighThree (twPhi e6RootParams_mul')
open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom monoHom_apply
  monoHom_surjective_of_det_ne_zero)

set_option linter.unusedSectionVars false

section Lang


private def d4tE1 : Fin Tag.E6.rank → ℤ := ![2, 2, 3, 4, 3, 2]

private def d4tE2 : Fin Tag.E6.rank → ℤ := ![4, 3, 5, 6, 4, 2]

private theorem d4t_symm : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]

private theorem d4t_iform_single (j : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ) :
    iform (Pi.single j 1) y = ∑ k, Tag.E6.cartan j k * y k := by
  rw [iform_single_left, show Tag.E6.symmetrizer = 1 from rfl, Matrix.one_apply_eq, one_mul]

private theorem d4t_iform_e1 (x : Fin Tag.E6.rank → ℤ) : iform x d4tE1 = x 0 + x 5 := by
  have key : ∀ x : Fin 6 → ℤ, ∑ i, ∑ j, x i * Tag.cartanE 6 i j *
      (![2, 2, 3, 4, 3, 2] : Fin 6 → ℤ) j = x 0 + x 5 := by
    intro x
    simp [Fin.sum_univ_six, Tag.cartanE]
    ring
  rw [iform, d4t_symm]
  exact key x

private theorem d4t_iform_e2 (x : Fin Tag.E6.rank → ℤ) : iform x d4tE2 = 3 * x 0 := by
  have key : ∀ x : Fin 6 → ℤ, ∑ i, ∑ j, x i * Tag.cartanE 6 i j *
      (![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) j = 3 * x 0 := by
    intro x
    simp [Fin.sum_univ_six, Tag.cartanE]
    ring
  rw [iform, d4t_symm]
  exact key x

private theorem d4t_perp_J {y : Fin Tag.E6.rank → ℤ}
    (h : ∀ j ∈ d4Nodes Tag.E6, iform (Pi.single j 1) y = 0) :
    y = (5 * y 1 - 3 * y 2) • d4tE1 + (2 * y 2 - 3 * y 1) • d4tE2 := by
  have key : ∀ y : Fin 6 → ℤ, ∑ k, Tag.cartanE 6 1 k * y k = 0 →
      ∑ k, Tag.cartanE 6 2 k * y k = 0 → ∑ k, Tag.cartanE 6 3 k * y k = 0 →
      ∑ k, Tag.cartanE 6 4 k * y k = 0 →
      y = (5 * y 1 - 3 * y 2) • (![2, 2, 3, 4, 3, 2] : Fin 6 → ℤ) +
        (2 * y 2 - 3 * y 1) • (![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) := by
    intro y h1 h2 h3 h4
    simp [Fin.sum_univ_six, Tag.cartanE] at h1 h2 h3 h4
    funext k
    fin_cases k <;> simp <;> omega
  have hm : ∀ j : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 → ∑ k, Tag.E6.cartan j k * y k = 0 :=
    fun j h1 h2 => (d4t_iform_single j y).symm.trans (h j ⟨h1, h2⟩)
  exact key y (hm 1 (by decide) (by decide)) (hm 2 (by decide) (by decide))
    (hm 3 (by decide) (by decide)) (hm 4 (by decide) (by decide))

private theorem d4t_perp_f {v : WeylGroup Tag.E6} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    iform γ (v • d4tE1) = 0 ∧ iform γ (v • d4tE2) = 0 := by
  obtain ⟨γ', ⟨-, hγ'⟩, rfl⟩ := hγ
  have h0 : γ' 0 = 0 := hγ' 0 fun h => absurd h.1 (by decide)
  have h5 : γ' 5 = 0 := hγ' 5 fun h => absurd h.2 (by decide)
  rw [iform_smul, iform_smul, d4t_iform_e1, d4t_iform_e2, h0, h5]
  simp

private theorem d4t_perp_span {v : WeylGroup Tag.E6} {y : Fin Tag.E6.rank → ℤ}
    (h : ∀ γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6), iform γ y = 0) :
    ∃ c₁ c₂ : ℤ, y = c₁ • (v • d4tE1) + c₂ • (v • d4tE2) := by
  have hy : ∀ j ∈ d4Nodes Tag.E6, iform (Pi.single j 1) (v⁻¹ • y) = 0 := by
    intro j hj
    have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
      ⟨_, ⟨isRoot_single Tag.E6 j, fun i hi =>
        Pi.single_eq_of_ne (fun e => hi (by rw [e]; exact hj)) 1⟩, rfl⟩
    rw [← iform_smul v, smul_inv_smul]
    exact h _ hmem
  refine ⟨5 * (v⁻¹ • y) 1 - 3 * (v⁻¹ • y) 2, 2 * (v⁻¹ • y) 2 - 3 * (v⁻¹ • y) 1, ?_⟩
  have e := congrArg (v • ·) (d4t_perp_J hy)
  simp only [smul_inv_smul, smul_add] at e
  exact e.trans (by rw [smul_comm v _ d4tE1, smul_comm v _ d4tE2])

private theorem d4t_iform_perm (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice e6RhoFour x) (permLattice e6RhoFour y) = iform x y := by
  rw [e6RhoFour_eq_twistPerm]
  exact iform_permLattice_E6 x y

private theorem d4t_perp_stable {w : WeylGroup Tag.E6} {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ ∈ Ψ, ∃ δ ∈ Ψ, γ = w • permLattice e6RhoFour δ)
    {f : Fin Tag.E6.rank → ℤ} (hf : ∀ γ ∈ Ψ, iform γ f = 0) :
    ∀ γ ∈ Ψ, iform γ (w • permLattice e6RhoFour f) = 0 := by
  intro γ hγ
  obtain ⟨δ, hδ, rfl⟩ := hρ γ hγ
  rw [iform_smul, d4t_iform_perm]
  exact hf δ hδ

private theorem d4t_foldr_mul {K : Type} [Field K] (ω : List (Fin Tag.E6.rank))
    (a b : Fin Tag.E6.rank → Kˣ) :
    ω.foldr e6StarS (a * b) = ω.foldr e6StarS a * ω.foldr e6StarS b := by
  induction ω with
  | nil => rfl
  | cons j ω ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, e6StarS_mul]

private theorem d4t_twPhi_mono {L : Type} [Field L] {q : ℕ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (ω : List (Fin Tag.E6.rank)) (s t : Lˣ)
    (m₁ m₂ : Fin Tag.E6.rank → ℤ) :
    twPhi Fr ω (fun l => s ^ m₁ l * t ^ m₂ l) =
      fun l => (s ^ q) ^ (((coxeterSystem Tag.E6).wordProd ω • permLattice e6RhoFour m₁) l) *
        (t ^ q) ^ (((coxeterSystem Tag.E6).wordProd ω • permLattice e6RhoFour m₂) l) := by
  have hmap : ∀ x : Lˣ, Units.map Fr.toMonoidHom x = x ^ q := fun x =>
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  have hperm : ∀ (m : Fin Tag.E6.rank → ℤ) (l : Fin Tag.E6.rank),
      permLattice e6RhoFour m l = m (e6RhoFour l) := fun m l => by
    simp only [permLattice, Function.comp_apply, e6RhoFour_symm_apply]
  have h1 : twPhi Fr ω (fun l => s ^ m₁ l * t ^ m₂ l) = ω.foldr e6StarS
      ((fun l => (s ^ q) ^ permLattice e6RhoFour m₁ l) *
        fun l => (t ^ q) ^ permLattice e6RhoFour m₂ l) := by
    unfold twPhi
    congr 1
    funext l
    rw [Pi.mul_apply, map_mul, map_zpow, map_zpow, hmap, hmap, hperm, hperm]
  rw [h1, d4t_foldr_mul, foldr_e6StarS_zpow, foldr_e6StarS_zpow, ← wordProd_smul_eq_foldr,
    ← wordProd_smul_eq_foldr]
  rfl

private theorem d4t_zpow_comb {G : Type*} [CommGroup G] {S T s t ζ : G} {r₁₁ r₁₂ r₂₁ r₂₂ : ℤ}
    (h₁ : S ^ r₁₁ * T ^ r₂₁ = s) (h₂ : S ^ r₁₂ * T ^ r₂₂ = t * ζ) (a b : ℤ) :
    S ^ (r₁₁ * a + r₁₂ * b) * T ^ (r₂₁ * a + r₂₂ * b) = s ^ a * t ^ b * ζ ^ b := by
  rw [zpow_add, zpow_add, mul_mul_mul_comm, zpow_mul, zpow_mul, zpow_mul, zpow_mul,
    ← mul_zpow, ← mul_zpow, h₁, h₂, mul_zpow, mul_assoc]

private theorem d4t_rootChar_mul {K : Type} [Field K] (a b : Fin Tag.E6.rank → Kˣ)
    (γ : Fin Tag.E6.rank → ℤ) :
    FourGroupChevalley.rootChar (a * b) γ =
      FourGroupChevalley.rootChar a γ * FourGroupChevalley.rootChar b γ := by
  simp only [FourGroupChevalley.rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem d4t_e6RootParams_zpow {K : Type} [Field K] (x : Kˣ)
    (m : Fin Tag.E6.rank → ℤ) (j : Fin Tag.E6.rank) :
    e6RootParams (fun l => x ^ m l) j = x ^ (∑ l, Tag.E6.cartan l j * m l) := by
  simp only [e6RootParams]
  rw [← liftProd_zpow_sum]
  exact Finset.prod_congr rfl fun l _ => by rw [← zpow_mul, mul_comm]

private theorem d4t_rootChar_mono {K : Type} [Field K] (x : Kˣ) (m γ : Fin Tag.E6.rank → ℤ) :
    FourGroupChevalley.rootChar (e6RootParams fun l => x ^ m l) γ = x ^ iform m γ := by
  simp only [FourGroupChevalley.rootChar, d4t_e6RootParams_zpow, ← zpow_mul]
  rw [liftProd_zpow_sum, iform, d4t_symm]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem d4t2ct_exists_lang {L : Type} [Field L] [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) 3)
    (ω : List (Fin Tag.E6.rank)) (v : WeylGroup Tag.E6) {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ Ψ, ∃ δ ∈ Ψ, γ = (coxeterSystem Tag.E6).wordProd ω • permLattice e6RhoFour δ) :
    ∃ u z : Fin Tag.E6.rank → Lˣ, twPhi Fr ω u = u * z ∧ e6RootParams z = 1 ∧ z ≠ 1 ∧
      ∀ γ ∈ Ψ, FourGroupChevalley.rootChar (e6RootParams u) γ = 1 := by
  classical
  subst hΨ
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ3 : ζ ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hζu.pow_eq_one
  have hperp := fun γ hγ => d4t_perp_f (v := v) (γ := γ) hγ
  obtain ⟨r₁₁, r₁₂, e₁⟩ := d4t_perp_span (d4t_perp_stable hρ fun γ hγ => (hperp γ hγ).1)
  obtain ⟨r₂₁, r₂₂, e₂⟩ := d4t_perp_span (d4t_perp_stable hρ fun γ hγ => (hperp γ hγ).2)
  let B : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(q : ℤ) * r₁₁ - 1, (q : ℤ) * r₂₁; (q : ℤ) * r₁₂, (q : ℤ) * r₂₂ - 1]
  have hB : B.det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h
    have h1 : (q : ℤ) ∣ 1 :=
      ⟨-((q : ℤ) * r₁₁ * r₂₂ - r₁₁ - r₂₂ - q * r₁₂ * r₂₁), by linear_combination h⟩
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  obtain ⟨st, hst⟩ := monoHom_surjective_of_det_ne_zero (L := L) B hB ![1, ζ]
  have hst0 := congrFun hst 0
  have hst1 := congrFun hst 1
  simp only [monoHom_apply, Fin.prod_univ_two, B, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons] at hst0 hst1
  have hs : (st 0 ^ q) ^ r₁₁ * (st 1 ^ q) ^ r₂₁ = st 0 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    rw [zpow_sub_one, mul_right_comm, mul_inv_eq_one] at hst0
    exact hst0
  have ht : (st 0 ^ q) ^ r₁₂ * (st 1 ^ q) ^ r₂₂ = st 1 * ζ := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    rw [zpow_sub_one, ← mul_assoc, mul_inv_eq_iff_eq_mul] at hst1
    rw [hst1, mul_comm]
  refine ⟨fun l => st 0 ^ (v • d4tE1) l * st 1 ^ (v • d4tE2) l,
    fun l => ζ ^ (v • d4tE2) l, ?_, ?_, ?_, ?_⟩
  · rw [d4t_twPhi_mono hFr, e₁, e₂]
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    exact d4t_zpow_comb hs ht _ _
  · funext j
    have h1 : ∑ l, Tag.E6.cartan l j * (v • d4tE2) l =
        3 * (v⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 := by
      have h2 : iform (Pi.single j 1) (v • d4tE2) = ∑ l, Tag.E6.cartan l j * (v • d4tE2) l := by
        rw [d4t_iform_single]
        exact Finset.sum_congr rfl fun l _ => by rw [e6Cartan_symm']
      rw [← h2, ← d4t_iform_e2, ← iform_smul v⁻¹, inv_smul_smul]
    rw [d4t_e6RootParams_zpow, h1, zpow_mul, hζ3, one_zpow]
    rfl
  · intro hz
    have h0 : ∀ l, (3 : ℤ) ∣ (v • d4tE2) l := fun l => by
      have h := congrFun hz l
      exact_mod_cast (hζu.zpow_eq_one_iff_dvd _).1 h
    choose g hg using h0
    have h3 : v • d4tE2 = (3 : ℤ) • g := funext fun l => by
      rw [hg l, Pi.smul_apply, smul_eq_mul]
    have h4 : d4tE2 = (3 : ℤ) • (v⁻¹ • g) := by
      rw [smul_comm, ← h3, inv_smul_smul]
    have h5 : (4 : ℤ) = 3 * (v⁻¹ • g) 0 := congrFun h4 0
    omega
  · intro γ hγ
    have hu : (fun l => st 0 ^ (v • d4tE1) l * st 1 ^ (v • d4tE2) l) =
        (fun l => st 0 ^ (v • d4tE1) l) * fun l => st 1 ^ (v • d4tE2) l := rfl
    rw [hu, e6RootParams_mul', d4t_rootChar_mul, d4t_rootChar_mono, d4t_rootChar_mono,
      iform_comm _ γ, iform_comm _ γ, (hperp γ hγ).1, (hperp γ hγ).2, zpow_zero, zpow_zero,
      mul_one]

end Lang

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
