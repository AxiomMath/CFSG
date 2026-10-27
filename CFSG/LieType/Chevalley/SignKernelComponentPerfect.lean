module

public import CFSG.LieType.Chevalley.SignKernelWitnesses
public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.LieType.Chevalley.RootCommutatorCertificate

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix RootOps

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_mem_commutator_of_conj_eq_neg
    {S : Subgroup (ModGL τ K)} (h2 : (2 : K) ≠ 0)
    {h : ModGL τ K} (hh : h ∈ S) {α : Fin τ.rank → ℤ} (hS : ∀ c, pinnedX τ K α c ∈ S)
    (hconj : ∀ c, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (-c)) (c : K) :
    pinnedX τ K α c ∈ ⁅S, S⁆ := by
  have e : pinnedX τ K α c = h * pinnedX τ K α (-(2⁻¹ * c)) * h⁻¹ *
      (pinnedX τ K α (-(2⁻¹ * c)))⁻¹ := by
    rw [hconj, pinnedX_neg, ← pinnedX_add, neg_neg, ← two_mul, ← mul_assoc,
      mul_inv_cancel₀ h2, one_mul]
  rw [e, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hh (hS _)

theorem canonicalRep_conj_torusElt_conj_pinnedX
    (w : WeylGroup τ) (k : Fin τ.rank) (t : Kˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹) * pinnedX τ K α c *
      (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹)⁻¹ =
      pinnedX τ K α (((t ^ (∑ l, τ.cartan k l * (w⁻¹ • α) l) : Kˣ) : K) * c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (IsRoot.smul hα w⁻¹)
  rw [smul_inv_smul] at h
  set n := canonicalRep (coxeterSystem τ) K w
  have h' : n⁻¹ * pinnedX τ K α c * n = pinnedX τ K (w⁻¹ • α) (ε * c) := by
    have e := h (ε * c)
    rw [← mul_assoc, hε, one_mul] at e
    rw [← e]
    group
  have h2 := root_torus_conjugation k (IsRoot.smul hα w⁻¹) t (ε * c)
  calc _ = n * (torusElt τ K k t * (n⁻¹ * pinnedX τ K α c * n) * (torusElt τ K k t)⁻¹) * n⁻¹ := by
        group
    _ = n * pinnedX τ K (w⁻¹ • α) (((t ^ (∑ l, τ.cartan k l * (w⁻¹ • α) l) : Kˣ) : K) *
        (ε * c)) * n⁻¹ := by rw [h', h2]
    _ = _ := by
        rw [h]
        congr 1
        linear_combination (((t ^ (∑ l, τ.cartan k l * (w⁻¹ • α) l) : Kˣ) : K) * c) * hε

theorem pinnedX_mem_commutator_of_odd
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} (h2 : (2 : K) ≠ 0)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ i)
    {n : ℤ} (hn : Odd n)
    (hodd : n * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) = 2 * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α)))
    (c : K) : pinnedX τ K α c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hαr := isRoot_of_mem_componentRoots hα
  have hβr := isRoot_of_mem_componentRoots hβ
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hβr
  have hh := componentTorus_le_componentRootSpan K χ i
    (canonicalRep_conj_torusElt_mem (K := K) (by rw [hwk]; exact hβ) (-1))
  have hm : ∑ l, τ.cartan k l * (w⁻¹ • α) l = n := by
    rw [← corootPair_smul_single, hwk, corootPair]
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform] at hodd
    rw [← hodd, Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hβr).ne']
  refine pinnedX_mem_commutator_of_conj_eq_neg h2 hh (fun d => pinnedX_mem_rootSpan hα d)
    (fun d => ?_) c
  rw [canonicalRep_conj_torusElt_conj_pinnedX w k (-1) hαr d, hm, hn.neg_one_zpow,
    Units.val_neg, Units.val_one, neg_one_mul]

theorem wordProd_smul_eq_foldr_reflect
    (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (fun i v => reflect τ i v) v := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] def f4PairWord
    : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd (toFinWord [3, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2])

theorem f4PairWord_smul_25
    : f4PairWord • orbitCertRoot .F4 25 = f4Rho := by
  rw [f4PairWord, wordProd_smul_eq_foldr_reflect]
  exact List.ofFn_injective (by decide +kernel)

theorem f4PairWord_smul_28
    : f4PairWord • orbitCertRoot .F4 28 = f4Sigma := by
  rw [f4PairWord, wordProd_smul_eq_foldr_reflect]
  exact List.ofFn_injective (by decide +kernel)

theorem orbitCertRoot_30 : orbitCertRoot .F4 30 = orbitCertRoot .F4 25 + orbitCertRoot .F4 28 :=
  List.ofFn_injective (by decide +kernel)

open MvPolynomial in
theorem f4_pinnedX_commutator_rep
    (s t : K) :
    pinnedX .F4 K (orbitCertRoot .F4 25) s * pinnedX .F4 K (orbitCertRoot .F4 28) t *
        pinnedX .F4 K (orbitCertRoot .F4 25) (-s) * pinnedX .F4 K (orbitCertRoot .F4 28) (-t) =
      pinnedX .F4 K (orbitCertRoot .F4 30) (((-2 : ℤ) : K) * s * t) := by
  have hr : ((25, 28, 144, [(1, 1, 30, -2)]) : PairRow) ∈ pairTable .F4 := by decide +kernel
  have h := ((rank_two_pair_certificate .F4).2 _ hr).2.2.2.2.2.2.2.2.2.2.2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] at h
  set g : MvPolynomial (Fin 2) ℤ →+* K := eval₂Hom (Int.castRingHom K) ![s, t]
  have hg0 : g (X 0) = s := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = t := eval₂Hom_X' _ _ _
  have hL := (((baseChange_pinnedX (τ := .F4) g (orbitCertRoot .F4 25) (X 0)).mul
    (baseChange_pinnedX g (orbitCertRoot .F4 28) (X 1))).mul
    (baseChange_pinnedX g (orbitCertRoot .F4 25) (-X 0))).mul
    (baseChange_pinnedX g (orbitCertRoot .F4 28) (-X 1))
  rw [map_neg, map_neg, hg0, hg1] at hL
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h] at hL
  have hR := baseChange_pinnedX (τ := .F4) g (orbitCertRoot .F4 30)
    (((-2 : ℤ) : MvPolynomial (Fin 2) ℤ) * X 0 * X 1)
  simp only [map_mul, map_intCast, hg0, hg1] at hR
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact hL.unique hR

theorem f4_pinnedX_mem_commutator
    {S : Subgroup (ModGL .F4 K)} (h2 : (2 : K) ≠ 0)
    (w : WeylGroup .F4) (hα : IsRoot .F4 (w • (f4Rho + f4Sigma)))
    (hρ : ∀ c, pinnedX .F4 K (w • f4Rho) c ∈ S) (hσ : ∀ c, pinnedX .F4 K (w • f4Sigma) c ∈ S)
    (c : K) : pinnedX .F4 K (w • (f4Rho + f4Sigma)) c ∈ ⁅S, S⁆ := by
  set v := w * f4PairWord
  have hv25 : v • orbitCertRoot .F4 25 = w • f4Rho := by rw [mul_smul, f4PairWord_smul_25]
  have hv28 : v • orbitCertRoot .F4 28 = w • f4Sigma := by rw [mul_smul, f4PairWord_smul_28]
  have hv30 : v • orbitCertRoot .F4 30 = w • (f4Rho + f4Sigma) := by
    rw [orbitCertRoot_30, smul_add, hv25, hv28, smul_add]
  have hrow : ((25, 28, 144, [(1, 1, 30, -2)]) : PairRow) ∈ pairTable .F4 := by decide +kernel
  have hr25 := ((rank_two_pair_certificate .F4).2 _ hrow).2.2.1
  have hr28 := ((rank_two_pair_certificate .F4).2 _ hrow).2.2.2.1
  have hr30 : IsRoot .F4 (orbitCertRoot .F4 30) := by
    have := IsRoot.smul hα v⁻¹
    rwa [← hv30, inv_smul_smul] at this
  obtain ⟨ε₁, -, h₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K v hr25
  obtain ⟨ε₂, -, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K v hr28
  obtain ⟨ε₃, hε₃, h₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K v hr30
  rw [hv25] at h₁
  rw [hv28] at h₂
  rw [hv30] at h₃
  have hκ : ε₃ * ((-2 : ℤ) : K) ≠ 0 := by
    refine mul_ne_zero (left_ne_zero_of_mul_eq_one hε₃) ?_
    rw [Int.cast_neg, Int.cast_ofNat, neg_ne_zero]
    exact h2
  obtain ⟨t, ht⟩ : ∃ t : K, ε₃ * (((-2 : ℤ) : K) * 1 * t) = c :=
    ⟨(ε₃ * ((-2 : ℤ) : K))⁻¹ * c, by rw [mul_one, ← mul_assoc, mul_inv_cancel_left₀ hκ]⟩
  set n := canonicalRep (coxeterSystem .F4) K v
  have hid := congrArg (fun x => n * x * n⁻¹) (f4_pinnedX_commutator_rep (K := K) 1 t)
  have e : ∀ a₁ a₂ a₃ a₄ : ModGL .F4 K, n * (a₁ * a₂ * a₃ * a₄) * n⁻¹ =
      (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) * (n * a₃ * n⁻¹) * (n * a₄ * n⁻¹) := fun _ _ _ _ => by
    group
  rw [e, h₁, h₁, h₂, h₂, h₃, ht, mul_neg, mul_neg, ← pinnedX_neg, ← pinnedX_neg,
    ← commutatorElement_def] at hid
  rw [← hid]
  exact Subgroup.commutator_mem_commutator (hρ _) (hσ _)

theorem odd_sign_kernel_nonrankone_root_component_perfect
    (τ : Tag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) :
    componentRootSpan K χ i ≤ adjointGroup τ K ∧
      ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine ⟨iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α, le_antisymm ?_ ?_⟩
  · refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases sign_kernel_nonrankone_root_commutator_witnesses τ χ i hi hα with
      ⟨β, hβ, n, hn, hodd⟩ | ⟨rfl, w, hρ, hσ, rfl⟩
    · exact pinnedX_mem_commutator_of_odd h2 hα hβ hn hodd c
    · exact f4_pinnedX_mem_commutator h2 w (isRoot_of_mem_componentRoots hα)
        (fun d => pinnedX_mem_rootSpan hρ d) (fun d => pinnedX_mem_rootSpan hσ d) c

end CFSG.LieType.Chevalley
