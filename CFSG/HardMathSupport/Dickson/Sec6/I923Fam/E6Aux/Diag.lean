module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.DiagComm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Timmesfeld.CrossChar
open Subgroup

section Lattice

@[expose] def e6Perm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

@[expose] def e6Lam : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def e6M : Fin Tag.E6.rank → ℤ := ![0, 0, 1, -1, 0, 1]

@[expose] def e6C : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 0, 1, 1]

theorem e6Lam_cartan : ∀ j : Fin Tag.E6.rank,
    ∑ i, Tag.E6.cartan j i * e6Lam i = 3 * e6M j := by
  decide +kernel

theorem e6Lam_perm : ∀ k : Fin Tag.E6.rank,
    e6Lam (e6Perm k) + e6Lam k = 3 * e6C k := by
  decide +kernel

end Lattice

section Kappa

variable (K : Type) [Field K]

@[expose] def e6Rho : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ) where
  toFun b i := b (e6Perm.symm i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def e6Phi : (Fin Tag.E6.rank → Kˣ) →* Kˣ where
  toFun b := ∏ i, b i ^ e6Lam i
  map_one' := by simp
  map_mul' b c := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

@[expose] def e6Cubes : Subgroup Kˣ := (powMonoidHom 3 : Kˣ →* Kˣ).range

@[expose] def e6Kappa : (Fin Tag.E6.rank → Kˣ) →* Kˣ ⧸ e6Cubes K :=
  (QuotientGroup.mk' (e6Cubes K)).comp (e6Phi K)

theorem e6Kappa_pow_three (x : Kˣ ⧸ e6Cubes K) : x ^ 3 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

theorem prod_zpow_monomial {G : Type*} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → ℤ) (t : Fin r → G) :
    ∏ i, (∏ j, t j ^ M i j) ^ lam i = ∏ j, t j ^ (∑ i, M i j * lam i) := by
  have h1 : ∀ i, (∏ j, t j ^ M i j) ^ lam i = ∏ j, t j ^ (M i j * lam i) := fun i => by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_finsetSum]

theorem e6Phi_monomialHom (t : Fin Tag.E6.rank → Kˣ) :
    e6Phi K (monomialHom (G := Kˣ) Tag.E6.cartan.transpose t) = (∏ j, t j ^ e6M j) ^ 3 := by
  change ∏ i, (∏ j, t j ^ Tag.E6.cartan.transpose i j) ^ e6Lam i = _
  rw [prod_zpow_monomial]
  rw [← zpow_natCast, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul]
  have := e6Lam_cartan j
  simp only [Matrix.transpose_apply]
  rw [this]
  congr 1
  push_cast
  ring

theorem e6Phi_rho_mul (b : Fin Tag.E6.rank → Kˣ) :
    e6Phi K (e6Rho K b * b) = (∏ k, b k ^ e6C k) ^ 3 := by
  change ∏ i, ((e6Rho K b * b) i) ^ e6Lam i = _
  have h1 : ∀ i, ((e6Rho K b * b) i) ^ e6Lam i =
      b (e6Perm.symm i) ^ e6Lam i * b i ^ e6Lam i := fun i => mul_zpow _ _ _
  simp only [h1, Finset.prod_mul_distrib]
  have h2 : ∏ i, b (e6Perm.symm i) ^ e6Lam i = ∏ k, b k ^ e6Lam (e6Perm k) := by
    have := Equiv.prod_comp e6Perm.symm (fun k => b k ^ e6Lam (e6Perm k))
    simpa using this
  rw [h2, ← Finset.prod_mul_distrib, ← zpow_natCast, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add, ← zpow_mul, e6Lam_perm k]
  congr 1
  push_cast
  ring

theorem e6Kappa_monomialHom (t : Fin Tag.E6.rank → Kˣ) :
    e6Kappa K (monomialHom (G := Kˣ) Tag.E6.cartan.transpose t) = 1 := by
  change QuotientGroup.mk' (e6Cubes K) (e6Phi K _) = 1
  rw [e6Phi_monomialHom]
  exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩

theorem e6Kappa_rho_mul (b : Fin Tag.E6.rank → Kˣ) :
    e6Kappa K (e6Rho K b * b) = 1 := by
  change QuotientGroup.mk' (e6Cubes K) (e6Phi K _) = 1
  rw [e6Phi_rho_mul]
  exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩

theorem not_three_dvd_card_of_kappa [Finite K] (h : ∀ b, e6Kappa K b = 1) :
    ¬ 3 ∣ Nat.card (Fin Tag.E6.rank → Kˣ) := by
  intro hdvd
  have hK : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdvd
    exact Nat.prime_three.dvd_of_dvd_pow hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hK
  have hcube : ∀ u : Kˣ, u ∈ e6Cubes K := by
    intro u
    have h1 := h (Pi.mulSingle (0 : Fin Tag.E6.rank) u)
    change QuotientGroup.mk' (e6Cubes K) (e6Phi K _) = 1 at h1
    have h2 : e6Phi K (Pi.mulSingle (0 : Fin Tag.E6.rank) u) = u := by
      change ∏ i, (Pi.mulSingle (0 : Fin Tag.E6.rank) u i) ^ e6Lam i = u
      rw [Finset.prod_eq_single (0 : Fin Tag.E6.rank)]
      · simp [e6Lam]
      · intro i _ hi
        simp [Pi.mulSingle_eq_of_ne hi]
      · simp
    rw [h2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hsurj : Function.Surjective (powMonoidHom 3 : Kˣ →* Kˣ) := fun u => hcube u
  have hinj := Finite.injective_iff_surjective.2 hsurj
  have hg3 : (powMonoidHom 3 : Kˣ →* Kˣ) g = (powMonoidHom 3 : Kˣ →* Kˣ) 1 := by
    simp only [powMonoidHom_apply, one_pow]
    rw [← hg]
    exact pow_orderOf_eq_one g
  have := hinj hg3
  rw [this, orderOf_one] at hg
  exact absurd hg (by norm_num)

end Kappa

section Diag


variable (K : Type) [Field K]

@[expose] noncomputable def e6P : ModGL Tag.E6 K := diagramMap TwistTag.E6 K

@[expose] noncomputable def e6Graph : MulAut (adjointGroup Tag.E6 K) :=
  exactNormalAut Tag.E6 K 1 (RingEquiv.refl K) 1

theorem coe_e6Graph (h : adjointGroup Tag.E6 K) :
    ((e6Graph K h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      e6P K * (h : ModGL Tag.E6 K) * (e6P K)⁻¹ := by
  unfold e6Graph
  rw [coe_exactNormalAut]
  have h1 : rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Kˣ) = (1 : ModGL Tag.E6 K) :=
    rootDiagUnit_one
  have h2 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (h : ModGL Tag.E6 K) = h :=
    Units.ext (entrywise_id _)
  rw [h1, h2, inv_one, one_mul, mul_one]
  simp [exactQ, e6P]

theorem e6P_mul_rootDiagUnit (b : Fin Tag.E6.rank → Kˣ) :
    e6P K * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 (e6Rho K b) * e6P K :=
  diagramMap_mul_rootDiagUnit (K := K) (t := TwistTag.E6) b

theorem e6Graph_mul_rootDiag (b : Fin Tag.E6.rank → Kˣ) :
    e6Graph K * rootDiagAutHom Tag.E6 K b = rootDiagAutHom Tag.E6 K (e6Rho K b) * e6Graph K := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have hP := e6P_mul_rootDiagUnit K b
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_e6Graph]
  change e6P K * (rootDiagUnit Tag.E6 b * (h : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹) *
      (e6P K)⁻¹ = rootDiagUnit Tag.E6 (e6Rho K b) * ((e6Graph K h : adjointGroup Tag.E6 K) :
        ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 (e6Rho K b))⁻¹
  rw [coe_e6Graph]
  calc e6P K * (rootDiagUnit Tag.E6 b * (h : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹) *
        (e6P K)⁻¹
      = (e6P K * rootDiagUnit Tag.E6 b) * (h : ModGL Tag.E6 K) *
          (e6P K * rootDiagUnit Tag.E6 b)⁻¹ := by group
    _ = (rootDiagUnit Tag.E6 (e6Rho K b) * e6P K) * (h : ModGL Tag.E6 K) *
          (rootDiagUnit Tag.E6 (e6Rho K b) * e6P K)⁻¹ := by rw [hP]
    _ = rootDiagUnit Tag.E6 (e6Rho K b) * (e6P K * (h : ModGL Tag.E6 K) * (e6P K)⁻¹) *
          (rootDiagUnit Tag.E6 (e6Rho K b))⁻¹ := by group

theorem e6Graph_conj_rootDiag (b : Fin Tag.E6.rank → Kˣ) :
    e6Graph K * rootDiagAutHom Tag.E6 K b * (e6Graph K)⁻¹ =
      rootDiagAutHom Tag.E6 K (e6Rho K b) :=
  mul_inv_eq_iff_eq_mul.2 (e6Graph_mul_rootDiag K b)

end Diag

section Main


variable (K : Type) [Field K] [Finite K]

theorem commutator_adjointGroup_e6 : commutator (adjointGroup Tag.E6 K) = ⊤ := by
  haveI : Group.IsPerfect (adjointGroup Tag.E6 K) :=
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K).1
  exact Group.IsPerfect.commutator_eq_top

theorem rootDiagAutHom_range_le_commutator_e6 :
    (rootDiagAutHom Tag.E6 K).range ≤ commutator (MulAut (adjointGroup Tag.E6 K)) := by
  have hC := commutator_adjointGroup_e6 K
  rintro _ ⟨b, rfl⟩
  have hIm : (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range.index ∣ 3 := by
    have h := (index_range_monomialHom_dvd K Tag.E6.cartan.transpose).2
    rw [Matrix.det_transpose, det_cartan_E6] at h
    exact h
  have hImC : ∀ b ∈ (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range,
      rootDiagAutHom Tag.E6 K b ∈ commutator (MulAut (adjointGroup Tag.E6 K)) := by
    rintro _ ⟨t, rfl⟩
    have h1 : rootDiagAutHom Tag.E6 K (monomialHom (G := Kˣ) Tag.E6.cartan.transpose t) ∈
        inner (adjointGroup Tag.E6 K) := by
      rw [monomialHom_transpose_cartan]
      exact rootDiagAut_cartanChar_mem_inner t
    exact innerAut_le_commutator_of_perfect hC h1
  have hκIm : ∀ b ∈ (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range, e6Kappa K b = 1 := by
    rintro _ ⟨t, rfl⟩
    exact e6Kappa_monomialHom K t
  have key := diag_mem_commutator (G := MulAut (adjointGroup Tag.E6 K))
    (M := Fin Tag.E6.rank → Kˣ) (Q := Kˣ ⧸ e6Cubes K) (rootDiagAutHom Tag.E6 K) (e6Rho K)
    (e6Graph K) (e6Graph_conj_rootDiag K) (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range
    hIm hImC (e6Kappa K) (e6Kappa_pow_three K) hκIm (e6Kappa_rho_mul K)
    (not_three_dvd_card_of_kappa K)
  exact key b

theorem e6Inndiag_le_commutator :
    e6Inndiag K ≤ commutator (MulAut (adjointGroup Tag.E6 K)) :=
  sup_le (innerAut_le_commutator_of_perfect (commutator_adjointGroup_e6 K))
    (rootDiagAutHom_range_le_commutator_e6 K)

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I923
