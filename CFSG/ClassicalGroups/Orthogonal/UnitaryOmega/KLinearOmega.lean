module

public import CFSG.Timmesfeld.Orders.ClassicalHypSum
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.RestrictScalars

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.OrthogonalInvolutions

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {σ : K ≃+* K}

omit [Finite K] [CharP K 2] in
private lemma commSpace_hypExt {m : ℕ} {g : (Fin m → K) ≃ₗ[F] (Fin m → K)} :
    commSpace (hypExt (K := F) g) =
      (commSpace g).map (LinearMap.inr F (F × F) (Fin m → K)) := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨g v.2 - v.2, sub_mem_commSpace g v.2, ?_⟩
    have hx : x = ((0 : F × F), g v.2 - v.2) := by
      rw [← hv]
      ext <;> simp [hypExt_apply]
    rw [hx]
    rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    refine ⟨((0 : F × F), v), ?_⟩
    ext <;> simp [hypExt_apply]

omit [Finite K] [CharP K 2] in
theorem finrank_commSpace_hypExt {m : ℕ}
    {g : (Fin m → K) ≃ₗ[F] (Fin m → K)} :
    Module.finrank F (commSpace (hypExt (K := F) g)) = Module.finrank F (commSpace g) := by
  rw [commSpace_hypExt, ← (Submodule.equivMapOfInjective
    (LinearMap.inr F (F × F) (Fin m → K))
    (LinearMap.inr_injective (M := F × F) (M₂ := Fin m → K)) (commSpace g)).finrank_eq]

omit [Finite K] [CharP K 2] in
private lemma even_finrank_commSpace_of_kLinear (E : QuadExt F K σ) {m : ℕ}
    {g : (Fin m → K) ≃ₗ[F] (Fin m → K)}
    (hKg : ∀ (c : K) (x : Fin m → K), g (c • x) = c • g x) :
    Even (Module.finrank F (commSpace g)) := by
  let gK : (Fin m → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun x => g x
      map_add' := fun x y => map_add g x y
      map_smul' := fun c x => hKg c x }
  have hcomm : commSpace g = (LinearMap.range (gK - 1)).restrictScalars F := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, hv⟩
  rw [hcomm]
  exact CFSG.StandardType.ClassicalPosition.even_finrank_restrictScalars
    (K := F) (A := K) (V := Fin m → K) (by rw [E.finrank_eq]; exact even_two) _

omit [Finite K] [CharP K 2] in
private lemma even_finrank_commSpace_hypExt (E : QuadExt F K σ) {m : ℕ}
    {g : (Fin m → K) ≃ₗ[F] (Fin m → K)}
    (hKg : ∀ (c : K) (x : Fin m → K), g (c • x) = c • g x) :
    Even (Module.finrank F (commSpace (hypExt (K := F) g))) := by
  rw [finrank_commSpace_hypExt]
  exact even_finrank_commSpace_of_kLinear E hKg

omit [Finite K] [CharP K 2] in
private lemma Qn_single_add_single (E : QuadExt F K σ) {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    [CharP F 2] (y : K) :
    Qn E m ((Pi.single i y : Fin m → K) + Pi.single j y) = 0 := by
  rw [Qn_apply]
  rw [← Finset.sum_subset (s₁ := {i, j}) (s₂ := Finset.univ) (Finset.subset_univ _) ?_]
  · rw [Finset.sum_pair hij]
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add, add_zero]
    exact CharTwo.add_self_eq_zero _
  · intro k _ hk
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hki, hkj⟩ := hk
    simp [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

omit [Finite K] [CharP K 2] in
theorem exists_totallySingular_three_hypSum (E : QuadExt F K σ) {m : ℕ} (hm : 2 ≤ m)
    [CharP F 2] :
    ∃ T : Submodule F ((F × F) × (Fin m → K)),
      Module.finrank F T = 3 ∧ ∀ x ∈ T, hypSum (Qn E m) x = 0 := by
  classical
  have hfd : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  let ι : F × K →ₗ[F] (F × F) × (Fin m → K) :=
    { toFun := fun p => ((p.1, 0), Pi.single i₀ p.2 + Pi.single i₁ p.2)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Pi.single_add, Prod.mk_add_mk]
        abel_nf
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.single_smul, Prod.smul_mk, RingHom.id_apply,
          smul_eq_mul]
        rw [smul_add, mul_zero] }
  have hinj : Function.Injective ι := by
    rintro ⟨a, y⟩ ⟨b, z⟩ h
    have h1 : a = b := by
      simpa [ι] using congrArg (fun p => p.1.1) h
    have h2 : y = z := by
      have hh := congrArg (fun p => p.2 i₀) h
      simpa [ι, h01] using hh
    rw [h1, h2]
  refine ⟨LinearMap.range ι, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self,
      E.finrank_eq]
  · rintro x ⟨p, rfl⟩
    change p.1 * 0 + Qn E m (Pi.single i₀ p.2 + Pi.single i₁ p.2) = 0
    rw [mul_zero, zero_add]
    exact Qn_single_add_single E h01 p.2

theorem hypExt_mem_orthDerived_of_kLinear (E : QuadExt F K σ) {m : ℕ} (hm : 2 ≤ m)
    {g : (Fin m → K) ≃ₗ[F] (Fin m → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E m))
    (hK : ∀ (c : K) (x : Fin m → K), g (c • x) = c • g x) :
    hypExt g ∈ CFSG.RankThree.Classical2.orthDerived (hypSum (Qn E m)) := by
  have hFinF : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have hF2 : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have hFd : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hQ := CFSG.Timmesfeld.ClassicalOrders.nondegenerate_polarBilin_hypSum
    (CFSG.ClassicalInvolution.PhanDn.Qn_polarBilin_nondegenerate E m)
  have hmem : hypExt g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (hypSum (Qn E m)) hQ :=
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
      ⟨CFSG.Timmesfeld.ClassicalOrders.hypExt_mem hg,
        even_finrank_commSpace_hypExt E hK⟩
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ
    (exists_totallySingular_three_hypSum E hm) hmem

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
