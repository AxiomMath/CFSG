module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniNorm

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {F : Type*} [Field F]

@[expose] def diagPairSL {n : ℕ} {i k : Fin n} (hik : i ≠ k) (a : Fˣ) :
    SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal (fun r => if r = i then (a : F) else if r = k then ((a⁻¹ : Fˣ) : F) else 1), by
    rw [Matrix.det_diagonal]
    have h : ∀ r : Fin n, (if r = i then (a : F) else if r = k then ((a⁻¹ : Fˣ) : F) else 1) =
        (if r = i then (a : F) else 1) * (if r = k then ((a⁻¹ : Fˣ) : F) else 1) := by
      intro r
      by_cases hri : r = i
      · subst hri
        simp [hik]
      · by_cases hrk : r = k
        · subst hrk
          simp [hri]
        · simp [hri, hrk]
    rw [Finset.prod_congr rfl (fun r _ => h r), Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq']
    simp⟩

theorem coe_diagPairSL {n : ℕ} {i k : Fin n} (hik : i ≠ k) (a : Fˣ) :
    ((diagPairSL hik a : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun r => if r = i then (a : F) else if r = k then ((a⁻¹ : Fˣ) : F) else 1) :=
  rfl

theorem diagPairSL_conj_transvection {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a : Fˣ) (c : F) :
    diagPairSL hik a * SpecialLinearGroup.transvection hij c * (diagPairSL hik a)⁻¹ =
      SpecialLinearGroup.transvection hij (a * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext r s
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, coe_diagPairSL,
    Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.single_apply]
  congr 1
  by_cases h : i = r ∧ j = s
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij.symm, hjk]
  · simp [h]

theorem projUnitriangular_four_le_closure :
    projUnitriangular 4 F ≤ closure {z : projectiveSL 4 F | z ∈ projUnitriangular 4 F ∧
      ∃ (i j : Fin 4) (hij : i < j) (m : SpecialLinearGroup (Fin 4) F),
        z = proj 4 F m * proj 4 F (SpecialLinearGroup.transvection hij.ne 1) *
          (proj 4 F m)⁻¹} := by
  have key : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  rintro _ ⟨u, hu, rfl⟩
  have h1 : proj 4 F u ∈
      (Subgroup.closure {g | ∃ i j a, i < j ∧ LinearCover.rootElt i j a = g}).map (proj 4 F) :=
    mem_map_of_mem _ (LinearCover.unitriangular_le_closure_rootElt hu)
  rw [MonoidHom.map_closure] at h1
  refine (closure_le _).2 ?_ h1
  rintro _ ⟨_, ⟨i, j, a, hij, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, LinearCover.rootElt_of_ne hij.ne]
  by_cases ha : a = 0
  · rw [ha, SpecialLinearGroup.transvection_coeff_zero, map_one]
    exact one_mem _
  · obtain ⟨k, hki, hkj⟩ := key i j
    refine subset_closure ⟨proj_transvection_mem_projUnitriangular hij a, i, j, hij,
      diagPairSL hki.symm (Units.mk0 a ha), ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul, diagPairSL_conj_transvection hij.ne hki.symm hkj.symm,
      Units.val_mk0, mul_one]

end Model

section Field

variable {X : Type} [Group X]

theorem le_closure_conj_involutions_of_fieldComponent [Finite X] {K : Type} [Field K]
    (hK : Nat.card K = 2) {s : X} (hs : orderOf s = 2) {Lb : Subgroup X}
    (hLs : Lb ≤ centralizer ({s} : Set X)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set X) ≤ Lb ⊔ zpowers s) {Ks : Subgroup X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hsK : s ∉ Ks) (hLK : Lb ≤ Ks)
    (hKm : LieModel Ks .PSL 4 2 2) (φ : SpecialLinearGroup (Fin 4) K →* X) (hφ : φ.range = Lb)
    {S : Subgroup X} (hSK : S ≤ Ks) (hS2 : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → S ≤ R → R ≤ Ks → R = S) {Q : Subgroup X}
    (hQS : Q ≤ S) (hQs : Q ≤ centralizer ({s} : Set X)) (hQc : 2 ^ 6 ≤ Nat.card Q) :
    S ≤ Subgroup.closure {y : X | y ∈ S ∧ ∃ n ∈ Ks, ∃ q ∈ Lb, q * q = 1 ∧ y = n * q * n⁻¹} := by
  classical
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  obtain ⟨F, _, _, _, ι, σ, ψ, hF4, -, -, -, hψL, -⟩ :=
    exists_normalized_mulEquiv_of_lieModel_four_four hK hs hLs hLq hLZ hCs hsN hsK hLK hKm φ hφ
  have hfixL : ∀ x ∈ Ks, x ∈ centralizer ({s} : Set X) → x ∈ Lb := by
    intro x hxK hxs
    rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hxs with h | h
    · exact h
    · exfalso
      apply hsK
      have h1 : x⁻¹ * (x * s) = s := by group
      rw [← h1]
      exact mul_mem (inv_mem hxK) (hLK h)
  set Qψ : Subgroup (projectiveSL 4 F) := (Q.subgroupOf Ks).map ψ.toMonoidHom with hQψ
  set Q' : Subgroup (projectiveSL 4 K) := Qψ.comap (projMap 4 ι) with hQ'
  have hQψι : Qψ ≤ (projMap 4 ι).range := by
    rintro _ ⟨k, hk, rfl⟩
    exact hψL k (hfixL _ k.2 (hQs (mem_subgroupOf.1 hk)))
  have hQ'map : Q'.map (projMap 4 ι) = Qψ := map_comap_eq_self hQψι
  have hinjι : Function.Injective (projMap 4 ι) := projMap_injective (by norm_num) ι
  have hQ'c : 2 ^ 6 ≤ Nat.card Q' := by
    have h1 : Nat.card Q' = Nat.card Qψ := by rw [← hQ'map, card_map_of_injective hinjι]
    have h2 : Nat.card Qψ = Nat.card Q := by
      rw [hQψ, card_map_of_injective ψ.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe (hQS.trans hSK)).toEquiv
    rw [h1, h2]
    exact hQc
  have hQ'2 : IsPGroup 2 Q' :=
    (((hS2.to_le hQS).comap_subtype (K := Ks)).map ψ.toMonoidHom).comap_of_injective _ hinjι
  obtain ⟨h, hh⟩ := exists_conj_projUnitriangular_le_of_card hK hQ'2 hQ'c
  set g := projMap 4 ι h with hgdef
  have hgQ : ∀ (i j : Fin 4) (hij : i < j),
      g * proj 4 F (SpecialLinearGroup.transvection hij.ne 1) * g⁻¹ ∈ Qψ := by
    intro i j hij
    have h1 := hh _ (proj_transvection_mem_projUnitriangular hij (1 : K))
    have h3 : projMap 4 ι (h * proj 4 K (SpecialLinearGroup.transvection hij.ne 1) * h⁻¹) ∈
        Qψ := h1
    rwa [map_mul, map_mul, map_inv, ← hgdef, projMap_proj, specialLinearGroup_map_transvection,
      map_one] at h3
  set Sψ : Subgroup (projectiveSL 4 F) := (S.subgroupOf Ks).map ψ.toMonoidHom with hSψ
  have hSψ2 : IsPGroup 2 Sψ := (hS2.comap_subtype (K := Ks)).map _
  have hconjU : ∀ x ∈ Sψ, g⁻¹ * x * g ∈ projUnitriangular 4 F := by
    have hP' := le_projUnitriangular_of_isPGroup (F := F) (n := 4) (by rw [hF4]; norm_num)
      isPGroup_scalars_four (hSψ2.map (MulAut.conj g⁻¹).toMonoidHom) (fun i j hij hij1 => by
        have hlt : i < j := Fin.lt_def.2 (by omega)
        have h2 : g * proj 4 F (SpecialLinearGroup.transvection hlt.ne 1) * g⁻¹ ∈ Sψ := by
          obtain ⟨k, hk, hk'⟩ := hgQ i j hlt
          exact ⟨k, mem_subgroupOf.2 (hQS (mem_subgroupOf.1 hk)), hk'⟩
        refine ⟨_, h2, ?_⟩
        change MulAut.conj g⁻¹ _ = _
        rw [MulAut.conj_apply]
        group)
    intro x hx
    have h1 : MulAut.conj g⁻¹ x ∈ projUnitriangular 4 F := hP' ⟨x, hx, rfl⟩
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  set R : Subgroup X := (((projUnitriangular 4 F).map (MulAut.conj g).toMonoidHom).map
    ψ.symm.toMonoidHom).map Ks.subtype with hR
  have hR2 : IsPGroup 2 R := ((((isPGroup_projUnitriangular_four hF4).1.map _).map _).map _)
  have hSR : S ≤ R := by
    intro x hx
    have hxK := hSK hx
    have h1 : g⁻¹ * ψ ⟨x, hxK⟩ * g ∈ projUnitriangular 4 F :=
      hconjU _ ⟨⟨x, hxK⟩, mem_subgroupOf.2 hx, rfl⟩
    refine ⟨⟨x, hxK⟩, ⟨ψ ⟨x, hxK⟩, ⟨g⁻¹ * ψ ⟨x, hxK⟩ * g, h1, ?_⟩, ?_⟩, rfl⟩
    · change MulAut.conj g _ = _
      rw [MulAut.conj_apply]
      group
    · change ψ.symm (ψ ⟨x, hxK⟩) = _
      rw [MulEquiv.symm_apply_apply]
  have hRS : R = S := hmax R hR2 hSR (map_subtype_le _)
  set f : projectiveSL 4 F →* X :=
    Ks.subtype.comp (ψ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hfdef
  have hfapp : ∀ z, f z = ((ψ.symm (g * z * g⁻¹) : Ks) : X) := fun z => rfl
  intro x hx
  have hxK := hSK hx
  have h1 : g⁻¹ * ψ ⟨x, hxK⟩ * g ∈ projUnitriangular 4 F :=
    hconjU _ ⟨⟨x, hxK⟩, mem_subgroupOf.2 hx, rfl⟩
  have h2 := mem_map_of_mem f (projUnitriangular_four_le_closure h1)
  have h3 : f (g⁻¹ * ψ ⟨x, hxK⟩ * g) = x := by
    rw [hfapp]
    have h4 : g * (g⁻¹ * ψ ⟨x, hxK⟩ * g) * g⁻¹ = ψ ⟨x, hxK⟩ := by group
    rw [h4, MulEquiv.symm_apply_apply]
  rw [MonoidHom.map_closure, h3] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨z, ⟨hzU, i, j, hij, m, rfl⟩, rfl⟩
  set T := proj 4 F (SpecialLinearGroup.transvection hij.ne (1 : F)) with hT
  refine ⟨?_, f (proj 4 F m), (ψ.symm _).2, f T, ?_, ?_, ?_⟩
  · rw [← hRS]
    exact ⟨ψ.symm _, ⟨_, ⟨_, hzU, rfl⟩, rfl⟩, rfl⟩
  ·
    obtain ⟨k, hk, hk'⟩ := hgQ i j hij
    have hkq : ψ.symm (g * T * g⁻¹) = k := by
      rw [← hk']
      exact ψ.symm_apply_apply k
    have hkQ : ((k : Ks) : X) ∈ Q := mem_subgroupOf.1 hk
    rw [hfapp, hkq]
    exact hfixL _ k.2 (hQs hkQ)
  ·
    rw [← map_mul, hT, ← map_mul, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero, map_one, map_one]
  · simp only [map_mul, map_inv]

end Field

end CFSG.SeitzReduction.LinearPilot
