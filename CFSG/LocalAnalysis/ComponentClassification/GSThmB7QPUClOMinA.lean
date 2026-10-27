module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)

theorem eq_top_of_normal_not_le_core {G : Type*} [Group G] [Finite G]
    (hres : CatalogueBPrimeJoin.primeResidual 2 G = ⊤)
    (hsimp : IsSimpleGroup (G ⧸ pPrimeCore 2 G)) (N : Subgroup G) [hN : N.Normal]
    (hNO : ¬ N ≤ pPrimeCore 2 G) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (pPrimeCore 2 G) with hφ
  have hmapN : (N.map φ).Normal := Subgroup.Normal.map hN φ (QuotientGroup.mk'_surjective _)
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hb | ht
  · exfalso
    apply hNO
    intro x hx
    have hx' : φ x ∈ N.map φ := ⟨x, hx, rfl⟩
    rw [hb, mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  have hsup : pPrimeCore 2 G ⊔ N = ⊤ := by
    have e := Subgroup.comap_map_eq φ N
    rw [ht, Subgroup.comap_top, hφ, QuotientGroup.ker_mk'] at e
    rw [sup_comm, ← e]
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (pPrimeCore 2 G).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ pPrimeCore 2 G ⊔ N := by rw [hsup]; exact mem_top g
    obtain ⟨o, ho, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
    refine ⟨⟨o, ho⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using hn
  have hdvd : N.index ∣ Nat.card (pPrimeCore 2 G) := by
    rw [Subgroup.index]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hcop : Nat.Coprime 2 N.index :=
    Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := G))
  have h := CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 N hcop
  rw [hres] at h
  exact top_le_iff.1 h

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem exists_normal_pair (h2 : (2 : K) ≠ 0) {g : similarityPairs (oQ (diagGL hw))}
    (hσ : g.val.right = 1) {I : Finset (Fin d)} (hIne : I.Nonempty) {c : Kˣ}
    (hc : ∀ i ∈ I, ∀ j, (g.val.left : Matrix (Fin d) (Fin d) K) i j =
        (if i = j then (c : K) else 0) ∧
      (g.val.left : Matrix (Fin d) (Fin d) K) j i = (if i = j then (c : K) else 0)) :
    ∃ (D : GL (Fin d) K) (hD : D ∈ matrixIsometries (oQ (diagGL hw))),
      D ∈ oIsoBlock K hw Iᶜ ∧ oκ _ (linPair D hD) = oκ _ g := by
  set A := g.val.left with hA
  set D := GeneralLinearGroup.scalar (Fin d) c⁻¹ * A with hDdef
  have hDm : (D : Matrix (Fin d) (Fin d) K) = (c⁻¹ : K) • (A : Matrix (Fin d) (Fin d) K) := by
    rw [hDdef, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val]
  obtain ⟨μ, hμ⟩ := g.2
  have hμ' : ∀ v, oQ (diagGL hw) ((A : Matrix (Fin d) (Fin d) K) *ᵥ v) =
      (μ : K) * oQ (diagGL hw) v := by
    intro v
    have e := hμ v
    rw [coordinateSemilinearMap_apply, hσ] at e
    exact e
  obtain ⟨i, hi⟩ := hIne
  have hAei : (A : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single i 1 = (c : K) • Pi.single i 1 := by
    funext j
    rw [mulVec_single_one, col_apply, Pi.smul_apply, (hc i hi j).2]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hQei : oQ (diagGL hw) (Pi.single i 1) = w i := by
    rw [oQ_apply, coe_diagGL]
    simp [dotProduct, mulVec, diagonal, Pi.single_apply]
  have hμc : (μ : K) = (c : K) * c := by
    have e := hμ' (Pi.single i 1)
    rw [hAei, QuadraticMap.map_smul, hQei, smul_eq_mul] at e
    exact (mul_right_cancel₀ (hw i) e).symm
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hDiso : ∀ v, oQ (diagGL hw) ((D : Matrix (Fin d) (Fin d) K) *ᵥ v) =
      oQ (diagGL hw) v := by
    intro v
    rw [hDm, Matrix.smul_mulVec, QuadraticMap.map_smul, hμ', hμc, smul_eq_mul]
    field_simp
  have hD : D ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_iff _ D).2 fun v => hDiso v
  refine ⟨D, hD, ?_, oκ_eq_of_left_eq (c := c⁻¹) (by rw [linPair_right, hσ]) (by
    rw [linPair_left])⟩
  rw [mem_oIsoBlock_iff]
  refine ⟨(mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) D).1 hD, fun a b hab => ?_⟩
  rw [hDm, Matrix.smul_apply, smul_eq_mul]
  rcases hab with ha | hb
  · rw [Finset.mem_compl, not_not] at ha
    rw [(hc a ha b).1]
    split_ifs <;> simp [hc0]
  · rw [Finset.mem_compl, not_not] at hb
    rw [(hc b hb a).2]
    by_cases hab : a = b
    · subst hab
      simp [hc0]
    · simp [hab, Ne.symm hab]

include hw in
theorem commutator_oBlock_eq (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    (hq : IsQuasisimple (Burgoyne.C.blockP K hw I)) :
    ⁅oBlock K hw I, oBlock K hw I⁆ = oBlock K hw I := by
  have hle := Burgoyne.C.oBlock_le_matrixDerived hw h2 I
  have hP : ⁅Burgoyne.C.blockP K hw I, Burgoyne.C.blockP K hw I⁆ = Burgoyne.C.blockP K hw I :=
    Subgroup.isPerfect_iff.1 hq.1
  refine le_antisymm (commutator_le_self _) fun x hx => ?_
  have hcl : ⁅oBlock K hw I, oBlock K hw I⁆ ≤ matrixDerived (oQ (diagGL hw)) :=
    (commutator_le_self _).trans hle
  have hmap : ((⁅oBlock K hw I, oBlock K hw I⁆ : Subgroup (GL (Fin d) K)).subgroupOf
      (matrixDerived (oQ (diagGL hw)))).map (projH _) = Burgoyne.C.blockP K hw I := by
    rw [← hP]
    change _ = ⁅((oBlock K hw I).subgroupOf _).map (projH _),
      ((oBlock K hw I).subgroupOf _).map (projH _)⁆
    rw [← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL hw))).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle,
      Subgroup.map_subgroupOf_eq_of_le hcl]
  have hxP : projH _ (⟨x, hle hx⟩ : matrixDerived (oQ (diagGL hw))) ∈
      Burgoyne.C.blockP K hw I := ⟨_, mem_subgroupOf.2 hx, rfl⟩
  rw [← hmap] at hxP
  obtain ⟨y, hy, hyx⟩ := hxP
  have hyI : y ∈ (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) :=
    mem_subgroupOf.2 (commutator_le_self _ (mem_subgroupOf.1 hy))
  have h1 := Burgoyne.C.projH_injOn_oBlock hw hIc
    (mul_mem (inv_mem hyI) (mem_subgroupOf.2 hx : (⟨x, hle hx⟩ : matrixDerived _) ∈ _))
    (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
  have hyx' : y = ⟨x, hle hx⟩ := inv_mul_eq_one.1 h1
  have := mem_subgroupOf.1 hy
  rw [hyx'] at this
  exact this

include hw in
theorem mul_sub_one_of_mem_oIsoBlock {I : Finset (Fin d)} {X D : GL (Fin d) K}
    (hX : X ∈ oIsoBlock K hw I) (hD : D ∈ oIsoBlock K hw Iᶜ) :
    (X : Matrix (Fin d) (Fin d) K) * ((D : Matrix (Fin d) (Fin d) K) - 1) =
      (D : Matrix (Fin d) (Fin d) K) - 1 := by
  obtain ⟨-, -, hX2⟩ := hX
  obtain ⟨-, hD1, -⟩ := hD
  rw [Burgoyne.PSL.compInd_compl] at hD1
  have e : (D : Matrix (Fin d) (Fin d) K) - 1 =
      compInd K I * ((D : Matrix (Fin d) (Fin d) K) - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hD1
    rw [Matrix.mul_sub, Matrix.mul_one]
    calc (D : Matrix (Fin d) (Fin d) K) - 1 =
        (D : Matrix (Fin d) (Fin d) K) - compInd K I * D - (1 - compInd K I) +
          (compInd K I * D - compInd K I) := by abel
      _ = compInd K I * D - compInd K I := by rw [hD1, sub_self, zero_add]
  rw [e, ← Matrix.mul_assoc, hX2]

theorem oκ_linPair_one {Q : QuadraticForm K (Fin d → K)}
    (h : (1 : GL (Fin d) K) ∈ matrixIsometries Q) : oκ Q (linPair 1 h) = 1 := by
  rw [show linPair (1 : GL (Fin d) K) h = 1 from Subtype.ext rfl, map_one]

theorem commute_of_kappa_fix {Q : QuadraticForm K (Fin d → K)} {M : Subgroup (GL (Fin d) K)}
    (hMH : M ≤ matrixDerived Q) (hMp : ⁅M, M⁆ = M) {D : GL (Fin d) K}
    (hD : D ∈ matrixIsometries Q)
    (hfix : ∀ Y ∈ M.subgroupOf (matrixDerived Q), oκ Q (linPair D hD) (projH _ Y) = projH _ Y) :
    ∀ X ∈ M, X * D = D * X := by
  intro X hX
  have hperfH : ⁅M.subgroupOf (matrixDerived Q), M.subgroupOf (matrixDerived Q)⁆ =
      M.subgroupOf (matrixDerived Q) := by
    apply Subgroup.map_injective (matrixDerived Q).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMH, hMp]
  have e := kappa_eq_of_fix (linPair D hD) hperfH hfix (X := ⟨X, hMH hX⟩) (mem_subgroupOf.2 hX)
  rw [linPair_left, linPair_right] at e
  have e2 : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = X := by
    ext
    rfl
  change (D : Matrix (Fin d) (Fin d) K) * ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map
    ⇑(1 : K ≃+* K) * ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X at e
  rw [e2] at e
  have e' : D * X * D⁻¹ = X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
  calc X * D = D * X * D⁻¹ * D := by rw [e']
    _ = D * X := by group

theorem mul_sub_one_comm {Y D : GL (Fin d) K} (h : Y * D = D * Y) :
    (Y : Matrix (Fin d) (Fin d) K) * ((D : Matrix (Fin d) (Fin d) K) - 1) =
      ((D : Matrix (Fin d) (Fin d) K) - 1) * (Y : Matrix (Fin d) (Fin d) K) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Units.val_mul, h,
    Units.val_mul]

omit [Field K] in
theorem signMat_compl' {K : Type} [Field K] (J : Finset (Fin d)) :
    signMat K Jᶜ = -signMat K J := by
  ext i j
  simp only [signMat, Matrix.neg_apply, diagonal_apply, Finset.mem_compl]
  split_ifs <;> simp

end CFSG.ComponentClassification.GSThmB.QPUCl
