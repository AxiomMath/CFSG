module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCExt
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParamMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem mat_spEmbed)

section Frame

variable (K : Type) [Field K] {r : ℕ}

@[expose] def pcOMCol (k : Fin (r + 1)) :
    Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → Fin (r + 2) ⊕ Fin (r + 2) → K
  | .inl i => Pi.single (.inl (k.succAbove i).castSucc) 1
  | .inr (.inl i) => Pi.single (.inr (k.succAbove i).castSucc) 1
  | .inr (.inr t) => ![kOmegaVec K (r + 1), Pi.single (.inl k.castSucc) 1 +
      Pi.single (.inr k.castSucc) 1 + Pi.single (.inl (Fin.last (r + 1))) 1] t

@[expose] def pcOMRow (k : Fin (r + 1)) :
    Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → Fin (r + 2) ⊕ Fin (r + 2) → K
  | .inl i => Pi.single (.inl (k.succAbove i).castSucc) 1
  | .inr (.inl i) => Pi.single (.inr (k.succAbove i).castSucc) 1
  | .inr (.inr t) => ![Pi.single (.inr (Fin.last (r + 1))) 1 + Pi.single (.inl k.castSucc) 1 +
      Pi.single (.inr k.castSucc) 1,
      Pi.single (.inl (Fin.last (r + 1))) 1 + Pi.single (.inr (Fin.last (r + 1))) 1] t

@[expose] def pcOMMat (k : Fin (r + 1)) :
    Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K :=
  Matrix.of fun a j => pcOMCol K k j a

@[expose] def pcOMProj (k : Fin (r + 1)) :
    Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) (Fin (r + 2) ⊕ Fin (r + 2)) K :=
  Matrix.of fun j a => pcOMRow K k j a

variable {K} (k : Fin (r + 1))

theorem pcOM_sig_ne_last (i : Fin r) : (k.succAbove i).castSucc ≠ Fin.last (r + 1) :=
  Fin.castSucc_ne_last _

theorem pcOM_sig_ne (i : Fin r) : (k.succAbove i).castSucc ≠ k.castSucc :=
  fun h => Fin.succAbove_ne k i (Fin.castSucc_injective _ h)

theorem pcOM_castSucc_ne_last : k.castSucc ≠ Fin.last (r + 1) := Fin.castSucc_ne_last k

theorem pcOMProj_mulVec_inl (x : Fin (r + 2) ⊕ Fin (r + 2) → K) (i : Fin r) :
    (pcOMProj K k *ᵥ x) (.inl i) = x (.inl (k.succAbove i).castSucc) := by
  simp [pcOMProj, Matrix.mulVec, pcOMRow]

theorem pcOMProj_mulVec_inr (x : Fin (r + 2) ⊕ Fin (r + 2) → K) (i : Fin r) :
    (pcOMProj K k *ᵥ x) (.inr (.inl i)) = x (.inr (k.succAbove i).castSucc) := by
  simp [pcOMProj, Matrix.mulVec, pcOMRow]

theorem pcOMProj_mulVec_u (x : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    (pcOMProj K k *ᵥ x) (.inr (.inr 0)) =
      x (.inr (Fin.last (r + 1))) + x (.inl k.castSucc) + x (.inr k.castSucc) := by
  change (Pi.single (Sum.inr (Fin.last (r + 1))) 1 + Pi.single (Sum.inl k.castSucc) 1 +
    Pi.single (Sum.inr k.castSucc) 1 : Fin (r + 2) ⊕ Fin (r + 2) → K) ⬝ᵥ x = _
  simp [add_dotProduct]

theorem pcOMProj_mulVec_w (x : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    (pcOMProj K k *ᵥ x) (.inr (.inr 1)) =
      x (.inl (Fin.last (r + 1))) + x (.inr (Fin.last (r + 1))) := by
  change (Pi.single (Sum.inl (Fin.last (r + 1))) 1 + Pi.single (Sum.inr (Fin.last (r + 1))) 1 :
    Fin (r + 2) ⊕ Fin (r + 2) → K) ⬝ᵥ x = _
  simp [add_dotProduct]

theorem pcOMMat_mulVec (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    pcOMMat K k *ᵥ y = ∑ i : Fin (r + 1 - 1),
      (y (.inl i) • Pi.single (.inl (k.succAbove i).castSucc) 1 +
      y (.inr (.inl i)) • Pi.single (.inr (k.succAbove i).castSucc) 1) +
      y (.inr (.inr 0)) • kOmegaVec K (r + 1) + y (.inr (.inr 1)) • (Pi.single (.inl k.castSucc) 1 +
        Pi.single (.inr k.castSucc) 1 + Pi.single (.inl (Fin.last (r + 1))) 1) := by
  funext a
  simp only [pcOMMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, pcOMCol, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  have h1 : ∀ i : Fin (r + 1 - 1), (Pi.single (Sum.inl (k.succAbove i).castSucc) (1 : K) :
      Fin (r + 2) ⊕ Fin (r + 2) → K) a * y (Sum.inl i) = y (Sum.inl i) *
        (Pi.single (Sum.inl (k.succAbove i).castSucc) (1 : K) : Fin (r + 2) ⊕ Fin (r + 2) → K) a :=
    fun i => mul_comm _ _
  have h2 : ∀ i : Fin (r + 1 - 1), (Pi.single (Sum.inr (k.succAbove i).castSucc) (1 : K) :
      Fin (r + 2) ⊕ Fin (r + 2) → K) a * y (Sum.inr (Sum.inl i)) = y (Sum.inr (Sum.inl i)) *
        (Pi.single (Sum.inr (k.succAbove i).castSucc) (1 : K) : Fin (r + 2) ⊕ Fin (r + 2) → K) a :=
    fun i => mul_comm _ _
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i]
  ring

theorem pcOMMat_mulVec_sig_inl (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) (i : Fin r) :
    (pcOMMat K k *ᵥ y) (.inl (k.succAbove i).castSucc) = y (.inl i) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, Pi.single_apply, kOmegaVec]

theorem pcOMMat_mulVec_sig_inr (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) (i : Fin r) :
    (pcOMMat K k *ᵥ y) (.inr (k.succAbove i).castSucc) = y (.inr (.inl i)) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, Pi.single_apply, kOmegaVec]

theorem pcOMMat_mulVec_k_inl (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    (pcOMMat K k *ᵥ y) (.inl k.castSucc) = y (.inr (.inr 1)) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, kOmegaVec]

theorem pcOMMat_mulVec_k_inr (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    (pcOMMat K k *ᵥ y) (.inr k.castSucc) = y (.inr (.inr 1)) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, kOmegaVec]

theorem pcOMMat_mulVec_last_inl (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    (pcOMMat K k *ᵥ y) (.inl (Fin.last (r + 1))) = y (.inr (.inr 0)) + y (.inr (.inr 1)) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, kOmegaVec, (pcOM_castSucc_ne_last k).symm]

theorem pcOMMat_mulVec_last_inr (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    (pcOMMat K k *ᵥ y) (.inr (Fin.last (r + 1))) = y (.inr (.inr 0)) := by
  rw [pcOMMat_mulVec]
  simp [Finset.sum_apply, kOmegaVec, (pcOM_castSucc_ne_last k).symm]

variable [CharP K 2]

theorem pcOMProj_mul_pcOMMat : pcOMProj K k * pcOMMat K k = 1 := by
  ext j j'
  have e : (pcOMProj K k * pcOMMat K k) j j' =
      (pcOMProj K k *ᵥ (pcOMMat K k *ᵥ Pi.single j' 1)) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  rw [e]
  have h2 : ∀ c : K, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  rcases j with i | i | t
  · rw [pcOMProj_mulVec_inl, pcOMMat_mulVec_sig_inl]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [pcOMProj_mulVec_inr, pcOMMat_mulVec_sig_inr]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pcOMProj_mulVec_u, pcOMMat_mulVec_last_inr, pcOMMat_mulVec_k_inl, pcOMMat_mulVec_k_inr,
        add_assoc, h2, add_zero]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pcOMProj_mulVec_w, pcOMMat_mulVec_last_inl, pcOMMat_mulVec_last_inr,
        add_right_comm, h2, zero_add]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]

omit [CharP K 2] in
theorem pcOM_quadPlus_split (v : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    StatedQuadPlus (r + 2) K v = ∑ i : Fin (r + 1 - 1),
      v (.inl (k.succAbove i).castSucc) * v (.inr (k.succAbove i).castSucc) +
        v (.inl k.castSucc) * v (.inr k.castSucc) +
          v (.inl (Fin.last (r + 1))) * v (.inr (Fin.last (r + 1))) := by
  have h : StatedQuadPlus (r + 2) K v = ∑ i : Fin r,
      v (.inl (k.succAbove i).castSucc) * v (.inr (k.succAbove i).castSucc) +
        v (.inl k.castSucc) * v (.inr k.castSucc) +
          v (.inl (Fin.last (r + 1))) * v (.inr (Fin.last (r + 1))) := by
    rw [StatedQuadPlus, Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ k]
    ring
  exact h

theorem pcOM_quad (x : Fin (r + 2) ⊕ Fin (r + 2) → K)
    (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    StatedQuadPlus (r + 2) K (x + pcOMMat K k *ᵥ y) - StatedQuadPlus (r + 2) K x =
      StatedQuadMinus (r + 1) K 1 1 (pcOMProj K k *ᵥ x + y) -
        StatedQuadMinus (r + 1) K 1 1 (pcOMProj K k *ᵥ x) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pcOM_quadPlus_split k, pcOM_quadPlus_split k]
  simp only [Pi.add_apply, pcOMMat_mulVec_sig_inl, pcOMMat_mulVec_sig_inr, pcOMMat_mulVec_k_inl,
    pcOMMat_mulVec_k_inr, pcOMMat_mulVec_last_inl, pcOMMat_mulVec_last_inr]
  simp only [StatedQuadMinus, Pi.add_apply, pcOMProj_mulVec_inl, pcOMProj_mulVec_inr,
    pcOMProj_mulVec_u, pcOMProj_mulVec_w]
  linear_combination (-((x (.inr (Fin.last (r + 1))) + x (.inl k.castSucc) +
    x (.inr k.castSucc)) * y (.inr (.inr 0)) + (x (.inl (Fin.last (r + 1))) +
      x (.inr (Fin.last (r + 1)))) * y (.inr (.inr 1)))) * h2

omit [CharP K 2] in
theorem pcOMMat_mulVec_vec : pcOMMat K k *ᵥ kOmMVec K r = kOmegaVec K (r + 1) := by
  rw [pcOMMat_mulVec]
  simp [kOmMVec]

omit [CharP K 2] in
theorem pcOMProj_mulVec_single_k (b : Fin (r + 2) ⊕ Fin (r + 2))
    (hb : b = .inl k.castSucc ∨ b = .inr k.castSucc) :
    pcOMProj K k *ᵥ Pi.single b 1 = kOmMVec K r := by
  funext j
  rcases j with i | i | t
  · rw [pcOMProj_mulVec_inl]
    rcases hb with rfl | rfl <;> simp [kOmMVec]
  · rw [pcOMProj_mulVec_inr]
    rcases hb with rfl | rfl <;> simp [kOmMVec]
  · fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pcOMProj_mulVec_u]
      rcases hb with rfl | rfl <;> simp [kOmMVec]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pcOMProj_mulVec_w]
      rcases hb with rfl | rfl <;>
        simp [kOmMVec, (pcOM_castSucc_ne_last k).symm]

omit [CharP K 2] in
theorem pcOMProj_mulVec_single_sig (b' : Fin r ⊕ Fin r) :
    pcOMProj K k *ᵥ Pi.single (kOmegaEmb (r + 1) (Sum.map k.succAbove k.succAbove b')) 1 =
      Pi.single (kOmMEmb r b') 1 := by
  funext j
  rcases j with i | i | t
  · rw [pcOMProj_mulVec_inl]
    rcases b' with b' | b' <;> simp [kOmegaEmb, Pi.single_apply, eq_comm]
  · rw [pcOMProj_mulVec_inr]
    rcases b' with b' | b' <;> simp [kOmegaEmb, Pi.single_apply, eq_comm]
  · fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pcOMProj_mulVec_u]
      rcases b' with b' | b' <;>
        simp [kOmegaEmb]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pcOMProj_mulVec_w]
      rcases b' with b' | b' <;> simp [kOmegaEmb]

omit [CharP K 2] in
theorem pcOMMat_mulVec_single_sig (b' : Fin r ⊕ Fin r) :
    pcOMMat K k *ᵥ Pi.single (kOmMEmb r b') 1 =
      Pi.single (kOmegaEmb (r + 1) (Sum.map k.succAbove k.succAbove b')) 1 := by
  rw [Matrix.mulVec_single_one]
  funext a
  rcases b' with b' | b' <;> rfl

omit [CharP K 2] in
theorem pcOMMat_mulVec_emb_sig (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K)
    (a' : Fin r ⊕ Fin r) :
    (pcOMMat K k *ᵥ y) (kOmegaEmb (r + 1) (Sum.map k.succAbove k.succAbove a')) =
      y (kOmMEmb r a') := by
  rcases a' with a' | a'
  · exact pcOMMat_mulVec_sig_inl k y a'
  · exact pcOMMat_mulVec_sig_inr k y a'

end Frame

section Ext

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

@[expose] noncomputable def pcOMExt :
    StatedOmega (StatedQuadMinus (r + 1) K 1 1) →* StatedOmega (StatedQuadPlus (r + 2) K) :=
  pcExtOmega (pcOMMat K k) (pcOMProj K k) (pcOMProj_mul_pcOMMat k) (pcOM_quad k)

theorem coe_pcOMExt (g : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
    (((pcOMExt k g : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) =
      pcExtMat (pcOMMat K k) (pcOMProj K k) ((g : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        K) : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) := rfl

theorem pcOMExt_injective : Function.Injective (pcOMExt (K := K) k) :=
  pcExtOmega_injective _ _

omit [CharP K 2] in
theorem pcOM_cases (b : Fin (r + 1) ⊕ Fin (r + 1)) :
    (∃ b' : Fin r ⊕ Fin r, b = Sum.map k.succAbove k.succAbove b') ∨ b = .inl k ∨ b = .inr k := by
  rcases b with b | b
  · rcases Fin.eq_self_or_eq_succAbove k b with h | ⟨j, h⟩
    · exact Or.inr (Or.inl (h ▸ rfl))
    · exact Or.inl ⟨.inl j, h ▸ rfl⟩
  · rcases Fin.eq_self_or_eq_succAbove k b with h | ⟨j, h⟩
    · exact Or.inr (Or.inr (h ▸ rfl))
    · exact Or.inl ⟨.inr j, h ▸ rfl⟩

omit [CharP K 2] in
theorem pcOM_not_mem_range {b : Fin (r + 1) ⊕ Fin (r + 1)} (hb : b = .inl k ∨ b = .inr k) :
    b ∉ Set.range (Sum.map k.succAbove k.succAbove) := by
  rintro ⟨z, hz⟩
  rcases hb with rfl | rfl <;> rcases z with z | z <;> simp at hz

end Ext

section Compat

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pcOMExt_q2OmMIota (hK : Nat.card K = 2) (hr : 3 ≤ r) (x : StatedSp r K) :
    pcOMExt k (q2OmMIota hr (q2Omega_irreducible_one_one hK) hK x) =
      q2OmIota (r := r + 1) (by omega) hK (by omega) (complSpEquiv k x) := by
  have hirr := q2Omega_irreducible_one_one hK
  set g := q2OmMIota hr hirr hK x with hgdef
  have hg : g ∈ fixedSubgroup (kOmMBetaC K r 1 1) := by
    rw [← range_q2OmMIota hr hirr hK]
    exact ⟨x, rfl⟩
  have hgS := coe_mem_kOmMStab K hr hirr hg
  have hgv := hgS.2
  obtain ⟨y, hy1, hy2⟩ := kOmMFixRes_q2OmMIota hr hirr hK x
  set G := ((g : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) :
    Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) with hGdef
  have hblock : ∀ a' b' : Fin r ⊕ Fin r, G (kOmMEmb r a') (kOmMEmb r b') = mat r K x a' b' := by
    intro a' b'
    rw [← hy2, mat_apply, coe_kOmMFixRes, hy1]
    rfl
  set A := pcOMExt k g with hAdef
  have hAv : ((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ kOmegaVec K (r + 1) = kOmegaVec K (r + 1) := by
    rw [hAdef, coe_pcOMExt, ← pcOMMat_mulVec_vec k,
      pcExtMat_mulVec_fix (pcOMProj_mul_pcOMMat k) hgv]
  have hA : A ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) :=
    (mem_fixedSubgroup_kOmegaBetaC_iff K (by omega) A).2 hAv
  have hres : kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨A, hA⟩ = complSpEquiv k x := by
    apply mat_injective
    rw [mat_apply, coe_kOmegaFixRes, mat_apply, coe_complSpEquiv_apply, ← mat_apply,
      mat_spEmbed]
    ext a b
    rw [Matrix.submatrix_apply]
    change pcExtMat (pcOMMat K k) (pcOMProj K k) G (kOmegaEmb (r + 1) a) (kOmegaEmb (r + 1) b) = _
    have hcol : pcExtMat (pcOMMat K k) (pcOMProj K k) G (kOmegaEmb (r + 1) a)
        (kOmegaEmb (r + 1) b) = (pcExtMat (pcOMMat K k) (pcOMProj K k) G *ᵥ
          Pi.single (kOmegaEmb (r + 1) b) 1) (kOmegaEmb (r + 1) a) := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol, pcExtMat_mulVec]
    rcases pcOM_cases k b with ⟨b', rfl⟩ | hb
    · rw [pcOMProj_mulVec_single_sig, Matrix.mulVec_sub, pcOMMat_mulVec_single_sig, Pi.add_apply,
        Pi.sub_apply, add_sub_cancel]
      rcases pcOM_cases k a with ⟨a', rfl⟩ | ha
      · rw [pcOMMat_mulVec_emb_sig, Matrix.mulVec_single_one, Matrix.col_apply, hblock,
          spEmbedMat_apply_image Fin.succAbove_right_injective]
      · rw [spEmbedMat_apply_of_not_mem _ (fun h => pcOM_not_mem_range k ha h.1)]
        have hne : a ≠ Sum.map k.succAbove k.succAbove b' := fun h =>
          pcOM_not_mem_range k ha ⟨b', h.symm⟩
        rw [Matrix.one_apply_ne hne]
        rcases ha with rfl | rfl
        · change (pcOMMat K k *ᵥ (G *ᵥ Pi.single (kOmMEmb r b') 1)) (.inl k.castSucc) = 0
          rw [pcOMMat_mulVec_k_inl, Matrix.mulVec_single_one, Matrix.col_apply]
          exact kOmMStab_col one_ne_zero hgS b'
        · change (pcOMMat K k *ᵥ (G *ᵥ Pi.single (kOmMEmb r b') 1)) (.inr k.castSucc) = 0
          rw [pcOMMat_mulVec_k_inr, Matrix.mulVec_single_one, Matrix.col_apply]
          exact kOmMStab_col one_ne_zero hgS b'
    · have hRb : pcOMProj K k *ᵥ Pi.single (kOmegaEmb (r + 1) b) 1 = kOmMVec K r := by
        apply pcOMProj_mulVec_single_k
        rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [hRb, hgv, sub_self, Matrix.mulVec_zero, add_zero,
        spEmbedMat_apply_of_not_mem _ (fun h => pcOM_not_mem_range k hb h.2)]
      simp only [Pi.single_apply, Matrix.one_apply, (kOmegaEmb_injective (r := r + 1)).eq_iff]
  have hι : q2OmIota (r := r + 1) (by omega) hK (by omega)
      (kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨A, hA⟩) = A := by
    have h := (MulEquiv.ofBijective (kOmegaFixRes K (by omega : 2 ≤ r + 1))
      (kOmegaFixRes_bijective_two K (by omega) hK (by omega))).symm_apply_apply ⟨A, hA⟩
    exact congrArg Subtype.val h
  rw [← hres, hι]

end Compat

end CFSG.SeitzReduction.SymplecticPilot
