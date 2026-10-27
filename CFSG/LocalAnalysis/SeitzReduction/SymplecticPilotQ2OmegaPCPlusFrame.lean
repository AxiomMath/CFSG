module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCMinusFrame

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem mat_spEmbed)

section Frame

variable (K : Type) [Field K] {r : ℕ}

@[expose] def pcOPZ (k : Fin (r + 1)) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl k) 1 + Pi.single (.inr (.inl k)) 1 + Pi.single (.inr (.inr 1)) 1

@[expose] def pcOPCol (k : Fin (r + 1)) :
    Fin (r + 1) ⊕ Fin (r + 1) → Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K
  | .inl j => Fin.lastCases (motive := fun _ => _ → K) (pcOPZ K k)
      (fun i => Pi.single (.inl (k.succAbove i)) 1) j
  | .inr j => Fin.lastCases (motive := fun _ => _ → K) (kOmMVec K (r + 1) + pcOPZ K k)
      (fun i => Pi.single (.inr (.inl (k.succAbove i))) 1) j

@[expose] def pcOPRow (k : Fin (r + 1)) :
    Fin (r + 1) ⊕ Fin (r + 1) → Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K
  | .inl j => Fin.lastCases (motive := fun _ => _ → K)
      (Pi.single (.inr (.inr 1)) 1 + Pi.single (.inr (.inr 0)) 1 + Pi.single (.inl k) 1 +
        Pi.single (.inr (.inl k)) 1) (fun i => Pi.single (.inl (k.succAbove i)) 1) j
  | .inr j => Fin.lastCases (motive := fun _ => _ → K)
      (Pi.single (.inr (.inr 0)) 1 + Pi.single (.inl k) 1 + Pi.single (.inr (.inl k)) 1)
      (fun i => Pi.single (.inr (.inl (k.succAbove i))) 1) j

@[expose] def pcOPMat (k : Fin (r + 1)) :
    Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) (Fin (r + 1) ⊕ Fin (r + 1)) K :=
  Matrix.of fun a j => pcOPCol K k j a

@[expose] def pcOPProj (k : Fin (r + 1)) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K :=
  Matrix.of fun j a => pcOPRow K k j a

variable {K} (k : Fin (r + 1))

theorem pcOPProj_mulVec_inl (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (i : Fin r) : (pcOPProj K k *ᵥ x) (.inl i.castSucc) = x (.inl (k.succAbove i)) := by
  simp [pcOPProj, Matrix.mulVec, pcOPRow]

theorem pcOPProj_mulVec_inr (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (i : Fin r) : (pcOPProj K k *ᵥ x) (.inr i.castSucc) = x (.inr (.inl (k.succAbove i))) := by
  simp [pcOPProj, Matrix.mulVec, pcOPRow]

theorem pcOPProj_mulVec_p (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    (pcOPProj K k *ᵥ x) (.inl (Fin.last r)) =
      x (.inr (.inr 1)) + x (.inr (.inr 0)) + x (.inl k) + x (.inr (.inl k)) := by
  simp only [pcOPProj, Matrix.mulVec, Matrix.of_apply, pcOPRow, Fin.lastCases_last]
  change ((Pi.single (Sum.inr (Sum.inr 1)) 1 :
      (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)) +
    (Pi.single (Sum.inr (Sum.inr 0)) 1 : (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)) +
    (Pi.single (Sum.inl k) 1 : (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)) +
    (Pi.single (Sum.inr (Sum.inl k)) 1 :
      (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K))) ⬝ᵥ x = _
  simp [add_dotProduct]

theorem pcOPProj_mulVec_q (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    (pcOPProj K k *ᵥ x) (.inr (Fin.last r)) =
      x (.inr (.inr 0)) + x (.inl k) + x (.inr (.inl k)) := by
  simp only [pcOPProj, Matrix.mulVec, Matrix.of_apply, pcOPRow, Fin.lastCases_last]
  change ((Pi.single (Sum.inr (Sum.inr 0)) 1 :
      (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)) +
    (Pi.single (Sum.inl k) 1 : (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)) +
    (Pi.single (Sum.inr (Sum.inl k)) 1 :
      (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K))) ⬝ᵥ x = _
  simp [add_dotProduct]

theorem pcOPMat_mulVec (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    pcOPMat K k *ᵥ y = ∑ i : Fin r,
      (y (.inl i.castSucc) • Pi.single (.inl (k.succAbove i)) 1 +
        y (.inr i.castSucc) • Pi.single (.inr (.inl (k.succAbove i))) 1) +
      y (.inl (Fin.last r)) • pcOPZ K k +
        y (.inr (Fin.last r)) • (kOmMVec K (r + 1) + pcOPZ K k) := by
  funext a
  simp only [pcOPMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_sum_type,
    Fin.sum_univ_castSucc, pcOPCol, Fin.lastCases_last, Fin.lastCases_castSucc,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  have h1 : ∀ i : Fin r, (Pi.single (Sum.inl (k.succAbove i)) (1 : K) :
      Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) a * y (Sum.inl i.castSucc) =
        y (Sum.inl i.castSucc) * (Pi.single (Sum.inl (k.succAbove i)) (1 : K) :
          Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) a := fun i => mul_comm _ _
  have h2 : ∀ i : Fin r, (Pi.single (Sum.inr (Sum.inl (k.succAbove i))) (1 : K) :
      Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) a * y (Sum.inr i.castSucc) =
        y (Sum.inr i.castSucc) * (Pi.single (Sum.inr (Sum.inl (k.succAbove i))) (1 : K) :
          Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) a := fun i => mul_comm _ _
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i]
  ring

theorem pcOPMat_mulVec_sig_inl (y : Fin (r + 1) ⊕ Fin (r + 1) → K) (i : Fin r) :
    (pcOPMat K k *ᵥ y) (.inl (k.succAbove i)) = y (.inl i.castSucc) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, Pi.single_apply, kOmMVec, pcOPZ, Fin.succAbove_ne]

theorem pcOPMat_mulVec_sig_inr (y : Fin (r + 1) ⊕ Fin (r + 1) → K) (i : Fin r) :
    (pcOPMat K k *ᵥ y) (.inr (.inl (k.succAbove i))) = y (.inr i.castSucc) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, Pi.single_apply, kOmMVec, pcOPZ, Fin.succAbove_ne]

theorem pcOPMat_mulVec_k_inl (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    (pcOPMat K k *ᵥ y) (.inl k) = y (.inl (Fin.last r)) + y (.inr (Fin.last r)) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, kOmMVec, pcOPZ]

theorem pcOPMat_mulVec_k_inr (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    (pcOPMat K k *ᵥ y) (.inr (.inl k)) = y (.inl (Fin.last r)) + y (.inr (Fin.last r)) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, kOmMVec, pcOPZ]

theorem pcOPMat_mulVec_u (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    (pcOPMat K k *ᵥ y) (.inr (.inr 0)) = y (.inr (Fin.last r)) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, kOmMVec, pcOPZ]

theorem pcOPMat_mulVec_w (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    (pcOPMat K k *ᵥ y) (.inr (.inr 1)) = y (.inl (Fin.last r)) + y (.inr (Fin.last r)) := by
  rw [pcOPMat_mulVec]
  simp [Finset.sum_apply, kOmMVec, pcOPZ]

variable [CharP K 2]

theorem pcOPProj_mul_pcOPMat : pcOPProj K k * pcOPMat K k = 1 := by
  ext j j'
  have e : (pcOPProj K k * pcOPMat K k) j j' =
      (pcOPProj K k *ᵥ (pcOPMat K k *ᵥ Pi.single j' 1)) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  rw [e]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ep : ∀ p q : K, p + q + q + (p + q) + (p + q) = p := fun p q => by
    linear_combination (p + 2 * q) * h2
  have eq : ∀ p q : K, q + (p + q) + (p + q) = q := fun p q => by
    linear_combination (p + q) * h2
  rcases j with j | j
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_p, pcOPMat_mulVec_w, pcOPMat_mulVec_u, pcOPMat_mulVec_k_inl,
        pcOPMat_mulVec_k_inr, ep]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    | cast i =>
      rw [pcOPProj_mulVec_inl, pcOPMat_mulVec_sig_inl]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_q, pcOPMat_mulVec_u, pcOPMat_mulVec_k_inl, pcOPMat_mulVec_k_inr, eq]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    | cast i =>
      rw [pcOPProj_mulVec_inr, pcOPMat_mulVec_sig_inr]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]

omit [CharP K 2] in
theorem pcOP_quadMinus_split (v : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus (r + 1 + 1) K 1 1 v = ∑ i : Fin r,
      v (.inl (k.succAbove i)) * v (.inr (.inl (k.succAbove i))) + v (.inl k) * v (.inr (.inl k)) +
        v (.inr (.inr 0)) ^ 2 + 1 * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
          1 * v (.inr (.inr 1)) ^ 2 := by
  rw [StatedQuadMinus]
  change (∑ a : Fin (r + 1), v (.inl a) * v (.inr (.inl a))) + _ + _ + _ = _
  rw [Fin.sum_univ_succAbove _ k]
  ring

omit [CharP K 2] in
theorem pcOP_quadPlus_split (w : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    StatedQuadPlus (r + 1) K w = ∑ i : Fin r, w (.inl i.castSucc) * w (.inr i.castSucc) +
      w (.inl (Fin.last r)) * w (.inr (Fin.last r)) := by
  rw [StatedQuadPlus, Fin.sum_univ_castSucc]

theorem pcOP_quad (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    StatedQuadMinus (r + 1 + 1) K 1 1 (x + pcOPMat K k *ᵥ y) -
        StatedQuadMinus (r + 1 + 1) K 1 1 x =
      StatedQuadPlus (r + 1) K (pcOPProj K k *ᵥ x + y) -
        StatedQuadPlus (r + 1) K (pcOPProj K k *ᵥ x) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pcOP_quadMinus_split k, pcOP_quadMinus_split k, pcOP_quadPlus_split, pcOP_quadPlus_split]
  simp only [Pi.add_apply, pcOPMat_mulVec_sig_inl, pcOPMat_mulVec_sig_inr, pcOPMat_mulVec_k_inl,
    pcOPMat_mulVec_k_inr, pcOPMat_mulVec_u, pcOPMat_mulVec_w, pcOPProj_mulVec_inl,
    pcOPProj_mulVec_inr, pcOPProj_mulVec_p, pcOPProj_mulVec_q]
  linear_combination ((y (.inl (Fin.last r)) + y (.inr (Fin.last r))) ^ 2 +
    y (.inr (Fin.last r)) ^ 2 + x (.inr (.inr 0)) * y (.inr (Fin.last r)) +
      x (.inr (.inr 1)) * (y (.inl (Fin.last r)) + y (.inr (Fin.last r)))) * h2

theorem pcOPMat_mulVec_vec : pcOPMat K k *ᵥ kOmegaVec K r = kOmMVec K (r + 1) := by
  have h2 : ∀ c : K, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  funext a
  rcases a with a | a | t
  · rcases Fin.eq_self_or_eq_succAbove k (a : Fin (r + 1)) with h | ⟨i, h⟩
    · rw [show a = k from h, pcOPMat_mulVec_k_inl]
      simp [kOmegaVec, kOmMVec, h2]
    · rw [show a = k.succAbove i from h, pcOPMat_mulVec_sig_inl]
      simp [kOmegaVec, kOmMVec, Fin.castSucc_ne_last]
  · rcases Fin.eq_self_or_eq_succAbove k (a : Fin (r + 1)) with h | ⟨i, h⟩
    · rw [show a = k from h, pcOPMat_mulVec_k_inr]
      simp [kOmegaVec, kOmMVec, h2]
    · rw [show a = k.succAbove i from h, pcOPMat_mulVec_sig_inr]
      simp [kOmegaVec, kOmMVec, Fin.castSucc_ne_last]
  · fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pcOPMat_mulVec_u]
      simp [kOmegaVec, kOmMVec]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pcOPMat_mulVec_w]
      simp [kOmegaVec, kOmMVec, h2]

omit [CharP K 2] in
theorem pcOPProj_mulVec_single_k (b : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
    (hb : b = .inl k ∨ b = .inr (.inl k)) :
    pcOPProj K k *ᵥ Pi.single b 1 = kOmegaVec K r := by
  funext j
  rcases j with j | j
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_p]
      rcases hb with rfl | rfl <;> simp [kOmegaVec]
    | cast i =>
      rw [pcOPProj_mulVec_inl]
      rcases hb with rfl | rfl <;> simp [kOmegaVec, Fin.succAbove_ne,
        Fin.castSucc_ne_last]
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_q]
      rcases hb with rfl | rfl <;> simp [kOmegaVec]
    | cast i =>
      rw [pcOPProj_mulVec_inr]
      rcases hb with rfl | rfl <;> simp [kOmegaVec, Fin.succAbove_ne,
        Fin.castSucc_ne_last]

omit [CharP K 2] in
theorem pcOPProj_mulVec_single_sig (b' : Fin r ⊕ Fin r) :
    pcOPProj K k *ᵥ Pi.single (kOmMEmb (r + 1) (Sum.map k.succAbove k.succAbove b')) 1 =
      Pi.single (kOmegaEmb r b') 1 := by
  funext j
  rcases j with j | j
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_p]
      rcases b' with b' | b' <;> simp [kOmegaEmb, Fin.castSucc_ne_last]
    | cast i =>
      rw [pcOPProj_mulVec_inl]
      rcases b' with b' | b' <;> simp [kOmegaEmb, Pi.single_apply]
  · induction j using Fin.lastCases with
    | last =>
      rw [pcOPProj_mulVec_q]
      rcases b' with b' | b' <;> simp [kOmegaEmb, Fin.castSucc_ne_last]
    | cast i =>
      rw [pcOPProj_mulVec_inr]
      rcases b' with b' | b' <;> simp [kOmegaEmb, Pi.single_apply, eq_comm]

omit [CharP K 2] in
theorem pcOPMat_mulVec_single_sig (b' : Fin r ⊕ Fin r) :
    pcOPMat K k *ᵥ Pi.single (kOmegaEmb r b') 1 =
      Pi.single (kOmMEmb (r + 1) (Sum.map k.succAbove k.succAbove b')) 1 := by
  rw [Matrix.mulVec_single_one]
  funext a
  rcases b' with b' | b' <;> simp [pcOPMat, pcOPCol, kOmegaEmb, Matrix.col_apply]

omit [CharP K 2] in
theorem pcOPMat_mulVec_emb_sig (y : Fin (r + 1) ⊕ Fin (r + 1) → K) (a' : Fin r ⊕ Fin r) :
    (pcOPMat K k *ᵥ y) (kOmMEmb (r + 1) (Sum.map k.succAbove k.succAbove a')) =
      y (kOmegaEmb r a') := by
  rcases a' with a' | a'
  · exact pcOPMat_mulVec_sig_inl k y a'
  · exact pcOPMat_mulVec_sig_inr k y a'

end Frame

section Ext

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

@[expose] noncomputable def pcOPExt :
    StatedOmega (StatedQuadPlus (r + 1) K) →* StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) :=
  pcExtOmega (pcOPMat K k) (pcOPProj K k) (pcOPProj_mul_pcOPMat k) (pcOP_quad k)

theorem pcOPExt_injective : Function.Injective (pcOPExt (K := K) k) :=
  pcExtOmega_injective _ _

end Ext

section Compat

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pcOPExt_q2OmIota (hK : Nat.card K = 2) (hr : 3 ≤ r) (x : StatedSp r K) :
    pcOPExt k (q2OmIota (by omega) hK hr x) =
      q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (complSpEquiv k x) := by
  have hirr := q2Omega_irreducible_one_one hK
  have h2 : ∀ c : K, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  set g := q2OmIota (by omega : 2 ≤ r) hK hr x with hgdef
  have hg : g ∈ fixedSubgroup (kOmegaBetaC K r) := by
    rw [← range_q2OmIota (by omega : 2 ≤ r) hK hr]
    exact ⟨x, rfl⟩
  have hgS := coe_mem_kOmegaStab K (by omega) hg
  have hgv := hgS.2
  obtain ⟨y, hy1, hy2⟩ := kOmegaFixRes_q2OmIota (by omega : 2 ≤ r) hK hr x
  set G := ((g : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) with hGdef
  have hblock : ∀ a' b' : Fin r ⊕ Fin r, G (kOmegaEmb r a') (kOmegaEmb r b') = mat r K x a' b' := by
    intro a' b'
    rw [← hy2, mat_apply, coe_kOmegaFixRes, hy1]
    rfl
  set A := pcOPExt k g with hAdef
  have hAv : ((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K (r + 1) =
          kOmMVec K (r + 1) := by
    change pcExtMat (pcOPMat K k) (pcOPProj K k) G *ᵥ kOmMVec K (r + 1) = _
    rw [← pcOPMat_mulVec_vec k, pcExtMat_mulVec_fix (pcOPProj_mul_pcOPMat k) hgv]
  have hA : A ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) :=
    (mem_fixedSubgroup_kOmMBetaC_iff K (by omega) hirr A).2 hAv
  have hres : kOmMFixRes K (by omega : 3 ≤ r + 1) hirr ⟨A, hA⟩ = complSpEquiv k x := by
    apply mat_injective
    rw [mat_apply, coe_kOmMFixRes, mat_apply, coe_complSpEquiv_apply, ← mat_apply,
      mat_spEmbed]
    ext a b
    rw [Matrix.submatrix_apply]
    change pcExtMat (pcOPMat K k) (pcOPProj K k) G (kOmMEmb (r + 1) a) (kOmMEmb (r + 1) b) = _
    have hcol : pcExtMat (pcOPMat K k) (pcOPProj K k) G (kOmMEmb (r + 1) a)
        (kOmMEmb (r + 1) b) = (pcExtMat (pcOPMat K k) (pcOPProj K k) G *ᵥ
          Pi.single (kOmMEmb (r + 1) b) 1) (kOmMEmb (r + 1) a) := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol, pcExtMat_mulVec]
    rcases pcOM_cases k b with ⟨b', rfl⟩ | hb
    · rw [pcOPProj_mulVec_single_sig, Matrix.mulVec_sub, pcOPMat_mulVec_single_sig, Pi.add_apply,
        Pi.sub_apply, add_sub_cancel]
      rcases pcOM_cases k a with ⟨a', rfl⟩ | ha
      · rw [pcOPMat_mulVec_emb_sig, Matrix.mulVec_single_one, Matrix.col_apply, hblock,
          spEmbedMat_apply_image Fin.succAbove_right_injective]
      · rw [spEmbedMat_apply_of_not_mem _ (fun h => pcOM_not_mem_range k ha h.1)]
        have hne : a ≠ Sum.map k.succAbove k.succAbove b' := fun h =>
          pcOM_not_mem_range k ha ⟨b', h.symm⟩
        rw [Matrix.one_apply_ne hne]
        have hc := kOmegaStab_col hgS b'
        rcases ha with rfl | rfl
        · change (pcOPMat K k *ᵥ (G *ᵥ Pi.single (kOmegaEmb r b') 1)) (.inl k) = 0
          rw [pcOPMat_mulVec_k_inl, Matrix.mulVec_single_one, Matrix.col_apply,
            Matrix.col_apply, hGdef, hc, h2]
        · change (pcOPMat K k *ᵥ (G *ᵥ Pi.single (kOmegaEmb r b') 1)) (.inr (.inl k)) = 0
          rw [pcOPMat_mulVec_k_inr, Matrix.mulVec_single_one, Matrix.col_apply,
            Matrix.col_apply, hGdef, hc, h2]
    · have hRb : pcOPProj K k *ᵥ Pi.single (kOmMEmb (r + 1) b) 1 = kOmegaVec K r := by
        apply pcOPProj_mulVec_single_k
        rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [hRb, hgv, sub_self, Matrix.mulVec_zero, add_zero,
        spEmbedMat_apply_of_not_mem _ (fun h => pcOM_not_mem_range k hb h.2)]
      simp only [Pi.single_apply, Matrix.one_apply, (kOmMEmb_injective (r := r + 1)).eq_iff]
  have hι : q2OmMIota (r := r + 1) (by omega) hirr hK
      (kOmMFixRes K (by omega : 3 ≤ r + 1) hirr ⟨A, hA⟩) = A := by
    have h := (MulEquiv.ofBijective (kOmMFixRes K (by omega : 3 ≤ r + 1) hirr)
      (kOmMFixRes_bijective_two K (by omega) hirr hK)).symm_apply_apply ⟨A, hA⟩
    exact congrArg Subtype.val h
  rw [← hres, hι]

end Compat

end CFSG.SeitzReduction.SymplecticPilot
