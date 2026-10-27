module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEPlusFrame
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinusPlace

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Supp

variable {r : ℕ}

theorem peP_mem_peSuppM_iff {J : Finset (Fin (r + 1 + 1 - 1))} {x : Fin (r + 1 + 1 - 1)} :
    x ∈ peSuppM J ↔ ∃ j ∈ J, (j.val + 1 < r + 1 ∧ (x.val = j.val ∨ x.val = j.val + 1)) ∨
      (¬ j.val + 1 < r + 1 ∧ x.val = j.val) := by
  simp only [peSuppM, Finset.mem_biUnion]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  by_cases h : j.val + 1 < r + 1 + 1 - 1
  · rw [dite_eq_left h]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    constructor
    · intro h'
      exact Or.inl ⟨by omega, h'⟩
    · rintro (⟨-, h'⟩ | ⟨h1, -⟩)
      · exact h'
      · omega
  · rw [dite_eq_right h]
    simp only [Finset.mem_singleton, Fin.ext_iff]
    constructor
    · intro h'
      exact Or.inr ⟨by omega, h'⟩
    · rintro (⟨h1, -⟩ | ⟨-, h'⟩)
      · omega
      · exact h'

theorem peP_card_peSuppM_le (J : Finset (Fin (r + 1 + 1 - 1))) :
    (peSuppM J).card ≤ 2 * J.card := by
  refine (Finset.card_biUnion_le).trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact Finset.card_le_two
  · simp

end Supp

section Off

variable {K : Type} [Field K] {r : ℕ}

theorem peOffM_pdPA {J : Finset (Fin (r + 1 + 1 - 1))} {k : Fin (r + 1)}
    (hk : (k : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) (hJ : ¬ PEMShort J) :
    PEOffM J (pdPA K k) := by
  refine ⟨fun a ha => ?_, fun h => absurd h hJ⟩
  have h1 : a ≠ k := fun h => hk (h ▸ ha)
  simp [pdPA, kOmMVec, h1]

theorem peOffM_pdPB {J : Finset (Fin (r + 1 + 1 - 1))} {k : Fin (r + 1)}
    (hk : (k : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) (hJ : ¬ PEMShort J) :
    PEOffM J (pdPB K k) := by
  refine ⟨fun a ha => ?_, fun h => absurd h hJ⟩
  have h1 : a ≠ k := fun h => hk (h ▸ ha)
  simp [pdPB, kOmMVec, h1]

theorem peOffM_inl_add_pdPP {J : Finset (Fin (r + 1 + 1 - 1))} {a b : Fin (r + 1)}
    (ha : (a : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) (hb : (b : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) :
    PEOffM J (Pi.single (Sum.inl a : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
      pdPP (K := K) b) := by
  refine ⟨fun x hx => ?_, fun _ => ?_⟩
  · have h1 : x ≠ a := fun h => ha (h ▸ hx)
    have h2 : x ≠ b := fun h => hb (h ▸ hx)
    simp [pdPP, h1, h2]
  · simp [pdPP]

theorem peOffM_inr_add_pdPP {J : Finset (Fin (r + 1 + 1 - 1))} {a b : Fin (r + 1)}
    (ha : (a : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) (hb : (b : Fin (r + 1 + 1 - 1)) ∉ peSuppM J) :
    PEOffM J (Pi.single (Sum.inr (Sum.inl a) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
      1 + pdPP (K := K) b) := by
  refine ⟨fun x hx => ?_, fun _ => ?_⟩
  · have h1 : x ≠ a := fun h => ha (h ▸ hx)
    have h2 : x ≠ b := fun h => hb (h ▸ hx)
    simp [pdPP, h1, h2]
  · simp [pdPP]

variable [CharP K 2]

theorem pe_polar_inl_add_pdPP_pePU {a b i : Fin (r + 1)} (hia : i ≠ a) :
    polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inl a : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b)
        (pePU K i) = 0 := by
  rw [pe_polar_pePU]
  simp [pdPP, Pi.single_apply, hia, CharTwo.add_self_eq_zero]

theorem pe_polar_inr_add_pdPP_pePU {a b i : Fin (r + 1)} (hia : i ≠ a) :
    polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inr (Sum.inl a) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
        pdPP b) (pePU K i) = 0 := by
  rw [pe_polar_pePU]
  simp [pdPP, Pi.single_apply, hia, CharTwo.add_self_eq_zero]

end Off

section Transporters

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr : 4 ≤ r)

@[expose] noncomputable def pePT10 : StatedSp (r + 1) K :=
  pePTr hK (by omega : 2 ≤ r) (i := ⟨1, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨2, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

@[expose] noncomputable def pePT23 : StatedSp (r + 1) K :=
  pePTr hK (by omega : 2 ≤ r) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (m := ⟨0, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

@[expose] noncomputable def pePT30 : StatedSp (r + 1) K :=
  pePTr hK (by omega : 2 ≤ r) (i := ⟨3, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨1, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

theorem q2OmMIota_pePT10 :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) =
      pePEich hK (by omega) (i := ⟨1, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨2, by omega⟩)
        (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
        (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmMIota_pePTr hK (by omega) _ _ _

theorem q2OmMIota_pePT23 :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT23 hK hr) =
      pePEich hK (by omega) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (m := ⟨0, by omega⟩)
        (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
        (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmMIota_pePTr hK (by omega) _ _ _

theorem q2OmMIota_pePT30 :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT30 hK hr) =
      pePEich hK (by omega) (i := ⟨3, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨1, by omega⟩)
        (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
        (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmMIota_pePTr hK (by omega) _ _ _

theorem q2OmMIota_pePT10_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) ∈
      (pcOPExt (K := K) k).range := by
  rw [q2OmMIota_pePT10]
  exact pePEich_mem_range _ _ _ _ _ (Fin.ne_of_val_ne (by simpa using h1))
    (Fin.ne_of_val_ne (by simpa using h0))

theorem q2OmMIota_pePT23_mem_range {k : Fin (r + 1)} (h2 : k.val ≠ 2) (h3 : k.val ≠ 3) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT23 hK hr) ∈
      (pcOPExt (K := K) k).range := by
  rw [q2OmMIota_pePT23]
  exact pePEich_mem_range _ _ _ _ _ (Fin.ne_of_val_ne (by simpa using h2))
    (Fin.ne_of_val_ne (by simpa using h3))

theorem q2OmMIota_pePT30_mem_range {k : Fin (r + 1)} (h3 : k.val ≠ 3) (h0 : k.val ≠ 0) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT30 hK hr) ∈
      (pcOPExt (K := K) k).range := by
  rw [q2OmMIota_pePT30]
  exact pePEich_mem_range _ _ _ _ _ (Fin.ne_of_val_ne (by simpa using h3))
    (Fin.ne_of_val_ne (by simpa using h0))

theorem q2OmMIota_pePT10_mulVec_a :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K ⟨1, by omega⟩ =
      Pi.single (Sum.inl ((⟨1, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨0, by omega⟩ := by
  rw [q2OmMIota_pePT10, pePEich_mulVec_a]

theorem q2OmMIota_pePT10_mulVec_b :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K ⟨1, by omega⟩ =
      Pi.single (Sum.inr (Sum.inl ((⟨1, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨0, by omega⟩ := by
  rw [q2OmMIota_pePT10, pePEich_mulVec_b]

theorem q2OmMIota_pePT23_mulVec_a :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT23 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K ⟨2, by omega⟩ =
      Pi.single (Sum.inl ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨3, by omega⟩ := by
  rw [q2OmMIota_pePT23, pePEich_mulVec_a]

theorem q2OmMIota_pePT23_mulVec_b :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT23 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K ⟨2, by omega⟩ =
      Pi.single (Sum.inr (Sum.inl ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨3, by omega⟩ := by
  rw [q2OmMIota_pePT23, pePEich_mulVec_b]

theorem q2OmMIota_pePT30_mulVec_a :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT30 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K ⟨3, by omega⟩ =
      Pi.single (Sum.inl ((⟨3, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨0, by omega⟩ := by
  rw [q2OmMIota_pePT30, pePEich_mulVec_a]

theorem q2OmMIota_pePT30_mulVec_b :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT30 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K ⟨3, by omega⟩ =
      Pi.single (Sum.inr (Sum.inl ((⟨3, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨0, by omega⟩ := by
  rw [q2OmMIota_pePT30, pePEich_mulVec_b]

theorem q2OmMIota_pePT10_mulVec_inl (a b : Fin (r + 1)) (ha0 : a.val ≠ 0) (ha1 : a.val ≠ 1) :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl (a : Fin (r + 1 + 1 - 1)) :
          Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b) =
      Pi.single (Sum.inl (a : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b := by
  rw [q2OmMIota_pePT10]
  exact pePEich_mulVec_of_polar _ _ _ _ _
    (pe_polar_inl_add_pdPP_pePU (Fin.ne_of_val_ne (by simp; omega)))
    (pe_polar_inl_add_pdPP_pePU (Fin.ne_of_val_ne (by simp; omega)))

theorem q2OmMIota_pePT10_mulVec_inr (a b : Fin (r + 1)) (ha0 : a.val ≠ 0) (ha1 : a.val ≠ 1) :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePT10 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr (Sum.inl (a : Fin (r + 1 + 1 - 1))) :
          Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b) =
      Pi.single (Sum.inr (Sum.inl (a : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b := by
  rw [q2OmMIota_pePT10]
  exact pePEich_mulVec_of_polar _ _ _ _ _
    (pe_polar_inr_add_pdPP_pePU (Fin.ne_of_val_ne (by simp; omega)))
    (pe_polar_inr_add_pdPP_pePU (Fin.ne_of_val_ne (by simp; omega)))

end Transporters

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem peP_conj_mem_range_of_peOff (hK : Nat.card K = 2) (hr2 : 2 ≤ r) (hn : 4 ≤ r + 1 + 1)
    {k : Fin (r + 1)} (h : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))
    {J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2}}
    (x : (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    (hA : PEOffM J.1 ((((h : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K k))
    (hB : PEOffM J.1 ((((h : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K k)) :
    h⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x * h ∈ (pcOPExt (K := K) k).range := by
  rw [mem_pcOPExt_range_iff k hK hr2]
  have key : ∀ z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K,
      PEOffM J.1 ((((h : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z) →
      ((((h⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x * h :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z = z := by
    intro z hz
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, peRhoM_mulVec, spinAction_leviM_of_peOff _ x hz,
      Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  exact ⟨key _ hA, key _ hB⟩

end Conj

section Placement

variable {r : ℕ} (hr : 4 ≤ r)

open Classical in
@[expose] noncomputable def pePIdx (J : Finset (Fin (r + 1 + 1 - 1))) : Fin (r + 1) :=
  if PEMShort J then
    (if (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J then ⟨2, by omega⟩
      else if (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J then ⟨3, by omega⟩ else ⟨1, by omega⟩)
  else if ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J then Fin.last r
  else if ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J then ⟨2, by omega⟩
  else if h : ∃ k : Fin (r + 1), (k : Fin (r + 1 + 1 - 1)) ∉ peSuppM J then h.choose else 0

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

open Classical in
@[expose] noncomputable def pePTrJ (J : Finset (Fin (r + 1 + 1 - 1))) : StatedSp (r + 1) K :=
  if PEMShort J then
    (if (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J then pePT10 hK hr * pePT23 hK hr
      else if (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J then pePT10 hK hr * pePT30 hK hr
      else pePT10 hK hr)
  else 1

end Placement

section Cases

variable {r : ℕ} (hr : 4 ≤ r)

theorem peP_bad_supp_zero {J : Finset (Fin (r + 1 + 1 - 1))} (hJ : J.card ≤ 2) (hb : PEMShort J)
    (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) {x : Fin (r + 1 + 1 - 1)}
    (hx : x ∈ peSuppM J) : x.val ≤ 1 ∨ x.val = r := by
  obtain ⟨b, hbJ, hbr⟩ := hb
  have hne : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  obtain ⟨j, hj, h⟩ := peP_mem_peSuppM_iff.1 hx
  have hb' : b.val = r := by have := b.2; omega
  rcases pe_eq_or_eq_of_card_le_two hJ h0 hbJ hne hj with h' | h'
  · rw [h'] at h
    simp only at h
    omega
  · rw [h'] at h
    omega

theorem peP_bad_supp_one {J : Finset (Fin (r + 1 + 1 - 1))} (hJ : J.card ≤ 2) (hb : PEMShort J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) {x : Fin (r + 1 + 1 - 1)}
    (hx : x ∈ peSuppM J) : (1 ≤ x.val ∧ x.val ≤ 2) ∨ x.val = r := by
  obtain ⟨b, hbJ, hbr⟩ := hb
  have hne : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  obtain ⟨j, hj, h⟩ := peP_mem_peSuppM_iff.1 hx
  have hb' : b.val = r := by have := b.2; omega
  rcases pe_eq_or_eq_of_card_le_two hJ h1 hbJ hne hj with h' | h'
  · rw [h'] at h
    simp only at h
    omega
  · rw [h'] at h
    omega

theorem peP_supp_two {J : Finset (Fin (r + 1 + 1 - 1))}
    (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    {x : Fin (r + 1 + 1 - 1)} (hx : x ∈ peSuppM J) : 2 ≤ x.val := by
  obtain ⟨j, hj, h⟩ := peP_mem_peSuppM_iff.1 hx
  have hj0 : j.val ≠ 0 := fun h' => h0 (by rwa [show j = ⟨0, by omega⟩ from Fin.ext h'] at hj)
  have hj1 : j.val ≠ 1 := fun h' => h1 (by rwa [show j = ⟨1, by omega⟩ from Fin.ext h'] at hj)
  omega

include hr in
theorem peP_exists_off {J : Finset (Fin (r + 1 + 1 - 1))} (hJ : J.card ≤ 2) :
    ∃ k : Fin (r + 1), (k : Fin (r + 1 + 1 - 1)) ∉ peSuppM J := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin (r + 1 + 1 - 1))) ⊆ peSuppM J := fun x _ => hc x
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := peP_card_peSuppM_le J
  omega

omit hr in
theorem peP_mem_peSuppM_singleton {a x : Fin (r + 1 + 1 - 1)} (ha : a.val + 1 < r + 1) :
    x ∈ peSuppM {a} ↔ x.val = a.val ∨ x.val = a.val + 1 := by
  rw [peP_mem_peSuppM_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    omega
  · intro h
    exact ⟨a, Finset.mem_singleton_self a, Or.inl ⟨ha, h⟩⟩

end Cases

section UnfoldIdx

variable {r : ℕ} (hr : 4 ≤ r) {J : Finset (Fin (r + 1 + 1 - 1))}

theorem pePIdx_bad_zero (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) :
    pePIdx hr J = ⟨2, by omega⟩ := by
  simp only [pePIdx, hb, h0, ↓reduceIte]

theorem pePIdx_bad_one (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) : pePIdx hr J = ⟨3, by omega⟩ := by
  simp only [pePIdx, hb, h0, h1, ↓reduceIte]

theorem pePIdx_bad_two (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J) : pePIdx hr J = ⟨1, by omega⟩ := by
  simp only [pePIdx, hb, h0, h1, ↓reduceIte]

theorem pePIdx_good_off (hJ : J.card ≤ 2) (hg : ¬ PEMShort J) :
    ((pePIdx hr J : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J := by
  unfold pePIdx
  rw [ite_eq_right hg]
  by_cases h1 : ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J
  · rw [ite_eq_left h1]
    exact h1
  · rw [ite_eq_right h1]
    by_cases h2 : ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J
    · rw [ite_eq_left h2]
      exact h2
    · rw [ite_eq_right h2]
      have h3 := peP_exists_off hr hJ
      rw [dite_eq_left h3]
      exact h3.choose_spec

theorem pePIdx_singleton {a : Fin (r + 1 + 1 - 1)} (ha : a.val + 1 < r + 1) :
    (pePIdx hr {a}).val = r ∨ ((pePIdx hr {a}).val = 2 ∧ a.val + 1 = r) := by
  have hg : ¬ PEMShort ({a} : Finset (Fin (r + 1 + 1 - 1))) := by
    rintro ⟨j, hj, hjr⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    omega
  unfold pePIdx
  rw [ite_eq_right hg]
  by_cases h1 : ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∈ peSuppM {a}
  · rw [ite_eq_right (not_not.2 h1)]
    have h1' := (peP_mem_peSuppM_singleton ha).1 h1
    simp only [Fin.val_last] at h1'
    have h2 : ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM {a} := by
      intro h
      have := (peP_mem_peSuppM_singleton ha).1 h
      simp only at this
      omega
    rw [ite_eq_left h2]
    exact Or.inr ⟨rfl, by omega⟩
  · rw [ite_eq_left h1]
    exact Or.inl rfl

end UnfoldIdx

section Unfold

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2) (hr : 4 ≤ r)
  {J : Finset (Fin (r + 1 + 1 - 1))}

theorem pePTrJ_bad_zero (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) :
    pePTrJ (K := K) hr hK J = pePT10 hK hr * pePT23 hK hr := by
  simp only [pePTrJ, hb, h0, ↓reduceIte]

theorem pePTrJ_bad_one (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J) :
    pePTrJ (K := K) hr hK J = pePT10 hK hr * pePT30 hK hr := by
  simp only [pePTrJ, hb, h0, h1, ↓reduceIte]

theorem pePTrJ_bad_two (hb : PEMShort J) (h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J) : pePTrJ (K := K) hr hK J = pePT10 hK hr := by
  simp only [pePTrJ, hb, h0, h1, ↓reduceIte]

theorem pePTrJ_good (hg : ¬ PEMShort J) : pePTrJ (K := K) hr hK J = 1 := by
  simp only [pePTrJ, hg, ↓reduceIte]

end Unfold

section Verify

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr : 4 ≤ r)

theorem peP_place (hn : 4 ≤ r + 1 + 1) (J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2})
    (x : (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (pePTrJ hr hK J.1))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
      q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (pePTrJ hr hK J.1) ∈
        (pcOPExt (K := K) (pePIdx hr J.1)).range := by
  have hr2 : 2 ≤ r := by omega
  by_cases hb : PEMShort J.1
  · by_cases h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
    · have h2 : ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 := fun h => by
        have := peP_bad_supp_zero hr J.2 hb h0 h
        simp only at this
        omega
      have h3 : ((⟨3, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 := fun h => by
        have := peP_bad_supp_zero hr J.2 hb h0 h
        simp only at this
        omega
      rw [pePIdx_bad_zero hr hb h0, pePTrJ_bad_zero hK hr hb h0]
      refine peP_conj_mem_range_of_peOff hK hr2 hn _ x ?_ ?_
      · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
          q2OmMIota_pePT23_mulVec_a, q2OmMIota_pePT10_mulVec_inl hK hr ⟨2, by omega⟩
            ⟨3, by omega⟩ (by simp) (by simp)]
        exact peOffM_inl_add_pdPP h2 h3
      · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
          q2OmMIota_pePT23_mulVec_b, q2OmMIota_pePT10_mulVec_inr hK hr ⟨2, by omega⟩
            ⟨3, by omega⟩ (by simp) (by simp)]
        exact peOffM_inr_add_pdPP h2 h3
    · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
      · have h3 : ((⟨3, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 :=
          fun h => by
            have := peP_bad_supp_one hr J.2 hb h1 h
            simp only at this
            omega
        have h0' : ((⟨0, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 :=
          fun h => by
            have := peP_bad_supp_one hr J.2 hb h1 h
            simp only at this
            omega
        rw [pePIdx_bad_one hr hb h0 h1, pePTrJ_bad_one hK hr hb h0 h1]
        refine peP_conj_mem_range_of_peOff hK hr2 hn _ x ?_ ?_
        · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
            q2OmMIota_pePT30_mulVec_a, q2OmMIota_pePT10_mulVec_inl hK hr ⟨3, by omega⟩
              ⟨0, by omega⟩ (by simp) (by simp)]
          exact peOffM_inl_add_pdPP h3 h0'
        · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
            q2OmMIota_pePT30_mulVec_b, q2OmMIota_pePT10_mulVec_inr hK hr ⟨3, by omega⟩
              ⟨0, by omega⟩ (by simp) (by simp)]
          exact peOffM_inr_add_pdPP h3 h0'
      · have h1' : ((⟨1, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 :=
          fun h => by
            have := peP_supp_two hr h0 h1 h
            simp only at this
            omega
        have h0' : ((⟨0, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∉ peSuppM J.1 :=
          fun h => by
            have := peP_supp_two hr h0 h1 h
            simp only at this
            omega
        rw [pePIdx_bad_two hr hb h0 h1, pePTrJ_bad_two hK hr hb h0 h1]
        refine peP_conj_mem_range_of_peOff hK hr2 hn _ x ?_ ?_
        · rw [q2OmMIota_pePT10_mulVec_a]
          exact peOffM_inl_add_pdPP h1' h0'
        · rw [q2OmMIota_pePT10_mulVec_b]
          exact peOffM_inr_add_pdPP h1' h0'
  · rw [pePTrJ_good hK hr hb, map_one]
    refine peP_conj_mem_range_of_peOff hK hr2 hn 1 x ?_ ?_
    · rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
      exact peOffM_pdPA (pePIdx_good_off hr J.2 hb) hb
    · rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
      exact peOffM_pdPB (pePIdx_good_off hr J.2 hb) hb

theorem peP_compat (I J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2}) (hIJ : I ≤ J)
    (hI : I.1.Nonempty) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        ((pePTrJ hr hK I.1)⁻¹ * pePTrJ hr hK J.1) ∈
      (pcOPExt (K := K) (pePIdx hr I.1)).range := by
  rcases eq_or_ne I J with rfl | hne
  · rw [inv_mul_cancel, map_one]
    exact one_mem _
  have hIJ' : I.1 ⊆ J.1 := hIJ
  have hlt : I.1.card < J.1.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hIJ', fun h => hne (Subtype.ext h)⟩)
  have hcardI : I.1.card = 1 := by
    have := hI.card_pos
    have := J.2
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcardI
  have haJ : a ∈ J.1 := hIJ' (by rw [ha]; exact Finset.mem_singleton_self a)
  obtain ⟨b, hbJ, hba⟩ : ∃ b ∈ J.1, b ≠ a := by
    by_contra hc
    push Not at hc
    have hsub : J.1 ⊆ {a} := fun z hz => Finset.mem_singleton.2 (hc z hz)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  have hJab : ∀ z ∈ J.1, z = a ∨ z = b := fun z hz =>
    pe_eq_or_eq_of_card_le_two J.2 haJ hbJ hba.symm hz
  rw [ha]
  by_cases hab : ¬ a.val + 1 < r + 1
  · have hbI : PEMShort ({a} : Finset (Fin (r + 1 + 1 - 1))) :=
      ⟨a, Finset.mem_singleton_self a, hab⟩
    have h0I : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ ({a} : Finset (Fin (r + 1 + 1 - 1))) := by
      rw [Finset.mem_singleton]
      intro h
      rw [← h] at hab
      simp at hab
      omega
    have h1I : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ ({a} : Finset (Fin (r + 1 + 1 - 1))) := by
      rw [Finset.mem_singleton]
      intro h
      rw [← h] at hab
      simp at hab
      omega
    rw [pePIdx_bad_two hr hbI h0I h1I, pePTrJ_bad_two hK hr hbI h0I h1I]
    have hbJ' : PEMShort J.1 := ⟨a, haJ, hab⟩
    by_cases h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
    · rw [pePTrJ_bad_zero hK hr hbJ' h0, ← mul_assoc, inv_mul_cancel, one_mul]
      exact q2OmMIota_pePT23_mem_range hK hr (by simp) (by simp)
    · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
      · rw [pePTrJ_bad_one hK hr hbJ' h0 h1, ← mul_assoc, inv_mul_cancel, one_mul]
        exact q2OmMIota_pePT30_mem_range hK hr (by simp) (by simp)
      · rw [pePTrJ_bad_two hK hr hbJ' h0 h1, inv_mul_cancel, map_one]
        exact one_mem _
  · push Not at hab
    have hgI : ¬ PEMShort ({a} : Finset (Fin (r + 1 + 1 - 1))) := by
      rintro ⟨j, hj, hjr⟩
      rw [Finset.mem_singleton] at hj
      subst hj
      omega
    rw [pePTrJ_good hK hr hgI, inv_one, one_mul]
    by_cases hbJ' : PEMShort J.1
    · obtain ⟨c, hcJ, hcr⟩ := hbJ'
      have hcb : c = b := by
        rcases hJab c hcJ with h | h
        · rw [h] at hcr
          omega
        · exact h
      subst hcb
      rcases pePIdx_singleton hr hab with hidx | ⟨hidx, hidx'⟩
      · by_cases h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
        · rw [pePTrJ_bad_zero hK hr ⟨c, hcJ, hcr⟩ h0, map_mul]
          exact mul_mem (q2OmMIota_pePT10_mem_range hK hr (by omega) (by omega))
            (q2OmMIota_pePT23_mem_range hK hr (by omega) (by omega))
        · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∈ J.1
          · rw [pePTrJ_bad_one hK hr ⟨c, hcJ, hcr⟩ h0 h1, map_mul]
            exact mul_mem (q2OmMIota_pePT10_mem_range hK hr (by omega) (by omega))
              (q2OmMIota_pePT30_mem_range hK hr (by omega) (by omega))
          · rw [pePTrJ_bad_two hK hr ⟨c, hcJ, hcr⟩ h0 h1]
            exact q2OmMIota_pePT10_mem_range hK hr (by omega) (by omega)
      · have h0 : (⟨0, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J.1 := by
          intro h
          rcases hJab _ h with h' | h'
          · have := congrArg Fin.val h'
            simp at this
            omega
          · have := congrArg Fin.val h'
            simp at this
            omega
        have h1 : (⟨1, by omega⟩ : Fin (r + 1 + 1 - 1)) ∉ J.1 := by
          intro h
          rcases hJab _ h with h' | h'
          · have := congrArg Fin.val h'
            simp at this
            omega
          · have := congrArg Fin.val h'
            simp at this
            omega
        rw [pePTrJ_bad_two hK hr ⟨c, hcJ, hcr⟩ h0 h1]
        exact q2OmMIota_pePT10_mem_range hK hr (by omega) (by omega)
    · rw [pePTrJ_good hK hr hbJ', map_one]
      exact one_mem _

end Verify

end CFSG.SeitzReduction.SymplecticPilot
