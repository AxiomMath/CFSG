module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinusFrame

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin

section Supp

variable {r : ℕ}

theorem pe_val_rootIdxD (j : Fin (r + 2)) :
    (rootIdxD (r + 2) j).val = if j.val + 1 < r + 2 then j.val else r := by
  unfold rootIdxD
  split_ifs <;> rfl

theorem pe_val_rootIdxD' (j : Fin (r + 2)) :
    (rootIdxD' (r + 2) j).val = if j.val + 1 < r + 2 then j.val + 1 else r + 1 := by
  unfold rootIdxD'
  split_ifs <;> rfl

theorem pe_mem_peSupp_iff {J : Finset (Fin (r + 2))} {x : Fin (r + 2)} :
    x ∈ peSupp J ↔ ∃ j ∈ J, (j.val + 1 < r + 2 ∧ (x.val = j.val ∨ x.val = j.val + 1)) ∨
      (j.val + 1 = r + 2 ∧ (x.val = r ∨ x.val = r + 1)) := by
  rw [mem_peSupp]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  rw [Fin.ext_iff, Fin.ext_iff, pe_val_rootIdxD, pe_val_rootIdxD']
  split_ifs with h <;> omega

theorem pe_card_peSupp_le (J : Finset (Fin (r + 2))) : (peSupp J).card ≤ 2 * J.card := by
  refine (Finset.card_biUnion_le).trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun j _ => Finset.card_le_two

theorem pe_eq_or_eq_of_card_le_two {α : Type*} [DecidableEq α] {J : Finset α} (hJ : J.card ≤ 2)
    {x y : α} (hx : x ∈ J) (hy : y ∈ J) (hxy : x ≠ y) {z : α} (hz : z ∈ J) : z = x ∨ z = y := by
  have hsub : ({x, y} : Finset α) ⊆ J := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hx
    · rw [Finset.mem_singleton.1 hw]
      exact hy
  have hcard : J.card ≤ ({x, y} : Finset α).card := by
    rw [Finset.card_pair hxy]
    exact hJ
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq] at hz
  rcases Finset.mem_insert.1 hz with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.1 h)

end Supp

section Off

variable {K : Type} [Field K] {r : ℕ}

theorem peOff_pdMA {S : Finset (Fin (r + 2))} {k : Fin (r + 1)} (hk : k.castSucc ∉ S)
    (hN : Fin.last (r + 1) ∉ S) : PEOff S (pdMA K k) := by
  intro a ha
  have h1 : a ≠ k.castSucc := fun h => hk (h ▸ ha)
  have h2 : a ≠ Fin.last (r + 1) := fun h => hN (h ▸ ha)
  simp [pdMA, kOmegaVec, h1, h2]

theorem peOff_pdMB {S : Finset (Fin (r + 2))} {k : Fin (r + 1)} (hk : k.castSucc ∉ S)
    (hN : Fin.last (r + 1) ∉ S) : PEOff S (pdMB K k) := by
  intro a ha
  have h1 : a ≠ k.castSucc := fun h => hk (h ▸ ha)
  have h2 : a ≠ Fin.last (r + 1) := fun h => hN (h ▸ ha)
  simp [pdMB, kOmegaVec, h1, h2]

theorem peOff_inl_add_pdMP {S : Finset (Fin (r + 2))} {a b : Fin (r + 1)} (ha : a.castSucc ∉ S)
    (hb : b.castSucc ∉ S) : PEOff S (Pi.single (.inl a.castSucc) 1 + pdMP (K := K) b) := by
  intro x hx
  have h1 : x ≠ a.castSucc := fun h => ha (h ▸ hx)
  have h2 : x ≠ b.castSucc := fun h => hb (h ▸ hx)
  simp [pdMP, h1, h2]

theorem peOff_inr_add_pdMP {S : Finset (Fin (r + 2))} {a b : Fin (r + 1)} (ha : a.castSucc ∉ S)
    (hb : b.castSucc ∉ S) : PEOff S (Pi.single (.inr a.castSucc) 1 + pdMP (K := K) b) := by
  intro x hx
  have h1 : x ≠ a.castSucc := fun h => ha (h ▸ hx)
  have h2 : x ≠ b.castSucc := fun h => hb (h ▸ hx)
  simp [pdMP, h1, h2]

variable [CharP K 2]

theorem pe_polar_inl_add_pdMP_peMU {a b i : Fin (r + 1)} (hia : i ≠ a) :
    polar (quadPlus (r + 2) K) (Pi.single (.inl a.castSucc) 1 + pdMP b) (peMU K i) = 0 := by
  rw [pe_polar_peMU]
  simp [pdMP, Pi.single_apply, hia, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem pe_polar_inr_add_pdMP_peMU {a b i : Fin (r + 1)} (hia : i ≠ a) :
    polar (quadPlus (r + 2) K) (Pi.single (.inr a.castSucc) 1 + pdMP b) (peMU K i) = 0 := by
  rw [pe_polar_peMU]
  simp [pdMP, Pi.single_apply, hia, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

end Off

section Transporters

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr : 4 ≤ r)

omit hK in
@[expose] noncomputable def peT10 : StatedSp (r + 1) K :=
  peMTr (by omega : 3 ≤ r) (i := ⟨1, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨2, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

omit hK in
@[expose] noncomputable def peT23 : StatedSp (r + 1) K :=
  peMTr (by omega : 3 ≤ r) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (m := ⟨0, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

omit hK in
@[expose] noncomputable def peT30 : StatedSp (r + 1) K :=
  peMTr (by omega : 3 ≤ r) (i := ⟨3, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨1, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

theorem q2OmIota_peT10 : q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) =
    peMEich (K := K) (by omega) (i := ⟨1, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨2, by omega⟩)
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmIota_peMTr hK (by omega) _ _ _

theorem q2OmIota_peT23 : q2OmIota (r := r + 1) (by omega) hK (by omega) (peT23 hr) =
    peMEich (K := K) (by omega) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (m := ⟨0, by omega⟩)
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmIota_peMTr hK (by omega) _ _ _

theorem q2OmIota_peT30 : q2OmIota (r := r + 1) (by omega) hK (by omega) (peT30 hr) =
    peMEich (K := K) (by omega) (i := ⟨3, by omega⟩) (j := ⟨0, by omega⟩) (m := ⟨1, by omega⟩)
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmIota_peMTr hK (by omega) _ _ _

theorem q2OmIota_peT10_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) ∈
      (pcOMExt (K := K) k).range := by
  rw [q2OmIota_peT10]
  exact peMEich_mem_range _ _ _ _ hK (by omega) (Fin.ne_of_val_ne (by simpa using h1))
    (Fin.ne_of_val_ne (by simpa using h0))

theorem q2OmIota_peT23_mem_range {k : Fin (r + 1)} (h2 : k.val ≠ 2) (h3 : k.val ≠ 3) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (peT23 hr) ∈
      (pcOMExt (K := K) k).range := by
  rw [q2OmIota_peT23]
  exact peMEich_mem_range _ _ _ _ hK (by omega) (Fin.ne_of_val_ne (by simpa using h2))
    (Fin.ne_of_val_ne (by simpa using h3))

theorem q2OmIota_peT30_mem_range {k : Fin (r + 1)} (h3 : k.val ≠ 3) (h0 : k.val ≠ 0) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (peT30 hr) ∈
      (pcOMExt (K := K) k).range := by
  rw [q2OmIota_peT30]
  exact peMEich_mem_range _ _ _ _ hK (by omega) (Fin.ne_of_val_ne (by simpa using h3))
    (Fin.ne_of_val_ne (by simpa using h0))

omit [Finite K] in
theorem peMEich_mulVec_inl_add_pdMP {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) {a b : Fin (r + 1)} (hai : i ≠ a) (haj : j ≠ a) :
    (((peMEich (K := K) (by omega : 1 ≤ r) hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ (Pi.single (Sum.inl a.castSucc) 1 + pdMP b) =
      Pi.single (Sum.inl a.castSucc) 1 + pdMP b :=
  peMEich_mulVec_of_polar _ _ _ _ (pe_polar_inl_add_pdMP_peMU hai) (pe_polar_inl_add_pdMP_peMU haj)

omit [Finite K] in
theorem peMEich_mulVec_inr_add_pdMP {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) {a b : Fin (r + 1)} (hai : i ≠ a) (haj : j ≠ a) :
    (((peMEich (K := K) (by omega : 1 ≤ r) hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ (Pi.single (Sum.inr a.castSucc) 1 + pdMP b) =
      Pi.single (Sum.inr a.castSucc) 1 + pdMP b :=
  peMEich_mulVec_of_polar _ _ _ _ (pe_polar_inr_add_pdMP_peMU hai) (pe_polar_inr_add_pdMP_peMU haj)

end Transporters

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem pe_conj_mem_range_of_peOff (hK : Nat.card K = 2) (hr3 : 3 ≤ r) (hn : 3 ≤ r + 2)
    {k : Fin (r + 1)} (h : StatedOmega (StatedQuadPlus (r + 2) K))
    {J : {J : Finset (Fin (r + 2)) // J.card ≤ 2}} (x : (plusDatum (r + 2) K hn).leviAmalgam J)
    (hA : PEOff (peSupp J.1) ((((h : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K k))
    (hB : PEOff (peSupp J.1) ((((h : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K k)) :
    h⁻¹ * peRho hn x * h ∈ (pcOMExt (K := K) k).range := by
  rw [mem_pcOMExt_range_iff k hK hr3]
  have key : ∀ z : Fin (r + 2) ⊕ Fin (r + 2) → K,
      PEOff (peSupp J.1) ((((h : StatedOmega (StatedQuadPlus (r + 2) K)) :
        GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
          (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z) →
      ((((h⁻¹ * peRho hn x * h : StatedOmega (StatedQuadPlus (r + 2) K))) :
        GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
          (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z = z := by
    intro z hz
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, peRho_mulVec, spinAction_levi_of_peOff hn x hz,
      Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  exact ⟨key _ hA, key _ hB⟩

end Conj

section Placement

variable {r : ℕ} (hr : 4 ≤ r)

@[expose] def PEMBad (J : Finset (Fin (r + 2))) : Prop := ∃ j ∈ J, r ≤ j.val

open Classical in
@[expose] noncomputable def peMIdx (J : Finset (Fin (r + 2))) : Fin (r + 1) :=
  if PEMBad J then
    (if (⟨0, by omega⟩ : Fin (r + 2)) ∈ J then ⟨2, by omega⟩
      else if (⟨1, by omega⟩ : Fin (r + 2)) ∈ J then ⟨3, by omega⟩ else ⟨1, by omega⟩)
  else if (Fin.last r).castSucc ∉ peSupp J then Fin.last r
  else if (⟨2, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J then ⟨2, by omega⟩
  else if h : ∃ k : Fin (r + 1), k.castSucc ∉ peSupp J then h.choose else 0

variable {K : Type} [Field K] [CharP K 2]

open Classical in
@[expose] noncomputable def peMTrJ (J : Finset (Fin (r + 2))) : StatedSp (r + 1) K :=
  if PEMBad J then
    (if (⟨0, by omega⟩ : Fin (r + 2)) ∈ J then peT10 hr * peT23 hr
      else if (⟨1, by omega⟩ : Fin (r + 2)) ∈ J then peT10 hr * peT30 hr else peT10 hr)
  else 1

end Placement

section Cases

variable {r : ℕ} (hr : 4 ≤ r)

theorem peM_bad_supp_zero {J : Finset (Fin (r + 2))} (hJ : J.card ≤ 2) (hb : PEMBad J)
    (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J) {x : Fin (r + 2)} (hx : x ∈ peSupp J) :
    x.val ≤ 1 ∨ r ≤ x.val := by
  obtain ⟨b, hbJ, hbr⟩ := hb
  have hne : (⟨0, by omega⟩ : Fin (r + 2)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  obtain ⟨j, hj, h⟩ := pe_mem_peSupp_iff.1 hx
  rcases pe_eq_or_eq_of_card_le_two hJ h0 hbJ hne hj with h' | h'
  · rw [h'] at h
    simp only at h
    omega
  · rw [h'] at h
    omega

theorem peM_bad_supp_one {J : Finset (Fin (r + 2))} (hJ : J.card ≤ 2) (hb : PEMBad J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J) {x : Fin (r + 2)} (hx : x ∈ peSupp J) :
    (1 ≤ x.val ∧ x.val ≤ 2) ∨ r ≤ x.val := by
  obtain ⟨b, hbJ, hbr⟩ := hb
  have hne : (⟨1, by omega⟩ : Fin (r + 2)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  obtain ⟨j, hj, h⟩ := pe_mem_peSupp_iff.1 hx
  rcases pe_eq_or_eq_of_card_le_two hJ h1 hbJ hne hj with h' | h'
  · rw [h'] at h
    simp only at h
    omega
  · rw [h'] at h
    omega

theorem peM_supp_two {J : Finset (Fin (r + 2))} (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∉ J) {x : Fin (r + 2)} (hx : x ∈ peSupp J) :
    2 ≤ x.val := by
  obtain ⟨j, hj, h⟩ := pe_mem_peSupp_iff.1 hx
  have hj0 : j.val ≠ 0 := fun h' => h0 (by rwa [show j = ⟨0, by omega⟩ from Fin.ext h'] at hj)
  have hj1 : j.val ≠ 1 := fun h' => h1 (by rwa [show j = ⟨1, by omega⟩ from Fin.ext h'] at hj)
  omega

omit hr in
theorem peM_good_supp {J : Finset (Fin (r + 2))} (hg : ¬ PEMBad J) {x : Fin (r + 2)}
    (hx : x ∈ peSupp J) : x.val ≤ r := by
  obtain ⟨j, hj, h⟩ := pe_mem_peSupp_iff.1 hx
  have hjr : j.val < r := by
    by_contra hc
    exact hg ⟨j, hj, by omega⟩
  omega

include hr in
theorem peM_exists_off {J : Finset (Fin (r + 2))} (hJ : J.card ≤ 2) :
    ∃ k : Fin (r + 1), k.castSucc ∉ peSupp J := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.map Fin.castSuccEmb : Finset (Fin (r + 2))) ⊆ peSupp J := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hx
    exact hc k
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := pe_card_peSupp_le J
  omega

omit hr in
theorem peM_mem_peSupp_singleton {a x : Fin (r + 2)} (ha : a.val < r) :
    x ∈ peSupp {a} ↔ x.val = a.val ∨ x.val = a.val + 1 := by
  rw [pe_mem_peSupp_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    omega
  · intro h
    exact ⟨a, Finset.mem_singleton_self a, Or.inl ⟨by omega, h⟩⟩

end Cases

section Act

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr : 4 ≤ r)

theorem q2OmIota_peT10_mulVec_a :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMA K ⟨1, by omega⟩ =
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨0, by omega⟩ := by
  rw [q2OmIota_peT10, peMEich_mulVec_a]

theorem q2OmIota_peT10_mulVec_b :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMB K ⟨1, by omega⟩ =
      Pi.single (Sum.inr (⟨1, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨0, by omega⟩ := by
  rw [q2OmIota_peT10, peMEich_mulVec_b]

theorem q2OmIota_peT23_mulVec_a :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT23 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMA K ⟨2, by omega⟩ =
      Pi.single (Sum.inl (⟨2, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨3, by omega⟩ := by
  rw [q2OmIota_peT23, peMEich_mulVec_a]

theorem q2OmIota_peT23_mulVec_b :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT23 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMB K ⟨2, by omega⟩ =
      Pi.single (Sum.inr (⟨2, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨3, by omega⟩ := by
  rw [q2OmIota_peT23, peMEich_mulVec_b]

theorem q2OmIota_peT30_mulVec_a :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT30 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMA K ⟨3, by omega⟩ =
      Pi.single (Sum.inl (⟨3, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨0, by omega⟩ := by
  rw [q2OmIota_peT30, peMEich_mulVec_a]

theorem q2OmIota_peT30_mulVec_b :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT30 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMB K ⟨3, by omega⟩ =
      Pi.single (Sum.inr (⟨3, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨0, by omega⟩ := by
  rw [q2OmIota_peT30, peMEich_mulVec_b]

theorem q2OmIota_peT10_mulVec_inl (a b : Fin (r + 1)) (ha0 : a.val ≠ 0) (ha1 : a.val ≠ 1) :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          (Pi.single (Sum.inl a.castSucc) 1 + pdMP b) =
      Pi.single (Sum.inl a.castSucc) 1 + pdMP b := by
  rw [q2OmIota_peT10]
  exact peMEich_mulVec_inl_add_pdMP hr _ _ _ (Fin.ne_of_val_ne (by simp; omega))
    (Fin.ne_of_val_ne (by simp; omega))

theorem q2OmIota_peT10_mulVec_inr (a b : Fin (r + 1)) (ha0 : a.val ≠ 0) (ha1 : a.val ≠ 1) :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (peT10 hr) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          (Pi.single (Sum.inr a.castSucc) 1 + pdMP b) =
      Pi.single (Sum.inr a.castSucc) 1 + pdMP b := by
  rw [q2OmIota_peT10]
  exact peMEich_mulVec_inr_add_pdMP hr _ _ _ (Fin.ne_of_val_ne (by simp; omega))
    (Fin.ne_of_val_ne (by simp; omega))

end Act

section Unfold

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (hr : 4 ≤ r) {J : Finset (Fin (r + 2))}

theorem peMIdx_bad_zero (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J) :
    peMIdx hr J = ⟨2, by omega⟩ := by
  simp only [peMIdx, hb, h0, ↓reduceIte]

theorem peMTrJ_bad_zero (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J) :
    peMTrJ (K := K) hr J = peT10 hr * peT23 hr := by
  simp only [peMTrJ, hb, h0, ↓reduceIte]

theorem peMIdx_bad_one (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J) : peMIdx hr J = ⟨3, by omega⟩ := by
  simp only [peMIdx, hb, h0, h1, ↓reduceIte]

theorem peMTrJ_bad_one (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J) : peMTrJ (K := K) hr J = peT10 hr * peT30 hr := by
  simp only [peMTrJ, hb, h0, h1, ↓reduceIte]

theorem peMIdx_bad_two (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∉ J) : peMIdx hr J = ⟨1, by omega⟩ := by
  simp only [peMIdx, hb, h0, h1, ↓reduceIte]

theorem peMTrJ_bad_two (hb : PEMBad J) (h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∉ J) : peMTrJ (K := K) hr J = peT10 hr := by
  simp only [peMTrJ, hb, h0, h1, ↓reduceIte]

theorem peMTrJ_good (hg : ¬ PEMBad J) : peMTrJ (K := K) hr J = 1 := by
  simp only [peMTrJ, hg, ↓reduceIte]

theorem peMIdx_good_off (hJ : J.card ≤ 2) (hg : ¬ PEMBad J) :
    (peMIdx hr J).castSucc ∉ peSupp J := by
  unfold peMIdx
  rw [ite_eq_right hg]
  by_cases h1 : (Fin.last r).castSucc ∉ peSupp J
  · rw [ite_eq_left h1]
    exact h1
  · rw [ite_eq_right h1]
    by_cases h2 : (⟨2, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J
    · rw [ite_eq_left h2]
      exact h2
    · rw [ite_eq_right h2]
      have h3 := peM_exists_off hr hJ
      rw [dite_eq_left h3]
      exact h3.choose_spec

theorem peMIdx_singleton {a : Fin (r + 2)} (ha : a.val < r) :
    (peMIdx hr {a}).val = r ∨ ((peMIdx hr {a}).val = 2 ∧ a.val + 1 = r) := by
  have hg : ¬ PEMBad ({a} : Finset (Fin (r + 2))) := by
    rintro ⟨j, hj, hjr⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    omega
  unfold peMIdx
  rw [ite_eq_right hg]
  by_cases h1 : (Fin.last r).castSucc ∈ peSupp {a}
  · rw [ite_eq_right (not_not.2 h1)]
    have h1' := (peM_mem_peSupp_singleton ha).1 h1
    simp only [Fin.val_castSucc, Fin.val_last] at h1'
    have h2 : (⟨2, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp {a} := by
      intro h
      have := (peM_mem_peSupp_singleton ha).1 h
      simp only [Fin.val_castSucc] at this
      omega
    rw [ite_eq_left h2]
    exact Or.inr ⟨rfl, by omega⟩
  · rw [ite_eq_left h1]
    exact Or.inl rfl

end Unfold

section Verify

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr : 4 ≤ r)

theorem peM_place (hn : 3 ≤ r + 2) (J : {J : Finset (Fin (r + 2)) // J.card ≤ 2})
    (x : (plusDatum (r + 2) K hn).leviAmalgam J) :
    (q2OmIota (r := r + 1) (by omega) hK (by omega) (peMTrJ hr J.1))⁻¹ * peRho hn x *
        q2OmIota (r := r + 1) (by omega) hK (by omega) (peMTrJ hr J.1) ∈
      (pcOMExt (K := K) (peMIdx hr J.1)).range := by
  have hr3 : 3 ≤ r := by omega
  by_cases hb : PEMBad J.1
  · by_cases h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J.1
    · have h2 : (⟨2, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
        have := peM_bad_supp_zero hr J.2 hb h0 h
        simp only [Fin.val_castSucc] at this
        omega
      have h3 : (⟨3, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
        have := peM_bad_supp_zero hr J.2 hb h0 h
        simp only [Fin.val_castSucc] at this
        omega
      rw [peMIdx_bad_zero hr hb h0, peMTrJ_bad_zero hr hb h0]
      refine pe_conj_mem_range_of_peOff hK hr3 hn _ x ?_ ?_
      · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
          q2OmIota_peT23_mulVec_a, q2OmIota_peT10_mulVec_inl hK hr ⟨2, by omega⟩ ⟨3, by omega⟩
            (by simp) (by simp)]
        exact peOff_inl_add_pdMP h2 h3
      · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
          q2OmIota_peT23_mulVec_b, q2OmIota_peT10_mulVec_inr hK hr ⟨2, by omega⟩ ⟨3, by omega⟩
            (by simp) (by simp)]
        exact peOff_inr_add_pdMP h2 h3
    · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J.1
      · have h3 : (⟨3, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
          have := peM_bad_supp_one hr J.2 hb h1 h
          simp only [Fin.val_castSucc] at this
          omega
        have h0' : (⟨0, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
          have := peM_bad_supp_one hr J.2 hb h1 h
          simp only [Fin.val_castSucc] at this
          omega
        rw [peMIdx_bad_one hr hb h0 h1, peMTrJ_bad_one hr hb h0 h1]
        refine pe_conj_mem_range_of_peOff hK hr3 hn _ x ?_ ?_
        · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
            q2OmIota_peT30_mulVec_a, q2OmIota_peT10_mulVec_inl hK hr ⟨3, by omega⟩ ⟨0, by omega⟩
              (by simp) (by simp)]
          exact peOff_inl_add_pdMP h3 h0'
        · rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
            q2OmIota_peT30_mulVec_b, q2OmIota_peT10_mulVec_inr hK hr ⟨3, by omega⟩ ⟨0, by omega⟩
              (by simp) (by simp)]
          exact peOff_inr_add_pdMP h3 h0'
      · have h1' : (⟨1, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
          have := peM_supp_two hr h0 h1 h
          simp only [Fin.val_castSucc] at this
          omega
        have h0' : (⟨0, by omega⟩ : Fin (r + 1)).castSucc ∉ peSupp J.1 := fun h => by
          have := peM_supp_two hr h0 h1 h
          simp only [Fin.val_castSucc] at this
          omega
        rw [peMIdx_bad_two hr hb h0 h1, peMTrJ_bad_two hr hb h0 h1]
        refine pe_conj_mem_range_of_peOff hK hr3 hn _ x ?_ ?_
        · rw [q2OmIota_peT10_mulVec_a]
          exact peOff_inl_add_pdMP h1' h0'
        · rw [q2OmIota_peT10_mulVec_b]
          exact peOff_inr_add_pdMP h1' h0'
  · have hN : Fin.last (r + 1) ∉ peSupp J.1 := fun h => by
      have := peM_good_supp hb h
      simp only [Fin.val_last] at this
      omega
    rw [peMTrJ_good hr hb, map_one]
    refine pe_conj_mem_range_of_peOff hK hr3 hn 1 x ?_ ?_
    · rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
      exact peOff_pdMA (peMIdx_good_off hr J.2 hb) hN
    · rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
      exact peOff_pdMB (peMIdx_good_off hr J.2 hb) hN

theorem peM_compat (I J : {J : Finset (Fin (r + 2)) // J.card ≤ 2}) (hIJ : I ≤ J)
    (hI : I.1.Nonempty) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) ((peMTrJ hr I.1)⁻¹ * peMTrJ hr J.1) ∈
      (pcOMExt (K := K) (peMIdx hr I.1)).range := by
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
  by_cases hab : r ≤ a.val
  · have hbI : PEMBad ({a} : Finset (Fin (r + 2))) := ⟨a, Finset.mem_singleton_self a, hab⟩
    have h0I : (⟨0, by omega⟩ : Fin (r + 2)) ∉ ({a} : Finset (Fin (r + 2))) := by
      rw [Finset.mem_singleton]
      intro h
      rw [← h] at hab
      simp at hab
      omega
    have h1I : (⟨1, by omega⟩ : Fin (r + 2)) ∉ ({a} : Finset (Fin (r + 2))) := by
      rw [Finset.mem_singleton]
      intro h
      rw [← h] at hab
      simp at hab
      omega
    rw [peMIdx_bad_two hr hbI h0I h1I, peMTrJ_bad_two hr hbI h0I h1I]
    have hbJ' : PEMBad J.1 := ⟨a, haJ, hab⟩
    by_cases h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J.1
    · rw [peMTrJ_bad_zero hr hbJ' h0, ← mul_assoc, inv_mul_cancel, one_mul]
      exact q2OmIota_peT23_mem_range hK hr (by simp) (by simp)
    · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J.1
      · rw [peMTrJ_bad_one hr hbJ' h0 h1, ← mul_assoc, inv_mul_cancel, one_mul]
        exact q2OmIota_peT30_mem_range hK hr (by simp) (by simp)
      · rw [peMTrJ_bad_two hr hbJ' h0 h1, inv_mul_cancel, map_one]
        exact one_mem _
  · push Not at hab
    have hgI : ¬ PEMBad ({a} : Finset (Fin (r + 2))) := by
      rintro ⟨j, hj, hjr⟩
      rw [Finset.mem_singleton] at hj
      subst hj
      omega
    rw [peMTrJ_good hr hgI, inv_one, one_mul]
    by_cases hbJ' : PEMBad J.1
    · obtain ⟨c, hcJ, hcr⟩ := hbJ'
      have hcb : c = b := by
        rcases hJab c hcJ with h | h
        · rw [h] at hcr
          omega
        · exact h
      subst hcb
      rcases peMIdx_singleton hr hab with hidx | ⟨hidx, hidx'⟩
      · by_cases h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∈ J.1
        · rw [peMTrJ_bad_zero hr ⟨c, hcJ, hcr⟩ h0, map_mul]
          exact mul_mem (q2OmIota_peT10_mem_range hK hr (by omega) (by omega))
            (q2OmIota_peT23_mem_range hK hr (by omega) (by omega))
        · by_cases h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∈ J.1
          · rw [peMTrJ_bad_one hr ⟨c, hcJ, hcr⟩ h0 h1, map_mul]
            exact mul_mem (q2OmIota_peT10_mem_range hK hr (by omega) (by omega))
              (q2OmIota_peT30_mem_range hK hr (by omega) (by omega))
          · rw [peMTrJ_bad_two hr ⟨c, hcJ, hcr⟩ h0 h1]
            exact q2OmIota_peT10_mem_range hK hr (by omega) (by omega)
      · have h0 : (⟨0, by omega⟩ : Fin (r + 2)) ∉ J.1 := by
          intro h
          rcases hJab _ h with h' | h'
          · have := congrArg Fin.val h'
            simp at this
            omega
          · have := congrArg Fin.val h'
            simp at this
            omega
        have h1 : (⟨1, by omega⟩ : Fin (r + 2)) ∉ J.1 := by
          intro h
          rcases hJab _ h with h' | h'
          · have := congrArg Fin.val h'
            simp at this
            omega
          · have := congrArg Fin.val h'
            simp at this
            omega
        rw [peMTrJ_bad_two hr ⟨c, hcJ, hcr⟩ h0 h1]
        exact q2OmIota_peT10_mem_range hK hr (by omega) (by omega)
    · rw [peMTrJ_good hr hbJ', map_one]
      exact one_mem _

end Verify

end CFSG.SeitzReduction.SymplecticPilot
