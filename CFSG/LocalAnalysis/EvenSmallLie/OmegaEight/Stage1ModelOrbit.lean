module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelElts

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped Pointwise

variable {ε : Eps}

@[expose] def Oset (ε : Eps) : Set (Fin (deg ε)) := {z | ∀ v : V6, v ≠ 0 → psiM ε v z ≠ z}

theorem vecBits_ne_zero {v : V6} (hv : v ≠ 0) : vecBits v ≠ 0 := fun h0 =>
  hv (by rw [← toVec_vecBits v, h0]; ext i; simp [toVec, bz])

theorem inO_iff {z : ℕ} (hz : z < deg ε) :
    inO ε z = true ↔ (⟨z, hz⟩ : Fin (deg ε)) ∈ Oset ε := by
  rw [inO, allLt_iff]
  constructor
  · intro h v hv e
    have hv' := vecBits_ne_zero hv
    have h1 := h (vecBits v - 1) (by have := vecBits_lt v; omega)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hv'), psiT_eq ε (vecBits_lt v),
      (rep_psiM v).1.apply hz, e] at h1
    simp at h1
  · intro h y hy
    have hy1 : y + 1 < 64 := by omega
    have hv : vecBits (toVec 6 (y + 1)) = y + 1 := vecBits_toVec hy1
    have hv0 : toVec 6 (y + 1) ≠ 0 := fun h0 => by
      rw [h0, vecBits_zero] at hv
      omega
    rw [psiT_eq ε hy1, ← hv, (rep_psiM _).1.apply hz]
    have := h _ hv0
    simp only [bne_iff_ne, ne_eq]
    exact fun e => this (Fin.ext e)

theorem oSet_parts (ε : Eps) :
    (∀ z < deg ε, inOT ε z = inO ε z) ∧ (∀ b ∈ pBaseA ε, inOT ε b = true) ∧
    (∀ z < deg ε, inOT ε z = true → ∃ y < 64, (psiT ε y)[0]! = z) ∧
    (oOrbitW ε).size = nOrb ε ∧
    (∀ i < (oOrbitW ε).size, isInvA (deg ε) (oOrbitW ε)[i]! (invCand (deg ε) (oOrbitW ε)[i]!) = true ∧
      memL ε (oOrbitW ε)[i]! = true) ∧
    (∀ i < (oOrbitW ε).size, ∀ j < i, ∃ z < deg ε,
      (((oOrbitW ε).map (maskOf ε))[i]!)[z]! ≠ (((oOrbitW ε).map (maskOf ε))[j]!)[z]!) := by
  have h := (modelChecks ε).2.2.1
  simp only [oSetCheckW, Bool.and_eq_true, allLt_iff, beq_iff_eq, Array.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun b hb => ?_, fun z hz hO => ?_, h4, h5, h6⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hb
    exact h2 i hi
  · rcases h3 z hz with h | ⟨y, hy, e⟩
    · rw [hO] at h
      exact absurd h (by decide)
    · exact ⟨y, hy, e⟩


theorem mem_Oset_iff_inOT {z : ℕ} (hz : z < deg ε) :
    (⟨z, hz⟩ : Fin (deg ε)) ∈ Oset ε ↔ inOT ε z = true := by
  rw [(oSet_parts ε).1 z hz, inO_iff hz]

theorem pBase_mem_Oset {b : Fin (deg ε)} (hb : b ∈ pBase ε) : b ∈ Oset ε := by
  have := (oSet_parts ε).2.1 b.val (by
    rw [pBaseA, List.mem_toArray, List.mem_map]
    exact ⟨b, hb, rfl⟩)
  exact (mem_Oset_iff_inOT b.2).2 this

theorem exists_psiM_apply {z : Fin (deg ε)} (hz : z ∈ Oset ε) :
    ∃ v, psiM ε v ⟨0, by have := one_le_deg ε; omega⟩ = z := by
  obtain ⟨y, hy, e⟩ := (oSet_parts ε).2.2.1 z.val z.2 ((mem_Oset_iff_inOT z.2).1 hz)
  refine ⟨toVec 6 y, Fin.ext ?_⟩
  rw [psiT_eq ε hy, ← vecBits_toVec hy, (rep_psiM _).1.apply (by have := one_le_deg ε; omega)] at e
  exact e

theorem apply_mem_Oset {g : Equiv.Perm (Fin (deg ε))} (hg : g ∈ normalizer (QMm ε : Set _))
    {z : Fin (deg ε)} (hz : z ∈ Oset ε) : g z ∈ Oset ε := by
  intro v hv e
  have h1 : g⁻¹ * psiM ε v * g ∈ QMm ε := by
    have := (mem_normalizer_iff.1 (inv_mem hg) (psiM ε v)).1 (psiM_mem_Q v)
    simpa using this
  obtain ⟨w, hw⟩ := mem_QMm.1 h1
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [psiM_zero] at hw
    have : psiM ε v = 1 := by
      have := congrArg (fun x => g * x * g⁻¹) hw
      simpa [mul_assoc] using this.symm
    exact hv (psiM_injective (this.trans psiM_zero.symm))
  apply hz w hw0
  rw [hw, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e]
  simp

theorem smul_Oset_of_mem_normalizer {g : Equiv.Perm (Fin (deg ε))}
    (hg : g ∈ normalizer (QMm ε : Set _)) : g • Oset ε = Oset ε := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hz
    have := apply_mem_Oset hg hz
    simpa using this
  · intro hz
    exact apply_mem_Oset (inv_mem hg) hz

theorem maskOf_get (g : Array ℕ) {z : ℕ} (hz : z < deg ε) :
    (maskOf ε g)[z]! = inOT ε (invCand (deg ε) g)[z]! := by
  rw [maskOf, getElem!_pos _ z (by simpa using hz), Array.getElem_ofFn]

theorem maskOf_iff {g : Array ℕ} {G : Equiv.Perm (Fin (deg ε))}
    (hG : Rep (deg ε) (invCand (deg ε) g) G⁻¹) {z : ℕ} (hz : z < deg ε) :
    (maskOf ε g)[z]! = true ↔ (⟨z, hz⟩ : Fin (deg ε)) ∈ G • Oset ε := by
  rw [maskOf_get g hz, Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def, hG.apply hz,
    ← mem_Oset_iff_inOT]

theorem map_getElem! {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {i : ℕ}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem smul_Oset_injective {i j : ℕ} (hi : i < nOrb ε) (hj : j < nOrb ε)
    {Gi Gj : Equiv.Perm (Fin (deg ε))} (hGi : Rep (deg ε) (invCand (deg ε) (oOrbitW ε)[i]!) Gi⁻¹)
    (hGj : Rep (deg ε) (invCand (deg ε) (oOrbitW ε)[j]!) Gj⁻¹) (e : Gi • Oset ε = Gj • Oset ε) :
    i = j := by
  have hsz := (oSet_parts ε).2.2.2.1
  have key : ∀ i j, i < nOrb ε → j < i →
      ∀ {Gi Gj : Equiv.Perm (Fin (deg ε))},
        Rep (deg ε) (invCand (deg ε) (oOrbitW ε)[i]!) Gi⁻¹ →
        Rep (deg ε) (invCand (deg ε) (oOrbitW ε)[j]!) Gj⁻¹ → Gi • Oset ε ≠ Gj • Oset ε := by
    intro i j hi hji Gi Gj hGi hGj e
    obtain ⟨z, hz, hne⟩ := (oSet_parts ε).2.2.2.2.2 i (by omega) j hji
    rw [map_getElem! _ _ (by omega), map_getElem! _ _ (by omega)] at hne
    apply hne
    rw [Bool.eq_iff_iff, maskOf_iff hGi hz, maskOf_iff hGj hz, e]
  rcases lt_trichotomy i j with h | h | h
  · exact absurd e.symm (key j i hj h hGj hGi)
  · exact h
  · exact absurd e (key i j hi h hGi hGj)

theorem card_normalizer_le :
    Nat.card (Lm ε ⊓ normalizer (QMm ε : Set _) : Subgroup _) ≤ 64 * (oBound ε / 2) := by
  set N := (Lm ε ⊓ normalizer (QMm ε : Set _) : Subgroup _)
  set S := MulAction.stabilizer (Lm ε) (Oset ε)
  have hle : N.subgroupOf (Lm ε) ≤ S := by
    intro g hg
    rw [mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    exact smul_Oset_of_mem_normalizer hg.2
  have h1 : Nat.card N ≤ Nat.card S := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : N ≤ Lm ε)).toEquiv]
    exact Subgroup.card_le_of_le hle
  have hsz := (oSet_parts ε).2.2.2.1
  have hT := (oSet_parts ε).2.2.2.2.1
  have hG : ∀ i : Fin (nOrb ε), permOfArr (deg ε) (oOrbitW ε)[(i : ℕ)]! ∈ Lm ε := fun i =>
    (memL_iff (rep_permOfArr (hT i (by omega)).1).1).1 (hT i (by omega)).2
  have h2 : nOrb ε ≤ S.index := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    let f : Fin (nOrb ε) → MulAction.orbit (Lm ε) (Oset ε) := fun i =>
      ⟨(⟨_, hG i⟩ : Lm ε) • Oset ε, MulAction.mem_orbit _ _⟩
    have hf : Function.Injective f := by
      intro i j e
      have e' : (permOfArr (deg ε) (oOrbitW ε)[(i : ℕ)]!) • Oset ε =
          (permOfArr (deg ε) (oOrbitW ε)[(j : ℕ)]!) • Oset ε := congrArg Subtype.val e
      exact Fin.ext (smul_Oset_injective i.2 j.2 (rep_permOfArr (hT i (by omega)).1).2
        (rep_permOfArr (hT j (by omega)).1).2 e')
    simpa using Nat.card_le_card_of_injective f hf
  have h3 := S.card_mul_index
  rw [card_Lm, card_Lm_eq] at h3
  have hpos : 0 < nOrb ε := by cases ε <;> decide
  have h4 : Nat.card S * nOrb ε ≤ 64 * (oBound ε / 2) * nOrb ε :=
    calc Nat.card S * nOrb ε ≤ Nat.card S * S.index := Nat.mul_le_mul_left _ h2
      _ = nOrb ε * (64 * (oBound ε / 2)) := h3
      _ = 64 * (oBound ε / 2) * nOrb ε := mul_comm _ _
  exact h1.trans (Nat.le_of_mul_le_mul_right h4 hpos)

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
