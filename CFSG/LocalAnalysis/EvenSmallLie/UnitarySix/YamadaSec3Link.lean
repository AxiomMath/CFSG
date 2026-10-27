module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Para
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Codes
public import CFSG.Fischer.T46Simple
public import CFSG.Fischer.T46Unitary

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Fischer


theorem psi0_mem (B : SUJ) : psi0 B ∈ T46 := by
  rw [← range_piSU]
  exact ⟨conjQ B, rfl⟩

@[expose] noncomputable def psiT : SUJ →* T46 := psi0.codRestrict T46 psi0_mem

theorem coe_psiT (B : SUJ) : (psiT B : Equiv.Perm (Fin 693)) = psi0 B := rfl


theorem rep_psi0_yamGen {k : ℕ} (hk : k < 18) : Rep 693 (gA k) (psi0 (yamGen k)) := by
  intro x
  rw [psi0_apply, ← (tabs_spec tabs_check hk).1, ← codesOf_yamMat hk, ← tabOfMat_eq_tabC ptsFacts,
    tabOfMat, getElem!_pos _ _ (by simp)]
  simp only [Array.getElem_ofFn]
  rfl

theorem psi0_yamGen {k : ℕ} (hk : k < 18) : psi0 (yamGen k) = gP k :=
  (permOfArr_eq_of_rep (rep_psi0_yamGen hk)).symm

theorem gP_mem_T46 {k : ℕ} (hk : k < 18) : gP k ∈ T46 := psi0_yamGen hk ▸ psi0_mem _

theorem wP_mem_T46 : ∀ w : List ℕ, (∀ k ∈ w, k < 18) → wP w ∈ T46
  | [], _ => by simp [wP, one_mem]
  | k :: w, hw => by
    rw [wP, List.map_cons, List.prod_cons]
    exact mul_mem (gP_mem_T46 (hw k List.mem_cons_self))
      (wP_mem_T46 w fun j hj => hw j (List.mem_cons_of_mem k hj))

theorem grp_le_T46 {c : ChainData} (hg : c.GensOK) : c.grp ≤ T46 :=
  grp_le fun w hw => wP_mem_T46 w (hg w hw)

theorem chL_eq_T46 : chL.grp = T46 :=
  Subgroup.eq_of_le_of_card_ge (grp_le_T46 gensOK_chL) (by rw [card_T46, card_chL])

set_option maxRecDepth 10000 in
theorem card_stabilizer_zero : Nat.card (MulAction.stabilizer T46 (0 : Fin 693)) = 13271040 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer T46 (0 : Fin 693))
  have horb : MulAction.orbit T46 (0 : Fin 693) = Set.univ := MulAction.orbit_eq_univ T46 0
  rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin 693),
    Fintype.card_fin, card_T46] at h
  omega

theorem stabilizer_zero_eq :
    (MulAction.stabilizer T46 (0 : Fin 693)).map T46.subtype = chK1A1.grp := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    refine ⟨⟨x, grp_le_T46 gensOK_chK1A1 hx⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
    exact K1A1_fix x hx
  · rw [Subgroup.card_map_of_injective T46.subtype_injective, card_stabilizer_zero, card_chK1A1]

theorem normalizer_S_eq :
    Subgroup.normalizer (chS.grp : Set (Equiv.Perm (Fin 693))) ⊓ T46 = chSJ.grp := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hn, hT⟩ := Subgroup.mem_inf.1 hx
    have h0 := normalizer_fix hn
    have hst : x ∈ (MulAction.stabilizer T46 (0 : Fin 693)).map T46.subtype :=
      ⟨⟨x, hT⟩, MulAction.mem_stabilizer_iff.2 h0, rfl⟩
    rw [stabilizer_zero_eq] at hst
    exact mem_SJ_of_normalizer hst hn
  · exact le_inf SJ_le_normalizer (grp_le_T46 gensOK_chSJ)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
