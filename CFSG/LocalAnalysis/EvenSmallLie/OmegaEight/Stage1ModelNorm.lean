module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelRad
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Q3Check

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

theorem mem_of_normalizes {X α : Type*} [Group X] [MulAction X α] {H K K₀ : Subgroup X}
    [Finite H] {F : α} {m : ℕ} (g : ℕ → X) (hg : ∀ i < m, g i ∈ H)
    (hinj : ∀ i < m, ∀ j < m, g i • F = g j • F → i = j)
    (hKH : K ≤ H) (hKF : ∀ k ∈ K, k • F = F) (hcard : Nat.card H = m * Nat.card K)
    (hK₀ : K₀ ≤ K) (hfix : ∀ i < m, (∀ k ∈ K₀, k • (g i • F) = g i • F) → g i • F = F)
    {x : X} (hx : x ∈ H) (hxN : x ∈ normalizer (K₀ : Set X)) : x ∈ K := by
  classical
  have : Finite K := Finite.of_injective (Subgroup.inclusion hKH) (inclusion_injective hKH)
  have : Finite (MulAction.orbit H F) := (Set.finite_range fun h : H => h • F).to_subtype
  set S := MulAction.stabilizer H F
  have hKS : K.subgroupOf H ≤ S := fun k hk => by
    rw [MulAction.mem_stabilizer_iff]
    exact hKF _ hk
  have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv
  have hKpos : 0 < Nat.card K := Nat.card_pos (α := K)
  set f : Fin m → MulAction.orbit H F := fun i =>
    ⟨(⟨g i, hg i i.2⟩ : H) • F, MulAction.mem_orbit _ _⟩
  have hf : Function.Injective f := fun i j e =>
    Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e))
  have hm : m ≤ S.index := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    simpa using Nat.card_le_card_of_injective f hf
  have h1 := S.card_mul_index
  rw [hcard] at h1
  have hKS' : Nat.card K ≤ Nat.card S := by
    rw [← hcardK]
    exact card_le_of_le hKS
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hSK : Nat.card S ≤ Nat.card K := by
    have h2 : Nat.card S * S.index ≤ Nat.card K * S.index :=
      calc Nat.card S * S.index = m * Nat.card K := h1
        _ ≤ S.index * Nat.card K := Nat.mul_le_mul_right _ hm
        _ = Nat.card K * S.index := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h2 hpos
  have hSeq : K.subgroupOf H = S := eq_of_le_of_card_ge hKS (by rw [hcardK]; exact hSK)
  have hSc : Nat.card S = Nat.card K := le_antisymm hSK hKS'
  have hidx : S.index = m := by
    rw [hSc, mul_comm m] at h1
    exact Nat.eq_of_mul_eq_mul_left hKpos h1
  have horb : ∀ y ∈ MulAction.orbit H F, ∃ i < m, y = g i • F := by
    intro y hy
    have hsub : Set.range (fun i : Fin m => (f i : α)) ⊆ MulAction.orbit H F := by
      rintro _ ⟨i, rfl⟩
      exact (f i).2
    have hrange : (Set.range (fun i : Fin m => (f i : α))).ncard = m := by
      rw [Set.ncard_range_of_injective (fun i j e => hf (Subtype.ext e)), Nat.card_fin]
    have heq : Set.range (fun i : Fin m => (f i : α)) = MulAction.orbit H F := by
      apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
      rw [hrange, ← MulAction.index_stabilizer, hidx]
    rw [← heq] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, i.2, rfl⟩
  obtain ⟨i, hi, hxi⟩ := horb (x • F) ⟨⟨x, hx⟩, rfl⟩
  have hfx : ∀ k ∈ K₀, k • (g i • F) = g i • F := by
    intro k hk
    rw [← hxi]
    have hk' : x⁻¹ * k * x ∈ K₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hxN) k).1 hk
      simpa using this
    calc k • x • F = x • (x⁻¹ * k * x) • F := by
          rw [smul_smul, smul_smul]
          group
      _ = x • F := by rw [hKF _ (hK₀ hk')]
  have hxF : x • F = F := hxi.trans (hfix i hi hfx)
  have hxS : (⟨x, hx⟩ : H) ∈ S := by
    rw [MulAction.mem_stabilizer_iff]
    exact hxF
  rw [← hSeq, mem_subgroupOf] at hxS
  exact hxS


namespace Model

theorem getD_eq_getElem! (M : Array Bool) {z : ℕ} (hz : z < M.size) : M.getD z false = M[z]! := by
  simp [Array.getD, hz]

theorem uOrig_spec {s : Array ℕ} (hs : s ∈ uOrig .plus) :
    Rep (deg .plus) s (permOfArr (deg .plus) s) ∧ permOfArr (deg .plus) s ∈ UQm .plus := by
  rw [uOrig, Array.mem_append, Array.mem_ofFn, Array.mem_ofFn] at hs
  rcases hs with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · have h := rep_psiM (ε := .plus) (Pi.single j 1)
    rw [vecBits_single] at h
    have e : permOfArr (deg .plus) (psiArr .plus (2 ^ (j : ℕ))) = psiM .plus (Pi.single j 1) := by
      rw [psiM, vecBits_single]
    rw [e]
    exact ⟨h.1, psiM_mem_U _⟩
  · exact ⟨(rep_uM (ε := .plus) k).1, uM_mem_U k⟩

theorem stabB_iff {s : Array ℕ} {σ : Equiv.Perm (Fin (deg .plus))} (hs : Rep (deg .plus) s σ)
    {M : Array Bool} {X : Set (Fin (deg .plus))}
    (hM : ∀ z (hz : z < 120), M.getD z false = true ↔ (⟨z, hz⟩ : Fin (deg .plus)) ∈ X) :
    stabB s M = true ↔ ∀ x ∈ X, σ x ∈ X := by
  rw [stabB, allLt_iff]
  constructor
  · intro h x hx
    have h1 := h x.val x.2
    rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · have := (hM x.val x.2).2 hx
      rw [this] at h1
      exact absurd h1 (by decide)
    · rw [hs.apply x.2] at h1
      exact (hM _ (σ x).2).1 h1
  · intro h z hz
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hz' : M.getD z false = true
    · right
      rw [hs.apply hz]
      exact (hM _ (σ ⟨z, hz⟩).2).2 (h _ ((hM z hz).1 hz'))
    · left
      simpa using hz'

theorem smul_eq_of_maps {σ : Equiv.Perm (Fin (deg .plus))} {X : Set (Fin (deg .plus))}
    (h : ∀ x ∈ X, σ x ∈ X) : σ • X = X := by
  have hsub : σ • X ⊆ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite _)

theorem closure_uM_inf_QMm : closure (Set.range (uM .plus)) ⊓ QMm .plus = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxQ⟩
  set z0 : Fin (deg .plus) := ⟨0, by decide⟩
  have hfix : closure (Set.range (uM .plus)) ≤ MulAction.stabilizer _ z0 := by
    rw [closure_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    apply Fin.ext
    rw [← (rep_uM (ε := .plus) k).1.apply (show 0 < 120 by norm_num)]
    exact q3_parts.1 k k.2
  have hx0 : x z0 = z0 := by
    have := hfix hxU
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this
  obtain ⟨v, rfl⟩ := mem_QMm.1 hxQ
  have hz0 : z0 ∈ Oset .plus := pBase_mem_Oset zero_mem_pBase
  by_cases hv : v = 0
  · rw [hv, psiM_zero]
    exact one_mem _
  · exact absurd hx0 (hz0 v hv)


theorem oMasks_iff {i : ℕ} (hi : i < (oOrbitW .plus).size) {G : Equiv.Perm (Fin (deg .plus))}
    (hG : Rep (deg .plus) (invCand (deg .plus) (oOrbitW .plus)[i]!) G⁻¹) (z : ℕ) (hz : z < 120) :
    (oMasksW[i]!).getD z false = true ↔ (⟨z, hz⟩ : Fin (deg .plus)) ∈ G • Oset .plus := by
  rw [oMasksW, map_getElem! _ _ hi, getD_eq_getElem! _ (by rw [maskOf, Array.size_ofFn]; exact hz)]
  exact maskOf_iff hG hz

theorem normalizer_UQm_le_PM {x : Equiv.Perm (Fin (deg .plus))} (hxL : x ∈ Lm .plus)
    (hxN : x ∈ normalizer (UQm .plus : Set (Equiv.Perm (Fin (deg .plus))))) : x ∈ PM .plus := by
  have hsz : (oOrbitW .plus).size = nOrb .plus := (oSet_parts .plus).2.2.2.1
  have hT := (oSet_parts .plus).2.2.2.2.1
  have hrep : ∀ i < nOrb .plus, Rep (deg .plus) (oOrbitW .plus)[i]!
      (permOfArr (deg .plus) (oOrbitW .plus)[i]!) ∧
      Rep (deg .plus) (invCand (deg .plus) (oOrbitW .plus)[i]!)
        (permOfArr (deg .plus) (oOrbitW .plus)[i]!)⁻¹ := fun i hi =>
    rep_permOfArr (hT i (by omega)).1
  refine mem_of_normalizes (H := Lm .plus) (K := PM .plus) (K₀ := UQm .plus) (F := Oset .plus)
    (m := nOrb .plus) (fun i => permOfArr (deg .plus) (oOrbitW .plus)[i]!) (fun i hi => ?_)
    (fun i hi j hj e => ?_) inf_le_left (fun k hk => smul_Oset_of_mem_normalizer hk.2) ?_
    UQm_le_PM (fun i hi hfixU => ?_) hxL hxN
  · exact (memL_iff (hrep i hi).1).1 (hT i (by omega)).2
  · exact smul_Oset_injective hi hj (hrep i hi).2 (hrep j hj).2 e
  · rw [card_Lm, card_Lm_eq, card_PM]
  · have hi0 : i = 0 := q3_parts.2.2.1 i (by omega) fun s hs => by
      obtain ⟨hs1, hs2⟩ := uOrig_spec hs
      refine (stabB_iff hs1 (oMasks_iff (by omega) (hrep i hi).2)).2 fun y hy => ?_
      have := hfixU _ hs2
      rw [← this]
      exact Set.smul_mem_smul_set hy
    subst hi0
    have h0 : permOfArr (deg .plus) (oOrbitW .plus)[0]! = 1 :=
      eq_of_eqA (hrep 0 (by decide)).1 rep_idA q3_parts.2.1
    simp only [h0, one_smul]

@[expose] def flagSets : Set (Fin (deg .plus)) × Set (Fin (deg .plus)) :=
  ({z | flagA.getD z.val false = true}, {z | flagB.getD z.val false = true})

theorem fmask_iff (A : Array Bool) {g : Array ℕ} {G : Equiv.Perm (Fin (deg .plus))}
    (hG : Rep (deg .plus) (invCand (deg .plus) g) G⁻¹) (z : ℕ) (hz : z < 120) :
    (fmask A g).getD z false = true ↔
      (⟨z, hz⟩ : Fin (deg .plus)) ∈ G • {y : Fin (deg .plus) | A.getD y.val false = true} := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def, Set.mem_ofPred_eq,
    ← hG.apply hz]
  simp [fmask, Array.getD, hz]
  rfl

theorem UQm_fix_flag : ∀ k ∈ UQm .plus, k • flagSets = flagSets := by
  have hle : UQm .plus ≤ MulAction.stabilizer (Equiv.Perm (Fin (deg .plus))) flagSets := by
    rw [UQm_eq, closure_le]
    have key : ∀ s ∈ uOrig .plus,
        permOfArr (deg .plus) s ∈ MulAction.stabilizer (Equiv.Perm (Fin (deg .plus))) flagSets := by
      intro s hs
      obtain ⟨hs1, -⟩ := uOrig_spec hs
      obtain ⟨hA, hB⟩ := q3_parts.2.2.2.2.2.2.2.1 s hs
      have hMA : ∀ z (hz : z < 120), flagA.getD z false = true ↔
          (⟨z, hz⟩ : Fin (deg .plus)) ∈ flagSets.1 := fun z hz => Iff.rfl
      have hMB : ∀ z (hz : z < 120), flagB.getD z false = true ↔
          (⟨z, hz⟩ : Fin (deg .plus)) ∈ flagSets.2 := fun z hz => Iff.rfl
      rw [MulAction.mem_stabilizer_iff, Prod.smul_def]
      ext1
      · exact smul_eq_of_maps ((stabB_iff hs1 hMA).1 hA)
      · exact smul_eq_of_maps ((stabB_iff hs1 hMB).1 hB)
    rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · have := key (psiArr .plus (2 ^ (j : ℕ))) (by
        rw [uOrig, Array.mem_append, Array.mem_ofFn]
        exact Or.inl ⟨j, rfl⟩)
      rwa [show permOfArr (deg .plus) (psiArr .plus (2 ^ (j : ℕ))) = psiM .plus (Pi.single j 1) by
        rw [psiM, vecBits_single]] at this
    · exact key (uArr .plus k) (by
        rw [uOrig, Array.mem_append, Array.mem_ofFn, Array.mem_ofFn]
        exact Or.inr ⟨k, rfl⟩)
  intro k hk
  exact hle hk

theorem normalizer_UQm_le_UQm {x : Equiv.Perm (Fin (deg .plus))} (hxP : x ∈ PM .plus)
    (hxN : x ∈ normalizer (UQm .plus : Set (Equiv.Perm (Fin (deg .plus))))) : x ∈ UQm .plus := by
  have hp := q3_parts
  have hsz : flagOrbitW.size = 315 := hp.2.2.2.1
  have hF := hp.2.2.2.2.2.1
  have hrep : ∀ j < 315, Rep (deg .plus) flagOrbitW[j]! (permOfArr (deg .plus) flagOrbitW[j]!) ∧
      Rep (deg .plus) (invCand (deg .plus) flagOrbitW[j]!)
        (permOfArr (deg .plus) flagOrbitW[j]!)⁻¹ := fun j hj =>
    rep_permOfArr (hF j (by omega)).1
  have hmA : ∀ j < 315, ∀ z (hz : z < 120), ((fMasksAW flagOrbitW)[j]!).getD z false = true ↔
      (⟨z, hz⟩ : Fin (deg .plus)) ∈ permOfArr (deg .plus) flagOrbitW[j]! • flagSets.1 := by
    intro j hj z hz
    rw [fMasksAW, map_getElem! _ _ (by omega)]
    exact fmask_iff flagA (hrep j hj).2 z hz
  have hmB : ∀ j < 315, ∀ z (hz : z < 120), ((fMasksBW flagOrbitW)[j]!).getD z false = true ↔
      (⟨z, hz⟩ : Fin (deg .plus)) ∈ permOfArr (deg .plus) flagOrbitW[j]! • flagSets.2 := by
    intro j hj z hz
    rw [fMasksBW, map_getElem! _ _ (by omega)]
    exact fmask_iff flagB (hrep j hj).2 z hz
  refine mem_of_normalizes (H := PM .plus) (K := UQm .plus) (K₀ := UQm .plus) (F := flagSets)
    (m := 315) (fun j => permOfArr (deg .plus) flagOrbitW[j]!) (fun j hj => ?_)
    (fun j hj j' hj' e => ?_) UQm_le_PM UQm_fix_flag ?_ le_rfl (fun j hj hfixU => ?_) hxP hxN
  · rw [← PQm_eq_PM]
    exact (memP_iff (hrep j hj).1).1 (hF j (by omega)).2
  · have hA : permOfArr (deg .plus) flagOrbitW[j]! • flagSets.1 =
        permOfArr (deg .plus) flagOrbitW[j']! • flagSets.1 := congrArg Prod.fst e
    have hB : permOfArr (deg .plus) flagOrbitW[j]! • flagSets.2 =
        permOfArr (deg .plus) flagOrbitW[j']! • flagSets.2 := congrArg Prod.snd e
    have key : ∀ a b, a < 315 → b < a →
        permOfArr (deg .plus) flagOrbitW[a]! • flagSets.1 =
          permOfArr (deg .plus) flagOrbitW[b]! • flagSets.1 →
        permOfArr (deg .plus) flagOrbitW[a]! • flagSets.2 =
          permOfArr (deg .plus) flagOrbitW[b]! • flagSets.2 → False := by
      intro a b ha hba e1 e2
      obtain ⟨z, hz, hne⟩ := hp.2.2.2.2.2.2.1 a (by omega) b hba
      rcases hne with hne | hne
      · apply hne
        rw [Bool.eq_iff_iff, hmA a ha z hz, hmA b (by omega) z hz, e1]
      · apply hne
        rw [Bool.eq_iff_iff, hmB a ha z hz, hmB b (by omega) z hz, e2]
    rcases lt_trichotomy j j' with h | h | h
    · exact (key j' j hj' h hA.symm hB.symm).elim
    · exact h
    · exact (key j j' hj h hA hB).elim
  · rw [card_PM, card_UQm]
    rfl
  · have hj0 : j = 0 := hp.2.2.2.2.2.2.2.2.1 j (by omega) fun s hs => by
      obtain ⟨hs1, hs2⟩ := uOrig_spec hs
      have hk := hfixU _ hs2
      rw [Prod.smul_def] at hk
      have hk1 : permOfArr (deg .plus) s • permOfArr (deg .plus) flagOrbitW[j]! • flagSets.1 =
          permOfArr (deg .plus) flagOrbitW[j]! • flagSets.1 := by
        have := congrArg Prod.fst hk
        simpa [Prod.smul_def] using this
      have hk2 : permOfArr (deg .plus) s • permOfArr (deg .plus) flagOrbitW[j]! • flagSets.2 =
          permOfArr (deg .plus) flagOrbitW[j]! • flagSets.2 := by
        have := congrArg Prod.snd hk
        simpa [Prod.smul_def] using this
      refine ⟨(stabB_iff hs1 (hmA j hj)).2 fun y hy => ?_, (stabB_iff hs1 (hmB j hj)).2 fun y hy => ?_⟩
      · rw [← hk1]
        exact Set.smul_mem_smul_set hy
      · rw [← hk2]
        exact Set.smul_mem_smul_set hy
    subst hj0
    have h0 : permOfArr (deg .plus) flagOrbitW[0]! = 1 :=
      eq_of_eqA (hrep 0 (by decide)).1 rep_idA hp.2.2.2.2.1
    simp only [h0, one_smul]

theorem normalizer_UQm {x : Equiv.Perm (Fin (deg .plus))} (hxL : x ∈ Lm .plus)
    (hxN : x ∈ normalizer (UQm .plus : Set (Equiv.Perm (Fin (deg .plus))))) : x ∈ UQm .plus :=
  normalizer_UQm_le_UQm (normalizer_UQm_le_PM hxL hxN) hxN

end Model

end CFSG.EvenSmallLie.OmegaEight.Stage1
