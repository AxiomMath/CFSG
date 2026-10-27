module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped Pointwise

variable {Γ : Type} [Group Γ]

private lemma mulAut_conj_smul_eq_conjSub (g : Γ) (H : Subgroup Γ) :
    MulAut.conj g • H = conjSub g H := by
  ext x
  rw [conjSub, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

private lemma conjSub_injective (g : Γ) : Function.Injective (conjSub g) :=
  Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
    (fun _ _ h => (MulAut.conj g).injective h)

private lemma card_conjSub (g : Γ) (H : Subgroup Γ) :
    Nat.card (conjSub g H) = Nat.card H := by
  rw [conjSub]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (fun _ _ h => (MulAut.conj g).injective h)

private lemma conjSub_mul (a b : Γ) (H : Subgroup Γ) :
    conjSub a (conjSub b H) = conjSub (a * b) H := by
  have hf : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [conjSub, conjSub, conjSub, Subgroup.map_map, hf]

theorem card_normIn_mul_le [Finite Γ] {L E : Subgroup Γ} {u : Γ} (hu : u ∈ invols L)
    (hconj : ∀ v ∈ invols L, ∃ l ∈ L, v = l * u * l⁻¹) (hEL : E ≤ L)
    (hE : Nat.card E = 8) (hEa : IsElemAbelian 2 E) (Ws : List (Subgroup Γ)) (hnodup : Ws.Nodup)
    (hWs : ∀ W ∈ Ws, (∃ l ∈ L, W = conjSub l E) ∧ u ∈ W) :
    Nat.card (normIn L E) * (Nat.card (invols L) * Ws.length) ≤ 7 * Nat.card L := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Finite (Subgroup Γ) :=
    Finite.of_injective _ (SetLike.coe_injective : Function.Injective
      (SetLike.coe : Subgroup Γ → Set Γ))
  haveI : Fintype (Subgroup Γ) := Fintype.ofFinite _
  letI : MulAction ↥L (Subgroup Γ) :=
    MulAction.compHom (Subgroup Γ) (MulAut.conj.comp L.subtype)
  let Wf : Finset (Subgroup Γ) := Finset.univ.filter (fun W => ∃ l ∈ L, W = conjSub l E)
  let If : Finset Γ := Finset.univ.filter (fun v => v ∈ invols L)
  have hIfcard : If.card = Nat.card (invols L) := by
    have hs : (invols L).Finite := Set.toFinite _
    have hEq : If = hs.toFinset := by
      ext v
      simp [If, Set.Finite.mem_toFinset]
    rw [hEq, ← Set.ncard_eq_toFinset_card (invols L) hs, Nat.card_coe_set_eq]
  have hWeq : Wf = (MulAction.orbit ↥L E).toFinset := by
    ext W
    rw [Set.mem_toFinset, MulAction.mem_orbit_iff]
    simp only [Wf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l, hl⟩, ?_⟩
      change MulAut.conj l • E = conjSub l E
      rw [mulAut_conj_smul_eq_conjSub]
    · rintro ⟨g, hg⟩
      refine ⟨(g : Γ), g.2, ?_⟩
      rw [← hg]
      change MulAut.conj (g : Γ) • E = conjSub (g : Γ) E
      rw [mulAut_conj_smul_eq_conjSub]
  have hmem : ∀ l : ↥L, l ∈ MulAction.stabilizer ↥L E ↔ conjSub (l : Γ) E = E := by
    intro l
    rw [MulAction.mem_stabilizer_iff]
    change MulAut.conj (l : Γ) • E = E ↔ conjSub (l : Γ) E = E
    rw [mulAut_conj_smul_eq_conjSub]
  have hmap : (MulAction.stabilizer ↥L E).map L.subtype = normIn L E := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [normIn, Subgroup.mem_inf]
      refine ⟨l.2, ?_⟩
      exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr
        (by simpa [conjSub] using (hmem l).mp hl)
    · intro hx
      rw [normIn, Subgroup.mem_inf] at hx
      obtain ⟨hxL, hxN⟩ := hx
      refine ⟨⟨x, hxL⟩, (hmem ⟨x, hxL⟩).mpr ?_, rfl⟩
      simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq).mp hxN
  have hstabcard : Nat.card (MulAction.stabilizer ↥L E) = Nat.card (normIn L E) := by
    have hcm := Subgroup.card_map_of_injective (K := MulAction.stabilizer ↥L E)
      (f := L.subtype) L.subtype_injective
    rw [hmap] at hcm
    exact hcm.symm
  have horbit : (MulAction.orbit ↥L E).ncard = Wf.card := by
    rw [Set.ncard_eq_toFinset_card', ← hWeq]
  have hstab : Wf.card * Nat.card (normIn L E) = Nat.card L := by
    have hidx := MulAction.index_stabilizer ↥L E
    have hcard := Subgroup.card_mul_index (H := MulAction.stabilizer ↥L E)
    rw [hidx] at hcard
    rw [hstabcard, horbit] at hcard
    exact (mul_comm Wf.card (Nat.card (normIn L E))).trans hcard
  have hm : ∀ v ∈ If, Ws.length ≤ (Wf.bipartiteAbove (fun v W => v ∈ W) v).card := by
    intro v hv
    simp only [If, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨l, hlL, hvl⟩ := hconj v hv
    have hsub : (Ws.toFinset.image (conjSub l)) ⊆
        Wf.bipartiteAbove (fun v W => v ∈ W) v := by
      intro W hW
      rw [Finset.mem_image] at hW
      obtain ⟨W', hW', rfl⟩ := hW
      rw [List.mem_toFinset] at hW'
      obtain ⟨⟨l', hl'L, hW'eq⟩, huW'⟩ := hWs W' hW'
      rw [Finset.mem_bipartiteAbove]
      refine ⟨?_, ?_⟩
      · simp only [Wf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l * l', L.mul_mem hlL hl'L, by rw [hW'eq, conjSub_mul]⟩
      · rw [conjSub]
        exact Subgroup.mem_map.mpr ⟨u, huW', by simp [MulAut.conj_apply, hvl]⟩
    calc Ws.length = (Ws.toFinset.image (conjSub l)).card := by
          rw [Finset.card_image_of_injective (f := conjSub l) Ws.toFinset
            (conjSub_injective l), List.toFinset_card_of_nodup hnodup]
      _ ≤ _ := Finset.card_le_card hsub
  have hn : ∀ W ∈ Wf, (If.bipartiteBelow (fun v W => v ∈ W) W).card ≤ 7 := by
    intro W hW
    simp only [Wf, Finset.mem_filter, Finset.mem_univ, true_and] at hW
    obtain ⟨l, _, hWl⟩ := hW
    have hWcard : Nat.card W = 8 := by
      rw [hWl, card_conjSub, hE]
    let Wfin : Finset Γ := Finset.univ.filter (fun v => v ∈ W)
    have hWfin_card : Wfin.card = 8 := by
      have hcoe : (Wfin : Set Γ) = (W : Set Γ) := by ext v; simp [Wfin]
      rw [← Set.ncard_coe_finset Wfin, hcoe, ← Nat.card_coe_set_eq]
      exact hWcard
    have hsub : If.bipartiteBelow (fun v W => v ∈ W) W ⊆ Wfin.erase 1 := by
      intro v hv
      rw [Finset.mem_bipartiteBelow, Finset.mem_filter] at hv
      obtain ⟨⟨-, hvI⟩, hvW⟩ := hv
      have hv1 : v ≠ 1 := by
        intro h
        have h2 := hvI.2
        rw [h, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      rw [Finset.mem_erase]
      exact ⟨hv1, by simp [Wfin, hvW]⟩
    calc (If.bipartiteBelow (fun v W => v ∈ W) W).card
        ≤ (Wfin.erase 1).card := Finset.card_le_card hsub
      _ = Wfin.card - 1 := Finset.card_erase_of_mem (by simp [Wfin])
      _ = 7 := by rw [hWfin_card]
  have hle : If.card * Ws.length ≤ 7 * Wf.card := by
    have h := Finset.card_nsmul_le_card_nsmul (R := ℕ)
      (r := fun (v : Γ) (W : Subgroup Γ) => v ∈ W) (s := If) (t := Wf)
      (m := Ws.length) (n := 7) hm hn
    change If.card * Ws.length ≤ Wf.card * 7 at h
    rw [mul_comm Wf.card 7] at h
    exact h
  have hmain : Nat.card (invols L) * Ws.length ≤ 7 * Wf.card := by
    rw [← hIfcard]
    exact hle
  calc Nat.card (normIn L E) * (Nat.card (invols L) * Ws.length)
      ≤ Nat.card (normIn L E) * (7 * Wf.card) := Nat.mul_le_mul_left _ hmain
    _ = 7 * Nat.card L := by
        rw [mul_comm (Nat.card (normIn L E)) (7 * Wf.card), mul_assoc, hstab]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
