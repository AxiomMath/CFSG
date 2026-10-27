module

public import CFSG.LargeExtraspecial.AS62Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Idx2

public section

namespace CFSG.LargeExtraspecial.AS62

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 U42F431 CFSG.CosetTable

@[expose] def tSylWords : List (List (Fin 4 × Bool)) :=
  [[(1, true), (3, false), (2, true), (1, true), (3, true), (2, true)],
   [(1, true), (2, true), (1, true), (3, true), (2, true), (3, false)],
   [(1, true)],
   [(0, true), (1, true), (3, false), (2, true), (1, true), (2, true), (3, true)],
   [(0, true), (1, true), (3, true), (2, true), (1, true), (2, true), (3, false)]]

theorem evalLs_tSylWords : ∀ k < 5,
    evalLs (fun a : Fin 4 × Bool => uLet (a.1.val, a.2)) (tSylWords.getD k []) =
      evalW (TgW.getD k []) := by
  decide +kernel

theorem coe_ΨB_mk (w : List (Fin 4 × Bool)) :
    (((ΨB (PresentedGroup.mk _ (FreeGroup.mk w)) : ↥B0) : Y) : P45) =
      FreeGroup.lift (fun i : Fin 4 => (genU i.val : P45)) (FreeGroup.mk w) := by
  rw [ΨB_mk]
  exact hom_freeLift (Xs.subtype.comp B0.subtype) genB0 (FreeGroup.mk w)

theorem gTY_mem_range_ΨB {k : ℕ} (hk : k < 5) : gTY k ∈ ΨB.range.map B0.subtype := by
  refine Subgroup.mem_map.2 ⟨ΨB (PresentedGroup.mk _ (FreeGroup.mk (tSylWords.getD k []))),
    MonoidHom.mem_range.2 ⟨_, rfl⟩, Subtype.ext ?_⟩
  change (((ΨB _ : ↥B0) : Y) : P45) = wordP (TgW.getD k [])
  rw [coe_ΨB_mk]
  have h := repL_evalLs (fun i : Fin 4 => (genU i.val : P45)) (fun a => uLet (a.1.val, a.2))
    (fun a => repL_uLet (Nat.lt_of_lt_of_le a.1.isLt (by norm_num)) a.2) (tSylWords.getD k [])
  rw [evalLs_tSylWords k hk] at h
  exact eq_of_repL h (repL_wordP _)

theorem T_le_range_ΨB : T ≤ ΨB.range.map B0.subtype := by
  rw [T, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact gTY_mem_range_ΨB k.isLt

theorem c3Y_mem_range_ΨB : c3Y ∈ ΨB.range.map B0.subtype :=
  Subgroup.mem_map.2
    ⟨ΨB (PresentedGroup.of 3), MonoidHom.mem_range.2 ⟨_, rfl⟩, by rw [ΨB_of]; rfl⟩

theorem surjective_of_le_range {α : Type*} [Group α] {P : Subgroup Y} (f : α →* ↥P)
    (h : P ≤ f.range.map P.subtype) : Function.Surjective f := by
  intro p
  obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.1 (h p.2)
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
  exact ⟨x, Subtype.ext hyp⟩

theorem ΨB_surjective :
    Function.Surjective ΨB := by
  have hK : T ⊔ Subgroup.zpowers c3Y ≤ ΨB.range.map B0.subtype :=
    sup_le T_le_range_ΨB ((Subgroup.zpowers_le).2 c3Y_mem_range_ΨB)
  have hcard : Nat.card B0 ≤ Nat.card (ΨB.range.map B0.subtype) := by
    rw [card_B0]
    exact card_K_ge.trans (Subgroup.card_le_of_le hK)
  exact surjective_of_le_range ΨB
    (Subgroup.eq_of_le_of_card_ge (Subgroup.map_subtype_le _) hcard).ge

theorem yU_notMem_B0 : yU ∉ B0 := fun h => yU_notMem_P2 (B0_le_P2 h)

theorem sU_notMem_B0 : sU ∉ B0 := fun h => sU_notMem_P1 (B0_le_P1 h)

theorem le_of_relIndex_prime {B R P : Subgroup Y} (hBR : B ≤ R) (hRP : R ≤ P)
    (hp : (B.relIndex P).Prime) {g : Y} (hg : g ∈ R) (hgB : g ∉ B) : P ≤ R := by
  have hmul := Subgroup.relIndex_mul_relIndex B R P hBR hRP
  rcases hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩ with h | h
  · exact absurd (Subgroup.relIndex_eq_one.1 h hg) hgB
  · rw [h] at hmul
    exact Subgroup.relIndex_eq_one.1
      (Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one _).symm))

theorem Ψ1_surjective :
    Function.Surjective Ψ1 := by
  have hBR : B0 ≤ Ψ1.range.map P1.subtype := by
    intro b hb
    obtain ⟨g, hg⟩ := ΨB_surjective ⟨b, hb⟩
    refine Subgroup.mem_map.2 ⟨Ψ1 (ι₁ g), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    rw [← MonoidHom.comp_apply Ψ1 ι₁, ← ψ_comm1, MonoidHom.comp_apply, hg]
    rfl
  have hy : yU ∈ Ψ1.range.map P1.subtype := Subgroup.mem_map.2
    ⟨Ψ1 (PresentedGroup.of 4), MonoidHom.mem_range.2 ⟨_, rfl⟩, by rw [Ψ1_of]; rfl⟩
  refine surjective_of_le_range Ψ1 (le_of_relIndex_prime hBR (Subgroup.map_subtype_le _) ?_ hy
    yU_notMem_B0)
  rw [relIndex_B0_P1]
  exact Nat.prime_three

theorem Ψ2_surjective :
    Function.Surjective Ψ2 := by
  have hBR : B0 ≤ Ψ2.range.map P2.subtype := by
    intro b hb
    obtain ⟨g, hg⟩ := ΨB_surjective ⟨b, hb⟩
    refine Subgroup.mem_map.2 ⟨Ψ2 (ι₂ g), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    rw [← MonoidHom.comp_apply Ψ2 ι₂, ← ψ_comm2, MonoidHom.comp_apply, hg]
    rfl
  have hs : sU ∈ Ψ2.range.map P2.subtype := Subgroup.mem_map.2
    ⟨Ψ2 (PresentedGroup.of 4), MonoidHom.mem_range.2 ⟨_, rfl⟩, by rw [Ψ2_of]; rfl⟩
  refine surjective_of_le_range Ψ2 (le_of_relIndex_prime hBR (Subgroup.map_subtype_le _) ?_ hs
    sU_notMem_B0)
  rw [relIndex_B0_P2]
  exact Nat.prime_five

end CFSG.LargeExtraspecial.AS62
