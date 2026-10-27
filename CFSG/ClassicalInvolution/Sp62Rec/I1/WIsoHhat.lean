module

public import Certificates.Certificate550101
public import CFSG.ClassicalInvolution.Solomon73.YamakiModel
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
import CFSG.ClassicalInvolution.Solomon73.YamakiTables

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open CFSG.CosetTable CFSG.ClassicalInvolution.Solomon73.Yamaki Matrix Equiv
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.Open

@[expose] def hwords : Fin 10 → List (Fin 12) :=
  ![[5, 3, 0], [5, 4], [5, 1, 0], [3, 1, 0], [4, 0], [5, 6, 10, 11, 10, 6],
    [5, 3, 2, 3, 0, 10, 11, 10, 2], [8, 5], [11, 5, 3, 6, 2, 1], [5, 4, 0, 10, 11, 10]]

@[expose] def hMat (i : Fin 10) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  wordMat yamakiMat (posW (hwords i))

set_option maxRecDepth 100000 in
theorem hMat_mul_self : ∀ i, hMat i * hMat i = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hMat_rels : ∀ r ∈ relsW (), halfOK hMat r = true := by decide +kernel

@[expose] def ywords : Fin 12 → List (Fin 10) :=
  ![[3, 2, 0], [3, 9, 2, 1, 0, 9, 3, 0], [9, 7, 8, 9, 6, 5, 7, 6, 8, 7, 9],
    [3, 9, 2, 1, 0, 9, 3, 2], [4, 3, 2, 0], [3, 9, 2, 1, 0, 9],
    [4, 3, 8, 9, 7, 8, 9, 0, 6, 5, 7, 6, 8, 7, 9, 8], [9, 3, 8, 2, 7, 0, 6, 7, 8, 9],
    [3, 9, 2, 1, 0, 9, 7], [], [3, 9, 2, 1, 0, 9, 3, 8, 2, 5, 7, 8, 9, 0, 6, 5, 7, 6, 8, 7],
    [4, 3, 5, 0, 6, 5]]

set_option maxRecDepth 100000 in
theorem yamaki_in_images : ∀ j : Fin 12, (j.val ≤ 8 ∨ j = 10 ∨ j = 11) →
    yamakiMat j = ((ywords j).map hMat).prod := by decide +kernel

set_option maxRecDepth 100000 in
theorem alpha_eq_prod : hMat 0 * hMat 1 * hMat 2 * hMat 3 * hMat 4 = yamakiMat 5 := by
  decide +kernel

abbrev WPG : Type := PG 10 (relsW ())

theorem finite_card_WPG :
    Finite WPG ∧ Nat.card WPG ≤ 23040 :=
  Certificates.certificate550101

@[expose] def wgen : Fin 10 → Wr 6 :=
  ![⟨v6 [0, 5], 1⟩, ⟨v6 [1, 5], 1⟩, ⟨v6 [2, 5], 1⟩, ⟨v6 [3, 5], 1⟩, ⟨v6 [4, 5], 1⟩,
    ⟨0, swap 0 1⟩, ⟨0, swap 1 2⟩, ⟨0, swap 2 3⟩, ⟨0, swap 3 4⟩, ⟨0, swap 4 5⟩]

theorem wgen_mul_self : ∀ i, wgen i * wgen i = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem wgen_rels : ∀ r ∈ relsW (), (r.map fun l => wgen l.1).prod = 1 := by decide +kernel

theorem wgen_wsum : ∀ i, wsum (wgen i) = 0 := by decide

@[expose] def wgen' (i : Fin 10) : ↥Wsub := ⟨wgen i, wgen_wsum i⟩

theorem wgen'_mul_self : ∀ i, wgen' i * wgen' i = 1 := fun i => Subtype.ext (wgen_mul_self i)

theorem lift_wgen'_rel : ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ (relsW ()).map FreeGroup.mk},
    FreeGroup.lift wgen' r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [lift_mk_eq_prod wgen'_mul_self]
  apply Subtype.ext
  have h1 := map_list_prod Wsub.subtype (w.map fun l => wgen' l.1)
  rw [List.map_map] at h1
  exact h1.trans (wgen_rels w hw)

@[expose] noncomputable def homW : WPG →* ↥Wsub := PresentedGroup.toGroup lift_wgen'_rel

theorem homW_of (i : Fin 10) : homW (PresentedGroup.of i) = wgen' i := PresentedGroup.toGroup.of _

@[expose] def c6 (i : Fin 5) : Fin 6 := ⟨i.val, by omega⟩
@[expose] def c10 (i : Fin 5) : Fin 10 := ⟨i.val, by omega⟩

set_option maxRecDepth 100000 in
theorem even_vec_prod : ∀ v : Fin 6 → ZMod 2, wsum (⟨v, 1⟩ : Wr 6) = 0 →
    (⟨v, 1⟩ : Wr 6) =
      (((List.finRange 5).filter (fun i => v (c6 i) = 1)).map (fun i => wgen (c10 i))).prod := by
  decide +kernel

theorem homW_surjective : Function.Surjective homW := by
  intro a
  set H : Subgroup (Wr 6) := homW.range.map Wsub.subtype with hH
  have hgen : ∀ i, wgen i ∈ H := fun i =>
    ⟨wgen' i, ⟨PresentedGroup.of i, homW_of i⟩, rfl⟩
  have hvec : ∀ v : Fin 6 → ZMod 2, wsum (⟨v, 1⟩ : Wr 6) = 0 → (⟨v, 1⟩ : Wr 6) ∈ H := by
    intro v hv
    rw [even_vec_prod v hv]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hgen _
  have hperm : ∀ σ : Perm (Fin 6), (⟨0, σ⟩ : Wr 6) ∈ H := by
    intro σ
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hgen 5
      · exact hgen 6
      · exact hgen 7
      · exact hgen 8
      · exact hgen 9
    | one => exact H.one_mem
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      exact this
  have hmem : (a : Wr 6) ∈ H := by
    have : (a : Wr 6) = ⟨(a : Wr 6).vec, 1⟩ * ⟨0, (a : Wr 6).perm⟩ :=
      Wr.ext (funext fun i => by simp [mul_vec]) (by simp [mul_perm])
    rw [this]
    exact H.mul_mem (hvec _ a.2) (hperm _)
  obtain ⟨b, hb, hba⟩ := hmem
  have hba' : b = a := Subtype.ext hba
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, hx.trans hba'⟩

section Hhat


@[expose] def hgen (i : Fin 10) : StatedSp 3 (ZMod 2) := ((hwords i).map yamakiSp).prod

theorem spMat_hgen (i : Fin 10) : spMat (hgen i) = hMat i := by
  unfold hgen hMat wordMat posW
  rw [map_list_prod, List.map_map, List.map_map]
  rfl

theorem hgen_mul_self : ∀ i, hgen i * hgen i = 1 := fun i =>
  spMat_injective (by rw [map_mul, map_one, spMat_hgen]; exact hMat_mul_self i)

theorem hletters : ∀ i, ∀ j ∈ hwords i, j.val ≤ 8 ∨ j = 10 ∨ j = 11 := by decide

theorem hgen_mem : ∀ i, hgen i ∈ Hhat := by
  intro i
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact yamakiSp_mem_Hhat (hletters i j hj)

@[expose] def hgen' (i : Fin 10) : ↥Hhat := ⟨hgen i, hgen_mem i⟩

theorem hgen'_mul_self : ∀ i, hgen' i * hgen' i = 1 := fun i => Subtype.ext (hgen_mul_self i)

theorem lift_hgen'_rel : ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ (relsW ()).map FreeGroup.mk},
    FreeGroup.lift hgen' r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [lift_mk_eq_prod hgen'_mul_self]
  apply Subtype.ext
  apply spMat_injective
  have h1 := map_list_prod (spMat.comp Hhat.subtype) (w.map fun l => hgen' l.1)
  rw [List.map_map] at h1
  have h2 : ((spMat.comp Hhat.subtype) ∘ fun l : Fin 10 × Bool => hgen' l.1) =
      fun l => hMat l.1 := funext fun l => spMat_hgen l.1
  rw [h2] at h1
  show (spMat.comp Hhat.subtype) ((w.map fun l => hgen' l.1).prod) = spMat 1
  rw [h1, map_one]
  exact wordMat_eq_one_of_halfOK hMat hMat_mul_self (hMat_rels w hw)

@[expose] noncomputable def homH : WPG →* ↥Hhat := PresentedGroup.toGroup lift_hgen'_rel

theorem homH_of (i : Fin 10) : homH (PresentedGroup.of i) = hgen' i := PresentedGroup.toGroup.of _

theorem yamakiSp_eq_prod (j : Fin 12) (hj : j.val ≤ 8 ∨ j = 10 ∨ j = 11) :
    yamakiSp j = ((ywords j).map hgen).prod := by
  apply spMat_injective
  rw [map_list_prod, List.map_map]
  have : (spMat ∘ hgen) = hMat := funext spMat_hgen
  rw [this]
  exact yamaki_in_images j hj

theorem homH_surjective : Function.Surjective homH := by
  intro h
  set H : Subgroup (StatedSp 3 (ZMod 2)) := homH.range.map Hhat.subtype with hH
  have hgenH : ∀ i, hgen i ∈ H := fun i => ⟨hgen' i, ⟨PresentedGroup.of i, homH_of i⟩, rfl⟩
  have hle : Hhat ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j.val ≤ 8 ∨ j = 10 ∨ j = 11 := by
      rcases hj with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rw [yamakiSp_eq_prod j hj']
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact hgenH _
  obtain ⟨b, hb, hbh⟩ := hle h.2
  have hba' : b = h := Subtype.ext hbh
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, hx.trans hba'⟩

end Hhat

section Iso


theorem homW_bijective : Function.Bijective homW := by
  haveI := finite_card_WPG.1
  exact homW_surjective.bijective_of_nat_card_le (by rw [card_Wsub]; exact finite_card_WPG.2)

theorem homH_bijective : Function.Bijective homH := by
  haveI := finite_card_WPG.1
  exact homH_surjective.bijective_of_nat_card_le (by rw [card_Hhat]; exact finite_card_WPG.2)

@[expose] noncomputable def ΘW : ↥Wsub ≃* ↥Hhat :=
  (MulEquiv.ofBijective homW homW_bijective).symm.trans (MulEquiv.ofBijective homH homH_bijective)

theorem ΘW_homW (x : WPG) : ΘW (homW x) = homH x := by
  have : (MulEquiv.ofBijective homW homW_bijective) x = homW x := rfl
  unfold ΘW
  rw [MulEquiv.trans_apply, ← this, MulEquiv.symm_apply_apply]
  rfl

theorem pi_eq_prod : (⟨allOnes 6, allOnes_mem_Wsub⟩ : ↥Wsub) =
    wgen' 0 * wgen' 1 * wgen' 2 * wgen' 3 * wgen' 4 := by
  apply Subtype.ext
  show allOnes 6 = wgen 0 * wgen 1 * wgen 2 * wgen 3 * wgen 4
  decide +kernel

theorem alpha_mem_Hhat' : alpha ∈ Hhat := yamakiSp_mem_Hhat (Or.inl (by decide))

theorem ΘW_pi : ΘW ⟨allOnes 6, allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat'⟩ := by
  have h1 : (⟨allOnes 6, allOnes_mem_Wsub⟩ : ↥Wsub) = homW (PresentedGroup.of 0 *
      PresentedGroup.of 1 * PresentedGroup.of 2 * PresentedGroup.of 3 * PresentedGroup.of 4) := by
    rw [pi_eq_prod]; simp only [map_mul, homW_of]
  rw [h1, ΘW_homW]
  apply Subtype.ext
  apply spMat_injective
  simp only [map_mul, homH_of]
  show spMat (hgen 0 * hgen 1 * hgen 2 * hgen 3 * hgen 4) = spMat (yamakiSp 5)
  rw [map_mul, map_mul, map_mul, map_mul, spMat_hgen, spMat_hgen, spMat_hgen, spMat_hgen,
    spMat_hgen]
  exact alpha_eq_prod

theorem exists_iso_Wsub_Hhat :
    ∃ Θ : ↥Wsub ≃* ↥Hhat, Θ ⟨allOnes 6, allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat'⟩ :=
  ⟨ΘW, ΘW_pi⟩

end Iso

end CFSG.ClassicalInvolution.Sp62Rec.I1
