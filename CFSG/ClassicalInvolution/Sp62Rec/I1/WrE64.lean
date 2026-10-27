module

public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem card_Wr_six : Nat.card (Wr 6) = 46080 := by
  have h1 : Nat.card (Wr 6) = Nat.card ((Fin 6 → ZMod 2) × Perm (Fin 6)) :=
    Nat.card_congr
      { toFun := fun a => (a.vec, a.perm)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_perm, ZMod.card, Fintype.card_fin]
  decide

private def cyc3 : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 1 2, swap 1 2 * swap 2 3, swap 2 3 * swap 3 4, swap 3 4 * swap 4 5]

private theorem cyc3_perm : ∀ σ : Perm (Fin 6),
    (cyc3.all fun s => decide (σ * s = s * σ)) = true → σ = 1 := by
  decide +kernel

private theorem cyc3_vec : ∀ v : Fin 6 → ZMod 2,
    (cyc3.all fun s => decide ((⟨v, 1⟩ : Wr 6) * ⟨0, s⟩ = ⟨0, s⟩ * ⟨v, 1⟩)) = true →
      v = 0 ∨ v = fun _ => 1 := by
  decide +kernel

private theorem cyc3_mem : ∀ s ∈ cyc3, wsum (⟨0, s⟩ : Wr 6) = 0 ∧ Perm.sign s = 1 := by
  decide +kernel

theorem mem_piSub_of_centralizes {w : Wr 6} (h : ∀ x ∈ aeSub 6, w * x = x * w) :
    w ∈ piSub 6 := by
  have hperm : w.perm = 1 := by
    refine cyc3_perm _ ?_
    rw [List.all_eq_true]
    intro s hs
    rw [decide_eq_true_eq]
    exact congrArg Wr.perm (h ⟨0, s⟩ (mem_aeSub.mpr (cyc3_mem s hs)))
  have hw : w = ⟨w.vec, 1⟩ := Wr.ext rfl hperm
  have hv := cyc3_vec w.vec (by
    rw [List.all_eq_true]
    intro s hs
    rw [decide_eq_true_eq]
    rw [hw] at h
    exact h ⟨0, s⟩ (mem_aeSub.mpr (cyc3_mem s hs)))
  rcases hv with hv | hv
  · left
    rw [hw, hv]; rfl
  · right
    rw [hw, hv]; rfl

private def blkp : Fin 6 → Fin 6 := ![1, 0, 5, 4, 3, 2]

private def blkEps (c : Fin 6 → ZMod 2) : Wr 6 :=
  ⟨fun i => (if i = 0 ∨ i = 1 then c 0 else 0) + (if i = 2 ∨ i = 5 then c 1 else 0) +
      (if i = 3 ∨ i = 4 then c 2 else 0),
    (if c 3 = 1 then swap 0 1 else 1) * (if c 4 = 1 then swap 2 5 else 1) *
      (if c 5 = 1 then swap 3 4 else 1)⟩

private theorem blkEps_add : ∀ c c' : Fin 6 → ZMod 2, blkEps (c + c') = blkEps c * blkEps c' := by
  decide +kernel

private theorem blkEps_inj : ∀ c c' : Fin 6 → ZMod 2, blkEps c = blkEps c' → c = c' := by
  decide +kernel

private theorem blkEps_wsum : ∀ c : Fin 6 → ZMod 2, wsum (blkEps c) = 0 := by
  decide +kernel

private theorem blkEps_perm : ∀ c : Fin 6 → ZMod 2, ∀ i, (blkEps c).perm i = i ∨
    (blkEps c).perm i = blkp i := by
  decide +kernel

private theorem double_zero : ∀ c : Fin 6 → ZMod 2, c + c = 0 := by
  decide +kernel

private def blkHom : Multiplicative (Fin 6 → ZMod 2) →* Wr 6 :=
  MonoidHom.mk' (fun c => blkEps (Multiplicative.toAdd c)) fun a b => blkEps_add _ _

private theorem blkHom_injective : Function.Injective blkHom := fun a b h =>
  Multiplicative.toAdd.injective (blkEps_inj _ _ h)

def A64 : Subgroup (Wr 6) := blkHom.range

theorem A64_comm : ∀ a ∈ A64, ∀ b ∈ A64, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem A64_sq : ∀ a ∈ A64, a * a = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [← map_mul]
  have : x * x = 1 := Multiplicative.toAdd.injective (by
    show Multiplicative.toAdd x + Multiplicative.toAdd x = 0
    exact double_zero _)
  rw [this, map_one]

theorem card_A64 : Nat.card A64 = 64 := by
  rw [A64, ← Nat.card_congr (MonoidHom.ofInjective blkHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rw [show Fintype.card (Multiplicative (Fin 6 → ZMod 2)) = Fintype.card (Fin 6 → ZMod 2) from rfl,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem A64_le_Wsub : A64 ≤ Wsub := by
  rintro _ ⟨x, rfl⟩
  exact blkEps_wsum _

private def gensP : List (Perm (Fin 6)) := [swap 0 1, swap 2 5, swap 3 4]

private theorem gensP_perm : ∀ σ : Perm (Fin 6),
    (gensP.all fun τ => decide (σ * τ * σ⁻¹ * τ⁻¹ = 1)) = true → ∀ i, σ i = i ∨ σ i = blkp i := by
  decide +kernel

private theorem gensP_vec : ∀ σ : Perm (Fin 6), (∀ i, σ i = i ∨ σ i = blkp i) →
    ∀ v : Fin 6 → ZMod 2,
      (gensP.all fun τ => decide ((⟨v, σ⟩ : Wr 6) * ⟨0, τ⟩ * ⟨v, σ⟩⁻¹ * ⟨0, τ⟩⁻¹ = 1 ∨
        (⟨v, σ⟩ : Wr 6) * ⟨0, τ⟩ * ⟨v, σ⟩⁻¹ * ⟨0, τ⟩⁻¹ = allOnes 6)) = true →
      ∃ c, blkEps c = ⟨v, σ⟩ := by
  decide +kernel

private theorem gensP_ex : ∀ τ ∈ gensP, ∃ c, blkEps c = ⟨0, τ⟩ := by
  decide +kernel

private theorem gensP_mem : ∀ τ ∈ gensP, (⟨0, τ⟩ : Wr 6) ∈ A64 := by
  intro τ hτ
  obtain ⟨c, hc⟩ := gensP_ex τ hτ
  exact ⟨Multiplicative.ofAdd c, hc⟩

theorem mem_A64_of_comm_mod_pi {w : Wr 6}
    (h : ∀ a ∈ A64, w * a * w⁻¹ * a⁻¹ ∈ piSub 6) : w ∈ A64 := by
  have hperm : ∀ i, w.perm i = i ∨ w.perm i = blkp i := by
    refine gensP_perm _ ?_
    rw [List.all_eq_true]
    intro τ hτ
    rw [decide_eq_true_eq]
    rcases mem_piSub.mp (h _ (gensP_mem τ hτ)) with h2 | h2 <;> exact congrArg Wr.perm h2
  obtain ⟨c, hc⟩ := gensP_vec w.perm hperm w.vec (by
    rw [List.all_eq_true]
    intro τ hτ
    rw [decide_eq_true_eq]
    exact mem_piSub.mp (h _ (gensP_mem τ hτ)))
  exact ⟨Multiplicative.ofAdd c, hc⟩

private def blockPerm (σ : Perm (Fin 6)) : Bool :=
  gensP.all fun τ => decide (∀ i, (σ * τ * σ⁻¹) i = i ∨ (σ * τ * σ⁻¹) i = blkp i)

private theorem card_blockPerm : Fintype.card {σ : Perm (Fin 6) // blockPerm σ = true} = 48 := by
  decide +kernel

theorem card_normalizer_A64_le : Nat.card (Subgroup.normalizer (A64 : Set (Wr 6))) ≤ 3072 := by
  have h1 : ∀ w ∈ Subgroup.normalizer (A64 : Set (Wr 6)), blockPerm w.perm = true := by
    intro w hw
    unfold blockPerm
    rw [List.all_eq_true]
    intro τ hτ
    rw [decide_eq_true_eq]
    obtain ⟨x, hx⟩ := (Subgroup.mem_normalizer_iff.mp hw _).mp (gensP_mem τ hτ)
    have hp : w.perm * τ * w.perm⁻¹ = (blkEps (Multiplicative.toAdd x)).perm :=
      congrArg Wr.perm hx.symm
    rw [hp]
    exact blkEps_perm _
  have h2 : Nat.card {w : Wr 6 // blockPerm w.perm = true} = 3072 := by
    have : {w : Wr 6 // blockPerm w.perm = true} ≃ (Fin 6 → ZMod 2) ×
        {σ : Perm (Fin 6) // blockPerm σ = true} :=
      { toFun := fun w => (w.1.vec, ⟨w.1.perm, w.2⟩)
        invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr this, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 6 → ZMod 2),
      Nat.card_eq_fintype_card (α := {σ : Perm (Fin 6) // blockPerm σ = true}), card_blockPerm,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  rw [← h2]
  exact Nat.card_le_card_of_injective (fun w => ⟨w.1, h1 w.1 w.2⟩) (fun a b hab => Subtype.ext (Subtype.mk.inj hab))

end CFSG.ClassicalInvolution.Sp62Rec.I1
