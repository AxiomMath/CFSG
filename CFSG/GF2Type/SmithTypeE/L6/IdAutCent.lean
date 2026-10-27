module

public import CFSG.GF2Type.SmithTypeE.LMod.Aut
public import CFSG.GF2Type.SmithTypeE.LMod.UaBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.GF2Type.SmithTypeE.LMod CFSG.SmithL6 Matrix
open scoped MatrixGroups

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

theorem ac_single_ne_zero (c : Fin 6) : (Pi.single c (1 : ZMod 2) : Fin 6 → ZMod 2) ≠ 0 :=
  fun h => by
    have := congrFun h c
    simp at this

theorem ac_single_apply_of_ne {c j : Fin 6} (h : j.val ≠ c.val) :
    (Pi.single c (1 : ZMod 2) : Fin 6 → ZMod 2) j = 0 := by
  rw [Pi.single_apply, if_neg]
  intro e
  exact h (congrArg Fin.val e)

theorem ac_dot_single {a b : Fin 6} (h : b.val ≠ a.val) :
    (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) ⬝ᵥ Pi.single b (1 : ZMod 2) = 0 := by
  rw [dotProduct_single, mul_one, ac_single_apply_of_ne h]

section Tv


theorem ac_exists_pt {v φ : Fin 6 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hd : φ ⬝ᵥ v = 0) :
    ∃ p : Fin 1953, tvVec (p : ℕ) = v ∧ tvForm (p : ℕ) = φ := by
  obtain ⟨k, hk⟩ := tvToSet_surjective (⟨(v, φ), hv, hφ, hd⟩ : TvSet)
  exact ⟨k, congrArg (fun q => q.1.1) hk, congrArg (fun q => q.1.2) hk⟩

end Tv

theorem ac_mask0 : maskArr[0]! = 255 := by
  have h : maskArr[0]! = wMask 0 := by simp [maskArr, getElem!_pos]
  rw [h]
  decide +kernel

theorem ac_annArr0 : annArr[0]! = annMaskOf 7 6 5 := by
  have hw : wB 0 = (7, 6, 5) := by decide +kernel
  have h : annArr[0]! = annMaskOf (wB 0).1 (wB 0).2.1 (wB 0).2.2 := by
    simp [annArr, getElem!_pos]
  rw [h, hw]

theorem ac_ann0_testBit {φ : ℕ} (hφ : φ < 64) :
    (annMaskOf 7 6 5).testBit φ = decide (φ % 8 = 0) := by
  have key : ∀ n < 64, (annMaskOf 7 6 5).testBit n = decide (n % 8 = 0) := by
    decide +kernel
  exact key φ hφ

theorem ac_255_testBit {v : ℕ} (hv : v < 64) : (255 : ℕ).testBit v = decide (v < 8) := by
  have key : ∀ n < 64, (255 : ℕ).testBit n = decide (n < 8) := by decide +kernel
  exact key v hv

theorem ac_inPlane0 {a : ℕ} (h1 : (tvPair a).1 < 64) (h2 : (tvPair a).2 < 64) :
    inPlane 0 a = true ↔ (tvPair a).1 < 8 ∧ (tvPair a).2 % 8 = 0 := by
  dsimp only [inPlane]
  rw [ac_mask0, ac_annArr0, ac_255_testBit h1, ac_ann0_testBit h2]
  simp

section Plane0


theorem ac_mem_wPlane0_iff (p : Fin 1953) : p ∈ wPlane 0 ↔
    (∀ j : Fin 6, 3 ≤ j.val → tvVec (p : ℕ) j = 0) ∧
      (∀ j : Fin 6, j.val < 3 → tvForm (p : ℕ) j = 0) := by
  obtain ⟨h1, h2, -⟩ := tvListFacts.entry (p : ℕ) p.2
  rw [mem_wPlane, ac_inPlane0 h1 h2]
  have hv : ∀ n < 64, ((∀ j : Fin 6, 3 ≤ j.val → dec6 n j = 0) ↔ n < 8) := by
    decide +kernel
  have hφ : ∀ n < 64, ((∀ j : Fin 6, j.val < 3 → dec6 n j = 0) ↔ n % 8 = 0) := by
    decide +kernel
  exact and_congr (hv _ h1).symm (hφ _ h2).symm

theorem ac_mem_wPlane0_of {p : Fin 1953} {v φ : Fin 6 → ZMod 2} (hv : tvVec (p : ℕ) = v)
    (hφ : tvForm (p : ℕ) = φ) (h1 : ∀ j : Fin 6, 3 ≤ j.val → v j = 0)
    (h2 : ∀ j : Fin 6, j.val < 3 → φ j = 0) : p ∈ wPlane 0 := by
  rw [ac_mem_wPlane0_iff]
  exact ⟨fun j hj => by rw [hv]; exact h1 j hj, fun j hj => by rw [hφ]; exact h2 j hj⟩

end Plane0

def acS : Set (SL(6, ZMod 2)) :=
  {B | ∀ r c : Fin 6, (c.val < 3 ∨ 3 ≤ r.val) →
    (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c = (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c}

theorem mem_acS {B : SL(6, ZMod 2)} : B ∈ acS ↔ ∀ r c : Fin 6, (c.val < 3 ∨ 3 ≤ r.val) →
    (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c = (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c :=
  Iff.rfl

def acBlk (B : SL(6, ZMod 2)) : Fin 3 → Fin 3 → ZMod 2 :=
  fun r c => (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) ⟨r.val, by have := r.isLt; omega⟩
    ⟨c.val + 3, by have := c.isLt; omega⟩

theorem ac_acBlk_injOn : Set.InjOn acBlk acS := by
  intro A hA B hB hAB
  rw [mem_acS] at hA hB
  apply Subtype.ext
  ext r c
  by_cases hrc : c.val < 3 ∨ 3 ≤ r.val
  · rw [hA r c hrc, hB r c hrc]
  · have hc : 3 ≤ c.val := by omega
    have hr : r.val < 3 := by omega
    have hc6 := c.isLt
    have key := congrFun (congrFun hAB ⟨r.val, by omega⟩) ⟨c.val - 3, by omega⟩
    simp only [acBlk] at key
    have hr' : (⟨r.val, by omega⟩ : Fin 6) = r := Fin.ext rfl
    have hc' : (⟨c.val - 3 + 3, by omega⟩ : Fin 6) = c :=
      Fin.ext (show c.val - 3 + 3 = c.val by omega)
    rw [hr', hc'] at key
    exact key

theorem ac_card_acS : acS.ncard ≤ 2 ^ 9 := by
  have h := Set.ncard_le_ncard_of_injOn acBlk (fun _ _ => Set.mem_univ _) ac_acBlk_injOn
    Set.finite_univ
  rw [Set.ncard_univ] at h
  have hc : Nat.card (Fin 3 → Fin 3 → ZMod 2) = 2 ^ 9 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rw [hc] at h
  exact h

section Cent0


theorem ac_mem_acS_of_fix {B : SL(6, ZMod 2)} (h : ∀ p ∈ wPlane 0, actPerm B p = p) :
    B ∈ acS := by
  rw [mem_acS]
  intro r c hrc
  rcases hrc with hc | hr
  · obtain ⟨p, hp1, hp2⟩ := ac_exists_pt (ac_single_ne_zero c) (ac_single_ne_zero 3)
      (ac_dot_single (a := 3) (b := c) (by show c.val ≠ 3; omega))
    have hpW : p ∈ wPlane 0 := ac_mem_wPlane0_of hp1 hp2
      (fun j hj => ac_single_apply_of_ne (by omega))
      (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 3; omega))
    have hv := congrArg (fun q : Fin 1953 => tvVec (q : ℕ)) (h p hpW)
    simp only [tvVec_actPerm, hp1] at hv
    have e := congrFun hv r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using e
  · obtain ⟨p, hp1, hp2⟩ := ac_exists_pt (ac_single_ne_zero 0) (ac_single_ne_zero r)
      (ac_dot_single (a := r) (b := 0) (by show (0 : ℕ) ≠ r.val; omega))
    have hpW : p ∈ wPlane 0 := ac_mem_wPlane0_of hp1 hp2
      (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 0; omega))
      (fun j hj => ac_single_apply_of_ne (by omega))
    have hf := congrArg (fun q : Fin 1953 => tvForm (q : ℕ)) (h p hpW)
    simp only [tvForm_actPerm, hp2] at hf
    have hB : (Pi.single r (1 : ZMod 2) : Fin 6 → ZMod 2) ᵥ* (B : Matrix (Fin 6) (Fin 6) (ZMod 2))
        = Pi.single r (1 : ZMod 2) := by
      calc (Pi.single r (1 : ZMod 2) : Fin 6 → ZMod 2) ᵥ* (B : Matrix (Fin 6) (Fin 6) (ZMod 2))
          = (Pi.single r (1 : ZMod 2) ᵥ* ((B⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))
              ᵥ* (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by rw [hf]
        _ = Pi.single r (1 : ZMod 2) ᵥ*
              (((B⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
                (B : Matrix (Fin 6) (Fin 6) (ZMod 2))) := by rw [vecMul_vecMul]
        _ = Pi.single r (1 : ZMod 2) := by rw [coe_inv_mul B, vecMul_one]
    have e := congrFun hB c
    have key : (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c = if c = r then 1 else 0 := by
      simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using e
    rcases eq_or_ne r c with h' | h'
    · subst h'
      simpa [Matrix.one_apply] using key
    · have h'' : c ≠ r := fun h0 => h' h0.symm
      simp [Matrix.one_apply, key, h', h'']

theorem ac_outer (A : SL(6, ZMod 2)) (h : ∀ p ∈ wPlane 0, (actPerm A * swapPerm) p = p) :
    False := by
  obtain ⟨p₁, hv₁, hf₁⟩ := ac_exists_pt (ac_single_ne_zero 0) (ac_single_ne_zero 3)
    (ac_dot_single (a := 3) (b := 0) (by decide))
  obtain ⟨p₂, hv₂, hf₂⟩ := ac_exists_pt (ac_single_ne_zero 1) (ac_single_ne_zero 3)
    (ac_dot_single (a := 3) (b := 1) (by decide))
  have hp₁ : p₁ ∈ wPlane 0 := ac_mem_wPlane0_of hv₁ hf₁
    (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 0; omega))
    (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 3; omega))
  have hp₂ : p₂ ∈ wPlane 0 := ac_mem_wPlane0_of hv₂ hf₂
    (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 1; omega))
    (fun j hj => ac_single_apply_of_ne (by show j.val ≠ 3; omega))
  have e₁ := congrArg (fun q : Fin 1953 => tvVec (q : ℕ)) (h p₁ hp₁)
  have e₂ := congrArg (fun q : Fin 1953 => tvVec (q : ℕ)) (h p₂ hp₂)
  simp only [Equiv.Perm.mul_apply, swapPerm_apply, tvVec_actPerm, tvVec_swapIdx, hf₁, hv₁] at e₁
  simp only [Equiv.Perm.mul_apply, swapPerm_apply, tvVec_actPerm, tvVec_swapIdx, hf₂, hv₂] at e₂
  have e := congrFun (e₁.symm.trans e₂) 0
  simp at e

end Cent0

section Zero0


theorem ac_actPerm_mem_UA_zero {A : SL(6, ZMod 2)} (h : ∀ p ∈ wPlane 0, actPerm A p = p) :
    actPerm A ∈ UA 0 := by
  have hUA : (UA 0 : Set (Equiv.Perm (Fin 1953))).ncard = 2 ^ 9 := by
    rw [← Nat.card_coe_set_eq]
    exact card_UA_zero
  have hsub : (UA 0 : Set (Equiv.Perm (Fin 1953))) ⊆ actPerm '' acS := by
    intro u hu
    obtain ⟨B, rfl⟩ := exists_actPerm_eq (UA_le_T6 hu)
    exact ⟨B, ac_mem_acS_of_fix fun p hp => UA_apply_of_mem_zero hu hp, rfl⟩
  have hle : (actPerm '' acS).ncard ≤ (UA 0 : Set (Equiv.Perm (Fin 1953))).ncard := by
    rw [Set.ncard_image_of_injective _ actPerm_injective, hUA]
    exact ac_card_acS
  have heq := Set.eq_of_subset_of_ncard_le hsub hle
  have hmem : actPerm A ∈ (UA 0 : Set (Equiv.Perm (Fin 1953))) := by
    rw [heq]
    exact ⟨A, ac_mem_acS_of_fix h, rfl⟩
  exact hmem

theorem ac_plane0 (β : MulAut T6) (hfix : ∀ p ∈ wPlane 0, autPerm β p = p) :
    autPerm β ∈ UA 0 := by
  obtain ⟨A, hA | hA⟩ := autPerm_form β
  · rw [hA]
    exact ac_actPerm_mem_UA_zero fun p hp => by rw [← hA]; exact hfix p hp
  · exact (ac_outer A fun p hp => by rw [← hA]; exact hfix p hp).elim

end Zero0

section Cent


theorem autPerm_mem_UA_of_commute {i : ℕ} (hi : i < 1395) (α : MulAut T6)
    (h : ∀ u ∈ UA i, u * autPerm α = autPerm α * u) : autPerm α ∈ UA i := by
  have hfix : ∀ p ∈ wPlane i, autPerm α p = p := by
    intro p hp
    have h1 := h (tvP p) (tvP_mem_UA hp)
    have h2 := isTvAut_autPerm α p
    have h3 : autPerm α * tvP p * (autPerm α)⁻¹ = tvP p := by
      rw [← h1, mul_inv_cancel_right]
    exact tvP_injective (h2.symm.trans h3)
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  obtain ⟨β, hβ⟩ : ∃ β : MulAut T6,
      β = (MulAut.conj (⟨x, hx⟩ : T6))⁻¹ * α * MulAut.conj (⟨x, hx⟩ : T6) := ⟨_, rfl⟩
  have hperm : autPerm β = x⁻¹ * autPerm α * x := by
    rw [hβ, map_mul, map_mul, map_inv, autPerm_conj]
  have hfix' : ∀ p ∈ wPlane 0, autPerm β p = p := by
    intro p hp
    have hxp : x p ∈ wPlane i := by
      rw [← hW]
      exact Set.mem_image_of_mem _ hp
    rw [hperm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hfix _ hxp]
    simp
  exact (mem_UA_iff_conj hx hW).2 (by rw [← hperm]; exact ac_plane0 β hfix')

end Cent

end CFSG.GF2Type.SmithTypeE.L6

