module

public import CFSG.Certificates.Kernel.FixBoundK.FixMath
public import CFSG.Certificates.Kernel.FixBoundK.TrivSound
public import CFSG.Certificates.Kernel.Common.BvecLoop

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu

@[expose] def TrivCond : Prop :=
  ∀ x₁ : Nat, TrivSound.IsCw x₁ → x₁ = 0 ∨ x₁ = Triv.omK ∨
    (∀ x₂, TrivSound.IsCw x₂ → Triv.synK (x₁ &&& x₂) = 0 →
      x₂ = 0 ∨ x₂ = Triv.omK ∨ x₂ = x₁ ∨ x₂ = x₁ ^^^ Triv.omK ∨
        (∀ x₃, TrivSound.IsCw x₃ → Triv.synK (x₁ &&& x₃) = 0 → Triv.synK (x₂ &&& x₃) = 0 →
          x₃ = 0 ∨ x₃ = Triv.omK ∨ x₃ = x₁ ∨ x₃ = x₁ ^^^ Triv.omK ∨ x₃ = x₂ ∨
            x₃ = x₂ ^^^ Triv.omK ∨ x₃ = x₁ ^^^ x₂ ∨ x₃ = x₁ ^^^ x₂ ^^^ Triv.omK))

theorem synK_zero_iff (x : Nat) : Triv.synK x = 0 ↔ bvec 24 x ∈ C := by
  rw [TrivSound.synK_eq, ← synS_eq]
  exact synS_eq_zero_iff x

theorem bvec_trivOm : bvec 24 Triv.omK = Ω := bvec_omK

theorem exists_mask (y : C) : ∃ n, TrivSound.IsCw n ∧ bvec 24 n = (y : Fin 24 → ZMod 2) := by
  obtain ⟨n, hn, e⟩ := CFSG.KC.BvecLoop.exists_bvec 24 (y : Fin 24 → ZMod 2)
  refine ⟨n, ⟨hn, (synK_zero_iff n).2 ?_⟩, e⟩
  rw [e]
  exact y.2

theorem synK_and_iff (a b : Nat) :
    Triv.synK (a &&& b) = 0 ↔ bvec 24 a * bvec 24 b ∈ C := by
  rw [synK_zero_iff, bvec_and]

theorem natCard_sub' (V : Submodule (ZMod 2) C) : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]

theorem finrank_le_three (ht : TrivCond) {Y : Submodule (ZMod 2) C} (hΩ : ΩC ∈ Y)
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, (y : Fin 24 → ZMod 2) * (y' : Fin 24 → ZMod 2) ∈ C) :
    Module.finrank (ZMod 2) Y ≤ 3 := by
  classical
  by_contra hle
  have h4 : 4 ≤ Module.finrank (ZMod 2) Y := by omega
  have hspan1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({ΩC} : Set C)) ≤ 1 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := C) ({ΩC} : Set C)
    have hc : ({ΩC} : Set C).toFinset.card ≤ 1 := by
      rw [Set.toFinset_singleton]
      simp
    omega
  have hy1 : ∃ y1 : C, y1 ∈ Y ∧ y1 ∉ Submodule.span (ZMod 2) ({ΩC} : Set C) := by
    by_contra h
    have hle' : Y ≤ Submodule.span (ZMod 2) ({ΩC} : Set C) := by
      intro y hy
      by_contra hyS
      exact h ⟨y, hy, hyS⟩
    have hmono := Submodule.finrank_mono hle'
    omega
  obtain ⟨y1, hy1Y, hy1not⟩ := hy1
  have hspan2 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({ΩC, y1} : Set C)) ≤ 2 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := C) ({ΩC, y1} : Set C)
    have hc : ({ΩC, y1} : Set C).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      simpa using Finset.card_insert_le (ΩC) ({y1} : Finset C)
    omega
  have hy2 : ∃ y2 : C, y2 ∈ Y ∧ y2 ∉ Submodule.span (ZMod 2) ({ΩC, y1} : Set C) := by
    by_contra h
    have hle' : Y ≤ Submodule.span (ZMod 2) ({ΩC, y1} : Set C) := by
      intro y hy
      by_contra hyS
      exact h ⟨y, hy, hyS⟩
    have hmono := Submodule.finrank_mono hle'
    omega
  obtain ⟨y2, hy2Y, hy2not⟩ := hy2
  have hspan3 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({ΩC, y1, y2} : Set C)) ≤ 3 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := C) ({ΩC, y1, y2} : Set C)
    have hc : ({ΩC, y1, y2} : Set C).toFinset.card ≤ 3 := by
      rw [Set.toFinset_insert, Set.toFinset_insert, Set.toFinset_singleton]
      have h1 := Finset.card_insert_le (ΩC) (insert y1 ({y2} : Finset C))
      have h2 := Finset.card_insert_le (y1) ({y2} : Finset C)
      have h3 : ({y2} : Finset C).card = 1 := Finset.card_singleton y2
      omega
    omega
  have hy3 : ∃ y3 : C, y3 ∈ Y ∧ y3 ∉ Submodule.span (ZMod 2) ({ΩC, y1, y2} : Set C) := by
    by_contra h
    have hle' : Y ≤ Submodule.span (ZMod 2) ({ΩC, y1, y2} : Set C) := by
      intro y hy
      by_contra hyS
      exact h ⟨y, hy, hyS⟩
    have hmono := Submodule.finrank_mono hle'
    omega
  obtain ⟨y3, hy3Y, hy3not⟩ := hy3
  obtain ⟨n1, hn1, hv1⟩ := exists_mask y1
  obtain ⟨n2, hn2, hv2⟩ := exists_mask y2
  obtain ⟨n3, hn3, hv3⟩ := exists_mask y3
  have hc12 : Triv.synK (n1 &&& n2) = 0 := by
    rw [synK_and_iff, hv1, hv2]
    exact hY y1 hy1Y y2 hy2Y
  have hc13 : Triv.synK (n1 &&& n3) = 0 := by
    rw [synK_and_iff, hv1, hv3]
    exact hY y1 hy1Y y3 hy3Y
  have hc23 : Triv.synK (n2 &&& n3) = 0 := by
    rw [synK_and_iff, hv2, hv3]
    exact hY y2 hy2Y y3 hy3Y
  set V := Submodule.span (ZMod 2) ({ΩC, y1, y2} : Set C) with hV
  have hΩspan1 : ΩC ∈ Submodule.span (ZMod 2) ({ΩC} : Set C) :=
    Submodule.subset_span (by simp)
  have hΩspan2 : ΩC ∈ Submodule.span (ZMod 2) ({ΩC, y1} : Set C) :=
    Submodule.subset_span (by simp)
  have hy1span2 : y1 ∈ Submodule.span (ZMod 2) ({ΩC, y1} : Set C) :=
    Submodule.subset_span (by simp)
  have hy1span : y1 ∈ V := Submodule.subset_span (by simp)
  have hy2span : y2 ∈ V := Submodule.subset_span (by simp)
  have hΩspan : ΩC ∈ V := Submodule.subset_span (by simp)
  have hcomb : ∀ (y : C) (a b c : ZMod 2), (y : Fin 24 → ZMod 2) =
      a • Ω + b • (y1 : Fin 24 → ZMod 2) + c • (y2 : Fin 24 → ZMod 2) → y ∈ V := by
    intro y a b c hy
    have e : y = a • ΩC + b • y1 + c • y2 := by
      apply Subtype.ext
      rw [hy]
      rfl
    rw [e]
    exact V.add_mem (V.add_mem (V.smul_mem a hΩspan) (V.smul_mem b hy1span))
      (V.smul_mem c hy2span)
  rcases ht n1 hn1 with h10 | h1N | hrest
  · apply hy1not
    have hy : y1 = 0 := by
      apply Subtype.ext
      rw [← hv1, h10, bvec_zero]
      exact (Submodule.coe_zero (p := C)).symm
    rw [hy]
    exact Submodule.zero_mem _
  · apply hy1not
    have hy : y1 = ΩC := by
      apply Subtype.ext
      rw [← hv1, h1N, bvec_trivOm]
      rfl
    rw [hy]
    exact hΩspan1
  · rcases hrest n2 hn2 hc12 with h20 | h2N | h21 | h2x | hrest3
    · apply hy2not
      have hy : y2 = 0 := by
        apply Subtype.ext
        rw [← hv2, h20, bvec_zero]
        exact (Submodule.coe_zero (p := C)).symm
      rw [hy]
      exact Submodule.zero_mem _
    · apply hy2not
      have hy : y2 = ΩC := by
        apply Subtype.ext
        rw [← hv2, h2N, bvec_trivOm]
        rfl
      rw [hy]
      exact hΩspan2
    · apply hy2not
      have hy : y2 = y1 := by
        apply Subtype.ext
        rw [← hv2, h21, hv1]
      rw [hy]
      exact hy1span2
    · apply hy2not
      have hy : y2 = y1 + ΩC := by
        apply Subtype.ext
        rw [Submodule.coe_add, ← hv2, h2x, bvec_xor, hv1, bvec_trivOm]
        rfl
      rw [hy]
      exact Submodule.add_mem (p := Submodule.span (ZMod 2) ({ΩC, y1} : Set C))
        hy1span2 hΩspan2
    · apply hy3not
      rcases hrest3 n3 hn3 hc13 hc23 with h | h | h | h | h | h | h | h
      · exact hcomb y3 0 0 0 (by rw [← hv3, h, bvec_zero]; module)
      · exact hcomb y3 1 0 0 (by rw [← hv3, h, bvec_trivOm]; module)
      · exact hcomb y3 0 1 0 (by rw [← hv3, h, hv1]; module)
      · exact hcomb y3 1 1 0 (by rw [← hv3, h, bvec_xor, hv1, bvec_trivOm]; module)
      · exact hcomb y3 0 0 1 (by rw [← hv3, h, hv2]; module)
      · exact hcomb y3 1 0 1 (by rw [← hv3, h, bvec_xor, hv2, bvec_trivOm]; module)
      · exact hcomb y3 0 1 1 (by rw [← hv3, h, bvec_xor, hv1, hv2]; module)
      · exact hcomb y3 1 1 1 (by rw [← hv3, h, bvec_xor, bvec_xor, hv1, hv2, bvec_trivOm]; module)

theorem fixBoundAt_bot (ht : TrivCond) : FixBoundAt (⊥ : Subgroup AutPerm) := by
  classical
  intro X hΩ _
  have hfix : fixModΩ (⊥ : Subgroup AutPerm) = ⊤ := by
    apply le_antisymm le_top
    intro c _
    rw [mem_fixModΩ]
    intro p hp
    rw [Subgroup.mem_bot.1 hp, permC_one, sub_self]
    exact ΩLine.zero_mem
  have hYfin : Module.finrank (ZMod 2) ↥(X ⊓ compatC X) ≤ 3 := by
    refine finrank_le_three ht (Y := X ⊓ compatC X) ⟨hΩ, ΩC_mem_compatC X⟩ ?_
    intro y hy y' hy'
    exact (mem_compatC.1 hy.2) y' hy'.1
  have hcardY8 : Nat.card ↥(X ⊓ compatC X) ≤ 8 := by
    rw [natCard_sub']
    calc 2 ^ Module.finrank (ZMod 2) ↥(X ⊓ compatC X) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) hYfin
      _ = 8 := by norm_num
  have hcard : Nat.card X * Nat.card (compatC X) =
      Nat.card ↥(X ⊔ compatC X) * Nat.card ↥(X ⊓ compatC X) := by
    rw [natCard_sub' X, natCard_sub' (compatC X), natCard_sub' (X ⊔ compatC X),
      natCard_sub' (X ⊓ compatC X), ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    have h := Submodule.finrank_sup_add_finrank_inf_eq X (compatC X)
    omega
  have hXZ : Nat.card X * Nat.card (compatC X) ≤ 8 * Nat.card ↥(X ⊔ compatC X) := by
    rw [hcard, Nat.mul_comm 8 (Nat.card ↥(X ⊔ compatC X))]
    exact Nat.mul_le_mul_left _ hcardY8
  have hVle : Nat.card ↥(X ⊔ compatC X) ≤
      Nat.card ↥(commΩ (⊥ : Subgroup AutPerm) ⊔ X ⊔
        (compatC X ⊓ fixModΩ (⊥ : Subgroup AutPerm))) := by
    rw [hfix, inf_top_eq]
    have hle : X ⊔ compatC X ≤ commΩ (⊥ : Subgroup AutPerm) ⊔ X ⊔ compatC X :=
      sup_le (le_trans le_sup_right le_sup_left) le_sup_right
    rw [natCard_sub', natCard_sub']
    exact Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_mono hle)
  calc
    Nat.card X * Nat.card (⊥ : Subgroup AutPerm) * 2 ^ 11 *
        Nat.card ↥(compatC X ⊓ fixModΩ (⊥ : Subgroup AutPerm))
        = 2 ^ 11 * (Nat.card X * Nat.card (compatC X)) := by
          rw [Subgroup.card_bot, hfix, inf_top_eq]
          ring
    _ ≤ 2 ^ 11 * (8 * Nat.card ↥(X ⊔ compatC X)) := Nat.mul_le_mul_left _ hXZ
    _ = 2 ^ 14 * Nat.card ↥(X ⊔ compatC X) := by ring
    _ ≤ 2 ^ 14 * Nat.card ↥(commΩ (⊥ : Subgroup AutPerm) ⊔ X ⊔
          (compatC X ⊓ fixModΩ (⊥ : Subgroup AutPerm))) :=
          Nat.mul_le_mul_left _ hVle

end CFSG.KC.FixBoundK

end
