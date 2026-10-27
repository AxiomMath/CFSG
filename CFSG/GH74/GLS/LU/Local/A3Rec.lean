module

public import CFSG.GH74.L5U5.IdentUnitary

public section

namespace CFSG.GH74.GLS.LU.Local

open CFSG.ClassicalInvolution.WeakCT CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5
open scoped MatrixGroups

theorem exists_surjection_pos_lin {K : Type} [Field K] [Finite K] (p f : ℕ) (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hq : 3 ≤ p ^ f) {G : Type} [Group G] (J : Fin 3 → Subgroup G)
    (hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (J i) (J j))
    (hne : ∃ x ∈ J 0, x ≠ 1) :
    ∃ (ψ : SL(4, K) →* G) (ι : Fin 3 → (SL(2, K) →* G)), ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center SL(4, K) ∧
      (∀ i, (ι i).range = J i ∧ Function.Injective (ι i)) ∧
      ∀ i A, ψ (blockSL2 K 3 i A) = ι i A := by
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by
    rw [h, pow_zero] at hq
    omega
  set N : Subgroup G := ⨆ i, J i with hN
  have hJN : ∀ i, J i ≤ N := fun i => le_iSup J i
  have hgen : ⨆ i, (J i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hJN _)]
    exact hN.symm
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs_ge_three (X := ↥N) (K := K) (by omega) (n := 3)
    (by omega) (U := fun i => (J i).subgroupOf N)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x hx y hy))
    (fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, linearBlockStandardPair_subgroupOf hW N (hJN i) (hJN j)⟩)
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := hne
    have hxr : (⟨x, hJN 0 hx⟩ : ↥N) ∈ (F.ι 0).range := by
      rw [(hF 0).1]; exact hx
    obtain ⟨A, hA⟩ := hxr
    exact ⟨0, A, by rw [hA]; exact fun h => hx1 (congrArg Subtype.val h)⟩
  obtain ⟨ψ', hcompat, hsurj, hker, -, -, -⟩ := exists_recognition (by norm_num : 3 ≤ 3) hp hf hK F hgen' hnt
  refine ⟨N.subtype.comp ψ', fun i => N.subtype.comp (F.ι i), ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective ψ' N.subtype N.subtype_injective]
    exact hker
  · intro i
    refine ⟨?_, N.subtype_injective.comp (hF i).2⟩
    rw [MonoidHom.range_comp, (hF i).1, Subgroup.map_subgroupOf_eq_of_le (hJN i)]
  · intro i A
    simp only [MonoidHom.comp_apply, hcompat]

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits in
theorem exists_surjection_pos_uni {K : Type} [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G]
    (J : Fin 3 → Subgroup G)
    (hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ J i, ∀ y ∈ J j, x * y = y * x)
    (hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W (J i) (J j))
    (hne : ∃ x ∈ J 0, x ≠ 1) :
    ∃ (ψ : Su K p f 4 →* G) (ι : Fin 3 → (Su K p f 2 →* G)), ψ.range = ⨆ i, J i ∧
      ψ.ker ≤ Subgroup.center (Su K p f 4) ∧
      (∀ i, (ι i).range = J i ∧ Function.Injective (ι i)) ∧
      ∀ i A, ψ (blockEmb2 K p f 3 i A) = ι i A := by
  have hq2 : p ^ f ≠ 2 := by omega
  set N : Subgroup G := ⨆ i, J i with hN
  have hJN : ∀ i, J i ≤ N := fun i => le_iSup J i
  have hgen : ⨆ i, (J i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hJN _)]
    exact hN.symm
  have hstd : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair K p f W ((J i).subgroupOf N) ((J j).subgroupOf N) :=
    fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, unitaryBlockStandardPair_subgroupOf hK hq2 hW N (hJN i) (hJN j)⟩
  have hW : WeakPhanA K p f 3 (fun i => (J i).subgroupOf N)
      (fun i j => (J i).subgroupOf N ⊔ (J j).subgroupOf N) := by
    refine ⟨?_, fun _ _ _ => rfl, ?_, ?_, hgen⟩
    · intro i
      by_cases h : (i : ℕ) + 1 < 3
      · obtain ⟨W, hW⟩ := hstd i ⟨i + 1, h⟩ rfl
        exact (nonempty_mulEquiv_of_standardPair hK hW).1
      · have hi : 0 < (i : ℕ) := by have := i.2; omega
        obtain ⟨W, hW⟩ := hstd ⟨(i : ℕ) - 1, by omega⟩ i (by simp only; omega)
        exact (nonempty_mulEquiv_of_standardPair hK hW).2
    · intro i j hij x hx y hy
      exact Subtype.ext (hcomm i j hij x hx y hy)
    · intro i j hj
      obtain ⟨W, hW⟩ := hstd i j hj
      rwa [unitaryBlockStandardPair_eq_sup hK hq2 hW] at hW
  obtain ⟨F, hFι, hFinj, -⟩ := coherent_family hK (by norm_num : 2 ≤ 3) hW
  obtain ⟨ψ', hψ2, -⟩ := phanUniversal K p f hK hq (n := 3) (by norm_num) F
  have hsurj : Function.Surjective ψ' := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hW.gen]
    refine iSup_le fun i => ?_
    rw [← hFι i, ← hψ2 i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : CFSG.IsQuasisimple (Su K p f 4) :=
    isQuasisimple_su hK (by norm_num) (fun h => by have := (Prod.mk.inj h).1; omega)
  have hnt : ∃ k, ψ' k ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := hne
    have hxr : (⟨x, hJN 0 hx⟩ : ↥N) ∈ (F.ι 0).range := by rw [hFι 0]; exact hx
    obtain ⟨A, hA⟩ := hxr
    refine ⟨blockEmb2 K p f 3 0 A, ?_⟩
    have := congrArg (fun g => g A) (hψ2 0)
    simp only [MonoidHom.comp_apply] at this
    rw [this, hA]
    exact fun h => hx1 (congrArg Subtype.val h)
  have hker : ψ'.ker ≤ Subgroup.center (Su K p f 4) := ker_le_center_of_isQuasisimple hquasi hnt
  refine ⟨N.subtype.comp ψ', fun i => N.subtype.comp (F.ι i), ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective ψ' N.subtype N.subtype_injective]
    exact hker
  · intro i
    refine ⟨?_, N.subtype_injective.comp (hFinj i)⟩
    rw [MonoidHom.range_comp, hFι i, Subgroup.map_subgroupOf_eq_of_le (hJN i)]
  · intro i A
    have := congrArg (fun g => g A) (hψ2 i)
    simpa using congrArg (fun x : ↥N => (x : G)) this

end CFSG.GH74.GLS.LU.Local
