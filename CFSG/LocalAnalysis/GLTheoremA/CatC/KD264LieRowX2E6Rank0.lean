module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Pieces
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open

@[expose] def a3Roots : Set (Fin 6 → ℤ) :=
  {![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
   ![1, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 0]}

theorem rootsE6_simple (i : Fin 6) : (Pi.single i (1 : ℤ)) ∈ rootsE6 := by
  unfold rootsE6
  rw [Set.mem_sInter]
  intro S hS
  exact hS.1 i

theorem rootsE6_closed {α : Fin 6 → ℤ} (hα : α ∈ rootsE6) (i : Fin 6) :
    rootRefl i α ∈ rootsE6 := by
  unfold rootsE6 at hα ⊢
  rw [Set.mem_sInter] at hα ⊢
  intro S hS
  exact hS.2 α (hα S hS) i

theorem mem_rootsE6_of_refl_eq {α β : Fin 6 → ℤ} (i : Fin 6) (hα : α ∈ rootsE6)
    (h : rootRefl i α = β) : β ∈ rootsE6 :=
  h ▸ rootsE6_closed hα i

theorem cartanE6_symm (i j : Fin 6) : cartanE6 i j = cartanE6 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem cartanForm_comm (α β : Fin 6 → ℤ) : cartanForm α β = cartanForm β α := by
  unfold cartanForm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [cartanE6_symm]
  ring

theorem a3Roots_subset_rootsE6 : a3Roots ⊆ rootsE6 := by
  have h0 : Pi.single (0 : Fin 6) (1 : ℤ) ∈ rootsE6 := rootsE6_simple 0
  have h2 : Pi.single (2 : Fin 6) (1 : ℤ) ∈ rootsE6 := rootsE6_simple 2
  have h3 : Pi.single (3 : Fin 6) (1 : ℤ) ∈ rootsE6 := rootsE6_simple 3
  have hd : (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 :=
    mem_rootsE6_of_refl_eq 2 h0 (by funext j; fin_cases j <;>
      simp [rootRefl, cartanE6, Fin.sum_univ_six, Pi.single_apply])
  have hf : (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 :=
    mem_rootsE6_of_refl_eq 3 h2 (by funext j; fin_cases j <;>
      simp [rootRefl, cartanE6, Fin.sum_univ_six, Pi.single_apply])
  have hg : (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 :=
    mem_rootsE6_of_refl_eq 3 hd (by funext j; fin_cases j <;>
      simp [rootRefl, cartanE6, Fin.sum_univ_six])
  have he0 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 := by
    convert h0 using 1
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have he2 : (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 := by
    convert h2 using 1
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have he3 : (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ) ∈ rootsE6 := by
    convert h3 using 1
    funext j; fin_cases j <;> simp [Pi.single_apply]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact he0
  · exact he2
  · exact he3
  · exact hd
  · exact hf
  · exact hg

theorem a3Roots_connected : IsRootConnected a3Roots := by
  have step : ∀ {a b : Fin 6 → ℤ}, a ∈ a3Roots → b ∈ a3Roots → cartanForm a b ≠ 0 →
      Relation.ReflTransGen (fun x y => x ∈ a3Roots ∧ y ∈ a3Roots ∧ cartanForm x y ≠ 0) a b :=
    fun ha hb h => Relation.ReflTransGen.single ⟨ha, hb, h⟩
  have hd : (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ) ∈ a3Roots := by simp [a3Roots]
  have hb : (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ) ∈ a3Roots := by simp [a3Roots]
  have hto : ∀ x ∈ a3Roots, Relation.ReflTransGen
      (fun a b => a ∈ a3Roots ∧ b ∈ a3Roots ∧ cartanForm a b ≠ 0) x ![1, 0, 1, 0, 0, 0] := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact step (by simp [a3Roots]) hd (by decide)
    · exact step (by simp [a3Roots]) hd (by decide)
    · exact step (by simp [a3Roots]) hd (by decide)
    · exact Relation.ReflTransGen.refl
    · exact (step (by simp [a3Roots]) hb (by decide)).tail ⟨hb, hd, by decide⟩
    · exact step (by simp [a3Roots]) hd (by decide)
  have hfrom : ∀ x ∈ a3Roots, Relation.ReflTransGen
      (fun a b => a ∈ a3Roots ∧ b ∈ a3Roots ∧ cartanForm a b ≠ 0) ![1, 0, 1, 0, 0, 0] x := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact step hd (by simp [a3Roots]) (by decide)
    · exact step hd (by simp [a3Roots]) (by decide)
    · exact step hd (by simp [a3Roots]) (by decide)
    · exact Relation.ReflTransGen.refl
    · exact (step hd hb (by decide)).tail ⟨hb, by simp [a3Roots], by decide⟩
    · exact step hd (by simp [a3Roots]) (by decide)
  intro x hx y hy
  exact (hto x hx).trans (hfrom y hy)

theorem a3Roots_rank : 3 ≤ rootRankQ a3Roots := by
  unfold rootRankQ
  let v : Fin 3 → (Fin 6 → ℚ) := ![fun i => ((![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) i : ℚ),
    fun i => ((![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ) i : ℚ),
    fun i => ((![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ) i : ℚ)]
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h2 := congrFun hg 2
    have h3 := congrFun hg 3
    simp [Fin.sum_univ_three, v] at h0 h2 h3
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h2
    · simpa using h3
  have hsub : Set.range v ⊆ (fun α : Fin 6 → ℤ => fun i => ((α i : ℤ) : ℚ)) '' a3Roots := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨_, by simp [a3Roots], rfl⟩
    · exact ⟨_, by simp [a3Roots], rfl⟩
    · exact ⟨_, by simp [a3Roots], rfl⟩
  calc 3 = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) := by
        rw [finrank_span_eq_card hli]; simp
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono hsub)

theorem rootGood_of_orth (F : Set (Fin 6 → ZMod 3))
    (hF : ∀ f ∈ F, f 0 = 0 ∧ f 2 = 0 ∧ f 3 = 0) : RootGood F := by
  refine ⟨a3Roots, a3Roots_subset_rootsE6, a3Roots_connected, a3Roots_rank, ?_⟩
  intro α hα f hf
  obtain ⟨h0, h2, h3⟩ := hF f hf
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Fin.sum_univ_six, h0, h2, h3]

theorem three_nsmul_eq_zero_coords (a : Fin 6 → ZMod 3) : (3 : ℕ) • a = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  have : ∀ x : ZMod 3, ((3 : ℕ) : ZMod 3) * x = 0 := by decide
  exact this (a i)

theorem card_toAddSubgroup_eq {A : Type} [AddGroup A] (S : Subgroup (Multiplicative A)) :
    Nat.card (Subgroup.toAddSubgroup' S) = Nat.card S := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.ofAdd (x : A), (Subgroup.mem_toAddSubgroup' S _).1 x.2⟩
      invFun := fun y => ⟨Multiplicative.toAdd (y : Multiplicative A),
        (Subgroup.mem_toAddSubgroup' S _).2 (by simpa using y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem isElemAbelian_top_mult :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin 6 → ZMod 3))) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
  · exact Subtype.ext (mul_comm (a : Multiplicative (Fin 6 → ZMod 3)) b)
  · apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one]
    exact three_nsmul_eq_zero_coords _

theorem weyl_rank0 (U : AddSubgroup (Fin 6 → ZMod 3)) (hU : 3 ^ 5 ≤ Nat.card U) :
    ∃ F : AddSubgroup (Fin 6 → ZMod 3), (F : Set (Fin 6 → ZMod 3)) ⊆ U ∧
      Nat.card F = 9 ∧ RootGood (F : Set (Fin 6 → ZMod 3)) := by
  obtain ⟨Um, hUm⟩ : ∃ Um : Subgroup (Multiplicative (Fin 6 → ZMod 3)),
      Subgroup.toAddSubgroup' Um = U := ⟨_, OrderIso.apply_symm_apply _ U⟩
  have hmemUm : ∀ x : Fin 6 → ZMod 3, Multiplicative.ofAdd x ∈ Um ↔ x ∈ U := by
    intro x
    rw [← Subgroup.mem_toAddSubgroup', hUm]
  have hUmcard : 3 ^ 5 ≤ Nat.card Um := by
    have := card_toAddSubgroup_eq Um
    rw [hUm] at this
    rw [← this]
    exact hU
  let proj : (Fin 6 → ZMod 3) →+ (Fin 3 → ZMod 3) :=
    { toFun := fun f => ![f 0, f 2, f 3]
      map_zero' := by funext i; fin_cases i <;> rfl
      map_add' := fun x y => by funext i; fin_cases i <;> simp }
  let h : Um →* Multiplicative (Fin 3 → ZMod 3) :=
    (AddMonoidHom.toMultiplicative proj).comp Um.subtype
  have hrange_le : Nat.card h.range ≤ 27 := by
    have h1 := Subgroup.card_le_card_group (G := Multiplicative (Fin 3 → ZMod 3)) (H := h.range)
    have h2 : Nat.card (Multiplicative (Fin 3 → ZMod 3)) = 27 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm]
      simp [Nat.card_eq_fintype_card]
    omega
  have hdiv := Subgroup.card_ker_mul_card_range h
  have hker9 : 9 ≤ Nat.card h.ker := by
    by_contra! hlt
    have hmul : Nat.card h.ker * Nat.card h.range ≤ 8 * 27 :=
      Nat.mul_le_mul (by omega) hrange_le
    linarith
  let L : Subgroup (Multiplicative (Fin 6 → ZMod 3)) := h.ker.map Um.subtype
  have hLcard : Nat.card L = Nat.card h.ker :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have hLab : IsElemAbelian 3 L := isElemAbelian_mono isElemAbelian_top_mult le_top
  obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hLab
  have h9' : 9 ≤ 3 ^ j := by rw [← hj, hLcard]; exact hker9
  have hj2 : 2 ≤ j := by
    by_contra! hlt
    have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  have h9 : 3 ^ 2 ∣ Nat.card L := by
    rw [hj]
    exact pow_dvd_pow 3 hj2
  obtain ⟨K, hKcard, _, hKL⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (H := ⊥) (L := L) (n := 2)
      (by simp) h9 bot_le
  refine ⟨Subgroup.toAddSubgroup' K, ?_, ?_, ?_⟩
  · intro x hx
    have hxK : Multiplicative.ofAdd x ∈ K := (Subgroup.mem_toAddSubgroup' K x).1 hx
    obtain ⟨y, _, hy⟩ := Subgroup.mem_map.1 (hKL hxK)
    have hyU : Multiplicative.ofAdd x ∈ Um := by
      rw [← hy]
      exact y.2
    exact (hmemUm x).1 hyU
  · rw [card_toAddSubgroup_eq, hKcard]
    norm_num
  · apply rootGood_of_orth
    intro f hf
    have hK : Multiplicative.ofAdd f ∈ K := (Subgroup.mem_toAddSubgroup' K f).1 hf
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.1 (hKL hK)
    have hfeq : Multiplicative.toAdd (y : Multiplicative (Fin 6 → ZMod 3)) = f := by
      have := congrArg Multiplicative.toAdd hyf
      simpa using this
    have hy1 : h y = 1 := MonoidHom.mem_ker.1 hy
    have h2 : Multiplicative.ofAdd (proj (Multiplicative.toAdd
        (y : Multiplicative (Fin 6 → ZMod 3)))) = 1 := hy1
    have h3 : proj f = 0 := by
      rw [← hfeq]
      exact ofAdd_eq_one.1 h2
    have e0 : f 0 = 0 := by simpa [proj] using congrFun h3 0
    have e2 : f 2 = 0 := by simpa [proj] using congrFun h3 1
    have e3 : f 3 = 0 := by simpa [proj] using congrFun h3 2
    exact ⟨e0, e2, e3⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
