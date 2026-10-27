module

public import CFSG.LieType.SeitzGeneration.HyperIrrIsolate
public import CFSG.LieType.SeitzGeneration.HyperIrrBlock

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem exists_ne_pair (hp3 : 3 ≤ p) (j l : Fin p) : ∃ m : Fin p, m ≠ j ∧ m ≠ l := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin p)) ⊆ {j, l} := fun m _ => by
    by_cases hm : m = j
    · simp [hm]
    · simp [h m hm]
  have h1 := Finset.card_le_card hsub
  have h2 : ({j, l} : Finset (Fin p)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem exists_ne_one (hp3 : 3 ≤ p) (i : Fin p) : ∃ i' : Fin p, i' ≠ i := by
  obtain ⟨m, hm, -⟩ := exists_ne_pair hp3 i i
  exact ⟨m, hm⟩

theorem Mf_transvection (j l : Fin p) (hjl : j ≠ l) (c : F) :
    Mf (((SpecialLinearGroup.transvection hjl c : SpecialLinearGroup (Fin p) F)) :
      Matrix (Fin p) (Fin p) F) = 1 + c • kr projF (Matrix.single j l 1) := by
  rw [SpecialLinearGroup.transvection_coe, Mf, add_sub_cancel_left,
    show (Matrix.single j l c : Matrix (Fin p) (Fin p) F) = c • Matrix.single j l 1 by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], kr_smul_right]

theorem kr_single (i j k l : Fin p) :
    kr (Matrix.single i k (1 : F)) (Matrix.single j l 1) =
      Matrix.single (finProdFinEquiv (i, j)) (finProdFinEquiv (k, l)) 1 := by
  ext a b
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨k', l'⟩, rfl⟩ := finProdFinEquiv.surjective b
  rw [kr_apply]
  simp only [Matrix.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h1 : i = i' <;> by_cases h2 : k = k' <;> by_cases h3 : j = j' <;>
    by_cases h4 : l = l' <;> simp [h1, h2, h3, h4]

section Main

variable {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)} {ω : F}

theorem transvection_mem_typeA (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (hblock : ∀ g : SpecialLinearGroup (Fin p) F, ∃ h ∈ K',
      (h : Matrix (Fin (p * p)) (Fin (p * p)) F) = Mf (g : Matrix (Fin p) (Fin p) F))
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K') {i k j l : Fin p}
    (hik : i ≠ k) (hjl : j ≠ l)
    (hne : finProdFinEquiv (i, j) ≠ finProdFinEquiv (k, l)) (c : F) :
    SpecialLinearGroup.transvection hne c ∈ K' := by
  have hP : (projF : Matrix (Fin p) (Fin p) F) ∈ nilSub K' j l hjl := fun c' => by
    obtain ⟨h, hh, he⟩ := hblock (SpecialLinearGroup.transvection hjl c')
    exact ⟨h, hh, by rw [he, Mf_transvection]⟩
  have hE := single_mem_nilSub hω hp3 hpF ht hP hik c
  obtain ⟨h, hh, he⟩ := hE
  have : h = SpecialLinearGroup.transvection hne c := by
    apply Subtype.ext
    rw [he, SpecialLinearGroup.transvection_coe, kr_single, Matrix.smul_single, smul_eq_mul,
      mul_one]
  rwa [this] at hh

theorem transvection_mem_typeB (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (hblock : ∀ g : SpecialLinearGroup (Fin p) F, ∃ h ∈ K',
      (h : Matrix (Fin (p * p)) (Fin (p * p)) F) = Mf (g : Matrix (Fin p) (Fin p) F))
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K') {i j l : Fin p}
    (hne : finProdFinEquiv (i, j) ≠ finProdFinEquiv (i, l)) (c : F) :
    SpecialLinearGroup.transvection hne c ∈ K' := by
  obtain ⟨i', hi'⟩ := exists_ne_one hp3 i
  obtain ⟨m, hmj, hml⟩ := exists_ne_pair hp3 j l
  have h1 : finProdFinEquiv (i, j) ≠ finProdFinEquiv (i', m) := fun h =>
    hi' (by simpa using (congrArg Prod.fst (finProdFinEquiv.injective h)).symm)
  have h2 : finProdFinEquiv (i', m) ≠ finProdFinEquiv (i, l) := fun h =>
    hi' (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
  have hx1 := transvection_mem_typeA hω hp3 hpF hblock ht (Ne.symm hi') (Ne.symm hmj) h1 c
  have hx2 := transvection_mem_typeA hω hp3 hpF hblock ht hi' hml h2 1
  have hcomm := SpecialLinearGroup.commutatorElement_transvection h1 h2 hne c (1 : F)
  rw [mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx1 hx2) (K'.inv_mem hx1)) (K'.inv_mem hx2)

theorem transvection_mem_all (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (hblock : ∀ g : SpecialLinearGroup (Fin p) F, ∃ h ∈ K',
      (h : Matrix (Fin (p * p)) (Fin (p * p)) F) = Mf (g : Matrix (Fin p) (Fin p) F))
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K')
    {α β : Fin (p * p)} (hαβ : α ≠ β) (c : F) : SpecialLinearGroup.transvection hαβ c ∈ K' := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective α
  obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective β
  by_cases hik : i = k
  · subst hik
    exact transvection_mem_typeB hω hp3 hpF hblock ht hαβ c
  · by_cases hjl : j = l
    · subst hjl
      obtain ⟨m, hmj, -⟩ := exists_ne_pair hp3 j j
      have h1 : finProdFinEquiv (i, j) ≠ finProdFinEquiv (i, m) := fun h =>
        hmj (by simpa using (congrArg Prod.snd (finProdFinEquiv.injective h)).symm)
      have h2 : finProdFinEquiv (i, m) ≠ finProdFinEquiv (k, j) := fun h =>
        hik (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
      have hx1 := transvection_mem_typeB hω hp3 hpF hblock ht h1 c
      have hx2 := transvection_mem_typeA hω hp3 hpF hblock ht hik hmj h2 1
      have hcomm := SpecialLinearGroup.commutatorElement_transvection h1 h2 hαβ c (1 : F)
      rw [mul_one] at hcomm
      rw [← hcomm, commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx1 hx2) (K'.inv_mem hx1)) (K'.inv_mem hx2)
    · exact transvection_mem_typeA hω hp3 hpF hblock ht hik hjl hαβ c

theorem eq_top_of_three_families (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K')
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K')
    {a : SpecialLinearGroup (Fin p) F} (ha : a ∉ Subgroup.center (SpecialLinearGroup (Fin p) F))
    (haK : a ∈ blockSub hpF K') : K' = ⊤ := by
  have hblock := Mf_mem_of_noncentral hp3 hpF hd ha haK
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin (p * p)) (K := F)
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact transvection_mem_all hω hp3 hpF hblock ht t.hij t.c

end Main

end CFSG.LieType.SeitzGeneration
