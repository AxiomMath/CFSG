module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic

import CFSG.ClassicalGroups.Orthogonal.SixPlane.Toral

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {n : ℕ}

theorem commute_of_mem_torus {S T : Finset (Fin n)} {s t : V n ≃ₗ[ZMod 2] V n}
    (hs : s ∈ torus n S) (ht : t ∈ torus n T) : Commute s t := by
  rw [torus] at hs ht
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    induction ht using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact commute_rot i j
    | one => exact Commute.one_right _
    | mul _ _ _ _ h₁ h₂ => exact h₁.mul_right h₂
    | inv _ _ h => exact h.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ h₁ h₂ => exact h₁.mul_left h₂
  | inv _ _ h => exact h.inv_left

theorem exists_mul_of_mem_torus_union {S T : Finset (Fin n)} {t : V n ≃ₗ[ZMod 2] V n}
    (ht : t ∈ torus n (S ∪ T)) : ∃ a ∈ torus n S, ∃ b ∈ torus n T, a * b = t := by
  classical
  rw [torus] at ht
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hi) with hiS | hiT
    · exact ⟨rot n i, Subgroup.subset_closure ⟨i, Finset.mem_coe.mpr hiS, rfl⟩, 1,
        (torus n T).one_mem, mul_one _⟩
    · exact ⟨1, (torus n S).one_mem, rot n i,
        Subgroup.subset_closure ⟨i, Finset.mem_coe.mpr hiT, rfl⟩, one_mul _⟩
  | one => exact ⟨1, (torus n S).one_mem, 1, (torus n T).one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', (torus n S).mul_mem ha ha', b * b', (torus n T).mul_mem hb hb', ?_⟩
    simp only [mul_assoc]
    rw [(commute_of_mem_torus hb ha').left_comm]
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, (torus n S).inv_mem ha, b⁻¹, (torus n T).inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact (commute_of_mem_torus ((torus n S).inv_mem ha) ((torus n T).inv_mem hb)).eq

private theorem two_le_card_inter_inter {A B C : Finset (Fin 6)} (hA : A.card = 5)
    (hB : B.card = 5) (hC : C.card = 5) : 2 ≤ (A ∩ B ∩ C).card := by
  have h1 : (A ∩ B ∩ C)ᶜ.card ≤ Aᶜ.card + Bᶜ.card + Cᶜ.card := by
    rw [Finset.compl_inter, Finset.compl_inter]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  simp only [Finset.card_compl, Fintype.card_fin, hA, hB, hC] at h1
  have h2 := Finset.card_le_univ (A ∩ B ∩ C)
  simp only [Fintype.card_fin] at h2
  omega

section Charts

variable {H : Type u} [Group H] (ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)
  (τ : Finset (Fin 6) → Finset (Fin 6) → V 6 ≃ₗ[ZMod 2] V 6)

private theorem cocycle_mem_torus
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (hτ : ∀ A B : Finset (Fin 6), τ A B ∈ torus 6 (A ∩ B))
    (hψ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∀ hg : τ A B * g * (τ A B)⁻¹ ∈ supp 6 B,
          ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨τ A B * g * (τ A B)⁻¹, hg⟩)
    {A B C : Finset (Fin 6)} (hA : A.card = 5) (hB : B.card = 5) (hC : C.card = 5) :
    τ B C * τ A B * (τ A C)⁻¹ ∈ torus 6 (Finset.univ \ (A ∩ B ∩ C)) := by
  have hτu : ∀ X Y, τ X Y ∈ torus 6 Finset.univ := fun X Y =>
    torus_mono (Finset.subset_univ _) (hτ X Y)
  have hsA : A ∩ B ∩ C ⊆ A := fun i hi => by simp only [Finset.mem_inter] at hi; exact hi.1.1
  have hsB : A ∩ B ∩ C ⊆ B := fun i hi => by simp only [Finset.mem_inter] at hi; exact hi.1.2
  have hsC : A ∩ B ∩ C ⊆ C := fun i hi => by simp only [Finset.mem_inter] at hi; exact hi.2
  have key : ∀ g ∈ supp 6 (A ∩ B ∩ C),
      τ A C * g * (τ A C)⁻¹ = τ B C * τ A B * g * (τ B C * τ A B)⁻¹ := by
    intro g hg
    have hh : τ A B * g * (τ A B)⁻¹ ∈ supp 6 (A ∩ B ∩ C) :=
      conj_mem_supp_of_mem_torus (hτu A B) hg
    have e1 := hψ A B hA hB g (supp_mono hsA hg) (supp_mono hsB hg) (supp_mono hsB hh)
    have e2 := hψ B C hB hC _ (supp_mono hsB hh) (supp_mono hsC hh)
      (conj_mem_supp_of_mem_torus (hτu B C) (supp_mono hsC hh))
    have e3 := hψ A C hA hC g (supp_mono hsA hg) (supp_mono hsC hg)
      (conj_mem_supp_of_mem_torus (hτu A C) (supp_mono hsC hg))
    have h : τ A C * g * (τ A C)⁻¹ = τ B C * (τ A B * g * (τ A B)⁻¹) * (τ B C)⁻¹ :=
      congrArg Subtype.val (hinj C hC (e3.symm.trans (e1.trans e2)))
    rw [h]
    group
  refine mem_torus_sdiff_of_commute (two_le_card_inter_inter hA hB hC)
    ((torus 6 _).mul_mem ((torus 6 _).mul_mem (hτu B C) (hτu A B)) ((torus 6 _).inv_mem
      (hτu A C))) fun g hg => ?_
  have hg' : (τ A C)⁻¹ * g * τ A C ∈ supp 6 (A ∩ B ∩ C) := by
    simpa using conj_mem_supp_of_mem_torus ((torus 6 _).inv_mem (hτu A C)) hg
  have k := key _ hg'
  rw [show τ A C * ((τ A C)⁻¹ * g * τ A C) * (τ A C)⁻¹ = g by group] at k
  show _ * g = g * _
  nth_rewrite 2 [k]
  group

theorem exists_torus_twist_of_pairs
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (hτ : ∀ A B : Finset (Fin 6), τ A B ∈ torus 6 (A ∩ B))
    (hψ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∀ hg : τ A B * g * (τ A B)⁻¹ ∈ supp 6 B,
          ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨τ A B * g * (τ A B)⁻¹, hg⟩) :
    ∃ t : ∀ A : Finset (Fin 6), ↥(supp 6 A), (∀ A, (t A : V 6 ≃ₗ[ZMod 2] V 6) ∈ torus 6 A) ∧
      ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
        (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
          ψ A hA (MulAut.conj (t A) ⟨g, hgA⟩) = ψ B hB (MulAut.conj (t B) ⟨g, hgB⟩) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin 6), R = Finset.univ.erase 0 := ⟨_, rfl⟩
  obtain ⟨Rp, hRp⟩ : ∃ Rp : Finset (Fin 6), Rp = Finset.univ.erase 1 := ⟨_, rfl⟩
  have hRc : R.card = 5 := by
    rw [hR, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hRpc : Rp.card = 5 := by
    rw [hRp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hτu : ∀ X Y, τ X Y ∈ torus 6 Finset.univ := fun X Y =>
    torus_mono (Finset.subset_univ _) (hτ X Y)
  have hsplit : ∀ A : Finset (Fin 6), ∃ a ∈ torus 6 (A ∩ Rp ∩ {0}),
      ∃ b ∈ torus 6 ((A ∩ Rp) \ {0}), a * b = τ A Rp := by
    intro A
    refine exists_mul_of_mem_torus_union ?_
    have hX : A ∩ Rp ∩ {0} ∪ (A ∩ Rp) \ {0} = A ∩ Rp := by
      ext i
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hX]
    exact hτ A Rp
  choose a ha b hb hab using hsplit
  have haA : ∀ A, a A ∈ torus 6 A := fun A =>
    torus_mono (fun i hi => by simp only [Finset.mem_inter] at hi; exact hi.1.1) (ha A)
  have huA : ∀ A, τ A R ∈ torus 6 A := fun A =>
    torus_mono (fun i hi => by simp only [Finset.mem_inter] at hi; exact hi.1) (hτ A R)
  have htA : ∀ A, (a A * τ A R)⁻¹ ∈ torus 6 A := fun A =>
    (torus 6 A).inv_mem ((torus 6 A).mul_mem (haA A) (huA A))
  refine ⟨fun A => ⟨(a A * τ A R)⁻¹, torus_le_supp A (htA A)⟩, htA, ?_⟩
  intro A B hA hB g hgA hgB
  obtain ⟨X₁, hX₁⟩ : ∃ X, X = (A ∩ B)ᶜ ∪ {0} := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X, X = (A ∩ B)ᶜ ∪ {0}ᶜ := ⟨_, rfl⟩
  have hε₁ : a B * τ B R * τ A B * (a A * τ A R)⁻¹ ∈ torus 6 X₁ := by
    have h0 : ∀ C, a C ∈ torus 6 X₁ := fun C => torus_mono (fun i hi => by
      simp only [Finset.mem_inter, Finset.mem_singleton] at hi
      rw [hX₁, Finset.mem_union, Finset.mem_singleton]
      exact Or.inr hi.2) (ha C)
    have hc : τ B R * τ A B * (τ A R)⁻¹ ∈ torus 6 X₁ := torus_mono (fun i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, and_true, Finset.mem_inter, hR,
        Finset.mem_erase, ne_eq] at hi
      rw [hX₁, Finset.mem_union, Finset.mem_compl, Finset.mem_inter, Finset.mem_singleton]
      tauto) (cocycle_mem_torus ψ τ hinj hτ hψ hA hB hRc)
    rw [show a B * τ B R * τ A B * (a A * τ A R)⁻¹ =
      a B * (τ B R * τ A B * (τ A R)⁻¹) * (a A)⁻¹ by group]
    exact (torus 6 _).mul_mem ((torus 6 _).mul_mem (h0 B) hc) ((torus 6 _).inv_mem (h0 A))
  have hε₂ : a B * τ B R * τ A B * (a A * τ A R)⁻¹ ∈ torus 6 X₂ := by
    have hsub : ∀ C, (C ∩ Rp) \ {0} ⊆ X₂ := fun C i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_singleton] at hi
      rw [hX₂, Finset.mem_union, Finset.mem_compl, Finset.mem_compl, Finset.mem_singleton]
      exact Or.inr hi.2
    have hsubR : ∀ C, C ∩ R ⊆ X₂ := fun C i hi => by
      simp only [Finset.mem_inter, hR, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
      rw [hX₂, Finset.mem_union, Finset.mem_compl, Finset.mem_compl, Finset.mem_singleton]
      exact Or.inr hi.2
    have hc : τ B Rp * τ A B * (τ A Rp)⁻¹ ∈ torus 6 X₂ := torus_mono (fun i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, and_true, Finset.mem_inter, hRp,
        Finset.mem_erase, ne_eq] at hi
      rw [hX₂, Finset.mem_union, Finset.mem_compl, Finset.mem_compl, Finset.mem_inter,
        Finset.mem_singleton]
      by_cases h1 : i = 1
      · subst h1
        exact Or.inr (by decide)
      · tauto) (cocycle_mem_torus ψ τ hinj hτ hψ hA hB hRpc)
    have hcm : (b B)⁻¹ * τ B R ∈ torus 6 X₂ :=
      (torus 6 _).mul_mem ((torus 6 _).inv_mem (torus_mono (hsub B) (hb B)))
        (torus_mono (hsubR B) (hτ B R))
    have hdm : (τ A R)⁻¹ * b A ∈ torus 6 X₂ :=
      (torus 6 _).mul_mem ((torus 6 _).inv_mem (torus_mono (hsubR A) (hτ A R)))
        (torus_mono (hsub A) (hb A))
    have hcu := torus_mono (Finset.subset_univ _) hcm
    have hdu := torus_mono (Finset.subset_univ _) hdm
    have hcτ := (commute_of_mem_torus hcu (hτu A B)).eq
    have hcd := (commute_of_mem_torus ((torus 6 _).mul_mem hcu hdu)
      ((torus 6 _).inv_mem (hτu A Rp))).eq
    have haB : a B = τ B Rp * (b B)⁻¹ := eq_mul_inv_of_mul_eq (hab B)
    have haA' : a A = τ A Rp * (b A)⁻¹ := eq_mul_inv_of_mul_eq (hab A)
    have e : a B * τ B R * τ A B * (a A * τ A R)⁻¹ =
        τ B Rp * τ A B * (τ A Rp)⁻¹ * ((b B)⁻¹ * τ B R * ((τ A R)⁻¹ * b A)) := by
      calc a B * τ B R * τ A B * (a A * τ A R)⁻¹
          = τ B Rp * ((b B)⁻¹ * τ B R * τ A B) * ((τ A R)⁻¹ * b A) * (τ A Rp)⁻¹ := by
            rw [haB, haA']
            group
        _ = τ B Rp * (τ A B * ((b B)⁻¹ * τ B R)) * ((τ A R)⁻¹ * b A) * (τ A Rp)⁻¹ := by
            rw [hcτ]
        _ = τ B Rp * τ A B * ((b B)⁻¹ * τ B R * ((τ A R)⁻¹ * b A) * (τ A Rp)⁻¹) := by
            group
        _ = τ B Rp * τ A B * ((τ A Rp)⁻¹ * ((b B)⁻¹ * τ B R * ((τ A R)⁻¹ * b A))) := by
            rw [hcd]
        _ = _ := by group
    rw [e]
    exact (torus 6 _).mul_mem hc ((torus 6 _).mul_mem hcm hdm)
  have hε : a B * τ B R * τ A B * (a A * τ A R)⁻¹ ∈ torus 6 (A ∩ B)ᶜ := by
    have h : a B * τ B R * τ A B * (a A * τ A R)⁻¹ ∈ torus 6 (X₁ ∩ X₂) := by
      rw [← torus_inf]
      exact Subgroup.mem_inf.mpr ⟨hε₁, hε₂⟩
    refine torus_mono (fun i hi => ?_) h
    rw [hX₁, hX₂] at hi
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl, Finset.mem_singleton] at hi
    rw [Finset.mem_compl, Finset.mem_inter]
    tauto
  have hgAB : g ∈ supp 6 (A ∩ B) := by
    rw [← supp_inf]
    exact ⟨hgA, hgB⟩
  have hc := (commute_of_mem_supp_of_disjoint disjoint_compl_left
    (torus_le_supp _ hε) hgAB).eq
  have htu : ∀ C, (a C * τ C R)⁻¹ ∈ torus 6 Finset.univ := fun C =>
    torus_mono (Finset.subset_univ _) (htA C)
  have hhA := conj_mem_supp_of_mem_torus (htu A) hgA
  have hhB := conj_mem_supp_of_mem_torus (htu A) hgB
  have e1 := hψ A B hA hB _ hhA hhB (conj_mem_supp_of_mem_torus (hτu A B) hhB)
  have heq : τ A B * ((a A * τ A R)⁻¹ * g * ((a A * τ A R)⁻¹)⁻¹) * (τ A B)⁻¹ =
      (a B * τ B R)⁻¹ * g * ((a B * τ B R)⁻¹)⁻¹ := by
    calc τ A B * ((a A * τ A R)⁻¹ * g * ((a A * τ A R)⁻¹)⁻¹) * (τ A B)⁻¹
        = (a B * τ B R)⁻¹ * ((a B * τ B R * τ A B * (a A * τ A R)⁻¹) * g) *
            (a B * τ B R * τ A B * (a A * τ A R)⁻¹)⁻¹ * ((a B * τ B R)⁻¹)⁻¹ := by group
      _ = (a B * τ B R)⁻¹ * (g * (a B * τ B R * τ A B * (a A * τ A R)⁻¹)) *
            (a B * τ B R * τ A B * (a A * τ A R)⁻¹)⁻¹ * ((a B * τ B R)⁻¹)⁻¹ := by rw [hc]
      _ = _ := by group
  have hcoe : ∀ (C : Finset (Fin 6)) (x : V 6 ≃ₗ[ZMod 2] V 6) (hx : x ∈ supp 6 C)
      (y : ↥(supp 6 C)), ((MulAut.conj (⟨x, hx⟩ : ↥(supp 6 C)) y : ↥(supp 6 C)) :
        V 6 ≃ₗ[ZMod 2] V 6) = x * y * x⁻¹ := fun _ _ _ _ => rfl
  have hLs : MulAut.conj (⟨(a A * τ A R)⁻¹, torus_le_supp A (htA A)⟩ : ↥(supp 6 A)) ⟨g, hgA⟩ =
      ⟨_, hhA⟩ := Subtype.ext (hcoe _ _ _ _)
  have hRs : MulAut.conj (⟨(a B * τ B R)⁻¹, torus_le_supp B (htA B)⟩ : ↥(supp 6 B)) ⟨g, hgB⟩ =
      ⟨_, conj_mem_supp_of_mem_torus (hτu A B) hhB⟩ := Subtype.ext ((hcoe _ _ _ _).trans heq.symm)
  rw [hLs, hRs]
  exact e1

end Charts

end CFSG.ClassicalGroups.Orthogonal.SixPlane
