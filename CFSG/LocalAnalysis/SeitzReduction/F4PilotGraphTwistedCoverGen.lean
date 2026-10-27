module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem simpleRootB_mem_roots_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleRootB r i ∈ roots r := by
  rw [simpleRootB_of_lt h]
  exact ⟨i, ⟨i.val + 1, h⟩, by rw [Fin.lt_def]; simp, Or.inl rfl⟩

theorem tailWeylElt_mem_of_simpleRoots
    {H : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))} (a₀ : A)
    (i : Fin r) (hp : tailRootGroup r qA (simpleRootB r i) ≤ H)
    (hn : tailRootGroup r qA (-simpleRootB r i) ≤ H) : tailWeylElt r qA a₀ i ∈ H := by
  by_cases h : i.val + 1 < r
  · rw [tailWeylElt_of_lt a₀ h]
    have hroot := simpleRootB_mem_roots_of_lt h
    have hp' : tailLongElt r qA (simpleRootB r i) 1 ∈ H :=
      hp ((mem_tailRootGroup_long hroot).2 ⟨1, rfl⟩)
    have hn' : tailLongElt r qA (-simpleRootB r i) (-1) ∈ H :=
      hn ((mem_tailRootGroup_long (neg_mem_roots hroot)).2 ⟨-1, rfl⟩)
    exact mul_mem (mul_mem hp' hn') hp'
  · rw [tailWeylElt, ite_eq_right h]
    rw [simpleRootB_of_not_lt h] at hp hn
    have h1 : eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), a₀) ∈ H :=
      hp (mem_tailRootGroup_eps.2 ⟨a₀, rfl⟩)
    have h2 : eichler (quadTail r qA) (hypVec K A (.inr i))
        ((0 : Fin r ⊕ Fin r → K), (qA a₀)⁻¹ • a₀) ∈ H :=
      hn (mem_tailRootGroup_neg_eps.2 ⟨_, rfl⟩)
    exact mul_mem (mul_mem h1 h2) h1

theorem exists_tailTorusWeyl_mem_nu_eq (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {H : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hH : ∀ i, tailWeylElt r qA a₀ i ∈ H) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroupB r) :
    ∃ n : tailTorusWeyl r qA a₀, (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) ∈ H ∧
      ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = w := by
  rw [← closure_simpleReflB] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨⟨_, tailWeylElt_mem_tailTorusWeyl a₀ i⟩, hH i,
      congrArg Subtype.val (tailTorusWeylNu_tailWeylElt hani ha₀ i)⟩
  | one => exact ⟨1, H.one_mem, by rw [map_one]; rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hnH, hn⟩ := ihx
    obtain ⟨m, hmH, hm⟩ := ihy
    exact ⟨n * m, H.mul_mem hnH hmH, by rw [map_mul, Subgroup.coe_mul, hn, hm]⟩
  | inv x _ ihx =>
    obtain ⟨n, hnH, hn⟩ := ihx
    exact ⟨n⁻¹, H.inv_mem hnH, by rw [map_inv, Subgroup.coe_inv, hn]⟩

theorem tailRootGroup_le_of_simpleRoots (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) {H : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hp : ∀ i, tailRootGroup r qA (simpleRootB r i) ≤ H)
    (hn : ∀ i, tailRootGroup r qA (-simpleRootB r i) ≤ H) {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    tailRootGroup r qA α ≤ H := by
  have hW : ∀ i, tailWeylElt r qA a₀ i ∈ H := fun i =>
    tailWeylElt_mem_of_simpleRoots a₀ i (hp i) (hn i)
  obtain ⟨i, w, hw, hwα, hβ⟩ : ∃ (i : Fin r), ∃ w ∈ weylGroupB r, w (simpleRootB r i) = α ∧
      simpleRootB r i ∈ rootsB r := by
    rcases hα with hs | hl
    · set i : Fin r := ⟨r - 1, by omega⟩ with hi
      have hlast : ¬i.val + 1 < r := by rw [hi]; simp only; omega
      have hsi : simpleRootB r i ∈ shortRootsB r := by
        rw [simpleRootB_of_not_lt hlast]
        exact ⟨i, Or.inl rfl⟩
      obtain ⟨w, hw, hwα⟩ := exists_weylB_apply_eq_short hsi hs
      exact ⟨i, w, hw, hwα, Or.inl hsi⟩
    · set i : Fin r := ⟨0, by omega⟩ with hi
      have hfirst : i.val + 1 < r := by rw [hi]; simp only; omega
      have hli := simpleRootB_mem_roots_of_lt hfirst
      obtain ⟨w, hw, hwα⟩ := exists_weylB_apply_eq_long hli hl
      exact ⟨i, w, hw, hwα, Or.inr hli⟩
  obtain ⟨n, hnH, hn'⟩ := exists_tailTorusWeyl_mem_nu_eq hani ha₀ hW hw
  have hmap := map_conj_tailRootGroup hani ha₀ n hβ
  rw [hn', hwα] at hmap
  rw [← hmap]
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hnH (hp i hx)) (H.inv_mem hnH)

theorem orthElementaryGroup_le_of_simpleRoots (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0)
    (hr : 2 ≤ r) {H : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hp : ∀ i, tailRootGroup r qA (simpleRootB r i) ≤ H)
    (hn : ∀ i, tailRootGroup r qA (-simpleRootB r i) ≤ H) :
    orthElementaryGroup (quadTail r qA) ≤ H := by
  obtain ⟨a₀, ha₀⟩ := hA
  rw [(orthogonal_geometry_tail_root_generation hani ⟨a₀, ha₀⟩).1, tailRootSupr]
  exact iSup₂_le fun α hα => tailRootGroup_le_of_simpleRoots hani ha₀ hr hp hn hα

end CFSG.SeitzReduction.F4Pilot
