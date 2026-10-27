module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality

section Transport

variable {τ : Tag}

theorem rootReflection_smul_conj (t : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    rootReflection (t • v) = t * rootReflection v * t⁻¹ := by
  by_cases hv : IsRoot τ v
  · exact rootReflection_smul_root t hv
  · have htv : ¬ IsRoot τ (t • v) := fun h => hv (by simpa using IsRoot.smul h t⁻¹)
    simp only [rootReflection, dif_neg hv, dif_neg htv, mul_one, mul_inv_cancel]

private theorem conj_pow_smul (t w' : WeylGroup τ) (n : ℕ) (x : Fin τ.rank → ℤ) :
    (t * w' * t⁻¹) ^ n • (t • x) = t • (w' ^ n • x) := by
  rw [conj_pow, mul_smul, mul_smul, inv_smul_smul]

theorem isOrthTriple_conj_iff (t w' : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    IsOrthTriple (t * w' * t⁻¹) (t • x) ↔ IsOrthTriple w' x := by
  have h1 := conj_pow_smul t w' 1 x
  rw [pow_one, pow_one] at h1
  unfold IsOrthTriple
  rw [h1, conj_pow_smul, iform_smul, iform_smul, iform_smul]

theorem tripleRefl_conj (t w' : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    tripleRefl (t * w' * t⁻¹) (t • x) = t * tripleRefl w' x * t⁻¹ := by
  have h1 := conj_pow_smul t w' 1 x
  rw [pow_one, pow_one] at h1
  unfold tripleRefl
  rw [h1, conj_pow_smul, rootReflection_smul_conj t x, rootReflection_smul_conj t (w' • x),
    rootReflection_smul_conj t (w' ^ 2 • x)]
  group

private theorem prod_map_conj {G α : Type*} [Group G] (t : G) (f : α → G) (l : List α) :
    (l.map fun x => t * f x * t⁻¹).prod = t * (l.map f).prod * t⁻¹ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih]
    group

theorem tripleRefl_transitive_conj {S S' : Set (Fin τ.rank → ℤ)} {t w' : WeylGroup τ}
    (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S')
    (h : ∀ d ∈ S', IsOrthTriple w' d → ∀ β ∈ S', IsOrthTriple w' β →
      ∃ l : List (Fin τ.rank → ℤ), l.length ≤ 2 ∧ (∀ δ ∈ l, δ ∈ S' ∧ IsOrthTriple w' δ) ∧
        (l.map (tripleRefl w')).prod • β ∈ ({d, w' • d, w' ^ 2 • d} : Set (Fin τ.rank → ℤ))) :
    ∀ d ∈ S, IsOrthTriple (t * w' * t⁻¹) d → ∀ β ∈ S, IsOrthTriple (t * w' * t⁻¹) β →
      ∃ l : List (Fin τ.rank → ℤ), l.length ≤ 2 ∧
        (∀ δ ∈ l, δ ∈ S ∧ IsOrthTriple (t * w' * t⁻¹) δ) ∧
        (l.map (tripleRefl (t * w' * t⁻¹))).prod • β ∈
          ({d, (t * w' * t⁻¹) • d, (t * w' * t⁻¹) ^ 2 • d} : Set (Fin τ.rank → ℤ)) := by
  intro d hd hdo β hβ hβo
  rw [← smul_inv_smul t d, isOrthTriple_conj_iff] at hdo
  rw [← smul_inv_smul t β, isOrthTriple_conj_iff] at hβo
  obtain ⟨l, hlen, hl, hmem⟩ := h _ ((hS d).1 hd) hdo _ ((hS β).1 hβ) hβo
  refine ⟨l.map (t • ·), by rw [List.length_map]; exact hlen, fun δ hδ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hδ
    exact ⟨(hS _).2 (by rw [inv_smul_smul]; exact (hl x hx).1),
      (isOrthTriple_conj_iff t w' x).2 (hl x hx).2⟩
  · have e : (tripleRefl (t * w' * t⁻¹) ∘ (t • ·)) = fun x => t * tripleRefl w' x * t⁻¹ :=
      funext fun x => tripleRefl_conj t w' x
    have eL : (t * (l.map (tripleRefl w')).prod * t⁻¹) • β =
        t • ((l.map (tripleRefl w')).prod • (t⁻¹ • β)) := by
      rw [mul_smul, mul_smul]
    rw [List.map_map, e, prod_map_conj, eL]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
    rcases hmem with h' | h' | h'
    · left
      rw [h', smul_inv_smul]
    · right; left
      have e1 := conj_pow_smul t w' 1 (t⁻¹ • d)
      rw [pow_one, pow_one, smul_inv_smul] at e1
      rw [h', e1]
    · right; right
      have e2 := conj_pow_smul t w' 2 (t⁻¹ • d)
      rw [smul_inv_smul] at e2
      rw [h', e2]

end Transport

section E8


theorem e8D4_tripleRefl_transitive {L : Type} [Field L] {a : Fin 2 → Fin Tag.E8.rank → Lˣ}
    {w : WeylGroup Tag.E8} (hD4 : E8D4OrthOrbit a w) {d β : Fin Tag.E8.rank → ℤ}
    (hd : d ∈ familyKernel a) (hdo : IsOrthTriple w d) (hβ : β ∈ familyKernel a)
    (hβo : IsOrthTriple w β) :
    ∃ l : List (Fin Tag.E8.rank → ℤ), (∀ δ ∈ l, δ ∈ familyKernel a ∧ IsOrthTriple w δ) ∧
      (l.map (tripleRefl w)).prod • β ∈ ({d, w • d, w ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ)) :=
  let ⟨l, _, hl, h⟩ := hD4.2.2.1 d hd hdo β hβ hβo
  ⟨l, hl, h⟩

end E8

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
