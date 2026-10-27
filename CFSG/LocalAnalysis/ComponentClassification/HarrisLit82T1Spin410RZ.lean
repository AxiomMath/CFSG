module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

theorem isSylowIn_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {P H : Subgroup A}
    (h : IsSylowIn 2 P H) : IsSylowIn 2 (P.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  ⟨map_mono h.1, h.2.1.map _, by
    rw [relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]
    exact h.2.2⟩

theorem lemma410a_of_isCoverOf {X : Type} [Group X] [Finite X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1)
    {S₀ : Subgroup X} (hS₀ : IsSylowIn 2 S₀ ⊤) {x : X} (hx : x ∈ S₀)
    (hxc : ∀ y ∈ S₀, x * y = y * x) : x = 1 ∨ x = z := by
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd h5 hX
  have hez : e z = spinZ K := eq_spinZ_of_mem_center hp hp2 hK
    ((mem_center_mulEquiv_iff e z).mpr hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  have hS := isSylowIn_map_mulEquiv e hS₀
  rw [map_top_of_surjective e.toMonoidHom e.surjective] at hS
  rcases spinSeven_lemma410a hp hp2 hK h5 hS (mem_map_of_mem e.toMonoidHom hx)
      (fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        show e x * e y' = e y' * e x
        rw [← map_mul, ← map_mul, hxc y' hy']) with h | h
  · left
    exact e.injective (h.trans (map_one e).symm)
  · right
    exact e.injective (h.trans hez.symm)

theorem lemma410f_of_isCoverOf {X : Type} [Group X] [Finite X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {t : X} (ht : orderOf t = 2) (htZ : t ∉ center X)
    {T₀ : Subgroup X} (hT₀ : IsSylowIn 2 T₀ (centralizer {t})) :
    closure {x | x ∈ T₀ ∧ x * x = 1} = T₀ := by
  obtain ⟨K, _, _, e, hK, hp, hp2, het⟩ := exists_mulEquiv_spinSeven h5 hX ht htZ
  have hT := isSylowIn_map_mulEquiv e hT₀
  rw [map_centralizer_singleton_mulEquiv e t, het] at hT
  have h := closure_involutions_eq_of_isSylowIn hp hp2 hK h5 hT
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [MonoidHom.map_closure, ← h]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_map]
  constructor
  · rintro ⟨x, ⟨hx, hxx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, hxx, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hyy⟩
    refine ⟨x, ⟨hx, e.injective ?_⟩, rfl⟩
    rw [map_mul, map_one]
    exact hyy

theorem harris82Lemma410Rest_holds : Harris82Lemma410Rest := by
  intro X _ _ p f _ _ h5 hX z hz hz1
  refine ⟨fun S₀ hS₀ x hx hxc => lemma410a_of_isCoverOf h5 hX hz hz1 hS₀ hx hxc,
    fun t ht htZ => ?_⟩
  obtain ⟨hc1, hc2⟩ := lemma410c_of_isCoverOf h5 hX hz hz1 ht htZ
  exact ⟨hc1, hc2, fun T₀ hT₀ => lemma410f_of_isCoverOf h5 hX ht htZ hT₀⟩

end CFSG.ComponentClassification.HarrisLit.T1
