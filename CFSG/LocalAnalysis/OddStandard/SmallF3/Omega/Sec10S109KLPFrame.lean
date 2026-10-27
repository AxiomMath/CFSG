module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPOut

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure KLTwo (L' B : Subgroup G) (φ φ' : (Fin 5 → ZMod 2) → G) : Prop where
  coord : KLCoord B φ
  perm' : IsPermModuleVia IsEvenVec φ' B (L' ⊓ normalizer (B : Set G)) (alternatingGroup (Fin 5))
  h4' : ∀ v, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L' (φ' v)
  h2' : ∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L' (φ' v)
  stab : KLStab L' φ

variable {L' B : Subgroup G} {φ φ' : (Fin 5 → ZMod 2) → G}

theorem KLTwo.eq_F_of_i4 (h : KLTwo L' B φ φ') {x : G} (hx : x ∈ B) (hi : IsI4PlusIn L' x) :
    ∃ j, x = φ' (klF j) := by
  have hc' := KLCoord.of_perm h.perm'
  obtain ⟨v, hv, rfl⟩ := (hc'.mem x).1 hx
  rcases even_weight_cases_five v hv with h0 | h2 | h4
  · exfalso
    rw [h0, hc'.map_zero] at hi
    have := hi.1
    rw [orderOf_one] at this
    omega
  · exact absurd hi (h.h2' v hv h2)
  · obtain ⟨j, rfl⟩ := kl_eq_F_of_weight_four v h4
    exact ⟨j, rfl⟩

theorem kl_frame_i4 (h : KLTwo L' B φ φ') : ∀ i, IsI4PlusIn L' (φ (klF i)) := by
  classical
  have hc := h.coord
  have hc' := KLCoord.of_perm h.perm'
  have hex : ∀ j, ∃ v, IsEvenVec v ∧ φ v = φ' (klF j) := fun j =>
    (hc.mem _).1 (hc'.mem_of_even (kl_isEven_F j))
  choose ψ hψe hψ using hex
  have hI4 : ∀ j, IsI4PlusIn L' (φ' (klF j)) := fun j =>
    h.h4' _ (kl_isEven_F j) (kl_weight_F j)
  have hψinj : Function.Injective ψ := by
    intro i j hij
    have e : φ' (klF i) = φ' (klF j) := by rw [← hψ i, ← hψ j, hij]
    exact kl_F_injective (hc'.inj _ _ (kl_isEven_F i) (kl_isEven_F j) e)
  have hψne : ∀ j, ψ j ≠ 0 := by
    intro j h0
    have h1 : φ' (klF j) = 1 := by rw [← hψ j, h0, hc.map_zero]
    have := (hI4 j).1
    rw [h1, orderOf_one] at this
    omega
  have key := kl_frame_lemma (Finset.univ.image ψ)
    (by rw [Finset.card_image_of_injective _ hψinj]; simp)
    (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      exact hψe j)
    (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      exact hψne j)
    (by
      intro σ hσ hσ0 v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨m, hm, hmact⟩ := h.stab σ hσ hσ0
      have hφ : φ (permVec σ (ψ j)) = m * φ' (klF j) * m⁻¹ := by
        rw [← hψ j, hmact _ (hψe j)]
      have hBmem : φ (permVec σ (ψ j)) ∈ B := hc.mem_of_even (kl_even_perm σ (hψe j))
      have hi4 : IsI4PlusIn L' (φ (permVec σ (ψ j))) := by
        rw [hφ]
        exact kl_isI4PlusIn_conj hm (hI4 j)
      obtain ⟨j', hj'⟩ := h.eq_F_of_i4 hBmem hi4
      refine Finset.mem_image.2 ⟨j', Finset.mem_univ _, ?_⟩
      exact hc.inj _ _ (hψe j') (kl_even_perm σ (hψe j)) ((hψ j').trans hj'.symm))
    (by
      intro a ha b hb c hc3 hab hac hbc habc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hc3
      have hij : klF i ≠ klF j := fun e => hab (by rw [kl_F_injective e])
      have hik : klF i ≠ klF k := fun e => hac (by rw [kl_F_injective e])
      have hjk : klF j ≠ klF k := fun e => hbc (by rw [kl_F_injective e])
      refine kl_three_weight_four (klF i) (klF j) (klF k) (kl_weight_F i) (kl_weight_F j)
        (kl_weight_F k) hij hik hjk ?_
      have h1 : φ' (klF i) * φ' (klF j) * φ' (klF k) = 1 := by
        rw [← hψ i, ← hψ j, ← hψ k, ← hc.add _ _ (hψe i) (hψe j),
          ← hc.add _ _ (kl_even_add (hψe i) (hψe j)) (hψe k), habc, hc.map_zero]
      refine hc'.inj _ _ (kl_even_add (kl_even_add (kl_isEven_F i) (kl_isEven_F j))
        (kl_isEven_F k)) kl_even_zero ?_
      rw [hc'.add _ _ (kl_even_add (kl_isEven_F i) (kl_isEven_F j)) (kl_isEven_F k),
        hc'.add _ _ (kl_isEven_F i) (kl_isEven_F j), hc'.map_zero]
      exact h1)
  intro i
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (key i)
  rw [← hj, hψ j]
  exact hI4 j

theorem kl_swap_pair (h : KLTwo L' B φ φ') :
    ∃ n ∈ L' ⊓ normalizer (B : Set G), n * φ (klF 0) * n⁻¹ = φ (klF 2) ∧
      n * φ (klF 1) * n⁻¹ = φ (klF 3) := by
  have hc := h.coord
  have hI4 := kl_frame_i4 h
  have hex : ∀ i, ∃ j, φ (klF i) = φ' (klF j) := fun i =>
    h.eq_F_of_i4 (hc.mem_of_even (kl_isEven_F i)) (hI4 i)
  choose π hπ using hex
  have hπinj : Function.Injective π := by
    intro i j hij
    have e : φ (klF i) = φ (klF j) := by rw [hπ i, hπ j, hij]
    exact kl_F_injective (hc.inj _ _ (kl_isEven_F i) (kl_isEven_F j) e)
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := kl_alt_two_trans (π 0) (π 1) (π 2) (π 3)
    (hπinj.ne (by decide)) (hπinj.ne (by decide))
  obtain ⟨n, hn, hnact⟩ := h.perm'.2.2.2.2 σ hσ
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hπ 0, hnact _ (kl_isEven_F _), kl_permVec_F, hσ0, ← hπ 2]
  · rw [hπ 1, hnact _ (kl_isEven_F _), kl_permVec_F, hσ1, ← hπ 3]

end CFSG.OddStandard.SmallF3.Omega
