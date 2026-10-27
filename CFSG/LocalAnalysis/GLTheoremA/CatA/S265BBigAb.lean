module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructAb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BBig

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem card_le_of_abelian_cube [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {x : V ≃ₗ[K] V} (hx : x ∈ Q) (hx3 : x ^ 3 ≠ 1) :
    Nat.card Q ≤ 3 ^ (1 + Module.finrank K V / 2) := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hZ := scalarLike_scalars (V := V) hK
  obtain ⟨T, hTQ, hT3, hTQ3, hTcard⟩ := exists_cube_kernel_of_good hZ hQ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hK
  have hcomm : ∀ s t : T, Commute ((s : V ≃ₗ[K] V) : V →ₗ[K] V) ((t : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    intro s t
    have h : ((s : V ≃ₗ[K] V) : V →ₗ[K] V) * ((t : V ≃ₗ[K] V) : V →ₗ[K] V) =
        ((t : V ≃ₗ[K] V) : V →ₗ[K] V) * ((s : V ≃ₗ[K] V) : V →ₗ[K] V) := by
      refine LinearMap.ext fun v => ?_
      have := congrArg (fun e : V ≃ₗ[K] V => e v) (hab s (hTQ s.2) t (hTQ t.2))
      simpa using this
    exact h
  have hpow : ∀ t : T, ((t : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 3 = 1 := fun t =>
    toLinearMap_pow_three (hT3 t t.2)
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ
    (fun t : T => ((t : V ≃ₗ[K] V) : V →ₗ[K] V)) hcomm hpow
  have hμ0 : ∀ t j, μ t j ≠ 0 := by
    intro t j h0
    have h1 := hb t j
    rw [h0, zero_smul] at h1
    exact b.ne_zero j ((t : V ≃ₗ[K] V).map_eq_zero_iff.1 h1)
  have hinj : Function.Injective μ := by
    intro t t' h
    apply Subtype.ext
    have h1 : ((t : V ≃ₗ[K] V) : V →ₗ[K] V) = ((t' : V ≃ₗ[K] V) : V →ₗ[K] V) :=
      b.ext fun j => by rw [hb t j, hb t' j, h]
    exact LinearEquiv.ext fun v => LinearMap.congr_fun h1 v
  have h1 := card_le_three_pow_card_image hK μ hμ0 hinj
  set k := (Finset.univ.image (fun j t => μ t j)).card with hk
  have hnsing : ¬ ∃ j : Fin (Module.finrank K V), ∀ i, i ≠ j → ∃ t, μ t i ≠ μ t j := by
    rintro ⟨j, hj⟩
    obtain ⟨c, hc⟩ := exists_eq_smul_of_unique_weight b
      (fun t : T => ((t : V ≃ₗ[K] V) : V →ₗ[K] V)) μ hb hj (x : V →ₗ[K] V) (by
        intro t v
        have := congrArg (fun e : V ≃ₗ[K] V => e v) (hab t (hTQ t.2) x hx)
        simpa using this)
    obtain ⟨ω, hω⟩ := mem_scalars_iff.1 (hQ.2 x hx)
    have hx3j : (x ^ 3) (b j) = c ^ 3 • b j := pow_three_apply hc
    rw [hω] at hx3j
    have hωc : (ω : K) = c ^ 3 := by
      have h4 : ((ω : K) - c ^ 3) • b j = 0 := by rw [sub_smul, hx3j, sub_self]
      rcases smul_eq_zero.1 h4 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h (b.ne_zero j)
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : (ω : K) = 0 := by rw [hωc]; ring
      exact ω.ne_zero this
    have hω1 : (ω : K) = 1 := by rw [hωc, pow_three_of_ne_zero hK hc0]
    apply hx3
    refine LinearEquiv.ext fun v => ?_
    rw [hω, hω1, one_smul]
    rfl
  push Not at hnsing
  have hle : 2 * k ≤ Module.finrank K V := by
    have := Finset.mul_card_image_le_card
      (f := fun (j : Fin (Module.finrank K V)) (t : T) => μ t j) (Finset.univ) 2 ?_
    · simpa using this
    · intro χ hχ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hχ
      obtain ⟨i, hi, hall⟩ := hnsing j
      have hsub : ({j, i} : Finset (Fin (Module.finrank K V))) ⊆
          Finset.univ.filter (fun a => (fun t => μ t a) = (fun t => μ t j)) := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · simp
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact funext hall
      calc 2 = ({j, i} : Finset (Fin (Module.finrank K V))).card :=
            (Finset.card_pair hi.symm).symm
        _ ≤ _ := Finset.card_le_card hsub
  calc Nat.card Q ≤ 3 * Nat.card T := hTcard
    _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left _ h1
    _ ≤ 3 * 3 ^ (Module.finrank K V / 2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 3 ^ (1 + Module.finrank K V / 2) := by rw [pow_add, pow_one]

end CFSG.LocalAnalysis.GLTheoremA.S265.BBig

end
