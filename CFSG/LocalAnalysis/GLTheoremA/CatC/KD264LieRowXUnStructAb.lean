module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructEig
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_isPrimitiveRoot_three [Finite K] (hK : Nat.card K = 4) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [card_units_eq_three hK] at hg
  exact ⟨(g : K), IsPrimitiveRoot.coe_units_iff.mpr (hg ▸ IsPrimitiveRoot.orderOf g)⟩

theorem pow_three_of_ne_zero [Finite K] (hK : Nat.card K = 4) {a : K} (ha : a ≠ 0) :
    a ^ 3 = 1 := by
  have h := congrArg (fun u : Kˣ => (u : K)) (units_pow_three hK (Units.mk0 a ha))
  simpa using h

theorem toLinearMap_pow_three {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1) : (g : V →ₗ[K] V) ^ 3 = 1 := by
  ext v
  have := congrArg (fun e : V ≃ₗ[K] V => e v) hg3
  simpa [LinearEquiv.pow_apply, Module.End.pow_apply] using this

theorem repr_apply_of_eigen {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) (f : V →ₗ[K] V)
    (μ : ι → K) (hf : ∀ j, f (b j) = μ j • b j) (v : V) (i : ι) :
    b.repr (f v) i = μ i * b.repr v i := by
  have hv : f v = ∑ j, (μ j * b.repr v j) • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hf, smul_smul, mul_comm]
  rw [hv]
  exact congrFun (b.repr_sum_self fun j => μ j * b.repr v j) i

theorem exists_eq_smul_of_unique_weight {ι T : Type*} [Fintype ι] (b : Module.Basis ι K V)
    (f : T → V →ₗ[K] V) (μ : T → ι → K) (hf : ∀ t j, f t (b j) = μ t j • b j) {j : ι}
    (hj : ∀ i, i ≠ j → ∃ t, μ t i ≠ μ t j) (x : V →ₗ[K] V)
    (hx : ∀ t v, f t (x v) = x (f t v)) : ∃ c : K, x (b j) = c • b j := by
  classical
  refine ⟨b.repr (x (b j)) j, ?_⟩
  have hzero : ∀ i, i ≠ j → b.repr (x (b j)) i = 0 := by
    intro i hi
    obtain ⟨t, ht⟩ := hj i hi
    have h1 : b.repr (f t (x (b j))) i = μ t i * b.repr (x (b j)) i :=
      repr_apply_of_eigen b (f t) (μ t) (hf t) _ i
    have h2 : f t (x (b j)) = μ t j • x (b j) := by rw [hx, hf, map_smul]
    rw [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h3 : (μ t i - μ t j) * b.repr (x (b j)) i = 0 := by rw [sub_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) ht
    · exact h
  conv_lhs => rw [← b.sum_repr (x (b j))]
  rw [Finset.sum_eq_single j]
  · intro i _ hi
    rw [hzero i hi, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem card_le_three_pow_card_image [Finite K] (hK : Nat.card K = 4) {ι T : Type*} [Fintype ι]
    [Finite T] (μ : T → ι → K) (hμ0 : ∀ t j, μ t j ≠ 0) (hinj : Function.Injective μ)
    [DecidableEq (T → K)] :
    Nat.card T ≤ 3 ^ (Finset.univ.image (fun j t => μ t j)).card := by
  classical
  set S : Finset (T → K) := Finset.univ.image (fun j t => μ t j) with hS
  have hne : ∀ (t : T) (χ : S), (χ : T → K) t ≠ 0 := by
    intro t χ
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 χ.2
    rw [← hj]
    exact hμ0 t j
  let Ψ : T → (S → Kˣ) := fun t χ => Units.mk0 ((χ : T → K) t) (hne t χ)
  have hΨ : Function.Injective Ψ := by
    intro t t' h
    apply hinj
    funext j
    have hj : (fun t => μ t j) ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have := congrArg (fun u : S → Kˣ => ((u ⟨_, hj⟩ : Kˣ) : K)) h
    simpa [Ψ] using this
  have h1 := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_fun, card_units_eq_three hK, Nat.card_eq_finsetCard] at h1
  exact h1

theorem finrank_le_six_of_abelian [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {x : V ≃ₗ[K] V} (hx : x ∈ Q) (hx3 : x ^ 3 ≠ 1)
    (hcard : 3 ^ (Module.finrank K V - 2) ≤ Nat.card Q) : Module.finrank K V ≤ 6 := by
  classical
  by_contra hN
  have hN7 : 7 ≤ Module.finrank K V := by omega
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
  have h2 : 3 ^ (Module.finrank K V - 2) ≤ 3 ^ (k + 1) := by
    calc 3 ^ (Module.finrank K V - 2) ≤ Nat.card Q := hcard
      _ ≤ 3 * Nat.card T := hTcard
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left _ h1
      _ = 3 ^ (k + 1) := by rw [pow_succ]; ring
  have h3 : Module.finrank K V - 2 ≤ k + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hsing : ∃ j : Fin (Module.finrank K V), ∀ i, i ≠ j → ∃ t, μ t i ≠ μ t j := by
    by_contra hcon
    push Not at hcon
    have hle : 2 * k ≤ Module.finrank K V := by
      have := Finset.mul_card_image_le_card
        (f := fun (j : Fin (Module.finrank K V)) (t : T) => μ t j) (Finset.univ) 2 ?_
      · simpa using this
      · intro χ hχ
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hχ
        obtain ⟨i, hi, hall⟩ := hcon j
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
    omega
  obtain ⟨j, hj⟩ := hsing
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

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
