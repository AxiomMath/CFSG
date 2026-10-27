module

public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem blockEmb4_comp_blockEmb2 {a : ℕ} (h4 : a + 4 ≤ n + 1) (k : Fin 3) :
    (blockEmb K p f (n + 1) 4 a h4).comp (blockEmb2 K p f 3 k) =
      blockEmb2 K p f n ⟨a + k, by omega⟩ :=
  blockEmb_comp h4 (by omega)

theorem blockSup_typeInt_three (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {a : ℕ}
    (ha : a + 2 < n) :
    blockSup K p f n (typeInt n a (a + 3)) =
      (blockEmb K p f (n + 1) 4 a (by omega)).range := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := hj
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, j.val = a + k.val :=
      ⟨⟨j.val - a, by omega⟩, by simp only; omega⟩
    have hjk : (⟨a + k.val, by omega⟩ : Fin n) = j := Fin.ext hk.symm
    rw [← hjk, ← blockEmb4_comp_blockEmb2 (by omega) k, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · rw [MonoidHom.range_eq_map, ← sup_range_blockEmb2_three hK hq, Subgroup.map_sup,
      Subgroup.map_sup]
    have hk : ∀ k : Fin 3, ((blockEmb2 K p f 3 k).range).map (blockEmb K p f (n + 1) 4 a
        (by omega)) ≤ blockSup K p f n (typeInt n a (a + 3)) := by
      intro k
      rw [← MonoidHom.range_comp, blockEmb4_comp_blockEmb2 (by omega) k]
      exact range_blockEmb2_le_blockSup ⟨by simp only; omega, by simp only; omega⟩
    exact sup_le (sup_le (hk 0) (hk 1)) (hk 2)

theorem mem_torus_of_blockEmb_mem_torus {m k i : ℕ} (h : i + k ≤ m) {A : Su K p f k}
    (hA : blockEmb K p f m k i h A ∈ torus (unitaryInvolution K p f) m) :
    A ∈ torus (unitaryInvolution K p f) k := by
  rw [mem_torus_iff] at hA ⊢
  intro x y hxy
  have h1 := hA (blockIdx i h x) (blockIdx i h y) (fun h' => hxy (blockIdx_injective _ h'))
  rw [coe_coe_blockEmb, blockMat_apply_blockIdx] at h1
  exact h1

theorem exists_blockEmb4_diag {a : ℕ} (ha : a + 2 < n) {A : Su K p f 4}
    (hA : blockEmb K p f (n + 1) 4 a (by omega) A ∈ torus (unitaryInvolution K p f) (n + 1)) :
    ∃ u v w : normOne (unitaryInvolution K p f),
      blockEmb K p f (n + 1) 4 a (by omega) A =
        blockEmb2 K p f n ⟨a, by omega⟩ (torusTwo (unitaryInvolution K p f) u) *
          blockEmb2 K p f n ⟨a + 1, by omega⟩ (torusTwo (unitaryInvolution K p f) v) *
          blockEmb2 K p f n ⟨a + 2, ha⟩ (torusTwo (unitaryInvolution K p f) w) := by
  have hAT : A ∈ torus (unitaryInvolution K p f) 4 := mem_torus_of_blockEmb_mem_torus _ hA
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 3).surjective ⟨A, hAT⟩
  have hsA : A = ((torusEquiv (unitaryInvolution K p f) 3 s :
      torus (unitaryInvolution K p f) 4) : Su K p f 4) := by rw [hs]
  have hs3 : s = Pi.mulSingle (0 : Fin 3) (s 0) * Pi.mulSingle (1 : Fin 3) (s 1) *
      Pi.mulSingle (2 : Fin 3) (s 2) := by
    funext x
    fin_cases x <;> simp
  have h3 := congrArg (torusEquiv (unitaryInvolution K p f) 3) hs3
  rw [map_mul, map_mul] at h3
  refine ⟨s 0, s 1, s 2, ?_⟩
  rw [hsA, h3, Subgroup.coe_mul, Subgroup.coe_mul, coe_torusEquiv_mulSingle,
    coe_torusEquiv_mulSingle, coe_torusEquiv_mulSingle, map_mul, map_mul]
  have e0 := DFunLike.congr_fun (blockEmb4_comp_blockEmb2 (K := K) (p := p) (f := f)
    (by omega : a + 4 ≤ n + 1) 0) (torusTwo (unitaryInvolution K p f) (s 0))
  have e1 := DFunLike.congr_fun (blockEmb4_comp_blockEmb2 (K := K) (p := p) (f := f)
    (by omega : a + 4 ≤ n + 1) 1) (torusTwo (unitaryInvolution K p f) (s 1))
  have e2 := DFunLike.congr_fun (blockEmb4_comp_blockEmb2 (K := K) (p := p) (f := f)
    (by omega : a + 4 ≤ n + 1) 2) (torusTwo (unitaryInvolution K p f) (s 2))
  exact congrArg₂ _ (congrArg₂ _ e0 e1) e2

end CFSG.ClassicalInvolution.Phan.Q3G
