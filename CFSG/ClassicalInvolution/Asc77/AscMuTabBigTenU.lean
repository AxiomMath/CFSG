module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBigTen

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open scoped MatrixGroups

namespace MuTab

section Diag

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem diagSU_pairDiag_mem_LcU {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u : normOne (unitaryInvolution K p f)) :
    diagSU (unitaryInvolution K p f) (pairDiag i j u)
        ((mem_detKer (σ := unitaryInvolution K p f)).mpr (prod_pairDiag hij u)) ∈
      LcU K p f (n := n) ⟨{i, j}, Finset.card_pair hij⟩ := by
  show _ ∈ longRootGroupSU K p f (zMat K n {i, j})
  rw [mem_longRootGroupSU]
  constructor
  · show Matrix.diagonal (fun l => (((pairDiag i j u l : normOne (unitaryInvolution K p f)) :
        Kˣ) : K)) * zMat K n {i, j} = zMat K n {i, j} * Matrix.diagonal
        (fun l => (((pairDiag i j u l : normOne (unitaryInvolution K p f)) : Kˣ) : K))
    rw [zMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    exact mul_comm _ _
  · show Matrix.diagonal (fun l => (((pairDiag i j u l : normOne (unitaryInvolution K p f)) :
        Kˣ) : K)) * (1 + zMat K n {i, j}) = 1 + zMat K n {i, j}
    rw [zMat, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    by_cases hli : l = i
    · subst hli
      simp [pairDiag]
    · by_cases hlj : l = j
      · subst hlj
        simp [pairDiag, hli]
      · simp [pairDiag, hli, hlj]

theorem orderOf_diagSUHom_pairDiag {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u : normOne (unitaryInvolution K p f)) :
    orderOf (diagSUHom (unitaryInvolution K p f) n
        ⟨pairDiag i j u, (mem_detKer (σ := unitaryInvolution K p f)).mpr (prod_pairDiag hij u)⟩) =
      orderOf u := by
  rw [orderOf_injective (diagSUHom (unitaryInvolution K p f) n) (diagSUHom_injective n)]
  rw [orderOf_eq_orderOf_iff]
  intro m
  have hpow : (⟨pairDiag i j u, (mem_detKer (σ := unitaryInvolution K p f)).mpr
      (prod_pairDiag hij u)⟩ : detKer (unitaryInvolution K p f) n) ^ m =
      ⟨pairDiag i j (u ^ m), (mem_detKer (σ := unitaryInvolution K p f)).mpr
        (prod_pairDiag hij (u ^ m))⟩ :=
    Subtype.ext (pairDiag_pow i j u m)
  rw [hpow]
  constructor
  · intro h
    have := congrArg (fun d : detKer (unitaryInvolution K p f) n => d.1 i) h
    simpa [pairDiag] using this
  · intro h
    refine Subtype.ext (funext fun l => ?_)
    rw [h]
    simp [pairDiag]

end Diag

section Ten

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem shapeBig10_psu5 (M : Ih8Model p f Ω .PSU 5 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) : ShapeBig10 Ω := by
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSU = .PSL ∧ (5 : ℕ) = 2) := by simp
  have he := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have h2 : (2 : GaloisField p (2 * e)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hcardF : Nat.card (GaloisField p e) = p ^ e := natCard_galoisField_eq' hf1
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 M.admissible
  obtain ⟨u₀, hu₀⟩ := exists_orderOf_two_part
    (normOne (unitaryInvolution (GaloisField p (2 * e)) p e))
  have hcard : 2 * 2 ^ (Nat.card (normOne (unitaryInvolution (GaloisField p (2 * e)) p e))
      ).factorization 2 = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 := by
    subst he
    rw [Phan.card_normOne hK, two_pow_sl2_three_mod_four (GaloisField p e)
      (by rw [hcardF]; exact hq3), hcardF]
  let T : Fin 10 → Pair 5 := fun k =>
    ⟨{(pairs5 k).1, (pairs5 k).2}, Finset.card_pair (ne_of_lt (pairs5_lt k))⟩
  let R : Fin 10 → Subgroup (modelUniv .PSU 5 p e Fact.out).K := fun k =>
    (LcU (GaloisField p (2 * e)) p e (T k)).map φ.symm.toMonoidHom
  have hRmem : ∀ k, R k ∈ M.cls := by
    intro k
    refine M.fund_subset_cls hne hG2 hD4 ((hφ _).mpr ?_)
    rw [muTab_map_equiv_symm_map]
    exact LcU_mem_longRootSetU h2 _ (T k)
  let y : Fin 10 → Su (GaloisField p (2 * e)) p e 5 := fun k =>
    diagSUHom (unitaryInvolution (GaloisField p (2 * e)) p e) 5
      ⟨pairDiag (pairs5 k).1 (pairs5 k).2 u₀, (mem_detKer (σ := unitaryInvolution
        (GaloisField p (2 * e)) p e)).mpr (prod_pairDiag (ne_of_lt (pairs5_lt k)) u₀)⟩
  have hy_mem : ∀ k, y k ∈ LcU (GaloisField p (2 * e)) p e (T k) := fun k =>
    diagSU_pairDiag_mem_LcU (ne_of_lt (pairs5_lt k)) u₀
  have hy_ord : ∀ k, orderOf (y k) = 2 ^ (Nat.card (normOne (unitaryInvolution
      (GaloisField p (2 * e)) p e))).factorization 2 := fun k =>
    (orderOf_diagSUHom_pairDiag (ne_of_lt (pairs5_lt k)) u₀).trans hu₀
  let Q₀ : Subgroup (Su (GaloisField p (2 * e)) p e 5) :=
    (CommGroup.primaryComponent (detKer (unitaryInvolution (GaloisField p (2 * e)) p e) 5) 2).map
      (diagSUHom (unitaryInvolution (GaloisField p (2 * e)) p e) 5)
  have hQ₀ : IsPGroup 2 Q₀ := CommGroup.primaryComponent.isPGroup.map _
  have hy_Q : ∀ k, y k ∈ Q₀ := by
    intro k
    refine ⟨⟨pairDiag (pairs5 k).1 (pairs5 k).2 u₀, (mem_detKer (σ := unitaryInvolution
      (GaloisField p (2 * e)) p e)).mpr (prod_pairDiag (ne_of_lt (pairs5_lt k)) u₀)⟩, ?_, rfl⟩
    refine ⟨(Nat.card (normOne (unitaryInvolution (GaloisField p (2 * e)) p e))).factorization 2,
      ?_⟩
    refine Subtype.ext ?_
    show (pairDiag (pairs5 k).1 (pairs5 k).2 u₀) ^ 2 ^ (Nat.card (normOne (unitaryInvolution
      (GaloisField p (2 * e)) p e))).factorization 2 = 1
    rw [pairDiag_pow, ← hu₀, pow_orderOf_eq_one]
    funext l
    simp [pairDiag]
  refine ⟨fun k => (R k).map M.ψ, fun k => Subgroup.zpowers (M.ψ (φ.symm (y k))),
    (Q₀.map φ.symm.toMonoidHom).map M.ψ, ?_, (hQ₀.map _).map _,
    fun k => ⟨M.map_mem (hRmem k), ?_, ?_, ?_⟩⟩
  · intro k l h
    have h1 := M.muTab_map_inj hp2 hq hD4 (hRmem k) (hRmem l) h
    have h3 := Subgroup.map_injective φ.symm.injective h1
    exact pairs5_inj k l (congrArg Subtype.val (LcU_injective hK hp2 (by omega) h3))
  · refine M.muTab_mem_USet hΩ hnpsl (hRmem k) (Subgroup.mem_map_of_mem _ (hy_mem k)) ?_ hcard
    rw [MulEquiv.orderOf_eq]
    exact hy_ord k
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hy_mem k)))
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hy_Q k)))

end Ten

end MuTab

end CFSG.ClassicalInvolution.Asc77
