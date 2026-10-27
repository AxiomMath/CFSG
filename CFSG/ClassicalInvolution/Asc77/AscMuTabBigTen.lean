module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem muTab_mem_USet (hΩ : HypOmegaMod p f Ω) (hnpsl : ¬ (t = .PSL ∧ k = 2))
    {S : Subgroup (modelUniv t k p e Fact.out).K} (hS : S ∈ M.cls) {u : _} (hu : u ∈ S) {a : ℕ}
    (hord : orderOf u = 2 ^ a)
    (hcard : 2 * 2 ^ a = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2) :
    Subgroup.zpowers (M.ψ u) ∈ USet Ω := by
  have hord' : orderOf (M.ψ u) = 2 ^ a := (M.muTab_orderOf_map hnpsl hS hu).trans hord
  have hcardT : Nat.card (Subgroup.zpowers (M.ψ u)) = 2 ^ a := by
    rw [Nat.card_zpowers, hord']
  have hT2 : IsPGroup 2 (Subgroup.zpowers (M.ψ u)) := IsPGroup.of_card hcardT
  have hTJ : Subgroup.zpowers (M.ψ u) ≤ S.map M.ψ :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hu)
  obtain ⟨R, -, hRJ, hTR⟩ := exists_mem_RSet_ge (M.map_mem hS) hT2 hTJ
  have hRcard := hΩ.natCard_isSylow2In (M.map_mem hS) hRJ
  exact mem_USet_of_natCard (M.map_mem hS) hRJ hTR inferInstance
    (by rw [hRcard, ← hcard, hcardT])

end Ih8Model

namespace MuTab

section Diag

variable {F : Type} [Field F]

section PairDiag

variable {N : Type} [CommGroup N]

@[expose] def pairDiag {n : ℕ} (i j : Fin n) (a : N) : Fin n → N :=
  fun l => if l = i then a else if l = j then a⁻¹ else 1

theorem prod_pairDiag {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : N) :
    ∏ l, pairDiag i j a l = 1 := by
  rw [Fintype.prod_eq_mul i j hij (fun x hx => by simp [pairDiag, hx.1, hx.2])]
  simp [pairDiag, hij.symm]

theorem pairDiag_pow {n : ℕ} (i j : Fin n) (a : N) (m : ℕ) :
    pairDiag i j a ^ m = pairDiag i j (a ^ m) := by
  funext l
  simp only [Pi.pow_apply, pairDiag]
  split_ifs <;> simp [inv_pow]

end PairDiag

variable (F) in
@[expose] def prodOne (n : ℕ) : Subgroup (Fin n → Fˣ) where
  carrier := {d | ∏ l, d l = 1}
  mul_mem' {a b} ha hb := by
    change ∏ l, (a * b) l = 1
    change ∏ l, a l = 1 at ha
    change ∏ l, b l = 1 at hb
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, ha, hb, mul_one]
  one_mem' := by
    change ∏ l, (1 : Fin n → Fˣ) l = 1
    simp
  inv_mem' {a} ha := by
    change ∏ l, (a⁻¹) l = 1
    change ∏ l, a l = 1 at ha
    simp only [Pi.inv_apply, Finset.prod_inv_distrib, ha, inv_one]

variable (F) in
@[expose] noncomputable def dgHom (n : ℕ) : prodOne F n →* SL(n, F) where
  toFun d := ⟨Matrix.diagonal fun l => ((d.1 l : Fˣ) : F), by
    rw [Matrix.det_diagonal]
    have := congrArg (Units.coeHom F) d.2
    simpa [map_prod] using this⟩
  map_one' := Subtype.ext (by simp [Matrix.diagonal_one])
  map_mul' a b := Subtype.ext (by
    show Matrix.diagonal (fun l => (((a * b).1 l : Fˣ) : F)) =
      Matrix.diagonal (fun l => ((a.1 l : Fˣ) : F)) *
        Matrix.diagonal (fun l => ((b.1 l : Fˣ) : F))
    rw [Matrix.diagonal_mul_diagonal]
    rfl)

theorem coe_dgHom {n : ℕ} (d : prodOne F n) :
    ((dgHom F n d : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun l => ((d.1 l : Fˣ) : F) := rfl

theorem dgHom_injective (n : ℕ) : Function.Injective (dgHom F n) := by
  intro a b h
  have h' := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F)) h
  simp only [coe_dgHom] at h'
  refine Subtype.ext (funext fun l => Units.ext ?_)
  have := Matrix.diagonal_injective h'
  exact congrFun this l

theorem dgHom_pairDiag_mem_Lc {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : Fˣ) :
    dgHom F n ⟨pairDiag i j a, prod_pairDiag hij a⟩ ∈
      Lc F (n := n) ⟨{i, j}, Finset.card_pair hij⟩ := by
  rw [mem_Lc]
  constructor
  · show Matrix.diagonal (fun l => ((pairDiag i j a l : Fˣ) : F)) * zMat F n {i, j} =
      zMat F n {i, j} * Matrix.diagonal (fun l => ((pairDiag i j a l : Fˣ) : F))
    rw [zMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    exact mul_comm _ _
  · show Matrix.diagonal (fun l => ((pairDiag i j a l : Fˣ) : F)) * (1 + zMat F n {i, j}) =
      1 + zMat F n {i, j}
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

theorem orderOf_dgHom_pairDiag {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : Fˣ) :
    orderOf (dgHom F n ⟨pairDiag i j a, prod_pairDiag hij a⟩) = orderOf a := by
  rw [orderOf_injective (dgHom F n) (dgHom_injective n)]
  rw [orderOf_eq_orderOf_iff]
  intro m
  have hpow : (⟨pairDiag i j a, prod_pairDiag hij a⟩ : prodOne F n) ^ m =
      ⟨pairDiag i j (a ^ m), prod_pairDiag hij (a ^ m)⟩ :=
    Subtype.ext (pairDiag_pow i j a m)
  rw [hpow]
  constructor
  · intro h
    have := congrArg (fun d : prodOne F n => d.1 i) h
    simpa [pairDiag] using this
  · intro h
    refine Subtype.ext (funext fun l => ?_)
    rw [h]
    simp [pairDiag]

end Diag

section Ten

@[expose] def pairs5 : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem pairs5_lt : ∀ k, (pairs5 k).1 < (pairs5 k).2 := by decide

theorem pairs5_inj : ∀ k l, ({(pairs5 k).1, (pairs5 k).2} : Finset (Fin 5)) =
    {(pairs5 l).1, (pairs5 l).2} → k = l := by decide

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem shapeBig10_psl5 (M : Ih8Model p f Ω .PSL 5 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq1 : p ^ f % 4 = 1) : ShapeBig10 Ω := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (5 : ℕ) = 2) := by simp
  have he := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hcardF : Nat.card (GaloisField p e) = p ^ e := natCard_galoisField_eq' hf1
  obtain ⟨a₀, ha₀⟩ := exists_orderOf_two_part (GaloisField p e)ˣ
  have hcard : 2 * 2 ^ (Nat.card (GaloisField p e)ˣ).factorization 2 =
      2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 := by
    subst he
    rw [two_pow_sl2_one_mod_four (GaloisField p e) (by rw [hcardF]; exact hq1),
      natCard_units_eq']
  let T : Fin 10 → Pair 5 := fun k =>
    ⟨{(pairs5 k).1, (pairs5 k).2}, Finset.card_pair (ne_of_lt (pairs5_lt k))⟩
  have hLmem : ∀ k, Lc (GaloisField p e) (T k) ∈ M.cls := by
    intro k
    have h1 : Lc (GaloisField p e) (T k) ∈ longRootSet (K := GaloisField p e) (by omega : 2 ≤ 5) :=
      Lc_mem_longRootSet h2 _ (T k)
    have h4 := fundamentalSubgroups_psl_eq (p := p) (f := e) (m := 4) (by norm_num)
    exact M.fund_subset_cls hne hG2 hD4 (by rw [h4]; exact h1)
  let y : Fin 10 → SL(5, GaloisField p e) := fun k =>
    dgHom (GaloisField p e) 5
      ⟨pairDiag (pairs5 k).1 (pairs5 k).2 a₀, prod_pairDiag (ne_of_lt (pairs5_lt k)) a₀⟩
  have hy_mem : ∀ k, y k ∈ Lc (GaloisField p e) (T k) := fun k =>
    dgHom_pairDiag_mem_Lc (ne_of_lt (pairs5_lt k)) a₀
  have hy_ord : ∀ k, orderOf (y k) = 2 ^ (Nat.card (GaloisField p e)ˣ).factorization 2 :=
    fun k => (orderOf_dgHom_pairDiag (ne_of_lt (pairs5_lt k)) a₀).trans ha₀
  let Q₀ : Subgroup SL(5, GaloisField p e) :=
    (CommGroup.primaryComponent (prodOne (GaloisField p e) 5) 2).map (dgHom (GaloisField p e) 5)
  have hQ₀ : IsPGroup 2 Q₀ := CommGroup.primaryComponent.isPGroup.map _
  have hy_Q : ∀ k, y k ∈ Q₀ := by
    intro k
    refine ⟨⟨pairDiag (pairs5 k).1 (pairs5 k).2 a₀, prod_pairDiag (ne_of_lt (pairs5_lt k)) a₀⟩,
      ?_, rfl⟩
    refine ⟨(Nat.card (GaloisField p e)ˣ).factorization 2, ?_⟩
    refine Subtype.ext ?_
    show (pairDiag (pairs5 k).1 (pairs5 k).2 a₀) ^ 2 ^ (Nat.card (GaloisField p e)ˣ).factorization 2
      = 1
    rw [pairDiag_pow, ← ha₀, pow_orderOf_eq_one]
    funext l
    simp [pairDiag]
  refine ⟨fun k => (Lc (GaloisField p e) (T k)).map M.ψ, fun k => Subgroup.zpowers (M.ψ (y k)),
    Q₀.map M.ψ, ?_, hQ₀.map M.ψ, fun k => ⟨M.map_mem (hLmem k), ?_, ?_, ?_⟩⟩
  · intro k l h
    have := M.muTab_map_inj hp2 hq hD4 (hLmem k) (hLmem l) h
    exact pairs5_inj k l (congrArg Subtype.val (Lc_injective h2 (by omega) this))
  · exact M.muTab_mem_USet hΩ hnpsl (hLmem k) (hy_mem k) (hy_ord k) hcard
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ (hy_mem k))
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ (hy_Q k))

end Ten

end MuTab

end CFSG.ClassicalInvolution.Asc77
