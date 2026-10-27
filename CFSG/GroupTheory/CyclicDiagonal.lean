module

public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjugatePower (a : G) (L : Subgroup G) (i : ℕ) : Subgroup G :=
  L.map (MulAut.conj (a ^ i)).toMonoidHom

theorem conjugatePower_add (a : G) (L : Subgroup G) (i j : ℕ) :
    conjugatePower a L (i + j) =
      (conjugatePower a L j).map (MulAut.conj (a ^ i)).toMonoidHom := by
  rw [conjugatePower, conjugatePower, Subgroup.map_map]
  congr 1
  ext x
  rw [MonoidHom.comp_apply]
  change MulAut.conj (a ^ (i + j)) x =
    MulAut.conj (a ^ i) (MulAut.conj (a ^ j) x)
  rw [pow_add, map_mul]
  rfl

theorem conjugatePower_mod (a : G) (L : Subgroup G) {r : ℕ} (ha : a ^ r = 1) (n : ℕ) :
    conjugatePower a L n = conjugatePower a L (n % r) := by
  have hpow : a ^ n = a ^ (n % r) := by
    conv_lhs => rw [← Nat.div_add_mod n r]
    rw [pow_add, pow_mul, ha, one_pow, one_mul]
  unfold conjugatePower
  rw [hpow]

@[expose] def ConjugatesCommute (a : G) (L : Subgroup G) (r : ℕ) : Prop :=
  ∀ i j : Fin r, i ≠ j →
    ∀ x ∈ conjugatePower a L (i : ℕ), ∀ y ∈ conjugatePower a L (j : ℕ), x * y = y * x

@[expose] def orbitDiagonalFactor (a : G) (r : ℕ) {L : Subgroup G} (y : ↥L) (i : Fin r) : G :=
  a ^ (i : ℕ) * (y : G) * (a ^ (i : ℕ))⁻¹

theorem orbitDiagonalFactor_mem_conjugatePower (a : G) (L : Subgroup G) (r : ℕ) (y : ↥L)
    (i : Fin r) : orbitDiagonalFactor a r y i ∈ conjugatePower a L (i : ℕ) := by
  rw [conjugatePower]
  change (MulAut.conj (a ^ (i : ℕ))) (y : G) ∈
    L.map ((MulAut.conj (a ^ (i : ℕ))).toMonoidHom)
  exact Subgroup.mem_map_of_mem _ y.2

theorem prod_ofFn_mul_ofFn_of_commute {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f g : Fin n → M),
      (∀ i j : Fin n, i ≠ j → Commute (f i) (f j)) →
      (∀ i j : Fin n, i ≠ j → Commute (g i) (g j)) →
      (∀ i j : Fin n, i ≠ j → Commute (f i) (g j)) →
      (List.ofFn (fun i => f i * g i)).prod =
        (List.ofFn f).prod * (List.ofFn g).prod
  | 0, _, _, _, _, _ => by simp
  | n + 1, f, g, hf, hg, hfg => by
      let f' : Fin n → M := fun i => f i.succ
      let g' : Fin n → M := fun i => g i.succ
      have hf_eq : f = Fin.cons (f 0) f' := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [f']
      have hg_eq : g = Fin.cons (g 0) g' := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [g']
      have hfg_eq : (fun i : Fin (n + 1) => f i * g i) =
          Fin.cons (f 0 * g 0) (fun i => f' i * g' i) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [f', g']
      rw [hfg_eq, hf_eq, hg_eq, List.ofFn_cons, List.ofFn_cons, List.ofFn_cons,
        List.prod_cons, List.prod_cons, List.prod_cons]
      rw [prod_ofFn_mul_ofFn_of_commute f' g'
        (fun i j hij => hf i.succ j.succ (by simpa using hij))
        (fun i j hij => hg i.succ j.succ (by simpa using hij))
        (fun i j hij => hfg i.succ j.succ (by simpa using hij))]
      have hcomm : Commute (g 0) (List.ofFn f').prod :=
        Commute.list_prod_right _ _ (fun x hx => by
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' f' x).1 hx
          exact (hfg i.succ 0 (by simp)).symm)
      calc (f 0 * g 0) * ((List.ofFn f').prod * (List.ofFn g').prod)
          = f 0 * (g 0 * (List.ofFn f').prod) * (List.ofFn g').prod := by group
        _ = f 0 * ((List.ofFn f').prod * g 0) * (List.ofFn g').prod := by rw [hcomm.eq]
        _ = (f 0 * (List.ofFn f').prod) * (g 0 * (List.ofFn g').prod) := by group

theorem pow_mul_pow_eq_pow_finRotate {a : G} {r : ℕ} (ha : a ^ r = 1) (i : Fin r) :
    a * a ^ (i : ℕ) = a ^ ((finRotate r i : Fin r) : ℕ) := by
  rcases r with _ | n
  · exact i.elim0
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.val_castSucc, coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]
    exact (pow_succ' a (j : ℕ)).symm
  · rw [Fin.val_last, finRotate_last]
    norm_num
    rw [show a * a ^ n = a ^ (n + 1) by group, ha]

@[expose] def orbitDiagonalHom (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) : ↥L →* G where
  toFun y := (List.ofFn (orbitDiagonalFactor a r y)).prod
  map_one' := by
    refine List.prod_eq_one ?_
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' (orbitDiagonalFactor a r (1 : ↥L)) x).1 hx
    simp [orbitDiagonalFactor]
  map_mul' y z := by
    have hpoint : orbitDiagonalFactor a r (y * z) =
        orbitDiagonalFactor a r y * orbitDiagonalFactor a r z := by
      funext i
      simp [orbitDiagonalFactor, mul_assoc]
    rw [hpoint]
    refine prod_ofFn_mul_ofFn_of_commute _ _ ?_ ?_ ?_
    · intro i j hij
      exact hcomm i j hij _ (orbitDiagonalFactor_mem_conjugatePower a L r y i) _
        (orbitDiagonalFactor_mem_conjugatePower a L r y j)
    · intro i j hij
      exact hcomm i j hij _ (orbitDiagonalFactor_mem_conjugatePower a L r z i) _
        (orbitDiagonalFactor_mem_conjugatePower a L r z j)
    · intro i j hij
      exact hcomm i j hij _ (orbitDiagonalFactor_mem_conjugatePower a L r y i) _
        (orbitDiagonalFactor_mem_conjugatePower a L r z j)

@[simp] theorem orbitDiagonalHom_apply (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) (y : ↥L) :
    orbitDiagonalHom a L r ha hcomm y = (List.ofFn (orbitDiagonalFactor a r y)).prod := rfl

theorem conjugate_orbitDiagonalHom (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) (y : ↥L) :
    a * orbitDiagonalHom a L r ha hcomm y * a⁻¹ = orbitDiagonalHom a L r ha hcomm y := by
  have hpair : List.Pairwise Commute (List.ofFn (orbitDiagonalFactor a r y)) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hcomm i j (ne_of_lt hij) _ (by
      rw [conjugatePower]; exact Subgroup.mem_map_of_mem _ y.2) _
      (by rw [conjugatePower]; exact Subgroup.mem_map_of_mem _ y.2)
  have hshift : ∀ i : Fin r,
      a * orbitDiagonalFactor a r y i * a⁻¹ = orbitDiagonalFactor a r y (finRotate r i) := by
    intro i
    rw [orbitDiagonalFactor, orbitDiagonalFactor]
    rw [show a * (a ^ (i : ℕ) * (y : G) * (a ^ (i : ℕ))⁻¹) * a⁻¹ =
        (a * a ^ (i : ℕ)) * (y : G) * (a * a ^ (i : ℕ))⁻¹ by group,
      pow_mul_pow_eq_pow_finRotate ha i]
  have hlist : List.ofFn (fun i => a * orbitDiagonalFactor a r y i * a⁻¹) =
      List.ofFn (fun i => orbitDiagonalFactor a r y (finRotate r i)) := by
    rw [List.ofFn_inj]
    funext i
    exact hshift i
  have hmap : (List.ofFn (orbitDiagonalFactor a r y)).map (MulAut.conj a).toMonoidHom =
      List.ofFn (fun i => a * orbitDiagonalFactor a r y i * a⁻¹) := by
    simp [List.ofFn_eq_map, List.map_map, Function.comp, MulAut.conj_apply]
  have hperm : (List.ofFn (fun i => orbitDiagonalFactor a r y (finRotate r i))).Perm
      (List.ofFn (orbitDiagonalFactor a r y)) :=
    Equiv.Perm.ofFn_comp_perm (finRotate r) (orbitDiagonalFactor a r y)
  have hprod : (List.ofFn (fun i => orbitDiagonalFactor a r y (finRotate r i))).prod =
      (List.ofFn (orbitDiagonalFactor a r y)).prod :=
    (List.Perm.prod_eq' hperm.symm hpair).symm
  change a * (List.ofFn (orbitDiagonalFactor a r y)).prod * a⁻¹ =
    (List.ofFn (orbitDiagonalFactor a r y)).prod
  rw [show a * (List.ofFn (orbitDiagonalFactor a r y)).prod * a⁻¹ =
      (MulAut.conj a) ((List.ofFn (orbitDiagonalFactor a r y)).prod) from rfl,
    ← List.prod_hom]
  change (List.map (⇑(MulAut.conj a).toMonoidHom)
    (List.ofFn (orbitDiagonalFactor a r y))).prod = (List.ofFn (orbitDiagonalFactor a r y)).prod
  rw [hmap, hlist, hprod]

theorem orbitDiagonalHom_mem_centralizer (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) (y : ↥L) :
    orbitDiagonalHom a L r ha hcomm y ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  have h := conjugate_orbitDiagonalHom a L r ha hcomm y
  calc a * orbitDiagonalHom a L r ha hcomm y
      = (a * orbitDiagonalHom a L r ha hcomm y * a⁻¹) * a := by group
    _ = orbitDiagonalHom a L r ha hcomm y * a := by rw [h]

theorem commute_of_commute_orbitDiagonalHom (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) (hr : 0 < r) {y : ↥L} {z : G} (hz : z ∈ L)
    (h : Commute (orbitDiagonalHom a L r ha hcomm y) z) : Commute (y : G) z := by
  rcases r with _ | n
  · omega
  let f : Fin (n + 1) → G := orbitDiagonalFactor a (n + 1) y
  let f' : Fin n → G := fun i => f i.succ
  have hf_eq : f = Fin.cons (f 0) f' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [f']
  have hdelta : orbitDiagonalHom a L (n + 1) ha hcomm y =
      (y : G) * (List.ofFn f').prod := by
    change (List.ofFn f).prod = (y : G) * (List.ofFn f').prod
    rw [hf_eq, List.ofFn_cons, List.prod_cons]
    simp [f, orbitDiagonalFactor]
  have hPcomm : Commute ((List.ofFn f').prod) z := by
    refine (Commute.list_prod_right _ _ (fun x hx => ?_)).symm
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' f' x).1 hx
    have hz0 : z ∈ conjugatePower a L 0 := by
      rw [conjugatePower]
      simpa using Subgroup.mem_map_of_mem
        ((MulAut.conj (a ^ (0 : ℕ))).toMonoidHom) hz
    exact (hcomm i.succ 0 (by simp)
      (orbitDiagonalFactor a (n + 1) y i.succ)
      (orbitDiagonalFactor_mem_conjugatePower a L (n + 1) y i.succ)
      z hz0).symm
  have heq := h.eq
  rw [hdelta] at heq
  show (y : G) * z = z * (y : G)
  calc (y : G) * z = (y : G) * z * (List.ofFn f').prod * ((List.ofFn f').prod)⁻¹ := by
        group
    _ = (y : G) * (z * (List.ofFn f').prod) * ((List.ofFn f').prod)⁻¹ := by group
    _ = (y : G) * ((List.ofFn f').prod * z) * ((List.ofFn f').prod)⁻¹ := by
        rw [← hPcomm.eq]
    _ = ((y : G) * (List.ofFn f').prod) * z * ((List.ofFn f').prod)⁻¹ := by group
    _ = (z * ((y : G) * (List.ofFn f').prod)) * ((List.ofFn f').prod)⁻¹ := by rw [heq]
    _ = z * (y : G) := by group

theorem orbitDiagonalHom_ker_le_center (a : G) (L : Subgroup G) (r : ℕ) (ha : a ^ r = 1)
    (hcomm : ConjugatesCommute a L r) (hr : 0 < r) :
    (orbitDiagonalHom a L r ha hcomm).ker ≤ Subgroup.center ↥L := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact (commute_of_commute_orbitDiagonalHom a L r ha hcomm hr z.2 (by
    rw [hy]
    show (1 : G) * (z : G) = (z : G) * 1
    simp)).symm

end CFSG.GroupTheory

end
