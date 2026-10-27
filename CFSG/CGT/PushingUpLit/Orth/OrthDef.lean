module

public import CFSG.CGT.PushingUpLit.Orth.OrthFin
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv
open scoped commutatorElement

structure IsO2 {G : Type*} [Group G] (K P : Subgroup G) : Prop where
  le : P ≤ K
  normal : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P
  pgroup : IsPGroup 2 P
  max : ∀ N : Subgroup G, N ≤ K → (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → IsPGroup 2 N → N ≤ P

structure OrthCfg (G : Type*) [Group G] (M Q : Subgroup G) where
  elt : Vec5 → G
  elt_add : ∀ v w, elt (v + w) = elt v * elt w
  elt_inj : Function.Injective elt
  mem_Q_iff : ∀ x, x ∈ Q ↔ ∃ v, elt v = x
  θ : ↥M →* Perm (Fin 5)
  θ_surj : Function.Surjective θ
  θ_ker : ∀ m : ↥M, θ m = 1 ↔ (m : G) ∈ Q
  equivar : ∀ (m : ↥M) (v : Vec5), (m : G) * elt v * (m : G)⁻¹ = elt (permAct (θ m) v)
  Q_le_M : Q ≤ M
  normalizer_Q : Subgroup.normalizer (Q : Set G) = M
  centralizer_Q : Subgroup.centralizer (Q : Set G) ≤ Q

namespace OrthCfg

variable {G : Type*} [Group G] {M Q : Subgroup G} (C : OrthCfg G M Q)

include C

theorem elt_zero : C.elt 0 = 1 := by
  have h : C.elt 0 * C.elt 0 = C.elt 0 * 1 := by
    rw [← C.elt_add, add_zero, mul_one]
  exact mul_left_cancel h

theorem elt_mem (v : Vec5) : C.elt v ∈ Q := (C.mem_Q_iff _).2 ⟨v, rfl⟩

theorem elt_mul_self (v : Vec5) : C.elt v * C.elt v = 1 := by
  rw [← C.elt_add, add_self_vec, C.elt_zero]

theorem elt_inv (v : Vec5) : (C.elt v)⁻¹ = C.elt v :=
  inv_eq_of_mul_eq_one_right (C.elt_mul_self v)

theorem elt_comm (v w : Vec5) : C.elt v * C.elt w = C.elt w * C.elt v := by
  rw [← C.elt_add, ← C.elt_add, add_comm]

theorem elt_ne_one {v : Vec5} (hv : v ≠ 0) : C.elt v ≠ 1 := fun h =>
  hv (C.elt_inj (h.trans C.elt_zero.symm))

theorem Q_comm {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := (C.mem_Q_iff x).1 hx
  obtain ⟨w, rfl⟩ := (C.mem_Q_iff y).1 hy
  exact C.elt_comm v w

theorem sq_eq_one_of_mem {x : G} (hx : x ∈ Q) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := (C.mem_Q_iff x).1 hx
  exact C.elt_mul_self v

theorem Q_le_centralizer_of_mem {x : G} (hx : x ∈ Q) :
    Q ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff.1 hz]
  exact C.Q_comm hx hy

open Classical in
noncomputable def vec (x : G) : Vec5 :=
  if h : x ∈ Q then Classical.choose ((C.mem_Q_iff x).1 h) else 0

theorem elt_vec {x : G} (hx : x ∈ Q) : C.elt (C.vec x) = x := by
  simp only [vec, hx, ↓reduceDIte]
  exact Classical.choose_spec ((C.mem_Q_iff x).1 hx)

theorem vec_elt (v : Vec5) : C.vec (C.elt v) = v :=
  C.elt_inj (C.elt_vec (C.elt_mem v))

theorem vec_mul {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : C.vec (x * y) = C.vec x + C.vec y := by
  apply C.elt_inj
  rw [C.elt_add, C.elt_vec hx, C.elt_vec hy, C.elt_vec (Q.mul_mem hx hy)]

theorem vec_eq_zero_iff {x : G} (hx : x ∈ Q) : C.vec x = 0 ↔ x = 1 := by
  constructor
  · intro h
    rw [← C.elt_vec hx, h, C.elt_zero]
  · rintro rfl
    have := C.vec_elt 0
    rwa [C.elt_zero] at this

open Classical in
noncomputable def th (x : G) : Perm (Fin 5) := if h : x ∈ M then C.θ ⟨x, h⟩ else 1

theorem th_eq {m : G} (h : m ∈ M) : C.th m = C.θ ⟨m, h⟩ := by
  simp only [th, h, ↓reduceDIte]

theorem th_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) : C.th (x * y) = C.th x * C.th y := by
  rw [C.th_eq (M.mul_mem hx hy), C.th_eq hx, C.th_eq hy]
  exact map_mul C.θ ⟨x, hx⟩ ⟨y, hy⟩

theorem th_one : C.th 1 = 1 := by
  rw [C.th_eq M.one_mem]
  exact map_one C.θ

theorem th_inv {x : G} (hx : x ∈ M) : C.th x⁻¹ = (C.th x)⁻¹ := by
  rw [C.th_eq (M.inv_mem hx), C.th_eq hx]
  exact map_inv C.θ ⟨x, hx⟩

theorem th_pow {x : G} (hx : x ∈ M) (n : ℕ) : C.th (x ^ n) = (C.th x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, C.th_one]
  | succ n ih => rw [pow_succ, pow_succ, C.th_mul (M.pow_mem hx n) hx, ih]

theorem th_surj (σ : Perm (Fin 5)) : ∃ m ∈ M, C.th m = σ := by
  obtain ⟨m, hm⟩ := C.θ_surj σ
  exact ⟨m, m.2, by rw [C.th_eq m.2]; exact hm⟩

theorem th_eq_one_iff {x : G} (hx : x ∈ M) : C.th x = 1 ↔ x ∈ Q := by
  rw [C.th_eq hx]; exact C.θ_ker ⟨x, hx⟩

theorem th_elt_mem {x : G} (hx : x ∈ Q) : C.th x = 1 :=
  (C.th_eq_one_iff (C.Q_le_M hx)).2 hx

theorem conj_elt {m : G} (hm : m ∈ M) (v : Vec5) :
    m * C.elt v * m⁻¹ = C.elt (permAct (C.th m) v) := by
  rw [C.th_eq hm]
  exact C.equivar ⟨m, hm⟩ v

theorem conj_vec {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ Q) :
    C.vec (m * x * m⁻¹) = permAct (C.th m) (C.vec x) := by
  obtain ⟨v, rfl⟩ := (C.mem_Q_iff x).1 hx
  rw [C.conj_elt hm, C.vec_elt, C.vec_elt]

theorem exists_conj_of_wt_eq {v w : Vec5} (h : wt v = wt w) :
    ∃ m ∈ M, m * C.elt v * m⁻¹ = C.elt w := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_wt_eq h
  obtain ⟨m, hm, hmσ⟩ := C.th_surj σ
  exact ⟨m, hm, by rw [C.conj_elt hm, hmσ, hσ]⟩

theorem mem_centralizer_elt_iff {m : G} (hm : m ∈ M) (v : Vec5) :
    m ∈ Subgroup.centralizer ({C.elt v} : Set G) ↔ permAct (C.th m) v = v := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 : C.elt v * m = m * C.elt v := h _ (Set.mem_singleton _)
    have h2 : m * C.elt v * m⁻¹ = C.elt v := by rw [← h1]; group
    rw [C.conj_elt hm] at h2
    exact C.elt_inj h2
  · intro h z hz
    rw [Set.mem_singleton_iff.1 hz]
    have h2 : m * C.elt v * m⁻¹ = C.elt v := by rw [C.conj_elt hm, h]
    calc C.elt v * m = (m * C.elt v * m⁻¹) * m := by rw [h2]
      _ = m * C.elt v := by group

@[expose] def pre (A : Subgroup (Perm (Fin 5))) : Subgroup G where
  carrier := {x | x ∈ M ∧ C.th x ∈ A}
  mul_mem' := fun {a b} ha hb =>
    ⟨M.mul_mem ha.1 hb.1, by rw [C.th_mul ha.1 hb.1]; exact A.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨M.one_mem, by rw [C.th_one]; exact A.one_mem⟩
  inv_mem' := fun {a} ha => ⟨M.inv_mem ha.1, by rw [C.th_inv ha.1]; exact A.inv_mem ha.2⟩

theorem mem_pre {A : Subgroup (Perm (Fin 5))} {x : G} : x ∈ C.pre A ↔ x ∈ M ∧ C.th x ∈ A :=
  Iff.rfl

theorem pre_le_M (A : Subgroup (Perm (Fin 5))) : C.pre A ≤ M := fun _ hx => hx.1

theorem th_mem_of_mem_pre {A : Subgroup (Perm (Fin 5))} {x : G} (hx : x ∈ C.pre A) : C.th x ∈ A :=
  hx.2

theorem Q_le_pre (A : Subgroup (Perm (Fin 5))) : Q ≤ C.pre A := fun _ hx =>
  ⟨C.Q_le_M hx, by rw [C.th_elt_mem hx]; exact A.one_mem⟩

theorem pre_mono {A B : Subgroup (Perm (Fin 5))} (h : A ≤ B) : C.pre A ≤ C.pre B :=
  fun _ hx => ⟨hx.1, h hx.2⟩

theorem isPGroup_pre {A : Subgroup (Perm (Fin 5))} (hA : IsPGroup 2 A) : IsPGroup 2 (C.pre A) := by
  intro x
  obtain ⟨k, hk⟩ := hA ⟨C.th x, x.2.2⟩
  refine ⟨k + 1, ?_⟩
  have h1 : (C.th x) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : (x : G) ^ (2 ^ k) ∈ Q := by
    rw [← C.th_eq_one_iff (M.pow_mem x.2.1 _), C.th_pow x.2.1, h1]
  have h3 : ((x : G) ^ (2 ^ k)) * ((x : G) ^ (2 ^ k)) = 1 := C.sq_eq_one_of_mem h2
  apply Subtype.ext
  show (x : G) ^ (2 ^ (k + 1)) = 1
  rw [pow_succ, pow_mul, pow_two]
  exact h3

theorem pre_subgroupOf (A : Subgroup (Perm (Fin 5))) :
    (C.pre A).subgroupOf M = A.comap C.θ := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, mem_pre, Subgroup.mem_comap, C.th_eq hx]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

theorem relindex_pre (A : Subgroup (Perm (Fin 5))) : (C.pre A).relIndex M = A.index := by
  rw [Subgroup.relIndex, C.pre_subgroupOf, Subgroup.index_comap_of_surjective _ C.θ_surj]

theorem pre_surj {A : Subgroup (Perm (Fin 5))} {σ : Perm (Fin 5)} (hσ : σ ∈ A) :
    ∃ m ∈ C.pre A, C.th m = σ := by
  obtain ⟨m, hm, h⟩ := C.th_surj σ
  exact ⟨m, ⟨hm, by rw [h]; exact hσ⟩, h⟩

noncomputable def eqVec : Q ≃ Vec5 where
  toFun x := C.vec x
  invFun v := ⟨C.elt v, C.elt_mem v⟩
  left_inv x := Subtype.ext (C.elt_vec x.2)
  right_inv v := C.vec_elt v

theorem card_Q : Nat.card Q = 32 := by
  rw [Nat.card_congr C.eqVec, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi]

theorem card_pre (A : Subgroup (Perm (Fin 5))) : Nat.card (C.pre A) = 32 * Nat.card A := by
  let f : ↥(C.pre A) →* ↥A :=
    { toFun := fun x => ⟨C.th x, x.2.2⟩
      map_one' := Subtype.ext C.th_one
      map_mul' := fun x y => Subtype.ext (C.th_mul x.2.1 y.2.1) }
  have hf : Function.Surjective f := fun a => by
    obtain ⟨m, hm, hma⟩ := C.pre_surj a.2
    exact ⟨⟨m, hm⟩, Subtype.ext hma⟩
  have hker : Nat.card f.ker = 32 := by
    rw [← C.card_Q]
    refine Nat.card_congr (Equiv.ofBijective (fun x : f.ker => (⟨(x : G), ?_⟩ : Q)) ⟨?_, ?_⟩)
    · have hx : C.th ((x : ↥(C.pre A)) : G) = 1 := congrArg Subtype.val x.2
      exact (C.th_eq_one_iff (x : ↥(C.pre A)).2.1).1 hx
    · intro a b hab
      have h1 := Subtype.mk.inj hab
      exact Subtype.ext (Subtype.ext h1)
    · intro y
      refine ⟨⟨⟨(y : G), C.Q_le_pre A y.2⟩, ?_⟩, rfl⟩
      exact Subtype.ext (C.th_elt_mem y.2)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥(C.pre A) ⧸ f.ker) = Nat.card A :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [h1, h2, hker, mul_comm]

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth
