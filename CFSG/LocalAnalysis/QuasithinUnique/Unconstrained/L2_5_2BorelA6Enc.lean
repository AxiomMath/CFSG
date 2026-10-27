module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.Borel252.A6

open Equiv

abbrev P6 : Type := Equiv.Perm (Fin 6)

def perm6 (cs : List (List (Fin 6))) : P6 := (cs.map List.formPerm).prod

structure R6 where
  a : Fin 6
  b : Fin 6
  c : Fin 6
  d : Fin 6
  e : Fin 6
  f : Fin 6
  deriving DecidableEq

namespace R6

def get (x : R6) : Fin 6 → Fin 6
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | 3 => x.d
  | 4 => x.e
  | 5 => x.f

def mul (x y : R6) : R6 := ⟨x.get y.a, x.get y.b, x.get y.c, x.get y.d, x.get y.e, x.get y.f⟩

def one : R6 := ⟨0, 1, 2, 3, 4, 5⟩

instance : Mul R6 := ⟨mul⟩

instance : One R6 := ⟨one⟩

def enc (σ : P6) : R6 := ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5⟩

theorem get_enc (σ : P6) (i : Fin 6) : (enc σ).get i = σ i := by
  fin_cases i <;> rfl

theorem enc_mul (σ τ : P6) : enc (σ * τ) = enc σ * enc τ := by
  show enc (σ * τ) = ⟨(enc σ).get (τ 0), (enc σ).get (τ 1), (enc σ).get (τ 2),
    (enc σ).get (τ 3), (enc σ).get (τ 4), (enc σ).get (τ 5)⟩
  simp only [get_enc]
  rfl

theorem enc_inj : Function.Injective enc := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun r => r.get i) h
  simpa only [get_enc] using this

theorem enc_one : enc 1 = 1 := by decide

end R6

def stepL {R : Type*} [Mul R] [DecidableEq R] (gens L : List R) : List R :=
  L ++ ((L.flatMap fun x => gens.map fun g => x * g).filter fun y => decide (y ∉ L)).dedup

def iterL {R : Type*} [One R] [Mul R] [DecidableEq R] (gens : List R) : ℕ → List R
  | 0 => [1]
  | n + 1 => stepL gens (iterL gens n)

def closedB {R : Type*} [One R] [Mul R] [DecidableEq R] (gens L : List R) : Bool :=
  decide ((1 : R) ∈ L) && L.all fun x => gens.all fun g => decide (x * g ∈ L)

theorem closedB_spec {R : Type*} [One R] [Mul R] [DecidableEq R] {gens L : List R}
    (h : closedB gens L = true) : (1 : R) ∈ L ∧ ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun x hx g hg => h.2 x hx g hg⟩

structure IsEnc {G R : Type*} [Group G] [Mul R] [One R] (enc : G → R) : Prop where
  inj : Function.Injective enc
  map_mul : ∀ x y, enc (x * y) = enc x * enc y
  map_one : enc 1 = 1

theorem iterL_sound {G R : Type*} [Group G] [Mul R] [One R] [DecidableEq R] {enc : G → R}
    (h : IsEnc enc) (gens : List G) (n : ℕ) :
    ∀ r ∈ iterL (gens.map enc) n, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r := by
  induction n with
  | zero =>
    intro r hr
    simp only [iterL, List.mem_singleton] at hr
    exact ⟨1, Subgroup.one_mem _, by rw [hr, h.map_one]⟩
  | succ n ih =>
    intro r hr
    simp only [iterL, stepL, List.mem_append, List.mem_dedup, List.mem_filter, List.mem_flatMap,
      List.mem_map] at hr
    rcases hr with hr | ⟨⟨y, hy, g', ⟨g, hg, rfl⟩, rfl⟩, -⟩
    · exact ih r hr
    · obtain ⟨x, hx, rfl⟩ := ih y hy
      exact ⟨x * g, Subgroup.mul_mem _ hx (Subgroup.subset_closure hg), h.map_mul x g⟩

theorem mem_closure_iff_of_closed {G R : Type*} [Group G] [Finite G] [Mul R] [One R]
    [DecidableEq R] {enc : G → R} (h : IsEnc enc) (gens : List G) (L : List R)
    (h1 : (1 : R) ∈ L) (hcl : ∀ x ∈ L, ∀ g ∈ gens.map enc, x * g ∈ L)
    (hs : ∀ r ∈ L, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔ enc x ∈ L := by
  constructor
  · intro hx
    have hsub : (Subgroup.closure {g | g ∈ gens}).toSubmonoid =
        Submonoid.closure {g | g ∈ gens} := Subgroup.closure_toSubmonoid_of_finite
    have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right (motive := fun m _ => enc m ∈ L)
      (by rwa [h.map_one]) ?_ hx'
    intro m _ y hy hm
    rw [h.map_mul]
    exact hcl _ hm _ (List.mem_map_of_mem hy)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hs _ hx
    rwa [← h.inj hyx]

theorem card_of_list {G R : Type*} [Group G] [DecidableEq R] {enc : G → R}
    (hinj : Function.Injective enc) (Y : Subgroup G) (L : List R) (hnd : L.Nodup)
    (hY : ∀ x, x ∈ Y ↔ enc x ∈ L) (hs : ∀ r ∈ L, ∃ x, enc x = r) : Nat.card Y = L.length := by
  have e : Y ≃ {r // r ∈ L.toFinset} :=
    Equiv.ofBijective (fun y => ⟨enc y, List.mem_toFinset.2 ((hY y).1 y.2)⟩)
      ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)),
      fun ⟨r, hr⟩ => by
        obtain ⟨x, hx⟩ := hs r (List.mem_toFinset.1 hr)
        exact ⟨⟨x, (hY x).2 (hx ▸ List.mem_toFinset.1 hr)⟩, Subtype.ext hx⟩⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem rawIsEnc : IsEnc R6.enc := ⟨R6.enc_inj, R6.enc_mul, R6.enc_one⟩

def d0Gens : List P6 := [perm6 [[0, 1, 2, 3], [4, 5]], perm6 [[0, 2], [4, 5]]]

def saGens : List P6 := d0Gens ++ [perm6 [[2, 3], [4, 5]]]

def sbGens : List P6 := d0Gens ++ [perm6 [[1, 4], [3, 5]]]

def vaGens : List P6 := [perm6 [[0, 1], [2, 3]], perm6 [[0, 2], [1, 3]]]

def vbGens : List P6 := [perm6 [[1, 3], [4, 5]], perm6 [[0, 2], [4, 5]]]

def reps9 : List P6 :=
  [perm6 [], perm6 [[3, 4, 5]], perm6 [[2, 3], [4, 5]], perm6 [[2, 3, 4]], perm6 [[2, 3, 5]],
    perm6 [[2, 4], [3, 5]], perm6 [[1, 2, 4, 3, 5]], perm6 [[1, 4, 3, 5, 2]], perm6 [[1, 4], [3, 5]]]

def rep (i : Fin 9) : P6 := reps9.getD i 1

structure TabEntry where
  i : Fin 9
  j : Fin 9
  k : Fin 9
  w : P6
  d : P6
  e : P6

def tabE : List TabEntry :=
  [⟨1, 1, 5, perm6 [[0, 1], [2, 3]], perm6 [[0, 1], [2, 3]], perm6 []⟩,
    ⟨3, 3, 1, perm6 [[0, 2], [1, 3]], perm6 [[0, 3], [1, 2]], perm6 [[1, 3], [4, 5]]⟩,
    ⟨5, 5, 3, perm6 [[0, 2], [4, 5]], perm6 [[0, 2], [1, 3]], perm6 [[0, 3], [1, 2]]⟩,
    ⟨1, 1, 4, perm6 [[0, 1, 2, 3], [4, 5]], perm6 [[0, 2], [4, 5]], perm6 [[0, 1], [2, 3]]⟩,
    ⟨4, 4, 7, perm6 [[1, 3], [4, 5]], perm6 [], perm6 [[1, 3], [4, 5]]⟩,
    ⟨7, 7, 3, perm6 [[1, 3], [4, 5]], perm6 [[0, 3, 2, 1], [4, 5]], perm6 [[0, 1, 2, 3], [4, 5]]⟩,
    ⟨1, 1, 8, perm6 [[0, 2], [1, 3]], perm6 [], perm6 [[0, 2], [4, 5]]⟩,
    ⟨6, 6, 3, perm6 [], perm6 [], perm6 [[1, 3], [4, 5]]⟩,
    ⟨1, 3, 2, perm6 [[0, 1, 2, 3], [4, 5]], perm6 [[1, 3], [4, 5]], perm6 [[0, 2], [1, 3]]⟩,
    ⟨8, 2, 6, perm6 [], perm6 [[1, 3], [4, 5]], perm6 [[1, 3], [4, 5]]⟩]

@[expose] def d0L : List R6 := iterL (d0Gens.map R6.enc) 4

@[expose] def saL : List R6 := iterL (saGens.map R6.enc) 5

@[expose] def sbL : List R6 := iterL (sbGens.map R6.enc) 5

@[expose] def vaL : List R6 := iterL (vaGens.map R6.enc) 3

@[expose] def vbL : List R6 := iterL (vbGens.map R6.enc) 3

def cenG1 : P6 := perm6 [[0, 1, 2]]

def cenG2 : P6 := perm6 [[1, 2, 3, 4, 5]]

@[expose] def conjIn (τ : R6) (L : List R6) (g : R6) : Bool := L.any fun y => decide (τ * g = y * τ)

theorem sizes_ok : d0L.length = 8 ∧ saL.length = 24 ∧ sbL.length = 24 ∧ d0L.Nodup ∧ saL.Nodup ∧
    sbL.Nodup ∧ vaL.length = 4 ∧ vbL.length = 4 ∧ vaL.Nodup ∧ vbL.Nodup := by
  decide +kernel

theorem closed_ok : closedB (d0Gens.map R6.enc) d0L = true ∧
    closedB (saGens.map R6.enc) saL = true ∧ closedB (sbGens.map R6.enc) sbL = true ∧
    closedB (vaGens.map R6.enc) vaL = true ∧ closedB (vbGens.map R6.enc) vbL = true := by
  decide +kernel

theorem cover_ok : ∀ x : P6, Perm.sign x = 1 →
    ∃ i : Fin 9, ∃ d ∈ d0L, ∃ e ∈ d0L, R6.enc x = d * R6.enc (rep i) * e := by
  decide +kernel

theorem tab_ok : ∀ t ∈ tabE, R6.enc t.w ∈ d0L ∧ R6.enc t.d ∈ d0L ∧ R6.enc t.e ∈ d0L ∧
    R6.enc (rep t.i) * R6.enc t.w * R6.enc (rep t.j) = R6.enc t.d * R6.enc (rep t.k) * R6.enc t.e := by
  decide +kernel

theorem lattice_ok : ∀ S : Finset (Fin 9), (0 : Fin 9) ∈ S → (∀ t ∈ tabE, t.i ∈ S → t.j ∈ S → t.k ∈ S) →
    S = {0} ∨ S = {0, 2} ∨ S = {0, 8} ∨ S = Finset.univ := by
  decide +kernel

theorem rep_facts : rep 0 = 1 ∧ R6.enc (rep 2) ∈ saL ∧ R6.enc (rep 8) ∈ sbL := by
  decide +kernel

theorem sa_cover : ∀ y ∈ saL, ∃ i : Fin 9, (i = 0 ∨ i = 2) ∧ ∃ d ∈ d0L, ∃ e ∈ d0L,
    y = d * R6.enc (rep i) * e := by
  decide +kernel

theorem sb_cover : ∀ y ∈ sbL, ∃ i : Fin 9, (i = 0 ∨ i = 8) ∧ ∃ d ∈ d0L, ∃ e ∈ d0L,
    y = d * R6.enc (rep i) * e := by
  decide +kernel

theorem gens_even : (∀ g ∈ d0Gens, Perm.sign g = 1) ∧ (∀ g ∈ saGens, Perm.sign g = 1) ∧
    (∀ g ∈ sbGens, Perm.sign g = 1) ∧ (∀ g ∈ vaGens, Perm.sign g = 1) ∧
    (∀ g ∈ vbGens, Perm.sign g = 1) ∧ Perm.sign cenG1 = 1 ∧ Perm.sign cenG2 = 1 := by
  decide +kernel

theorem sub_ok : (∀ x ∈ vaL, x ∈ d0L) ∧ (∀ x ∈ vbL, x ∈ d0L) ∧ (∀ x ∈ d0L, x ∈ saL) ∧
    (∀ x ∈ d0L, x ∈ sbL) := by
  decide +kernel

theorem sup_ok : ∀ g ∈ d0Gens, ∃ a ∈ vaL, ∃ b ∈ vbL, R6.enc g = a * b := by
  decide +kernel

theorem centA_ok : ∀ x : P6, Perm.sign x = 1 →
    (∀ v ∈ vaGens, R6.enc x * R6.enc v = R6.enc v * R6.enc x) → R6.enc x ∈ vaL := by
  decide +kernel

theorem centB_ok : ∀ x : P6, Perm.sign x = 1 →
    (∀ v ∈ vbGens, R6.enc x * R6.enc v = R6.enc v * R6.enc x) → R6.enc x ∈ vbL := by
  decide +kernel

theorem center_ok : ∀ x : P6, Perm.sign x = 1 → R6.enc x * R6.enc cenG1 = R6.enc cenG1 * R6.enc x →
    R6.enc x * R6.enc cenG2 = R6.enc cenG2 * R6.enc x → R6.enc x = 1 := by
  decide +kernel

theorem normD0_ok : ∀ x : P6, Perm.sign x = 1 →
    (d0Gens.map R6.enc).all (conjIn (R6.enc x) d0L) = true → R6.enc x ∈ d0L := by
  decide +kernel

theorem normVa_ok : ∀ x : P6, Perm.sign x = 1 →
    (vaGens.map R6.enc).all (conjIn (R6.enc x) vaL) = true → R6.enc x ∈ saL := by
  decide +kernel

theorem normVb_ok : ∀ x : P6, Perm.sign x = 1 →
    (vbGens.map R6.enc).all (conjIn (R6.enc x) vbL) = true → R6.enc x ∈ sbL := by
  decide +kernel

theorem SN_ok : (∀ g ∈ saGens.map R6.enc, ∀ v ∈ vaGens.map R6.enc, conjIn g vaL v = true) ∧
    (∀ g ∈ sbGens.map R6.enc, ∀ v ∈ vbGens.map R6.enc, conjIn g vbL v = true) := by
  decide +kernel

theorem core_ok : (∀ c ∈ d0L, (∀ g ∈ saL, conjIn g d0L c = true) → c ∈ vaL) ∧
    (∀ c ∈ d0L, (∀ g ∈ sbL, conjIn g d0L c = true) → c ∈ vbL) := by
  decide +kernel

theorem witness_ok : R6.enc (perm6 [[2, 3], [4, 5]]) ∈ saL ∧ R6.enc (perm6 [[2, 3], [4, 5]]) ∉ d0L ∧
    R6.enc (perm6 [[1, 4], [3, 5]]) ∈ sbL ∧ R6.enc (perm6 [[1, 4], [3, 5]]) ∉ d0L ∧
    R6.enc (perm6 [[0, 4, 3]]) ∉ saL ∧ R6.enc (perm6 [[0, 4, 3]]) ∉ sbL ∧
    Perm.sign (perm6 [[2, 3], [4, 5]]) = 1 ∧ Perm.sign (perm6 [[1, 4], [3, 5]]) = 1 ∧
    Perm.sign (perm6 [[0, 4, 3]]) = 1 := by
  decide +kernel

end CFSG.QuasithinUnique.Borel252.A6
