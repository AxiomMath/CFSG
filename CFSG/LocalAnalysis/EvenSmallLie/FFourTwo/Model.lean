module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.PcGroup
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Griess
public import CFSG.Blueprint.ChevalleyPinned
public import CFSG.Blueprint.ChevalleyRootsInputs
public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCoverRoots
import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.TwoToOne
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.EvenSmallLie.FFourTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover

@[expose] def prList : List (Fin Tag.F4.rank → ℤ) :=
  [![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 1, 0],
    ![1, 1, 0, 0], ![0, 1, 1, 1], ![0, 1, 2, 0], ![1, 1, 1, 0], ![0, 1, 2, 1], ![1, 1, 1, 1],
    ![1, 1, 2, 0], ![0, 1, 2, 2], ![1, 1, 2, 1], ![1, 2, 2, 0], ![1, 1, 2, 2], ![1, 2, 2, 1],
    ![1, 2, 2, 2], ![1, 2, 3, 1], ![1, 2, 4, 2], ![1, 3, 4, 2], ![1, 2, 3, 2], ![2, 3, 4, 2]]

@[expose] def pr (k : ℕ) : Fin Tag.F4.rank → ℤ := prList.getD k 0

@[expose] def cmTab : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 16777504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 16785536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  128, 0, 0, 16810496, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 16781824, 0, 0, 16844800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1024, 0, 17041408, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  16786432, 0, 0, 4096, 0, 0, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2048, 0, 0, 0, 16384, 0, 0, 131072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 17842176, 0, 0, 19005440, 0, 0, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 16384, 0, 0, 0, 131072, 0, 0, 25690112, 0, 4194304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0,
  16859136, 0, 32768, 0, 0, 0, 0, 19398656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 65536, 0, 0, 262144, 0, 0, 29360128, 0, 0, 1048576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0,
  0, 0, 25296896, 0, 0, 524288, 0, 4194304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  17170432, 0, 0, 0, 18350080, 0, 0, 0, 0, 0, 0, 0, 0, 2097152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 262144, 0, 0, 23068672, 0, 0, 1048576, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0,
  0,
  0, 524288, 0, 0, 4194304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 22020096, 0, 0, 0, 0, 0, 0, 2097152, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  4194304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 2097152, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def cmF (j i : ℕ) : ℕ := cmTab.getD (25 * j + i) 0

@[expose] def idxOf (v : Fin Tag.F4.rank → ℤ) : ℕ :=
  ((List.range 24).find? fun k => List.ofFn (pr k) == List.ofFn v).getD 24

abbrev IsIdx (k : ℕ) (v : Fin Tag.F4.rank → ℤ) : Prop :=
  k < 24 ∧ List.ofFn (pr k) = List.ofFn v

@[expose] def PairOK (j i : ℕ) : Prop :=
  ((f4Len (pr j) = f4Len (pr i) ∧ 2 * f4Ip (pr j) (pr i) = -f4Len (pr j)) ∧
      IsIdx (idxOf (pr j + pr i)) (pr j + pr i) ∧ cmF j i = 2 ^ idxOf (pr j + pr i)) ∨
    ((f4Len (pr j) = 2 ∧ f4Len (pr i) = 1 ∧ f4Ip (pr j) (pr i) = -1) ∧
      IsIdx (idxOf (pr j + pr i)) (pr j + pr i) ∧
          IsIdx (idxOf (pr j + 2 • pr i)) (pr j + 2 • pr i) ∧
      idxOf (pr j + pr i) ≠ idxOf (pr j + 2 • pr i) ∧
      cmF j i = 2 ^ idxOf (pr j + pr i) + 2 ^ idxOf (pr j + 2 • pr i) + 2 ^ 24) ∨
    ((f4Len (pr i) = 2 ∧ f4Len (pr j) = 1 ∧ f4Ip (pr i) (pr j) = -1) ∧
      IsIdx (idxOf (pr i + pr j)) (pr i + pr j) ∧
          IsIdx (idxOf (pr i + 2 • pr j)) (pr i + 2 • pr j) ∧
      idxOf (pr i + pr j) ≠ idxOf (pr i + 2 • pr j) ∧
      cmF j i = 2 ^ idxOf (pr i + pr j) + 2 ^ idxOf (pr i + 2 • pr j) + 2 ^ 24) ∨
    (¬(f4Len (pr j) = f4Len (pr i) ∧ 2 * f4Ip (pr j) (pr i) = -f4Len (pr j)) ∧
      ¬(f4Len (pr j) = 2 ∧ f4Len (pr i) = 1 ∧ f4Ip (pr j) (pr i) = -1) ∧
      ¬(f4Len (pr j) = 1 ∧ f4Len (pr i) = 2 ∧ f4Ip (pr j) (pr i) = -1) ∧ cmF j i = 0)

instance (j i : ℕ) : Decidable (PairOK j i) := by unfold PairOK; infer_instance

theorem pairOK_all : ∀ j < 24, ∀ i < j, PairOK j i := by
  decide +kernel

theorem pr_root : ∀ k < 24, (∃ k' : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k') =
    List.ofFn (pr k)) ∧ 0 < height (pr k) := by
  decide +kernel

theorem pr_complete : ∀ k' : Fin 48, 0 < height (Tag.F4.rootCertificate.root k') →
    ∃ k < 24, List.ofFn (pr k) = List.ofFn (Tag.F4.rootCertificate.root k') := by
  decide +kernel

theorem cmF_24 : ∀ i < 24, cmF 24 i = 0 := by decide +kernel

theorem cmF_lt : ∀ j < 25, ∀ i < j, cmF j i < 2 ^ 25 := by decide +kernel

theorem cmF_low : ∀ j < 25, ∀ i < j, cmF j i % 2 ^ (j + 1) = 0 := by decide +kernel

theorem pr_ne : ∀ j < 24, ∀ i < j, List.ofFn (pr j) ≠ List.ofFn (pr i) := by
  decide +kernel

theorem isRoot_pr {k : ℕ} (hk : k < 24) : IsRoot .F4 (pr k) :=
  isRoot_of_ofFn (pr_root k hk).1

theorem height_pr {k : ℕ} (hk : k < 24) : 0 < height (pr k) := (pr_root k hk).2

theorem pr_of_isIdx {k : ℕ} {v : Fin Tag.F4.rank → ℤ} (h : IsIdx k v) : pr k = v :=
  eq_of_ofFn h.2

theorem nf_two_pow_add {G : Type*} [Group G] (g : ℕ → G) {a E : ℕ} (h : Pc.LowZero (a + 1) E) :
    Pc.nf g (2 ^ a + E) = g a * Pc.nf g E := by
  have hE : E = 2 ^ (a + 1) * (E / 2 ^ (a + 1)) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ((Pc.lowZero_iff_mod _ _).1 h))).symm
  have hlt : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_succ (by omega)
  have e : 2 ^ a + E = 2 ^ a ||| E := by
    rw [hE, add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.or_comm]
  rw [e, Pc.nf_or g h _ hlt, Pc.nf_two_pow]

@[expose] def weylTab : Array ℕ := #[
  0, 4, 2, 3, 1, 7, 6, 5, 13, 11, 10, 9, 16, 8, 14, 18, 12, 17, 15, 22, 20, 21, 19, 23,
  4, 0, 8, 3, 0, 5, 12, 10, 2, 9, 7, 14, 6, 13, 11, 15, 16, 19, 20, 17, 18, 21, 22, 23,
  0, 5, 0, 6, 7, 1, 3, 4, 8, 9, 10, 11, 15, 13, 17, 12, 18, 14, 16, 19, 21, 20, 22, 23,
  0, 1, 6, 0, 4, 9, 2, 11, 12, 5, 14, 7, 8, 16, 10, 15, 13, 17, 18, 19, 20, 23, 22, 21]

@[expose] def negTab : Array (List ℕ) := #[
  [], [1], [2], [3], [4, 1], [5], [6], [7, 5], [8], [9], [10], [11, 9], [12], [13, 10, 8, 24],
  [14], [15], [16, 14, 12, 24], [17], [18, 17, 15, 24], [19], [20], [21], [22, 19], [23],
  [0], [], [2], [3], [4, 0], [5], [6], [7], [8, 5, 2, 24], [9], [10, 7], [11], [12, 9, 6, 24],
  [13], [14, 11], [15], [16], [17], [18], [19, 17], [20, 22, 18, 24], [21], [22], [23],
  [0], [1], [], [3], [4], [5, 1, 8, 24], [6, 3], [7, 4, 13, 24], [8], [9], [10], [11], [12],
  [13], [14], [15, 12], [16], [17, 14, 23, 24], [18, 16], [19], [20], [21, 20], [22], [23],
  [0], [1], [2], [], [4], [5], [6, 2], [7], [8], [9, 5, 15, 24], [10], [11, 7, 18, 24], [12, 8],
  [13], [14, 10, 20, 24], [15], [16, 13], [17], [18], [19], [20], [21], [22], [23, 21]]

theorem pr_simple : ∀ a : Fin 4, List.ofFn (pr a) =
    List.ofFn (Pi.single (Cover.fi (3 - a) (by omega)) 1 : Fin Tag.F4.rank → ℤ) := by
  decide +kernel

theorem weylTab_spec : ∀ a < 4, ∀ k < 24, k ≠ a →
    weylTab.getD (24 * a + k) 0 < 24 ∧ weylTab.getD (24 * a + k) 0 ≠ a ∧
    List.ofFn (reflect .F4 (Cover.fi (3 - a) (by omega)) (pr k)) =
      List.ofFn (pr (weylTab.getD (24 * a + k) 0)) := by
  decide +kernel

@[expose] def NegOK (a k : ℕ) : Prop :=
  let r := pr k
  let s := -pr a
  let w := negTab.getD (24 * a + k) []
  ((f4Len r = f4Len s ∧ 2 * f4Ip r s = -f4Len r) ∧ IsIdx (idxOf (r + s)) (r + s) ∧
      w = [k, idxOf (r + s)]) ∨
    ((f4Len r = 2 ∧ f4Len s = 1 ∧ f4Ip r s = -1) ∧ IsIdx (idxOf (r + s)) (r + s) ∧
      IsIdx (idxOf (r + 2 • s)) (r + 2 • s) ∧ w = [k, idxOf (r + s), idxOf (r + 2 • s), 24]) ∨
    ((f4Len s = 2 ∧ f4Len r = 1 ∧ f4Ip s r = -1) ∧ IsIdx (idxOf (s + r)) (s + r) ∧
      IsIdx (idxOf (s + 2 • r)) (s + 2 • r) ∧ w = [k, idxOf (s + r), idxOf (s + 2 • r), 24]) ∨
    (¬(f4Len r = f4Len s ∧ 2 * f4Ip r s = -f4Len r) ∧
      ¬(f4Len r = 2 ∧ f4Len s = 1 ∧ f4Ip r s = -1) ∧
      ¬(f4Len r = 1 ∧ f4Len s = 2 ∧ f4Ip r s = -1) ∧ w = [k])

instance (a k : ℕ) : Decidable (NegOK a k) := by unfold NegOK; infer_instance

theorem negOK_all : ∀ a < 4, ∀ k < 24, k ≠ a → NegOK a k := by
  decide +kernel

@[expose] def mulU (a b : ℕ) : ℕ := Pc.mul cmF 25 a b

@[expose] def invU (a : ℕ) : ℕ := Pc.inv cmF 25 a

@[expose] def conjU (a x : ℕ) : ℕ := Pc.mg cmF 25 (mulU (2 ^ a) x) a

@[expose] def bitsBelow (n x : ℕ) : List ℕ := (List.range n).filter fun k => x.testBit k

@[expose] def zPart (x : ℕ) : List ℕ := if x.testBit 24 then [24] else []

@[expose] def weylU (a x : ℕ) : ℕ :=
  Pc.mulList cmF 25 0 ((bitsBelow 24 x).map (fun k => weylTab.getD (24 * a + k) 0) ++ zPart x)

@[expose] def negU (a x : ℕ) : ℕ :=
  Pc.mulList cmF 25 0 ((bitsBelow 24 x).flatMap (fun k => negTab.getD (24 * a + k) []) ++ zPart x)

@[expose] def hU (a x : ℕ) : ℕ := conjU a (negU a (conjU a (negU a x)))

@[expose] def hOK (a x : ℕ) : Bool :=
  !x.testBit a && !(conjU a (negU a x)).testBit a

@[expose] def commHU (a x : ℕ) : ℕ := mulU x (invU (hU a x))

end CFSG.EvenSmallLie.FFourTwo

noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo.Cover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M)

@[expose] noncomputable def gU
    (k : ℕ) : M :=
  if k < 24 then C.yhat (pr k) else if k = 24 then C.z else 1

theorem gU_lt
    {k : ℕ} (hk : k < 24) : C.gU k = C.yhat (pr k) := by rw [gU, ite_eq_left hk]

theorem gU_24
    : C.gU 24 = C.z := by rw [gU]; simp

theorem gU_mul_self
    {k : ℕ} (hk : k < 25) : C.gU k * C.gU k = 1 := by
  by_cases h : k < 24
  · rw [C.gU_lt h]; exact C.yhat_mul_self (isRoot_pr h)
  · obtain rfl : k = 24 := by omega
    rw [C.gU_24, C.z_mul_z]

theorem π_gU
    {k : ℕ} (hk : k < 24) : C.π (C.gU k) = xr (pr k) := by
  rw [C.gU_lt hk, C.π_yhat (isRoot_pr hk)]

theorem nf_gU_two_pair
    {a b : ℕ} (ha : a < 24) (hb : b < 24) (hab : a ≠ b)
    (hc : C.gU a * C.gU b = C.gU b * C.gU a) :
    Pc.nf C.gU (2 ^ a + 2 ^ b + 2 ^ 24) = C.gU a * C.gU b * C.z := by
  have key : ∀ {a b : ℕ}, a < b → b < 24 →
      Pc.nf C.gU (2 ^ a + 2 ^ b + 2 ^ 24) = C.gU a * C.gU b * C.z := fun {a b} hab hb => by
    have h1 : Pc.LowZero (a + 1) (2 ^ b + 2 ^ 24) := fun j hj => by
      rw [show 2 ^ b + 2 ^ 24 = 2 ^ 24 * 1 + 2 ^ b by ring,
        Nat.testBit_two_pow_mul_add _ (Nat.pow_lt_pow_right (by norm_num) hb),
        ite_eq_left (by omega : j < 24), Nat.testBit_two_pow]
      simp; omega
    have h2 : Pc.LowZero (b + 1) (2 ^ 24) := fun j hj => by rw [Nat.testBit_two_pow]; simp; omega
    rw [add_assoc, nf_two_pow_add _ h1, nf_two_pow_add _ h2, Pc.nf_two_pow, C.gU_24, mul_assoc]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h hb
  · rw [add_comm (2 ^ a), key h ha, hc]

theorem pcData
    [Finite M] [Group.IsPerfect M] : Pc.PcData C.gU cmF 25 where
  inv := fun k hk => C.gU_mul_self hk
  lt := fun i j hij hj => cmF_lt j hj i hij
  low := fun i j hij hj => (Pc.lowZero_iff_mod _ _).2 (cmF_low j hj i hij)
  rel := by
    intro i j hij hj
    have hi2 := C.gU_mul_self (show i < 25 by omega)
    by_cases hj24 : j = 24
    · subst hj24
      rw [cmF_24 i (by omega), Pc.nf_zero, mul_one, C.gU_24, mul_assoc, ← C.z_comm (C.gU i), ←
        mul_assoc, hi2, one_mul]
    have hj' : j < 24 := by omega
    have hi' : i < 24 := by omega
    have hj2 := C.gU_mul_self hj
    suffices h : ⁅C.gU j, C.gU i⁆ = Pc.nf C.gU (cmF j i) by
      rw [← h, commutatorElement_def, inv_eq_of_mul_eq_one_right hj2,
        inv_eq_of_mul_eq_one_right hi2]
      simp only [← mul_assoc, hj2, one_mul]
    have hrj := isRoot_pr hj'
    have hri := isRoot_pr hi'
    rw [C.gU_lt hj', C.gU_lt hi']
    rcases pairOK_all j hj' i hij with ⟨c1, hx, hcm⟩ | ⟨c2, hx1, hx2, hne, hcm⟩ |
      ⟨c3, hx1, hx2, hne, hcm⟩ | ⟨n1, n2, n3, hcm⟩
    · rw [hcm, Pc.nf_two_pow, C.gU_lt hx.1, pr_of_isIdx hx]
      exact C.commutator_yhat_of_dec ⟨hrj, hri, rfl, c1⟩
    · have hm : Mixed (pr j) (pr i) := ⟨hrj, hri, c2⟩
      rw [hcm, C.nf_gU_two_pair hx1.1 hx2.1 hne (by
        rw [C.gU_lt hx1.1, C.gU_lt hx2.1, pr_of_isIdx hx1, pr_of_isIdx hx2]
        exact C.mixed_sum_commute hm), C.gU_lt hx1.1, C.gU_lt hx2.1, pr_of_isIdx hx1,
        pr_of_isIdx hx2]
      exact (C.commutator_yhat_mixed_z hm).1
    · have hm : Mixed (pr i) (pr j) := ⟨hri, hrj, c3⟩
      rw [hcm, C.nf_gU_two_pair hx1.1 hx2.1 hne (by
        rw [C.gU_lt hx1.1, C.gU_lt hx2.1, pr_of_isIdx hx1, pr_of_isIdx hx2]
        exact C.mixed_sum_commute hm), C.gU_lt hx1.1, C.gU_lt hx2.1, pr_of_isIdx hx1,
        pr_of_isIdx hx2]
      exact (C.commutator_yhat_mixed_z hm).2
    · rw [hcm, Pc.nf_zero, commutatorElement_eq_one_iff_mul_comm]
      have hp := rootPair_of_pos hrj (height_pr hj') hri (height_pr hi')
        (fun e => pr_ne j hj' i hij (congrArg List.ofFn e))
      exact C.commute_yhat hp n1 n2 n3

abbrev Uhat
    : Subgroup M := Pc.gens C.gU 25

abbrev UX
    (K : Type) [Field K] : Subgroup (adjointGroup .F4 K) :=
  (posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)

omit [Field K] in
theorem xr_mem_UX
    [Field K] {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hαp : 0 < height α) :
    xr (K := K) α ∈ UX K :=
  Subgroup.mem_subgroupOf.2 (by
    rw [posUnipotent]
    exact pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α}) ⟨hα, hαp⟩ 1)

theorem z_mem_Uhat : C.z ∈ C.Uhat := by
  rw [← C.gU_24]; exact Pc.g_mem_gens (by omega)

theorem map_Uhat
    : (C.Uhat).map C.π = UX K := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    by_cases h : k < 24
    · change C.π (C.gU k) ∈ UX K
      rw [C.π_gU h]; exact xr_mem_UX (isRoot_pr h) (height_pr h)
    · obtain rfl : k = 24 := by omega
      change C.π (C.gU 24) ∈ UX K
      rw [C.gU_24, C.π_z]; exact one_mem _
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [C.card]; norm_num)
    refine (posUnipotent_le_closure_xr C.card).trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, hαp, rfl⟩
    obtain ⟨k', rfl⟩ := isRoot_f4_iff.mp hα
    obtain ⟨k, hk, hkα⟩ := pr_complete k' hαp
    refine ⟨C.gU k, Pc.g_mem_gens (by omega), ?_⟩
    rw [C.π_gU hk, eq_of_ofFn hkα]

theorem Uhat_eq_comap
    : C.Uhat = (UX K).comap C.π := by
  apply le_antisymm
  · rw [← Subgroup.map_le_iff_le_comap, C.map_Uhat]
  · intro m hm
    rw [Subgroup.mem_comap, ← C.map_Uhat] at hm
    obtain ⟨u, hu, hum⟩ := hm
    rcases C.eq_or_eq_mul hum with h | h
    · rw [h]; exact hu
    · rw [h]; exact mul_mem hu C.z_mem_Uhat

omit C in
theorem card_UX
    (hK : Nat.card K = 2) : Nat.card (UX K) = 2 ^ 24 := by
  obtain ⟨-, -, -, -, -, -, hn, -⟩ := f4_field_two_root_pair_relations hK
  rw [card_subgroupOf_of_le (posUnipotent_le_adjointGroup (K := K)), card_posUnipotent, hK, hn]

theorem card_Uhat
    [Finite M] : Nat.card C.Uhat = 2 ^ 25 := by
  have h1 := GTwoFour.card_le_two_mul C.surj C.ker_iff C.Uhat (fun _ => True)
  have h2 := GTwoFour.two_mul_card_le C.ker_iff C.z_ne C.Uhat C.z_mem_Uhat (fun _ => True)
  have e1 : Nat.card {s : C.Uhat // True} = Nat.card C.Uhat :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  have e2 : Nat.card {q // q ∈ (C.Uhat).map C.π ∧ True} = Nat.card (UX K) := by
    rw [C.map_Uhat]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun q => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)
  rw [e1, e2, card_UX C.card] at h1 h2
  rw [pow_succ]; omega

theorem index_Uhat
    : (C.Uhat).index = (UX K).index := by
  rw [C.Uhat_eq_comap, Subgroup.index_comap_of_surjective _ C.surj]

theorem not_two_dvd_index_Uhat :
    ¬ 2 ∣ (C.Uhat).index := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [C.card]; norm_num)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two le_rfl
      (by rw [C.card, pow_one])
  obtain ⟨-, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := .F4) (K := K))
  rw [C.index_Uhat]; exact hUi
end CFSG.EvenSmallLie.FFourTwo.Cover

end
