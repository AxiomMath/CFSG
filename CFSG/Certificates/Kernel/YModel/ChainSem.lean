module

public import CFSG.Certificates.Kernel.YModel.SchSem
public import CFSG.Certificates.Kernel.YModel.TextSound
public import CFSG.Certificates.Kernel.YModel.BfsDefs
import CFSG.Certificates.Kernel.YModel.SchCard
import CFSG.Certificates.Kernel.YModel.BfsSem
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Box

public section

namespace CFSG.KC.YModel.Chain

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.YModel.Sem
  CFSG.KC.YModel.Sch CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native CFSG.Monster.B

theorem closed_back {N : Nat} {f : Nat → Nat} (hf : ∀ x < N, f x < N)
    (hinj : ∀ x < N, ∀ y < N, f x = f y → x = y) {C : Nat → Prop}
    (hC : ∀ x < N, C x → C (f x)) : ∀ x < N, C (f x) → C x := by
  classical
  set A := (Finset.range N).filter C
  have hsub : A.image f ⊆ A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hf x hx.1, hC x hx.1 hx.2⟩
  have hcard : (A.image f).card = A.card := Finset.card_image_of_injOn fun x hx y hy e => by
    rw [Finset.coe_filter] at hx hy
    exact hinj x (Finset.mem_range.mp hx.1) y (Finset.mem_range.mp hy.1) e
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  intro x hx hfx
  have : f x ∈ A.image f := by
    rw [heq, Finset.mem_filter, Finset.mem_range]
    exact ⟨hf x hx, hfx⟩
  obtain ⟨y, hy, e⟩ := Finset.mem_image.mp this
  rw [Finset.mem_filter, Finset.mem_range] at hy
  rw [hinj y hy.1 x hx e] at hy
  exact hy.2

theorem closed_fwd {N : Nat} {f : Nat → Nat} (hf : ∀ x < N, f x < N)
    (hinj : ∀ x < N, ∀ y < N, f x = f y → x = y) {C : Nat → Prop}
    (hC : ∀ x < N, C (f x) → C x) : ∀ x < N, C x → C (f x) := by
  classical
  set A := (Finset.range N).filter C
  set P := (Finset.range N).filter fun x => C (f x)
  have hsub : P ⊆ A := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1, hC x hx.1 hx.2⟩
  have himg : P.image f = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact ⟨hf x hx.1, hx.2⟩
    ·
      have hsurj : ∀ y < N, ∃ x < N, f x = y := by
        have hi : ((Finset.range N).image f) = Finset.range N := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
            exact Finset.mem_range.mpr (hf x (Finset.mem_range.mp hx))
          · rw [Finset.card_image_of_injOn fun x hx y hy e =>
              hinj x (Finset.mem_range.mp hx) y (Finset.mem_range.mp hy) e]
        intro y hy
        have : y ∈ (Finset.range N).image f := by rw [hi]; exact Finset.mem_range.mpr hy
        obtain ⟨x, hx, e⟩ := Finset.mem_image.mp this
        exact ⟨x, Finset.mem_range.mp hx, e⟩
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨x, hx, rfl⟩ := hsurj y hy.1
      exact Finset.mem_image.mpr ⟨x, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hx, hy.2⟩, rfl⟩
  have hcard : P.card = A.card := by
    rw [← himg, Finset.card_image_of_injOn fun x hx y hy e => by
      rw [Finset.coe_filter] at hx hy
      exact hinj x (Finset.mem_range.mp hx.1) y (Finset.mem_range.mp hy.1) e]
  have hPA := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  intro x hx hCx
  have : x ∈ P := by
    rw [hPA, Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, hCx⟩
  rw [Finset.mem_filter] at this
  exact this.2

theorem bitB_eq (x b : Nat) : bitB x b = x.testBit b := by
  unfold bitB
  change ((x >>> b &&& 1) == 1) = _
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x >>> b) with h | h <;> simp [h]

theorem testBit_fixedSet {k N : Nat} (hv : StagesValid k N) (p : Nat) :
    (fixedSet k (apK k N (idP k))).testBit p = (decide (p < 2 ^ k) && (benesPerm k N p == p)) := by
  unfold fixedSet
  rw [shl1, nxor, Nat.testBit_xor, testBit_ones']
  have hrec := testBit_orRec (fun b => Nat.land (Nat.xor (Nat.shiftRight (apK k N (idP k))
    (Nat.mul b (2 ^ k))) (idPlane (2 ^ k) b)) (ones (2 ^ k))) p k
  by_cases hp : p < 2 ^ k
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_xor]
    have hpi := benesPerm_lt hv hp
    have key : (Nat.rec (motive := fun _ => Nat) 0 (fun b acc => Nat.lor acc
        (Nat.land (Nat.xor (Nat.shiftRight (apK k N (idP k)) (Nat.mul b (2 ^ k))) (idPlane (2 ^ k) b))
          (ones (2 ^ k)))) k).testBit p = true ↔ benesPerm k N p ≠ p := by
      rw [hrec]
      simp only [nland, nxor, nshr, nmul, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
        testBit_ones', decide_eq_true hp, Bool.and_true]
      constructor
      · rintro ⟨b, hb, h⟩ e
        unfold apK at h
        rw [wid_eq, show b * 2 ^ k + p = 2 ^ k * b + p by rw [Nat.mul_comm],
          (testBit_netApply rfl hv (idP k)).1 b hb p hp, testBit_idP hb hpi, e,
          idPlane_testBit hb, decide_eq_true hp, Bool.true_and, Bool.xor_self] at h
        exact Bool.false_ne_true h
      · intro hne
        by_contra hall
        push Not at hall
        apply hne
        apply eq_of_bits hpi hp
        intro b hb
        have h := hall b hb
        unfold apK at h
        rw [wid_eq, show b * 2 ^ k + p = 2 ^ k * b + p by rw [Nat.mul_comm],
          (testBit_netApply rfl hv (idP k)).1 b hb p hp, testBit_idP hb hpi,
          idPlane_testBit hb, decide_eq_true hp, Bool.true_and] at h
        simpa using h
    by_cases he : benesPerm k N p = p
    · rw [he, beq_self_eq_true]
      have : ¬ (Nat.rec (motive := fun _ => Nat) 0 (fun b acc => Nat.lor acc
        (Nat.land (Nat.xor (Nat.shiftRight (apK k N (idP k)) (Nat.mul b (2 ^ k))) (idPlane (2 ^ k) b))
          (ones (2 ^ k)))) k).testBit p = true := fun h => key.mp h he
      simpa using this
    · rw [key.mpr he, beq_false_of_ne he]
      rfl
  · rw [decide_eq_false hp, Bool.false_and, Bool.false_xor]
    cases h : (Nat.rec (motive := fun _ => Nat) 0 (fun b acc => Nat.lor acc
        (Nat.land (Nat.xor (Nat.shiftRight (apK k N (idP k)) (Nat.mul b (2 ^ k))) (idPlane (2 ^ k) b))
          (ones (2 ^ k)))) k).testBit p
    · rfl
    · obtain ⟨b, -, h⟩ := hrec.mp h
      simp only [nland, Nat.testBit_and, testBit_ones', decide_eq_false hp,
        Bool.and_false] at h
      exact absurd h Bool.false_ne_true

theorem netApply_one (k N X : Nat) :
    netApply k (2 ^ k) 1 N X = netApply k (2 ^ k) (repU (2 ^ k) 1) N X := by
  rw [repU_one (Nat.two_pow_pos k)]

theorem testBit_orbStep {k : Nat} : ∀ (Ns : List Nat), (∀ N ∈ Ns, StagesValid k N) → ∀ (X p : Nat),
    (orbStep k Ns X).testBit p = true ↔ X.testBit p = true ∨
      (p < 2 ^ k ∧ ∃ N ∈ Ns, X.testBit (benesPerm k N p) = true)
  | [], _, X, p => by
    change X.testBit p = true ↔ _
    simp
  | N :: Ns, hv, X, p => by
    change (Nat.lor (orbStep k Ns X) (netApply k (Nat.shiftLeft 1 k) 1 N X)).testBit p = true ↔ _
    rw [nlor, Nat.testBit_or, Bool.or_eq_true,
      testBit_orbStep Ns (fun N' h => hv N' (List.mem_cons_of_mem _ h)) X p, shl1, netApply_one]
    have hN := hv N List.mem_cons_self
    by_cases hp : p < 2 ^ k
    · have e := (testBit_netApply (P := 1) rfl hN X).1 0 (by decide) p hp
      rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at e
      rw [e]
      constructor
      · rintro ((h | ⟨-, N', hN', h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨hp, N', List.mem_cons_of_mem _ hN', h⟩
        · exact Or.inr ⟨hp, N, List.mem_cons_self, h⟩
      · rintro (h | ⟨-, N', hN', h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hN' with rfl | hN'
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨hp, N', hN', h⟩)
    · have e := (testBit_netApply (P := 1) rfl hN X).2 p (by omega)
      rw [e]
      constructor
      · rintro ((h | ⟨h, -⟩) | h)
        · exact Or.inl h
        · exact absurd h hp
        · exact Or.inl h
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl (Or.inl h)
        · exact absurd h hp

theorem orbitOK_spec {k : Nat} {Ns : List Nat} {b R M : Nat} (hv : ∀ N ∈ Ns, StagesValid k N)
    (hb : b < 2 ^ k) (h : orbitOK k Ns b R M = true) :
    M.testBit b = true ∧ (∀ p, M.testBit p = true → p < 2 ^ k) ∧
      (∀ p < 2 ^ k, ∀ N ∈ Ns, M.testBit (benesPerm k N p) = true → M.testBit p = true) ∧
      ∀ C : Nat → Prop, C b → (∀ p < 2 ^ k, ∀ N ∈ Ns, C (benesPerm k N p) → C p) →
        ∀ p, M.testBit p = true → C p := by
  obtain ⟨h1, h2⟩ := andB_eq h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  set X : Nat → Nat := fun r => Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 b)
    (fun _ X => strictN (orbStep k Ns X) (fun Y => Y)) r with hXd
  have hXs : ∀ r, X (r + 1) = orbStep k Ns (X r) := fun r => Benes.strictN_eq _ _
  have hb' : ∀ p, (X 0).testBit p = true ↔ p = b := by
    intro p
    change (Nat.shiftLeft 1 b).testBit p = true ↔ _
    rw [shl1, Nat.testBit_two_pow, decide_eq_true_eq, eq_comm]
  have e2' : X R = M := e2
  have key : ∀ r, (X r).testBit b = true ∧ (∀ p, (X r).testBit p = true → p < 2 ^ k) ∧
      ∀ C : Nat → Prop, C b → (∀ p < 2 ^ k, ∀ N ∈ Ns, C (benesPerm k N p) → C p) →
        ∀ p, (X r).testBit p = true → C p := by
    intro r
    induction r with
    | zero =>
      refine ⟨(hb' b).mpr rfl, fun p hp => ?_, fun C hC _ p hp => ?_⟩
      · rw [(hb' p).mp hp]
        exact hb
      · rw [(hb' p).mp hp]
        exact hC
    | succ r ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      rw [hXs]
      refine ⟨(testBit_orbStep Ns hv _ b).mpr (Or.inl i1), fun p hp => ?_, fun C hC hcl p hp => ?_⟩
      · rcases (testBit_orbStep Ns hv _ p).mp hp with h | ⟨h, -⟩
        · exact i2 p h
        · exact h
      · rcases (testBit_orbStep Ns hv _ p).mp hp with h | ⟨h, N, hN, h'⟩
        · exact i3 C hC hcl p h
        · exact hcl p h N hN (i3 C hC hcl _ h')
  obtain ⟨k1, k2, k3⟩ := key R
  rw [e2'] at k1 k2 k3
  refine ⟨k1, k2, fun p hp N hN hM => ?_, k3⟩
  rw [← e1]
  exact (testBit_orbStep Ns hv M p).mpr (Or.inr ⟨hp, N, hN, hM⟩)

theorem mem_levelNets {k : Nat} {T : Nat → Nat} {B i N : Nat} : ∀ s,
    N ∈ levelNets k T B s i ↔ ∃ j < s, fixesK k T B j i = true ∧ T j = N
  | 0 => by
    change N ∈ ([] : List Nat) ↔ _
    simp
  | s + 1 => by
    change N ∈ Bool.rec (motive := fun _ => List Nat) (levelNets k T B s i)
      (T s :: levelNets k T B s i) (fixesK k T B s i) ↔ _
    cases hf : fixesK k T B s i
    · dsimp only
      rw [mem_levelNets s]
      constructor
      · rintro ⟨j, hj, h1, h2⟩
        exact ⟨j, by omega, h1, h2⟩
      · rintro ⟨j, hj, h1, h2⟩
        have hjs : j ≠ s := by
          rintro rfl
          rw [hf] at h1
          exact Bool.false_ne_true h1
        exact ⟨j, by omega, h1, h2⟩
    · dsimp only
      rw [List.mem_cons, mem_levelNets s]
      constructor
      · rintro (rfl | ⟨j, hj, h1, h2⟩)
        · exact ⟨s, by omega, hf, rfl⟩
        · exact ⟨j, by omega, h1, h2⟩
      · rintro ⟨j, hj, h1, h2⟩
        by_cases hjs : j = s
        · subst hjs
          exact Or.inl h2.symm
        · exact Or.inr ⟨j, by omega, h1, h2⟩

theorem brec_iff (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem fixesK_iff {k : Nat} {T : Nat → Nat} {B j : Nat} (hv : StagesValid k (T j)) : ∀ i,
    (∀ t < i, fieldAt 32 B t < 2 ^ k) →
      (fixesK k T B j i = true ↔ ∀ t < i, benesPerm k (T j) (fieldAt 32 B t) = fieldAt 32 B t)
  | 0, _ => by
    change true = true ↔ _
    simp
  | i + 1, hB => by
    change andB (bitB (fixedSet k (apK k (T j) (idP k))) (fieldAt 32 B i))
      (fixesK k T B j i) = true ↔ _
    rw [andB, brec_iff, fixesK_iff hv i (fun t ht => hB t (by omega)), bitB_eq,
      testBit_fixedSet hv, decide_eq_true (hB i (by omega)), Bool.true_and, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact h2 t ht
      · exact h1
    · intro h
      exact ⟨h i (by omega), fun t ht => h t (by omega)⟩

theorem codesOK_spec {w j : Nat} : ∀ len P, codesOK w j P len = true →
    ∀ x ∈ codesL w P len, 1 < x ∧ x >>> 1 ≤ j
  | 0, _, _, x, hx => by simp [codesL] at hx
  | len + 1, P, h, x, hx => by
    change andB (Nat.blt 1 (fieldAt w P 0))
      (andB (Nat.ble (Nat.shiftRight (fieldAt w P 0) 1) j) (codesOK w j (Nat.shiftRight P w) len))
      = true at h
    obtain ⟨h1, h2⟩ := andB_eq h
    obtain ⟨h2, h3⟩ := andB_eq h2
    rw [codesL_succ] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2⟩
    · exact codesOK_spec len _ h3 x hx

theorem wordOK_spec {k w m i : Nat} {T WP WL : Nat → Nat} (h : wordOK k w m T WP WL i = true) :
    StagesValid k (T (m + i)) ∧ codesOK w (m + i) (WP i) (WL i) = true ∧
      wordNet k (wordNets k w T (WP i) (WL i)) (T (m + i)) = true := by
  unfold wordOK at h
  obtain ⟨h1, h⟩ := andB_eq h
  obtain ⟨h2, h3⟩ := andB_eq h
  exact ⟨stagesValid_of_ymodel h1, h2, h3⟩

theorem word_good {k n w m i : Nat} {T WP WL : Nat → Nat} (hn : n ≤ 2 ^ k)
    (h : wordOK k w m T WP WL i = true) (hg : CodesGood k n T (codesL w (WP i) (WL i))) :
    Good k n (T (m + i)) ∧ netPerm k n (T (m + i)) = cpermL k n T (codesL w (WP i) (WL i)) := by
  obtain ⟨hv, -, hw⟩ := wordOK_spec h
  have g1 := good_wordNets hg
  have e := Nat.eq_of_beq_eq_true hw
  rw [shl1] at e
  have hc := eq_of_idP (acts_netsApply _ fun N hN => (g1 N hN).2.1) (acts_netApply hv) e
  have hG : Good k n (T (m + i)) := ⟨hn, hv, fun i' h1 h2 => by
    rw [← hc i' h2, compN_fix _ g1 i' h1 h2]⟩
  refine ⟨hG, ?_⟩
  rw [← prod_wordNets hg]
  ext i'
  rw [netPerm_apply hG, prod_apply _ g1, hc i' (by have := i'.2; omega)]

theorem rep_letterA {k n J : Nat} {T : Nat → Nat} {S Sinv : Array (Array Nat)} {x : Nat}
    (hS : ∀ j < J, Co2.Rep n S[j]! (netPerm k n (T j)) ∧ Sinv[j]! = invCand n S[j]!)
    (hx : 1 < x ∧ x >>> 1 ≤ J) :
    Co2.Rep n (letterA S Sinv (TextSem.decI x)) (cperm k n T x) := by
  have hx2 : x >>> 1 = x / 2 := by rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hj : x / 2 - 1 < J := by omega
  unfold letterA cperm TextSem.decI
  rw [Nat.testBit_zero, hx2]
  by_cases hodd : x % 2 = 1
  · rw [if_pos hodd, decide_eq_true hodd, if_pos rfl,
      if_neg (by omega : ¬ (0 : Int) < -((x / 2 : Nat) : Int))]
    have e : (-(-((x / 2 : Nat) : Int))).toNat - 1 = x / 2 - 1 := by rw [neg_neg, Int.toNat_natCast]
    rw [e, (hS _ hj).2]
    exact rep_invCand (hS _ hj).1
  · rw [if_neg hodd, decide_eq_false hodd, if_pos (by omega : (0 : Int) < ((x / 2 : Nat) : Int))]
    have e : (((x / 2 : Nat) : Int)).toNat - 1 = x / 2 - 1 := by rw [Int.toNat_natCast]
    rw [e]
    exact (hS _ hj).1

theorem rep_wordA {k n J : Nat} {T : Nat → Nat} {S Sinv : Array (Array Nat)}
    (hS : ∀ j < J, Co2.Rep n S[j]! (netPerm k n (T j)) ∧ Sinv[j]! = invCand n S[j]!) :
    ∀ cs : List Nat, (∀ x ∈ cs, 1 < x ∧ x >>> 1 ≤ J) →
      Co2.Rep n (wordA n S Sinv (cs.map TextSem.decI)) (cpermL k n T cs)
  | [], _ => by
    rw [List.map_nil, wordA]
    exact Co2.rep_idA
  | x :: cs, h => by
    rw [List.map_cons, wordA, cpermL, List.map_cons, List.prod_cons]
    exact Co2.rep_compA (rep_letterA hS (h x List.mem_cons_self))
      (rep_wordA hS cs fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem getElem!_push' {α : Type} [Inhabited α] (a : Array α) (v : α) {i : Nat} (hi : i < a.size) :
    (a.push v)[i]! = a[i]! := by
  rw [getElem!_pos (a.push v) i (by simp; omega), getElem!_pos a i hi, Array.getElem_push_lt hi]

theorem getElem!_push_eq' {α : Type} [Inhabited α] (a : Array α) (v : α) : (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by simp), Array.getElem_push_eq]

@[expose] def StrongQ (k n m : Nat) (T : Nat → Nat) (O : Array (Array Nat)) (j : Nat)
    (p : Array (Array Nat) × Array (Array Nat)) : Prop :=
  p.1.size = m + j ∧ p.2.size = m + j ∧ ∀ i < m + j, Good k n (T i) ∧
    Co2.Rep n p.1[i]! (netPerm k n (T i)) ∧ p.2[i]! = invCand n p.1[i]! ∧ (i < m → p.1[i]! = O[i]!)

theorem strong_spec {k n m nw w : Nat} {T WP WL : Nat → Nat} {O : Array (Array Nat)}
    {W : Array (List Int)} (hn : n ≤ 2 ^ k) (hO : O.size = m)
    (hOT : ∀ c < m, Good k n (T c) ∧ Co2.Rep n O[c]! (netPerm k n (T c)))
    (hWs : W.size = nw) (hWw : ∀ i < nw, W[i]! = (codesL w (WP i) (WL i)).map TextSem.decI)
    (hw : ∀ i < nw, wordOK k w m T WP WL i = true) :
    StrongQ k n m T O nw (strongOf n O W) := by
  unfold strongOf
  rw [← Array.foldl_toList]
  have key : ∀ (ws : List (List Int)) (i : Nat) (p : Array (Array Nat) × Array (Array Nat)),
      i + ws.length = nw → (∀ t (ht : t < ws.length), ws[t] = W[i + t]!) → StrongQ k n m T O i p →
      StrongQ k n m T O nw (ws.foldl (fun p w =>
        (p.1.push (wordA n p.1 p.2 w), p.2.push (invCand n (wordA n p.1 p.2 w)))) p) := by
    intro ws
    induction ws with
    | nil =>
      intro i p hi _ hQ
      rw [List.length_nil, Nat.add_zero] at hi
      subst hi
      exact hQ
    | cons wd ws ih =>
      intro i p hi hws hQ
      rw [List.foldl_cons]
      apply ih (i + 1) _ (by simp at hi; omega) (fun t ht => by
        rw [show i + 1 + t = i + (t + 1) by omega, ← hws (t + 1) (by simp; omega)]
        rfl)
      obtain ⟨q1, q2, q3⟩ := hQ
      have hi' : i < nw := by simp at hi; omega
      have hwd : wd = (codesL w (WP i) (WL i)).map TextSem.decI := by
        rw [← hWw i hi', ← Nat.add_zero i, ← hws 0 (by simp)]
        rfl
      have hcodes := codesOK_spec _ _ (wordOK_spec (hw i hi')).2.1
      have hg : CodesGood k n T (codesL w (WP i) (WL i)) := fun x hx =>
        (q3 _ (by have := hcodes x hx; omega)).1
      obtain ⟨hG, hperm⟩ := word_good hn (hw i hi') hg
      have hrep := rep_wordA (J := m + i) (fun j hj => ⟨(q3 j hj).2.1, (q3 j hj).2.2.1⟩) _ hcodes
      rw [← hwd, ← hperm] at hrep
      refine ⟨by simp [q1]; omega, by simp [q2]; omega, fun j hj => ?_⟩
      by_cases hj' : j < m + i
      · obtain ⟨r1, r2, r3, r4⟩ := q3 j hj'
        dsimp only
        rw [getElem!_push' _ _ (by rw [q1]; exact hj'), getElem!_push' _ _ (by rw [q2]; exact hj')]
        exact ⟨r1, r2, r3, r4⟩
      · have e : j = m + i := by omega
        subst e
        dsimp only
        have e1 : (p.1.push (wordA n p.1 p.2 wd))[m + i]! = wordA n p.1 p.2 wd := by
          rw [← q1, getElem!_push_eq']
        have e2 : (p.2.push (invCand n (wordA n p.1 p.2 wd)))[m + i]! =
            invCand n (wordA n p.1 p.2 wd) := by
          rw [← q2, getElem!_push_eq']
        rw [e1, e2]
        exact ⟨hG, hrep, rfl, fun h => by omega⟩
  apply key W.toList 0 _ (by simp [hWs]) (fun t ht => by
    rw [Nat.zero_add, getElem!_pos W t (by simpa using ht), Array.getElem_toList])
  refine ⟨by simp [hO], by simp [hO], fun i hi => ?_⟩
  rw [Nat.add_zero] at hi
  refine ⟨(hOT i hi).1, (hOT i hi).2, ?_, fun _ => rfl⟩
  dsimp only
  rw [getElem!_pos _ i (by simp [hO]; exact hi), getElem!_pos O i (by rw [hO]; exact hi),
    Array.getElem_map]

theorem levelOK_spec {k n s : Nat} {T : Nat → Nat} {B : Nat} {R M Z : Nat → Nat} {i : Nat}
    (h : levelOK k n s T B R M Z i = true) :
    fieldAt 32 B i < n ∧ orbitOK k (levelNets k T B s i) (fieldAt 32 B i) (R i) (M i) = true ∧
      popc k (M i) = Z i := by
  unfold levelOK at h
  obtain ⟨h1, h⟩ := andB_eq h
  obtain ⟨h2, h3⟩ := andB_eq h
  exact ⟨Nat.blt_eq.mp h1, h2, Nat.eq_of_beq_eq_true h3⟩

theorem decI_spec {x : Nat} (hx : 1 < x) :
    TextSem.decI x ≠ 0 ∧ (TextSem.decI x).natAbs = x / 2 := by
  unfold TextSem.decI
  split <;> omega

theorem mem_levelGens_iff {S : Array (Array Nat)} {base : Array Nat} {i : Nat} :
    (∀ j < (levelGens S base i).size, ∃ j' < S.size, (levelGens S base i)[j]! = S[j']! ∧
      fixesFirst base S[j']! i = true) ∧
    ∀ j' < S.size, fixesFirst base S[j']! i = true →
      ∃ j < (levelGens S base i).size, (levelGens S base i)[j]! = S[j']! := by
  constructor
  · intro j hj
    have hm : (levelGens S base i)[j] ∈ S.filter fun t => fixesFirst base t i := Array.getElem_mem hj
    rw [Array.mem_filter] at hm
    obtain ⟨j', hj', e⟩ := Array.getElem_of_mem hm.1
    refine ⟨j', hj', ?_, ?_⟩
    · rw [getElem!_pos _ j hj, getElem!_pos S j' hj', e]
    · rw [getElem!_pos S j' hj', e]
      exact hm.2
  · intro j' hj' hf
    have hm : S[j'] ∈ S.filter fun t => fixesFirst base t i := by
      rw [Array.mem_filter]
      refine ⟨Array.getElem_mem hj', ?_⟩
      rw [← getElem!_pos S j' hj']
      exact hf
    obtain ⟨j, hj, e⟩ := Array.getElem_of_mem hm
    refine ⟨j, hj, ?_⟩
    rw [getElem!_pos _ j hj, getElem!_pos S j' hj']
    exact e

theorem level_points {k n s : Nat} {T : Nat → Nat} {B : Nat} {R M : Nat → Nat} {i : Nat}
    {S : Array (Array Nat)} {base : Array Nat} (hn : n ≤ 2 ^ k) (hSs : S.size = s)
    (hS : ∀ j < s, Good k n (T j) ∧ Co2.Rep n S[j]! (netPerm k n (T j)))
    (hfix : ∀ j < s, fixesFirst base S[j]! i = true ↔ fixesK k T B j i = true)
    (hb : fieldAt 32 B i < n)
    (horb : orbitOK k (levelNets k T B s i) (fieldAt 32 B i) (R i) (M i) = true) (r : Nat) :
    (r < 2 ^ k ∧ (M i).testBit r = true) ↔
      (r < n ∧ Bfs.Reach (levelGens S base i) (fieldAt 32 B i) r) := by
  set b := fieldAt 32 B i
  set steps := levelGens S base i
  obtain ⟨hmem, hin⟩ := mem_levelGens_iff (S := S) (base := base) (i := i)
  rw [hSs] at hmem hin
  have hv : ∀ N ∈ levelNets k T B s i, StagesValid k N := by
    intro N hN
    obtain ⟨j, hj, -, rfl⟩ := (mem_levelNets s).mp hN
    exact (hS j hj).1.2.1
  obtain ⟨k1, k2, k3, k4⟩ := orbitOK_spec hv (by omega) horb
  have hf : ∀ j < s, ∀ x < n, (S[j]!)[x]! = benesPerm k (T j) x := fun j hj x hx => by
    rw [(hS j hj).2.apply hx, netPerm_apply (hS j hj).1]
  have hflt : ∀ j < s, ∀ x < n, (S[j]!)[x]! < n := fun j hj x hx => (hS j hj).2.lt hx
  have hfinj : ∀ j < s, ∀ x < n, ∀ y < n, (S[j]!)[x]! = (S[j]!)[y]! → x = y := by
    intro j hj x hx y hy e
    rw [(hS j hj).2.apply hx, (hS j hj).2.apply hy] at e
    have := (netPerm k n (T j)).injective (Fin.ext e)
    exact congrArg Fin.val this
  have hsteps : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n := by
    intro j hj x hx
    obtain ⟨j', hj', e, -⟩ := hmem j hj
    rw [e]
    exact hflt j' hj' x hx
  have hreach_lt : ∀ y, Bfs.Reach steps b y → y < n := by
    intro y hy
    induction hy with
    | root => exact hb
    | step j hj _ ih => exact hsteps j hj _ ih
  constructor
  · rintro ⟨hr, hM⟩
    apply k4 (fun p => p < n ∧ Bfs.Reach steps b p) ⟨hb, Bfs.Reach.root⟩ _ r hM
    intro p hp N hN ⟨hq1, hq2⟩
    obtain ⟨j', hj', hfK, rfl⟩ := (mem_levelNets s).mp hN
    have hpn : p < n := by
      by_contra hc
      have := (hS j' hj').1.2.2 p (by omega) hp
      rw [this] at hq1
      exact hc hq1
    refine ⟨hpn, ?_⟩
    obtain ⟨j, hj, e⟩ := hin j' hj' ((hfix j' hj').mpr hfK)
    have hfwd : ∀ x < n, Bfs.Reach steps b x → Bfs.Reach steps b ((S[j']!)[x]!) := by
      intro x _ hx
      rw [← e]
      exact Bfs.Reach.step j hj hx
    have := closed_back (hflt j' hj') (hfinj j' hj') hfwd p hpn
    rw [hf j' hj' p hpn] at this
    exact this hq2
  · rintro ⟨-, hR⟩
    have key : ∀ y, Bfs.Reach steps b y → (M i).testBit y = true := by
      intro y hy
      induction hy with
      | root => exact k1
      | step j hj hx ih =>
        obtain ⟨j', hj', e, hff⟩ := hmem j hj
        have hxn := hreach_lt _ hx
        rw [e, hf j' hj' _ hxn]
        have hN : T j' ∈ levelNets k T B s i := (mem_levelNets s).mpr ⟨j', hj', (hfix j' hj').mp hff, rfl⟩
        have hvj := (hS j' hj').1.2.1
        exact closed_fwd (N := 2 ^ k) (fun x hx => benesPerm_lt hvj hx)
          (fun x hx y hy e' => by
            have := congrArg (benesInv k (T j')) e'
            rwa [benesInv_benesPerm hvj, benesInv_benesPerm hvj] at this)
          (fun x hx hM => k3 x hx _ hN hM) _ (by omega) ih
    have := key r hR
    exact ⟨k2 r this, this⟩

theorem steps_lt {k n s : Nat} {T : Nat → Nat} {i : Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hSs : S.size = s)
    (hS : ∀ j < s, Good k n (T j) ∧ Co2.Rep n S[j]! (netPerm k n (T j))) :
    ∀ j < (levelGens S base i).size, ∀ x < n, ((levelGens S base i)[j]!)[x]! < n := by
  intro j hj x hx
  obtain ⟨j', hj', e, -⟩ := (mem_levelGens_iff (S := S) (base := base) (i := i)).1 j hj
  rw [e]
  exact (hS j' (by omega)).2.lt hx

theorem level_size {k n s : Nat} {T : Nat → Nat} {B : Nat} {R M Z : Nat → Nat} {i : Nat}
    {S : Array (Array Nat)} {base : Array Nat} (hn : n ≤ 2 ^ k) (hSs : S.size = s)
    (hS : ∀ j < s, Good k n (T j) ∧ Co2.Rep n S[j]! (netPerm k n (T j)))
    (hfix : ∀ j < s, fixesFirst base S[j]! i = true ↔ fixesK k T B j i = true)
    (hb : fieldAt 32 B i < n)
    (horb : orbitOK k (levelNets k T B s i) (fieldAt 32 B i) (R i) (M i) = true)
    (hZ : popc k (M i) = Z i) :
    (orbitSearch n (fieldAt 32 B i) (levelGens S base i)).pts.size = Z i := by
  classical
  have hsteps := steps_lt (base := base) (i := i) hSs hS
  obtain ⟨-, hinj, hmemR⟩ := Bfs.orbitSearch_spec hb hsteps
  have hv : ∀ N ∈ levelNets k T B s i, StagesValid k N := by
    intro N hN
    obtain ⟨j, hj, -, rfl⟩ := (mem_levelNets s).mp hN
    exact (hS j hj).1.2.1
  have k2 := (orbitOK_spec hv (by omega) horb).2.1
  have hreach_lt : ∀ y, Bfs.Reach (levelGens S base i) (fieldAt 32 B i) y → y < n := by
    intro y hy
    induction hy with
    | root => exact hb
    | step j hj _ ih => exact hsteps j hj _ ih
  have hM : M i < 2 ^ 2 ^ k := Nat.lt_pow_two_of_testBit _ fun p hp => by
    cases h : (M i).testBit p
    · rfl
    · exact absurd (k2 p h) (by omega)
  set os := orbitSearch n (fieldAt 32 B i) (levelGens S base i)
  rw [← hZ, popc_eq k _ hM]
  have hsum : ∑ r ∈ Finset.range (2 ^ k), ((M i).testBit r).toNat =
      ((Finset.range (2 ^ k)).filter fun r => (M i).testBit r = true).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro r _
    cases (M i).testBit r <;> rfl
  have hset : ((Finset.range (2 ^ k)).filter fun r => (M i).testBit r = true) =
      (Finset.range os.pts.size).image fun a => os.pts[a]! := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro hr
      have := (level_points hn hSs hS hfix hb horb r).mp hr
      exact (hmemR r).mpr this.2
    · rintro ⟨a, ha, rfl⟩
      have hR := (hmemR _).mp ⟨a, ha, rfl⟩
      exact (level_points hn hSs hS hfix hb horb _).mpr ⟨hreach_lt _ hR, hR⟩
  rw [hsum, hset, Finset.card_image_of_injOn fun a ha b hb e =>
    hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) e, Finset.card_range]

theorem chain_spec {k n m nw w nb : Nat} {T WP WL R M Z : Nat → Nat} {B : Nat}
    {O : Array (Array Nat)} {W : Array (List Int)} {base : Array Nat}
    (hn : n ≤ 2 ^ k) (hp : permsOK n O = true) (hO : O.size = m)
    (hOT : ∀ c < m, Good k n (T c) ∧ Co2.Rep n O[c]! (netPerm k n (T c)))
    (hWs : W.size = nw) (hWw : ∀ i < nw, W[i]! = (codesL w (WP i) (WL i)).map TextSem.decI)
    (hBs : base.size = nb) (hBb : ∀ i < nb, base[i]! = fieldAt 32 B i)
    (hw : ∀ i < nw, wordOK k w m T WP WL i = true)
    (hl : ∀ i < nb, levelOK k n (Nat.add m nw) T B R M Z i = true) :
    chainOK n O W base = true ∧ chainSizes n O W base = (List.range nb).map Z := by
  obtain ⟨hS1, hS2, hS⟩ := strong_spec hn hO hOT hWs hWw hw
  set S := (strongOf n O W).1 with hSd
  set Sinv := (strongOf n O W).2 with hSinvd
  have hSR : ∀ j < m + nw, Good k n (T j) ∧ Co2.Rep n S[j]! (netPerm k n (T j)) :=
    fun j hj => ⟨(hS j hj).1, (hS j hj).2.1⟩
  have hlv := fun i (hi : i < nb) => levelOK_spec (hl i hi)
  have hfix : ∀ i < nb, ∀ j < m + nw, fixesFirst base S[j]! i = true ↔ fixesK k T B j i = true := by
    intro i hi j hj
    rw [fixesK_iff (hS j hj).1.2.1 i (fun t ht => by have := (hlv t (by omega)).1; omega)]
    unfold fixesFirst
    rw [CFSG.Monster.B.Co2.allLt_iff]
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro ht
    have htn := (hlv t (by omega)).1
    rw [hBb t (by omega), beq_iff_eq, (hS j hj).2.1.apply htn, netPerm_apply (hS j hj).1]
  have hword : ∀ i < nw, Co2.Rep n (wordA n S Sinv W[i]!) (netPerm k n (T (m + i))) ∧
      ∀ x ∈ codesL w (WP i) (WL i), 1 < x ∧ x >>> 1 ≤ m + i := by
    intro i hi
    have hcodes := codesOK_spec _ _ (wordOK_spec (hw i hi)).2.1
    have hg : CodesGood k n T (codesL w (WP i) (WL i)) := fun x hx =>
      (hS _ (by have := hcodes x hx; omega)).1
    obtain ⟨-, hperm⟩ := word_good hn (hw i hi) hg
    have := rep_wordA (J := m + nw) (S := S) (Sinv := Sinv)
      (fun j hj => ⟨(hS j hj).2.1, (hS j hj).2.2.1⟩) _ (fun x hx => by
        have := hcodes x hx
        exact ⟨this.1, by omega⟩)
    rw [← hWw i hi, ← hperm] at this
    exact ⟨this, hcodes⟩
  refine ⟨?_, ?_⟩
  · unfold chainOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff]
    rw [← hSd, ← hSinvd, hO, hWs, hBs]
    refine ⟨⟨⟨⟨⟨⟨⟨hp, by rw [hS1]⟩, by rw [hS1, hS2]⟩, fun c hc => ?_⟩, fun j hj => ?_⟩, fun i hi => ?_⟩,
      fun i hi => ?_⟩, fun i hi => ?_⟩
    · rw [(hS c (by omega)).2.2.2 hc]
      exact (CFSG.Monster.B.Co2.eqA_iff (hOT c hc).2 (hOT c hc).2).mpr rfl
    · rw [hS1] at hj
      rw [(hS j hj).2.2.1]
      have hR := (hS j hj).2.1
      exact isInvA_invCand (fun x hx => hR.lt hx) fun x hx y hy e => by
        rw [hR.apply hx, hR.apply hy] at e
        exact congrArg Fin.val ((netPerm k n (T j)).injective (Fin.ext e))
    · obtain ⟨hR, hcodes⟩ := hword i hi
      refine ⟨?_, (CFSG.Monster.B.Co2.eqA_iff (hS (m + i) (by omega)).2.1 hR).mpr rfl⟩
      unfold CFSG.Monster.B.Co2.Native.lettersOK
      rw [hWw i hi, List.all_eq_true]
      intro l hl
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨h1, h2⟩ := decI_spec (hcodes x hx).1
      have h3 := (hcodes x hx).2
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one] at h3
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, h1, not_false_eq_true, decide_eq_true_eq,
        true_and, h2]
      exact h3
    · rw [hBb i hi]
      exact (hlv i hi).1
    · rw [hBb i hi]
      exact (Bfs.orbitSearch_spec (hlv i hi).1 (steps_lt (base := base) (i := i) hS1 hSR)).1
  · unfold chainSizes
    rw [← hSd, hBs]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [hBb i hi']
    exact level_size hn hS1 hSR (hfix i hi') (hlv i hi').1 (hlv i hi').2.1 (hlv i hi').2.2

end CFSG.KC.YModel.Chain

end
