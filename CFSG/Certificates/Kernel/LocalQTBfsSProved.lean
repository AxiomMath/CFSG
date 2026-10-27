module

public import Certificates.Data.Kernel.LocalQT.FusionS
public import CFSG.Certificates.Kernel.LocalQTBaseSProved

public section

namespace CFSG.KC.LQT.BSP

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BS.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

structure Order (n r : Nat) (G : List (Array Nat)) (M : Nat) (U : Nat → List Nat)
    (par dk : Nat → Nat) (cl : Nat → Nat → Nat) : Prop where
  key : ∀ a < M, ∀ b < M, keyNat n r (U a) = keyNat n r (U b) → a = b
  step : ∀ i < M, ∀ t < G.length, cl i t < M ∧ U (cl i t) = applyTab G[t]! (U i)
  disc : ∀ i < M, ∀ t < G.length, cl i t = 0 ∨ dk (cl i t) ≤ i * G.length + t
  par_spec : ∀ k < M, 0 < k → par k < k ∧
    ∃ t < G.length, dk k = par k * G.length + t ∧ cl (par k) t = k
  mono : ∀ k, 0 < k → k + 1 < M → dk k < dk (k + 1)

theorem divmod_eq {g a b a' b' : Nat} (hb : b < g) (hb' : b' < g) (h : a * g + b = a' * g + b') :
    a = a' ∧ b = b' := by
  have hg : 0 < g := by omega
  have h1 : (a * g + b) / g = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (a' * g + b') / g = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hb', Nat.zero_add]
  have h3 : (a * g + b) % g = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h4 : (a' * g + b') % g = b' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb']
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

section Loop

variable {n r M : Nat} {G : List (Array Nat)} {U : Nat → List Nat} {par dk : Nat → Nat}
  {cl : Nat → Nat → Nat}

@[expose] def Inv (n r M : Nat) (U : Nat → List Nat) (par dk : Nat → Nat) (c : Nat) (S : St) :
    Prop :=
  ∃ m, 0 < m ∧ m ≤ M ∧ S.1.size = m ∧ S.2.1.size = m ∧ (∀ k < m, S.1[k]! = U k) ∧
    (∀ k < m, 0 < k → S.2.1[k]! = par k) ∧
    (∀ y, S.2.2.contains y = true ↔ ∃ k < m, keyNat n r (U k) = y) ∧
    (∀ k < m, S.2.2.getD (keyNat n r (U k)) 0 = k) ∧
    (∀ k, 0 < k → k < M → (k < m ↔ dk k < c))

theorem Order.mono_lt (hO : Order n r G M U par dk cl) {a : Nat} (ha : 0 < a) :
    ∀ b, a < b → b < M → dk a < dk b := by
  intro b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro hab hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact Nat.lt_trans (ih h (by omega)) (hO.mono b (by omega) hb)
    · exact hO.mono a ha hb

theorem Order.dk_lt (hO : Order n r G M U par dk cl) {k : Nat} (hk : k < M) (hk0 : 0 < k) :
    dk k < (par k + 1) * G.length := by
  obtain ⟨-, t, ht, hd, -⟩ := hO.par_spec k hk hk0
  rw [hd, Nat.succ_mul]
  omega

theorem push_get_lt {α : Type} [Inhabited α] (A : Array α) (x : α) {k : Nat} (hk : k < A.size) :
    (A.push x)[k]! = A[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, ← getElem!_pos A k hk]

theorem push_get_eq {α : Type} [Inhabited α] (A : Array α) (x : α) : (A.push x)[A.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem body_step (hO : Order n r G M U par dk cl) {c i t : Nat} {S : St}
    (hc : Inv n r M U par dk c S) (hct : c = i * G.length + t) (ht : t < G.length)
    (hi : i < S.1.size) :
    Inv n r M U par dk (c + 1) (bodyB n r i (U i) S G[t]!) ∧
      i < (bodyB n r i (U i) S G[t]!).1.size := by
  obtain ⟨m, hm0, hmM, hs1, hs2, hS1, hSp, hmc, hmg, hlast⟩ := hc
  have him : i < m := by omega
  have hiM : i < M := by omega
  obtain ⟨hkM, hkU⟩ := hO.step i hiM t ht
  generalize hk : cl i t = k at hkM hkU
  have hcont : S.2.2.contains (keyNat n r (applyTab G[t]! (U i))) = true ↔ k < m := by
    rw [← hkU, hmc]
    constructor
    · rintro ⟨j, hj, e⟩
      rw [hO.key j (by omega) k hkM e] at hj
      exact hj
    · intro h
      exact ⟨k, h, rfl⟩
  have hdisc := hO.disc i hiM t ht
  rw [hk] at hdisc
  by_cases hkm : k < m
  · have hf := hcont.2 hkm
    have e : bodyB n r i (U i) S G[t]! = S := by
      unfold bodyB
      rw [if_pos hf]
    rw [e]
    refine ⟨⟨m, hm0, hmM, hs1, hs2, hS1, hSp, hmc, hmg, fun k' hk'0 hk'M => ?_⟩, by omega⟩
    constructor
    · intro h
      have := (hlast k' hk'0 hk'M).1 h
      omega
    · intro h
      by_cases hlt : dk k' < c
      · exact (hlast k' hk'0 hk'M).2 hlt
      · have hdk : dk k' = c := by omega
        obtain ⟨-, t', ht', hd, hcl'⟩ := hO.par_spec k' hk'M hk'0
        have h2 : par k' * G.length + t' = i * G.length + t := by rw [← hd, hdk, hct]
        obtain ⟨h3, h4⟩ := divmod_eq ht' ht h2
        rw [h3, h4, hk] at hcl'
        rw [← hcl']
        exact hkm
  · have hf : ¬ S.2.2.contains (keyNat n r (applyTab G[t]! (U i))) = true :=
      fun h => hkm (hcont.1 h)
    have e : bodyB n r i (U i) S G[t]! = (S.1.push (U k), S.2.1.push i,
        S.2.2.insert (keyNat n r (U k)) S.1.size) := by
      unfold bodyB
      rw [if_neg hf, hkU]
    have hk0 : 0 < k := by omega
    have hdkc : dk k = c := by
      have h1 : dk k ≤ c := by
        rcases hdisc with h | h
        · omega
        · omega
      have h2 : ¬ dk k < c := fun h => hkm ((hlast k hk0 hkM).2 h)
      omega
    have hkm' : m = k := by
      by_contra hne
      have hmk : m < k := by omega
      have h1 := hO.mono_lt hm0 k hmk hkM
      have h2 := (hlast m hm0 (by omega)).2 (by omega)
      omega
    subst hkm'
    obtain ⟨-, t', ht', hd, hcl'⟩ := hO.par_spec m hkM hk0
    have h2 : par m * G.length + t' = i * G.length + t := by rw [← hd, hdkc, hct]
    obtain ⟨hpi, -⟩ := divmod_eq ht' ht h2
    have hnotN : ∀ j < m, keyNat n r (U j) ≠ keyNat n r (U m) := fun j hj e' => by
      have := hO.key j (by omega) m hkM e'
      omega
    have hpush1 : (S.1.push (U m))[m]! = U m := by
      have := push_get_eq S.1 (U m)
      rwa [hs1] at this
    have hpush2 : (S.2.1.push i)[m]! = i := by
      have := push_get_eq S.2.1 i
      rwa [hs2] at this
    rw [e]
    refine ⟨⟨m + 1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show (S.1.push (U m)).size = m + 1
      rw [Array.size_push, hs1]
    · show (S.2.1.push i).size = m + 1
      rw [Array.size_push, hs2]
    · intro k' hk'
      show (S.1.push (U m))[k']! = U k'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | rfl
      · rw [push_get_lt _ _ (by omega), hS1 k' h]
      · exact hpush1
    · intro k' hk' hk'0
      show (S.2.1.push i)[k']! = par k'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | rfl
      · rw [push_get_lt _ _ (by omega), hSp k' h hk'0]
      · rw [hpush2, hpi]
    · intro y
      show (S.2.2.insert (keyNat n r (U m)) S.1.size).contains y = true ↔ _
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmc]
      constructor
      · rintro (rfl | ⟨j, hj, e'⟩)
        · exact ⟨m, by omega, rfl⟩
        · exact ⟨j, by omega, e'⟩
      · rintro ⟨j, hj, e'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, e'⟩
        · exact Or.inl e'
    · intro k' hk'
      show (S.2.2.insert (keyNat n r (U m)) S.1.size).getD (keyNat n r (U k')) 0 = k'
      rw [Std.HashMap.getD_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | rfl
      · rw [if_neg (by rw [beq_iff_eq]; exact fun e' => hnotN k' h e'.symm)]
        exact hmg k' h
      · rw [if_pos (by rw [beq_iff_eq]), hs1]
    · intro k' hk'0 hk'M
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · have := (hlast k' hk'0 hk'M).1 h
          omega
        · omega
      · intro h
        by_contra hn
        have h1 := hO.mono_lt hm0 k' (by omega) hk'M
        omega
    · show i < (S.1.push (U m)).size
      rw [Array.size_push]
      omega

theorem row_step (hO : Order n r G M U par dk cl) {i : Nat} :
    ∀ (e t0 : Nat), t0 + e = G.length → ∀ S : St, Inv n r M U par dk (i * G.length + t0) S →
    i < S.1.size →
    Inv n r M U par dk (i * G.length + G.length) ((G.drop t0).foldl (bodyB n r i (U i)) S) ∧
      i < ((G.drop t0).foldl (bodyB n r i (U i)) S).1.size := by
  intro e
  induction e with
  | zero =>
    intro t0 ht0 S hc hi
    have e : t0 = G.length := by omega
    subst e
    rw [List.drop_of_length_le (Nat.le_refl _)]
    exact ⟨hc, hi⟩
  | succ e ih =>
    intro t0 ht0 S hc hi
    have ht : t0 < G.length := by omega
    rw [List.drop_eq_getElem_cons ht, List.foldl_cons, ← getElem!_pos G t0 ht]
    obtain ⟨h1, h2⟩ := body_step hO hc rfl ht hi
    rw [show i * G.length + t0 + 1 = i * G.length + (t0 + 1) by omega] at h1
    exact ih (t0 + 1) (by omega) _ h1 h2

theorem final_size (hO : Order n r G M U par dk cl) {i : Nat} {S : St}
    (hc : Inv n r M U par dk (i * G.length) S) (hi : S.1.size ≤ i) : S.1.size = M := by
  obtain ⟨m, hm0, hmM, hs1, -, -, -, -, -, hlast⟩ := hc
  by_contra hne
  have hmM' : m < M := by omega
  have h1 : ¬ dk m < i * G.length := fun h => by
    have := (hlast m hm0 hmM').2 h
    omega
  have h2 := hO.dk_lt hmM' hm0
  obtain ⟨hp, -⟩ := hO.par_spec m hmM' hm0
  have h3 : (par m + 1) * G.length ≤ i * G.length := Nat.mul_le_mul_right _ (by omega)
  omega

theorem loop_order (hO : Order n r G M U par dk cl) : ∀ (f i : Nat) (S : St),
    Inv n r M U par dk (i * G.length) S → M ≤ i + f →
    (bfsLoopB n r G f i S).1.size = M ∧ (∀ k < M, (bfsLoopB n r G f i S).1[k]! = U k) ∧
      (∀ k < M, 0 < k → (bfsLoopB n r G f i S).2.1[k]! = par k) ∧
      (∀ k < M, (bfsLoopB n r G f i S).2.2.getD (keyNat n r (U k)) 0 = k) := by
  have fin : ∀ S : St, Inv n r M U par dk (0 * 0 + 0) S → True := fun _ _ => trivial
  intro f
  induction f with
  | zero =>
    intro i S hc hf
    have e : bfsLoopB n r G 0 i S = S := rfl
    rw [e]
    obtain ⟨m, hm0, hmM, hs1, hs2, hS1, hSp, hmc, hmg, hlast⟩ := hc
    have hm : m = M := by
      have := final_size hO (i := i) ⟨m, hm0, hmM, hs1, hs2, hS1, hSp, hmc, hmg, hlast⟩ (by omega)
      omega
    subst hm
    exact ⟨hs1, hS1, hSp, hmg⟩
  | succ f ih =>
    intro i S hc hf
    rw [bfsLoopB_succ]
    by_cases hlt : i < S.1.size
    · rw [if_pos hlt]
      have hS1 : S.1[i]! = U i := by
        obtain ⟨m, -, -, hs1, -, hS1, -⟩ := hc
        exact hS1 i (by omega)
      rw [hS1]
      have := row_step hO (i := i) G.length 0 (Nat.zero_add _) S (by simpa using hc) hlt
      rw [List.drop_zero] at this
      apply ih (i + 1) _ _ (by omega)
      rw [Nat.succ_mul]
      exact this.1
    · rw [if_neg hlt]
      have hM := final_size hO hc (by omega)
      obtain ⟨m, hm0, hmM, hs1, hs2, hS1, hSp, hmc, hmg, hlast⟩ := hc
      have hm : m = M := by omega
      subst hm
      exact ⟨hs1, hS1, hSp, hmg⟩

theorem init_inv (hO : Order n r G M U par dk cl) {o : List Nat} (hM : 0 < M) (hU0 : U 0 = o) :
    Inv n r M U par dk (0 * G.length) (#[o], #[0],
      (∅ : Std.HashMap Nat Nat).insert (keyNat n r o) 0) := by
  refine ⟨1, by omega, hM, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have : k = 0 := by omega
    subst this
    rw [hU0]
    rfl
  · intro k hk hk0
    omega
  · intro y
    simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
    constructor
    · rintro rfl
      exact ⟨0, by omega, by rw [hU0]⟩
    · rintro ⟨k, hk, rfl⟩
      have : k = 0 := by omega
      subst this
      rw [hU0]
  · intro k hk
    have : k = 0 := by omega
    subst this
    rw [hU0]
    simp only [Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
  · intro k hk0 hkM
    rw [Nat.zero_mul]
    constructor
    · intro h
      omega
    · intro h
      omega

theorem enum_order {B : List Nat} {Gi : List (Array Nat)}
    (hO : Order n B.length G M U par dk cl) (hM : 0 < M) (hU0 : U 0 = ptsOf B G) (fuel : Nat)
    (hfuel : M ≤ fuel) :
    (bfsEnumB n B G Gi fuel).1.size = M ∧ (∀ k < M, (bfsEnumB n B G Gi fuel).1[k]! = U k) ∧
      (∀ k < M, 0 < k → (bfsEnumB n B G Gi fuel).2.1[k]! = par k) ∧
      ∀ i < M, ∀ j < G.length,
        (bfsEnumB n B G Gi fuel).2.2[i * (G.length + Gi.length) + j]! = cl i j := by
  obtain ⟨hsz, hU, hp, hg⟩ := loop_order hO fuel 0 _ (init_inv hO hM hU0) (by omega)
  generalize hSf : bfsLoopB n B.length G fuel 0 (#[ptsOf B G], #[0],
    (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) = S at hsz hU hp hg
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hSf]
  rw [hbe]
  refine ⟨hsz, hU, hp, fun i hi j hj => ?_⟩
  dsimp only
  rw [arr_getN, cl_fold, ← List.length_append]
  rw [(flatMap_getD (G ++ Gi) _ S.1.size).2 i (by omega) j (by simp; omega),
    getBang_append_left hj, hU i hi, ← (hO.step i hi j hj).2, hg _ (hO.step i hi j hj).1]

end Loop

theorem base_setup {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (zn gn gin hn hin k fuel M lg : Nat) (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true) :
    (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 ∧
    (∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]!) ∧
    (∀ p ∈ qp, p.1 < (slpTabsA ta.toArray tb.toArray prog).size ∧
      p.2 < (slpTabsA ta.toArray tb.toArray prog).size) ∧
    (∀ b ∈ B, b < n) ∧
    (∀ t < qp.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l =
        applyTab (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)[t]! l) ∧
    ptsW w B (fstT TF qp) =
      ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) ∧
    M = 2 ^ k ∧ M ≤ fuel ∧
    (∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b)) ∧
    Rep n w (TF 0) ta.toArray ∧ Rep n w (TF 1) tb.toArray := by
  rw [baseSK] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm, hRS, hK2, -, hqpb, hfive, hqinv, hginv, hhinv, hB,
    hrows, hMk, hMf, hmo, hmg, hmh, hnc⟩ := h
  obtain ⟨hzn, hgn, hgin, hhn, hhin⟩ := hfive
  have hnodes : ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
    intro q hq
    have hKm' := Nat.le_of_ble_eq_true hKm
    rw [lenA_eq, Nat.add_eq, Nat.mul_eq] at hKm'
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hKm'
        omega
      · exact h0
    have hc : (2 + q) / m < K := by
      rw [Nat.div_lt_iff_lt_mul hm0]
      omega
    have := allR_true (hnd _ hc) ((2 + q) % m) (Nat.mod_lt _ hm0)
    rw [Nat.div_add_mod'] at this
    dsimp only at this
    have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q) (Nat.add (lenA prog) 2)) = true := by
      rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
      constructor <;> omega
    have := impB_true this h2
    rw [P.beq_iff, nthP_eq, show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
    exact this
  have hTs : (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 := by
    rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  have hRepT : ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]! := by
    rw [slpTabsA]
    apply slpTF_rep prog #[ta.toArray, tb.toArray]
    · intro j hj
      rcases j with _ | _ | j
      · rw [P.beq_iff.1 hTF0]
        exact rep_codeK hw hta
      · rw [P.beq_iff.1 hTF1]
        exact rep_codeK hw htb
      · simp at hj
    · exact slpOKK_spec' prog 2 hso
    · intro q hq
      exact hnodes q hq
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT ⊢
  have hNT : Nat.add (lenA prog) 2 = T.size := by rw [hTs, lenA_eq, Nat.add_eq]
  rw [hNT] at hqpb hzn hgn hgin hhn hhin
  rw [P.blt_iff] at hzn hgn hgin hhn hhin
  rw [allA_eq, List.all_eq_true] at hqpb hqinv
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hqpb p hp
    rw [andB_eq, Bool.and_eq_true, P.blt_iff, P.blt_iff] at this
    exact this
  rw [allL_eq, List.all_eq_true] at hB
  have hB' : ∀ b ∈ B, b < n := fun b hb => P.blt_iff.1 (hB b hb)
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [hGdef, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨TF p.1, hRepT _ (hq1' p hp).1⟩
  have hfor : ∀ l : List (Nat × Nat), (∀ p ∈ l, p.1 < T.size) →
      List.Forall₂ (fun c s => Rep n w c s) (l.map fun p => TF p.1) (l.map fun p => T[p.1]!) := by
    intro l hl
    induction l with
    | nil => exact List.Forall₂.nil
    | cons p l ih =>
      exact List.Forall₂.cons (hRepT _ (hl p (List.mem_cons_self ..)))
        (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
  have hpts : ptsW w B (fstT TF qp) = ptsOf B G := by
    rw [fstT_eq]
    exact ptsW_eq hB' (hfor qp fun p hp => (hq1' p hp).1)
  rw [hpts] at hmo hmg hmh
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (hB' b hb)).1
  have hlt2 : ∀ {l : List Nat}, (∀ x ∈ l, x < n) → ∀ x ∈ l, x < 2 ^ w :=
    fun hl x hx => Nat.lt_of_lt_of_le (hl x hx) hw
  have hRS' : n ≤ 64 * RS := Nat.le_of_ble_eq_true hRS
  have hrowsT : ∀ t (ht : t < qp.length), ∀ k' < RS,
      RT (t * RS + k') = rowW w (TF qp[t].1) k' := by
    intro t ht k' hk'
    have := rowsT_go (fstT TF qp) 0 hrows t (by rw [fstT_eq, List.length_map]; exact ht) k' hk'
    rw [Nat.zero_add, fstT_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht] at this
    exact this
  have happ : ∀ t < qp.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l = applyTab G[t]! l := by
    intro t ht l hl
    rw [hGj t ht]
    exact imgsR_rep hRS' (hrowsT t ht) (hRepT _ (hq1' _ (List.getElem_mem ht)).1) hl
  have hM : 0 < M := by
    rw [P.beq_iff.1 hMk]
    exact Nat.two_pow_pos k
  have hent : ∀ j < M, entS w (lenA B) (lenA (ptsOf B G)) M lg (lenA qp) (imgsR w RS RT) E PG
      (codeK w (ptsOf B G)) (codeK w (imgsW w (TF zn) (ptsOf B G))) j = true := by
    intro j hj
    have hK2' := Nat.le_of_ble_eq_true hK2
    rw [Nat.mul_eq] at hK2'
    have hL0 : 0 < L2 := by
      rcases Nat.eq_zero_or_pos L2 with h0 | h0
      · rw [h0, Nat.mul_zero] at hK2'
        omega
      · exact h0
    have hc : j / L2 < K2 := by
      rw [Nat.div_lt_iff_lt_mul hL0]
      omega
    have := hs _ hc
    rw [setS] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (j % L2) (Nat.mod_lt _ hL0)
    rw [Nat.div_add_mod'] at this
    exact impB_true this (P.blt_iff.2 hj)
  rw [lenA_eq, lenA_eq, lenA_eq] at hent
  have hstrict : ∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) ((entS_spec (hent b (by omega))).1 hb)
      · exact (entS_spec (hent a (by omega))).1 hb
  exact ⟨hTs, hRepT, hq1', hB', happ, hpts, P.beq_iff.1 hMk, Nat.le_of_ble_eq_true hMf, hstrict,
    by rw [P.beq_iff.1 hTF0]; exact rep_codeK hw hta,
    by rw [P.beq_iff.1 hTF1]; exact rep_codeK hw htb⟩


theorem bfsI_spec {w nb r M lg W g : Nat} {app : Nat → List Nat → List Nat}
    {E BO IB PT CT : Nat → Nat} {oC i : Nat}
    (h : bfsI w nb r M lg W g app E BO IB PT CT oC i = true) :
    BO i < M ∧ IB (BO i) = i ∧ (i = 0 → E (BO i) = oC) ∧
    (∀ t < g, E (findS w nb M lg E (keyC w nb (codeK w (app t (decW w r (E (BO i))))))) =
        codeK w (app t (decW w r (E (BO i)))) ∧
      IB (findS w nb M lg E (keyC w nb (codeK w (app t (decW w r (E (BO i))))))) =
        fieldT W CT (i * (g + g) + t) ∧ fieldT W CT (i * (g + g) + t) < M ∧
      (fieldT W CT (i * (g + g) + t) = 0 ∨
        discK W g PT CT (fieldT W CT (i * (g + g) + t)) ≤ i * g + t)) ∧
    (i = 0 ∨ (fieldT W PT i < i ∧ discT W g CT (fieldT W PT i) i < g ∧
      (i + 1 < M → discK W g PT CT i < discK W g PT CT (i + 1)))) := by
  rw [bfsI] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨P.blt_iff.1 h1, P.beq_iff.1 h2, fun hi => P.beq_iff.1 (impB_true h3 (P.beq_iff.2 hi)),
    fun t ht => ?_, ?_⟩
  · rw [rangeK_eq', allL_eq, List.all_eq_true] at h4
    have := h4 t (List.mem_range.2 ht)
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, orB_eq, Bool.or_eq_true,
      Nat.add_eq, Nat.mul_eq] at this
    obtain ⟨e1, e2, e3, e4⟩ := this
    refine ⟨P.beq_iff.1 e1, P.beq_iff.1 e2, P.blt_iff.1 e3, ?_⟩
    rcases e4 with e4 | e4
    · exact Or.inl (P.beq_iff.1 e4)
    · exact Or.inr (Nat.le_of_ble_eq_true e4)
  · rw [orB_eq, Bool.or_eq_true] at h5
    rcases h5 with h5 | h5
    · exact Or.inl (P.beq_iff.1 h5)
    · right
      simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h5
      obtain ⟨e1, e2, e3⟩ := h5
      refine ⟨P.blt_iff.1 e1, P.blt_iff.1 e2, fun hi => P.blt_iff.1 (impB_true e3 (P.blt_iff.2 hi))⟩

theorem find_go (f : Nat → Bool) (d : Nat) : ∀ (m j : Nat),
    Nat.rec (motive := fun _ => Nat → Nat) (fun _ => d)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m j =
    ((List.range' j m).find? f).getD d
  | 0, _ => rfl
  | m + 1, j => by
    change Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => d)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m (j + 1)) j
        (f j) = _
    rw [List.range'_succ, List.find?_cons]
    cases f j
    · exact find_go f d m (j + 1)
    · rfl

theorem discT_eq (W g : Nat) (CT : Nat → Nat) (p i : Nat) : discT W g CT p i =
    ((List.range g).find? fun t => Nat.beq (fieldT W CT (Nat.add (Nat.mul p (Nat.add g g)) t)) i).getD
      g := by
  rw [discT, List.range_eq_range']
  exact find_go _ g g 0

theorem disc_spec {W g : Nat} {PT CT : Nat → Nat} {i : Nat}
    (h : discT W g CT (fieldT W PT i) i < g) :
    ∃ t, t < g ∧ discT W g CT (fieldT W PT i) i = t ∧
      fieldT W CT (fieldT W PT i * (g + g) + t) = i := by
  rw [discT_eq] at h
  cases hf : (List.range g).find? fun t =>
      Nat.beq (fieldT W CT (Nat.add (Nat.mul (fieldT W PT i) (Nat.add g g)) t)) i with
  | none => rw [hf] at h; simp at h
  | some t =>
    have h1 := List.find?_some hf
    refine ⟨t, List.mem_range.1 (List.mem_of_find?_eq_some hf), ?_, P.beq_iff.1 h1⟩
    rw [discT_eq, hf]
    rfl

theorem findS_lt {w nb M lg : Nat} {E : Nat → Nat} {key : Nat} (hM : 0 < M) :
    findS w nb M lg E key < M := findS_go lg 0 hM

theorem order_of_bfsI {n w W M lg : Nat} (hw : n ≤ 2 ^ w) {B : List Nat} {G : List (Array Nat)}
    {app : Nat → List Nat → List Nat} {E BO IB PT CT : Nat → Nat} (hM : 0 < M)
    (hov : ∀ x ∈ ptsOf B G, x < n) (hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n)
    (happ : ∀ t < G.length, ∀ l : List Nat, (∀ y ∈ l, y < n) → app t l = applyTab G[t]! l)
    (hbfs : ∀ i < M, bfsI w B.length (ptsOf B G).length M lg W G.length app E BO IB PT CT
      (codeK w (ptsOf B G)) i = true)
    (hstrict : ∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b)) :
    Order n B.length G M (fun i => decW w (ptsOf B G).length (E (BO i))) (fieldT W PT)
      (discK W G.length PT CT) (fun i t => fieldT W CT (i * (G.length + G.length) + t)) ∧
    decW w (ptsOf B G).length (E (BO 0)) = ptsOf B G ∧
    (∀ i < M, BO i < M ∧ IB (BO i) = i) ∧ (∀ j < M, ∃ i < M, BO i = j) ∧
    (∀ i < M, Val n (ptsOf B G).length (decW w (ptsOf B G).length (E (BO i))) ∧
      E (BO i) = codeK w (decW w (ptsOf B G).length (E (BO i)))) := by
  have hsp := fun i (hi : i < M) => bfsI_spec (hbfs i hi)
  have hlt2 : ∀ {l : List Nat}, (∀ x ∈ l, x < n) → ∀ x ∈ l, x < 2 ^ w :=
    fun hl x hx => Nat.lt_of_lt_of_le (hl x hx) hw
  have hBOlt : ∀ i < M, BO i < M := fun i hi => (hsp i hi).1
  have hIB : ∀ i < M, IB (BO i) = i := fun i hi => (hsp i hi).2.1
  have hinj : ∀ a < M, ∀ b < M, BO a = BO b → a = b := fun a ha b hb e => by
    rw [← hIB a ha, ← hIB b hb, e]
  have hsurj : ∀ j < M, ∃ i < M, BO i = j := by
    have hf : Function.Injective (fun i : Fin M => (⟨BO i, hBOlt i i.2⟩ : Fin M)) := by
      intro a b e
      apply Fin.ext
      exact hinj a a.2 b b.2 (congrArg Fin.val e)
    intro j hj
    obtain ⟨i, hi⟩ := Finite.injective_iff_surjective.1 hf ⟨j, hj⟩
    exact ⟨i, i.2, congrArg Fin.val hi⟩
  have hfind : ∀ i < M, ∀ t < G.length, fieldT W CT (i * (G.length + G.length) + t) < M ∧
      E (BO (fieldT W CT (i * (G.length + G.length) + t))) =
        codeK w (app t (decW w (ptsOf B G).length (E (BO i)))) := by
    intro i hi t ht
    obtain ⟨h1, h2, h3, h4⟩ := (hsp i hi).2.2.2.1 t ht
    have hj := findS_lt (w := w) (nb := B.length) (lg := lg) (E := E)
      (key := keyC w B.length (codeK w (app t (decW w (ptsOf B G).length (E (BO i)))))) hM
    obtain ⟨i', hi', e'⟩ := hsurj _ hj
    have hk : i' = fieldT W CT (i * (G.length + G.length) + t) := by
      rw [← h2, ← e', hIB i' hi']
    subst hk
    exact ⟨h3, by rw [e']; exact h1⟩
  have hVal : ∀ a, a < M → Val n (ptsOf B G).length (decW w (ptsOf B G).length (E (BO a))) ∧
      E (BO a) = codeK w (decW w (ptsOf B G).length (E (BO a))) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · have e := (hsp 0 ha).2.2.1 rfl
        rw [e, decW_codeK' (hlt2 hov) rfl]
        exact ⟨⟨rfl, hov⟩, rfl⟩
      · rcases (hsp a ha).2.2.2.2 with h0 | ⟨hp, hd, -⟩
        · omega
        · obtain ⟨t, ht, -, hct⟩ := disc_spec hd
          have hpM : fieldT W PT a < M := by omega
          obtain ⟨hv, -⟩ := ih _ hp hpM
          have ⟨hk1, hk2⟩ := hfind _ hpM t ht
          rw [hct] at hk2
          rw [happ t ht _ hv.2] at hk2
          have hV : Val n (ptsOf B G).length (applyTab G[t]! (decW w (ptsOf B G).length
              (E (BO (fieldT W PT a))))) :=
            ⟨by rw [applyTab, List.length_map]; exact hv.1, fun x hx => by
              rw [applyTab, List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              exact hGlt t ht y (hv.2 y hy)⟩
          rw [hk2, decW_codeK' (hlt2 hV.2) hV.1]
          exact ⟨hV, rfl⟩
  have hU0 : decW w (ptsOf B G).length (E (BO 0)) = ptsOf B G := by
    rw [(hsp 0 hM).2.2.1 rfl, decW_codeK' (hlt2 hov) rfl]
  have hstepU : ∀ i < M, ∀ t < G.length,
      fieldT W CT (i * (G.length + G.length) + t) < M ∧
      decW w (ptsOf B G).length (E (BO (fieldT W CT (i * (G.length + G.length) + t)))) =
        applyTab G[t]! (decW w (ptsOf B G).length (E (BO i))) := by
    intro i hi t ht
    obtain ⟨h1, h2⟩ := hfind i hi t ht
    have hv := (hVal i hi).1
    have hV : Val n (ptsOf B G).length (applyTab G[t]! (decW w (ptsOf B G).length (E (BO i)))) :=
      ⟨by rw [applyTab, List.length_map]; exact hv.1, fun x hx => by
        rw [applyTab, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hGlt t ht y (hv.2 y hy)⟩
    refine ⟨h1, ?_⟩
    rw [h2, happ t ht _ hv.2, decW_codeK' (hlt2 hV.2) hV.1]
  refine ⟨⟨?_, hstepU, ?_, ?_, ?_⟩, hU0, fun i hi => ⟨hBOlt i hi, hIB i hi⟩, hsurj, hVal⟩
  ·
    intro a ha b hb e
    have hva := hVal a ha
    have hvb := hVal b hb
    rw [keyNat_eq_iff hva.1 hvb.1] at e
    have e2 : keyC w B.length (E (BO a)) = keyC w B.length (E (BO b)) := by
      rw [hva.2, hvb.2, keyC_codeK (hlt2 hva.1.2), keyC_codeK (hlt2 hvb.1.2), e]
    have hBa := hBOlt a ha
    have hBb := hBOlt b hb
    rcases Nat.lt_trichotomy (BO a) (BO b) with h | h | h
    · exact absurd e2 (Nat.ne_of_lt (hstrict _ _ h hBb))
    · exact hinj a ha b hb h
    · exact absurd e2.symm (Nat.ne_of_lt (hstrict _ _ h hBa))
  · intro i hi t ht
    exact (hsp i hi).2.2.2.1 t ht |>.2.2.2
  · intro k hk hk0
    rcases (hsp k hk).2.2.2.2 with h0 | ⟨hp, hd, -⟩
    · omega
    · obtain ⟨t, ht, hdt, hct⟩ := disc_spec hd
      refine ⟨hp, t, ht, ?_, hct⟩
      show fieldT W PT k * G.length + discT W G.length CT (fieldT W PT k) k = _
      rw [hdt]
  · intro k hk0 hk1
    rcases (hsp k (by omega)).2.2.2.2 with h0 | ⟨-, -, hm⟩
    · omega
    · exact hm hk1

theorem bfsS_order {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat) (W : Nat) (BO IB PT CT : Nat → Nat)
    (K3 L3 : Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true)
    (hb : ∀ c < K3, bfsS w B qp TF RS RT M lg W E BO IB PT CT (c * L3) L3 = true)
    (hcov : M ≤ K3 * L3) :
    Order n B.length (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) M
      (fun i => decW w (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length
        (E (BO i))) (fieldT W PT)
      (discK W (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!).length PT CT)
      (fun i t => fieldT W CT (i * ((qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!).length +
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!).length) + t)) ∧
    decW w (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length
      (E (BO 0)) = ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) := by
  obtain ⟨hTs, hRepT, hq1', hB', happ, hpts, hMk, hMf, hstrict, -, -⟩ :=
    base_setup hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG h hnd hs
  have hM : 0 < M := by
    rw [hMk]
    exact Nat.two_pow_pos k
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT hq1' happ hpts ⊢
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := List.length_map _
  have hGil : Gi.length = qp.length := List.length_map _
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n := by
    intro t ht y hy
    have ht' : t < qp.length := by omega
    rw [hGj t ht']
    exact ((hRepT _ (hq1' _ (List.getElem_mem ht')).1).2 y hy).1
  have hov : ∀ x ∈ ptsOf B G, x < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      rw [← getElem!_pos G t ht]
      exact hGlt t ht b (hB' b hb)
  have hbfs : ∀ i < M, bfsI w B.length (ptsOf B G).length M lg W G.length (imgsR w RS RT) E BO IB
      PT CT (codeK w (ptsOf B G)) i = true := by
    intro i hi
    have hK3 : 0 < L3 := by
      rcases Nat.eq_zero_or_pos L3 with h0 | h0
      · rw [h0, Nat.mul_zero] at hcov
        omega
      · exact h0
    have hc : i / L3 < K3 := by
      rw [Nat.div_lt_iff_lt_mul hK3]
      omega
    have := hb _ hc
    rw [bfsS] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (i % L3) (Nat.mod_lt _ hK3)
    rw [Nat.div_add_mod'] at this
    have := impB_true this (P.blt_iff.2 hi)
    rw [lenA_eq, lenA_eq, lenA_eq] at this
    rw [hGl]
    exact this
  have happ' : ∀ t < G.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l = applyTab G[t]! l := fun t ht l hl => happ t (by omega) l hl
  obtain ⟨hO, hU0, -, -, -⟩ := order_of_bfsI (W := W) (lg := lg) hw hM hov hGlt happ' hbfs
    hstrict
  exact ⟨hO, hU0⟩

theorem bfsS_enum {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat) (W : Nat) (BO IB PT CT : Nat → Nat)
    (K3 L3 : Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true)
    (hb : ∀ c < K3, bfsS w B qp TF RS RT M lg W E BO IB PT CT (c * L3) L3 = true)
    (hcov : M ≤ K3 * L3) :
    0 < M ∧
    (∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b)) ∧
    (∀ i < M, BO i < M ∧ IB (BO i) = i) ∧ (∀ j < M, ∃ i < M, BO i = j) ∧
    (∀ i < M, Val n (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length
      (decW w (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length
        (E (BO i))) ∧
      E (BO i) = codeK w (decW w
        (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length (E (BO i)))) ∧
    (∀ i < M, 0 < i → fieldT W PT i < i ∧ 0 < qp.length) ∧
    (∀ i < M, ∀ j < qp.length, fieldT W CT (i * (qp.length + qp.length) + j) < M) ∧
    ∀ X, X = bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel →
      X.1.size = M ∧
      (∀ i < M, X.1[i]! = decW w
        (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)).length
        (E (BO i))) ∧
      (∀ i < M, 0 < i → X.2.1[i]! = fieldT W PT i) ∧
      ∀ i < M, ∀ j < qp.length, X.2.2[i * (qp.length + qp.length) + j]! =
        fieldT W CT (i * (qp.length + qp.length) + j) := by
  obtain ⟨hTs, hRepT, hq1', hB', happ, hpts, hMk, hMf, hstrict, -, -⟩ :=
    base_setup hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG h hnd hs
  have hM : 0 < M := by
    rw [hMk]
    exact Nat.two_pow_pos k
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT hq1' happ hpts ⊢
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := List.length_map _
  have hGil : Gi.length = qp.length := List.length_map _
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n := by
    intro t ht y hy
    have ht' : t < qp.length := by omega
    rw [hGj t ht']
    exact ((hRepT _ (hq1' _ (List.getElem_mem ht')).1).2 y hy).1
  have hov : ∀ x ∈ ptsOf B G, x < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      rw [← getElem!_pos G t ht]
      exact hGlt t ht b (hB' b hb)
  have hbfs : ∀ i < M, bfsI w B.length (ptsOf B G).length M lg W G.length (imgsR w RS RT) E BO IB
      PT CT (codeK w (ptsOf B G)) i = true := by
    intro i hi
    have hK3 : 0 < L3 := by
      rcases Nat.eq_zero_or_pos L3 with h0 | h0
      · rw [h0, Nat.mul_zero] at hcov
        omega
      · exact h0
    have hc : i / L3 < K3 := by
      rw [Nat.div_lt_iff_lt_mul hK3]
      omega
    have := hb _ hc
    rw [bfsS] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (i % L3) (Nat.mod_lt _ hK3)
    rw [Nat.div_add_mod'] at this
    have := impB_true this (P.blt_iff.2 hi)
    rw [lenA_eq, lenA_eq, lenA_eq] at this
    rw [hGl]
    exact this
  have happ' : ∀ t < G.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l = applyTab G[t]! l := fun t ht l hl => happ t (by omega) l hl
  obtain ⟨hO, hU0, hBO, hsurj, hVal⟩ := order_of_bfsI (W := W) (lg := lg) hw hM hov hGlt happ' hbfs
    hstrict
  refine ⟨hM, hstrict, hBO, hsurj, hVal, fun i hi hi0 => ?_, fun i hi j hj => ?_, fun X hX => ?_⟩
  · obtain ⟨h1, t, ht, -⟩ := hO.par_spec i hi hi0
    exact ⟨h1, by omega⟩
  · have := (hO.step i hi j (by omega)).1
    rwa [hGl] at this
  subst hX
  obtain ⟨e1, e2, e3, e4⟩ := enum_order (Gi := Gi) hO hM hU0 fuel hMf
  rw [hGl, hGil] at e4
  refine ⟨e1, e2, e3, fun i hi j hj => ?_⟩
  rw [e4 i hi j (by omega)]

end CFSG.KC.LQT.BSP

end
