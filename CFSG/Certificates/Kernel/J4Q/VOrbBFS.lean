module

public import CFSG.Certificates.Kernel.J4Q.VOrbStorage
public import CFSG.Certificates.Kernel.J4Q.RepQT2B

public section

namespace CFSG.KC.J4Q.VOrbBFS

open CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KC.J4Q.VOrbStorage

def StepOK {β : Type} (I Q : β → Prop) : ForInStep β → Prop
  | .yield b => I b
  | .done b => Q b

theorem forIn_range'_inv {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) : ∀ (m s : Nat) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b → StepOK (I (q + 1)) Q (f q b)) →
    (∀ b, I (s + m) b → Q b) → I s b → Q (forIn (List.range' s m) b f)
  | 0, s, b, _, hend, h0 => hend b (by simpa using h0)
  | m + 1, s, b, hstep, hend, h0 => by
    rw [List.range'_succ, List.forIn_cons]
    have hs := hstep s b (Nat.le_refl _) (by omega) h0
    cases hf : f s b with
    | done b' =>
      rw [hf] at hs
      exact hs
    | yield b' =>
      rw [hf] at hs
      exact forIn_range'_inv I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [show s + (m + 1) = s + 1 + m by omega])) hs

theorem forIn_range_inv {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β)
    (hstep : ∀ q b, q < n → I q b → StepOK (I (q + 1)) Q (f q b))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact forIn_range'_inv I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

theorem forIn_range_bind {β γ : Type} (I : Nat → β → Prop) (P : γ → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β) (g : β → Id γ)
    (hstep : ∀ q b, q < n → I q b → StepOK (I (q + 1)) (fun b => P (g b).run) (f q b))
    (hend : ∀ b, I n b → P (g b).run) (h0 : I 0 b) : P (forIn [:n] b f >>= g).run :=
  forIn_range_inv I (fun b => P (g b).run) f n b hstep hend h0

theorem get!_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem v2N_inj {a b : V2} (h : v2N a = v2N b) : a = b := by
  have hb : a.beq b = true := by rw [beq_v2N, h, Nat.beq_refl]
  exact V2.beq_iff.1 hb

section Probe

variable {bits : Nat}

def home (bits : Nat) (k : V2) : Nat := k.hash.toNat % 2 ^ bits

def slotAt (bits h d : Nat) : Nat := (h + d) % 2 ^ bits

theorem slotAt_lt (h d : Nat) : slotAt bits h d < 2 ^ bits :=
  Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem slotAt_succ (h d : Nat) : (slotAt bits h d + 1) % 2 ^ bits = slotAt bits h (d + 1) := by
  unfold slotAt
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem slotAt_zero {h : Nat} (hh : h < 2 ^ bits) : slotAt bits h 0 = h := by
  unfold slotAt
  rw [Nat.add_zero, Nat.mod_eq_of_lt hh]

theorem slotAt_surj (h : Nat) {s : Nat} (hs : s < 2 ^ bits) :
    ∃ d < 2 ^ bits, slotAt bits h d = s := by
  have hn := Nat.two_pow_pos bits
  have hm : h % 2 ^ bits < 2 ^ bits := Nat.mod_lt _ hn
  refine ⟨(s + 2 ^ bits - h % 2 ^ bits) % 2 ^ bits, Nat.mod_lt _ hn, ?_⟩
  unfold slotAt
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod,
    show h % 2 ^ bits + (s + 2 ^ bits - h % 2 ^ bits) = s + 2 ^ bits by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hs]

structure HInv (bits : Nat) (pts : Array V2) (slots : ByteArray) : Prop where
  size : slots.size = 4 * 2 ^ bits
  range : ∀ s < 2 ^ bits, rdU32 slots s ≤ pts.size
  inj : ∀ s < 2 ^ bits, ∀ t < 2 ^ bits, rdU32 slots s = rdU32 slots t → rdU32 slots s ≠ 0 → s = t
  cover : ∀ i (hi : i < pts.size), ∃ d < 2 ^ bits,
    rdU32 slots (slotAt bits (home bits pts[i]) d) = i + 1 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits pts[i]) d') ≠ 0
  nodup : ∀ i j (hi : i < pts.size) (hj : j < pts.size), pts[i] = pts[j] → i = j

theorem exists_empty {pts : Array V2} {slots : ByteArray} (H : HInv bits pts slots)
    (hsz : pts.size < 2 ^ bits) (h : Nat) : ∃ d < 2 ^ bits, rdU32 slots (slotAt bits h d) = 0 := by
  by_contra hne'
  have hne : ∀ d < 2 ^ bits, rdU32 slots (slotAt bits h d) ≠ 0 :=
    fun d hd h0 => hne' ⟨d, hd, h0⟩
  have hall : ∀ s < 2 ^ bits, rdU32 slots s ≠ 0 := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := slotAt_surj (bits := bits) h hs
    exact hne d hd
  have hc := Finset.card_le_card_of_injOn (s := Finset.range (2 ^ bits))
    (t := Finset.Icc 1 pts.size) (fun s => rdU32 slots s)
    (by
      intro s hs
      have hs' : s < 2 ^ bits := Finset.mem_range.1 hs
      have h1 := hall s hs'
      have h2 := H.range s hs'
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega)
    (by
      intro s hs t ht hst
      exact H.inj s (Finset.mem_range.1 hs) t (Finset.mem_range.1 ht) hst
        (hall s (Finset.mem_range.1 hs)))
  simp only [Finset.card_range, Nat.card_Icc] at hc
  omega

theorem home_eq (k : V2) : k.hash.toNat &&& 2 ^ bits - 1 = home bits k :=
  Nat.and_two_pow_sub_one_eq_mod _ _

theorem home_lt (k : V2) : home bits k < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem vfind_spec {pts : Array V2} {slots : ByteArray} (H : HInv bits pts slots) (k : V2) :
    (vfind pts slots bits k ≠ 0 → ∃ h : vfind pts slots bits k - 1 < pts.size,
      pts[vfind pts slots bits k - 1] = k) ∧
    (k ∈ pts → vfind pts slots bits k ≠ 0) := by
  have hn := Nat.two_pow_pos bits
  let R : Nat → Prop := fun r =>
    (r ≠ 0 → ∃ h : r - 1 < pts.size, pts[r - 1] = k) ∧ (k ∈ pts → r ≠ 0)
  let I : Nat → Option Nat × Nat → Prop := fun j st =>
    st.1 = none ∧ st.2 = slotAt bits (home bits k) j ∧ ∀ d < j,
      rdU32 slots (slotAt bits (home bits k) d) ≠ 0 ∧
      (pts[rdU32 slots (slotAt bits (home bits k) d) - 1]?.getD V2.zero).beq k = false
  have hfound : ∀ i (hi : i < pts.size), pts[i] = k → ∃ d < 2 ^ bits,
      rdU32 slots (slotAt bits (home bits k) d) = i + 1 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0 := by
    intro i hi hik
    obtain ⟨d, hd, h1, h2⟩ := H.cover i hi
    rw [hik] at h1 h2
    exact ⟨d, hd, h1, h2⟩
  have hbeq : ∀ i (hi : i < pts.size), pts[i] = k →
      (pts[i + 1 - 1]?.getD V2.zero).beq k = true := by
    intro i hi hik
    rw [Nat.add_sub_cancel, Array.getElem?_eq_getElem hi, Option.getD_some, hik]
    exact V2.beq_iff.2 rfl
  change R (vfind pts slots bits k)
  unfold vfind
  dsimp only
  refine forIn_range_bind I R _ _ _ _ ?_ ?_ ?_
  · intro j st _ hI
    obtain ⟨h1, h2, h3⟩ := hI
    split
    · rename_i he
      have he' : rdU32 slots st.2 = 0 := by simpa using he
      refine ⟨fun h => (h rfl).elim, fun hk => ?_⟩
      obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 hk
      obtain ⟨d, hd, hd1, hd2⟩ := hfound i hi hik
      rw [h2] at he'
      rcases Nat.lt_trichotomy j d with hjd | hjd | hjd
      · exact (hd2 j hjd he').elim
      · subst hjd
        omega
      · have := (h3 d hjd).2
        rw [hd1, hbeq i hi hik] at this
        exact absurd this (by decide)
    · rename_i he
      have he' : rdU32 slots st.2 ≠ 0 := by simpa using he
      split
      · rename_i hb
        refine ⟨fun _ => ?_, fun _ => he'⟩
        have hr := H.range st.2 (by rw [h2]; exact slotAt_lt _ _)
        have hlt : rdU32 slots st.2 - 1 < pts.size := by omega
        refine ⟨hlt, ?_⟩
        rw [Array.getElem?_eq_getElem hlt, Option.getD_some] at hb
        exact V2.beq_iff.1 hb
      · rename_i hb
        refine ⟨rfl, ?_, ?_⟩
        · dsimp only
          rw [Nat.and_two_pow_sub_one_eq_mod, h2, slotAt_succ]
        · intro d hd
          rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
          · exact h3 d hd
          · rw [← h2]
            exact ⟨he', by simpa using hb⟩
  · rintro ⟨o, h⟩ ⟨h1, h2, h3⟩
    dsimp only at h1
    subst h1
    change R 0
    refine ⟨fun h => (h rfl).elim, fun hk => ?_⟩
    obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 hk
    obtain ⟨d, hd, hd1, _⟩ := hfound i hi hik
    have := (h3 d hd).2
    rw [hd1, hbeq i hi hik] at this
    exact absurd this (by decide)
  · exact ⟨rfl, by rw [home_eq, slotAt_zero (home_lt k)], fun d hd => (Nat.not_lt_zero _ hd).elim⟩

theorem vslot_spec {pts : Array V2} {slots : ByteArray} (H : HInv bits pts slots)
    (hsz : pts.size < 2 ^ bits) (k : V2) :
    ∃ d < 2 ^ bits, vslot slots bits k = slotAt bits (home bits k) d ∧
      rdU32 slots (slotAt bits (home bits k) d) = 0 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0 := by
  let I : Nat → Option Nat × Nat → Prop := fun j st =>
    st.1 = none ∧ st.2 = slotAt bits (home bits k) j ∧ ∀ d < j,
      rdU32 slots (slotAt bits (home bits k) d) ≠ 0
  let R : Nat → Prop := fun r => ∃ d < 2 ^ bits, r = slotAt bits (home bits k) d ∧
      rdU32 slots (slotAt bits (home bits k) d) = 0 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0
  change R (vslot slots bits k)
  unfold vslot
  dsimp only
  refine forIn_range_bind I R _ _ _ _ ?_ ?_ ?_
  · intro j st hj hI
    obtain ⟨h1, h2, h3⟩ := hI
    split
    · rename_i he
      have he' : rdU32 slots st.2 = 0 := by simpa using he
      exact ⟨j, hj, h2, by rw [← h2]; exact he', h3⟩
    · rename_i he
      have he' : rdU32 slots st.2 ≠ 0 := by simpa using he
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only
        rw [Nat.and_two_pow_sub_one_eq_mod, h2, slotAt_succ]
      · intro d hd
        rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
        · exact h3 d hd
        · rw [← h2]
          exact he'
  · intro st hI
    obtain ⟨_, _, h3⟩ := hI
    obtain ⟨d, hd, h0⟩ := exists_empty H hsz (home bits k)
    exact (h3 d hd h0).elim
  · exact ⟨rfl, by rw [home_eq, slotAt_zero (home_lt k)], fun d hd => (Nat.not_lt_zero _ hd).elim⟩

theorem hinv_zeros (hb : 4 * 2 ^ bits < 2 ^ 32) : HInv bits #[] (zeros (4 * 2 ^ bits)) where
  size := size_zeros _
  range s hs := by rw [rdU32_zeros hb hs]; exact Nat.le_refl _
  inj s hs _ _ _ h0 := (h0 (rdU32_zeros hb hs)).elim
  cover i hi := (Nat.not_lt_zero _ hi).elim
  nodup i _ hi := (Nat.not_lt_zero _ hi).elim

theorem hinv_insert {pts : Array V2} {slots : ByteArray} (H : HInv bits pts slots)
    (hb : 4 * 2 ^ bits < 2 ^ 32) (hsz : pts.size < 2 ^ bits) {k : V2} (hk : k ∉ pts) :
    HInv bits (pts.push k) (vinsert pts slots bits k) := by
  obtain ⟨d, hd, hs, h0, hpre⟩ := vslot_spec H hsz k
  have hsl : slots.size < 2 ^ 32 := by rw [H.size]; exact hb
  have hn := Nat.two_pow_pos bits
  set s := vslot slots bits k with hsdef
  have hslt : s < 2 ^ bits := by rw [hs]; exact slotAt_lt _ _
  have haddr : ∀ t < 2 ^ bits, 4 * t + 3 < slots.size := by
    intro t ht
    rw [H.size]
    omega
  have hrd : ∀ t < 2 ^ bits, rdU32 (vinsert pts slots bits k) t =
      if t = s then pts.size + 1 else rdU32 slots t := by
    intro t ht
    unfold vinsert
    rw [← hsdef]
    by_cases hts : t = s
    · subst hts
      rw [ite_eq_left rfl, rdU32_wrU32_self _ hsl (haddr _ ht) (by omega)]
    · rw [ite_eq_right hts, rdU32_wrU32_other _ hsl (haddr _ hslt) (haddr _ ht) (Ne.symm hts)]
  have hs0 : rdU32 slots s = 0 := by rw [hs]; exact h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold vinsert
    rw [size_wrU32, H.size]
  · intro t ht
    rw [hrd t ht, Array.size_push]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (H.range t ht)
  · intro t ht u hu htu hne
    rw [hrd t ht, hrd u hu] at htu
    rw [hrd t ht] at hne
    have hrt := H.range t ht
    have hru := H.range u hu
    by_cases h1 : t = s <;> by_cases h2 : u = s <;> simp only [h1, h2, ite_true, ite_false] at htu hne
    · rw [h1, h2]
    · omega
    · omega
    · exact H.inj t ht u hu htu hne
  · intro i hi
    rw [Array.size_push] at hi
    by_cases hil : i < pts.size
    · obtain ⟨d1, hd1, he, hb1⟩ := H.cover i hil
      have hget : (pts.push k)[i] = pts[i] := Array.getElem_push_lt hil
      refine ⟨d1, hd1, ?_, ?_⟩
      · rw [hget, hrd _ (slotAt_lt _ _)]
        have hne : slotAt bits (home bits pts[i]) d1 ≠ s := by
          intro he'
          rw [he', hs0] at he
          omega
        rw [ite_eq_right hne, he]
      · intro d' hd'
        rw [hget, hrd _ (slotAt_lt _ _)]
        split
        · omega
        · exact hb1 d' hd'
    · have hi' : i = pts.size := by omega
      subst hi'
      have hget : (pts.push k)[pts.size] = k := Array.getElem_push_eq
      refine ⟨d, hd, ?_, ?_⟩
      · rw [hget, hrd _ (slotAt_lt _ _), ← hs, ite_eq_left rfl]
      · intro d' hd'
        rw [hget, hrd _ (slotAt_lt _ _)]
        have hne : slotAt bits (home bits k) d' ≠ s := by
          intro he'
          exact hpre d' hd' (by rw [he']; exact hs0)
        rw [ite_eq_right hne]
        exact hpre d' hd'
  · intro i j hi hj hij
    rw [Array.size_push] at hi hj
    by_cases h1 : i < pts.size <;> by_cases h2 : j < pts.size
    · rw [Array.getElem_push_lt h1, Array.getElem_push_lt h2] at hij
      exact H.nodup i j h1 h2 hij
    · have : j = pts.size := by omega
      subst this
      rw [Array.getElem_push_lt h1, Array.getElem_push_eq] at hij
      exact (hk (hij ▸ Array.getElem_mem h1)).elim
    · have : i = pts.size := by omega
      subst this
      rw [Array.getElem_push_lt h2, Array.getElem_push_eq] at hij
      exact (hk (hij.symm ▸ Array.getElem_mem h2)).elim
    · omega

end Probe

section BFS

variable {ts : Array (Array V2)} {w : V2} {cap bits : Nat} {A : List Nat}

theorem get!_mem {xs : Array V2} {i : Nat} (h : i < xs.size) : xs[i]! ∈ xs := by
  rw [getElem!_pos xs i h]
  exact Array.getElem_mem h

theorem exists_get! {xs : Array V2} {v : V2} (h : v ∈ xs) : ∃ i < xs.size, xs[i]! = v := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
  exact ⟨i, hi, getElem!_pos xs i hi⟩

structure Base (ts : Array (Array V2)) (w : V2) (cap bits : Nat) (A : List Nat)
    (st : Array V2 × Array Nat × Array Nat × ByteArray) : Prop where
  hinv : HInv bits st.1 st.2.2.2
  szp : st.2.1.size = st.1.size
  szl : st.2.2.1.size = st.1.size
  pos : 0 < st.1.size
  le : st.1.size ≤ cap
  root : st.1[0]! = w
  mem : ∀ v ∈ st.1, v.wf = true ∧ v2N v ∈ A
  tree : ∀ i < st.1.size, 0 < i → st.2.1[i]! < i ∧ st.2.2.1[i]! < ts.size ∧
    frApply ts[st.2.2.1[i]!]! st.1[st.2.1[i]!]! = st.1[i]!

def Closed (ts : Array (Array V2)) (q : Nat) (pts : Array V2) : Prop :=
  ∀ i < q, ∀ g < ts.size, frApply ts[g]! pts[i]! ∈ pts

theorem closed_push {q : Nat} {pts : Array V2} (h : Closed ts q pts) (hq : q ≤ pts.size) (y : V2) :
    Closed ts q (pts.push y) := by
  intro i hi g hg
  rw [get!_push_lt _ _ (by omega)]
  exact Array.mem_push_of_mem y (h i hi g hg)

theorem size_eq_cap (hAn : A.Nodup) (hAl : A.length = cap)
    (hreach : ∀ S : Nat → Prop, S (v2N w) →
      (∀ v, S (v2N v) → ∀ g < ts.size, S (v2N (frApply ts[g]! v))) → ∀ x ∈ A, S x)
    {st : Array V2 × Array Nat × Array Nat × ByteArray} (hB : Base ts w cap bits A st)
    (hc : st.1.size = cap ∨ Closed ts st.1.size st.1) : st.1.size = cap := by
  rcases hc with hc | hc
  · exact hc
  have hS := hreach (fun x => ∃ v ∈ st.1, v2N v = x) ⟨w, hB.root ▸ get!_mem hB.pos, rfl⟩
    (by
      rintro v ⟨u, hu, huv⟩ g hg
      rw [v2N_inj huv] at hu
      obtain ⟨i, hi, rfl⟩ := exists_get! hu
      exact ⟨_, hc i hi g hg, rfl⟩)
  have hsub : A ⊆ st.1.toList.map v2N := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hS x hx
    exact List.mem_map_of_mem (Array.mem_toList_iff.2 hv)
  have := hAn.length_le_of_subset hsub
  rw [List.length_map, @Array.length_toList _ st.1] at this
  have := hB.le
  omega

theorem toList_nodup {pts : Array V2} {slots : ByteArray} (H : HInv bits pts slots) :
    (pts.toList.map v2N).Nodup := by
  refine List.Nodup.map (fun a b h => v2N_inj h) ?_
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi : i.1 < pts.size := by simp
  have hj : j.1 < pts.size := by simp
  apply Fin.ext
  apply H.nodup i.1 j.1 hi hj
  simpa [List.get_eq_getElem, Array.getElem_toList] using hij

theorem final (hAl : A.length = cap)
    (hcl : ∀ v, v.wf = true → v2N v ∈ A → ∀ g < ts.size, v2N (frApply ts[g]! v) ∈ A)
    {st : Array V2 × Array Nat × Array Nat × ByteArray} (hB : Base ts w cap bits A st)
    (hsz : st.1.size = cap) :
    vorbOK ts w ⟨st.1, st.2.1, st.2.2.1, st.2.2.2, bits⟩ cap = true := by
  have H := hB.hinv
  have hsub : st.1.toList.map v2N ⊆ A := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact (hB.mem v (Array.mem_toList_iff.1 hv)).2
  have hperm := (List.subperm_of_subset (toList_nodup H) hsub).perm_of_length_le
    (by rw [List.length_map, @Array.length_toList _ st.1, hsz, hAl])
  have hin : ∀ v, v2N v ∈ A → v ∈ st.1 := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := List.mem_map.1 (hperm.symm.subset hv)
    rw [← v2N_inj huv]
    exact Array.mem_toList_iff.1 hu
  have himg : ∀ v ∈ st.1, ∀ g < ts.size, frApply ts[g]! v ∈ st.1 := by
    intro v hv g hg
    have hm := hB.mem v hv
    exact hin _ (hcl v hm.1 hm.2 g hg)
  have hfind : ∀ i < st.1.size, vfind st.1 st.2.2.2 bits st.1[i]! = i + 1 := by
    intro i hi
    have hs := vfind_spec H st.1[i]!
    have hne := hs.2 (get!_mem hi)
    obtain ⟨hlt, heq⟩ := hs.1 hne
    have := H.nodup _ i hlt hi (heq.trans (getElem!_pos st.1 i hi))
    omega
  have hfind' : ∀ v ∈ st.1, vfind st.1 st.2.2.2 bits v ≠ 0 ∧
      vfind st.1 st.2.2.2 bits v ≤ st.1.size ∧ st.1[vfind st.1 st.2.2.2 bits v - 1]! = v := by
    intro v hv
    have hs := vfind_spec H v
    have hne := hs.2 hv
    obtain ⟨hlt, heq⟩ := hs.1 hne
    refine ⟨hne, by omega, ?_⟩
    rw [getElem!_pos st.1 _ hlt, heq]
  have hpos := hB.pos
  unfold vorbOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  have hp : st.2.1.size = cap := by rw [hB.szp, hsz]
  have hl : st.2.2.1.size = cap := by rw [hB.szl, hsz]
  have hc0 : 0 < cap := by omega
  refine ⟨⟨⟨⟨⟨hsz, hp⟩, hl⟩, hc0⟩, V2.beq_iff.2 hB.root⟩, fun q hq => ?_⟩
  have hq' : q < st.1.size := by omega
  unfold vorbAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨(hB.mem _ (get!_mem hq')).1, hfind q hq'⟩, fun g hg => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfind' _ (himg _ (get!_mem hq') g hg)
    exact ⟨⟨h1, h2⟩, V2.beq_iff.2 h3⟩
  · rcases Nat.eq_zero_or_pos q with h0 | h0
    · exact Or.inl h0
    · obtain ⟨h1, h2, h3⟩ := hB.tree q hq' h0
      exact Or.inr ⟨⟨h1, h2⟩, V2.beq_iff.2 h3⟩

def Inner (ts : Array (Array V2)) (w : V2) (cap bits : Nat) (A : List Nat) (q : Nat) (p : V2)
    (g : Nat) (st : Array V2 × Array Nat × Array Nat × ByteArray) : Prop :=
  Base ts w cap bits A st ∧ q < st.1.size ∧ st.1[q]! = p ∧
    (st.1.size = cap ∨ (Closed ts q st.1 ∧ ∀ g' < g, frApply ts[g']! p ∈ st.1))

theorem inner_push (hb : 4 * 2 ^ bits < 2 ^ 32) (hcap : cap < 2 ^ bits)
    (hwf : ∀ v, v.wf = true → ∀ g < ts.size, (frApply ts[g]! v).wf = true)
    (hcl : ∀ v, v.wf = true → v2N v ∈ A → ∀ g < ts.size, v2N (frApply ts[g]! v) ∈ A)
    {q g : Nat} {p : V2} (hg : g < ts.size) {pts : Array V2} {par lab : Array Nat}
    {slots : ByteArray} (hJ : Inner ts w cap bits A q p g (pts, par, lab, slots))
    (hv0 : vfind pts slots bits (frApply ts[g]! p) = 0) (hlt : pts.size < cap) :
    Inner ts w cap bits A q p (g + 1) (pts.push (frApply ts[g]! p), par.push q, lab.push g,
      vinsert pts slots bits (frApply ts[g]! p)) := by
  obtain ⟨⟨hinv, szp, szl, pos, le, root, mem, tree⟩, hq, hp, hc⟩ := hJ
  dsimp only at *
  have hpm : p ∈ pts := hp ▸ get!_mem hq
  have hpw := mem p hpm
  have hy : frApply ts[g]! p ∉ pts := fun hy => (vfind_spec hinv _).2 hy hv0
  have hc' : Closed ts q pts ∧ ∀ g' < g, frApply ts[g']! p ∈ pts := hc.resolve_left (by omega)
  refine ⟨⟨hinv_insert hinv hb (by omega) hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · simp only [Array.size_push, szp]
  · simp only [Array.size_push, szl]
  · simp only [Array.size_push]
    omega
  · simp only [Array.size_push]
    omega
  · rw [get!_push_lt _ _ pos]
    exact root
  · intro v hv
    rcases Array.mem_push.1 hv with hv | rfl
    · exact mem v hv
    · exact ⟨hwf p hpw.1 g hg, hcl p hpw.1 hpw.2 g hg⟩
  · intro i hi h0
    rw [Array.size_push] at hi
    by_cases hil : i < pts.size
    · obtain ⟨t1, t2, t3⟩ := tree i hil h0
      rw [get!_push_lt _ _ (by omega), get!_push_lt _ _ (by omega), get!_push_lt _ _ hil]
      rw [get!_push_lt _ _ (by omega)]
      exact ⟨t1, t2, t3⟩
    · have hi' : i = pts.size := by omega
      subst hi'
      dsimp only
      have e1 : (par.push q)[pts.size]! = q := by rw [← szp]; exact get!_push_eq par q
      have e2 : (lab.push g)[pts.size]! = g := by rw [← szl]; exact get!_push_eq lab g
      rw [e1, e2, get!_push_lt _ _ hq, hp, get!_push_eq]
      exact ⟨hq, hg, rfl⟩
  · simp only [Array.size_push]
    omega
  · rw [get!_push_lt _ _ hq, hp]
  · exact closed_push hc'.1 (Nat.le_of_lt hq) _
  · intro g' hg'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | rfl
    · exact Array.mem_push_of_mem _ (hc'.2 g' hg')
    · exact Array.mem_push_self

theorem inner_keep {q g : Nat} {p : V2} {pts : Array V2} {par lab : Array Nat}
    {slots : ByteArray} (hJ : Inner ts w cap bits A q p g (pts, par, lab, slots))
    (hcond : vfind pts slots bits (frApply ts[g]! p) = 0 → ¬ pts.size < cap) :
    Inner ts w cap bits A q p (g + 1) (pts, par, lab, slots) := by
  obtain ⟨hB, hq, hp, hc⟩ := hJ
  refine ⟨hB, hq, hp, ?_⟩
  dsimp only at *
  by_cases hs : pts.size = cap
  · exact Or.inl hs
  obtain ⟨h1, h2⟩ := hc.resolve_left hs
  refine Or.inr ⟨h1, fun g' hg' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | rfl
  · exact h2 g' hg'
  · have hle := hB.le
    have hne : vfind pts slots bits (frApply ts[g']! p) ≠ 0 :=
      fun h => hcond h (by dsimp only at hle; omega)
    obtain ⟨hlt, heq⟩ := (vfind_spec hB.hinv _).1 hne
    rw [← heq]
    exact Array.getElem_mem hlt

theorem vorbit_ok (hb : 4 * 2 ^ bits < 2 ^ 32) (hcap : cap < 2 ^ bits) (hAn : A.Nodup)
    (hAl : A.length = cap) (hw : w.wf = true) (hwA : v2N w ∈ A)
    (hwf : ∀ v, v.wf = true → ∀ g < ts.size, (frApply ts[g]! v).wf = true)
    (hcl : ∀ v, v.wf = true → v2N v ∈ A → ∀ g < ts.size, v2N (frApply ts[g]! v) ∈ A)
    (hreach : ∀ S : Nat → Prop, S (v2N w) →
      (∀ v, S (v2N v) → ∀ g < ts.size, S (v2N (frApply ts[g]! v))) → ∀ x ∈ A, S x) :
    vorbOK ts w (vorbit ts w cap bits) cap = true := by
  have hc1 : 0 < cap := hAl ▸ List.length_pos_of_mem hwA
  let P : VOrb → Prop := fun O => vorbOK ts w O cap = true
  let I : Nat → Array V2 × Array Nat × Array Nat × ByteArray → Prop := fun q st =>
    Base ts w cap bits A st ∧ q ≤ st.1.size ∧ (st.1.size = cap ∨ Closed ts q st.1)
  have hfin : ∀ st : Array V2 × Array Nat × Array Nat × ByteArray, Base ts w cap bits A st →
      (st.1.size = cap ∨ Closed ts st.1.size st.1) → P ⟨st.1, st.2.1, st.2.2.1, st.2.2.2, bits⟩ :=
    fun st hB hc => final hAl hcl hB (size_eq_cap hAn hAl hreach hB hc)
  change P (vorbit ts w cap bits)
  unfold vorbit
  dsimp only
  refine forIn_range_bind I P _ _ _ _ ?_ ?_ ?_
  · rintro q ⟨pts, par, lab, slots⟩ hq ⟨hB, hle, hc⟩
    dsimp only at hle hc
    dsimp only
    split
    · rename_i hqs
      refine forIn_range_bind (Inner ts w cap bits A q pts[q]!) _ _ _ _ _ ?_ ?_ ?_
      · rintro g ⟨pts', par', lab', slots'⟩ hg hJ
        dsimp only
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          exact inner_push hb hcap hwf hcl hg hJ hcond.1 hcond.2
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at hcond
          exact inner_keep hJ hcond
      · rintro ⟨pts', par', lab', slots'⟩ ⟨hB', hq', hp', hc'⟩
        dsimp only at hq' hp' hc'
        show I (q + 1) (pts', par', lab', slots')
        refine ⟨hB', by dsimp only; omega, ?_⟩
        rcases hc' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · refine Or.inr fun i hi g hg => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact h1 i hi g hg
          · rw [hp']
            exact h2 g hg
      · exact ⟨hB, hqs, rfl, hc.imp id fun h => ⟨h, fun g hg => absurd hg (Nat.not_lt_zero _)⟩⟩
    · rename_i hqs
      have hqe : q = pts.size := by omega
      subst hqe
      exact hfin (pts, par, lab, slots) hB hc
  · rintro ⟨pts, par, lab, slots⟩ ⟨hB, hle, _⟩
    have := hB.le
    dsimp only at hle this
    exact hfin (pts, par, lab, slots) hB (Or.inl (by dsimp only; omega))
  · refine ⟨⟨hinv_insert (hinv_zeros hb) hb (by simp) (by simp), by simp, by simp, by simp,
      by simp; omega, get!_push_eq (#[] : Array V2) w, ?_, ?_⟩, Nat.zero_le _,
      Or.inr fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · intro v hv
      have hv' : v = w := by simpa using hv
      subst hv'
      exact ⟨hw, hwA⟩
    · intro i hi h0
      simp at hi
      omega

end BFS

end CFSG.KC.J4Q.VOrbBFS

end
