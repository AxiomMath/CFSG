module

public import CFSG.Certificates.Kernel.J4Hub.Defs
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LocalQTSecLemmas
import CFSG.Certificates.Kernel.J4.ChainSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

@[expose] noncomputable def pcMat (p d w S : Nat) (RB : Nat → Nat) (PR k : Nat) :
    Matrix (Fin d) (Fin d) (ZMod p) :=
  ordMat p d w S (RB (at16 PR k))

@[expose] def pcSub (p d w S : Nat) (RB : Nat → Nat) (PR i n : Nat) :
    Subgroup (GL (Fin d) (ZMod p)) :=
  Subgroup.closure {g | ∃ k, i ≤ k ∧ k < n ∧
    ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k}

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem andT' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem rec_and' {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := andT' h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_and' m h1 g hg
    · exact h2

theorem regsIn_spec {PR n r : Nat} (h : regsIn PR n r = true) :
    ∀ k < n, 0 < at16 PR k ∧ at16 PR k < r := by
  intro k hk
  obtain ⟨h1, h2⟩ := andT' (rec_and' (f := fun k => regBelow (at16 PR k) r) n h k hk)
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩

theorem pc_reg (hnb : nb = d * S) {G : Subgroup (GL (Fin d) (ZMod p))}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {RB : Nat → Nat} {nreg PR n : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) (hpr : regsIn PR n nreg = true) {k : Nat} (hk : k < n) :
    Canon p d w (RB (at16 PR k)) ∧ ∃ g ∈ G,
      ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k := by
  subst hnb
  obtain ⟨h1, h2⟩ := regsIn_spec hpr k hk
  obtain ⟨hv, hg⟩ := hR _ h1 h2
  exact ⟨validM_canon hc hv, hg⟩

theorem mem_pcSub {RB : Nat → Nat} {PR i n k : Nat} (hik : i ≤ k) (hk : k < n)
    {g : GL (Fin d) (ZMod p)}
    (hg : ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k) :
    g ∈ pcSub p d w S RB PR i n :=
  Subgroup.subset_closure ⟨k, hik, hk, hg⟩

theorem pcSub_anti {RB : Nat → Nat} {PR i j n : Nat} (hij : i ≤ j) :
    pcSub p d w S RB PR j n ≤ pcSub p d w S RB PR i n :=
  Subgroup.closure_mono fun _ ⟨k, h1, h2, h3⟩ => ⟨k, Nat.le_trans hij h1, h2, h3⟩

theorem pcSub_le (hnb : nb = d * S) {G : Subgroup (GL (Fin d) (ZMod p))}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {RB : Nat → Nat} {nreg PR n : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) (hpr : regsIn PR n nreg = true) (i : Nat) :
    pcSub p d w S RB PR i n ≤ G := by
  refine (Subgroup.closure_le G).2 ?_
  rintro g ⟨k, -, hk, hg⟩
  obtain ⟨-, g', hg', e⟩ := pc_reg hnb hc hR hpr hk
  have : g = g' := Units.ext (hg.trans e.symm)
  rw [this]
  exact hg'

theorem finite_GL (hp : 2 ≤ p) : Finite (GL (Fin d) (ZMod p)) := by
  have : NeZero p := ⟨by omega⟩
  exact Finite.of_injective (fun u : GL (Fin d) (ZMod p) => (u : Matrix (Fin d) (Fin d) (ZMod p)))
    fun a b h => Units.ext h

open CFSG.KC.LQT.SecS CFSG.KS.PackFld in
theorem validV_canon (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {v : Nat}
    (hv : validM p S LV HV v = true) : VCanon p d w v := by
  obtain ⟨hp, hS, hw, -, hT, -⟩ := consts_facts hc
  obtain ⟨hLV, hHV⟩ := consts_v hc hw
  subst hS hLV hHV
  unfold validM at hv
  obtain ⟨h1, hv⟩ := andT' hv
  obtain ⟨h2, h3⟩ := andT' hv
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hlt : v < 2 ^ (w * d) := by
    have h1' : v >>> (d * w) = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm d w] at h1'
    rcases Nat.div_eq_zero_iff.1 h1' with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨a, rfl, ha⟩ : ∃ a, v = pk w d a ∧ ∀ t < d, a t < 2 ^ w :=
    ⟨lane w v, pk_lane hw hlt, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  have hHb : ∀ t < d, (2 : Nat) ^ (w - 1) < 2 ^ w := fun _ _ => by
    have := Nat.two_pow_pos (w - 1)
    omega
  have htop : ∀ t < d, a t < 2 ^ (w - 1) := by
    intro t ht
    have h2' : pk w d a &&& pk w d (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h2
    have hF := fld_and (fld_pk ha) (fld_pk hHb)
    rw [h2'] at hF
    have hb := hF t (w - 1) (by omega)
    rw [Nat.zero_testBit] at hb
    simp only [ht, ↓reduceIte] at hb
    have ha2 : a t < 2 * 2 ^ (w - 1) := by have := ha t ht; omega
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, testBit_top ha2] at hb
    simpa using hb
  have h3' : ((pk w d a ||| pk w d (fun _ => 2 ^ (w - 1))) - p * pk w d (fun _ => 1)) &&&
      pk w d (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h3
  rw [top_H hw htop hp2] at h3'
  unfold pk at h3'
  refine ⟨pk_lt ha, fun t ht => ?_⟩
  rw [lane_pk ha ht]
  by_contra hn
  have hz := Finset.sum_eq_zero_iff.1 h3' t (Finset.mem_range.2 ht)
  have hn' : p ≤ a t := Nat.le_of_not_lt hn
  simp only [hn', ↓reduceIte] at hz
  exact absurd hz (Nat.mul_ne_zero (Nat.two_pow_pos _).ne' (Nat.two_pow_pos _).ne')

theorem brec_zero {Q : Nat → Prop} (h0 : Q 0) {Y : Nat} {c : Bool} (h : c = true → Q Y) :
    Q (Bool.rec (motive := fun _ => Nat) (nat_lit 0) Y c) := by
  cases c
  · exact h0
  · exact h rfl

noncomputable def treeChunk (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb: Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => (fun k par g => CFSG.KC.Loop.strictN
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
          (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt par k) (andB (Nat.ble fr g) (andB (Nat.blt g tb)
            (Nat.beq (PT k) (vm (PT par) (RB (at16 PR g)))))))))
        (ih2 (Nat.shiftRight J (nat_lit 24))))
      (Nat.sub S (nat_lit 1)) (bitsN J (nat_lit 0) (nat_lit 16)) (bitsN J (nat_lit 16) (nat_lit 8)))

theorem runTree_cons (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb C : Nat)
    (Cs : List Nat) (s : Nat) :
    runTree RB PT vm PR fr tb (C :: Cs) s =
      runTree RB PT vm PR fr tb Cs (treeChunk RB PT vm PR fr tb (Nat.land C (nat_lit 65535))
        (Nat.shiftRight C (nat_lit 16)) s) :=
  strictN_eq' _ _

def TreeGood (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb k : Nat) : Prop :=
  ∃ par g, par < k ∧ fr ≤ g ∧ g < tb∧ PT k = vm (PT par) (RB (at16 PR g))

def TreeInv (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb s : Nat) : Prop :=
  s = 0 ∨ (2 ≤ s ∧ ∀ k, 1 ≤ k → k + 1 < s → TreeGood RB PT vm PR fr tb k)

theorem treeChunk_inv (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb: Nat) :
    ∀ m J s, TreeInv RB PT vm PR fr tb s →
      TreeInv RB PT vm PR fr tb (treeChunk RB PT vm PR fr tb m J s)
  | 0, _, _, h => h
  | m + 1, J, s, h => by
    have e : treeChunk RB PT vm PR fr tb (m + 1) J s = treeChunk RB PT vm PR fr tb m
        (Nat.shiftRight J (nat_lit 24)) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ s)
          (andB (Nat.blt (nat_lit 0) s) (andB (Nat.blt (bitsN J 0 16) (s - 1))
            (andB (Nat.ble fr (bitsN J 16 8)) (andB (Nat.blt (bitsN J 16 8) tb)
              (Nat.beq (PT (s - 1)) (vm (PT (bitsN J 0 16)) (RB (at16 PR (bitsN J 16 8)))))))))) :=
      strictN_eq' _ _
    rw [e]
    apply treeChunk_inv
    refine brec_zero (Q := TreeInv RB PT vm PR fr tb) (Or.inl rfl) fun hc => ?_
    · obtain ⟨h0, hc⟩ := andT' hc
      obtain ⟨h1, hc⟩ := andT' hc
      obtain ⟨h2, hc⟩ := andT' hc
      obtain ⟨h3, h4⟩ := andT' hc
      have hs0 : 0 < s := Nat.blt_eq.mp h0
      rcases h with h | ⟨hs2, hk⟩
      · omega
      refine Or.inr ⟨by omega, fun k hk1 hks => ?_⟩
      rcases Nat.lt_or_ge (k + 1) s with hlt | hge
      · exact hk k hk1 hlt
      · have hk' : k = s - 1 := by
          change k + 1 < s + 1 at hks
          omega
        subst hk'
        exact ⟨_, _, Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2, Nat.blt_eq.mp h3,
          Nat.eq_of_beq_eq_true h4⟩

theorem runTree_inv (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr tb: Nat) :
    ∀ (Cs : List Nat) s, TreeInv RB PT vm PR fr tb s →
      TreeInv RB PT vm PR fr tb (runTree RB PT vm PR fr tb Cs s)
  | [], _, h => h
  | C :: Cs, s, h => by
    rw [runTree_cons]
    exact runTree_inv RB PT vm PR fr tb Cs _ (treeChunk_inv RB PT vm PR fr tb _ _ _ h)

theorem tree_spec {RB PT : Nat → Nat} {vm : Nat → Nat → Nat} {PR fr tb N : Nat} {Cs : List Nat}
    (h : Nat.beq (runTree RB PT vm PR fr tb Cs 2) (Nat.succ N) = true) :
    ∀ k, 1 ≤ k → k < N → TreeGood RB PT vm PR fr tb k := by
  have hi := runTree_inv RB PT vm PR fr tb Cs 2 (Or.inr ⟨le_rfl, fun k h1 h2 => by omega⟩)
  rw [Nat.eq_of_beq_eq_true h] at hi
  rcases hi with hi | ⟨-, hi⟩
  · exact absurd hi (Nat.succ_ne_zero N)
  · intro k h1 h2
    exact hi k h1 (by omega)

noncomputable def sortChunk (PT : Nat → Nat) (n : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => CFSG.KC.Loop.strictN (sortStep PT n S (bitsN J (nat_lit 0) (nat_lit 16)))
      (ih2 (Nat.shiftRight J (nat_lit 16))))

theorem runSorted_cons (PT : Nat → Nat) (n C : Nat) (Cs : List Nat) (s : Nat) :
    runSorted PT n (C :: Cs) s =
      runSorted PT n Cs (sortChunk PT n (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eq' _ _

def SortInv (PT : Nat → Nat) (n s : Nat) : Prop :=
  s = 0 ∨ ∃ c bm pv : Nat, ∃ V : Finset Nat, s = (c + 1) + 2 ^ 16 * bm + 2 ^ (16 + n) * pv ∧
    bm < 2 ^ n ∧ V.card = c ∧ (∀ x, x ∈ V ↔ x < n ∧ bm.testBit x = true) ∧
    Set.InjOn PT V ∧ ∀ x ∈ V, PT x < pv

theorem decomp_fields {c bm pv n : Nat} (hc : c + 1 < 2 ^ 16) (hbm : bm < 2 ^ n) :
    Nat.land ((c + 1) + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) (nat_lit 65535) = c + 1 ∧
    Nat.land (Nat.shiftRight ((c + 1) + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) (nat_lit 16))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) = bm ∧
    Nat.shiftRight ((c + 1) + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) (Nat.add (nat_lit 16) n) = pv := by
  have e1 : (65535 : Nat) = 2 ^ 16 - 1 := by norm_num
  have hpos := Nat.two_pow_pos n
  have e16 : 2 ^ (16 + n) = 2 ^ 16 * 2 ^ n := Nat.pow_add _ _ _
  refine ⟨?_, ?_, ?_⟩
  · change (c + 1 + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) &&& 65535 = c + 1
    rw [e1, Nat.and_two_pow_sub_one_eq_mod, e16, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · change ((c + 1 + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) >>> 16) &&& ((1 <<< n) - 1) = bm
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      e16, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 16),
      Nat.div_eq_of_lt hc, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbm]
  · change (c + 1 + 2 ^ 16 * bm + 2 ^ (16 + n) * pv) >>> (16 + n) = pv
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    have hlt : c + 1 + 2 ^ 16 * bm < 2 ^ (16 + n) := by
      rw [e16]
      have : 2 ^ 16 * bm + 2 ^ 16 ≤ 2 ^ 16 * 2 ^ n := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hbm
      omega
    rw [Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem sortChunk_inv (PT : Nat → Nat) (n : Nat) (hn : n + 1 < 2 ^ 16) :
    ∀ m J s, SortInv PT n s → SortInv PT n (sortChunk PT n m J s)
  | 0, _, _, h => h
  | m + 1, J, s, h => by
    have e : sortChunk PT n (m + 1) J s =
        sortChunk PT n m (Nat.shiftRight J (nat_lit 16)) (sortStep PT n s (bitsN J 0 16)) :=
      strictN_eq' _ _
    rw [e]
    apply sortChunk_inv PT n hn
    generalize bitsN J 0 16 = x
    rcases h with rfl | ⟨c, bm, pv, V, rfl, hbm, hV, hmem, hinj, hlt⟩
    · exact Or.inl rfl
    have hcn : c ≤ n := by
      have : V ⊆ Finset.range n := fun y hy => Finset.mem_range.2 ((hmem y).1 hy).1
      have := Finset.card_le_card this
      simp only [Finset.card_range] at this
      omega
    obtain ⟨f1, f2, f3⟩ := decomp_fields (pv := pv) (by omega : c + 1 < 2 ^ 16) hbm
    unfold sortStep
    dsimp only
    rw [f2]
    refine brec_zero (Q := SortInv PT n) (Or.inl rfl) fun hc => ?_
    obtain ⟨-, hc⟩ := andT' hc
    obtain ⟨hx, hc⟩ := andT' hc
    obtain ⟨hnv, hpv⟩ := andT' hc
    rw [f3] at hpv
    have hx' : x < n := Nat.blt_eq.mp hx
    have hpv' : pv ≤ PT x := Nat.le_of_ble_eq_true hpv
    have hnv' : bm.testBit x = false := by
      have h0 : Nat.land bm (Nat.shiftLeft (nat_lit 1) x) = 0 := Nat.eq_of_beq_eq_true hnv
      have h1 := congrArg (fun y => Nat.testBit y x) h0
      simp only at h1
      change (bm &&& (1 <<< x)).testBit x = (0 : Nat).testBit x at h1
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_and, Nat.testBit_two_pow_self,
        Nat.zero_testBit, Bool.and_true] at h1
      exact h1
    have hxV : x ∉ V := fun hxV => by
      have := ((hmem x).1 hxV).2
      rw [hnv'] at this
      exact absurd this (by decide)
    refine Or.inr ⟨c + 1, bm ||| 2 ^ x, PT x + 1, insert x V, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [f1]
      change Nat.succ (c + 1) + ((bm ||| 1 <<< x) <<< 16 + Nat.succ (PT x) <<< (16 + n)) = _
      simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.succ_eq_add_one]
      ring
    · exact Nat.or_lt_two_pow hbm (Nat.pow_lt_pow_right (by norm_num) hx')
    · rw [Finset.card_insert_of_notMem hxV, hV]
    · intro y
      rw [Finset.mem_insert, hmem, Nat.testBit_or, Nat.testBit_two_pow]
      constructor
      · rintro (rfl | ⟨hy, hb⟩)
        · exact ⟨hx', by simp⟩
        · exact ⟨hy, by simp [hb]⟩
      · rintro ⟨hy, hb⟩
        by_cases hxy : y = x
        · exact Or.inl hxy
        · right
          refine ⟨hy, ?_⟩
          have hxy' : ¬ x = y := fun e => hxy e.symm
          simpa [hxy'] using hb
    · rw [Finset.coe_insert]
      refine (Set.injOn_insert (fun h => hxV h)).2 ⟨hinj, fun hx2 => ?_⟩
      obtain ⟨y, hy, e⟩ := hx2
      have := hlt y hy
      omega
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · omega
      · have := hlt y hy
        omega

theorem runSorted_inv (PT : Nat → Nat) (n : Nat) (hn : n + 1 < 2 ^ 16) :
    ∀ (Cs : List Nat) s, SortInv PT n s → SortInv PT n (runSorted PT n Cs s)
  | [], _, h => h
  | C :: Cs, s, h => by
    rw [runSorted_cons]
    exact runSorted_inv PT n hn Cs _ (sortChunk_inv PT n hn _ _ _ h)

theorem sorted_spec {PT : Nat → Nat} {n SS : Nat} {Cs : List Nat}
    (h : Nat.beq (runSorted PT n Cs 1) SS = true) (hs : sortedAll n SS = true) :
    ∀ i < n, ∀ j < n, PT i = PT j → i = j := by
  obtain ⟨h0, h1⟩ := andT' hs
  have hf : Nat.land SS (nat_lit 65535) = n + 1 := Nat.eq_of_beq_eq_true h1
  have hn : n + 1 < 2 ^ 16 := by
    rw [← hf]
    change SS &&& 65535 < 2 ^ 16
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hi := runSorted_inv PT n hn Cs 1
    (Or.inr ⟨0, 0, 0, ∅, by simp, Nat.two_pow_pos n, rfl, by simp, by simp, by simp⟩)
  rw [Nat.eq_of_beq_eq_true h] at hi
  rcases hi with hi | ⟨c, bm, pv, V, rfl, hbm, hV, hmem, hinj, -⟩
  · rw [hi] at h0
    exact absurd h0 (by decide)
  have hcn : c ≤ n := by
    have : V ⊆ Finset.range n := fun y hy => Finset.mem_range.2 ((hmem y).1 hy).1
    have := Finset.card_le_card this
    simp only [Finset.card_range] at this
    omega
  obtain ⟨f1, -, -⟩ := decomp_fields (pv := pv) (by omega : c + 1 < 2 ^ 16) hbm
  rw [f1] at hf
  have hc : c = n := by omega
  have hV' : V = Finset.range n := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => Finset.mem_range.2 ((hmem y).1 hy).1) ?_
    rw [Finset.card_range, hV, hc]
  intro i hi j hj e
  exact hinj (by rw [hV']; simpa using hi) (by rw [hV']; simpa using hj) e

theorem baseFixed_spec {RB : Nat → Nat} {vm : Nat → Nat → Nat} {vldV : Nat → Bool}
    {PR v tb n : Nat} (h : baseFixed RB vm vldV PR v tb n = true) :
    vldV v = true ∧ ∀ k < n, tb≤ k → vm v (RB (at16 PR k)) = v := by
  obtain ⟨h1, h2⟩ := andT' h
  refine ⟨h1, fun k hk htk => ?_⟩
  have := rec_and' (f := fun k => Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (vm v (RB (at16 PR k))) v) (Nat.ble tb k)) n h2 k hk
  rw [Nat.ble_eq_true_of_le htk] at this
  exact Nat.eq_of_beq_eq_true this

@[expose] noncomputable def blkAcc (BL : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun b acc => (fun fr tb=>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ tb)
        (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.beq fr (Nat.sub acc (nat_lit 1))) (Nat.blt fr tb))))
    (bitsN BL (Nat.mul (nat_lit 16) b) (nat_lit 8)) (bitsN BL (Nat.add (Nat.mul (nat_lit 16) b) (nat_lit 8)) (nat_lit 8)))

theorem blkAcc_succ {BL b : Nat} (h : 0 < blkAcc BL (b + 1)) :
    0 < blkAcc BL b ∧ blkFr BL b = blkAcc BL b - 1 ∧ blkFr BL b < blkTo BL b ∧
      blkAcc BL (b + 1) = blkTo BL b + 1 := by
  have e : blkAcc BL (b + 1) = Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ (blkTo BL b))
      (andB (Nat.blt (nat_lit 0) (blkAcc BL b)) (andB (Nat.beq (blkFr BL b) (Nat.sub (blkAcc BL b)
        (nat_lit 1))) (Nat.blt (blkFr BL b) (blkTo BL b)))) := rfl
  rw [e] at h ⊢
  generalize hc : andB (Nat.blt (nat_lit 0) (blkAcc BL b)) (andB (Nat.beq (blkFr BL b)
    (Nat.sub (blkAcc BL b) (nat_lit 1))) (Nat.blt (blkFr BL b) (blkTo BL b))) = c at h ⊢
  cases c
  · exact absurd h (Nat.lt_irrefl 0)
  · obtain ⟨h1, h2⟩ := andT' hc
    obtain ⟨h2, h3⟩ := andT' h2
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h3, rfl⟩

open CFSG.KC.LQT.SecS in
theorem block_le (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n PR fr tb: Nat} (hpr : regsIn PR n nreg = true)
    (hft : fr ≤ tb) {PT : Nat → Nat} {TC SC : List Nat} {SS : Nat}
    (hb : baseFixed RB (vecR p w S d T LV HV RM) (validM p S LV HV) PR (PT 0) tb n = true)
    (ht : Nat.beq (runTree RB PT (vecR p w S d T LV HV RM) PR fr n TC 2)
      (Nat.succ (q ^ (tb - fr))) = true)
    (hs : Nat.beq (runSorted PT (q ^ (tb - fr)) SC 1) SS = true)
    (hsa : sortedAll (q ^ (tb - fr)) SS = true) :
    q ^ (tb - fr) * Nat.card (pcSub p d w S RB PR tb n) ≤
      Nat.card (pcSub p d w S RB PR fr n) := by
  obtain ⟨hp, -, hw, -⟩ := consts_facts hc
  have := finite_GL (d := d) hp
  have hsort := sorted_spec hs hsa
  have htree := tree_spec ht
  obtain ⟨hv0, hfix⟩ := baseFixed_spec hb
  have c0 := validV_canon hc hv0
  have orb : ∀ k, k < q ^ (tb - fr) → VCanon p d w (PT k) ∧
      ∃ x ∈ pcSub p d w S RB PR fr n, toVec p d w (PT k) =
        toVec p d w (PT 0) ᵥ* ((x : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨c0, 1, one_mem _, by simp⟩
      obtain ⟨par, g, hpar, hfg, hgn, e⟩ := htree k hk0 hk
      obtain ⟨cp, x, hx, ex⟩ := ih par hpar (by omega)
      obtain ⟨cg, u, -, eu⟩ := pc_reg hnb hc hR hpr hgn
      obtain ⟨c1, e1⟩ := vecR_sound hc cp cg
      rw [← e] at c1 e1
      refine ⟨c1, x * u, mul_mem hx (mem_pcSub hfg hgn eu), ?_⟩
      rw [e1, ex, Units.val_mul, eu, ← Matrix.vecMul_vecMul]
      rfl
  choose! hcan x hxm hxv using orb
  let A : CFSG.Certificates.J4Chain.RightAct (GL (Fin d) (ZMod p)) (Fin d → ZMod p) :=
    ⟨fun v g => v ᵥ* ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)),
      fun v => by simp, fun v x y => by simp [Matrix.vecMul_vecMul]⟩
  have key := CFSG.Certificates.J4Chain.card_mul_le_of_orbit A (pcSub p d w S RB PR fr n)
    (toVec p d w (PT 0)) (q ^ (tb - fr)) x hxm fun k hk j hj e =>
      hsort k hk j hj (vec_inj hw (hcan k hk) (hcan j hj) (by rw [hxv k hk, hxv j hj]; exact e))
  have hle : pcSub p d w S RB PR tb n ≤
      A.fixSub {toVec p d w (PT 0)} ⊓ pcSub p d w S RB PR fr n := by
    refine le_inf ?_ (pcSub_anti hft)
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, htk, hk, hg⟩
    refine A.mem_fixSub.2 fun a ha => ?_
    rw [Set.mem_singleton_iff.1 ha]
    obtain ⟨cg, -⟩ := pc_reg hnb hc hR hpr hk
    have e1 := (vecR_sound hc c0 cg).2
    rw [hfix k hk htk] at e1
    change toVec p d w (PT 0) ᵥ* ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = _
    rw [hg]
    exact e1.symm
  calc q ^ (tb - fr) * Nat.card (pcSub p d w S RB PR tb n)
      ≤ q ^ (tb - fr) * Nat.card (A.fixSub {toVec p d w (PT 0)} ⊓ pcSub p d w S RB PR fr n :
          Subgroup (GL (Fin d) (ZMod p))) := Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
    _ ≤ _ := key

theorem blocks_le (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n PR nbl BL : Nat} (hpr : regsIn PR n nreg = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n q nbl BL) :
    q ^ n ≤ Nat.card (pcSub p d w S RB PR 0 n) := by
  obtain ⟨hp, -⟩ := consts_facts hc
  have := finite_GL (d := d) hp
  obtain ⟨hok, hblk⟩ := hbl
  have hfin : 0 < blkAcc BL nbl ∧ blkAcc BL nbl - 1 = n := by
    obtain ⟨h1, h2⟩ := andT' hok
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
  have step : ∀ b ≤ nbl, 0 < blkAcc BL b → q ^ (blkAcc BL b - 1) *
      Nat.card (pcSub p d w S RB PR (blkAcc BL b - 1) n) ≤ Nat.card (pcSub p d w S RB PR 0 n) := by
    intro b
    induction b with
    | zero =>
      intro _ _
      change q ^ (1 - 1) * Nat.card (pcSub p d w S RB PR (1 - 1) n) ≤ _
      simp
    | succ b ih =>
      intro hb h
      obtain ⟨h0, hfr, hlt, hacc⟩ := blkAcc_succ h
      have ih' := ih (by omega) h0
      obtain ⟨PT, TC, SC, SS, h1, h2, h3, h4⟩ := hblk b (by omega)
      have hblock := block_le hc hnb hR hpr (Nat.le_of_lt hlt) h1 h2 h3 h4
      rw [hacc, Nat.add_sub_cancel]
      rw [← hfr] at ih'
      calc q ^ blkTo BL b * Nat.card (pcSub p d w S RB PR (blkTo BL b) n)
          = q ^ blkFr BL b * (q ^ (blkTo BL b - blkFr BL b) *
              Nat.card (pcSub p d w S RB PR (blkTo BL b) n)) := by
            rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hlt.le]
        _ ≤ q ^ blkFr BL b * Nat.card (pcSub p d w S RB PR (blkFr BL b) n) :=
            Nat.mul_le_mul_left _ hblock
        _ ≤ _ := ih'
  have h := step nbl le_rfl hfin.1
  rw [hfin.2] at h
  have h1 : 0 < Nat.card (pcSub p d w S RB PR n n) := Nat.card_pos
  calc q ^ n = q ^ n * 1 := (Nat.mul_one _).symm
    _ ≤ q ^ n * Nat.card (pcSub p d w S RB PR n n) := Nat.mul_le_mul_left _ h1
    _ ≤ _ := h

end CFSG.KS.J4Hub

end
