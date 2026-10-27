module

public import CFSG.Certificates.Kernel.Spor.SlpMatSound
public import Certificates.Data.Kernel.Spor.SlpInv

public section

namespace CFSG.KC.SlpM

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KS.Mat3

section Pairs

variable {M : Type*} [Monoid M]

@[expose] def InvPairs (L : Array M) : Prop :=
  ∀ k, L.getD (2 * k) 1 * L.getD (2 * k + 1) 1 = 1 ∧ L.getD (2 * k + 1) 1 * L.getD (2 * k) 1 = 1

theorem inv_prod_right {f h : Int → M} : ∀ w : List Int, (∀ z ∈ w, f z * h z = 1) →
    (w.map f).prod * (w.reverse.map h).prod = 1
  | [], _ => by simp
  | z :: w, hw => by
    rw [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]
    calc f z * (w.map f).prod * ((w.reverse.map h).prod * h z)
        = f z * ((w.map f).prod * (w.reverse.map h).prod) * h z := by simp only [mul_assoc]
      _ = 1 := by
        rw [inv_prod_right w (fun z' hz' => hw z' (List.mem_cons_of_mem _ hz')), mul_one,
          hw z List.mem_cons_self]

theorem inv_prod_left {f h : Int → M} : ∀ w : List Int, (∀ z ∈ w, h z * f z = 1) →
    (w.reverse.map h).prod * (w.map f).prod = 1
  | [], _ => by simp
  | z :: w, hw => by
    rw [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]
    calc (w.reverse.map h).prod * h z * (f z * (w.map f).prod)
        = (w.reverse.map h).prod * (h z * f z) * (w.map f).prod := by simp only [mul_assoc]
      _ = 1 := by
        rw [hw z List.mem_cons_self, mul_one,
          inv_prod_left w (fun z' hz' => hw z' (List.mem_cons_of_mem _ hz'))]

theorem semLetter_inv {g : Int → M} (hg1 : g 1 * g (-1) = 1 ∧ g (-1) * g 1 = 1)
    (hg2 : g 2 * g (-2) = 1 ∧ g (-2) * g 2 = 1) {L : Array M} (hL : InvPairs L) {z : Int}
    (hz : z ≠ 0) :
    semLetter g L z * semLetter g L (-z) = 1 ∧ semLetter g L (-z) * semLetter g L z = 1 := by
  unfold semLetter
  rw [Int.natAbs_neg]
  by_cases ha : z.natAbs ≤ 2
  · rw [if_pos ha, if_pos ha]
    have hz4 : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
    rcases hz4 with rfl | rfl | rfl | rfl
    · exact hg1
    · rw [neg_neg]
      exact ⟨hg1.2, hg1.1⟩
    · exact hg2
    · rw [neg_neg]
      exact ⟨hg2.2, hg2.1⟩
  · rw [if_neg ha, if_neg ha]
    by_cases hp : 0 < z
    · rw [if_pos hp, if_neg (by omega : ¬ 0 < -z)]
      exact hL _
    · rw [if_neg hp, if_pos (by omega : 0 < -z)]
      exact ⟨(hL _).2, (hL _).1⟩

theorem invPairs_empty : InvPairs (#[] : Array M) := fun k => by simp

theorem invPairs_step {g : Int → M} (hg1 : g 1 * g (-1) = 1 ∧ g (-1) * g 1 = 1)
    (hg2 : g 2 * g (-2) = 1 ∧ g (-2) * g 2 = 1) {L : Array M} {n : Nat} (hn : L.size = 2 * n)
    (hL : InvPairs L) {w : List Int} (hw : ∀ z ∈ w, z ≠ 0) : InvPairs (semStep g L w) := by
  intro k
  have hs : (semStep g L w).size = 2 * n + 2 := by rw [semStep_size, hn]
  rcases lt_trichotomy k n with hk | rfl | hk
  · have e1 : (semStep g L w).getD (2 * k) 1 = L.getD (2 * k) 1 := by
      simp only [Array.getD_eq_getD_getElem?]
      rw [semStep_getElem? g L w (by omega)]
    have e2 : (semStep g L w).getD (2 * k + 1) 1 = L.getD (2 * k + 1) 1 := by
      simp only [Array.getD_eq_getD_getElem?]
      rw [semStep_getElem? g L w (by omega)]
    rw [e1, e2]
    exact hL k
  · have hS := chk_semStep_getD g L w
    rw [hn] at hS
    rw [hS.1, hS.2]
    have hlet : ∀ z ∈ w, semLetter g L z * semLetter g L (-z) = 1 ∧
        semLetter g L (-z) * semLetter g L z = 1 := fun z hz => semLetter_inv hg1 hg2 hL (hw z hz)
    exact ⟨inv_prod_right (f := semLetter g L) (h := fun z => semLetter g L (-z)) w
        (fun z hz => (hlet z hz).1),
      inv_prod_left (f := semLetter g L) (h := fun z => semLetter g L (-z)) w
        (fun z hz => (hlet z hz).2)⟩
  · have o : ∀ i, 2 * n + 2 ≤ i → (semStep g L w).getD i 1 = 1 := fun i hi => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [o (2 * k) (by omega), o (2 * k + 1) (by omega), mul_one]
    exact ⟨rfl, rfl⟩

theorem invPairs_foldl {g : Int → M} (hg1 : g 1 * g (-1) = 1 ∧ g (-1) * g 1 = 1)
    (hg2 : g 2 * g (-2) = 1 ∧ g (-2) * g 2 = 1) :
    ∀ (ws : List (List Int)) {L : Array M} {n : Nat}, L.size = 2 * n → InvPairs L →
      (∀ w ∈ ws, ∀ z ∈ w, z ≠ 0) → InvPairs (ws.foldl (semStep g) L)
  | [], _, _, _, hL, _ => hL
  | w :: ws, L, n, hn, hL, hw => by
    rw [List.foldl_cons]
    exact invPairs_foldl hg1 hg2 ws (n := n + 1) (by rw [semStep_size, hn]; omega)
      (invPairs_step hg1 hg2 hn hL (hw w List.mem_cons_self))
      (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))

theorem semN_pair {g : Int → M} (hg1 : g 1 * g (-1) = 1 ∧ g (-1) * g 1 = 1)
    (hg2 : g 2 * g (-2) = 1 ∧ g (-2) * g 2 = 1) {W : List (List Nat)}
    (hz : ∀ w ∈ W, ∀ c ∈ w, 0 < c / 2) (j : Nat) :
    semN g W (2 * j) * semN g W (2 * j + 1) = 1 := by
  unfold semN
  rw [chk_semArr_toArray]
  refine (invPairs_foldl hg1 hg2 _ (L := #[]) (n := 0) rfl invPairs_empty ?_ j).1
  intro w hw z hz'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
  unfold decW at hz'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz'
  intro h0
  have h1 := decC_natAbs c
  rw [h0, Int.natAbs_zero] at h1
  have h2 := hz u hu c hc
  omega

theorem gen3_inv {gA gB : M} (hA : gA * gA = 1) (hB : gB * (gB * gB) = 1) :
    (gen3 gA gB 1 * gen3 gA gB (-1) = 1 ∧ gen3 gA gB (-1) * gen3 gA gB 1 = 1) ∧
      (gen3 gA gB 2 * gen3 gA gB (-2) = 1 ∧ gen3 gA gB (-2) * gen3 gA gB 2 = 1) := by
  have e1 : gen3 gA gB 1 = gA := by
    unfold gen3
    rw [if_pos (by decide)]
  have e2 : gen3 gA gB (-1) = gA := by
    unfold gen3
    rw [if_pos (by decide)]
  have e3 : gen3 gA gB 2 = gB := by
    unfold gen3
    rw [if_neg (by decide), if_pos rfl]
  have e4 : gen3 gA gB (-2) = gB ^ 2 := by
    unfold gen3
    rw [if_neg (by decide), if_neg (by decide)]
  rw [e1, e2, e3, e4, pow_two]
  refine ⟨⟨hA, hA⟩, hB, ?_⟩
  rw [mul_assoc]
  exact hB

end Pairs

theorem slpC_pos {W : List (List Nat)} (h : slpC W 0 = true) : ∀ w ∈ W, ∀ c ∈ w, 0 < c / 2 := by
  intro w hw c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
  exact (slpC_spec h i hi c (by rw [getElem!_pos W i hi]; exact hc)).1

theorem nilB_spec {α : Type} {l : List α} (h : nilB l = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l =>
    change false = true at h
    exact absurd h (by decide)

theorem invOut_spec {mul : Nat → Nat → Nat} {ONE : Nat} {VLD : Nat → Bool} {R : Nat → Nat}
    {nR : Nat} {PC PN LY : Nat → Nat} {base k : Nat} {p : Nat × Nat}
    (h : invOut mul ONE VLD R nR PC PN LY base k p = true) :
    p.1 % 2 = 1 ∧ 0 < p.2 - 1 ∧ p.2 - 1 < nR ∧ PN (p.2 - 1) = p.1 - 1 ∧ PC (p.2 - 1) < k ∧
      (LY (PC (p.2 - 1)) = LY k ∨ p.1 - 1 < base) ∧ VLD (R p.2) = true ∧
      mul (R p.2) (R (p.2 - 1)) = ONE := by
  unfold invOut at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, h7, h8⟩ := by simpa only [andB_iff] using h
  have ho : Nat.land p.1 1 = 1 := Nat.eq_of_beq_eq_true h1
  rw [chk_land] at ho
  refine ⟨ho, blt_true h2, blt_true h3, Nat.eq_of_beq_eq_true h4, blt_true h5, ?_, h7,
    Nat.eq_of_beq_eq_true h8⟩
  rcases (orB_iff _ _).1 h6 with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · exact Or.inr (blt_true e)

theorem slp_recordsI {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true)
    {GA GB GB2 : Nat} {gA gB : Matrix (Fin d) (Fin d) (ZMod 3)}
    (hA : Canon3 N GA ∧ mat3 d N GA = gA) (hB : Canon3 N GB ∧ mat3 d N GB = gB)
    (hB2 : Canon3 N GB2 ∧ mat3 d N GB2 = gB * gB) (hAA : gA * gA = 1) (hBB : gB * (gB * gB) = 1)
    {WL : Nat → List (List Nat)} {base : Nat}
    (hW : ∀ l l' n, n < base → semN (gen3 gA gB) (WL l) n = semN (gen3 gA gB) (WL l') n)
    (hz : ∀ l, ∀ w ∈ WL l, ∀ c ∈ w, 0 < c / 2)
    {K nR : Nat} {R : Nat → Nat} {LY PC PN : Nat → Nat} {IN OU : Nat → List (Nat × Nat)}
    {ND : Nat → List Nat} {EQ NE : Nat → List (List Nat × List Nat)}
    (hk : ∀ k < K, chunkOK (mul3s d N LO CI RM) ONE (valid3 N LO) GA GB GB2 (WL (LY k)) R (IN k)
      (ND k) (OU k) (EQ k) (NE k) = true ∨
      invOK (mul3s d N LO CI RM) ONE (valid3 N LO) R nR PC PN LY base k (OU k) (EQ k) (NE k) = true)
    (hp : planOK K nR base LY PC PN IN OU = true) :
    (∀ r < nR, 0 < r → Canon3 N (R r) ∧ mat3 d N (R r) = semN (gen3 gA gB) (WL (LY (PC r))) (PN r)) ∧
      ∀ k < K, (∀ e ∈ EQ k, semE (gen3 gA gB) (WL (LY k)) e.1 = semE (gen3 gA gB) (WL (LY k)) e.2) ∧
        ∀ e ∈ NE k, semE (gen3 gA gB) (WL (LY k)) e.1 ≠ semE (gen3 gA gB) (WL (LY k)) e.2 := by
  obtain ⟨pin, prec⟩ := planOK_spec hp
  obtain ⟨-, -, hLO, -, -, -⟩ := CFSG.KS.Mat3.consts3_facts hc
  have hg := gen3_inv hAA hBB
  have hinp : ∀ k, k < K → (∀ k' < k, k' < K → ∀ p ∈ OU k',
      Canon3 N (R p.2) ∧ mat3 d N (R p.2) = semN (gen3 gA gB) (WL (LY k')) p.1) →
      ∀ p ∈ IN k, mat3 d N (R p.2) = semN (gen3 gA gB) (WL (LY k)) p.1 := by
    intro k hkK ih p hp
    obtain ⟨h0, hr, hn, hlt, hly⟩ := pin k hkK p hp
    obtain ⟨hK, hm⟩ := prec p.2 hr h0
    have := (ih (PC p.2) hlt hK (PN p.2, p.2) hm).2
    rw [this, hn]
    rcases hly with e | e
    · rw [e]
    · exact hW _ _ _ e
  have hout : ∀ k, k < K → ∀ p ∈ OU k,
      Canon3 N (R p.2) ∧ mat3 d N (R p.2) = semN (gen3 gA gB) (WL (LY k)) p.1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkK
      rcases hk k hkK with hc1 | hi
      · exact (chunkOK_spec hc hA hB hB2 hc1 (hinp k hkK fun k' hk' hk'K => ih k' hk' hk'K)).1
      · intro p hp
        obtain ⟨h1, -⟩ := (andB_iff _ _).1 hi
        obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := invOut_spec (allL_spec h1 p hp)
        obtain ⟨hK, hm⟩ := prec (p.2 - 1) o3 o2
        have hr := ih (PC (p.2 - 1)) o5 hK (PN (p.2 - 1), p.2 - 1) hm
        dsimp only at hr
        rw [o4] at hr
        have hY : mat3 d N (R (p.2 - 1)) = semN (gen3 gA gB) (WL (LY k)) (p.1 - 1) := by
          rw [hr.2]
          rcases o6 with e | e
          · rw [e]
          · exact hW _ _ _ e
        have hX : Canon3 N (R p.2) := (valid3_iff hLO).1 o7
        obtain ⟨-, hm2⟩ := mul3s_sound hc hX hr.1
        rw [o8, (one3_sound hc).2, hY] at hm2
        have hpair := semN_pair hg.1 hg.2 (hz (LY k)) ((p.1 - 1) / 2)
        have e1 : 2 * ((p.1 - 1) / 2) = p.1 - 1 := by omega
        have e2 : 2 * ((p.1 - 1) / 2) + 1 = p.1 := by omega
        rw [e2, e1] at hpair
        refine ⟨hX, ?_⟩
        calc mat3 d N (R p.2)
            = mat3 d N (R p.2) * (semN (gen3 gA gB) (WL (LY k)) (p.1 - 1) *
                semN (gen3 gA gB) (WL (LY k)) p.1) := by rw [hpair, mul_one]
          _ = semN (gen3 gA gB) (WL (LY k)) p.1 := by rw [← mul_assoc, ← hm2, one_mul]
  refine ⟨fun r hr hr0 => ?_, fun k hkK => ?_⟩
  · obtain ⟨hK, hm⟩ := prec r hr hr0
    exact hout (PC r) hK (PN r, r) hm
  · rcases hk k hkK with hc1 | hi
    · exact (chunkOK_spec hc hA hB hB2 hc1 (hinp k hkK fun k' _ hk'K => hout k' hk'K)).2
    · obtain ⟨-, h2⟩ := (andB_iff _ _).1 hi
      obtain ⟨h3, h4⟩ := (andB_iff _ _).1 h2
      rw [nilB_spec h3, nilB_spec h4]
      exact ⟨fun e he => by simp at he, fun e he => by simp at he⟩

end CFSG.KC.SlpM

end
