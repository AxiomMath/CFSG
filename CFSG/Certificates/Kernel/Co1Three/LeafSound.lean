module

public import Certificates.Data.Kernel.Co1Three.Leaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Leaf
public import CFSG.Certificates.Kernel.Co1F2Sound
import CFSG.Certificates.Kernel.Co1LeafPSound
import CFSG.Certificates.Kernel.Co1BWordSound
import CFSG.Certificates.Kernel.Co1BInvSound
import all CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Leaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit

public section

namespace CFSG.KC.Co1Leaf

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
open CFSG.KC.Co1BBound CFSG.KC.Co1F2
open CFSG.Sporadic.Co1Schreier.Native (Rows)

@[expose] noncomputable def selV (Bv : List Vec24) (c : ℕ) : Vec24 :=
  ∑ k ∈ Finset.range Bv.length, if c.testBit k = true then Bv.getD k 0 else 0

structure LeafFacts (gs : List Rows) (X : ℕ → Prop) (T : List ℕ) : Prop where
  comm : GensComm gs
  cube : ∀ g ∈ gs, rowsMatrix 24 g ^ 3 = 1
  tests : ∀ x ∈ T, X x
  core : ∃ P : M24, IsSumF gs P ∧ P * P = P ∧
    (∃ w : Vec24, P *ᵥ w = 0 ∧ ∃ S : Fin 24 → M24, (∀ i, IsSumF gs (S i)) ∧
      ∀ i, (Pi.single i 1 : Vec24) + P *ᵥ Pi.single i 1 = S i *ᵥ w) ∧
    ∃ Bv : List Vec24, (∀ b ∈ Bv, P *ᵥ b = b) ∧ (∀ v, ∃ c, selV Bv c = P *ᵥ v) ∧
      ∀ N : M24, (∀ b ∈ Bv, ∃ c, selV Bv c = N *ᵥ b) →
        (∀ x ∈ T, ∃ y, X y ∧
          toVecD 24 y = toVecD 24 x + P *ᵥ toVecD 24 x + N *ᵥ (P *ᵥ toVecD 24 x)) →
        ∀ b ∈ Bv, (N ^ 3) *ᵥ b = b

section Helpers

open CFSG.KC.Co1LeafP CFSG.KC.M1F2 CFSG.KC.Co1B Timmesfeld.Co1Leaf
open CFSG.KLie.CT (andB allN pw2 fget)
open CFSG.Sporadic.Co1Schreier.Native (mul pow one)

noncomputable abbrev MatK (M : ℕ) : M24 := rowsMatrix 24 (unpackR 24 M)

theorem lk_matK_mul (A B : ℕ) : MatK (mulWK A B) = MatK A * MatK B := by
  rw [MatK, ← mulWK_unpack, rowsMatrix_mulRows]

theorem lk_matK_one : MatK oneK = 1 := by
  change rowsMatrix 24 (unpackR 24 (idF 24)) = 1
  rw [CFSG.KC.F2W.unpackR_idF]
  exact rowsMatrix_idRows 24

theorem lk_matK_tr (g : ℕ) : MatK (trK 24 g) = (MatK g)ᵀ := by
  rw [MatK, MatK, ← CFSG.KC.F2W.transposeRows_unpackR, rowsMatrix_transposeRows]

theorem lk_vmF (M x : ℕ) : toVecD 24 (vmF 24 M x) = (MatK M)ᵀ *ᵥ toVecD 24 x := by
  rw [Matrix.mulVec_transpose, ← CFSG.KC.F2W.vecMulN_unpackR, toVecD_vecMulN]

theorem lk_ext {A B : M24} (h : ∀ x : ℕ, A *ᵥ toVecD 24 x = B *ᵥ toVecD 24 x) : A = B := by
  ext i j
  have := congrFun (h (1 <<< j.val)) i
  rw [toVecD_shiftLeft, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  simpa using this

theorem lk_selV_nil (c : ℕ) : selV [] c = 0 := by simp [selV]

theorem lk_selV_cons (v : Vec24) (Bv : List Vec24) (c : ℕ) :
    selV (v :: Bv) c = (if c.testBit 0 = true then v else 0) + selV Bv (c >>> 1) := by
  unfold selV
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_shiftRight, List.getD_cons_succ, Nat.add_comm 1 k]

theorem lk_selV_zero (Bv : List Vec24) : selV Bv 0 = 0 := by simp [selV]

theorem lk_selV_xor (Bv : List Vec24) (a b : ℕ) : selV Bv (a ^^^ b) = selV Bv a + selV Bv b := by
  simp only [selV, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> simp [vec_add_self]

theorem lk_selV_mod (Bv : List Vec24) (c : ℕ) : selV Bv (c % 2 ^ Bv.length) = selV Bv c := by
  unfold selV
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (Finset.mem_range.1 hk), Bool.true_and]

theorem lk_selV_pow (Bv : List Vec24) {k : ℕ} (hk : k < Bv.length) :
    selV Bv (2 ^ k) = Bv.getD k 0 := by
  unfold selV
  rw [Finset.sum_eq_single k]
  · rw [Nat.testBit_two_pow_self, if_pos rfl]
  · intro j _ hj
    simp [Nat.testBit_two_pow_of_ne (Ne.symm hj)]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

theorem lk_selK_hom (φ : ℕ → Vec24) (h0 : φ 0 = 0) (hx : ∀ a b, φ (a ^^^ b) = φ a + φ b) :
    ∀ (L : List ℕ) (m : ℕ), φ (selK L m) = selV (L.map φ) m
  | [], m => by rw [lp_selK_nil, h0, List.map_nil, lk_selV_nil]
  | x :: L, m => by
    rw [List.map_cons, lk_selV_cons, ← lk_selK_hom φ h0 hx L]
    cases hm : m.testBit 0
    · rw [lp_selK_f hm]
      simp
    · rw [lp_selK_t hm, hx]
      simp

theorem lk_toVecD_selK (L : List ℕ) (m : ℕ) : toVecD 24 (selK L m) = selV (L.map (toVecD 24)) m :=
  lk_selK_hom _ (toVecD_zero 24) (toVecD_xor 24) L m

theorem lk_selK_comp (B : List ℕ) : ∀ (t : List ℕ) (c : ℕ), selK B (selK t c) = selK (t.map (selK B)) c
  | [], _ => lp_selK_zero B
  | x :: t, c => by
    rw [List.map_cons]
    cases hc : c.testBit 0
    · rw [lp_selK_f hc, lp_selK_f hc, lk_selK_comp B t]
    · rw [lp_selK_t hc, lp_selK_t hc, lp_selK_xor, lk_selK_comp B t]

theorem lk_selK_top : ∀ (t : List ℕ) (j c : ℕ), j < t.length → c >>> j = 1 →
    selK t c = selK (t.take j) c ^^^ t.getD j 0
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | a :: t, 0, c, _, hc => by
    rw [Nat.shiftRight_zero] at hc
    subst hc
    have e : (1 : ℕ) >>> 1 = 0 := rfl
    rw [lp_selK_t (by decide), List.take_zero, lp_selK_nil, List.getD_cons_zero, Nat.zero_xor, e,
      lp_selK_zero, Nat.xor_zero]
  | a :: t, j + 1, c, h, hc => by
    have hc' : (c >>> 1) >>> j = 1 := by
      rw [← Nat.shiftRight_add, Nat.add_comm]
      exact hc
    have ih := lk_selK_top t j (c >>> 1) (by simpa using h) hc'
    rw [List.take_succ_cons, List.getD_cons_succ]
    cases hb : c.testBit 0
    · rw [lp_selK_f hb, lp_selK_f hb, ih]
    · rw [lp_selK_t hb, lp_selK_t hb, ih, Nat.xor_assoc]

theorem lk_selK_vmF {L : List ℕ} {F : ℕ → M24}
    (hF : ∀ k < L.length, ∀ x, toVecD 24 (vmF 24 (L.getD k 0) x) = F k *ᵥ toVecD 24 x) (m x : ℕ) :
    toVecD 24 (selK (L.map fun b => vmF 24 b x) m) =
      (∑ k ∈ Finset.range L.length, if m.testBit k = true then F k else 0) *ᵥ toVecD 24 x := by
  rw [lk_toVecD_selK, selV, Matrix.sum_mulVec, List.length_map, List.length_map]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  split_ifs
  · have e := List.getD_eq_getElem L 0 hk'
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, List.getElem_map, ← e,
      hF k hk']
  · rw [Matrix.zero_mulVec]

theorem lk_isSumF (gs : List Rows) (m : ℕ) : ∀ n,
    IsSumF gs (∑ k ∈ Finset.range n, if m.testBit k = true then fM gs k else 0)
  | 0 => ⟨[], by simp⟩
  | n + 1 => by
    obtain ⟨l, hl⟩ := lk_isSumF gs m n
    rw [Finset.sum_range_succ, hl]
    split_ifs
    · exact ⟨l ++ [n], by simp⟩
    · exact ⟨l, by simp⟩

theorem lk_vmF_unit_aux (M t : ℕ) : ∀ k, Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => if (2 ^ t).testBit k then rowF 24 M k ^^^ acc else acc) k =
      if t < k then rowF 24 M t else 0
  | 0 => by simp
  | k + 1 => by
    change (if (2 ^ t).testBit k then rowF 24 M k ^^^ _ else _) = _
    rw [lk_vmF_unit_aux M t k, Nat.testBit_two_pow]
    by_cases htk : t = k
    · subst htk
      simp
    · have : t < k + 1 ↔ t < k := by omega
      simp [htk, this]

theorem lk_fget (M : ℕ) {t : ℕ} (ht : t < 24) : fget M t 24 = vmF 24 M (2 ^ t) := by
  rw [CFSG.KC.F2W.vmF_rec, lk_vmF_unit_aux, if_pos ht]
  rfl

theorem lk_triK (g : ℕ) : ∀ L : List ℕ,
    triK g L = L.flatMap fun x => [x, mulWK x g, mulWK (mulWK x g) g]
  | [] => rfl
  | x :: L => by
    rw [List.flatMap_cons, ← lk_triK g L]
    change strictL (mulWK x g) (fun y => strictL (mulWK y g) fun z => x :: y :: z :: triK g L) = _
    rw [lp_strictL, lp_strictL]
    rfl

theorem lk_trL : ∀ G : List ℕ, trL G = G.map (trK 24)
  | [] => rfl
  | g :: G => by
    change strictL (trK 24 g) (fun t => t :: trL G) = _
    rw [lp_strictL, lk_trL G]
    rfl

theorem lk_eltsK_foldl : ∀ (G L : List ℕ),
    List.rec (motive := fun _ => List ℕ → List ℕ) (fun L => L) (fun g _ ih L => ih (triK g L)) G L =
      G.foldl (fun L g => triK g L) L
  | [], _ => rfl
  | g :: G, L => lk_eltsK_foldl G (triK g L)

theorem lk_expVecs_len : ∀ r, ∀ e ∈ expVecs 3 r, e.length = r := by
  intro r
  induction r with
  | zero =>
    intro e he
    simp [expVecs] at he
    simp [he]
  | succ r ih =>
    intro e he
    simp only [expVecs, List.mem_flatMap, List.mem_map] at he
    obtain ⟨e', he', k, -, rfl⟩ := he
    simp [ih e' he']

theorem lk_eltR_snoc (Hs : List Rows) (g : Rows) (e : List ℕ) (he : e.length = Hs.length) (a : ℕ) :
    eltR (Hs ++ [g]) (e ++ [a]) = mul (eltR Hs e) (pow g a) := by
  unfold eltR
  rw [List.zip_append he.symm, List.foldl_append]
  rfl

theorem lk_snocT {Hs : List Rows} {g' : Rows} {e : List ℕ} (he : e.length = Hs.length)
    (hG : ∀ h ∈ Hs, rowsMatrix 24 g' * rowsMatrix 24 h = rowsMatrix 24 h * rowsMatrix 24 g')
    (a : ℕ) : (rowsMatrix 24 (eltR (Hs ++ [g']) (e ++ [a])))ᵀ =
      (rowsMatrix 24 (eltR Hs e))ᵀ * (rowsMatrix 24 g')ᵀ ^ a := by
  rw [lk_eltR_snoc Hs g' e he, rowsMatrix_mul24, rowsMatrix_pow24,
    comm_pow24 (comm_eltR hG e).symm a, Matrix.transpose_mul, Matrix.transpose_pow]

theorem lk_step {Hs : List Rows} {g' : Rows} {gt : ℕ} (hgt : MatK gt = (rowsMatrix 24 g')ᵀ)
    (hG : ∀ h ∈ Hs, rowsMatrix 24 g' * rowsMatrix 24 h = rowsMatrix 24 h * rowsMatrix 24 g') :
    ∀ (E : List (List ℕ)) (K : List ℕ), (∀ e ∈ E, e.length = Hs.length) →
      K.map MatK = E.map (fun e => (rowsMatrix 24 (eltR Hs e))ᵀ) →
      (K.flatMap fun x => [x, mulWK x gt, mulWK (mulWK x gt) gt]).map MatK =
        (E.flatMap fun e => (List.range 3).map fun k => e ++ [k]).map
          (fun e => (rowsMatrix 24 (eltR (Hs ++ [g']) e))ᵀ)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)
  | e :: E, x :: K, hE, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append,
      lk_step hgt hG E K (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) h.2]
    refine (List.append_left_inj _).2 ?_
    have he := hE e List.mem_cons_self
    have h3 : List.range 3 = [0, 1, 2] := rfl
    rw [h3]
    simp only [List.map_cons, List.map_nil, lk_matK_mul, hgt, h.1, lk_snocT he hG, pow_zero,
      pow_one, pow_two, mul_one, mul_assoc]

theorem lk_K : ∀ H : List ℕ, (∀ g ∈ H, ∀ h ∈ H, MatK g * MatK h = MatK h * MatK g) →
    ((H.map (trK 24)).foldl (fun L g => triK g L) [oneK]).map MatK =
      (expVecs 3 H.length).map fun e => (rowsMatrix 24 (eltR (H.map (unpackR 24)) e))ᵀ := by
  intro H
  induction H using List.reverseRecOn with
  | nil =>
    intro _
    simp [expVecs, eltR, lk_matK_one, rowsMatrix_one24]
  | append_singleton H g ih =>
    intro hc
    have ih' := ih fun a ha b hb => hc a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.length_append, List.length_cons, List.length_nil]
    rw [lk_triK, expVecs]
    refine lk_step (lk_matK_tr g) (fun h hh => ?_) _ _ (fun e he => ?_) ih'
    · obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hh
      exact hc g (List.mem_append_right _ List.mem_cons_self) h' (List.mem_append_left _ hh')
    · rw [lk_expVecs_len _ e he, List.length_map]

theorem lk_ET {G : List ℕ} (hc : ∀ g ∈ G, ∀ h ∈ G, MatK g * MatK h = MatK h * MatK g) :
    ∀ k < (eltsK (trL G)).length, ∀ x,
      toVecD 24 (vmF 24 ((eltsK (trL G)).getD k 0) x) = fM (G.map (unpackR 24)) k *ᵥ toVecD 24 x := by
  intro k hk x
  have hK := lk_K G hc
  have he : eltsK (trL G) = (G.map (trK 24)).foldl (fun L g => triK g L) [oneK] := by
    rw [← lk_trL]
    exact lk_eltsK_foldl _ _
  rw [he] at hk ⊢
  rw [lk_vmF, List.getD_eq_getElem _ _ hk]
  have h1 := List.getElem_of_eq hK (by rw [List.length_map]; exact hk)
  simp only [List.getElem_map] at h1
  have hk2 : k < (expVecs 3 G.length).length := by
    have hl := congrArg List.length hK
    rw [List.length_map, List.length_map] at hl
    rw [← hl]
    exact hk
  have h2 : (eltsOf (G.map (unpackR 24))).getD k (one ()) =
      eltR (G.map (unpackR 24)) (expVecs 3 G.length)[k] := by
    simp [eltsOf, Array.getD, hk2]
  change _ = (rowsMatrix 24 ((eltsOf (G.map (unpackR 24))).getD k (one ()))) *ᵥ _
  rw [h2, h1, Matrix.transpose_transpose]

theorem lk_gensK_inner (g : ℕ) : ∀ L : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun h _ ih2 => andB (Nat.beq (mulWK g h) (mulWK h g)) ih2) L = true →
      ∀ h ∈ L, mulWK g h = mulWK h g
  | [], _, _, hh => by cases hh
  | a :: L, H, h, hh => by
    obtain ⟨h1, h2⟩ := lp_andB H
    rcases List.mem_cons.1 hh with rfl | hh
    · exact Nat.eq_of_beq_eq_true h1
    · exact lk_gensK_inner g L h2 h hh

theorem lk_gensK (G : List ℕ) : ∀ L : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun g _ ih => andB (canK g) (andB (Nat.beq (mulWK g (mulWK g g)) oneK)
      (andB (List.rec (motive := fun _ => Bool) true
        (fun h _ ih2 => andB (Nat.beq (mulWK g h) (mulWK h g)) ih2) G) ih))) L = true →
    ∀ g ∈ L, mulWK g (mulWK g g) = oneK ∧ ∀ h ∈ G, mulWK g h = mulWK h g
  | [], _, _, hg => by cases hg
  | a :: L, H, g, hg => by
    obtain ⟨-, H⟩ := lp_andB H
    obtain ⟨h1, H⟩ := lp_andB H
    obtain ⟨h2, h3⟩ := lp_andB H
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨Nat.eq_of_beq_eq_true h1, lk_gensK_inner g G h2⟩
    · exact lk_gensK G L h3 g hg

theorem lk_fwK (ET : List ℕ) (w : ℕ) : fwK ET w = ET.map fun b => vmF 24 b w := by
  induction ET with
  | nil => rfl
  | cons e ET ih =>
    rw [List.map_cons, ← ih]
    change strictL (vmF 24 e w) (fun v => v :: fwK ET w) = _
    exact lp_strictL _ _

theorem lk_spanK (FW : List ℕ) (PT : ℕ) : ∀ (S : List ℕ) (i : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun i => Nat.beq i (nat_lit 24))
      (fun s _ ih i => CFSG.KC.M1F2.strictB i fun i =>
        andB (Nat.beq (selK FW s) (Nat.xor (pw2 i) (fget PT i (nat_lit 24)))) (ih (Nat.succ i)))
      S i = true →
    i + S.length = 24 ∧ ∀ k < S.length, selK FW (S.getD k 0) = pw2 (i + k) ^^^ fget PT (i + k) 24
  | [], i, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | s :: S, i, h => by
    obtain ⟨h1, h2⟩ := lp_andB ((lp_strictB _ _).symm.trans h)
    obtain ⟨e, hk⟩ := lk_spanK FW PT S (i + 1) h2
    refine ⟨by rw [List.length_cons]; omega, fun k hk' => ?_⟩
    cases k with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h1
    | succ k =>
      have e2 : i + (k + 1) = i + 1 + k := by omega
      rw [List.getD_cons_succ, hk k (by simpa using hk'), e2]

theorem lk_basisK (PT : ℕ) : ∀ B : List ℕ, basisK PT B = true → ∀ b ∈ B, b < 2 ^ 24 ∧ vmF 24 PT b = b
  | [], _, _, hb => by cases hb
  | a :: B, H, b, hb => by
    obtain ⟨h1, H⟩ := lp_andB H
    obtain ⟨h2, h3⟩ := lp_andB H
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [lp_pw2] at h1
      exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
    · exact lk_basisK PT B h3 b hb

theorem lk_lenT : ∀ T : List (List ℕ), lenT T = T.length
  | [] => rfl
  | _ :: T => congrArg Nat.succ (lk_lenT T)

theorem lk_testK {XB : ℕ → ℕ} {PT : ℕ} {B : List ℕ} {j x : ℕ} (h : testK XB PT B j x = true) :
    memK XB x = true ∧ selK B (crdK B (vmF 24 PT x)) = vmF 24 PT x ∧
      crdK B (vmF 24 PT x) >>> j = 1 := by
  unfold testK at h
  obtain ⟨h1, h⟩ := lp_andB h
  rw [lp_strictB, lp_strictB] at h
  obtain ⟨h2, h3⟩ := lp_andB h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem lk_testsR {XB : ℕ → ℕ} {PT : ℕ} {B : List ℕ} : ∀ (T : List (List ℕ)) (j : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun xs _ ih j => CFSG.KC.M1F2.strictB j fun j => andB
        (List.rec (motive := fun _ => Bool) true (fun x _ ih2 => andB (testK XB PT B j x) ih2) xs)
        (ih (Nat.succ j))) T j = true →
    ∀ i < T.length, ∀ x ∈ T.getD i [], testK XB PT B (j + i) x = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | xs :: T, j, h, i, hi => by
    obtain ⟨h1, h2⟩ := lp_andB ((lp_strictB _ _).symm.trans h)
    cases i with
    | zero =>
      intro x hx
      rw [List.getD_cons_zero] at hx
      rw [Nat.add_zero]
      clear h2 h hi
      induction xs with
      | nil => cases hx
      | cons a xs ih =>
        obtain ⟨h3, h4⟩ := lp_andB h1
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h3
        · exact ih h4 hx
    | succ i =>
      intro x hx
      rw [List.getD_cons_succ] at hx
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e]
      exact lk_testsR T (j + 1) h2 i (by simpa using hi) x hx

theorem lk_allCube : ∀ P : List (List ℕ), allCubeK P = true → ∀ t ∈ P, cubeK t = true
  | [], _, _, ht => by cases ht
  | a :: P, H, t, ht => by
    obtain ⟨h1, h2⟩ := lp_andB H
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h1
    · exact lk_allCube P h2 t ht

theorem lk_strictP (y : ℕ) (k : ℕ → List (ℕ × ℕ)) : strictP y k = k y := by
  cases y <;> rfl

theorem lk_imsK (B : List ℕ) : ∀ pre : List ℕ, imsK B pre = pre.map (selK B)
  | [] => rfl
  | t :: pre => by
    rw [List.map_cons, ← lk_imsK B pre]
    change strictL (selK B t) (fun v => v :: imsK B pre) = _
    exact lp_strictL _ _

theorem lk_zsK (IM : List ℕ) : ∀ Q : List (ℕ × ℕ), zsK IM Q = Q.map fun q => q.1 ^^^ selK IM q.2
  | [] => rfl
  | q :: Q => by
    rw [List.map_cons, ← lk_zsK IM Q]
    change strictL (q.1 ^^^ selK IM q.2) (fun z => z :: zsK IM Q) = _
    exact lp_strictL _ _

theorem lk_pairsK (PT : ℕ) (B : List ℕ) : ∀ xs : List ℕ,
    pairsK PT B xs = xs.map fun x => (x ^^^ vmF 24 PT x, crdK B (vmF 24 PT x))
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, ← lk_pairsK PT B xs]
    change strictP (vmF 24 PT x) (fun px => (x ^^^ px, crdK B px) :: pairsK PT B xs) = _
    exact lk_strictP _ _

theorem lk_passK {XB : ℕ → ℕ} {v : ℕ} : ∀ Z : List ℕ, (∀ z ∈ Z, memK XB (z ^^^ v) = true) →
    passK XB Z v = true
  | [], _ => rfl
  | z :: Z, h => by
    change andB (memK XB (z ^^^ v)) (passK XB Z v) = true
    rw [h z List.mem_cons_self, lk_passK Z fun z' hz => h z' (List.mem_cons_of_mem _ hz)]
    rfl

noncomputable def lkEnumG (XB : Nat → Nat) (Z : List Nat) (B : List Nat) :
    Nat → Nat → Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Nat → List Nat)
    (fun c v _ acc => Bool.rec (motive := fun _ => List Nat) acc (List.cons c acc) (passK XB Z v))
    (fun b _ ih c v p acc => strictL p fun p => strictL (Nat.shiftLeft p (nat_lit 1)) fun p2 =>
      ih c v p2 (strictL (Nat.lor c p) fun c' => strictL (Nat.xor v b) fun v' => ih c' v' p2 acc))
    B

theorem lk_enum_cons (XB : ℕ → ℕ) (Z : List ℕ) (b : ℕ) (B : List ℕ) (c v p : ℕ) (acc : List ℕ) :
    lkEnumG XB Z (b :: B) c v p acc =
      lkEnumG XB Z B c v (p <<< 1) (lkEnumG XB Z B (c ||| p) (v ^^^ b) (p <<< 1) acc) := by
  change strictL p (fun p => strictL (Nat.shiftLeft p 1) fun p2 => lkEnumG XB Z B c v p2
    (strictL (Nat.lor c p) fun c' => strictL (Nat.xor v b) fun v' => lkEnumG XB Z B c' v' p2 acc)) = _
  simp only [lp_strictL]
  rfl

theorem lk_enum_sub {XB : ℕ → ℕ} {Z : List ℕ} : ∀ (B : List ℕ) (c v p : ℕ) (acc : List ℕ),
    ∀ y ∈ acc, y ∈ lkEnumG XB Z B c v p acc
  | [], c, v, p, acc, y, hy => by
    change y ∈ Bool.rec (motive := fun _ => List ℕ) acc (c :: acc) (passK XB Z v)
    cases passK XB Z v
    · exact hy
    · exact List.mem_cons_of_mem _ hy
  | b :: B, c, v, p, acc, y, hy => by
    rw [lk_enum_cons]
    exact lk_enum_sub B _ _ _ _ y (lk_enum_sub B _ _ _ _ y hy)

theorem lk_bits (d s : ℕ) :
    d <<< s = (if d.testBit 0 = true then 2 ^ s else 0) ||| ((d >>> 1) <<< (s + 1)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases lt_trichotomy i s with h | rfl | h
  · have h1 : ¬ (i ≥ s) := by omega
    have h2 : ¬ (i ≥ s + 1) := by omega
    cases hb : d.testBit 0 <;> simp [h1, h2, Nat.testBit_two_pow, Nat.ne_of_gt h]
  · cases hb : d.testBit 0 <;> simp [hb, Nat.testBit_two_pow]
  · have h4 : 1 + (i - (s + 1)) = i - s := by omega
    have h1 : i ≥ s := by omega
    have h2 : i ≥ s + 1 := by omega
    cases hb : d.testBit 0 <;> simp [h1, h2, h4, Nat.testBit_two_pow, Nat.ne_of_lt h]

theorem lk_enum_mem {XB : ℕ → ℕ} {Z : List ℕ} : ∀ (B : List ℕ) (c v s : ℕ) (acc : List ℕ) (d : ℕ),
    d < 2 ^ B.length → passK XB Z (v ^^^ selK B d) = true →
      (c ||| (d <<< s)) ∈ lkEnumG XB Z B c v (2 ^ s) acc
  | [], c, v, s, acc, d, hd, hp => by
    have h0 : d = 0 := by simpa using hd
    subst h0
    rw [lp_selK_nil, Nat.xor_zero] at hp
    change _ ∈ Bool.rec (motive := fun _ => List ℕ) acc (c :: acc) (passK XB Z v)
    rw [hp, Nat.zero_shiftLeft, Nat.or_zero]
    exact List.mem_cons_self
  | b :: B, c, v, s, acc, d, hd, hp => by
    rw [lk_enum_cons]
    have hp2 : 2 ^ s <<< 1 = 2 ^ (s + 1) := by rw [Nat.shiftLeft_eq, pow_one, pow_succ]
    rw [hp2]
    have hd' : d >>> 1 < 2 ^ B.length := by
      rw [List.length_cons, pow_succ] at hd
      rw [Nat.shiftRight_eq_div_pow, pow_one]
      omega
    rw [lk_bits d s]
    cases hb : d.testBit 0
    · rw [lp_selK_f hb] at hp
      simp only [Bool.false_eq_true, if_false, Nat.zero_or]
      exact lk_enum_mem B c v (s + 1) _ (d >>> 1) hd' hp
    · rw [lp_selK_t hb, ← Nat.xor_assoc] at hp
      simp only [if_true]
      rw [← Nat.or_assoc]
      exact lk_enum_sub B _ _ _ _ _ (lk_enum_mem B (c ||| 2 ^ s) (v ^^^ b) (s + 1) acc (d >>> 1) hd' hp)

theorem lk_enumK_mem {XB : ℕ → ℕ} {Z B : List ℕ} {d : ℕ} (hd : d < 2 ^ B.length)
    (hp : passK XB Z (selK B d) = true) : d ∈ enumK XB Z B := by
  have := lk_enum_mem (XB := XB) (Z := Z) B 0 0 0 [] d hd (by rw [Nat.zero_xor]; exact hp)
  rw [Nat.shiftLeft_zero, Nat.zero_or, pow_zero] at this
  exact this

theorem lk_extK_sub (pre : List ℕ) : ∀ (cs : List ℕ) (acc : List (List ℕ)), ∀ y ∈ acc,
    y ∈ extK pre cs acc
  | [], _, _, hy => hy
  | _ :: cs, acc, y, hy => List.mem_cons_of_mem _ (lk_extK_sub pre cs acc y hy)

theorem lk_extK_mem (pre : List ℕ) : ∀ (cs : List ℕ) (acc : List (List ℕ)) (c : ℕ), c ∈ cs →
    pre ++ [c] ∈ extK pre cs acc
  | [], _, _, hc => by cases hc
  | a :: cs, acc, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lk_extK_mem pre cs acc c hc)

theorem lk_levelK_mem {XB : ℕ → ℕ} {B : List ℕ} {Q : List (ℕ × ℕ)} :
    ∀ (P : List (List ℕ)) (pre : List ℕ) (c : ℕ), pre ∈ P →
      c ∈ enumK XB (zsK (imsK B pre) Q) B → pre ++ [c] ∈ levelK XB B Q P
  | [], _, _, hp, _ => by cases hp
  | p :: P, pre, c, hp, hc => by
    change _ ∈ extK p (enumK XB (zsK (imsK B p) Q) B) (levelK XB B Q P)
    rcases List.mem_cons.1 hp with rfl | hp
    · exact lk_extK_mem _ _ _ _ hc
    · exact lk_extK_sub _ _ _ _ (lk_levelK_mem P pre c hp hc)

theorem lk_searchR {XB : ℕ → ℕ} {PT : ℕ} {B : List ℕ} (t : List ℕ) :
    ∀ (T' : List (List ℕ)) (j : ℕ) (P : List (List ℕ)),
      (∀ i < T'.length, ∀ Ps : List (List ℕ), t.take (j + i) ∈ Ps →
        t.take (j + i + 1) ∈ levelK XB B (pairsK PT B (T'.getD i [])) Ps) →
      t.take j ∈ P →
      t.take (j + T'.length) ∈ List.rec (motive := fun _ => List (List ℕ) → List (List ℕ))
        (fun P => P) (fun xs _ ih P => ih (levelK XB B (pairsK PT B xs) P)) T' P
  | [], j, P, _, hP => by simpa using hP
  | xs :: T', j, P, hs, hP => by
    have h0 := hs 0 (by simp) P (by simpa using hP)
    have e : j + (xs :: T').length = j + 1 + T'.length := by
      rw [List.length_cons]
      omega
    rw [e]
    refine lk_searchR t T' (j + 1) (levelK XB B (pairsK PT B xs) P) (fun i hi Ps hPs => ?_)
      (by simpa using h0)
    have e2 : j + (i + 1) = j + 1 + i := by omega
    have := hs (i + 1) (by simpa using hi) Ps (by rw [e2]; exact hPs)
    rw [e2, List.getD_cons_succ] at this
    exact this

end Helpers

open CFSG.KC.Co1LeafP CFSG.KC.M1F2 in
theorem leafK_facts {XB : ℕ → ℕ} {G : List ℕ} {piM w : ℕ} {S B : List ℕ} {T : List (List ℕ)}
    (hX0 : ∀ x, memK XB x = true → x < 2 ^ 24) (h : leafK XB G piM w S B T = true) :
    LeafFacts (G.map (unpackR 24)) (fun x => memK XB x = true) T.flatten := by
  obtain ⟨hG, hbody⟩ := lp_andB h
  rw [leafBodyK, lp_strictB] at hbody
  generalize hPT : selK (eltsK (trL G)) piM = PT at hbody
  obtain ⟨hPP, hb⟩ := lp_andB hbody
  obtain ⟨-, hb⟩ := lp_andB hb
  obtain ⟨hPw, hb⟩ := lp_andB hb
  obtain ⟨hspan, hb⟩ := lp_andB hb
  obtain ⟨hbas, hb⟩ := lp_andB hb
  obtain ⟨hcrd, hb⟩ := lp_andB hb
  obtain ⟨htests, hcubes⟩ := lp_andB hb
  have hgen := lk_gensK G G hG
  have hcM : ∀ g ∈ G, ∀ h ∈ G, MatK g * MatK h = MatK h * MatK g := fun g hg h hh => by
    rw [← lk_matK_mul, ← lk_matK_mul, (hgen g hg).2 h hh]
  have hETv := lk_ET hcM
  set ET := eltsK (trL G) with hET
  set gs := G.map (unpackR 24) with hgs
  set P : M24 := ∑ k ∈ Finset.range ET.length, if piM.testBit k = true then fM gs k else 0 with hPdef
  have hP : ∀ x, P *ᵥ toVecD 24 x = toVecD 24 (vmF 24 PT x) := fun x => by
    rw [← hPT, lp_vmF_selK, lk_selK_vmF hETv]
  have hPm : (MatK PT)ᵀ = P := lk_ext fun x => by rw [← lk_vmF, hP]
  have hB := lk_basisK PT B hbas
  have hBlt : ∀ b ∈ B, b < 2 ^ 24 := fun b hb => (hB b hb).1
  have hBv : (B.map (toVecD 24)).length = B.length := List.length_map _
  obtain ⟨hlen, hrec⟩ := lp_andB htests
  have hTlen : T.length = B.length := by
    rw [← lk_lenT, ← lp_lenL]
    exact Nat.eq_of_beq_eq_true hlen
  have hlev : ∀ i < T.length, ∀ x ∈ T.getD i [], testK XB PT B i x = true := fun i hi x hx => by
    have := lk_testsR T 0 hrec i hi x hx
    rwa [Nat.zero_add] at this
  have hflat : ∀ i < T.length, ∀ x ∈ T.getD i [], x ∈ T.flatten := fun i hi x hx => by
    rw [List.getD_eq_getElem _ _ hi] at hx
    exact List.mem_flatten.2 ⟨_, List.getElem_mem hi, hx⟩
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_, fun x hx => ?_, ⟨P, lk_isSumF gs piM _, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hg'
    exact hcM a ha b hb
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    have e := congrArg MatK (hgen a ha).1
    rw [lk_matK_mul, lk_matK_mul, lk_matK_one] at e
    rw [pow_succ, pow_two, mul_assoc]
    exact e
  · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
    have := hlev i hi x (by rw [List.getD_eq_getElem _ _ hi]; exact hxl)
    exact (lk_testK this).1
  · rw [← hPm, ← Matrix.transpose_mul, ← lk_matK_mul, Nat.eq_of_beq_eq_true hPP]
  ·
    refine ⟨toVecD 24 w, by rw [hP, Nat.eq_of_beq_eq_true hPw, toVecD_zero],
      fun i => ∑ k ∈ Finset.range ET.length,
        if (S.getD i.val 0).testBit k = true then fM gs k else 0,
      fun i => lk_isSumF gs _ _, fun i => ?_⟩
    obtain ⟨hS24, hSk⟩ := lk_spanK (fwK ET w) PT S 0 hspan
    have e := congrArg (toVecD 24) (hSk i.val (by omega))
    rw [lk_fwK, lk_selK_vmF hETv, Nat.zero_add, toVecD_xor, lp_pw2, lk_fget PT i.isLt, ← hP,
      ← Nat.one_shiftLeft, toVecD_shiftLeft] at e
    exact e.symm
  ·
    refine ⟨B.map (toVecD 24), fun b hb => ?_, fun v => ?_, fun N hN1 hN2 => ?_⟩
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
      rw [hP, (hB b0 hb0).2]
    · obtain ⟨x, -, rfl⟩ := exists_toVecD v
      have hcr : ∀ r < 24, selK B (crdK B (CFSG.KLie.CT.fget PT r 24)) =
          CFSG.KLie.CT.fget PT r 24 := fun r hr => by
        have := lp_allN hcrd r hr
        rw [lp_strictB, lp_strictB] at this
        exact Nat.eq_of_beq_eq_true (lp_andB this).2
      obtain ⟨a, ha⟩ := lp_e_span hcr x
      exact ⟨a, by rw [← lk_toVecD_selK, ← ha, hP]⟩
    ·
      have hc : ∀ k, ∃ c, k < B.length →
          selV (B.map (toVecD 24)) c = N *ᵥ (B.map (toVecD 24)).getD k 0 := fun k => by
        by_cases hk : k < B.length
        · obtain ⟨c, hc⟩ := hN1 _ (List.getD_eq_getElem _ (0 : Vec24) (by rw [hBv]; exact hk) ▸
            List.getElem_mem (by rw [hBv]; exact hk))
          exact ⟨c, fun _ => hc⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose cf hcf using hc
      set t : List ℕ := (List.range B.length).map fun k => cf k % 2 ^ B.length with htdef
      have htl : t.length = B.length := by rw [htdef, List.length_map, List.length_range]
      have htg : ∀ k (hk : k < t.length), t[k] = cf k % 2 ^ B.length := fun k hk => by
        simp only [htdef, List.getElem_map, List.getElem_range]
      have hT : ∀ k < B.length, selV (B.map (toVecD 24)) (t.getD k 0) =
          N *ᵥ (B.map (toVecD 24)).getD k 0 := fun k hk => by
        rw [List.getD_eq_getElem _ _ (by rw [htl]; exact hk), htg, ← hBv, lk_selV_mod]
        exact hcf k hk
      have hlin : ∀ c, N *ᵥ selV (B.map (toVecD 24)) c =
          selV (B.map (toVecD 24)) (selK t c) := fun c => by
        rw [lk_selK_hom _ (lk_selV_zero _) (lk_selV_xor _) t c, selV, selV, Matrix.mulVec_sum]
        simp only [List.length_map]
        rw [htl]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        split_ifs
        · have e := List.getD_eq_getElem t 0 (by rw [htl]; exact hk')
          rw [List.getD_eq_getElem (t.map _) _ (by rw [List.length_map, htl]; exact hk'),
            List.getElem_map,
            ← e, hT k hk']
        · exact Matrix.mulVec_zero N
      have hstep : ∀ i < T.length, ∀ Ps : List (List ℕ), t.take (0 + i) ∈ Ps →
          t.take (0 + i + 1) ∈ levelK XB B (pairsK PT B (T.getD i [])) Ps := by
        intro i hi Ps hPs
        rw [Nat.zero_add] at hPs ⊢
        have hit : i < t.length := by rw [htl, ← hTlen]; exact hi
        rw [List.take_succ, List.getElem?_eq_getElem hit, Option.toList_some]
        refine lk_levelK_mem _ _ _ hPs (lk_enumK_mem ?_ ?_)
        · rw [htg i hit]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · apply lk_passK
          intro z hz
          rw [lk_zsK, lk_pairsK, List.map_map, List.mem_map] at hz
          obtain ⟨x, hx, rfl⟩ := hz
          obtain ⟨hxm, hxs, hxj⟩ := lk_testK (hlev i hi x hx)
          obtain ⟨y, hyX, hy⟩ := hN2 x (hflat i hi x hx)
          rw [hP x] at hy
          have h1 : selV (B.map (toVecD 24)) (crdK B (vmF 24 PT x)) = toVecD 24 (vmF 24 PT x) := by
            rw [← lk_toVecD_selK, hxs]
          have h2 : N *ᵥ toVecD 24 (vmF 24 PT x) =
              toVecD 24 (selK ((t.take i).map (selK B)) (crdK B (vmF 24 PT x))) +
                toVecD 24 (selK B t[i]) := by
            rw [← h1, hlin, ← lk_toVecD_selK, lk_selK_top t i _ hit hxj, lp_selK_xor, lk_selK_comp,
              toVecD_xor, List.getD_eq_getElem _ _ hit]
          have hIM : ∀ v ∈ (t.take i).map (selK B), v < 2 ^ 24 := fun v hv => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
            exact lp_selK_lt B hBlt a
          have key : y = ((x ^^^ vmF 24 PT x) ^^^
              selK ((t.take i).map (selK B)) (crdK B (vmF 24 PT x))) ^^^ selK B t[i] := by
            refine toVecD_injective (hX0 y hyX) (lp_xor_lt (lp_xor_lt (lp_xor_lt (hX0 x hxm)
              (lp_vmF_lt _ _)) (lp_selK_lt _ hIM _)) (lp_selK_lt B hBlt _)) ?_
            rw [hy, h2, toVecD_xor, toVecD_xor, toVecD_xor]
            abel
          rw [lk_imsK]
          rw [key] at hyX
          exact hyX
      have hmem := lk_searchR (XB := XB) (PT := PT) (B := B) t T 0 [[]] hstep (by simp)
      rw [Nat.zero_add, hTlen, ← htl, List.take_length] at hmem
      have hcube := lk_allCube _ hcubes t hmem
      intro b hb
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
      have hk' : k < B.length := by rw [← hBv]; exact hk
      have hkt : k < lenL t := by rw [lp_lenL, htl]; exact hk'
      have hc3 := lp_allN hcube k hkt
      rw [lp_strictB, lp_pw2] at hc3
      have e := List.getD_eq_getElem (B.map (toVecD 24)) 0 hk
      rw [← e, ← lk_selV_pow _ hk, pow_succ, pow_two, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hlin, hlin, hlin, Nat.eq_of_beq_eq_true hc3]

theorem getD_mem_of_lt {α : Type*} {L : List α} {k : ℕ} (d : α) (hk : k < L.length) :
    L.getD k d ∈ L := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem eq_one_of_leafFacts {gs : List Rows} {X : ℕ → Prop} {T : List ℕ}
    (hF : LeafFacts gs X T) {n : M24}
    (hn : ∀ g ∈ gs, n * rowsMatrix 24 g = rowsMatrix 24 g * n)
    (hXn : ∀ x, X x → ∃ y, X y ∧ n *ᵥ toVecD 24 x = toVecD 24 y)
    {m : ℕ} (hm : n ^ m = 1) (hm3 : Nat.Coprime m 3) : n = 1 := by
  obtain ⟨P, hPsum, hP2, ⟨w, hPw, S, hSsum, hS⟩, Bv, hB, hcrd, hsearch⟩ := hF.core
  have hc := hF.comm
  have h3 := hF.cube
  have hPn : P * n = n * P := (hPsum.comm hn).symm
  set A : Vec24 → M24 := fun u => ∑ i : Fin 24, if u i = 1 then S i else 0 with hAdef
  have hAn : ∀ u, n * A u = A u * n := fun u =>
    comm_finsetSum24 _ _ fun i _ => comm_ite24 ((hSsum i).comm hn)
  have hAM : ∀ u {M : M24}, IsSumF gs M → A u * M = M * A u := fun u M hM =>
    (comm_finsetSum24 _ _ fun i _ => comm_ite24 ((hSsum i).comm_sumF hc hM).symm).symm
  have hAA : ∀ u u', A u * A u' = A u' * A u := fun u u' =>
    comm_finsetSum24 _ _ fun i _ => comm_ite24 (hAM u (hSsum i))
  have hA4 : ∀ u, A u ^ 4 = A u := by
    intro u
    refine finset_sum_pow_four _ _ (fun i _ j _ => ?_) (fun i _ => ?_)
    · split_ifs
      · exact (hSsum i).comm_sumF hc (hSsum j)
      · rw [mul_zero, zero_mul]
      · rw [mul_zero, zero_mul]
      · rw [mul_zero]
    · split_ifs
      · exact (hSsum i).pow_four hc h3
      · exact zero_pow (by norm_num)
  have hsplit : ∀ u : Vec24, u + P *ᵥ u = A u *ᵥ w := by
    intro u
    calc u + P *ᵥ u
        = (∑ i : Fin 24, if u i = 1 then (Pi.single i 1 : Vec24) else 0) +
            ∑ i : Fin 24, if u i = 1 then P *ᵥ (Pi.single i 1 : Vec24) else 0 := by
          rw [← vec_eq_ite u, ← mulVec_eq_ite]
      _ = ∑ i : Fin 24, if u i = 1 then S i *ᵥ w else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs
          · exact hS i
          · rw [add_zero]
      _ = A u *ᵥ w := by
          rw [hAdef, Matrix.sum_mulVec]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs
          · rfl
          · exact (Matrix.zero_mulVec w).symm
  have hdec : ∀ u : Vec24, P *ᵥ u = 0 → u = A u *ᵥ w := by
    intro u hu
    rw [← hsplit u, hu, add_zero]
  have hnw : P *ᵥ (n *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hPn, ← Matrix.mulVec_mulVec, hPw, Matrix.mulVec_zero]
  set a : M24 := A (n *ᵥ w) with ha
  have hna : n *ᵥ w = a *ᵥ w := hdec _ hnw
  have hker_a : ∀ u, P *ᵥ u = 0 → n *ᵥ u = a *ᵥ u := by
    intro u hu
    have hu' := hdec u hu
    calc n *ᵥ u = n *ᵥ (A u *ᵥ w) := by rw [← hu']
      _ = A u *ᵥ (n *ᵥ w) := by rw [Matrix.mulVec_mulVec, hAn u, ← Matrix.mulVec_mulVec]
      _ = A u *ᵥ (a *ᵥ w) := by rw [hna]
      _ = a *ᵥ (A u *ᵥ w) := by rw [Matrix.mulVec_mulVec, hAA u, ← Matrix.mulVec_mulVec]
      _ = a *ᵥ u := by rw [← hu']
  have hker_ainv : ∀ u, P *ᵥ u = 0 → P *ᵥ (a *ᵥ u) = 0 := by
    intro u hu
    rw [Matrix.mulVec_mulVec, ← hAM _ hPsum, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have hker_pow : ∀ k u, P *ᵥ u = 0 → (n ^ k) *ᵥ u = (a ^ k) *ᵥ u := by
    intro k
    induction k with
    | zero => intro u _; rw [pow_zero, pow_zero]
    | succ k ih =>
      intro u hu
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hker_a u hu,
        ih _ (hker_ainv u hu)]
  have hker_n : ∀ k u, P *ᵥ u = 0 → P *ᵥ ((n ^ k) *ᵥ u) = 0 := by
    intro k u hu
    rw [Matrix.mulVec_mulVec, comm_pow24 hPn k, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have hK : ∀ u, P *ᵥ u = 0 → n *ᵥ u = u := by
    intro u hu
    refine mulVec_fix_of_cube hm hm3 ?_
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact absurd hm3 (by norm_num)
    set u' := (n ^ (m - 1)) *ᵥ u with hu'
    have hu'k : P *ᵥ u' = 0 := hker_n _ _ hu
    have hnu' : n *ᵥ u' = u := by
      rw [hu', Matrix.mulVec_mulVec, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), hm,
        Matrix.one_mulVec]
    have h4 : (n ^ 4) *ᵥ u' = n *ᵥ u' := by
      rw [hker_pow 4 u' hu'k, hA4, ← hker_a u' hu'k]
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ← Matrix.mulVec_mulVec, hnu'] at h4
    exact h4
  have hker : ∀ v : Vec24, P *ᵥ (v + P *ᵥ v) = 0 := fun v => by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hP2, vec_add_self]
  have hnv : ∀ v : Vec24, n *ᵥ v = (v + P *ᵥ v) + n *ᵥ (P *ᵥ v) := fun v => by
    rw [← hK _ (hker v), ← Matrix.mulVec_add, add_assoc, vec_add_self, add_zero]
  have hb3 : ∀ b ∈ Bv, (n ^ 3) *ᵥ b = b := by
    refine hsearch n (fun b hb => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc⟩ := hcrd (n *ᵥ b)
      refine ⟨c, ?_⟩
      rw [hc, Matrix.mulVec_mulVec, hPn, ← Matrix.mulVec_mulVec, hB b hb]
    · obtain ⟨y, hyX, hy⟩ := hXn x (hF.tests x hx)
      exact ⟨y, hyX, by rw [← hy, hnv]⟩
  have hI : ∀ y, n *ᵥ (P *ᵥ y) = P *ᵥ y := by
    intro y
    refine mulVec_fix_of_cube hm hm3 ?_
    obtain ⟨c, hc⟩ := hcrd y
    rw [← hc, selV, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    split_ifs
    · exact hb3 _ (getD_mem_of_lt 0 hk)
    · exact Matrix.mulVec_zero _
  refine matrix_eq_one_of_mulVec fun v => ?_
  rw [hnv, hI, add_assoc, vec_add_self, add_zero]

theorem eq_one_of_leafK {XB : ℕ → ℕ} {G : List ℕ} {piM w : ℕ} {S B : List ℕ} {T : List (List ℕ)}
    (hX0 : ∀ x, memK XB x = true → x < 2 ^ 24) (h : leafK XB G piM w S B T = true) {n : M24}
    (hn : ∀ g ∈ G, n * rowsMatrix 24 (unpackR 24 g) = rowsMatrix 24 (unpackR 24 g) * n)
    (hXn : ∀ x, memK XB x = true → ∃ y, memK XB y = true ∧ n *ᵥ toVecD 24 x = toVecD 24 y)
    {m : ℕ} (hm : n ^ m = 1) (hm3 : Nat.Coprime m 3) : n = 1 := by
  refine eq_one_of_leafFacts (leafK_facts hX0 h) (fun g hg => ?_) hXn hm hm3
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact hn g' hg'

end CFSG.KC.Co1Leaf

end
