module

public import Certificates.Data.Kernel.LocalQT.LatM
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.LocalQTA7KSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
import Mathlib.Data.List.GetD

public section

namespace CFSG.KC.LQT.L

theorem anyA_of_mem {α : Type} {l : List α} {f : α → Bool} {x : α} (hx : x ∈ l)
    (h : f x = true) : anyA l f = true := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l ih =>
    change CFSG.KC.Ord.orB (f y) (anyA l f) = true
    rw [P.orB_iff]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl h
    · exact Or.inr (ih hx)

theorem setEqM_trans {a b T : SetM} (ha : setEqM a T = true) (hb : setEqM b T = true) :
    setEqM a b = true := by
  unfold setEqM at ha hb ⊢
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at ha hb ⊢
  exact ⟨ha.1, hb.1, ha.2.2.1.trans hb.2.2.1.symm, ha.2.2.2.trans hb.2.2.2.symm⟩

theorem isLat7_of_rec {C : List Lvl} {d : ℕ} {G : List ℕ} {Ls : List (List ℕ)} {T : SetM}
    {Z : List ℕ} (hok : chainOK 7 C = true)
    (h : CFSG.KC.Ord.andB (closedM 7 C (chainF C) G (bfsM 7 C (chainF C) G d))
      (setEqM (bfsM 7 C (chainF C) G d) T) = true)
    (hZ : Z ∈ Ls) (hT : setEqM (bfsM 7 C (chainF C) Z d) T = true) :
    isLat7 C d G Ls = true := by
  rw [P.andB_iff] at h
  have ha : anyA Ls (fun Z => setEqM (bfsM 7 C (chainF C) G d) (bfsM 7 C (chainF C) Z d)) =
      true := anyA_of_mem hZ (setEqM_trans h.2 hT)
  unfold isLat7
  rw [hok, h.1, ha]
  rfl

section
open CFSG.KC.LQT.S CFSG.KC.LQT.CM CFSG.QuasithinUnique.Vol2Native.A312L

theorem isLat7_of_recG {C : List Lvl} {d : ℕ} {G Z : List Seven.P7} {Ls : List (List ℕ)}
    {T : SetM} (hok : chainOK 7 C = true) (hI : chainInj 7 C = true)
    (h : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) (G.map P.code) d) T)
      (P.allL (G.map P.code) (memM 7 C (chainF C) T)) = true)
    (hZ : Z.map P.code ∈ Ls) (hcZ : closed7 C d (Z.map P.code) = true)
    (hT : setEqM (bfsM 7 C (chainF C) (Z.map P.code) d) T = true) :
    isLat7 C d (G.map P.code) Ls = true := by
  rw [P.andB_iff] at h
  obtain ⟨hGT, hmem⟩ := h
  refine isLat7_of_rec hok ?_ hZ hT
  rw [P.andB_iff]
  refine ⟨?_, hGT⟩
  have hGZ := setEqM_trans hGT hT
  simp only [← LK.code_eq_P] at hGZ hT hcZ hmem ⊢
  unfold setEqM at hGZ hT
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at hGZ hT
  obtain ⟨hbG, hbZ, -, hm⟩ := hGZ
  simp only [map_code7] at hbG hbZ hm hT hmem ⊢
  have repG := rep7 hok hI _ d hbG
  have repZ := rep7 hok hI _ d hbZ
  have hinj := idxInj7 hok hI (chainF C)
  have memEq := repM_mask_eq hinj repG repZ hm
  have hcZ' : PermLat.closedH (Z.map Seven.R7.enc) (PermLat.bfsSet (Z.map Seven.R7.enc) d) =
      true := by
    have := closed7_sound C hI Z hcZ
    rwa [closedH7_eq, bfsSet7_eq] at this
  have hcl := PermLat.mem_closure_iff_H Seven.rawIsEnc7 Z d hcZ'
  have hgen : ∀ σ ∈ G, σ ∈ Subgroup.closure {g | g ∈ Z} := by
    intro σ hσ
    have h1 := (P.allL_iff _ _).1 hmem _ (List.mem_map_of_mem (List.mem_map_of_mem hσ))
    rw [memM_eq, hT.2.2.2.symm, ← memM_eq] at h1
    exact (hcl σ).2 ((repM_mem hinj repZ _).1 h1)
  refine (closedM_iff hinj rc7_mul rc7_one _ repG hbG).2 ?_
  unfold PermLat.closedH
  rw [Bool.and_eq_true, Std.HashSet.contains_iff_mem, List.all_eq_true]
  refine ⟨(memEq 1).2 (Seven.R7.enc_one ▸ (hcl 1).1 (Subgroup.one_mem _)), fun x hx => ?_⟩
  rw [List.all_eq_true]
  intro g hg
  rw [Std.HashSet.contains_iff_mem]
  obtain ⟨y, hy, rfl⟩ := PermLat.bfsSet_sound Seven.rawIsEnc7 Z d x
    ((memEq x).1 (Std.HashSet.mem_toList.1 hx))
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
  rw [← Seven.R7.enc_mul]
  exact (memEq _).2 ((hcl _).1 (Subgroup.mul_mem _ hy (hgen σ hσ)))

end

section
open CFSG.KC.LQT.S CFSG.KC.LQT.CM CFSG.QuasithinUnique.Vol2Native.A312L

variable {n : ℕ} {C : List Lvl} {F : ℕ}

theorem addM_bit_self (S : SetM × List ℕ) (y : ℕ) :
    (addM n C F S y).1.mask.testBit (idxM n C F y) = true := by
  rw [addM_eq]
  split_ifs with h
  · exact h
  · change (S.1.mask ||| 2 ^ idxM n C F y).testBit _ = true
    rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]

theorem addM_bit_mono (S : SetM × List ℕ) (y i : ℕ) (h : S.1.mask.testBit i = true) :
    (addM n C F S y).1.mask.testBit i = true := by
  rw [addM_eq]
  split_ifs
  · exact h
  · change (S.1.mask ||| 2 ^ idxM n C F y).testBit i = true
    rw [Nat.testBit_or, h, Bool.true_or]

theorem innerFold_mono (x : ℕ) (G : List ℕ) : ∀ (st : SetM × List ℕ) (i : ℕ),
    st.1.mask.testBit i = true →
    (G.foldl (fun st g => addM n C F st (P.mul n x g)) st).1.mask.testBit i = true := by
  induction G with
  | nil => exact fun _ _ h => h
  | cons g G ih => exact fun st i h => ih _ i (addM_bit_mono st _ i h)

theorem innerFold_bit (x : ℕ) (G : List ℕ) : ∀ (st : SetM × List ℕ) (g : ℕ), g ∈ G →
    (G.foldl (fun st g => addM n C F st (P.mul n x g)) st).1.mask.testBit
      (idxM n C F (P.mul n x g)) = true := by
  induction G with
  | nil => exact fun _ _ h => absurd h List.not_mem_nil
  | cons h G ih =>
    intro st g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact innerFold_mono x G _ _ (addM_bit_self st _)
    · exact ih _ g hg

theorem innerFold_skip (x : ℕ) (M : List ℕ) : ∀ (st : SetM × List ℕ),
    (∀ m ∈ M, st.1.mask.testBit (idxM n C F (P.mul n x m)) = true) →
    M.foldl (fun st g => addM n C F st (P.mul n x g)) st = st := by
  induction M with
  | nil => exact fun _ _ => rfl
  | cons m M ih =>
    intro st h
    rw [List.foldl_cons, addM_eq]
    simp only [h m List.mem_cons_self, ↓reduceIte]
    exact ih st fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

theorem bfsM_dup (L M N : List ℕ) (hM : ∀ m ∈ M, m ∈ L) (d : ℕ) :
    bfsM n C F (L ++ M ++ N) d = bfsM n C F (L ++ N) d := by
  have hr : ∀ S Fr, roundM n C F (L ++ M ++ N) S Fr = roundM n C F (L ++ N) S Fr := by
    intro S Fr
    rw [roundM_eq, roundM_eq]
    congr 1
    funext st x
    rw [List.foldl_append, List.foldl_append, List.foldl_append,
      innerFold_skip x M _ fun m hm => innerFold_bit x L st m (hM m hm)]
  rw [bfsM_eq, bfsM_eq]
  congr 1
  induction d with
  | zero => rfl
  | succ d ih =>
    change roundM n C F _ (stM n C F _ d).1 (stM n C F _ d).2 =
      roundM n C F _ (stM n C F _ d).1 (stM n C F _ d).2
    rw [ih, hr]

theorem bfsM_sub (L M : List ℕ) (hM : ∀ m ∈ M, m ∈ L) (d : ℕ) :
    bfsM n C F (L ++ M) d = bfsM n C F L d := by
  simpa using bfsM_dup (n := n) (C := C) (F := F) L M [] hM d

theorem map_sub_code {G₁ G₂ : List Seven.P7} (hS : G₂ ⊆ G₁) :
    ∀ m ∈ G₂.map P.code, m ∈ G₁.map P.code := by
  intro m hm
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hm
  exact List.mem_map_of_mem (hS hσ)

theorem recG_sub {C : List Lvl} {d : ℕ} {G₁ G₂ : List Seven.P7} {T : SetM} {X : Bool}
    (hS : G₂ ⊆ G₁) (h1 : setEqM (bfsM 7 C (chainF C) (G₁.map P.code) d) T = true)
    (h2 : X = true) :
    CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((G₁ ++ G₂).map P.code) d) T) X = true := by
  rw [List.map_append, bfsM_sub _ _ (map_sub_code hS), h1, h2]
  rfl

theorem recG_dup {C : List Lvl} {d : ℕ} {G₁ D N : List Seven.P7} {T : SetM} {X : Bool}
    (hD : D ⊆ G₁) (h1 : setEqM (bfsM 7 C (chainF C) ((G₁ ++ N).map P.code) d) T = true)
    (h2 : X = true) :
    CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((G₁ ++ (D ++ N)).map P.code) d) T) X =
      true := by
  rw [List.map_append, List.map_append, ← List.append_assoc,
    bfsM_dup _ _ _ (map_sub_code hD), ← List.map_append, h1, h2]
  rfl

end

theorem getD_mem_map {α β : Type} (l : List (List α)) (f : α → β) {k : ℕ} (hk : k < l.length) :
    (l.getD k []).map f ∈ l.map (List.map f) := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.mem_map_of_mem (List.getElem_mem hk)

section Ball
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]

@[expose] def ballP (gens : List R) : ℕ → R → Prop
  | 0, y => y = 1
  | d + 1, y => ballP gens d y ∨ ∃ x, ballP gens d x ∧ ∃ g ∈ gens, x * g = y

@[expose] def insH (acc : Std.HashSet R × List R) (y : R) : Std.HashSet R × List R :=
  if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)

omit [One R] in
theorem bfsStep_insH (gens : List R) (S : Std.HashSet R) (Fr : List R) :
    bfsStep gens S Fr =
      Fr.foldl (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) (S, []) := by
  unfold bfsStep insH
  rfl

abbrev GrowH (S : Std.HashSet R) (acc : Std.HashSet R × List R) : Prop :=
  (∀ z ∈ S, z ∈ acc.1) ∧ (∀ z ∈ acc.1, z ∈ S ∨ z ∈ acc.2) ∧ ∀ z ∈ acc.2, z ∈ acc.1

omit [Mul R] [One R] in
theorem growH_insH {S : Std.HashSet R} {acc : Std.HashSet R × List R} (h : GrowH S acc) (y : R) :
    GrowH S (insH acc y) ∧ y ∈ (insH acc y).1 ∧ ∀ z ∈ acc.1, z ∈ (insH acc y).1 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold insH
  split_ifs with hc
  · exact ⟨⟨h1, h2, h3⟩, Std.HashSet.contains_iff_mem.1 hc, fun z hz => hz⟩
  · dsimp only
    have hi : ∀ z ∈ acc.1, z ∈ acc.1.insert y := fun z hz =>
      Std.HashSet.mem_insert.2 (Or.inr hz)
    refine ⟨⟨fun z hz => hi z (h1 z hz), fun z hz => ?_, fun z hz => ?_⟩,
      Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true y)), hi⟩
    · rcases Std.HashSet.mem_insert.1 hz with e | hz
      · exact Or.inr (List.mem_cons.2 (Or.inl (beq_iff_eq.1 e).symm))
      · exact (h2 z hz).imp_right (List.mem_cons_of_mem _)
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _))
      · exact hi z (h3 z hz)

omit [One R] in
theorem growH_inner {S : Std.HashSet R} (x : R) : ∀ (l : List R) (acc : Std.HashSet R × List R),
    GrowH S acc →
    GrowH S (l.foldl (fun acc g => insH acc (x * g)) acc) ∧
    (∀ g ∈ l, x * g ∈ (l.foldl (fun acc g => insH acc (x * g)) acc).1) ∧
    ∀ z ∈ acc.1, z ∈ (l.foldl (fun acc g => insH acc (x * g)) acc).1
  | [], _, h => ⟨h, fun _ hg => absurd hg List.not_mem_nil, fun _ hz => hz⟩
  | g :: l, acc, h => by
    obtain ⟨h1, hy, hm⟩ := growH_insH h (x * g)
    obtain ⟨k1, k2, k3⟩ := growH_inner x l _ h1
    refine ⟨k1, fun g' hg' => ?_, fun z hz => k3 z (hm z hz)⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact k3 _ hy
    · exact k2 g' hg'

omit [One R] in
theorem growH_outer {S : Std.HashSet R} (gens : List R) :
    ∀ (Fr : List R) (acc : Std.HashSet R × List R), GrowH S acc →
    GrowH S (Fr.foldl (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) acc) ∧
    (∀ x ∈ Fr, ∀ g ∈ gens,
      x * g ∈ (Fr.foldl (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) acc).1) ∧
    ∀ z ∈ acc.1, z ∈ (Fr.foldl (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) acc).1
  | [], _, h => ⟨h, fun _ hx => absurd hx List.not_mem_nil, fun _ hz => hz⟩
  | x :: Fr, acc, h => by
    obtain ⟨h1, h2, h3⟩ := growH_inner x gens acc h
    obtain ⟨k1, k2, k3⟩ := growH_outer gens Fr _ h1
    refine ⟨k1, fun x' hx' g hg => ?_, fun z hz => k3 z (h3 z hz)⟩
    rcases List.mem_cons.1 hx' with rfl | hx'
    · exact k3 _ (h2 g hg)
    · exact k2 x' hx' g hg

abbrev InvH (gens : List R) (st : Std.HashSet R × List R) : Prop :=
  (∀ y ∈ st.2, y ∈ st.1) ∧ ∀ y ∈ st.1, y ∉ st.2 → ∀ g ∈ gens, y * g ∈ st.1

omit [One R] in
theorem bfsStep_invH (gens : List R) (st : Std.HashSet R × List R) (h : InvH gens st) :
    InvH gens (bfsStep gens st.1 st.2) ∧ (∀ y ∈ st.1, y ∈ (bfsStep gens st.1 st.2).1) ∧
    ∀ y ∈ st.1, ∀ g ∈ gens, y * g ∈ (bfsStep gens st.1 st.2).1 := by
  obtain ⟨hF, hI⟩ := h
  rw [bfsStep_insH]
  obtain ⟨⟨-, g2, g3⟩, h2, h3⟩ := growH_outer gens st.2 (st.1, [])
    ⟨fun z hz => hz, fun z hz => Or.inl hz, fun z hz => absurd hz List.not_mem_nil⟩
  have hp : ∀ y ∈ st.1, ∀ g ∈ gens, y * g ∈ (st.2.foldl
      (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) (st.1, [])).1 := by
    intro y hy g hg
    by_cases hyF : y ∈ st.2
    · exact h2 y hyF g hg
    · exact h3 _ (hI y hy hyF g hg)
  refine ⟨⟨g3, fun y hy hn g hg => ?_⟩, h3, hp⟩
  rcases g2 y hy with hy | hy
  · exact hp y hy g hg
  · exact absurd hy hn

theorem bfsRun_ballP (gens : List R) : ∀ (d r : ℕ) (st : Std.HashSet R × List R), InvH gens st →
    (∀ y, ballP gens r y → y ∈ st.1) → ∀ y, ballP gens (r + d) y → y ∈ (bfsRun gens d st).1
  | 0, _, _, _, hb => hb
  | d + 1, r, st, h, hb => by
    obtain ⟨h1, h2, h3⟩ := bfsStep_invH gens st h
    have hb' : ∀ y, ballP gens (r + 1) y → y ∈ (bfsStep gens st.1 st.2).1 := by
      intro y hy
      rw [ballP] at hy
      rcases hy with hy | ⟨x, hx, g, hg, rfl⟩
      · exact h2 y (hb y hy)
      · exact h3 x (hb x hx) g hg
    intro y hy
    have e : r + (d + 1) = r + 1 + d := by omega
    rw [e] at hy
    exact bfsRun_ballP gens d (r + 1) _ h1 hb' y hy

theorem mem_bfsSet_of_ballP (gens : List R) (d : ℕ) (y : R) (h : ballP gens d y) :
    y ∈ bfsSet gens d := by
  have h1 : (1 : R) ∈ ((∅ : Std.HashSet R).insert 1) :=
    Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _))
  refine bfsRun_ballP gens d 0 _ ⟨fun z hz => ?_, fun z hz' hn => absurd ?_ hn⟩ ?_ y
    (by rwa [Nat.zero_add])
  · rw [List.mem_singleton.1 hz]
    exact h1
  · rcases Std.HashSet.mem_insert.1 hz' with e | e
    · exact List.mem_singleton.2 (beq_iff_eq.1 e).symm
    · exact absurd e Std.HashSet.not_mem_empty
  · intro z hz
    rw [ballP] at hz
    rw [hz]
    exact h1

omit [DecidableEq R] [Hashable R] in
theorem ballP_one (gens : List R) : ∀ d, ballP gens d 1
  | 0 => rfl
  | d + 1 => Or.inl (ballP_one gens d)

omit [DecidableEq R] [Hashable R] in
theorem ballP_mono {L L' : List R} (hL : ∀ g ∈ L, g ∈ L') : ∀ (d : ℕ) (y : R),
    ballP L d y → ballP L' d y
  | 0, _, h => h
  | d + 1, y, h => by
    rw [ballP] at h ⊢
    rcases h with h | ⟨x, hx, g, hg, e⟩
    · exact Or.inl (ballP_mono hL d y h)
    · exact Or.inr ⟨x, ballP_mono hL d x hx, g, hL g hg, e⟩

omit [One R] in
theorem insH_fold_all (Q : R → Prop) (x : R) : ∀ (l : List R) (acc : Std.HashSet R × List R),
    (∀ z ∈ acc.1, Q z) → (∀ g ∈ l, Q (x * g)) →
    ∀ z ∈ (l.foldl (fun acc g => insH acc (x * g)) acc).1, Q z
  | [], _, h, _ => h
  | g :: l, acc, h, hl => by
    refine insH_fold_all Q x l _ (fun z hz => ?_) (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
    change z ∈ (insH acc (x * g)).1 at hz
    unfold insH at hz
    split_ifs at hz
    · exact h z hz
    · rcases Std.HashSet.mem_insert.1 hz with e | hz
      · rw [← beq_iff_eq.1 e]
        exact hl g List.mem_cons_self
      · exact h z hz

omit [One R] in
theorem outer_fold_all (Q : R → Prop) (gens : List R) :
    ∀ (Fr : List R) (acc : Std.HashSet R × List R), (∀ z ∈ acc.1, Q z) →
    (∀ x ∈ Fr, ∀ g ∈ gens, Q (x * g)) →
    ∀ z ∈ (Fr.foldl (fun acc x => gens.foldl (fun acc g => insH acc (x * g)) acc) acc).1, Q z
  | [], _, h, _ => h
  | x :: Fr, acc, h, hl =>
    outer_fold_all Q gens Fr _ (insH_fold_all Q x gens acc h (hl x List.mem_cons_self))
      fun x' hx' => hl x' (List.mem_cons_of_mem _ hx')

theorem bfsRun_sub_ballP (gens : List R) : ∀ (d r : ℕ) (st : Std.HashSet R × List R),
    (∀ y ∈ st.2, y ∈ st.1) → (∀ y ∈ st.1, ballP gens r y) →
    ∀ y ∈ (bfsRun gens d st).1, ballP gens (r + d) y
  | 0, _, _, _, hb => hb
  | d + 1, r, st, hF, hb => by
    have hg := growH_outer (S := st.1) gens st.2 (st.1, [])
      ⟨fun z hz => hz, fun z hz => Or.inl hz, fun z hz => absurd hz List.not_mem_nil⟩
    have hb' : ∀ y ∈ (bfsStep gens st.1 st.2).1, ballP gens (r + 1) y := by
      rw [bfsStep_insH]
      refine outer_fold_all _ gens st.2 (st.1, []) (fun z hz => Or.inl (hb z hz)) ?_
      intro x hx g hg
      exact Or.inr ⟨x, hb x (hF x hx), g, hg, rfl⟩
    have hF' : ∀ y ∈ (bfsStep gens st.1 st.2).2, y ∈ (bfsStep gens st.1 st.2).1 := by
      rw [bfsStep_insH]
      exact hg.1.2.2
    intro y hy
    have e : r + (d + 1) = r + 1 + d := by omega
    rw [e]
    exact bfsRun_sub_ballP gens d (r + 1) _ hF' hb' y hy

theorem ballP_of_mem_bfsSet (gens : List R) (d : ℕ) (y : R) (h : y ∈ bfsSet gens d) :
    ballP gens d y := by
  have hF : ∀ z ∈ [(1 : R)], z ∈ ((∅ : Std.HashSet R).insert 1) := by
    intro z hz
    rw [List.mem_singleton.1 hz]
    exact Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _))
  have hb : ∀ z ∈ ((∅ : Std.HashSet R).insert 1), ballP gens 0 z := by
    intro z hz
    rcases Std.HashSet.mem_insert.1 hz with e | e
    · exact (beq_iff_eq.1 e).symm
    · exact absurd e Std.HashSet.not_mem_empty
  have := bfsRun_sub_ballP gens d 0 ((∅ : Std.HashSet R).insert 1, [1]) hF hb y h
  rwa [Nat.zero_add] at this

theorem mem_bfsSet_iff_of_closed {L L' : List R} {d : ℕ} (hL : ∀ g ∈ L, g ∈ L')
    (hc : ∀ x ∈ bfsSet L d, ∀ g ∈ L', x * g ∈ bfsSet L d) (y : R) :
    y ∈ bfsSet L' d ↔ y ∈ bfsSet L d := by
  constructor
  · have h1 := mem_bfsSet_of_ballP L d 1 (ballP_one L d)
    refine bfsRun_sound L' (· ∈ bfsSet L d) hc d ((∅ : Std.HashSet R).insert 1, [1])
      (fun z hz => ?_) (fun z hz => ?_) y
    · rcases Std.HashSet.mem_insert.1 hz with e | e
      · rw [← beq_iff_eq.1 e]
        exact h1
      · exact absurd e Std.HashSet.not_mem_empty
    · rw [List.mem_singleton.1 hz]
      exact h1
  · exact fun h => mem_bfsSet_of_ballP L' d y (ballP_mono hL d y (ballP_of_mem_bfsSet L d y h))

omit [DecidableEq R] [Hashable R] in
theorem ballP_le {L : List R} {a b : ℕ} (hab : a ≤ b) (y : R) (h : ballP L a y) : ballP L b y := by
  induction b with
  | zero => rwa [Nat.le_zero.1 hab] at h
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hl | hl
    · exact Or.inl (ih (Nat.lt_succ_iff.1 hl))
    · rwa [Nat.le_antisymm hab hl] at h

omit [DecidableEq R] [Hashable R] in
theorem ballP_mul {L : List R} (hA : ∀ a b c : R, a * b * c = a * (b * c))
    (h1 : ∀ a : R, a * 1 = a) {a : ℕ} {x : R} (hx : ballP L a x) :
    ∀ (b : ℕ) (y : R), ballP L b y → ballP L (a + b) (x * y)
  | 0, y, hy => by
    rw [ballP] at hy
    rw [hy, h1]
    exact hx
  | b + 1, y, hy => by
    rw [ballP] at hy
    rcases hy with hy | ⟨z, hz, g, hg, rfl⟩
    · exact Or.inl (ballP_mul hA h1 hx b y hy)
    · rw [← hA]
      exact Or.inr ⟨x * z, ballP_mul hA h1 hx b z hz, g, hg, rfl⟩

omit [DecidableEq R] [Hashable R] in
theorem ballP_comp {S L : List R} {k : ℕ} (hA : ∀ a b c : R, a * b * c = a * (b * c))
    (h1 : ∀ a : R, a * 1 = a) (hS : ∀ s ∈ S, ballP L k s) :
    ∀ (m : ℕ) (y : R), ballP S m y → ballP L (m * k) y
  | 0, y, hy => by
    rw [ballP] at hy
    rw [hy, Nat.zero_mul]
    rfl
  | m + 1, y, hy => by
    rw [ballP] at hy
    rw [Nat.succ_mul]
    rcases hy with hy | ⟨x, hx, s, hs, rfl⟩
    · exact ballP_le (Nat.le_add_right _ _) y (ballP_comp hA h1 hS m y hy)
    · exact ballP_mul hA h1 (ballP_comp hA h1 hS m x hx) k s (hS s hs)

end Ball

section MaskBall
open CFSG.KC.LQT.S CFSG.KC.LQT.CM CFSG.QuasithinUnique.Vol2Native.A312L

variable {n : ℕ} {C : List Lvl} {F : ℕ} {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  {φ : R → ℕ}

abbrev OkK (φ : R → ℕ) (K : R → Prop) (B : SetM × List ℕ) : Prop :=
  B.1.ok = true ∧ ∀ c ∈ B.2, ∃ r, K r ∧ φ r = c

omit [Mul R] [One R] [DecidableEq R] [Hashable R] in
theorem okK_addM {K : R → Prop} (hKF : ∀ r, K r → idxM n C F (φ r) < F) {B : SetM × List ℕ}
    (h : OkK φ K B) {r : R} (hr : K r) : OkK φ K (addM n C F B (φ r)) := by
  obtain ⟨hok, hfr⟩ := h
  rw [addM_eq]
  split_ifs
  · exact ⟨hok, hfr⟩
  · refine ⟨P.andB_iff.2 ⟨hok, P.blt_iff.2 (hKF r hr)⟩, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨r, hr, rfl⟩
    · exact hfr c hc

omit [One R] [DecidableEq R] [Hashable R] in
theorem okK_inner {K : R → Prop} (hKF : ∀ r, K r → idxM n C F (φ r) < F) {gens : List R}
    (hKm : ∀ x, K x → ∀ g ∈ gens, K (x * g)) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    {x : R} (hx : K x) : ∀ (gs : List R), (∀ g ∈ gs, g ∈ gens) → ∀ B, OkK φ K B →
    OkK φ K ((gs.map φ).foldl (fun st g => addM n C F st (P.mul n (φ x) g)) B)
  | [], _, _, h => h
  | g :: gs, hg, B, h => by
    rw [List.map_cons, List.foldl_cons, ← hmf]
    exact okK_inner hKF hKm hmf hx gs (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) _
      (okK_addM hKF h (hKm x hx g (hg g List.mem_cons_self)))

omit [One R] [DecidableEq R] [Hashable R] in
theorem okK_outer {K : R → Prop} (hKF : ∀ r, K r → idxM n C F (φ r) < F) (gens : List R)
    (hKm : ∀ x, K x → ∀ g ∈ gens, K (x * g)) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b)) :
    ∀ (Fr : List ℕ), (∀ c ∈ Fr, ∃ r, K r ∧ φ r = c) → ∀ B, OkK φ K B →
    OkK φ K (Fr.foldl (fun st x => (gens.map φ).foldl
      (fun st g => addM n C F st (P.mul n x g)) st) B)
  | [], _, _, h => h
  | c :: Fr, hF, B, h => by
    obtain ⟨r, hr, e⟩ := hF c List.mem_cons_self
    rw [List.foldl_cons, ← e]
    exact okK_outer hKF gens hKm hmf Fr (fun c' h' => hF c' (List.mem_cons_of_mem _ h')) _
      (okK_inner hKF hKm hmf hr gens (fun g hg => hg) B h)

omit [DecidableEq R] [Hashable R] in
theorem okK_stM {K : R → Prop} (hKF : ∀ r, K r → idxM n C F (φ r) < F) (gens : List R)
    (hKm : ∀ x, K x → ∀ g ∈ gens, K (x * g)) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (h1 : φ 1 = P.one n) (hK1 : K 1) : ∀ d, OkK φ K (stM n C F (gens.map φ) d)
  | 0 => by
    change OkK φ K (addM n C F (SetM.mk 0 0 [] true, []) (P.one n))
    rw [← h1]
    exact okK_addM hKF ⟨rfl, fun c hc => absurd hc List.not_mem_nil⟩ hK1
  | d + 1 => by
    obtain ⟨hok, hfr⟩ := okK_stM hKF gens hKm hmf h1 hK1 d
    change OkK φ K (roundM n C F (gens.map φ) (stM n C F (gens.map φ) d).1
      (stM n C F (gens.map φ) d).2)
    rw [roundM_eq]
    exact okK_outer hKF gens hKm hmf _ hfr _ ⟨hok, fun c hc => absurd hc List.not_mem_nil⟩

omit [DecidableEq R] [Hashable R] in
theorem ok_bfsM_of_K {K : R → Prop} (hKF : ∀ r, K r → idxM n C F (φ r) < F) (gens : List R)
    (hKm : ∀ x, K x → ∀ g ∈ gens, K (x * g)) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (h1 : φ 1 = P.one n) (hK1 : K 1) (d : ℕ) : (bfsM n C F (gens.map φ) d).ok = true := by
  rw [bfsM_eq]
  exact (okK_stM hKF gens hKm hmf h1 hK1 d).1

theorem setEqM_of_mem_iff (hinj : IdxInj φ n C F)
    (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b)) (h1 : φ 1 = P.one n) {L L' : List R}
    {d : ℕ} (ha : (bfsM n C F (L.map φ) d).ok = true) (hb : (bfsM n C F (L'.map φ) d).ok = true)
    (he : ∀ r, r ∈ PermLat.bfsSet L d ↔ r ∈ PermLat.bfsSet L' d) :
    setEqM (bfsM n C F (L.map φ) d) (bfsM n C F (L'.map φ) d) = true := by
  obtain ⟨E, hnd, hmem, -, hsz, hbit, -⟩ := rep_bfsM hinj hmf h1 L d ha
  obtain ⟨E', hnd', hmem', -, hsz', hbit', -⟩ := rep_bfsM hinj hmf h1 L' d hb
  have hEE : ∀ r, r ∈ E ↔ r ∈ E' := fun r => by rw [← hmem, ← hmem', he]
  unfold setEqM
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff]
  refine ⟨ha, hb, ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
  · rw [hsz, hsz']
    exact ((List.perm_ext_iff_of_nodup hnd hnd').2 hEE).length_eq
  · rw [Bool.eq_iff_iff, hbit, hbit']
    simp only [hEE]

theorem setEqM_trans' {a b T : SetM} (ha : setEqM a b = true) (hb : setEqM b T = true) :
    setEqM a T = true := by
  unfold setEqM at ha hb ⊢
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at ha hb ⊢
  exact ⟨ha.1, hb.2.1, ha.2.2.1.trans hb.2.2.1, ha.2.2.2.trans hb.2.2.2⟩

theorem recG_mono {C : List Lvl} {d : ℕ} {G G' Z : List Seven.P7} {T : SetM}
    (hok : chainOK 7 C = true) (hI : chainInj 7 C = true) (hS : G ⊆ G')
    (h1 : setEqM (bfsM 7 C (chainF C) (G.map P.code) d) T = true)
    (hmem : P.allL (G'.map P.code) (memM 7 C (chainF C) T) = true)
    (hcZ : closed7 C d (Z.map P.code) = true)
    (hT : setEqM (bfsM 7 C (chainF C) (Z.map P.code) d) T = true) :
    setEqM (bfsM 7 C (chainF C) (G'.map P.code) d) T = true := by
  have hGZ := setEqM_trans h1 hT
  simp only [← LK.code_eq_P] at h1 hmem hcZ hT hGZ ⊢
  have hT' := hT
  unfold setEqM at hGZ hT'
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at hGZ hT'
  obtain ⟨hbG, hbZ, -, hm⟩ := hGZ
  simp only [map_code7] at hbG hbZ hm hT hT' hmem h1 ⊢
  have repG := rep7 hok hI _ d hbG
  have repZ := rep7 hok hI _ d hbZ
  have hinj := idxInj7 hok hI (chainF C)
  have memEq := repM_mask_eq hinj repG repZ hm
  have hcZ' : PermLat.closedH (Z.map Seven.R7.enc) (PermLat.bfsSet (Z.map Seven.R7.enc) d) =
      true := by
    have := closed7_sound C hI Z hcZ
    rwa [closedH7_eq, bfsSet7_eq] at this
  have hcl := PermLat.mem_closure_iff_H Seven.rawIsEnc7 Z d hcZ'
  have hgen : ∀ σ ∈ G', σ ∈ Subgroup.closure {g | g ∈ Z} := by
    intro σ hσ
    have h1 := (P.allL_iff _ _).1 hmem _ (List.mem_map_of_mem (List.mem_map_of_mem hσ))
    rw [memM_eq, hT'.2.2.2.symm, ← memM_eq] at h1
    exact (hcl σ).2 ((repM_mem hinj repZ _).1 h1)
  have hKm : ∀ x ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d, ∀ g ∈ G'.map Seven.R7.enc,
      x * g ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d := by
    intro x hx g hg
    obtain ⟨y, hy, rfl⟩ := PermLat.bfsSet_sound Seven.rawIsEnc7 Z d x hx
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    rw [← Seven.R7.enc_mul]
    exact (hcl _).1 (Subgroup.mul_mem _ hy (hgen σ hσ))
  have hc : ∀ x ∈ PermLat.bfsSet (G.map Seven.R7.enc) d, ∀ g ∈ G'.map Seven.R7.enc,
      x * g ∈ PermLat.bfsSet (G.map Seven.R7.enc) d := fun x hx g hg =>
    (memEq _).2 (hKm x ((memEq x).1 hx) g hg)
  have he := mem_bfsSet_iff_of_closed (List.map_subset _ hS) hc
  have hKF : ∀ r ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d, idxM 7 C (chainF C) (rc7 r) < chainF C := by
    intro r hr
    obtain ⟨E, -, hE, -, -, -, hlt⟩ := repZ
    exact hlt r ((hE r).1 hr)
  have hok' := ok_bfsM_of_K (K := (· ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d)) hKF _ hKm rc7_mul
    rc7_one (mem_bfsSet_of_ballP _ d 1 (ballP_one _ d)) d
  refine setEqM_trans' ?_ hT
  refine setEqM_of_mem_iff hinj rc7_mul rc7_one hok' hbZ fun r => ?_
  rw [he, memEq]

theorem recG_monoR {C : List Lvl} {d : ℕ} {G G' Z : List Seven.P7} {T : SetM}
    (hok : chainOK 7 C = true) (hI : chainInj 7 C = true) (hS : G ⊆ G')
    (h1 : setEqM (bfsM 7 C (chainF C) (G.map P.code) d) T = true)
    (hmem : P.allL (G'.map P.code) (memM 7 C (chainF C) T) = true)
    (hcZ : closed7 C d (Z.map P.code) = true)
    (hT : setEqM (bfsM 7 C (chainF C) (Z.map P.code) d) T = true) :
    CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) (G'.map P.code) d) T)
      (P.allL (G'.map P.code) (memM 7 C (chainF C) T)) = true :=
  P.andB_iff.2 ⟨recG_mono hok hI hS h1 hmem hcZ hT, hmem⟩

theorem r7_get_mul (x y : Seven.R7) (i : Fin 7) :
    (Seven.R7.mul x y).get i = x.get (y.get i) := by
  fin_cases i <;> rfl

theorem r7_mul_assoc (x y z : Seven.R7) : x * y * z = x * (y * z) := by
  change (⟨(Seven.R7.mul x y).get z.a, (Seven.R7.mul x y).get z.b, (Seven.R7.mul x y).get z.c,
    (Seven.R7.mul x y).get z.d, (Seven.R7.mul x y).get z.e, (Seven.R7.mul x y).get z.f,
    (Seven.R7.mul x y).get z.g⟩ : Seven.R7) = ⟨x.get (y.get z.a), x.get (y.get z.b),
    x.get (y.get z.c), x.get (y.get z.d), x.get (y.get z.e), x.get (y.get z.f), x.get (y.get z.g)⟩
  simp only [r7_get_mul]

theorem r7_mul_one (x : Seven.R7) : x * 1 = x := by
  cases x
  rfl

theorem recG_ball {C : List Lvl} {d m k : ℕ} {S G' Z : List Seven.P7} {T : SetM}
    (hok : chainOK 7 C = true) (hI : chainInj 7 C = true) (hd : m * k ≤ d)
    (h1 : setEqM (bfsM 7 C (chainF C) (S.map P.code) m) T = true)
    (hWo : (bfsM 7 C (chainF C) (G'.map P.code) k).ok = true)
    (hW : P.allL (S.map P.code) (memM 7 C (chainF C) (bfsM 7 C (chainF C) (G'.map P.code) k)) =
      true)
    (hmem : P.allL (G'.map P.code) (memM 7 C (chainF C) T) = true)
    (hcZ : closed7 C d (Z.map P.code) = true)
    (hT : setEqM (bfsM 7 C (chainF C) (Z.map P.code) d) T = true) :
    setEqM (bfsM 7 C (chainF C) (G'.map P.code) d) T = true := by
  have hGZ := setEqM_trans h1 hT
  simp only [← LK.code_eq_P] at h1 hWo hW hmem hcZ hT hGZ ⊢
  have hT' := hT
  unfold setEqM at hGZ hT'
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff, P.beq_iff] at hGZ hT'
  obtain ⟨hbS, hbZ, -, hm⟩ := hGZ
  simp only [map_code7] at hbS hbZ hm hT hT' hmem h1 hWo hW ⊢
  have repS := rep7 hok hI _ m hbS
  have repZ := rep7 hok hI _ d hbZ
  have repW := rep7 hok hI _ k hWo
  have hinj := idxInj7 hok hI (chainF C)
  have memEq := repM_mask_eq hinj repS repZ hm
  have hcZ' : PermLat.closedH (Z.map Seven.R7.enc) (PermLat.bfsSet (Z.map Seven.R7.enc) d) =
      true := by
    have := closed7_sound C hI Z hcZ
    rwa [closedH7_eq, bfsSet7_eq] at this
  have hcl := PermLat.mem_closure_iff_H Seven.rawIsEnc7 Z d hcZ'
  have hgen : ∀ σ ∈ G', σ ∈ Subgroup.closure {g | g ∈ Z} := by
    intro σ hσ
    have h2 := (P.allL_iff _ _).1 hmem _ (List.mem_map_of_mem (List.mem_map_of_mem hσ))
    rw [memM_eq, hT'.2.2.2.symm, ← memM_eq] at h2
    exact (hcl σ).2 ((repM_mem hinj repZ _).1 h2)
  have hKm : ∀ x ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d, ∀ g ∈ G'.map Seven.R7.enc,
      x * g ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d := by
    intro x hx g hg
    obtain ⟨y, hy, rfl⟩ := PermLat.bfsSet_sound Seven.rawIsEnc7 Z d x hx
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    rw [← Seven.R7.enc_mul]
    exact (hcl _).1 (Subgroup.mul_mem _ hy (hgen σ hσ))
  have hSW : ∀ s ∈ S.map Seven.R7.enc, ballP (G'.map Seven.R7.enc) k s := by
    intro s hs
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hs
    have h2 := (P.allL_iff _ _).1 hW _ (List.mem_map_of_mem (List.mem_map_of_mem hσ))
    exact ballP_of_mem_bfsSet _ k _ ((repM_mem hinj repW _).1 h2)
  have h1Z : (1 : Seven.R7) ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d :=
    mem_bfsSet_of_ballP _ d 1 (ballP_one _ d)
  have he : ∀ r, r ∈ PermLat.bfsSet (G'.map Seven.R7.enc) d ↔
      r ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d := by
    intro r
    constructor
    · refine PermLat.bfsRun_sound _ (· ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d) hKm d
        ((∅ : Std.HashSet Seven.R7).insert 1, [1]) (fun z hz => ?_) (fun z hz => ?_) r
      · rcases Std.HashSet.mem_insert.1 hz with e | e
        · rw [← beq_iff_eq.1 e]
          exact h1Z
        · exact absurd e Std.HashSet.not_mem_empty
      · rw [List.mem_singleton.1 hz]
        exact h1Z
    · intro hr
      refine mem_bfsSet_of_ballP _ d r (ballP_le hd r ?_)
      exact ballP_comp r7_mul_assoc r7_mul_one hSW m r
        (ballP_of_mem_bfsSet _ m r ((memEq r).2 hr))
  have hKF : ∀ r ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d, idxM 7 C (chainF C) (rc7 r) < chainF C := by
    intro r hr
    obtain ⟨E, -, hE, -, -, -, hlt⟩ := repZ
    exact hlt r ((hE r).1 hr)
  have hok' := ok_bfsM_of_K (K := (· ∈ PermLat.bfsSet (Z.map Seven.R7.enc) d)) hKF _ hKm rc7_mul
    rc7_one h1Z d
  refine setEqM_trans' ?_ hT
  exact setEqM_of_mem_iff hinj rc7_mul rc7_one hok' hbZ he

theorem recG_ballR {C : List Lvl} {d m k : ℕ} {S G' Z : List Seven.P7} {T : SetM}
    (hok : chainOK 7 C = true) (hI : chainInj 7 C = true) (hd : m * k ≤ d)
    (h1 : setEqM (bfsM 7 C (chainF C) (S.map P.code) m) T = true)
    (hWo : (bfsM 7 C (chainF C) (G'.map P.code) k).ok = true)
    (hW : P.allL (S.map P.code) (memM 7 C (chainF C) (bfsM 7 C (chainF C) (G'.map P.code) k)) =
      true)
    (hmem : P.allL (G'.map P.code) (memM 7 C (chainF C) T) = true)
    (hcZ : closed7 C d (Z.map P.code) = true)
    (hT : setEqM (bfsM 7 C (chainF C) (Z.map P.code) d) T = true) :
    CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) (G'.map P.code) d) T)
      (P.allL (G'.map P.code) (memM 7 C (chainF C) T)) = true :=
  P.andB_iff.2 ⟨recG_ball hok hI hd h1 hWo hW hmem hcZ hT, hmem⟩

theorem sub_mid {α : Type} {D A B X : List α} (h : A ⊆ B) : D ++ A ++ X ⊆ D ++ B ++ X := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_left _ (List.mem_append_right _ (h hx))
  · exact List.mem_append_right _ hx

theorem sub_pair {α : Type} {D : List α} {a b : α} : D ++ [b, a] ⊆ D ++ [a] ++ (D ++ [b]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append_left _ (List.mem_append_left _ hx)
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
    · exact List.mem_append_left _ (List.mem_append_right _ hx)

theorem setEqM_of_recR {a T : SetM} {X : Bool} (h : CFSG.KC.Ord.andB (setEqM a T) X = true) :
    setEqM a T = true :=
  (P.andB_iff.1 h).1

end MaskBall

end CFSG.KC.LQT.L

end
