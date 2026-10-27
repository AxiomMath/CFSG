module

public import Certificates.Data.OmegaSevenMax.Checker

public section

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax

theorem encV_lt (v : V) : encV v < 2187 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  unfold encV
  omega

theorem digit_encV (v : V) (i : Fin 7) : encV v / 3 ^ (i : ℕ) % 3 = (v i).val := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  unfold encV
  match i with
  | ⟨0, _⟩ => show _ / 1 % 3 = (v 0).val; omega
  | ⟨1, _⟩ => show _ / 3 % 3 = (v 1).val; omega
  | ⟨2, _⟩ => show _ / 9 % 3 = (v 2).val; omega
  | ⟨3, _⟩ => show _ / 27 % 3 = (v 3).val; omega
  | ⟨4, _⟩ => show _ / 81 % 3 = (v 4).val; omega
  | ⟨5, _⟩ => show _ / 243 % 3 = (v 5).val; omega
  | ⟨6, _⟩ => show _ / 729 % 3 = (v 6).val; omega
  | ⟨n + 7, h⟩ => exact absurd h (by omega)

theorem decV_encV (v : V) : decV (encV v) = v := by
  funext i
  simp only [decV, digit_encV, ZMod.natCast_zmod_val]

theorem encV_decV {c : ℕ} (hc : c < 2187) : encV (decV c) = c := by
  have e0 : ((0 : Fin 7) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 7) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 7) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 7) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 7) : ℕ) = 4 := rfl
  have e5 : ((5 : Fin 7) : ℕ) = 5 := rfl
  have e6 : ((6 : Fin 7) : ℕ) = 6 := rfl
  simp only [encV, decV, ZMod.val_natCast, e0, e1, e2, e3, e4, e5, e6, Nat.reducePow, pow_zero,
    Nat.div_one]
  omega

theorem decV_injOn {c d : ℕ} (hc : c < 2187) (hd : d < 2187) (h : decV c = decV d) : c = d := by
  rw [← encV_decV hc, ← encV_decV hd, h]

theorem testBit_foldl (L : List ℕ) (acc c : ℕ) :
    (L.foldl (fun a d => a ||| (1 <<< d)) acc).testBit c = (acc.testBit c || decide (c ∈ L)) := by
  induction L generalizing acc with
  | nil => simp
  | cons d t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases h1 : d = c
    · subst h1
      simp
    · have h2 : ¬ c = d := fun h => h1 h.symm
      simp [h1, h2]

theorem testBit_bitsOf (L : List ℕ) (c : ℕ) : (bitsOf L).testBit c = decide (c ∈ L) := by
  unfold bitsOf
  rw [testBit_foldl]
  simp

theorem bitsOf_eq_iff {L L' : List ℕ} : bitsOf L = bitsOf L' ↔ ∀ c, c ∈ L ↔ c ∈ L' := by
  constructor
  · intro h c
    have h' := congrArg (fun n => n.testBit c) h
    simp only [testBit_bitsOf, decide_eq_decide] at h'
    exact h'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro c
    rw [testBit_bitsOf, testBit_bitsOf]
    exact decide_eq_decide.2 (h c)

theorem nodupB_iff (L : List ℕ) : nodupB L = true ↔ L.Nodup := by
  induction L with
  | nil => simp [nodupB]
  | cons a t ih =>
    first
      | (simp [nodupB, ih]; done)
      | (show (!t.contains a && nodupB t) = true ↔ _
         rw [Bool.and_eq_true, ih, List.nodup_cons]
         simp [List.contains_eq_mem])

@[expose] def decSet (L : List ℕ) : Finset V := (L.map decV).toFinset

theorem mem_decSet {L : List ℕ} {x : V} : x ∈ decSet L ↔ ∃ c ∈ L, decV c = x := by
  simp [decSet]

theorem decSet_eq_of_bitsOf {L L' : List ℕ} (h : bitsOf L = bitsOf L') : decSet L = decSet L' := by
  have h' := bitsOf_eq_iff.1 h
  ext x
  rw [mem_decSet, mem_decSet]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (h' c).1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (h' c).2 hc, rfl⟩

theorem bitsOf_eq_of_decSet {L L' : List ℕ} (hL : ∀ c ∈ L, c < 2187) (hL' : ∀ c ∈ L', c < 2187)
    (h : decSet L = decSet L') : bitsOf L = bitsOf L' := by
  rw [bitsOf_eq_iff]
  intro c
  constructor
  · intro hc
    have : decV c ∈ decSet L := mem_decSet.2 ⟨c, hc, rfl⟩
    rw [h, mem_decSet] at this
    obtain ⟨d, hd, hdc⟩ := this
    have := decV_injOn (hL' d hd) (hL c hc) hdc
    rw [← this]
    exact hd
  · intro hc
    have : decV c ∈ decSet L' := mem_decSet.2 ⟨c, hc, rfl⟩
    rw [← h, mem_decSet] at this
    obtain ⟨d, hd, hdc⟩ := this
    have := decV_injOn (hL d hd) (hL' c hc) hdc
    rw [← this]
    exact hd

theorem permOf_size (f : ℕ → ℕ) : (permOf f).size = 2187 := by
  simp [permOf]

theorem permOf_get (f : ℕ → ℕ) {c : ℕ} (hc : c < 2187) : (permOf f)[c]! = f c := by
  have h : c < (permOf f).size := by rw [permOf_size]; exact hc
  first
    | (simp [permOf, hc]; done)
    | (rw [getElem!_pos (permOf f) c h]; simp [permOf]; done)

theorem reflTab_get (u : ℕ) {c : ℕ} (hc : c < 2187) :
    (reflTab u)[c]! = encV (rxV (decV u) (decV c)) := by
  unfold reflTab
  exact permOf_get _ hc

theorem compTab_get (a b : Array ℕ) {c : ℕ} (hc : c < 2187) :
    (compTab a b)[c]! = a[b[c]!]! := by
  unfold compTab
  exact permOf_get _ hc

theorem compRefl_get (u w : ℕ) {c : ℕ} (hc : c < 2187) :
    (compTab (reflTab u) (reflTab w))[c]! = encV (rxV (decV u) (rxV (decV w) (decV c))) := by
  rw [compTab_get _ _ hc, reflTab_get _ hc, reflTab_get _ (encV_lt _), decV_encV]

theorem genTabs_size (T : Tables) : (genTabs T).size = T.genU.size := by
  simp [genTabs]

theorem genTabs_get (T : Tables) {k : ℕ} (hk : k < T.genU.size) {c : ℕ} (hc : c < 2187) :
    (genTabs T)[k]![c]! = encV (rxV (decV T.genU[k]!) (rxV (decV T.genW[k]!) (decV c))) := by
  have e : (genTabs T)[k]! = compTab (reflTab T.genU[k]!) (reflTab T.genW[k]!) := by
    have hk' : k < (genTabs T).size := by rw [genTabs_size]; exact hk
    first
      | (simp [genTabs, hk]; done)
      | (rw [getElem!_pos (genTabs T) k hk']; simp [genTabs]; done)
  rw [e, compRefl_get _ _ hc]

theorem hTabs_size : (hTabs ()).size = 6 := by
  simp [hTabs]

theorem hTabs_get {j : ℕ} (hj : j < 6) {c : ℕ} (hc : c < 2187) :
    (hTabs ())[j]![c]! = encV (rxV (decV 1) (rxV (decV (3 ^ (j + 1))) (decV c))) := by
  have e : (hTabs ())[j]! = compTab (reflTab 1) (reflTab (3 ^ (j + 1))) := by
    have hj' : j < (hTabs ()).size := by rw [hTabs_size]; exact hj
    first
      | (simp [hTabs, hj]; done)
      | (rw [getElem!_pos (hTabs ()) j hj']; simp [hTabs]; done)
  rw [e, compRefl_get _ _ hc]

structure TableSem (T : Tables) (G H : Array (Array ℕ)) : Prop where
  gsize : G.size = T.genU.size
  gget : ∀ k, k < T.genU.size → ∀ c, c < 2187 →
    G[k]![c]! = encV (rxV (decV T.genU[k]!) (rxV (decV T.genW[k]!) (decV c)))
  hget : ∀ j, j < 6 → ∀ c, c < 2187 →
    H[j]![c]! = encV (rxV (decV 1) (rxV (decV (3 ^ (j + 1))) (decV c)))

theorem tableSem_gen (T : Tables) : TableSem T (genTabs T) (hTabs ()) where
  gsize := genTabs_size T
  gget k hk c hc := genTabs_get T hk hc
  hget j hj c hc := hTabs_get hj hc

structure VerifyFacts (T : Tables) (G H : Array (Array ℕ)) (P : Array (List ℕ)) : Prop where
  roots_lt : ∀ c ∈ T.roots, c < 2187
  pt0 : P[0]! = T.roots
  tree : ∀ i, i < 3159 → i = 0 ∨ (T.treePar[i]! < i ∧ T.treeGen[i]! < G.size ∧
    P[i]! = (P[T.treePar[i]!]!).map fun c => G[T.treeGen[i]!]![c]!)
  genQ : ∀ k, k < T.genU.size → qV (decV T.genU[k]!) = 1 ∧ qV (decV T.genW[k]!) = 1
  q0 : qV (decV 1) = 1
  qj : ∀ j, j < 6 → qV (decV (3 ^ (j + 1))) = 1
  nodup : ∀ i j, i < 3159 → j < 3159 → bitsOf P[i]! = bitsOf P[j]! → i = j
  hfix : ∀ j, j < 6 → bitsOf (T.roots.map fun c => H[j]![c]!) = bitsOf T.roots
  cls0 : T.cls[0]! = 0
  clsne : ∀ i, i < 3159 → i = 0 ∨ T.cls[i]! ≠ 0
  clsOK : ∀ i, i < 3159 → T.cls[i]! < 4 ∧
    (T.clsPar[i]! = i → i = T.clsRoot[T.cls[i]!]!) ∧
    (T.clsPar[i]! ≠ i → T.clsPar[i]! < 3159 ∧ T.cls[T.clsPar[i]!]! = T.cls[i]! ∧
      T.clsGen[i]! < 6 ∧
      bitsOf ((P[T.clsPar[i]!]!).map fun c => H[T.clsGen[i]!]![c]!) = bitsOf P[i]!)
  anc : ∀ i, i < 3159 → T.clsPar[clsAnc T 64 i]! = clsAnc T 64 i
  count0 : classCount T 0 = 1
  count1 : classCount T 1 = 288
  count2 : classCount T 2 = 630
  count3 : classCount T 3 = 2240

structure Facts (T : Tables) (G H : Array (Array ℕ)) (P : Array (List ℕ)) : Prop
    extends TableSem T G H, VerifyFacts T G H P

theorem classOK_sound {T : Tables} {H : Array (Array ℕ)} {P : Array (List ℕ)} {i : ℕ}
    (h : classOK T H P i = true) :
    T.cls[i]! < 4 ∧ (T.clsPar[i]! = i → i = T.clsRoot[T.cls[i]!]!) ∧
      (T.clsPar[i]! ≠ i → T.clsPar[i]! < 3159 ∧ T.cls[T.clsPar[i]!]! = T.cls[i]! ∧
        T.clsGen[i]! < 6 ∧
        bitsOf ((P[T.clsPar[i]!]!).map fun c => H[T.clsGen[i]!]![c]!) = bitsOf P[i]!) := by
  unfold classOK at h
  split at h
  · rename_i hc
    have hp : T.clsPar[i]! = i := beq_iff_eq.1 hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.1, fun _ => h.2, fun hne => absurd hp hne⟩
  · rename_i hc
    have hp : T.clsPar[i]! ≠ i := fun e => hc (beq_iff_eq.2 e)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    exact ⟨h.1, fun hh => absurd hh hp, fun _ => h.2⟩

theorem verify_sound {T : Tables} {G H : Array (Array ℕ)} {P : Array (List ℕ)}
    (h : verify T G H P = true) : VerifyFacts T G H P := by
  unfold verify recurrenceOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨-, -, hr, -, hP0, htree, -, -, -, -, -, -, -, hgq, hq0, hqj, hnd, -, -, hfix, hc0, hcne,
    -, hco, hanc, hn0, hn1, hn2, hn3⟩ := h
  refine ⟨hr, hP0, htree, hgq, hq0, hqj, ?_, hfix, hc0, hcne, ?_, hanc, hn0, hn1, hn2, hn3⟩
  · have hnd' := (nodupB_iff _).1 hnd
    rw [List.nodup_map_iff_inj_on List.nodup_range] at hnd'
    intro i j hi hj hij
    exact hnd' i (List.mem_range.2 hi) j (List.mem_range.2 hj) hij
  · intro i hi
    exact classOK_sound (hco i hi)

theorem check_facts (T : Tables) (h : check T = true) :
    Facts T (genTabs T) (hTabs ()) (buildPts T (genTabs T)) :=
  { toTableSem := tableSem_gen T
    toVerifyFacts := verify_sound h }

@[expose] def rootSetOf (T : Tables) : Finset V := decSet T.roots

variable {T : Tables} {G H : Array (Array ℕ)} {P : Array (List ℕ)}

theorem decSet_map_gen (F : Facts T G H P) {k : ℕ} (hk : k < T.genU.size) {L : List ℕ}
    (hL : ∀ c ∈ L, c < 2187) :
    decSet (L.map fun c => G[k]![c]!) =
      (decSet L).image (fun x => rxV (decV T.genU[k]!) (rxV (decV T.genW[k]!) x)) := by
  ext x
  simp only [mem_decSet, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨decV c, ⟨c, hc, rfl⟩, ?_⟩
    rw [F.gget k hk c (hL c hc), decV_encV]
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨G[k]![c]!, ⟨c, hc, rfl⟩, ?_⟩
    rw [F.gget k hk c (hL c hc), decV_encV]

theorem decSet_map_h (F : Facts T G H P) {j : ℕ} (hj : j < 6) {L : List ℕ}
    (hL : ∀ c ∈ L, c < 2187) :
    decSet (L.map fun c => H[j]![c]!) =
      (decSet L).image (fun x => rxV (decV 1) (rxV (decV (3 ^ (j + 1))) x)) := by
  ext x
  simp only [mem_decSet, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨decV c, ⟨c, hc, rfl⟩, ?_⟩
    rw [F.hget j hj c (hL c hc), decV_encV]
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨H[j]![c]!, ⟨c, hc, rfl⟩, ?_⟩
    rw [F.hget j hj c (hL c hc), decV_encV]

theorem classCount_eq (T : Tables) (c : ℕ) :
    classCount T c = ((Finset.range 3159).filter fun i => T.cls[i]! = c).card := by
  have e : ((List.range 3159).filter fun i => T.cls[i]! == c).toFinset =
      (Finset.range 3159).filter fun i => T.cls[i]! = c := by
    ext i
    simp
  unfold classCount
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), e]

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
