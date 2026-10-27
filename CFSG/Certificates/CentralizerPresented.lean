module

public import CFSG.Certificates.CentralizerFinite
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commute_of_comm_eq_one {x v : G} (h : x⁻¹ * v⁻¹ * x * v = 1) : Commute x v := by
  have : v⁻¹ * x * v = x := by
    have := congrArg (x * ·) h
    simpa [mul_assoc] using this
  calc x * v = v * (v⁻¹ * x * v) := by group
    _ = v * x := by rw [this]

theorem commute_pow_comm_of_even {x v : G} (hx : x ^ 2 = 1) {j : ℕ}
    (h : (x⁻¹ * v⁻¹ * x * v) ^ (2 * j) = 1) : Commute x ((x⁻¹ * v⁻¹ * x * v) ^ j) := by
  have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, hx]
  set c := x⁻¹ * v⁻¹ * x * v
  have hc : x * c * x⁻¹ = c⁻¹ := by
    simp only [c, mul_inv_rev, inv_inv]
    rw [hxi]
    have hx2 : x * x = 1 := by rw [← sq, hx]
    calc x * (x * v⁻¹ * x * v) * x = (x * x) * v⁻¹ * x * v * x := by group
      _ = v⁻¹ * x * v * x := by rw [hx2, one_mul]
      _ = v⁻¹ * (x * (v * x)) := by group
  have hcj : x * c ^ j * x⁻¹ = (c ^ j)⁻¹ := by
    rw [← conj_pow, hc, inv_pow]
  have hinv : (c ^ j)⁻¹ = c ^ j := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, h]
  have := hcj.trans hinv
  calc x * c ^ j = x * c ^ j * x⁻¹ * x := by group
    _ = c ^ j * x := by rw [this]

theorem commute_pow_comm_inv_of_even {x v : G} (hx : x ^ 2 = 1) {j : ℕ}
    (h : (x⁻¹ * v⁻¹ * x * v) ^ (2 * j) = 1) : Commute x ((x⁻¹ * v * x * v⁻¹) ^ j) := by
  have hconj : x⁻¹ * v * x * v⁻¹ = v * (x⁻¹ * v⁻¹ * x * v)⁻¹ * v⁻¹ := by group
  have h' : (x⁻¹ * (v⁻¹)⁻¹ * x * v⁻¹) ^ (2 * j) = 1 := by
    rw [inv_inv, hconj, conj_pow, inv_pow, h, inv_one, mul_one, mul_inv_cancel]
  simpa only [inv_inv] using commute_pow_comm_of_even hx h'

theorem commute_mul_pow_comm_of_odd {x v : G} (hx : x ^ 2 = 1) {j : ℕ}
    (h : (x⁻¹ * v⁻¹ * x * v) ^ (2 * j + 1) = 1) : Commute x (v * (x⁻¹ * v⁻¹ * x * v) ^ j) := by
  have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, hx]
  have hx2 : x * x = 1 := by rw [← sq, hx]
  set c := x⁻¹ * v⁻¹ * x * v
  have hc : x * c * x⁻¹ = c⁻¹ := by
    simp only [c, mul_inv_rev, inv_inv]
    rw [hxi]
    calc x * (x * v⁻¹ * x * v) * x = (x * x) * v⁻¹ * x * v * x := by group
      _ = v⁻¹ * (x * (v * x)) := by rw [hx2, one_mul]; group
  have key : ∀ n : ℕ, x * c ^ n = (c ^ n)⁻¹ * x := by
    intro n
    have : x * c ^ n * x⁻¹ = (c ^ n)⁻¹ := by rw [← conj_pow, hc, inv_pow]
    calc x * c ^ n = x * c ^ n * x⁻¹ * x := by group
      _ = (c ^ n)⁻¹ * x := by rw [this]
  have ht : v⁻¹ * x * v = x * c := by
    simp only [c]; rw [hxi]
    calc v⁻¹ * x * v = (x * x) * v⁻¹ * x * v := by rw [hx2, one_mul]
      _ = x * (x * v⁻¹ * x * v) := by group
  have hconj : (v * c ^ j)⁻¹ * x * (v * c ^ j) = x := by
    calc (v * c ^ j)⁻¹ * x * (v * c ^ j) = (c ^ j)⁻¹ * (v⁻¹ * x * v) * c ^ j := by group
      _ = (c ^ j)⁻¹ * (x * c ^ (j + 1)) := by rw [ht, pow_succ']; group
      _ = (c ^ j)⁻¹ * ((c ^ (j + 1))⁻¹ * x) := by rw [key]
      _ = (c ^ (2 * j + 1))⁻¹ * x := by
        rw [← mul_assoc, ← mul_inv_rev, ← pow_add]; congr 3; ring
      _ = x := by rw [h, inv_one, one_mul]
  calc x * (v * c ^ j) = (v * c ^ j) * ((v * c ^ j)⁻¹ * x * (v * c ^ j)) := by group
    _ = (v * c ^ j) * x := by rw [hconj]

theorem commute_inv_mul_pow_comm_inv_of_odd {x v : G} (hx : x ^ 2 = 1) {j : ℕ}
    (h : (x⁻¹ * v⁻¹ * x * v) ^ (2 * j + 1) = 1) :
    Commute x (v⁻¹ * (x⁻¹ * v * x * v⁻¹) ^ j) := by
  have hconj : x⁻¹ * v * x * v⁻¹ = v * (x⁻¹ * v⁻¹ * x * v)⁻¹ * v⁻¹ := by group
  have h' : (x⁻¹ * (v⁻¹)⁻¹ * x * v⁻¹) ^ (2 * j + 1) = 1 := by
    rw [inv_inv, hconj, conj_pow, inv_pow, h, inv_one, mul_one, mul_inv_cancel]
  simpa only [inv_inv] using commute_mul_pow_comm_of_odd hx h'

@[expose] def invC (w : List ℕ) : List ℕ := w.reverse.map invCode

@[expose] def commC (X : ℕ) (v : List ℕ) : List ℕ := [X + 1] ++ invC v ++ [X] ++ v

@[expose] def centOf (X : ℕ) (sq : Bool) (r : List ℕ) (k : ℕ) : List (List ℕ) :=
  if k = 0 then [] else
  let v := (r.take (r.length / k)).drop ((r.take (r.length / k)).length / 2 + 1)
  if r = (List.replicate k (commC X v)).flatten then
    if k = 1 then [v]
    else if sq then
      if k % 2 = 0 then [(List.replicate (k / 2) (commC X v)).flatten,
          (List.replicate (k / 2) (commC X (invC v))).flatten]
      else [v ++ (List.replicate (k / 2) (commC X v)).flatten,
          invC v ++ (List.replicate (k / 2) (commC X (invC v))).flatten]
    else []
  else []

@[expose] def centWords (X : ℕ) (rels : List (List ℕ)) : List (List ℕ) :=
  [[X]] ++ rels.flatMap fun r =>
    (List.range (r.length + 1)).flatMap (centOf X (rels.contains [X, X]) r)

@[expose] def relWords (rels : List (List ℕ)) : List (List ℕ) :=
  rels.flatMap fun r => rotations r ++ rotations (invC r)

@[expose] def centSq (X : ℕ) (rels : List (List ℕ)) (r : List ℕ) : List (List ℕ) :=
  let w := (r.drop 1).take ((r.length - 2) / 2)
  if r = [X] ++ w ++ [X] ++ w ∧ rels.contains [X, X] ∧ rels.contains (w ++ w) then [w] else []

@[expose] def centWordsR (X : ℕ) (rels : List (List ℕ)) : List (List ℕ) :=
  dedup ([[X]] ++ (relWords rels).flatMap fun r =>
    (List.range (r.length + 1)).flatMap (centOf X (rels.contains [X, X]) r) ++ centSq X rels r)

section Presented

variable {m : ℕ} {rels : Set (FreeGroup (Fin m))}

theorem invCode_invCode (c : ℕ) : invCode (invCode c) = c := by
  unfold invCode
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have hb : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
    have hb' : Nat.beq (Nat.mod (Nat.succ c) 2) 0 = false := by
      cases hh : Nat.beq (Nat.mod (Nat.succ c) 2) 0
      · rfl
      · have : (c + 1) % 2 = 0 := Nat.eq_of_beq_eq_true hh
        omega
    rw [hb, Bool.cond_true, hb', Bool.cond_false]; rfl
  · have hb : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hh : Nat.beq (Nat.mod c 2) 0
      · rfl
      · have : c % 2 = 0 := Nat.eq_of_beq_eq_true hh
        omega
    have hb' : Nat.beq (Nat.mod (Nat.pred c) 2) 0 = true := by
      rw [Nat.beq_eq]; show (c - 1) % 2 = 0; omega
    rw [hb, Bool.cond_false, hb', Bool.cond_true]
    show c - 1 + 1 = c
    omega

theorem invC_invC (w : List ℕ) : invC (invC w) = w := by
  simp [invC, List.map_reverse, List.map_map, Function.comp_def, invCode_invCode]

theorem evalWord_invC {w : List ℕ} (hw : ∀ c ∈ w, c < 2 * m) :
    evalWord (presLetter rels) (invC w) = (evalWord (presLetter rels) w)⁻¹ := by
  have := evalWord_invWord (gen := presLetter rels) (inv := invArr m) (w := w)
    (fun y hy => by rw [invArr_getD (hw y hy)]; exact presLetter_invCode rels (hw y hy))
  have h2 : invWord (invArr m) w = invC w := by
    simp only [invWord, invC]
    apply List.map_congr_left
    intro y hy
    exact invArr_getD (hw y (List.mem_reverse.mp hy))
  rwa [h2] at this

theorem evalWord_commC {i : ℕ} (hi : i < m) {v : List ℕ} (hv : ∀ c ∈ v, c < 2 * m) :
    evalWord (presLetter rels) (commC (2 * i) v) =
      (presLetter rels (2 * i))⁻¹ * (evalWord (presLetter rels) v)⁻¹ *
        presLetter rels (2 * i) * evalWord (presLetter rels) v := by
  have hX1 : presLetter rels (2 * i + 1) = (presLetter rels (2 * i))⁻¹ := by
    have := presLetter_invCode rels (c := 2 * i) (by omega)
    rwa [show invCode (2 * i) = 2 * i + 1 by
      unfold invCode
      rw [show Nat.beq (Nat.mod (2 * i) 2) 0 = true by rw [Nat.beq_eq]; show 2 * i % 2 = 0; omega]
      rfl] at this
  simp only [commC, evalWord_append', evalWord_cons, evalWord_nil, mul_one, hX1,
    evalWord_invC hv, mul_assoc]

theorem evalWord_codes_eq_one {ws : List (List (Fin m × Bool))} {r : List ℕ}
    (hr : r ∈ codes ws) :
    evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1 := by
  simp only [codes, List.mem_map] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  rw [evalWord_presLetter]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)

theorem commute_of_mem_centOf {ws : List (List (Fin m × Bool))} {i : ℕ} (hi : i < m)
    {r : List ℕ} (hl : ∀ c ∈ r, c < 2 * m)
    (hr1 : evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1)
    {k : ℕ} {w : List ℕ} (hwk : w ∈ centOf (2 * i) ((codes ws).contains [2 * i, 2 * i]) r k) :
    Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) w) := by
  set gen := presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  unfold centOf at hwk
  split at hwk
  · simp at hwk
  · rename_i hk0
    dsimp only at hwk
    set v := (r.take (r.length / k)).drop ((r.take (r.length / k)).length / 2 + 1)
    have hv : ∀ c ∈ v, c < 2 * m := fun c hc =>
      hl c (List.mem_of_mem_take (List.mem_of_mem_drop hc))
    have hvi : ∀ c ∈ invC v, c < 2 * m := by
      intro c hc
      simp only [invC, List.mem_map, List.mem_reverse] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      exact invCode_lt (hv d hd)
    split at hwk
    · rename_i hreq
      have hpow : ((gen (2 * i))⁻¹ * (evalWord gen v)⁻¹ * gen (2 * i) * evalWord gen v) ^ k =
          1 := by
        rw [← evalWord_commC hi hv, ← evalWord_flatten_replicate, ← hreq, hr1]
      split at hwk
      · rename_i hk1
        simp only [List.mem_singleton] at hwk
        subst hwk hk1
        exact commute_of_comm_eq_one (by simpa using hpow)
      · split at hwk
        · rename_i hk1 hsq
          have hx2 : gen (2 * i) ^ 2 = 1 := by
            have hm : [2 * i, 2 * i] ∈ codes ws := by simpa using hsq
            have := evalWord_codes_eq_one hm
            simpa [evalWord, sq] using this
          split at hwk
          · rename_i hev
            have hk2 : k = 2 * (k / 2) := by omega
            rw [hk2] at hpow
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwk
            rcases hwk with rfl | rfl
            · rw [evalWord_flatten_replicate, evalWord_commC hi hv]
              exact commute_pow_comm_of_even hx2 hpow
            · rw [evalWord_flatten_replicate, evalWord_commC hi hvi, evalWord_invC hv, inv_inv]
              exact commute_pow_comm_inv_of_even hx2 hpow
          · rename_i hev
            have hk2 : k = 2 * (k / 2) + 1 := by omega
            rw [hk2] at hpow
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwk
            rcases hwk with rfl | rfl
            · rw [evalWord_append', evalWord_flatten_replicate, evalWord_commC hi hv]
              exact commute_mul_pow_comm_of_odd hx2 hpow
            · rw [evalWord_append', evalWord_flatten_replicate, evalWord_commC hi hvi,
                evalWord_invC hv, inv_inv]
              exact commute_inv_mul_pow_comm_inv_of_odd hx2 hpow
        · simp at hwk
    · simp at hwk

theorem commute_of_mem_centWords {ws : List (List (Fin m × Bool))} {i : ℕ} (hi : i < m)
    {w : List ℕ} (hw : w ∈ centWords (2 * i) (codes ws)) :
    Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) w) := by
  simp only [centWords, List.mem_append, List.mem_singleton, List.mem_flatMap,
    List.mem_range] at hw
  rcases hw with rfl | ⟨r, hr, k, -, hwk⟩
  · simp only [evalWord_cons, evalWord_nil, mul_one]; exact Commute.refl _
  · exact commute_of_mem_centOf hi (letters_codes hr) (evalWord_codes_eq_one hr) hwk

theorem mem_relWords {ws : List (List (Fin m × Bool))} {r : List ℕ}
    (hr : r ∈ relWords (codes ws)) : (∀ c ∈ r, c < 2 * m) ∧
      evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1 := by
  simp only [relWords, List.mem_flatMap, List.mem_append] at hr
  obtain ⟨r₀, hr₀, hr⟩ := hr
  have hl := letters_codes hr₀
  have h1 := evalWord_codes_eq_one hr₀
  have hli : ∀ c ∈ invC r₀, c < 2 * m := by
    intro c hc
    simp only [invC, List.mem_map, List.mem_reverse] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact invCode_lt (hl d hd)
  rcases hr with hr | hr
  · exact ⟨letters_rotation hr hl, evalWord_rotation hr h1⟩
  · exact ⟨letters_rotation hr hli, evalWord_rotation hr (by rw [evalWord_invC hl, h1, inv_one])⟩

theorem commute_of_mul_self {x w : G} (hx : x * x = 1) (hw : w * w = 1)
    (h : x * w * x * w = 1) : Commute x w := by
  have hx' : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx).symm
  have hw' : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw).symm
  have h2 : (x * w) * (x * w) = 1 := by rw [← h]; simp only [mul_assoc]
  have h3 := eq_inv_of_mul_eq_one_left h2
  rwa [mul_inv_rev, hx', hw'] at h3

theorem commute_of_mem_centSq {ws : List (List (Fin m × Bool))} {i : ℕ} {r w : List ℕ}
    (hr1 : evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1)
    (hw : w ∈ centSq (2 * i) (codes ws) r) :
    Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) w) := by
  set gen := presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  dsimp only [centSq] at hw
  split at hw
  · rename_i hc
    obtain ⟨hr, hsq, hww⟩ := hc
    simp only [List.mem_singleton] at hw
    subst hw
    have hx : gen (2 * i) * gen (2 * i) = 1 := by
      have hm : [2 * i, 2 * i] ∈ codes ws := by simpa using hsq
      simpa [evalWord] using evalWord_codes_eq_one hm
    have hm2 : (r.drop 1).take ((r.length - 2) / 2) ++ (r.drop 1).take ((r.length - 2) / 2) ∈
        codes ws := by simpa using hww
    have hw2 := evalWord_codes_eq_one hm2
    rw [evalWord_append'] at hw2
    rw [hr] at hr1
    simp only [evalWord_append', evalWord_cons, evalWord_nil, mul_one] at hr1
    exact commute_of_mul_self hx hw2 (by simpa only [mul_assoc] using hr1)
  · simp at hw

theorem commute_of_mem_centWordsR {ws : List (List (Fin m × Bool))} {i : ℕ} (hi : i < m)
    {w : List ℕ} (hw : w ∈ centWordsR (2 * i) (codes ws)) :
    Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) w) := by
  have hw' := mem_dedup hw
  simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range] at hw'
  rcases hw' with rfl | ⟨r, hr, hwr⟩
  · simp only [evalWord_cons, evalWord_nil, mul_one]; exact Commute.refl _
  · obtain ⟨hl, hr1⟩ := mem_relWords hr
    rcases hwr with ⟨k, -, hwk⟩ | hwk
    · exact commute_of_mem_centOf hi hl hr1 hwk
    · exact commute_of_mem_centSq hr1 hwk

theorem lift_mk_eq {ws : List (List (Fin m × Bool))} {K : Type*} [Group K] (φ : PG m ws →* K)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i => φ (PresentedGroup.of i)) (FreeGroup.mk w) =
      φ (PresentedGroup.mk _ (FreeGroup.mk w)) := by
  have : FreeGroup.lift (fun i => φ (PresentedGroup.of i)) =
      φ.comp (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]; rfl

theorem eq_top_of_card_le_one {ws us : List (List (Fin m × Bool))} (N : Subgroup (PG m ws))
    [N.Normal]
    (hus : ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) ∈ N)
    (hfin : Finite (PG m (ws ++ us))) (hcard : Nat.card (PG m (ws ++ us)) ≤ 1) : N = ⊤ := by
  set Q := PG m ws ⧸ N
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk},
      FreeGroup.lift (fun i => (QuotientGroup.mk' N) (PresentedGroup.of i)) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_append] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_mk_eq]
    rcases hw with hw | hw
    · rw [PresentedGroup.one_of_mem (List.mem_map_of_mem hw), map_one]
    · exact (QuotientGroup.eq_one_iff _).mpr (hus w hw)
  set ψ := PresentedGroup.toGroup hrel
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hg : g ∈ (⊤ : Subgroup (PG m ws)) := Subgroup.mem_top g
      rw [← PresentedGroup.closure_range_of] at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨PresentedGroup.of i, by simp [ψ]⟩
      | one => exact ⟨1, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
      | inv x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩
  have hsub : Subsingleton (PG m (ws ++ us)) := by
    rw [← Finite.card_le_one_iff_subsingleton]; exact hcard
  have hQ : Subsingleton Q := hsurj.subsingleton
  rw [eq_top_iff]
  intro g _
  have := Subsingleton.elim (QuotientGroup.mk g : Q) 1
  exact (QuotientGroup.eq_one_iff g).mp this

@[expose] def commWords (m : ℕ) : List (List (Fin m × Bool)) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange m).map fun j => [(i, false), (j, false), (i, true), (j, true)]

@[expose] def genWord (m i : ℕ) : List (Fin m × Bool) :=
  ((List.finRange m).filter fun j => j.val = i).map fun j => (j, true)

theorem mk_genWord_mem {ws : List (List (Fin m × Bool))} {i : ℕ} (hi : i < m) :
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk (genWord m i))
      ∈ Subgroup.closure {(PresentedGroup.of ⟨i, hi⟩ : PG m ws)} := by
  have hl : ∀ l ∈ genWord m i, l = (⟨i, hi⟩, true) := by
    intro l hl
    simp only [genWord, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    exact Prod.ext (Fin.ext hj) rfl
  generalize genWord m i = w at hl
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    rw [hl l (by simp), show FreeGroup.mk ((⟨i, hi⟩, true) :: w) =
      FreeGroup.of ⟨i, hi⟩ * FreeGroup.mk w from rfl, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure rfl)
      (ih fun l' hl' => hl l' (List.mem_cons_of_mem _ hl'))

@[expose] def centCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (i cap n cap₂ cap₃ : ℕ) : Bool :=
  decide (i < m) &&
  (centWords (2 * i) (codes ws)).all (fun s => s.all fun c => decide (c < 2 * m)) &&
  checkHLT (mkParams (2 * m) (invArr m) (codes ws) (centWords (2 * i) (codes ws))) cap n &&
  check (presParams (ws ++ [genWord m i]) []) cap₂ 1 &&
  check (presParams (ws ++ commWords m) []) cap₃ 1

theorem presLetter_two_mul {rels : Set (FreeGroup (Fin m))} {i : ℕ} (hi : i < m) :
    presLetter rels (2 * i) = PresentedGroup.of ⟨i, hi⟩ := by
  have := presLetter_letterCode rels (⟨i, hi⟩, true)
  simp only [letterCode, ↓reduceIte, add_zero] at this
  rw [this]; rfl

theorem finite_of_centralizingWords (ws : List (List (Fin m × Bool))) {i : ℕ} (hi : i < m)
    (cw : List (List ℕ))
    (hcw : ∀ s ∈ cw, Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) s))
    (hlet : ∀ s ∈ cw, ∀ c ∈ s, c < 2 * m) {cap n cap₂ cap₃ : ℕ}
    (h1 : checkHLT (mkParams (2 * m) (invArr m) (codes ws) cw) cap n = true)
    (h2 : check (presParams (ws ++ [genWord m i]) []) cap₂ 1 = true)
    (h3 : check (presParams (ws ++ commWords m) []) cap₃ 1 = true) : Finite (PG m ws) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set gen := presLetter rels
  set x : PG m ws := PresentedGroup.of ⟨i, hi⟩
  have hx : gen (2 * i) = x := presLetter_two_mul hi
  set H : Subgroup (PG m ws) := Subgroup.closure {g | ∃ s ∈ cw, g = evalWord gen s}
  have hH : H ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have := hcw s hs
    rw [hx] at this
    exact this.eq.symm
  have hg := goodParams ws [] H (by simp)
  have hgood : Good gen H (mkParams (2 * m) (invArr m) (codes ws) cw) := by
    refine ⟨hg.inv_lt, hg.gen_inv, ?_, ?_, ?_⟩
    · intro x' p hp
      exact hg.scans x' p (by simpa [presParams, mkParams] using hp)
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_subs hp
      exact ⟨hp1, hlet _ hp2, Subgroup.subset_closure ⟨_, hp2, rfl⟩⟩
    · intro p hp
      exact hg.rels p (by simpa [presParams, mkParams] using hp)
  obtain ⟨hfi, -⟩ := index_le_of_checkHLT hgood (by
    have := closure_presLetter rels
    simpa [mkParams] using this) h1
  obtain ⟨f2, c2⟩ := card_le_of_check_trivial (ws ++ [genWord m i]) h2
  have hN : Subgroup.normalClosure {x} = ⊤ := by
    apply eq_top_of_card_le_one (us := [genWord m i]) _ _ f2 c2
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact Subgroup.closure_le_normalClosure (mk_genWord_mem hi)
  obtain ⟨f3, c3⟩ := card_le_of_check_trivial (ws ++ commWords m) h3
  have hP : commutator (PG m ws) = ⊤ := by
    apply eq_top_of_card_le_one (us := commWords m) _ _ f3 c3
    intro u hu
    simp only [commWords, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at hu
    obtain ⟨a, b, rfl⟩ := hu
    have : PresentedGroup.mk rels (FreeGroup.mk [(a, false), (b, false), (a, true), (b, true)]) =
        ⁅(PresentedGroup.of a : PG m ws)⁻¹, (PresentedGroup.of b)⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv]
      rfl
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact finite_of_centralizer_finiteIndex x H hH hN hP

theorem finite_of_centCheck (ws : List (List (Fin m × Bool))) {i cap n cap₂ cap₃ : ℕ}
    (h : centCheck ws i cap n cap₂ cap₃ = true) : Finite (PG m ws) := by
  unfold centCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hi, hlet⟩, h1⟩, h2⟩, h3⟩ := h
  exact finite_of_centralizingWords ws hi _ (fun s hs => commute_of_mem_centWords hi hs) hlet h1
    h2 h3

@[expose] def centCheckR {m : ℕ} (ws : List (List (Fin m × Bool))) (i cap n cap₂ cap₃ : ℕ) : Bool :=
  decide (i < m) &&
  (centWordsR (2 * i) (codes ws)).all (fun s => s.all fun c => decide (c < 2 * m)) &&
  checkHLT (mkParams (2 * m) (invArr m) (codes ws) (centWordsR (2 * i) (codes ws))) cap n &&
  check (presParams (ws ++ [genWord m i]) []) cap₂ 1 &&
  check (presParams (ws ++ commWords m) []) cap₃ 1

theorem finite_of_centCheckR (ws : List (List (Fin m × Bool))) {i cap n cap₂ cap₃ : ℕ}
    (h : centCheckR ws i cap n cap₂ cap₃ = true) : Finite (PG m ws) := by
  unfold centCheckR at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hi, hlet⟩, h1⟩, h2⟩, h3⟩ := h
  exact finite_of_centralizingWords ws hi _ (fun s hs => commute_of_mem_centWordsR hi hs) hlet h1
    h2 h3

end Presented

end CFSG.CosetTable
