
module

public import Certificates.Data.Kernel.C21205.Crit
public import CFSG.Certificates.Kernel.C21205.SylowSound
public import CFSG.LargeExtraspecial.AS35QCoSp6Base

public section

namespace CFSG.KC.C21205

open CFSG.LargeExtraspecial.AS35QCo CFSG.LargeExtraspecial.AS35QCo.Native CFSG.KS.PK
  CFSG.KC.Misc.Spec CFSG.Sporadic.Co2Smith CFSG.KC.Ord CFSG.KC.LQT.P

local notation "cd" x => fld x 36 0

theorem allL_true {l : List ℕ} {f : ℕ → Bool} : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | cons a l ih =>
    change andB (f a) (allL l f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem beq_false_ne {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := Nat.ne_of_beq_eq_false h

theorem ne_of_newL {v : ℕ} : ∀ {L : List ℕ}, newL v L = true → ∀ x ∈ L, v ≠ x
  | [], _, _, hx => absurd hx List.not_mem_nil
  | x :: L, h, z, hz => by
    change andB (notB (Nat.beq v x)) (newL v L) = true at h
    rw [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.mp hz with rfl | hz
    · exact beq_false_ne h.1
    · exact ne_of_newL h.2 z hz

theorem mem_of_memL {c : ℕ} : ∀ {S : List ℕ}, memL c S = true → c ∈ S
  | [], h => absurd h Bool.false_ne_true
  | x :: S, h => by
    change orB (Nat.beq c x) (memL c S) = true at h
    rw [orB_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_memL h)

theorem ne_of_xorB {a b : Bool} (h : xorB a b = true) : a ≠ b := by
  revert h
  cases a <;> cases b <;> decide

theorem sevenW_nil (y m : ℕ) (acc : List ℕ) (n : ℕ) : sevenW [] y m acc n = Nat.ble 7 n := rfl

theorem sevenW_cons (e : ℕ) (F : List ℕ) (y m : ℕ) (acc : List ℕ) (n : ℕ) :
    sevenW (e :: F) y m acc n =
      if Nat.beq (Nat.land m 1) 1 = true then
        letB (mulK (mulK (fld e 36 0) y) (fld (Nat.shiftRight e 36) 36 0)) fun v =>
          andB (newL v acc) (letB (Nat.succ n) fun n' => sevenW F y (Nat.shiftRight m 1) (v :: acc) n')
      else sevenW F y (Nat.shiftRight m 1) acc n := by
  have h : sevenW (e :: F) y m acc n = Bool.rec (motive := fun _ => Bool)
      (sevenW F y (Nat.shiftRight m 1) acc n)
      (letB (mulK (mulK (fld e 36 0) y) (fld (Nat.shiftRight e 36) 36 0)) fun v =>
        andB (newL v acc) (letB (Nat.succ n) fun n' => sevenW F y (Nat.shiftRight m 1) (v :: acc) n'))
      (Nat.beq (Nat.land m 1) 1) := rfl
  rw [h]
  cases Nat.beq (Nat.land m 1) 1 <;> rfl

theorem sevenW_spec {y : ℕ} {P : ℕ → Prop} :
    ∀ {F : List ℕ}, (∀ e ∈ F, P (mulK (mulK (fld e 36 0) y) (fld (Nat.shiftRight e 36) 36 0))) →
      ∀ (m : ℕ) (acc : List ℕ) (n : ℕ), sevenW F y m acc n = true → acc.Nodup →
        acc.length = n → (∀ v ∈ acc, P v) → ∃ l : List ℕ, l.Nodup ∧ 7 ≤ l.length ∧ ∀ v ∈ l, P v
  | [], _, m, acc, n, h, hnd, hl, hP => by
    rw [sevenW_nil] at h
    exact ⟨acc, hnd, hl ▸ Nat.le_of_ble_eq_true h, hP⟩
  | e :: F, hF, m, acc, n, h, hnd, hl, hP => by
    have hF' : ∀ e ∈ F, P (mulK (mulK (fld e 36 0) y) (fld (Nat.shiftRight e 36) 36 0)) :=
      fun e he => hF e (List.mem_cons_of_mem _ he)
    rw [sevenW_cons] at h
    split_ifs at h
    · rw [letB_eq, andB_eq, letB_eq, Bool.and_eq_true] at h
      refine sevenW_spec hF' _ _ _ h.2 (List.nodup_cons.mpr ⟨fun hv => ne_of_newL h.1 _ hv rfl, hnd⟩)
        (by rw [List.length_cons, hl]) ?_
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hF e List.mem_cons_self
      · exact hP v hv
    · exact sevenW_spec hF' _ _ _ h hnd hl hP

theorem exists_of_ncW {y : ℕ} : ∀ {W : List ℕ} {m : ℕ}, ncW W y m = true →
    ∃ e ∈ W, mulK y (Nat.shiftRight e 72) ≠ mulK (Nat.shiftRight e 72) y
  | [], _, h => absurd h Bool.false_ne_true
  | e :: W, m, h => by
    change orB (andB (Nat.beq (Nat.land m 1) 1) (letB (Nat.shiftRight e 72) fun u =>
      notB (Nat.beq (mulK y u) (mulK u y)))) (ncW W y (Nat.shiftRight m 1)) = true at h
    rw [orB_eq, andB_eq, letB_eq, notB_eq, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at h
    rcases h with ⟨-, h⟩ | h
    · exact ⟨e, List.mem_cons_self, beq_false_ne h⟩
    · obtain ⟨e', he', hne⟩ := exists_of_ncW h
      exact ⟨e', List.mem_cons_of_mem _ he', hne⟩

theorem strictC_cons (x : ℕ) (L : List ℕ) (k : ℕ → ℕ → Bool) (lo n : ℕ) :
    strictC (x :: L) k lo n = letB (fld x 36 0) fun c =>
      andB (Nat.ble lo c) (letB (Nat.succ n) fun n' => strictC L k (Nat.succ c) n') := rfl

theorem strictC_spec (k : ℕ → ℕ → Bool) : ∀ (L : List ℕ) (lo n : ℕ), strictC L k lo n = true →
    ∃ lo', lo ≤ lo' ∧ k lo' (n + L.length) = true ∧
      (L.map fun x => fld x 36 0).Pairwise (· < ·) ∧
      ∀ c ∈ L.map (fun x => fld x 36 0), lo ≤ c ∧ c < lo'
  | [], lo, n, h => ⟨lo, le_rfl, by rw [List.length_nil, Nat.add_zero]; exact h,
      List.Pairwise.nil, fun c hc => absurd hc List.not_mem_nil⟩
  | x :: L, lo, n, h => by
    rw [strictC_cons, letB_eq, andB_eq, letB_eq, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hlo, h⟩ := h
    obtain ⟨lo', hle, hk, hp, hb⟩ := strictC_spec k L _ _ h
    refine ⟨lo', by omega, ?_, ?_, ?_⟩
    · rw [List.length_cons, show n + (L.length + 1) = Nat.succ n + L.length by omega]
      exact hk
    · rw [List.map_cons, List.pairwise_cons]
      exact ⟨fun c hc => by have := (hb c hc).1; omega, hp⟩
    · intro c hc
      rw [List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨hlo, by omega⟩
      · have := hb c hc
        omega

theorem strictD_spec (N : ℕ) : ∀ (D : List (List ℕ)) (lo n : ℕ), strictD D N lo n = true →
    (D.flatten.map fun x => fld x 36 0).Pairwise (· < ·) ∧
      (∀ c ∈ D.flatten.map (fun x => fld x 36 0), lo ≤ c) ∧ n + D.flatten.length = N
  | [], lo, n, h => ⟨List.Pairwise.nil, fun c hc => absurd hc List.not_mem_nil, by
      rw [List.flatten_nil, List.length_nil, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h⟩
  | L :: D, lo, n, h => by
    change strictC L (strictD D N) lo n = true at h
    obtain ⟨lo', hle, hk, hp, hb⟩ := strictC_spec _ L lo n h
    obtain ⟨hp', hb', hn⟩ := strictD_spec N D lo' _ hk
    refine ⟨?_, ?_, ?_⟩
    · rw [List.flatten_cons, List.map_append, List.pairwise_append]
      exact ⟨hp, hp', fun a ha b hb2 => by have := (hb a ha).2; have := hb' b hb2; omega⟩
    · intro c hc
      rw [List.flatten_cons, List.map_append, List.mem_append] at hc
      rcases hc with hc | hc
      · exact (hb c hc).1
      · have := hb' c hc
        omega
    · rw [List.flatten_cons, List.length_append]
      omega

theorem orbW_cons (r x : ℕ) (O : List ℕ) (lo : ℕ) :
    orbW r (x :: O) lo = letB (fld x 36 0) fun m => letB (Nat.shiftRight x 36) fun mi =>
      letB (mulK (mulK m r) mi) fun v => andB (pairK m mi) (andB (Nat.ble lo v) (orbW r O (Nat.succ v))) :=
  rfl

theorem orbW_spec (r : ℕ) : ∀ (O : List ℕ) (lo : ℕ), orbW r O lo = true →
    (O.map fun x => mulK (mulK (fld x 36 0) r) (Nat.shiftRight x 36)).Pairwise (· < ·) ∧
      (∀ v ∈ O.map (fun x => mulK (mulK (fld x 36 0) r) (Nat.shiftRight x 36)), lo ≤ v) ∧
      ∀ x ∈ O, pairK (fld x 36 0) (Nat.shiftRight x 36) = true
  | [], _, _ => ⟨List.Pairwise.nil, fun _ hv => absurd hv List.not_mem_nil,
      fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: O, lo, h => by
    rw [orbW_cons, letB_eq, letB_eq, letB_eq, andB_eq, andB_eq, Bool.and_eq_true,
      Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hpx, hlo, h⟩ := h
    obtain ⟨hp, hb, hpr⟩ := orbW_spec r O _ h
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, List.pairwise_cons]
      exact ⟨fun c hc => by have := hb c hc; omega, hp⟩
    · intro v hv
      rw [List.map_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hlo
      · have := hb v hv
        omega
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hpx
      · exact hpr z hz

theorem scanK_nil (r : ℕ) (L : List ℕ) : scanK r [] L = true :=
  allL_true.mpr fun x _ => by rw [letB_eq]; rfl

theorem forall_mem_of_chunkAt {D : List (List ℕ)} {n : ℕ} {f : List ℕ → Bool}
    (hlen : Nat.beq D.length n = true) (h : ∀ i < n, f (chunkAt D i) = true) :
    ∀ L ∈ D, f L = true := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have e : chunkAt D i = D[i] := by
    rw [chunkAt, List.getD_eq_getElem _ _ hi]
  rw [← e]
  exact h i (Nat.eq_of_beq_eq_true hlen ▸ hi)

theorem rep_powK {c : ℕ} {g : Sp62} (hg : LargeExtraspecial.AS35QCo.Rep c g) :
    ∀ e, LargeExtraspecial.AS35QCo.Rep (powK c e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact Rep.one
  | e + 1 => by
    rw [pow_succ]
    exact rep_mulK (rep_powK hg e) hg

theorem powK_lt (c : ℕ) : ∀ e, powK c e < 2 ^ 36
  | 0 => (by decide : idc < 2 ^ 36)
  | e + 1 => mulK_lt _ _

theorem pow_sixty_comm {C : Subgroup Sp62} {y g : Sp62} (hg : g ∈ C)
    (hsmall : ((fun h : Sp62 => h * y * h⁻¹) '' (C : Set Sp62)).ncard ≤ 6) :
    g ^ 60 * y = y * g ^ 60 := by
  classical
  have hfin : ((fun h : Sp62 => h * y * h⁻¹) '' (C : Set Sp62)).Finite := Set.toFinite _
  have hT : hfin.toFinset.card ≤ 6 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hsmall
  have hmaps : ∀ i ∈ Finset.range 7, g ^ i * y * (g ^ i)⁻¹ ∈ hfin.toFinset := by
    intro i _
    rw [Set.Finite.mem_toFinset]
    exact ⟨g ^ i, C.pow_mem hg i, rfl⟩
  obtain ⟨i, hi, j, hj, hij, e⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun i : ℕ => g ^ i * y * (g ^ i)⁻¹) (by rw [Finset.card_range]; omega) hmaps
  have key : ∀ i j, i < j → j < 7 → g ^ i * y * (g ^ i)⁻¹ = g ^ j * y * (g ^ j)⁻¹ →
      g ^ 60 * y = y * g ^ 60 := by
    intro i j hij hj e
    set a := g ^ i
    set b := g ^ (j - i)
    have hji : g ^ j = a * b := by rw [← pow_add]; congr 1; omega
    rw [hji] at e
    have hyb : y = b * y * b⁻¹ := by
      calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = a⁻¹ * (a * b * y * (a * b)⁻¹) * a := by rw [e]
        _ = b * y * b⁻¹ := by group
    have hc : Commute b y := by
      calc b * y = b * y * b⁻¹ * b := by group
        _ = y * b := by rw [← hyb]
    have h1 : 1 ≤ j - i := by omega
    have h6 : j - i ≤ 6 := by omega
    obtain ⟨q, hq⟩ : (j - i) ∣ 60 := by
      generalize j - i = d at h1 h6
      interval_cases d <;> norm_num
    rw [hq, pow_mul]
    exact (hc.pow_left q).eq
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h (Finset.mem_range.mp hj) e
  · exact key j i h (Finset.mem_range.mp hi) e.symm

section Crit

variable {r nA A B : ℕ} {O F W S : List ℕ} {D : List (List ℕ)} {N : ℕ}

theorem false_of_small_of_critK (hcrit : critK r nA A B O F W D N = true)
    (hch : ∀ L ∈ D, chunkK r nA A B F W S L = true) (hsc : ∀ L ∈ D, scanK r S L = true)
    {ρ : Sp62} (hρ : LargeExtraspecial.AS35QCo.Rep r ρ)
    {y : Sp62} (hy : y ∈ Subgroup.centralizer ({ρ} : Set Sp62)) (hy1 : y ≠ 1) (hyρ : y ≠ ρ)
    (hsmall : ((fun h : Sp62 => h * y * h⁻¹) ''
      (Subgroup.centralizer ({ρ} : Set Sp62) : Set Sp62)).ncard ≤ 6)
    {h₀ : Sp62} (hh₀ : h₀ ∈ Subgroup.centralizer ({ρ} : Set Sp62))
    (hconj : h₀ * y * h₀⁻¹ = ρ * y) : False := by
  set C := Subgroup.centralizer ({ρ} : Set Sp62) with hCdef
  have hfinS := finite_sp62
  simp only [critK, andB_eq, Bool.and_eq_true] at hcrit
  obtain ⟨hO, hF, hW, hA, hB, hG, hN⟩ := hcrit
  have hN' : O.length * N = 1451520 := Nat.eq_of_beq_eq_true hN
  have memC : ∀ {c : ℕ} {g : Sp62}, LargeExtraspecial.AS35QCo.Rep c g → mulK c r = mulK r c →
      g ∈ C := by
    intro c g hg e
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact Rep.unique (e ▸ rep_mulK hg hρ) (rep_mulK hρ hg)
  have hfac : ∀ {n P : ℕ}, facK r n P = true → ∀ i < n,
      ∃ g ∈ C, LargeExtraspecial.AS35QCo.Rep (fld (fld P 72 i) 36 0) g := by
    intro n P h i hi
    simp only [facK, allN_lqt_iff, letB_eq, andB_eq, Bool.and_eq_true] at h
    obtain ⟨hp, hc⟩ := h i hi
    obtain ⟨g, hg, -⟩ := exists_rep_of_pairK hp
    exact ⟨g, memC hg (Nat.eq_of_beq_eq_true hc), hg⟩
  set E := D.flatten with hE
  have hent : ∀ x ∈ E, entryK r nA A B F W S x = true := by
    intro x hx
    obtain ⟨L, hL, hxL⟩ := List.mem_flatten.mp hx
    exact allL_true.mp (hch L hL) x hxL
  have hentC : ∀ x ∈ E, ∃ g ∈ C, LargeExtraspecial.AS35QCo.Rep (cd x) g := by
    intro x hx
    have h := hent x hx
    simp only [entryK, letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hi, hc, -⟩ := h
    obtain ⟨a, haC, ha⟩ := hfac hA _ hi
    obtain ⟨b, hbC, hb⟩ := hfac hB _ (fld_lt _ 9 0)
    exact ⟨a * b, C.mul_mem haC hbC, Nat.eq_of_beq_eq_true hc ▸ rep_mulK ha hb⟩
  obtain ⟨hpE, -, hlenE⟩ := strictD_spec N D 0 0 hG
  rw [Nat.zero_add, ← hE] at hlenE
  set T : Set Sp62 := {g | ∃ x ∈ E, LargeExtraspecial.AS35QCo.Rep (cd x) g} with hT
  have hTlen := length_le_ncard (T := T) (hpE.imp ne_of_lt)
    (fun c hc => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
      exact fld_lt _ _ _)
    (fun c hc => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨g, -, hg⟩ := hentC x hx
      exact ⟨g, ⟨x, hx, hg⟩, hg⟩)
  rw [List.length_map, hlenE] at hTlen
  obtain ⟨hpO, -, hpairO⟩ := orbW_spec r O 0 hO
  have hOlen := length_le_ncard (T := {h : Sp62 | ∃ m, h = m * ρ * m⁻¹}) (hpO.imp ne_of_lt)
    (fun c hc => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
      exact mulK_lt _ _)
    (fun c hc => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨m, hm, hmi⟩ := exists_rep_of_pairK (hpairO x hx)
      exact ⟨m * ρ * m⁻¹, ⟨m, rfl⟩, rep_mulK (rep_mulK hm hρ) hmi⟩)
  rw [List.length_map] at hOlen
  have hcard := card_centralizer_mul_ncard ρ
  rw [← hCdef] at hcard
  have hTC : T ⊆ (C : Set Sp62) := by
    rintro g ⟨x, hx, hg⟩
    obtain ⟨g', hg'C, hg'⟩ := hentC x hx
    exact Rep.unique hg' hg ▸ hg'C
  have hCN : Nat.card C ≤ N := by
    have hpos : 0 < {h : Sp62 | ∃ m, h = m * ρ * m⁻¹}.ncard := by
      rcases Nat.eq_zero_or_pos {h : Sp62 | ∃ m, h = m * ρ * m⁻¹}.ncard with h | h
      · rw [h, Nat.mul_zero] at hcard
        omega
      · exact h
    have h1 := Nat.mul_le_mul_right N hOlen
    have h2 : {h : Sp62 | ∃ m, h = m * ρ * m⁻¹}.ncard * Nat.card C ≤
        {h : Sp62 | ∃ m, h = m * ρ * m⁻¹}.ncard * N := by
      rw [Nat.mul_comm _ (Nat.card C), hcard, ← hN']
      exact h1
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hTeq : T = (C : Set Sp62) := by
    apply Set.eq_of_subset_of_ncard_le hTC _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq]
    exact hCN.trans hTlen
  have hcode : ∀ g ∈ C, ∃ x ∈ E, LargeExtraspecial.AS35QCo.Rep (cd x) g := fun g hg => by
    rw [← SetLike.mem_coe, ← hTeq] at hg
    exact hg
  obtain ⟨x, hx, hcy⟩ := hcode y hy
  have h := hent x hx
  simp only [entryK, letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, ht⟩ := h
  set c := cd x with hcdef
  have hclt : c < 2 ^ 36 := fld_lt _ _ _
  have hρy : h₀ * y = ρ * y * h₀ := by
    calc h₀ * y = h₀ * y * h₀⁻¹ * h₀ := by group
      _ = ρ * y * h₀ := by rw [hconj]
  simp only [testK, orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true] at ht
  rcases ht with ⟨-, h0⟩ | ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨-, h3⟩ | ⟨-, h4⟩
  ·
    rcases h0 with e | e
    · exact hy1 (Rep.unique (Nat.eq_of_beq_eq_true e ▸ hcy) Rep.one)
    · exact hyρ (Rep.unique (Nat.eq_of_beq_eq_true e ▸ hcy) hρ)
  ·
    set p := Nat.shiftRight x 54
    have key : ∀ {d : ℕ} {g : Sp62}, LargeExtraspecial.AS35QCo.Rep d g → d < 2 ^ 36 →
        (Nat.beq d idc = true ↔ g = 1) := by
      intro d g hd hlt
      constructor
      · intro e
        exact Rep.unique (Nat.eq_of_beq_eq_true e ▸ hd) Rep.one
      · intro e
        rw [Rep.code_eq hd (e ▸ Rep.one) hlt (by decide)]
        exact Nat.beq_refl _
    apply ne_of_xorB h1
    rw [Bool.eq_iff_iff, key (rep_powK hcy p) (powK_lt _ _),
      key (rep_powK (rep_mulK hρ hcy) p) (powK_lt _ _), ← hconj, conj_pow]
    constructor
    · intro e
      rw [e]
      group
    · intro e
      calc y ^ p = h₀⁻¹ * (h₀ * y ^ p * h₀⁻¹) * h₀ := by group
        _ = 1 := by rw [e]; group
  ·
    simp only [fK, allL_true, letB_eq, andB_eq, Bool.and_eq_true] at hF
    obtain ⟨l, hl, h7, hP⟩ := sevenW_spec (P := fun v => v < 2 ^ 36 ∧ ∃ h ∈ C,
        LargeExtraspecial.AS35QCo.Rep v (h * y * h⁻¹))
      (fun e he => by
        obtain ⟨hp, hc⟩ := hF e he
        obtain ⟨g, hg, hgi⟩ := exists_rep_of_pairK hp
        exact ⟨mulK_lt _ _, g, memC hg (Nat.eq_of_beq_eq_true hc),
          rep_mulK (rep_mulK hg hcy) hgi⟩)
      _ _ _ h2 (List.nodup_singleton _) rfl (fun v hv => by
        rw [List.mem_singleton] at hv
        subst hv
        exact ⟨hclt, 1, C.one_mem, by rw [one_mul, inv_one, mul_one]; exact hcy⟩)
    have hl7 := length_le_ncard (T := (fun h : Sp62 => h * y * h⁻¹) '' (C : Set Sp62)) hl
      (fun v hv => (hP v hv).1)
      (fun v hv => by
        obtain ⟨-, h, hhC, hv'⟩ := hP v hv
        exact ⟨_, ⟨h, hhC, rfl⟩, hv'⟩)
    omega
  ·
    have hcS := mem_of_memL h3
    obtain ⟨x', hx', hd⟩ := hcode h₀ hh₀
    obtain ⟨L, hL, hxL⟩ := List.mem_flatten.mp hx'
    have hs := allL_true.mp (hsc L hL) x' hxL
    rw [letB_eq] at hs
    have hs' := allL_true.mp hs c hcS
    rw [notB_eq, Bool.not_eq_true'] at hs'
    apply beq_false_ne hs'
    exact Rep.code_eq (rep_mulK hd hcy) (hρy ▸ rep_mulK (rep_mulK hρ hcy) hd) (mulK_lt _ _)
      (mulK_lt _ _)
  ·
    obtain ⟨e, he, hne⟩ := exists_of_ncW h4
    simp only [wK, allL_true, letB_eq, andB_eq, Bool.and_eq_true] at hW
    obtain ⟨hp, hc, hu⟩ := hW e he
    obtain ⟨g, hg, -⟩ := exists_rep_of_pairK hp
    have hgC := memC hg (Nat.eq_of_beq_eq_true hc)
    have hU : LargeExtraspecial.AS35QCo.Rep (Nat.shiftRight e 72) (g ^ 60) :=
      Nat.eq_of_beq_eq_true hu ▸ rep_powK hg 60
    apply hne
    have hcomm := pow_sixty_comm hgC hsmall
    exact Rep.code_eq (rep_mulK hcy hU) (hcomm ▸ rep_mulK hU hcy) (mulK_lt _ _) (mulK_lt _ _)

end Crit

end CFSG.KC.C21205

end
