module

public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley

@[expose] def vecIdx : List ℕ → ℕ
  | [] => 0
  | c :: t => c * 3 ^ t.length + vecIdx t

@[expose] def rootDot : List ℤ → List ℕ → ℤ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, c :: cs => a * c + rootDot as cs

theorem vecIdx_lt : ∀ v : List ℕ, (∀ x ∈ v, x < 3) → vecIdx v < 3 ^ v.length
  | [], _ => by simp [vecIdx]
  | c :: t, h => by
    have hc : c < 3 := h c (by simp)
    have ht := vecIdx_lt t (fun x hx => h x (by simp [hx]))
    simp only [vecIdx, List.length_cons, pow_succ]
    interval_cases c <;> omega

theorem eq_zero_of_vecIdx_eq_zero :
    ∀ v : List ℕ, (∀ x ∈ v, x < 3) → vecIdx v = 0 → ∀ x ∈ v, x = 0
  | [], _, _ => by simp
  | c :: t, h, h0 => by
    have hW : 0 < 3 ^ t.length := by positivity
    have hc : c = 0 := by
      by_contra hne
      have : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hne
      simp only [vecIdx] at h0
      nlinarith
    have ht : vecIdx t = 0 := by simp only [vecIdx] at h0; subst hc; simpa using h0
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hc
    · exact eq_zero_of_vecIdx_eq_zero t (fun y hy => h y (by simp [hy])) ht x hx

@[expose] def selBits (t : ℕ × ℕ × ℕ) (s : ℤ) : ℕ :=
  match (s % 3).toNat with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

@[expose] def stepBits (t : ℕ × ℕ × ℕ) (a : ℤ) (W : ℕ) (r : ℤ) : ℕ :=
  selBits t r ||| (selBits t (r - a) <<< W) ||| (selBits t (r - 2 * a) <<< (2 * W))

@[expose] def hypTriple : List ℤ → ℕ × ℕ × ℕ
  | [] => (1, 0, 0)
  | a :: rest =>
    (stepBits (hypTriple rest) a (3 ^ rest.length) 0, stepBits (hypTriple rest) a (3 ^ rest.length) 1,
      stepBits (hypTriple rest) a (3 ^ rest.length) 2)

theorem selBits_congr (t : ℕ × ℕ × ℕ) {s s' : ℤ} (h : s % 3 = s' % 3) :
    selBits t s = selBits t s' := by
  unfold selBits; rw [h]

theorem stepBits_congr (t : ℕ × ℕ × ℕ) (a : ℤ) (W : ℕ) {r r' : ℤ} (h : r % 3 = r' % 3) :
    stepBits t a W r = stepBits t a W r' := by
  have h1 : selBits t r = selBits t r' := selBits_congr t h
  have h2 : selBits t (r - a) = selBits t (r' - a) := selBits_congr t (by omega)
  have h3 : selBits t (r - 2 * a) = selBits t (r' - 2 * a) := selBits_congr t (by omega)
  unfold stepBits
  rw [h1, h2, h3]

theorem selBits_triple (t : ℕ × ℕ × ℕ) (a : ℤ) (W : ℕ) (s : ℤ) :
    selBits (stepBits t a W 0, stepBits t a W 1, stepBits t a W 2) s = stepBits t a W s := by
  have hs : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hs with h | h | h
  · simp only [selBits, h]
    exact stepBits_congr t a W (by omega)
  · simp only [selBits, h]
    exact stepBits_congr t a W (by omega)
  · simp only [selBits, h]
    exact stepBits_congr t a W (by omega)

theorem hypTriple_spec : ∀ a : List ℤ, ∀ s : ℤ,
    (∀ j, 3 ^ a.length ≤ j → Nat.testBit (selBits (hypTriple a) s) j = false) ∧
    (∀ v : List ℕ, v.length = a.length → (∀ x ∈ v, x < 3) →
      (Nat.testBit (selBits (hypTriple a) s) (vecIdx v) = true ↔ rootDot a v % 3 = s % 3))
  | [], s => by
    have h1 : selBits (hypTriple []) s = if s % 3 = 0 then 1 else 0 := by
      simp only [hypTriple, selBits]
      rcases (by omega : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2) with h | h | h <;> simp [h]
    refine ⟨fun j hj => ?_, fun v hv _ => ?_⟩
    · rw [h1]
      simp only [List.length_nil, pow_zero] at hj
      split_ifs
      · exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      · simp
    · have : v = [] := List.length_eq_zero_iff.1 (by simpa using hv)
      subst this
      rw [h1]
      by_cases h : s % 3 = 0
      · simp [h, vecIdx, rootDot]
      · simp [h, vecIdx, rootDot]
        omega
  | a :: rest, s => by
    have ih := hypTriple_spec rest
    have hWpos : 0 < 3 ^ rest.length := by positivity
    have hsel : selBits (hypTriple (a :: rest)) s =
        stepBits (hypTriple rest) a (3 ^ rest.length) s := by
      simp only [hypTriple]
      exact selBits_triple (hypTriple rest) a (3 ^ rest.length) s
    rw [hsel]
    unfold stepBits
    refine ⟨fun j hj => ?_, fun v hv hv3 => ?_⟩
    · have hj' : 3 * 3 ^ rest.length ≤ j := by
        simpa [List.length_cons, pow_succ, mul_comm] using hj
      have h1 := (ih s).1 j (by omega)
      have h2 := (ih (s - a)).1 (j - 3 ^ rest.length) (by omega)
      have h3 := (ih (s - 2 * a)).1 (j - 2 * 3 ^ rest.length) (by omega)
      simp [Nat.testBit_or, Nat.testBit_shiftLeft, h1, h2, h3]
    · cases v with
      | nil => simp at hv
      | cons c t =>
        have htl : t.length = rest.length := by simpa using hv
        have hc : c < 3 := hv3 c (by simp)
        have ht3 : ∀ x ∈ t, x < 3 := fun x hx => hv3 x (by simp [hx])
        have hI : vecIdx t < 3 ^ rest.length := htl ▸ vecIdx_lt t ht3
        have hvi : vecIdx (c :: t) = c * 3 ^ rest.length + vecIdx t := by
          simp [vecIdx, htl]
        have hrd : rootDot (a :: rest) (c :: t) = a * c + rootDot rest t := by simp [rootDot]
        rw [hvi, hrd]
        have iP := (ih s).1
        have iQ := (ih (s - a)).1
        have iR := (ih (s - 2 * a)).1
        have sP := (ih s).2 t htl ht3
        have sQ := (ih (s - a)).2 t htl ht3
        have sR := (ih (s - 2 * a)).2 t htl ht3
        interval_cases c
        · have e : (0 : ℕ) * 3 ^ rest.length + vecIdx t = vecIdx t := by simp
          rw [e]
          have hn1 : ¬ (3 ^ rest.length ≤ vecIdx t) := by omega
          have hn2 : ¬ (2 * 3 ^ rest.length ≤ vecIdx t) := by omega
          simp [Nat.testBit_or, Nat.testBit_shiftLeft, hn1, hn2, sP]
        · have e1 : 3 ^ rest.length + vecIdx t - 3 ^ rest.length = vecIdx t := by omega
          have hP : Nat.testBit (selBits (hypTriple rest) s) (3 ^ rest.length + vecIdx t) = false :=
            iP _ (by omega)
          have hn2 : ¬ (2 * 3 ^ rest.length ≤ 3 ^ rest.length + vecIdx t) := by omega
          simp [Nat.testBit_or, Nat.testBit_shiftLeft, hP, hn2, e1, sQ]
          omega
        · have hP : Nat.testBit (selBits (hypTriple rest) s) (2 * 3 ^ rest.length + vecIdx t) = false :=
            iP _ (by omega)
          have hQ : Nat.testBit (selBits (hypTriple rest) (s - a))
              (2 * 3 ^ rest.length + vecIdx t - 3 ^ rest.length) = false := iQ _ (by omega)
          have e2 : 2 * 3 ^ rest.length + vecIdx t - 2 * 3 ^ rest.length = vecIdx t := by omega
          simp [Nat.testBit_or, Nat.testBit_shiftLeft, hP, hQ, e2, sR]
          omega


@[expose] def hyperBits (a : List ℤ) : ℕ := selBits (hypTriple a) 0

theorem hyperBits_spec (a : List ℤ) {v : List ℕ} (hv : v.length = a.length)
    (hv3 : ∀ x ∈ v, x < 3) :
    Nat.testBit (hyperBits a) (vecIdx v) = true ↔ rootDot a v % 3 = 0 := by
  have := (hypTriple_spec a 0).2 v hv hv3
  simpa [hyperBits] using this

@[expose] def coverAux (full j : ℕ) : List ℕ → ℕ → Bool
  | [], acc => acc == full
  | H :: rest, acc =>
    if (if Nat.testBit H j then acc ||| H else acc) == full then true
    else coverAux full j rest (if Nat.testBit H j then acc ||| H else acc)

theorem coverAux_spec (full j : ℕ) : ∀ (Hs : List ℕ) (acc : ℕ), coverAux full j Hs acc = true →
    ∀ t, Nat.testBit full t = true →
      Nat.testBit acc t = true ∨ ∃ H ∈ Hs, Nat.testBit H j = true ∧ Nat.testBit H t = true
  | [], acc, h, t, ht => by
    left
    simp only [coverAux, beq_iff_eq] at h
    rw [h]; exact ht
  | H :: rest, acc, h, t, ht => by
    have hrel : ∀ t, Nat.testBit (if Nat.testBit H j then acc ||| H else acc) t = true →
        Nat.testBit acc t = true ∨ (Nat.testBit H j = true ∧ Nat.testBit H t = true) := by
      intro t ht
      by_cases hj : Nat.testBit H j = true
      · simp only [hj, if_true, Nat.testBit_or, Bool.or_eq_true] at ht
        rcases ht with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hj, h⟩
      · simp only [hj, if_false] at ht
        exact Or.inl ht
    by_cases hf : ((if Nat.testBit H j then acc ||| H else acc) == full) = true
    · have hq : (if Nat.testBit H j then acc ||| H else acc) = full := beq_iff_eq.1 hf
      have ht' : Nat.testBit (if Nat.testBit H j then acc ||| H else acc) t = true := by
        rw [hq]; exact ht
      rcases hrel t ht' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨H, List.mem_cons_self, h1, h2⟩
    · have h' : coverAux full j rest (if Nat.testBit H j then acc ||| H else acc) = true := by
        simpa [coverAux, hf] using h
      rcases coverAux_spec full j rest _ h' t ht with h | ⟨H', hH', h1, h2⟩
      · rcases hrel t h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨H, List.mem_cons_self, h1, h2⟩
      · exact Or.inr ⟨H', List.mem_cons_of_mem _ hH', h1, h2⟩

@[expose] def allPairsKilled (roots : List (List ℤ)) (n : ℕ) : Bool :=
  (List.range (3 ^ n)).all fun j =>
    j == 0 || coverAux (2 ^ (3 ^ n) - 1) j (roots.map hyperBits) 0

theorem allPairsKilled_sound {roots : List (List ℤ)} {n : ℕ} (hlen : ∀ a ∈ roots, a.length = n)
    (h : allPairsKilled roots n = true) {v u : List ℕ} (hv : v.length = n) (hu : u.length = n)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3) (hv0 : ∃ x ∈ v, x ≠ 0) :
    ∃ a ∈ roots, rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0 := by
  unfold allPairsKilled at h
  rw [List.all_eq_true] at h
  have hjlt : vecIdx v < 3 ^ n := hv ▸ vecIdx_lt v hv3
  have hj0 : vecIdx v ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := hv0
    exact hx0 (eq_zero_of_vecIdx_eq_zero v hv3 h0 x hx)
  have hcov := h (vecIdx v) (List.mem_range.2 hjlt)
  simp only [Bool.or_eq_true, beq_iff_eq, hj0, false_or] at hcov
  have hult : vecIdx u < 3 ^ n := hu ▸ vecIdx_lt u hu3
  have hfull : Nat.testBit (2 ^ (3 ^ n) - 1) (vecIdx u) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hult
  rcases coverAux_spec _ _ _ _ hcov _ hfull with h0 | ⟨H, hH, h1, h2⟩
  · simp at h0
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hH
    exact ⟨a, ha, (hyperBits_spec a (hv.trans (hlen a ha).symm) hv3).1 h1,
      (hyperBits_spec a (hu.trans (hlen a ha).symm) hu3).1 h2⟩


@[expose] def regKillCheck (roots : List (List ℤ)) (n c : ℕ) : Bool :=
  (List.range (3 ^ n)).all fun j =>
    j == 0 || coverAux (2 ^ (3 ^ n) - 1) j (roots.map hyperBits) 0 ||
      ((roots.map hyperBits).filter fun H => Nat.testBit H j).length == c

theorem exists_kill_of_cover {roots : List (List ℤ)} {n : ℕ} (hlen : ∀ a ∈ roots, a.length = n)
    {v u : List ℕ} (hv : v.length = n) (hu : u.length = n)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3)
    (hcov : coverAux (2 ^ (3 ^ n) - 1) (vecIdx v) (roots.map hyperBits) 0 = true) :
    ∃ a ∈ roots, rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0 := by
  have hult : vecIdx u < 3 ^ n := hu ▸ vecIdx_lt u hu3
  have hfull : Nat.testBit (2 ^ (3 ^ n) - 1) (vecIdx u) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hult
  rcases coverAux_spec _ _ _ _ hcov _ hfull with h0 | ⟨H, hH, h1, h2⟩
  · simp at h0
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hH
    exact ⟨a, ha, (hyperBits_spec a (hv.trans (hlen a ha).symm) hv3).1 h1,
      (hyperBits_spec a (hu.trans (hlen a ha).symm) hu3).1 h2⟩

theorem regKill_sound {roots : List (List ℤ)} {n c : ℕ} (hlen : ∀ a ∈ roots, a.length = n)
    (h : regKillCheck roots n c = true) {v u : List ℕ} (hv : v.length = n) (hu : u.length = n)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3) (hv0 : ∃ x ∈ v, x ≠ 0)
    (hreg : ∀ a ∈ roots, ¬ (rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0)) :
    (roots.filter fun a => rootDot a v % 3 = 0).length = c := by
  unfold regKillCheck at h
  rw [List.all_eq_true] at h
  have hjlt : vecIdx v < 3 ^ n := hv ▸ vecIdx_lt v hv3
  have hj0 : vecIdx v ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := hv0
    exact hx0 (eq_zero_of_vecIdx_eq_zero v hv3 h0 x hx)
  have hc := h (vecIdx v) (List.mem_range.2 hjlt)
  simp only [Bool.or_eq_true, beq_iff_eq, hj0, false_or] at hc
  rcases hc with hcov | hcount
  · obtain ⟨a, ha, h1, h2⟩ := exists_kill_of_cover hlen hv hu hv3 hu3 hcov
    exact absurd ⟨h1, h2⟩ (hreg a ha)
  · rw [← hcount, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun a ha => ?_
    have := hyperBits_spec a (hv.trans (hlen a ha).symm) hv3
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact this.symm


theorem rootDot_ofFn : ∀ (n : ℕ) (α : Fin n → ℤ) (κ : Fin n → ℕ),
    rootDot (List.ofFn α) (List.ofFn κ) = ∑ i, α i * (κ i : ℤ)
  | 0, α, κ => by simp [rootDot]
  | n + 1, α, κ => by
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ]
    simp only [rootDot]
    rw [rootDot_ofFn n (fun i => α i.succ) (fun i => κ i.succ)]

theorem three_dvd_sum_of_mod {n : ℕ} (α : Fin n → ℤ) (k : Fin n → ℕ)
    (h : (∑ i, α i * ((k i % 3 : ℕ) : ℤ)) % 3 = 0) : (3 : ℤ) ∣ ∑ i, α i * (k i : ℤ) := by
  have h1 : (3 : ℤ) ∣ ∑ i, α i * ((k i % 3 : ℕ) : ℤ) := Int.dvd_of_emod_eq_zero h
  have h2 : (3 : ℤ) ∣ ∑ i, α i * (k i : ℤ) - ∑ i, α i * ((k i % 3 : ℕ) : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have : (k i : ℤ) - ((k i % 3 : ℕ) : ℤ) = 3 * ((k i / 3 : ℕ) : ℤ) := by omega
    rw [← mul_sub, this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have := dvd_add h2 h1
  simpa using this

theorem exists_root_kills (τ : Tag) (roots : List (List ℤ))
    (hsub : ∀ a ∈ roots, a ∈ τ.artifactRoots) (h : allPairsKilled roots τ.rank = true)
    (k₁ k₂ : Fin τ.rank → ℕ) (hk : ∃ i, ¬ 3 ∣ k₁ i) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := by
  have hlen : ∀ a ∈ roots, a.length = τ.rank := fun a ha => length_of_mem_artifactRoots (hsub a ha)
  obtain ⟨i, hi⟩ := hk
  obtain ⟨a, ha, h1, h2⟩ := allPairsKilled_sound hlen h
    (v := List.ofFn fun i => k₁ i % 3) (u := List.ofFn fun i => k₂ i % 3)
    (by simp) (by simp)
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.mod_lt _ (by norm_num))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.mod_lt _ (by norm_num))
    ⟨k₁ i % 3, List.mem_ofFn.2 ⟨i, rfl⟩, by omega⟩
  have hal : a.length = τ.rank := hlen a ha
  set α : Fin τ.rank → ℤ := fun i => a.getD i 0 with hαdef
  have hα : List.ofFn α = a := by
    refine List.ext_getElem (by simp [hal]) fun m hm hm' => ?_
    simp [hαdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']
  refine ⟨α, isRoot_iff_mem_artifactRoots.2 (by rw [hα]; exact hsub a ha), ?_, ?_⟩
  · rw [← hα, rootDot_ofFn] at h1
    exact three_dvd_sum_of_mod α k₁ h1
  · rw [← hα, rootDot_ofFn] at h2
    exact three_dvd_sum_of_mod α k₂ h2

@[expose] def posRoots (roots : List (List ℤ)) : List (List ℤ) := roots.filter fun a => a.all (0 ≤ ·)

theorem e7_allPairsKilled : allPairsKilled (posRoots e7ArtifactRoots) 7 = true := by decide +kernel

theorem e8_allPairsKilled : allPairsKilled (posRoots e8ArtifactRoots) 8 = true := by decide +kernel

theorem f4_regKill : regKillCheck f4ArtifactRoots 4 12 = true := by decide +kernel

theorem e6_regKill : regKillCheck e6ArtifactRoots 6 18 = true := by decide +kernel

theorem e7_planeKilled (k₁ k₂ : Fin Tag.E7.rank → ℕ)
    (h : ∃ i, ¬ 3 ∣ k₁ i) :
    ∃ α : Fin Tag.E7.rank → ℤ, IsRoot .E7 α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) :=
  exists_root_kills .E7 (posRoots e7ArtifactRoots) (fun a ha => (List.mem_filter.1 ha).1)
    e7_allPairsKilled k₁ k₂ h

theorem e8_planeKilled (k₁ k₂ : Fin Tag.E8.rank → ℕ)
    (h : ∃ i, ¬ 3 ∣ k₁ i) :
    ∃ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) :=
  exists_root_kills .E8 (posRoots e8ArtifactRoots) (fun a ha => (List.mem_filter.1 ha).1)
    e8_allPairsKilled k₁ k₂ h

theorem f4_regular_threeA {v u : List ℕ} (hv : v.length = 4) (hu : u.length = 4)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3) (hv0 : ∃ x ∈ v, x ≠ 0)
    (hreg : ∀ a ∈ f4ArtifactRoots, ¬ (rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0)) :
    (f4ArtifactRoots.filter fun a => rootDot a v % 3 = 0).length = 12 :=
  regKill_sound (fun a ha => length_of_mem_artifactRoots (τ := .F4) ha) f4_regKill hv hu hv3 hu3 hv0
    hreg

theorem e6_regular_threeA {v u : List ℕ} (hv : v.length = 6) (hu : u.length = 6)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3) (hv0 : ∃ x ∈ v, x ≠ 0)
    (hreg : ∀ a ∈ e6ArtifactRoots, ¬ (rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0)) :
    (e6ArtifactRoots.filter fun a => rootDot a v % 3 = 0).length = 18 :=
  regKill_sound (fun a ha => length_of_mem_artifactRoots (τ := .E6) ha) e6_regKill hv hu hv3 hu3 hv0
    hreg

theorem f4_hasRegular : ∃ v u : List ℕ, v.length = 4 ∧ u.length = 4 ∧ (∀ x ∈ v, x < 3) ∧
    (∀ x ∈ u, x < 3) ∧ (∃ x ∈ v, x ≠ 0) ∧
    ∀ a ∈ f4ArtifactRoots, ¬ (rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0) :=
  ⟨[0, 0, 1, 0], [1, 1, 0, 1], rfl, rfl, by decide, by decide, ⟨1, by simp, by decide⟩, by decide +kernel⟩

end CFSG.LieType.SeitzGeneration.ExcHighThree
