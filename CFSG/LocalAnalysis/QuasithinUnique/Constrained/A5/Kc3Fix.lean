module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cert

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def parseNats (s : String) : List ℕ :=
  (s.splitOn " ").filterMap fun t => if t.isEmpty then none else some t.toNat!

@[expose] def pairUp : List ℕ → List (ℕ × ℕ)
  | p :: s :: rest => (p, s) :: pairUp rest
  | _ => []

section Tree

variable {R : Type} [Mul R] [One R]

@[expose] def treeReps (gens : List R) (rT : List (ℕ × ℕ)) : Array R :=
  rT.foldl (fun acc ps => acc.push (gens.getD ps.2 1 * acc.getD ps.1 1)) #[1]

theorem foldl_mem {P : R → Prop} (gens : List R) (hg : ∀ s, P (gens.getD s 1)) (hone : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (rT : List (ℕ × ℕ)) :
    ∀ (acc : Array R), (∀ r ∈ acc, P r) →
      ∀ r ∈ rT.foldl (fun acc ps => acc.push (gens.getD ps.2 1 * acc.getD ps.1 1)) acc, P r := by
  induction rT with
  | nil => intro acc hacc; exact hacc
  | cons ps rT ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    intro r hr
    rw [Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact hacc r hr
    · refine hmul _ _ (hg _) ?_
      have : acc.getD ps.1 1 ∈ acc ∨ acc.getD ps.1 1 = 1 := by
        unfold Array.getD
        split
        · left; exact Array.getElem_mem _
        · right; rfl
      rcases this with h | h
      · exact hacc _ h
      · rw [h]; exact hone

theorem treeReps_mem {P : R → Prop} (gens : List R) (hg : ∀ s, P (gens.getD s 1)) (hone : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (rT : List (ℕ × ℕ)) :
    ∀ r ∈ treeReps gens rT, P r :=
  foldl_mem gens hg hone hmul rT #[1] (by intro r hr; simp at hr; subst hr; exact hone)

end Tree

section Fix

variable {n : ℕ}

@[expose] def fixPts (Es : Std.HashSet (RN n)) : List (Fin n) :=
  (List.finRange n).filter fun p => Es.toList.all fun e => e.val[p] == p

@[expose] def imgMask (T : List (Fin n)) (r : RN n) : ℕ :=
  ((T.map fun p => r.val[p]).toFinset).sum fun q => 2 ^ q.val

@[expose] def ECert.orbitCheckT (gR : List (RN n)) (c : ECert) : Bool :=
  decide (((treeReps gR (pairUp c.rT)).toList.map (imgMask (fixPts (c.Es gR)))).Nodup)

@[expose] def ECert.coreCheckT (gR : List (RN n)) (c : ECert) (kOrd : ℕ) : Bool :=
  c.eCheck gR && c.nCheck gR && c.orbitCheckT gR &&
    (kOrd == (treeReps gR (pairUp c.rT)).size * c.nOrd)

variable {G : Type} [Group G] {enc : G → RN n}

@[expose] def act (enc : G → RN n) (g : G) (p : Fin n) : Fin n := (enc g).val[p]

theorem act_mul (h : IsEnc enc) (g g' : G) (p : Fin n) :
    act enc (g * g') p = act enc g (act enc g' p) := by
  unfold act
  rw [h.map_mul, RN.mul_get]

omit [Group G] in
theorem imgMask_enc (T : List (Fin n)) (g : G) :
    imgMask T (enc g) = ((T.map (act enc g)).toFinset).sum fun q => 2 ^ q.val := rfl

theorem mem_fixPts_iff (Es : Std.HashSet (RN n)) (E : Subgroup G)
    (hmemE : ∀ x : G, x ∈ E ↔ enc x ∈ Es) (hsurj : ∀ ε ∈ Es, ∃ x ∈ E, enc x = ε) (p : Fin n) :
    p ∈ fixPts Es ↔ ∀ x ∈ E, act enc x p = p := by
  unfold fixPts
  simp only [List.mem_filter, List.mem_finRange, true_and, List.all_eq_true, beq_iff_eq,
    Std.HashSet.mem_toList]
  constructor
  · intro hp x hx
    exact hp (enc x) ((hmemE x).1 hx)
  · intro hp ε hε
    obtain ⟨x, hx, rfl⟩ := hsurj ε hε
    exact hp x hx

theorem norm_fix (h : IsEnc enc) (E : Subgroup G) {p : Fin n} (hp : ∀ x ∈ E, act enc x p = p)
    {ν : G} (hν : ν ∈ Subgroup.normalizer (E : Set G)) :
    ∀ x ∈ E, act enc x (act enc ν p) = act enc ν p := by
  intro x hx
  have hx' : ν⁻¹ * x * ν ∈ E := ((Subgroup.mem_normalizer_iff''.1 hν) x).1 hx
  calc act enc x (act enc ν p) = act enc (x * ν) p := (act_mul h x ν p).symm
    _ = act enc (ν * (ν⁻¹ * x * ν)) p := by congr 1; group
    _ = act enc ν (act enc (ν⁻¹ * x * ν) p) := act_mul h _ _ p
    _ = act enc ν p := by rw [hp _ hx']

theorem img_eq (h : IsEnc enc) (E : Subgroup G) (T : List (Fin n))
    (hT : ∀ p, p ∈ T ↔ ∀ x ∈ E, act enc x p = p) {g₁ g₂ : G}
    (hν : g₁⁻¹ * g₂ ∈ Subgroup.normalizer (E : Set G)) :
    (T.map (act enc g₂)).toFinset = (T.map (act enc g₁)).toFinset := by
  have key : ∀ {g₁ g₂ : G}, g₁⁻¹ * g₂ ∈ Subgroup.normalizer (E : Set G) →
      ∀ q ∈ (T.map (act enc g₂)).toFinset, q ∈ (T.map (act enc g₁)).toFinset := by
    intro g₁ g₂ hν q hq
    simp only [List.mem_toFinset, List.mem_map] at hq ⊢
    obtain ⟨p, hp, rfl⟩ := hq
    refine ⟨act enc (g₁⁻¹ * g₂) p, (hT _).2 (norm_fix h E ((hT p).1 hp) hν), ?_⟩
    rw [← act_mul h]
    congr 1
    group
  ext q
  constructor
  · exact key hν q
  · exact key (by simpa using inv_mem hν) q

variable [Finite G]

theorem orbit_bound_tree (h : IsEnc enc) (a b : G) (c : ECert) (E : Subgroup G)
    (hmemE : ∀ x : G, x ∈ E ↔ enc x ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc))
    (hmemEs : ∀ ε ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc), ∃ x ∈ E, enc x = ε)
    (hO : c.orbitCheckT ([a, b, a⁻¹, b⁻¹].map enc) = true) :
    (treeReps ([a, b, a⁻¹, b⁻¹].map enc) (pairUp c.rT)).size *
      Nat.card (Subgroup.normalizer (E : Set G)) ≤ Nat.card G := by
  classical
  set gR : List (RN n) := [a, b, a⁻¹, b⁻¹].map enc with hgR
  set T : List (Fin n) := fixPts (c.Es gR) with hTdef
  have hT : ∀ p, p ∈ T ↔ ∀ x ∈ E, act enc x p = p :=
    mem_fixPts_iff (c.Es gR) E hmemE hmemEs
  set L : List (RN n) := (treeReps gR (pairUp c.rT)).toList with hL
  have hnd : (L.map (imgMask T)).Nodup := by
    simpa [ECert.orbitCheckT] using hO
  have hLmem : ∀ r ∈ L, ∃ g : G, enc g = r := by
    intro r hr
    refine treeReps_mem (P := fun r => ∃ g : G, enc g = r) gR ?_ ⟨1, h.map_one⟩ ?_ (pairUp c.rT) r
      (by simpa [hL] using hr)
    · intro s
      rcases Nat.lt_or_ge s 4 with hs | hs
      · interval_cases s
        · exact ⟨a, rfl⟩
        · exact ⟨b, rfl⟩
        · exact ⟨a⁻¹, rfl⟩
        · exact ⟨b⁻¹, rfl⟩
      · rw [hgR, List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨1, h.map_one⟩
    · rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
      exact ⟨g * g', h.map_mul g g'⟩
  have hLnd : L.Nodup := List.Nodup.of_map _ hnd
  let ι : RN n → G := fun r => if hr : ∃ g : G, enc g = r then Classical.choose hr else 1
  have hι : ∀ r ∈ L, enc (ι r) = r := by
    intro r hr
    have hr' := hLmem r hr
    simp only [ι, hr', ↓reduceDIte]
    exact Classical.choose_spec hr'
  have : Fintype (G ⧸ Subgroup.normalizer (E : Set G)) := Fintype.ofFinite _
  have h1 : L.toFinset.card ≤
      (Finset.univ : Finset (G ⧸ Subgroup.normalizer (E : Set G))).card := by
    refine Finset.card_le_card_of_injOn
      (fun r => (QuotientGroup.mk (ι r) : G ⧸ Subgroup.normalizer (E : Set G)))
      (fun _ _ => Finset.mem_univ _) ?_
    intro r₁ hr₁ r₂ hr₂ hq
    have hr₁' : r₁ ∈ L := List.mem_toFinset.1 hr₁
    have hr₂' : r₂ ∈ L := List.mem_toFinset.1 hr₂
    have hq' : (ι r₁)⁻¹ * ι r₂ ∈ Subgroup.normalizer (E : Set G) := by
      have := QuotientGroup.eq.1 hq
      exact this
    have himg := img_eq h E T hT hq'
    have hmask : imgMask T r₁ = imgMask T r₂ := by
      calc imgMask T r₁ = imgMask T (enc (ι r₁)) := by rw [hι r₁ hr₁']
        _ = imgMask T (enc (ι r₂)) := by
          rw [imgMask_enc, imgMask_enc, himg]
        _ = imgMask T r₂ := by rw [hι r₂ hr₂']
    exact List.inj_on_of_nodup_map hnd hr₁' hr₂' hmask
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLnd
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h1
  have hLsize : L.length = (treeReps gR (pairUp c.rT)).size := by simp [hL]
  rw [hLsize] at h1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.normalizer (E : Set G))]
  exact Nat.mul_le_mul_right _ h1

theorem ECert.exists_soundT (h : IsEnc enc) (a b : G) (c : ECert) (kOrd : ℕ)
    (hk : Nat.card G = kOrd) (hc : c.coreCheckT ([a, b, a⁻¹, b⁻¹].map enc) kOrd = true) :
    ∃ E N : Subgroup G, c.Sound enc a b E N := by
  simp only [ECert.coreCheckT, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hE, hN⟩, hO⟩, hK⟩ := hc
  refine ECert.exists_soundCore h a b c (treeReps ([a, b, a⁻¹, b⁻¹].map enc) (pairUp c.rT)).size
    (by rw [hk]; exact hK.symm) ?_ ?_
  · simp only [hE, hN, Bool.and_self]
  · intro E hmemE hmemEs
    exact orbit_bound_tree h a b c E hmemE hmemEs hO

end Fix

end CFSG.QuasithinUnique.A5.Kc3Cert
