module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Two
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cert

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six
  CFSG.QuasithinUnique.A5

section Sub

variable {n : ℕ}

@[expose] def subgroupCheck (gR : List (RN n)) (pW : List (List ℕ)) (depth size : ℕ) : Bool :=
  closedH (pW.map (evalW gR)) (bfsSet (pW.map (evalW gR)) depth) &&
    ((bfsSet (pW.map (evalW gR)) depth).size == size)

variable {G : Type} [Group G] {enc : G → RN n}

theorem subgroup_sound [Finite G] (h : IsEnc enc) (a b : G) (pW : List (List ℕ)) (depth size : ℕ)
    (hc : subgroupCheck ([a, b, a⁻¹, b⁻¹].map enc) pW depth size = true) :
    ∃ P : Subgroup G, Nat.card P = size ∧
      ∀ x : G, x ∈ P ↔ enc x ∈ bfsSet (pW.map (evalW ([a, b, a⁻¹, b⁻¹].map enc))) depth := by
  classical
  set gl : List G := [a, b, a⁻¹, b⁻¹] with hgl
  set gR : List (RN n) := gl.map enc with hgR
  set pG : List G := pW.map (evalW gl) with hpG
  have hpR : pW.map (evalW gR) = pG.map enc := by
    simp only [hpG, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp, enc_evalW h, hgR]
  simp only [subgroupCheck, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hcl, hsize⟩ := hc
  have hcl1 : closedH (pG.map enc) (bfsSet (pG.map enc) depth) = true := by
    rw [← hpR]; exact hcl
  refine ⟨Subgroup.closure {g | g ∈ pG}, ?_, ?_⟩
  · rw [card_closure_of_closedH h pG depth hcl1, ← hpR]
    exact hsize
  · intro x
    rw [mem_closure_iff_H h pG depth hcl1 x, hpR]

end Sub

section Conj

variable {n : ℕ}

@[expose] def conjClosed (g0 g1 g2 g3 : RN n) (S : Std.HashSet (RN n)) : Bool :=
  S.toList.all fun x => S.contains (g0 * x * g2) && S.contains (g1 * x * g3) &&
    S.contains (g2 * x * g0) && S.contains (g3 * x * g1)

@[expose] def conjStep (g0 g1 g2 g3 : RN n) (st : Std.HashSet (RN n) × List (RN n)) :
    Std.HashSet (RN n) × List (RN n) :=
  st.2.foldl (fun acc x =>
    [g0 * x * g2, g1 * x * g3, g2 * x * g0, g3 * x * g1].foldl (fun acc y =>
      if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) (st.1, [])

@[expose] def conjBfs (g0 g1 g2 g3 : RN n) (seeds : List (RN n)) (rounds : ℕ) :
    Std.HashSet (RN n) :=
  (Nat.iterate (conjStep g0 g1 g2 g3) rounds (Std.HashSet.ofList seeds, seeds)).1

@[expose] def invSeeds (Ps : Std.HashSet (RN n)) : List (RN n) :=
  Ps.toList.filter fun x => x * x == 1 && x != 1

variable {G : Type} [Group G] {enc : G → RN n}

theorem conj_mem_of_closed (h : IsEnc enc) {a b : G}
    (hab : Subgroup.closure ({a, b} : Set G) = ⊤) {S : Std.HashSet (RN n)}
    (hS : conjClosed (enc a) (enc b) (enc a⁻¹) (enc b⁻¹) S = true) :
    ∀ g s : G, enc s ∈ S → enc (g * s * g⁻¹) ∈ S := by
  intro g
  have hg : g ∈ Subgroup.closure ({a, b} : Set G) := by rw [hab]; trivial
  simp only [conjClosed, List.all_eq_true, Bool.and_eq_true, Std.HashSet.mem_toList,
    Std.HashSet.contains_iff_mem] at hS
  refine Subgroup.closure_induction'' (p := fun g _ => ∀ s : G, enc s ∈ S → enc (g * s * g⁻¹) ∈ S)
    ?_ ?_ ?_ ?_ hg
  · intro x hx s hs
    rcases hx with hx | hx
    · rw [hx, h.map_mul, h.map_mul]
      exact (hS (enc s) hs).1.1.1
    · rw [Set.mem_singleton_iff.1 hx, h.map_mul, h.map_mul]
      exact (hS (enc s) hs).1.1.2
  · intro x hx s hs
    rcases hx with hx | hx
    · rw [hx, h.map_mul, h.map_mul, inv_inv]
      exact (hS (enc s) hs).1.2
    · rw [Set.mem_singleton_iff.1 hx, h.map_mul, h.map_mul, inv_inv]
      exact (hS (enc s) hs).2
  · intro s hs
    simpa using hs
  · intro x y _ _ ihx ihy s hs
    have := ihx _ (ihy s hs)
    have e : x * (y * s * y⁻¹) * x⁻¹ = x * y * s * (x * y)⁻¹ := by group
    rwa [e] at this

variable [Finite G]

theorem involution_mem (h : IsEnc enc) {a b : G}
    (hab : Subgroup.closure ({a, b} : Set G) = ⊤) {S : Std.HashSet (RN n)}
    (hS : conjClosed (enc a) (enc b) (enc a⁻¹) (enc b⁻¹) S = true)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) (Ps : Std.HashSet (RN n))
    (hmemP : ∀ x : G, x ∈ P ↔ enc x ∈ Ps)
    (hseeds : ∀ x ∈ Ps, x * x = 1 → x ≠ 1 → x ∈ S) (t : G) (ht : t * t = 1) (ht1 : t ≠ 1) :
    enc t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hF : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le hP hPi hF
  have hmem : g * t * g⁻¹ ∈ P := hg ⟨t, Subgroup.mem_zpowers t, rfl⟩
  have hs := (hmemP _).1 hmem
  have hsq : enc (g * t * g⁻¹) * enc (g * t * g⁻¹) = 1 := by
    have : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht]; group
    rw [← h.map_mul, this, h.map_one]
  have hne : enc (g * t * g⁻¹) ≠ 1 := by
    intro h1
    have h2 : g * t * g⁻¹ = 1 := h.inj (by rw [h1, h.map_one])
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h2]
    group
  have h3 := conj_mem_of_closed h hab hS g⁻¹ (g * t * g⁻¹) (hseeds _ hs hsq hne)
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  rwa [e] at h3

end Conj

section Check

variable {n : ℕ}

@[expose] def xPow (X : RN n) : ℕ → RN n
  | 0 => 1
  | k + 1 => X * xPow X k

@[expose] def conjX (X y : RN n) (k : ℕ) : RN n := xPow X k * y * xPow X (5 - k)

@[expose] def yCheck (X : RN n) (S1 S2 S3 S4 S5 : Std.HashSet (RN n)) (y : RN n) : Bool :=
  S1.contains y || S2.contains y || S3.contains y || S4.contains y || S5.contains y ||
    y * conjX X y 1 != conjX X y 1 * y || y * conjX X y 2 != conjX X y 2 * y ||
    y * conjX X y 3 != conjX X y 3 * y || y * conjX X y 4 != conjX X y 4 * y ||
    y * conjX X y 1 * conjX X y 2 * conjX X y 3 * conjX X y 4 != 1

variable {G : Type} [Group G] {enc : G → RN n}

theorem enc_pow (h : IsEnc enc) (x : G) (k : ℕ) : enc (x ^ k) = xPow (enc x) k := by
  induction k with
  | zero => simpa [xPow] using h.map_one
  | succ k ih => rw [pow_succ', h.map_mul, ih]; rfl

theorem enc_conj (h : IsEnc enc) (x₀ : G) (hx5 : x₀ ^ 5 = 1) (y : G) (k : ℕ) (hk : k ≤ 5) :
    enc (x₀ ^ k * y * (x₀ ^ k)⁻¹) = conjX (enc x₀) (enc y) k := by
  have hinv : (x₀ ^ k)⁻¹ = x₀ ^ (5 - k) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    have : k + (5 - k) = 5 := by omega
    rw [this, hx5]
  rw [hinv, h.map_mul, h.map_mul, enc_pow h, enc_pow h]
  rfl

theorem yCheck_sound (h : IsEnc enc) (x₀ : G) (hx5 : x₀ ^ 5 = 1)
    (S1 S2 S3 S4 S5 : Std.HashSet (RN n)) (F1 F2 F3 F4 F5 : Subgroup G)
    (h1 : ∀ x : G, x ∈ F1 ↔ enc x ∈ S1) (h2 : ∀ x : G, x ∈ F2 ↔ enc x ∈ S2)
    (h3 : ∀ x : G, x ∈ F3 ↔ enc x ∈ S3) (h4 : ∀ x : G, x ∈ F4 ↔ enc x ∈ S4)
    (h5 : ∀ x : G, x ∈ F5 ↔ enc x ∈ S5) (y : G)
    (hy : yCheck (enc x₀) S1 S2 S3 S4 S5 (enc y) = true) :
    (∃ F ∈ [F1, F2, F3, F4, F5], y ∈ F) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧
        y * (x₀ ^ k * y * (x₀ ^ k)⁻¹) ≠ (x₀ ^ k * y * (x₀ ^ k)⁻¹) * y) ∨
      y * (x₀ ^ 1 * y * (x₀ ^ 1)⁻¹) * (x₀ ^ 2 * y * (x₀ ^ 2)⁻¹) * (x₀ ^ 3 * y * (x₀ ^ 3)⁻¹) *
        (x₀ ^ 4 * y * (x₀ ^ 4)⁻¹) ≠ 1 := by
  have hc : ∀ k : ℕ, k ≤ 5 → enc (x₀ ^ k * y * (x₀ ^ k)⁻¹) = conjX (enc x₀) (enc y) k :=
    fun k hk => enc_conj h x₀ hx5 y k hk
  have nc : ∀ k : ℕ, k ≤ 5 → enc y * conjX (enc x₀) (enc y) k ≠
      conjX (enc x₀) (enc y) k * enc y →
      y * (x₀ ^ k * y * (x₀ ^ k)⁻¹) ≠ (x₀ ^ k * y * (x₀ ^ k)⁻¹) * y := by
    intro k hk hne heq
    apply hne
    rw [← hc k hk, ← h.map_mul, ← h.map_mul, heq]
  simp only [yCheck, Bool.or_eq_true, bne_iff_ne, ne_eq, Std.HashSet.contains_iff_mem] at hy
  rcases hy with ((((((((hy | hy) | hy) | hy) | hy) | hy) | hy) | hy) | hy) | hy
  · left; exact ⟨F1, by simp, (h1 y).2 hy⟩
  · left; exact ⟨F2, by simp, (h2 y).2 hy⟩
  · left; exact ⟨F3, by simp, (h3 y).2 hy⟩
  · left; exact ⟨F4, by simp, (h4 y).2 hy⟩
  · left; exact ⟨F5, by simp, (h5 y).2 hy⟩
  · right; left; exact ⟨1, le_rfl, by norm_num, nc 1 (by norm_num) hy⟩
  · right; left; exact ⟨2, by norm_num, by norm_num, nc 2 (by norm_num) hy⟩
  · right; left; exact ⟨3, by norm_num, by norm_num, nc 3 (by norm_num) hy⟩
  · right; left; exact ⟨4, by norm_num, le_rfl, nc 4 (by norm_num) hy⟩
  · right; right
    intro heq
    apply hy
    rw [← hc 1 (by norm_num), ← hc 2 (by norm_num), ← hc 3 (by norm_num), ← hc 4 (by norm_num),
      ← h.map_mul, ← h.map_mul, ← h.map_mul, ← h.map_mul, heq, h.map_one]

end Check

end CFSG.QuasithinUnique.A5.Kc3Cert
