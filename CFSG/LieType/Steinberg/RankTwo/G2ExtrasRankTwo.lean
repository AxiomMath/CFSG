module

public import CFSG.LieType.Steinberg.Statement
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.Steinberg.G2.Extras

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

local notation "xG" => xPar (rootOperatorFamily Tag.G2)

local notation "g2Root" => RootCertificate.root (Tag.rootCertificate Tag.G2)

namespace G2Extras

theorem prod_map_eq_filter_mul_filter {X G : Type*} [Monoid G] (l : List X) (q : X → Bool)
    (g : X → G) (h : ∀ a ∈ l, q a = false → ∀ b ∈ l, Commute (g a) (g b)) :
    (l.map g).prod = ((l.filter q).map g).prod * ((l.filter fun a => !q a).map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun c hc hqc d hd =>
      h c (List.mem_cons_of_mem a hc) hqc d (List.mem_cons_of_mem a hd)
    cases hqa : q a
    · have hc : Commute (g a) ((t.filter q).map g).prod :=
        Commute.list_prod_right _ _ fun b hb => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
          exact h a (List.mem_cons_self ..) hqa d
            (List.mem_cons_of_mem a (List.mem_filter.1 hd).1)
      rw [List.filter_cons_of_neg (by simp [hqa]), List.filter_cons_of_pos (by simp [hqa]),
        List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih', ← mul_assoc,
        hc.eq, mul_assoc]
    · rw [List.filter_cons_of_pos hqa, List.filter_cons_of_neg (by simp [hqa]), List.map_cons,
        List.map_cons, List.prod_cons, List.prod_cons, ih', mul_assoc]

theorem eq_pair_or_of_nodup {X : Type*} {l : List X} {a b : X} (hnd : l.Nodup) (hab : a ≠ b)
    (h : ∀ x, x ∈ l ↔ x = a ∨ x = b) : l = [a, b] ∨ l = [b, a] := by
  have hp : l.Perm [a, b] := (List.perm_ext_iff_of_nodup hnd (by simp [hab])).2 fun x => by
    simp [h]
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hp.length_eq
  have hx := (h x).1 (by simp)
  have hy := (h y).1 (by simp)
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    simp at hnd
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd rfl hxy

theorem isRoot_g2Root {n : ℕ} (hn : n < 12) : IsRoot .G2 (g2Root n) :=
  isRoot_rootCertificate_root hn

theorem g2_root_bound
    {v : Fin (Tag.rank .G2) → ℤ} (hv : IsRoot .G2 v) :
    -2 ≤ v (0 : Fin 2) ∧ v (0 : Fin 2) ≤ 2 ∧ -3 ≤ v (1 : Fin 2) ∧ v (1 : Fin 2) ≤ 3 := by
  have h : ∀ w ∈ rootFinset .G2,
      -2 ≤ w (0 : Fin 2) ∧ w (0 : Fin 2) ≤ 2 ∧ -3 ≤ w (1 : Fin 2) ∧ w (1 : Fin 2) ≤ 3 := by
    decide
  exact h v (mem_rootFinset.2 hv)

theorem g2Root_two : g2Root 2 = ![-1, 0] := by ext i; fin_cases i <;> rfl

theorem g2Root_four : g2Root 4 = ![1, 1] := by ext i; fin_cases i <;> rfl

theorem g2Root_six : g2Root 6 = ![-1, -3] := by ext i; fin_cases i <;> rfl

theorem g2Root_seven : g2Root 7 = ![2, 3] := by ext i; fin_cases i <;> rfl

theorem g2Root_seven_add_six : g2Root 7 + g2Root 6 = g2Root 0 := by
  ext i; fin_cases i <;> rfl

theorem g2Root_two_add_four : g2Root 2 + g2Root 4 = g2Root 1 := by
  ext i; fin_cases i <;> rfl

theorem g2Root_two_add_two_four : g2Root 2 + 2 • g2Root 4 = g2Root 8 := by
  ext i; fin_cases i <;> rfl

theorem g2Root_two_add_three_four : g2Root 2 + 3 • g2Root 4 = g2Root 7 := by
  ext i; fin_cases i <;> rfl

theorem g2Root_two_two_add_three_four : 2 • g2Root 2 + 3 • g2Root 4 = g2Root 3 := by
  ext i; fin_cases i <;> rfl

theorem coord_two_four (i j : ℕ) :
    (i • g2Root 2 + j • g2Root 4) (0 : Fin 2) = (j : ℤ) - i ∧
      (i • g2Root 2 + j • g2Root 4) (1 : Fin 2) = j := by
  rw [g2Root_two, g2Root_four]
  constructor
  · change i • (-1 : ℤ) + j • (1 : ℤ) = (j : ℤ) - i
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    ring
  · change i • (0 : ℤ) + j • (1 : ℤ) = j
    simp

theorem coord_seven_six (i j : ℕ) :
    (i • g2Root 7 + j • g2Root 6) (0 : Fin 2) = 2 * (i : ℤ) - j ∧
      (i • g2Root 7 + j • g2Root 6) (1 : Fin 2) = 3 * (i : ℤ) - 3 * j := by
  rw [g2Root_seven, g2Root_six]
  constructor
  · change i • (2 : ℤ) + j • (-1 : ℤ) = 2 * (i : ℤ) - j
    simp only [nsmul_eq_mul]
    ring
  · change i • (3 : ℤ) + j • (-3 : ℤ) = 3 * (i : ℤ) - 3 * j
    simp only [nsmul_eq_mul]
    ring

variable {Φ : CFSG.LieType.Steinberg.RootSystem (Fin (Tag.rank .G2))}

theorem mem_expPairs_two_four
    (hΦ : Φ.roots = {v | IsRoot .G2 v}) (p : ℕ × ℕ) :
    p ∈ expPairs Φ (g2Root 2) (g2Root 4) ↔
      p ∈ ([(1, 1), (1, 2), (1, 3), (2, 3)] : List (ℕ × ℕ)) := by
  obtain ⟨i, j⟩ := p
  change (0 < i ∧ 0 < j ∧ i • g2Root 2 + j • g2Root 4 ∈ Φ.roots) ↔ _
  rw [hΦ, Set.mem_ofPred_eq, ← mem_rootFinset]
  constructor
  · rintro ⟨hi, hj, hr⟩
    have hb := g2_root_bound (mem_rootFinset.1 hr)
    obtain ⟨e0, e1⟩ := coord_two_four i j
    rw [e0, e1] at hb
    have key : ∀ i ∈ List.range 6, ∀ j ∈ List.range 4, 0 < i → 0 < j →
        i • g2Root 2 + j • g2Root 4 ∈ rootFinset .G2 →
          (i, j) ∈ ([(1, 1), (1, 2), (1, 3), (2, 3)] : List (ℕ × ℕ)) := by decide
    exact key i (List.mem_range.2 (by omega)) j (List.mem_range.2 (by omega)) hi hj hr
  · intro h
    have key : ∀ p ∈ ([(1, 1), (1, 2), (1, 3), (2, 3)] : List (ℕ × ℕ)),
        0 < p.1 ∧ 0 < p.2 ∧ p.1 • g2Root 2 + p.2 • g2Root 4 ∈ rootFinset .G2 := by decide
    exact key _ h

theorem mem_expPairs_seven_six
    (hΦ : Φ.roots = {v | IsRoot .G2 v}) (p : ℕ × ℕ) :
    p ∈ expPairs Φ (g2Root 7) (g2Root 6) ↔ p ∈ ([(1, 1)] : List (ℕ × ℕ)) := by
  obtain ⟨i, j⟩ := p
  change (0 < i ∧ 0 < j ∧ i • g2Root 7 + j • g2Root 6 ∈ Φ.roots) ↔ _
  rw [hΦ, Set.mem_ofPred_eq, ← mem_rootFinset]
  constructor
  · rintro ⟨hi, hj, hr⟩
    have hb := g2_root_bound (mem_rootFinset.1 hr)
    obtain ⟨e0, e1⟩ := coord_seven_six i j
    rw [e0, e1] at hb
    have key : ∀ i ∈ List.range 4, ∀ j ∈ List.range 5, 0 < i → 0 < j →
        i • g2Root 7 + j • g2Root 6 ∈ rootFinset .G2 →
          (i, j) ∈ ([(1, 1)] : List (ℕ × ℕ)) := by decide
    exact key i (List.mem_range.2 (by omega)) j (List.mem_range.2 (by omega)) hi hj hr
  · intro h
    have key : ∀ p ∈ ([(1, 1)] : List (ℕ × ℕ)),
        0 < p.1 ∧ 0 < p.2 ∧ p.1 • g2Root 7 + p.2 • g2Root 6 ∈ rootFinset .G2 := by decide
    exact key _ h

section Group

variable {k : Type} [Field k]

theorem commute_of_repCheck_nil
    {a b : ℕ} (h : repCheck .G2 a b [] = true) (s t : k) :
    Commute (xG (g2Root a) s) (xG (g2Root b) t) := by
  have := CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := k) h s t
  rw [List.map_nil, List.prod_nil] at this
  exact commutatorElement_eq_one_iff_commute.1 this

theorem commutator_seven_six
    (s t : k) :
    ⁅xG (g2Root 7) s, xG (g2Root 6) t⁆ = xG (g2Root 0) (s * t) := by
  have h : repCheck .G2 7 6 [(1, 1, 0, 1)] = true := by decide +kernel
  simpa using CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := k) h s t

theorem commutator_two_four :
    ⁅xG (g2Root 2) (1 : k), xG (g2Root 4) (1 : k)⁆ =
      xG (g2Root 1) 1 * xG (g2Root 8) 1 * xG (g2Root 7) 1 * xG (g2Root 3) (-1) := by
  have h : repCheck .G2 2 4 [(1, 1, 1, 1), (1, 2, 8, 1), (1, 3, 7, 1), (2, 3, 3, -1)] = true := by
    decide +kernel
  have := CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := k) h 1 1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    Int.cast_one, Int.cast_neg] at this
  rw [this]
  simp only [mul_assoc]

theorem mul_swap_eight_one
    (s t : k) :
    xG (g2Root 8) s * xG (g2Root 1) t =
      xG (g2Root 1) t * xG (g2Root 8) s * xG (g2Root 3) (-3 * s * t) := by
  have h : repCheck .G2 8 1 [(1, 1, 3, -3)] = true := by decide +kernel
  have hc := CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := k) h s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    Int.cast_neg] at hc
  have hz1 := commute_of_repCheck_nil (k := k) (a := 3) (b := 1) (by decide +kernel)
    (((-3 : ℤ) : k) * s * t) t
  have hz8 := commute_of_repCheck_nil (k := k) (a := 3) (b := 8) (by decide +kernel)
    (((-3 : ℤ) : k) * s * t) s
  have e : xG (g2Root 8) s * xG (g2Root 1) t =
      ⁅xG (g2Root 8) s, xG (g2Root 1) t⁆ * xG (g2Root 1) t * xG (g2Root 8) s := by
    rw [commutatorElement_def]
    group
  rw [e, hc]
  push_cast at hz1 hz8 ⊢
  rw [hz1.eq, mul_assoc, hz8.eq, ← mul_assoc]

end Group

section Coeff

variable {k : Type} [Field k] {O : CommOrder Φ}
  {C : (Fin (Tag.rank .G2) → ℤ) → (Fin (Tag.rank .G2) → ℤ) → ℕ × ℕ → ℤ}

theorem coeff_seven_six
    (hΦ : Φ.roots = {v | IsRoot .G2 v})
    (hC : CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C) :
    (C (g2Root 7) (g2Root 6) (1, 1) : k) = 1 := by
  have h7 : g2Root 7 ∈ Φ.roots := by rw [hΦ]; exact isRoot_g2Root (by norm_num)
  have h6 : g2Root 6 ∈ Φ.roots := by rw [hΦ]; exact isRoot_g2Root (by norm_num)
  have hsum : g2Root 7 + g2Root 6 ≠ 0 := by
    rw [g2Root_seven_add_six]
    exact (isRoot_g2Root (by norm_num)).ne_zero
  have hl : O.list (g2Root 7) (g2Root 6) = [(1, 1)] := by
    refine List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (O.nodup _ _)
      (List.nodup_singleton _)).2 fun p => ?_)
    rw [O.mem_iff _ h7 _ h6 hsum, mem_expPairs_seven_six hΦ]
  have h1 := hC _ h7 _ h6 hsum 1 1
  rw [hl, commutator_seven_six] at h1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    one_smul, g2Root_seven_add_six] at h1
  exact (xPar_injective (isRoot_g2Root (by norm_num)) h1).symm

@[expose] def phiG2 : (Fin (Tag.rank .G2) → ℤ) →+ ℤ :=
  Pi.evalAddMonoidHom (fun _ => ℤ) (1 : Fin 2) - Pi.evalAddMonoidHom (fun _ => ℤ) (0 : Fin 2)

theorem eq_of_prod_eq_short
    {a b c d a' b' c' d' : k}
    (h : xG (g2Root 1) a * xG (g2Root 8) b * xG (g2Root 7) c * xG (g2Root 3) d =
      xG (g2Root 1) a' * xG (g2Root 8) b' * xG (g2Root 7) c' * xG (g2Root 3) d') :
    a = a' := by
  set L : List (Fin (Tag.rank .G2) → ℤ) := [g2Root 1, g2Root 8, g2Root 7, g2Root 3] with hLdef
  have hroots : ∀ γ ∈ L, IsRoot .G2 γ ∧ 0 < phiG2 γ := by
    intro γ hγ
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl <;> exact ⟨isRoot_g2Root (by norm_num), by decide⟩
  have hinj := prodInjective (F := rootOperatorFamily .G2) (K := k) phiG2 L (by decide) hroots
    (by decide)
  have h81 : g2Root 8 ≠ g2Root 1 := by decide
  have h71 : g2Root 7 ≠ g2Root 1 := by decide
  have h78 : g2Root 7 ≠ g2Root 8 := by decide
  have h31 : g2Root 3 ≠ g2Root 1 := by decide
  have h38 : g2Root 3 ≠ g2Root 8 := by decide
  have h37 : g2Root 3 ≠ g2Root 7 := by decide
  classical
  set f : (Fin (Tag.rank .G2) → ℤ) → adjointGroup .G2 k := fun v =>
    xG v (if v = g2Root 1 then a else if v = g2Root 8 then b else if v = g2Root 7 then c else d)
  set g : (Fin (Tag.rank .G2) → ℤ) → adjointGroup .G2 k := fun v =>
    xG v (if v = g2Root 1 then a' else if v = g2Root 8 then b' else if v = g2Root 7 then c'
      else d')
  have hf := hinj f g (fun γ hγ => xPar_mem (hroots γ hγ).1 _)
    (fun γ hγ => xPar_mem (hroots γ hγ).1 _)
    (by simpa [f, g, hLdef, h81, h71, h78, h31, h38, h37, mul_assoc] using h) (g2Root 1)
    (by simp [hLdef])
  simp only [f, g] at hf
  exact xPar_injective (isRoot_g2Root (by norm_num)) hf

theorem coeff_two_four
    (hΦ : Φ.roots = {v | IsRoot .G2 v})
    (hC : CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C) :
    (C (g2Root 2) (g2Root 4) (1, 1) : k) = 1 := by
  have h2 : g2Root 2 ∈ Φ.roots := by rw [hΦ]; exact isRoot_g2Root (by norm_num)
  have h4 : g2Root 4 ∈ Φ.roots := by rw [hΦ]; exact isRoot_g2Root (by norm_num)
  have hsum : g2Root 2 + g2Root 4 ≠ 0 := by
    rw [g2Root_two_add_four]
    exact (isRoot_g2Root (by norm_num)).ne_zero
  set l := O.list (g2Root 2) (g2Root 4) with hldef
  have hmem : ∀ p, p ∈ l ↔ p ∈ ([(1, 1), (1, 2), (1, 3), (2, 3)] : List (ℕ × ℕ)) := fun p =>
    (O.mem_iff _ h2 _ h4 hsum p).trans (mem_expPairs_two_four hΦ p)
  set y : ℕ × ℕ → adjointGroup .G2 k := fun p =>
    xG (p.1 • g2Root 2 + p.2 • g2Root 4) ((C (g2Root 2) (g2Root 4) p : k) * 1 ^ p.1 * 1 ^ p.2)
    with hydef
  set a := (C (g2Root 2) (g2Root 4) (1, 1) : k)
  set b := (C (g2Root 2) (g2Root 4) (1, 2) : k)
  set c := (C (g2Root 2) (g2Root 4) (1, 3) : k)
  set d := (C (g2Root 2) (g2Root 4) (2, 3) : k)
  have y11 : y (1, 1) = xG (g2Root 1) a := by
    simp only [hydef, one_smul, one_pow, mul_one, g2Root_two_add_four]
    rfl
  have y12 : y (1, 2) = xG (g2Root 8) b := by
    simp only [hydef, one_smul, one_pow, mul_one, g2Root_two_add_two_four]
    rfl
  have y13 : y (1, 3) = xG (g2Root 7) c := by
    simp only [hydef, one_smul, one_pow, mul_one, g2Root_two_add_three_four]
    rfl
  have y23 : y (2, 3) = xG (g2Root 3) d := by
    simp only [hydef, one_pow, mul_one, g2Root_two_two_add_three_four]
    rfl
  have hcomm : ∀ p ∈ l, decide (p.2 ≤ 2) = false → ∀ q ∈ l, Commute (y p) (y q) := by
    intro p hp hpk q hq
    rw [hmem] at hp hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl
    · exact absurd hpk (by decide)
    · exact absurd hpk (by decide)
    · rw [y13]
      rcases hq with rfl | rfl | rfl | rfl
      · rw [y11]; exact commute_of_repCheck_nil (by decide +kernel) _ _
      · rw [y12]; exact commute_of_repCheck_nil (by decide +kernel) _ _
      · rw [y13]
      · rw [y23]; exact (commute_of_repCheck_nil (by decide +kernel) _ _).symm
    · rw [y23]
      rcases hq with rfl | rfl | rfl | rfl
      · rw [y11]; exact commute_of_repCheck_nil (by decide +kernel) _ _
      · rw [y12]; exact commute_of_repCheck_nil (by decide +kernel) _ _
      · rw [y13]; exact commute_of_repCheck_nil (by decide +kernel) _ _
      · rw [y23]
  have hsplit := prod_map_eq_filter_mul_filter l (fun p => decide (p.2 ≤ 2)) y hcomm
  have hnd := O.nodup (g2Root 2) (g2Root 4)
  have hkeep : l.filter (fun p => decide (p.2 ≤ 2)) = [(1, 1), (1, 2)] ∨
      l.filter (fun p => decide (p.2 ≤ 2)) = [(1, 2), (1, 1)] := by
    refine eq_pair_or_of_nodup (hnd.filter _) (by decide) fun p => ?_
    rw [List.mem_filter, hmem]
    constructor
    · rintro ⟨hp, hpk⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hpk (by decide)
      · exact absurd hpk (by decide)
    · rintro (rfl | rfl) <;> decide
  have hrest : l.filter (fun p => !decide (p.2 ≤ 2)) = [(1, 3), (2, 3)] ∨
      l.filter (fun p => !decide (p.2 ≤ 2)) = [(2, 3), (1, 3)] := by
    refine eq_pair_or_of_nodup (hnd.filter _) (by decide) fun p => ?_
    rw [List.mem_filter, hmem]
    constructor
    · rintro ⟨hp, hpk⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact absurd hpk (by decide)
      · exact absurd hpk (by decide)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl) <;> decide
  have hzr : ∀ u v : k, xG (g2Root 3) u * xG (g2Root 7) v = xG (g2Root 7) v * xG (g2Root 3) u :=
    fun u v => (commute_of_repCheck_nil (by decide +kernel) u v).eq
  have hnf : ∃ e : k, ⁅xG (g2Root 2) (1 : k), xG (g2Root 4) (1 : k)⁆ =
      xG (g2Root 1) a * xG (g2Root 8) b * xG (g2Root 7) c * xG (g2Root 3) e := by
    have h1 := hC _ h2 _ h4 hsum 1 1
    rw [← hldef, hsplit] at h1
    rcases hkeep with hk | hk <;> rcases hrest with hr | hr <;>
      simp only [hk, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        y11, y12, y13, y23] at h1
    · exact ⟨d, by rw [h1]; simp only [mul_assoc]⟩
    · exact ⟨d, by rw [h1, hzr]; simp only [mul_assoc]⟩
    all_goals
      refine ⟨-3 * b * a + d, ?_⟩
      have e1 := mul_swap_eight_one (k := k) b a
      have e2 := hzr (-3 * b * a) c
      have e3 : xG (g2Root 3) (-3 * b * a + d) =
          xG (g2Root 3) (-3 * b * a) * xG (g2Root 3) d :=
        xPar_add _ _ _
      rw [h1, e3]
      try rw [hzr d c]
      calc xG (g2Root 8) b * xG (g2Root 1) a * (xG (g2Root 7) c * xG (g2Root 3) d)
          = xG (g2Root 8) b * xG (g2Root 1) a * xG (g2Root 7) c * xG (g2Root 3) d := by
            simp only [mul_assoc]
        _ = xG (g2Root 1) a * xG (g2Root 8) b * (xG (g2Root 3) (-3 * b * a) * xG (g2Root 7) c) *
            xG (g2Root 3) d := by
            rw [e1]
            simp only [mul_assoc]
        _ = _ := by
            rw [e2]
            simp only [mul_assoc]
  obtain ⟨e, he⟩ := hnf
  exact eq_of_prod_eq_short (he.symm.trans commutator_two_four)

end Coeff

end G2Extras

open G2Extras

theorem g2_rankTwo
    {k : Type} [Field k]
    {Φ : CFSG.LieType.Steinberg.RootSystem (Fin (Tag.rank .G2))}
    (hΦ : Φ.roots = {v | IsRoot .G2 v}) {O : CommOrder Φ}
    {C : (Fin (Tag.rank .G2) → ℤ) → (Fin (Tag.rank .G2) → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) O C)
    (i : Fin (Tag.rank .G2)) :
    ∃ δ ∈ Φ.roots, ∃ γ ∈ Φ.roots, δ + γ ≠ 0 ∧ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
      Pi.single i 1 = δ + j • γ ∧ IsUnit (C δ γ (1, j) : k) := by
  have hr : ∀ n < 12, g2Root n ∈ Φ.roots := fun n hn => by rw [hΦ]; exact isRoot_g2Root hn
  fin_cases i
  · refine ⟨g2Root 7, hr 7 (by norm_num), g2Root 6, hr 6 (by norm_num), ?_, 1, Or.inl rfl, ?_,
      ?_⟩
    · rw [g2Root_seven_add_six]
      exact (isRoot_g2Root (by norm_num)).ne_zero
    · rw [one_smul, g2Root_seven_add_six]
      ext j; fin_cases j <;> rfl
    · rw [coeff_seven_six hΦ hC]
      exact isUnit_one
  · refine ⟨g2Root 2, hr 2 (by norm_num), g2Root 4, hr 4 (by norm_num), ?_, 1, Or.inl rfl, ?_,
      ?_⟩
    · rw [g2Root_two_add_four]
      exact (isRoot_g2Root (by norm_num)).ne_zero
    · rw [one_smul, g2Root_two_add_four]
      ext j; fin_cases j <;> rfl
    · rw [coeff_two_four hΦ hC]
      exact isUnit_one

end CFSG.LieType.Steinberg.RankTwo
