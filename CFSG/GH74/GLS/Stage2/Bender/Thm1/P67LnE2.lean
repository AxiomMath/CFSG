module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE2Gen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut.BlockTorus

section Roots

variable {L : Type} [Field L] [Finite L]

theorem card_pow_eq_one_le (r : ℕ) (hr : 0 < r) :
    Nat.card {u : Lˣ // u ^ r = 1} ≤ r := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have h := IsCyclic.card_pow_eq_one_le (α := Lˣ) (n := r) hr
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

end Roots

section Arith

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_sub_one {r : ℕ} [Fact r.Prime] (hr2 : Odd r) (hrq : (Nat.card K : ZMod r) = -1) :
    ¬ r ∣ Nat.card K - 1 := by
  intro h
  have hpos : 1 ≤ Nat.card K := Nat.card_pos
  have h1 : ((Nat.card K - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub hpos, hrq] at h1
  have h2 : ((2 : ℕ) : ZMod r) = 0 := by
    push_cast at h1 ⊢
    linear_combination -h1
  have hr : r.Prime := Fact.out
  have h3 : r ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h2
  have h4 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
  subst h4
  exact absurd hr2 (by decide)

theorem conjAut_ne_one_of_pow {n : ℕ} (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime)
    (hrK1 : ¬ r ∣ Nat.card K - 1) {x : GL (Fin n) K} (hx : x ^ r = 1) (hx1 : x ≠ 1) :
    conjAut n K x ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := eq_scalar_of_conjAut_eq_one hn h
  rw [← hc, ← map_pow] at hx
  have h3 : c ^ r = 1 := scalar_eq_one (by omega) hx
  have h4 : c = 1 := units_eq_one_of_pow_eq_one hr hrK1 h3
  rw [h4, map_one] at hc
  exact hx1 hc.symm

end Arith

section Torus

variable {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem pow_eq_one_of_torHom {g x : GL (Fin (4 + s)) K} {u w : (Lq K p)ˣ} {r : ℕ}
    (h : Φ K p s (g⁻¹ * x * g) = torHom K p s (u, w)) (hx : x ^ r = 1) :
    u ^ r = 1 ∧ w ^ r = 1 := by
  have h0 : (g⁻¹ * x * g) ^ r = 1 := by
    have := conj_pow (a := g⁻¹) (b := x) (i := r)
    simpa [hx] using this
  have h1 : torHom K p s (u ^ r, w ^ r) = torHom K p s 1 := by
    rw [map_one, show (u ^ r, w ^ r) = (u, w) ^ r from rfl, map_pow, ← h, ← map_pow, h0, map_one]
  have h2 := torHom_injective K p s h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

end Torus

section Main

variable {K : Type} [Field K] [Finite K]

theorem exists_torus_elems (p : ℕ) [Fact p.Prime] [CharP K p] {s : ℕ} (hs : s ≤ 1) {r : ℕ}
    [Fact r.Prime] (hr2 : Odd r) (hrq : (Nat.card K : ZMod r) = -1)
    {V : Subgroup (MulAut (projectiveSL (4 + s) K))} [IsElementaryAbelian r ↥V]
    (hVc : Nat.card ↥V = r ^ 2) (hVD : ∀ v ∈ V, ∃ A : GL (Fin (4 + s)) K, v = conjAut (4 + s) K A) :
    ∃ (g xa xb x1 : GL (Fin (4 + s)) K) (ζ : (Lq K p)ˣ),
      conjAut (4 + s) K xa ∈ V ∧ conjAut (4 + s) K xa ≠ 1 ∧
      conjAut (4 + s) K xb ∈ V ∧ conjAut (4 + s) K xb ≠ 1 ∧
      conjAut (4 + s) K x1 ∈ V ∧ conjAut (4 + s) K x1 ≠ 1 ∧
      Φ K p s (g⁻¹ * xa * g) = torHom K p s (ζ, 1) ∧
      Φ K p s (g⁻¹ * xb * g) = torHom K p s (1, ζ) ∧
      Φ K p s (g⁻¹ * x1 * g) = torHom K p s (ζ, ζ) := by
  classical
  have hr : r.Prime := Fact.out
  have hrK1 := not_dvd_sub_one hr2 hrq
  obtain ⟨W, hWe, hWc, hWV, -⟩ :=
    exists_lift_group (K := K) (n := 4 + s) (by omega) hrK1 hVc hVD
  have := hWe
  have hWpow : ∀ x ∈ W, x ^ r = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := W) x hx
  obtain ⟨g, hg⟩ := torus_conj K p s hr2 hrq hs W (IsElementaryAbelian.isPGroup r W)
  choose! U Wt hUW using hg
  let μ := {u : (Lq K p)ˣ // u ^ r = 1}
  have hμ : Nat.card μ ≤ r := card_pow_eq_one_le r hr.pos
  let f : W → μ × μ := fun x =>
    (⟨U x, (pow_eq_one_of_torHom p s (hUW x x.2) (hWpow x x.2)).1⟩,
     ⟨Wt x, (pow_eq_one_of_torHom p s (hUW x x.2) (hWpow x x.2)).2⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : U x = U y := congrArg (fun t : μ × μ => (t.1 : (Lq K p)ˣ)) hxy
    have h2 : Wt x = Wt y := congrArg (fun t : μ × μ => (t.2 : (Lq K p)ˣ)) hxy
    have h3 : Φ K p s (g⁻¹ * x * g) = Φ K p s (g⁻¹ * y * g) := by
      rw [hUW x x.2, hUW y y.2, h1, h2]
    have h4 := mul_right_cancel ((Φ K p s).injective h3)
    exact Subtype.ext (mul_left_cancel h4)
  have hcard : Nat.card (μ × μ) ≤ Nat.card W := by
    rw [Nat.card_prod, hWc, sq]
    exact Nat.mul_le_mul hμ hμ
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hcard
  have hμr : r ≤ Nat.card μ := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card W ≤ Nat.card (μ × μ) := Nat.card_le_card_of_injective f hfinj
    rw [Nat.card_prod, hWc] at h1
    nlinarith
  have hnt : Nontrivial μ :=
    Finite.one_lt_card_iff_nontrivial.mp (by have := hr.two_le; omega)
  let one : μ := ⟨1, one_pow r⟩
  obtain ⟨ζ, hζ⟩ := exists_ne one
  have hζ1 : (ζ : (Lq K p)ˣ) ≠ 1 := fun h => hζ (Subtype.ext h)
  have key : ∀ a b : μ, ∃ x ∈ W, Φ K p s (g⁻¹ * x * g) =
      torHom K p s ((a : (Lq K p)ˣ), (b : (Lq K p)ˣ)) := by
    intro a b
    obtain ⟨x, hx⟩ := hbij.2 (a, b)
    refine ⟨x, x.2, ?_⟩
    have h1 : U x = a := congrArg (fun t : μ × μ => (t.1 : (Lq K p)ˣ)) hx
    have h2 : Wt x = b := congrArg (fun t : μ × μ => (t.2 : (Lq K p)ˣ)) hx
    rw [hUW x x.2, h1, h2]
  have hnontriv : ∀ x ∈ W, ∀ a b : (Lq K p)ˣ, Φ K p s (g⁻¹ * x * g) = torHom K p s (a, b) →
      (a ≠ 1 ∨ b ≠ 1) → conjAut (4 + s) K x ≠ 1 := by
    intro x hx a b hab hne
    apply conjAut_ne_one_of_pow (by omega) hr hrK1 (hWpow x hx)
    rintro rfl
    have h1 : (a, b) = (1 : (Lq K p)ˣ × (Lq K p)ˣ) := by
      apply torHom_injective K p s
      rw [← hab, map_one]
      simp
    rcases hne with hne | hne
    · exact hne (congrArg Prod.fst h1)
    · exact hne (congrArg Prod.snd h1)
  obtain ⟨xa, hxaW, hxa⟩ := key ζ one
  obtain ⟨xb, hxbW, hxb⟩ := key one ζ
  obtain ⟨x1, hx1W, hx1⟩ := key ζ ζ
  exact ⟨g, xa, xb, x1, ζ, hWV xa hxaW, hnontriv xa hxaW _ _ hxa (Or.inl hζ1), hWV xb hxbW,
    hnontriv xb hxbW _ _ hxb (Or.inr hζ1), hWV x1 hx1W, hnontriv x1 hx1W _ _ hx1 (Or.inl hζ1),
    hxa, hxb, hx1⟩

theorem false_of_e2_four (p : ℕ) [Fact p.Prime] [CharP K p] {r : ℕ} [Fact r.Prime] (hr2 : Odd r)
    (hrq : (Nat.card K : ZMod r) = -1) {V Z : Subgroup (MulAut (projectiveSL 4 K))}
    (h2 : N2Cfg (projectiveSL 4 K) r V Z) (h3 : N3Full (projectiveSL 4 K) V Z)
    (hVD : ∀ v ∈ V, ∃ A : GL (Fin 4) K, v = conjAut 4 K A) : False := by
  classical
  have h2' := h2
  obtain ⟨-, -, hVe, hVc, -⟩ := h2'
  have : IsElementaryAbelian r ↥V := hVe
  obtain ⟨g, xa, xb, x1, ζ, hxaV, hxa1, hxbV, hxb1, hx1V, hx11, hxa, hxb, hx1⟩ :=
    exists_torus_elems (K := K) (s := 0) p (by norm_num) hr2 hrq hVc hVD
  set T : Subgroup (projectiveSL 4 K) := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v with hT
  have hle : ∀ x : GL (Fin 4) K, conjAut 4 K x ∈ V → conjAut 4 K x ≠ 1 →
      fixSub (conjAut 4 K x) ≤ T := fun x hx hne =>
    le_iSup₂_of_le (conjAut 4 K x) hx
      (le_iSup (fun _ : conjAut 4 K x ≠ 1 => fixSub (conjAut 4 K x)) hne)
  have hgen : T = ⊤ :=
    gen4 K p g xa xb x1 ζ hxa hxb hx1 T (hle xa hxaV hxa1) (hle xb hxbV hxb1) (hle x1 hx1V hx11)
  exact false_of_generation (isSimpleGroup_projectiveSL (by norm_num))
    (exists_noncomm_projectiveSL (by norm_num)) h2 h3 hgen

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2
