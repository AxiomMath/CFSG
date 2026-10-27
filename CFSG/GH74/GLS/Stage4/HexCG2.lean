module

public import CFSG.GH74.GLS.Stage4.HexCAsm2
public import CFSG.GH74.GLS.Stage4.HexCLocal
public import CFSG.GH74.GLS.Stage4.HexCDataW
public import CFSG.GH74.GLS.Stage4.HexCLam
public import CFSG.GH74.GLS.Stage4.HexCSt2

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem cast_prime_eq_zero {G : Type} [Group G] {root : ℤ → Subgroup G} {F : Type} [Field F]
    (D : HexData root F) {p : ℕ} (hexp : ∀ x ∈ root 4, x ^ p = 1) : (p : F) = 0 := by
  have key : ∀ n : ℕ, D.p4 (n : F) = (D.p4 1) ^ n := by
    intro n
    induction n with
    | zero => simp [map_zero_of_add' D.p4_add]
    | succ k ih => rw [Nat.cast_succ, D.p4_add, ih, pow_succ]
  apply D.p4_inj
  rw [key, hexp _ (D.p4_mem 1), map_zero_of_add' D.p4_add]

theorem two_three_ne_zero {F : Type} [Field F] [Finite F] {p q : ℕ} (hp : p.Prime) (hqodd : Odd q)
    (hcard : Nat.card F = q) (hpF : (p : F) = 0) (hp3 : p ≠ 3) :
    (2 : F) ≠ 0 ∧ (3 : F) ≠ 0 := by
  have hcp : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 hpF
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : q = p ^ (n : ℕ) := by rw [← hcard, Nat.card_eq_fintype_card, hn]
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2q : 2 ∣ q := by rw [hq]; exact dvd_pow_self 2 n.ne_zero
    have := Nat.odd_iff.1 hqodd
    omega
  refine ⟨fun h => hp2 ?_, fun h => hp3 ?_⟩
  · have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((CharP.cast_eq_zero_iff F p 2).1 this)
  · have : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 ((CharP.cast_eq_zero_iff F p 3).1 this)

theorem g2_coords_ne3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {H : Subgroup G}
    {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G} (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) {p q : ℕ} (hp : p.Prime) (hqodd : Odd q) (hq : RootOrdersG2 root q)
    (hP : PStruct p U root) (h1 : SL2At H R.N root 1) (h4 : SL2At H R.N root 4)
    (hO : OrthPair root) (hL : LongA2 root) (hnd : NondegG2 root) (hp3 : p ≠ 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      ∃ ψ : Fin 6 → F → G, G2Coords (R.toPre hgen).toSystemOfSimple ψ := by
  obtain ⟨E⟩ := sl2Pos_of_sl2At h4
  obtain ⟨E₁⟩ := sl2Pos_of_sl2At h1
  have hab : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x :=
    fun i hi1 hi6 x hx y hy => by
      have := (hP.2 i hi1 hi6).1
      exact setLike_mul_comm hx hy
  have hC : Hex6Comm root := Hex6Comm.of_data R hO hL.1 hL.2.1 hL.2.2 hab
  obtain ⟨D, hDφ⟩ := hexData_exists_phi R E E₁ hC hO hq hqodd
  have hcard : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]; exact hq 4 (by norm_num) (by norm_num)
  have hpF : (p : E.F) = 0 := cast_prime_eq_zero D (hP.2 4 (by norm_num) (by norm_num)).2
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp hqodd hcard hpF hp3
  obtain ⟨μ, hμ⟩ := exists_mu R hC D
  obtain ⟨a2, a4, L, hcd⟩ := exists_commData R D
  obtain ⟨A2, A4, g3, had⟩ := exists_actData R D
  have hnact : ActsPos 6 root (D.φ (sl2W E.F)) (fun q => 4 - q) := by
    rw [hDφ]; exact actsPos_weylSix R E hO
  obtain ⟨e, ha2, hmuL, ha4, hA2, hMg, hA4⟩ := stage2 R hC D h2 h3 hμ hcd had rfl hnact
  have he : e ≠ 0 := e_ne_zero D hnd had hA2
  obtain ⟨Λ, hΛmem, hΛμ, hΛadd, hΛsurj⟩ := exists_Lam D hμ had.g3_mem he h3 hMg
    (by rw [hq 3 (by norm_num) (by norm_num), hcard])
  have hΛinv : ∀ u ∈ root 3, Λ (μ u) = u := fun u hu => by
    obtain ⟨v, rfl⟩ := hΛsurj u hu
    rw [hΛμ]
  have hΛinj : ∀ v w, Λ v = Λ w → v = w := fun v w h => by
    rw [← hΛμ v, ← hΛμ w, h]
  have hr1 : ∀ s v, ⁅D.p1 s, Λ v⁆ = D.p2 (s * v) := fun s v => by
    rw [hμ.r1 s _ (hΛmem v), hΛμ]
  have hr5 : ∀ t v, ⁅D.p5 t, Λ v⁆ = D.p4 (t * v) := fun t v => by
    rw [hμ.r5 t _ (hΛmem v), hΛμ]
  have hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ =
      D.p2 (3 * e * s ^ 2 * t) * Λ (6 * e * (s * t)) * D.p4 (3 * e * s * t ^ 2) := fun s t => by
    have hLst : L s t = Λ (6 * e * (s * t)) := by
      rw [← hmuL s t, hΛinv _ (hcd.L_mem s t)]
    rw [hcd.eq s t, ha2 s t, ha4 s t, hLst]
  have hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (e * c * s ^ 3) * Λ (3 * e * c * s ^ 2) *
      D.p4 (2 * e * c ^ 2 * s ^ 3) * D.p5 (c * s) := fun c s => by
    have hg : g3 c s = Λ (3 * e * c * s ^ 2) := by
      rw [← hMg c s, hΛinv _ (had.g3_mem c s)]
    rw [had.eq c s]
    unfold Nel
    rw [hA2 c s, hA4 c s, hg]
  have hrel := g2Rel_of_data hC D hΛmem hΛadd hr5 e hr1 hc15 hAct
  exact ⟨E.F, E.field, E.finite, hcard, g2ψ D e Λ,
    g2Coords_of_data R hgen D he h3 hΛmem hΛinj hΛsurj hrel⟩

end CFSG.GH74.GLS.Stage4.Hex
