module

public import CFSG.GH74.GLS.Stage4.HexCD4Rel
public import CFSG.GH74.GLS.Stage4.HexCD4Conv
public import CFSG.GH74.GLS.Stage4.HexCD4T1
public import CFSG.GH74.GLS.Stage4.HexCD4Weyl
public import CFSG.GH74.GLS.Stage4.HexCD4Alg5
public import CFSG.GH74.GLS.Stage4.HexCD4Nondeg
public import CFSG.GH74.GLS.Stage4.HexCNondeg
public import CFSG.GH74.GLS.Stage4.HexCD4P3

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4 CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem exists_galData {F K : Type} [Field F] [Field K] [Finite F] (θ : F →+* K) {q : ℕ}
    (hq : 3 ≤ q) (hF : Nat.card F = q) (hK : Nat.card K = q ^ 3) :
    ∃ Gl : GalData F K, Gl.θ = θ ∧ Gl.q = q := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ : ∃ p, CharP F p := ⟨ringChar F, ringChar.charP F⟩
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  have : CharP K p := charP_of_injective_ringHom θ.injective p
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hqp : q = p ^ (n : ℕ) := by rw [← hF, Nat.card_eq_fintype_card, hn]
  exact ⟨{ θ := θ
           σ := iterateFrobenius K p n
           q := q
           hq := hq
           hF := hF
           hK := hK
           hσ := fun x => by rw [iterateFrobenius_def, hqp] }, rfl, rfl⟩

theorem d4_coords {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {H : Subgroup G}
    {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G} (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) {p q : ℕ} (hq3 : 3 ≤ q) (hqodd : Odd q)
    (hq : RootOrdersD4a root q) (hP : PStruct p U root) (h1 : SL2At H R.N root 1)
    (h4 : SL2At H R.N root 4) (hO : OrthPair root) (hL : LongA2 root) (hnd : NondegG2 root)
    (hnd13 : NondegD4X13 root) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
      (hσq : ∀ c, σ c = c ^ q) (ψ : ∀ i : Fin 6, d43Par σ i → G),
      D4Coords (R.toPre hgen).toSystemOfSimple (sigma_three_of_card hK hσq) ψ := by
  obtain ⟨E⟩ := sl2Pos_of_sl2At h4
  obtain ⟨E₁⟩ := sl2Pos_of_sl2At h1
  have hab : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x :=
    fun i hi1 hi6 x hx y hy => by
      have := (hP.2 i hi1 hi6).1
      exact setLike_mul_comm hx hy
  have hC : Hex6Comm root := Hex6Comm.of_data R hO hL.1 hL.2.1 hL.2.2 hab
  obtain ⟨D, hDφ, -, -⟩ := hexData4_exists_phi R E E₁ hC hO hq hqodd
  have hcardF : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]
    have := hq 4 (by norm_num) (by norm_num)
    simpa using this
  have hcardK : Nat.card E₁.F = q ^ 3 := by
    rw [← E₁.toRankOneAt.card_root]
    have := hq 1 (by norm_num) (by norm_num)
    simpa using this
  have hcard3 : Nat.card (root 3) = Nat.card E₁.F := by
    rw [hcardK]
    have := hq 3 (by norm_num) (by norm_num)
    simpa using this
  have := E.finite
  have := E₁.finite
  have h2 : (2 : E.F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hcardF]; exact hqodd)
  obtain ⟨Gl, hGlθ, hGlq⟩ := exists_galData D.θ hq3 hcardF hcardK
  have hθ : D.θ = Gl.θ := hGlθ.symm
  obtain ⟨β, hβ⟩ := exists_pair R hC D
  obtain ⟨p3, hp3add, hp3mem, hp3inj, hp3surj, hp3β⟩ := exists_p3 D Gl hθ hβ hcard3 hnd13
  obtain ⟨a2, a4, L, hcd⟩ := exists_commData4 R D
  obtain ⟨A2, A4, g3, had⟩ := exists_actData4 R D
  choose ℓ hℓ using fun s t => hp3surj (L s t) (hcd.L_mem s t)
  choose gh hgh using fun c s => hp3surj (g3 c s) (had.g3_mem c s)
  have H := d4Funcs_of_data R hC D Gl hθ hβ hp3add hp3inj hp3β hcd had
    (fun s t => (hℓ s t).symm) (fun c s => (hgh c s).symm)
  have hcov : ∀ ρ : E₁.Fˣ, ∃ χ : E.Fˣ, ∀ c s, gh ((χ : E.F) * c) ((ρ : E₁.F) ^ 2 * s) =
      ((ρ : E₁.F) ^ 2)⁻¹ * (Gl.θ (χ : E.F))⁻¹ * gh c s := by
    intro ρ
    obtain ⟨χ, hχ, h⟩ := t1_cov R D Gl h2 hβ hp3mem hp3surj hp3inj hp3β had
      (fun c s => (hgh c s).symm) ρ
    exact ⟨Units.mk0 χ hχ, fun c s => by simpa using (h c s).2.1⟩
  have hnact : ActsPos 6 root (D.φ (sl2W E.F)) (fun q => 4 - q) := by
    rw [hDφ]; exact actsPos_weylSix R E hO
  obtain ⟨⟨f₁, hf1⟩, ⟨f₅, hf5⟩, ⟨f₂, hf2⟩, ⟨f₄, hf4⟩⟩ := weyl_coords4 D hnact
  have hslot : ∀ s, f₂ 1 * A2 1 s + a4 (-s) s = A4 (-1) (-s) := fun s => by
    have := weyl_slot4 R hC D hcd had rfl hnact hf1 hf5 hf2 hf4 s
    rw [weyl_f2_lin D rfl hf2 (A2 1 s)] at this
    linear_combination this
  have hA2gen : ∀ {k : E.F}, (∀ s, gh 1 s = Gl.θ k * Gl.sharp s) →
      (∀ s t, a2 s t = k * Gl.trF (Gl.sharp s * t)) → ∀ c s, A2 c s = c * (k * Gl.Nm s) := by
    intro k hκ ha2
    by_cases h3 : (3 : E.F) = 0
    · refine d4_A2_p3 Gl H h3 hκ ha2 (fun ρ => ?_)
      obtain ⟨χ, hχ, h⟩ := t1_cov R D Gl h2 hβ hp3mem hp3surj hp3inj hp3β had
        (fun c s => (hgh c s).symm) ρ
      exact ⟨χ, hχ, fun c s => (h c s).1⟩
    · exact d4_A2 Gl H h2 h3 hκ ha2
  obtain ⟨k, hg1, hℓk, ha2k, ha4k, hA2k, hA4k⟩ := d4_formulas' Gl h2 H hcov hslot hA2gen
  have hk : k ≠ 0 := by
    intro hk0
    apply hnd
    intro x hx y hy
    obtain ⟨c, rfl⟩ := D.p6_surj x hx
    obtain ⟨s, rfl⟩ := D.p1_surj y hy
    rw [had.eq c s]
    unfold Nel4
    have e2 : D.p2 (A2 c s) = 1 := by
      rw [hA2k, hk0, zero_mul, mul_zero]; exact map_zero_of_add' D.p2_add
    have e3 : g3 c s = 1 := by
      rw [← hgh c s, H.g_eq Gl c s, hg1 s, hk0, map_zero, zero_mul, mul_zero]
      exact map_zero_of_add' hp3add
    have e4 : D.p4 (A4 c s) = 1 := by
      rw [hA4k, hk0, mul_zero, zero_mul, zero_mul]; exact map_zero_of_add' D.p4_add
    rw [e2, e3, e4]
    simp only [one_mul]
    exact Subgroup.mem_sup_right (D.p5_mem _)
  have hr1 : ∀ s a, ⁅D.p1 s, p3 a⁆ = D.p2 (Gl.trF (a * s)) := fun s a => by
    rw [hβ.r1 s _ (hp3mem a), hp3β]
  have hr5 : ∀ t a, ⁅D.p5 t, p3 a⁆ = D.p4 (Gl.trF (a * t)) := fun t a => by
    rw [hβ.r5 t _ (hp3mem a), hp3β]
  have hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = D.p2 (k * Gl.trF (Gl.sharp s * t)) *
      p3 (Gl.θ k * Gl.cross s t) * D.p4 (k * Gl.trF (s * Gl.sharp t)) := fun s t => by
    rw [hcd.eq s t, ha2k s t, ← hℓ s t, hℓk s t, ha4k s t]
  have hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (c * (k * Gl.Nm s)) *
      p3 (Gl.θ c * (Gl.θ k * Gl.sharp s)) * D.p4 (2 * k * c ^ 2 * Gl.Nm s) *
        D.p5 (Gl.θ c * s) := fun c s => by
    rw [had.eq c s]
    unfold Nel4
    rw [hA2k c s, hA4k c s, ← hgh c s, H.g_eq Gl c s, hg1 s, hθ]
  exact ⟨E₁.F, E₁.field, E₁.finite, Gl.σ, hcardK, fun c => by rw [Gl.hσ, hGlq], d4ψ D Gl k p3,
    d4Coords_of_data hC D Gl hp3add hp3mem hr1 hr5 k hc15 hAct R hgen hp3inj hp3surj hk⟩

end CFSG.GH74.GLS.Stage4.Hex
