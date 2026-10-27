module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteInteger
public import CFSG.CharacterTheory.Wreathed.LinearNormalizerLabelNonvanishing
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesLocal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatComplete

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.FullDefectLabels

section Roots

variable {m : ℕ} {ζ : ℂ}

theorem sum_Ico_zpow_neg (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) :
    ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) = -1 := by
  have hsum := hζ.inv.geom_sum_eq_zero hm
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero] at hsum
  have h : ∀ j : ℕ, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) = ζ⁻¹ ^ j := by
    intro j
    rw [Nat.cast_one, mul_one, zpow_neg, zpow_natCast, inv_pow]
  rw [Finset.sum_congr rfl fun j _ => h j]
  linear_combination hsum

theorem zpow_neg_half (hζ : IsPrimitiveRoot ζ m) {M : ℕ} (hm : m = 2 * M) (hM : 0 < M) :
    ζ ^ (-((M : ℤ) * ((1 : ℕ) : ℤ))) = -1 := by
  have h2 : IsPrimitiveRoot (ζ ^ M) 2 := by
    have h := hζ.pow_of_dvd (p := M) (by omega) ⟨2, by rw [hm]; ring⟩
    rwa [show m / M = 2 by rw [hm]; exact Nat.mul_div_cancel 2 hM] at h
  rw [Nat.cast_one, mul_one, zpow_neg, zpow_natCast, h2.eq_neg_one_of_two_right]
  norm_num

theorem line_sum [NeZero m] {M : ℕ} (hm : m = 2 * M) (hM : 0 < M) (κ : ℂ) (l : ZMod m) :
    ∑ i : ZMod m, (if (i = 0 ∨ i = M) ∧ (l - i = 0 ∨ l - i = M) then (0 : ℂ) else κ) =
      if l = 0 ∨ l = M then ((m : ℂ) - 2) * κ else (m : ℂ) * κ := by
  have hM0 : (M : ZMod m) ≠ 0 := natCast_ne_zero_of_lt hM (by omega)
  have hMM := M_add_M hm
  have h0mem : (0 : ZMod m) ∈ Finset.univ := Finset.mem_univ _
  have hMmem : (M : ZMod m) ∈ (Finset.univ : Finset (ZMod m)).erase 0 :=
    Finset.mem_erase.mpr ⟨hM0, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ hMmem]
  have hrest : ∑ i ∈ ((Finset.univ : Finset (ZMod m)).erase 0).erase (M : ZMod m),
      (if (i = 0 ∨ i = M) ∧ (l - i = 0 ∨ l - i = M) then (0 : ℂ) else κ) =
        ((m : ℂ) - 2) * κ := by
    rw [Finset.sum_congr rfl (fun i hi => by
      have hi' := Finset.mem_erase.mp hi
      have hi'' := Finset.mem_erase.mp hi'.2
      rw [ite_eq_right (fun h => h.1.elim hi''.1 hi'.1)])]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hMmem,
      Finset.card_erase_of_mem h0mem, Finset.card_univ, ZMod.card,
      show m - 1 - 1 = m - 2 by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  have e1 : l - M = 0 ↔ l = M := sub_eq_zero
  have e2 : l - M = M ↔ l = 0 := by
    constructor
    · intro h
      linear_combination h + hMM
    · intro h
      linear_combination h - hMM
  have hf0 : (if ((0 : ZMod m) = 0 ∨ (0 : ZMod m) = M) ∧ (l - 0 = 0 ∨ l - 0 = M) then (0 : ℂ)
      else κ) = if l = 0 ∨ l = M then 0 else κ := by
    simp
  have hfM : (if ((M : ZMod m) = 0 ∨ (M : ZMod m) = M) ∧ (l - M = 0 ∨ l - M = M) then (0 : ℂ)
      else κ) = if l = 0 ∨ l = M then 0 else κ := by
    simp only [hM0, false_or, true_and, e1, e2]
    by_cases h : l = 0 ∨ l = M
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
  rw [hf0, hfM, hrest]
  split_ifs <;> ring

theorem fourier_exc_vanish (hζ : IsPrimitiveRoot ζ m) {M : ℕ} (hm : m = 2 * M) (hM : 0 < M)
    (L : ZMod m → ℂ) (κ : ℂ)
    (hL : ∀ l, L l = if l = 0 ∨ l = M then ((m : ℂ) - 2) * κ else (m : ℂ) * κ) :
    ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) * (L 0 - L (-(j : ZMod m))) = 0 := by
  have hnM := neg_M hm
  have hterm : ∀ j ∈ Finset.Ico 1 m,
      ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) * (L 0 - L (-(j : ZMod m))) =
        -2 * κ * ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) +
          (if j = M then 2 * κ * ζ ^ (-((M : ℤ) * ((1 : ℕ) : ℤ))) else 0) := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    rw [hL 0, hL (-(j : ZMod m)), ite_eq_left (Or.inl rfl)]
    have hj0 : (j : ZMod m) ≠ 0 := natCast_ne_zero_of_lt (by omega) hj'.2
    by_cases hjM : j = M
    · subst hjM
      rw [ite_eq_left (Or.inr hnM), ite_eq_left rfl]
      ring
    · have hne : ¬(-(j : ZMod m) = 0 ∨ -(j : ZMod m) = M) := by
        rintro (h | h)
        · exact hj0 (neg_eq_zero.mp h)
        · apply hjM
          have h' : (j : ZMod m) = M := by rw [← hnM, ← h, neg_neg]
          exact natCast_inj_of_lt hj'.2 (by omega) h'
      rw [ite_eq_right hne, ite_eq_right hjM]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_Ico_zpow_neg hζ (by omega), Finset.sum_ite_eq' (Finset.Ico 1 m) M,
    ite_eq_left (Finset.mem_Ico.mpr ⟨hM, by omega⟩), zpow_neg_half hζ hm hM]
  ring

end Roots

section Nonvanishing

variable {G : Type} [Group G] [Fintype G]

theorem flat_value_a_ne_zero (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (lam : involutionCentralizer n S e →* ℂˣ)
    (hlamE : ∀ (v : involutionCentralizer n S e) (z : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      (v : G) = z → (lam v : ℂ) = (eb.representation θB).character z)
    (hlamS : ∀ v : involutionCentralizer n S e, (v : G) ∈ (S : Subgroup G) → lam v = 1) :
    ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character (wreathModelHom S e (Original.a (2 ^ n))) ≠ 0 := by
  have hstruct :=
    BaseFourCentralizerStructure.sylow_and_base_four_group_centralizer_structure n hn S e
  obtain ⟨dn, hdn⟩ := hstruct.normalizer_direct
  have hxS : wreathModelHom S e (Original.x (2 ^ n)) ∈ (S : Subgroup G) :=
    BrauerWong.wreathModelHom_mem S e _
  have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ involutionCentralizer n S e := by
    intro x hx
    obtain ⟨q', hq', c', hc', rfl⟩ := FlatTwistedBases.normalizer_eq_mul_centralizer S e hn x hx
    refine (involutionCentralizer n S e).mul_mem (sylow_le_involutionCentralizer n hn S e hq')
      (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    exact (Subgroup.mem_centralizer_iff.mp hc' _ hxS).symm
  let lam' : Subgroup.normalizer ((S : Subgroup G) : Set G) →* ℂˣ :=
    lam.comp (Subgroup.inclusion hNS)
  have hlamS' : ∀ x : Subgroup.normalizer ((S : Subgroup G) : Set G),
      (x : G) ∈ (S : Subgroup G) → lam' x = 1 := fun x hx => hlamS _ hx
  have hlabel : ∀ x, (nb.representation θhat).character x = lam' x := by
    intro x
    obtain ⟨⟨v, z⟩, rfl⟩ := dn.surjective x
    have hx : dn (v, z) = ⟨(v : G) * z, (Subgroup.normalizer ((S : Subgroup G) : Set G)).mul_mem
        (Subgroup.le_normalizer v.2) ((oddCore_le_normalizer S) z.2)⟩ := Subtype.ext (hdn (v, z))
    rw [hx, hθ v z]
    have hvN : (v : G) ∈ involutionCentralizer n S e := sylow_le_involutionCentralizer n hn S e v.2
    have hzN : (z : G) ∈ involutionCentralizer n S e := hNS ((oddCore_le_normalizer S) z.2)
    have hmul : Subgroup.inclusion hNS ⟨(v : G) * z, (Subgroup.normalizer
        ((S : Subgroup G) : Set G)).mul_mem (Subgroup.le_normalizer v.2)
          ((oddCore_le_normalizer S) z.2)⟩ = (⟨v, hvN⟩ : involutionCentralizer n S e) * ⟨z, hzN⟩ :=
      Subtype.ext rfl
    change _ = ((lam (Subgroup.inclusion hNS _) : ℂˣ) : ℂ)
    rw [hmul, map_mul, Units.val_mul, hlamS ⟨v, hvN⟩ v.2, Units.val_one, one_mul,
      hlamE ⟨z, hzN⟩ z rfl]
  have hnv := (linear_normalizer_label_sylow_center_nonvanishing basis ideal 2 S nb lam' hlamS'
    θhat hlabel B hB).2.2
  have haZ : wreathModelHom S e (Original.a (2 ^ n)) ∈ modelCenter S e := by
    rw [BrauerWong.modelCenter_eq_zpowers S e]
    exact Subgroup.mem_zpowers _
  intro χ hχ
  exact hnv χ hχ _ (BrauerWong.modelCenter_le_sylow S e haZ)
    (BrauerWong.modelCenter_le_centralizer n hn S e haZ)

end Nonvanishing

section Support

theorem single_subtype_apply {ι : Type*} [DecidableEq ι] {BB : Finset ι} (i : BB) (x : ℤ)
    (j : BB) : (Pi.single i x : BB → ℤ) j = (Pi.single i.1 x : ι → ℤ) j.1 := by
  by_cases h : j = i
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Subtype.ext h'))]

theorem exists_support {ι : Type*} [DecidableEq ι] (BB : Finset ι) {m M : ℕ} [NeZero m]
    (hm : m = 2 * M) (J : Finset ℕ) (hJ : J = oddIdx m) (deg : ι → ℤ) (hdeg : ∀ χ, 0 < deg χ)
    (X : ZMod m → ι → ℂ) (Y : ℕ → ι → ℤ) (c : ZMod m → ZMod m → ι → ℂ)
    (V : Finset (ZMod m × ZMod m)) (Xz : ZMod m → BB → ℤ) (cz : ZMod m → ZMod m → BB → ℤ)
    (hX : ∀ j : ZMod m, j ≠ 0 → ∀ i : BB, X j i.1 = Xz j i)
    (hc : ∀ a b (i : BB), c a b i.1 = cz a b i) (Rdet : Prop) (hRdet : Rdet)
    (hCS : CompleteSupport m M (fun i : BB => deg i.1) Xz (fun r i => Y r i.1) cz V) :
    ∃ (δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ) (χ₀ χ₁ χ₂ χ₃ χ₄ : ι) (ξ : ℕ → ι)
      (P Q : ℕ → Fin 2 → ι) (ψ : ZMod m × ZMod m → ι) (D Δ : ℤ),
      let Acol : ι → ℤ :=
        (Pi.single χ₀ δ₀ : ι → ℤ) + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ +
          Pi.single χ₃ δ₃
      let Kc : ι → ℤ :=
        (Pi.single χ₀ δ₀ : ι → ℤ) - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄)
      let Xodd : ℕ → ι → ℤ := fun h => Acol + Pi.single (ξ h) (2 * α)
      let Yzero : ι → ℤ :=
        β • ((Pi.single χ₀ δ₀ : ι → ℤ) + Pi.single χ₁ δ₁ - Pi.single χ₂ δ₂ -
          Pi.single χ₃ δ₃)
      let Cmid : ι → ℤ := Kc + Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃
      let Xeven : ℕ → ι → ℤ := fun r => Acol - Pi.single (P r 0) δ₂ -
        Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ - Pi.single (Q r 1) δ₃
      let Yeven : ℕ → ι → ℤ := fun r => -(Pi.single (P r 0) δ₂ : ι → ℤ) +
        Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ + Pi.single (Q r 1) δ₃
      let Cdiag : ℕ → Fin 2 → ι → ℤ := fun r er =>
        Kc + Pi.single (P r er) δ₂ - Pi.single (Q r er) δ₃
      let Cgen : ZMod m × ZMod m → ι → ℤ := fun I => Kc + Pi.single (ψ I) γ
      let core : Finset ι := {χ₀, χ₁, χ₂, χ₃, χ₄}
      let evenFam : Finset ι :=
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
          ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)
      (∀ sgn ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ], sgn = 1 ∨ sgn = -1) ∧
      Function.Injective ![χ₀, χ₁, χ₂, χ₃, χ₄] ∧ Set.InjOn ξ J ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ er er' : Fin 2,
        (P r er = P r' er' → r = r' ∧ er = er') ∧ (Q r er = Q r' er' → r = r' ∧ er = er') ∧
          P r er ≠ Q r' er') ∧
      Set.InjOn ψ V ∧
      (∀ h ∈ J, ξ h ∉ core) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ er, P r er ∉ core ∧ Q r er ∉ core ∧ P r er ∉ J.image ξ ∧
        Q r er ∉ J.image ξ) ∧
      (∀ I ∈ V, ψ I ∉ core ∧ ψ I ∉ J.image ξ ∧ ψ I ∉ evenFam) ∧
      (∀ h ∈ J, ∀ χ ∈ BB, X h χ = Xodd h χ) ∧
      (∀ χ ∈ BB, Y 0 χ = Yzero χ) ∧
      (∀ χ ∈ BB, c M M χ = Cmid χ) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, X (-(2 * (r : ZMod m))) χ = Xeven r χ) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, Y r χ = Yeven r χ) ∧
      (∀ r ∈ Finset.Ico 1 M, ∃ er : Fin 2, (∀ χ ∈ BB, c r r χ = Cdiag r er χ) ∧
        ∀ χ ∈ BB, c (r + M) (r + M) χ = Cdiag r (1 - er) χ) ∧
      (∀ I ∈ V, ∀ χ ∈ BB, c I.1 I.2 χ = Cgen I χ) ∧
      Rdet ∧
      (0 < deg χ₀ ∧ 0 < deg χ₁ ∧ 0 < deg χ₂ ∧ 0 < deg χ₃ ∧ 0 < deg χ₄) ∧
      0 < D ∧ 0 < Δ ∧
      (∀ h ∈ J, deg (ξ h) = D) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃) ∧
      (∀ I ∈ V, deg (ψ I) = Δ) ∧
      δ₀ * deg χ₀ + δ₁ * deg χ₁ = -(α * D) ∧ δ₂ * deg χ₂ + δ₃ * deg χ₃ = -(α * D) ∧
      δ₄ * deg χ₄ = δ₃ * deg χ₃ - δ₀ * deg χ₀ ∧ δ₄ * deg χ₄ = δ₁ * deg χ₁ - δ₂ * deg χ₂ ∧
      γ * Δ = δ₂ * deg χ₂ - δ₃ * deg χ₃ ∧ δ₂ * deg χ₂ - δ₃ * deg χ₃ ≠ 0 ∧
      BB = core ∪ J.image ξ ∪ evenFam ∪ V.image ψ ∧
      BB.card = (m ^ 2 + 12 * m + 8) / 6 := by
  subst hJ
  obtain ⟨δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ, χ₀, χ₁, χ₂, χ₃, χ₄, ξ, P, Q, ψ, D, Δ, hCS⟩ := hCS
  obtain ⟨hsigns, hcinj, hξinj, hPQ, hψinj, hξcore, hPQcore, hψfam, hexh, hcard, hXodd, hY0,
    hCmid, hXeven, hYeven, hdiag, hgen, hD, hΔ, hdξ, hdPQ, hdψ, e1, e2, e3, e4, e5, e6⟩ := hCS
  have hcore : ∀ x : BB, x.1 ∈ ({χ₀.1, χ₁.1, χ₂.1, χ₃.1, χ₄.1} : Finset ι) ↔
      x ∈ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset BB) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
  have hodd : ∀ x : BB, x.1 ∈ (oddIdx m).image (fun h => (ξ h).1) ↔
      x ∈ (oddIdx m).image ξ := by
    intro x
    simp only [Finset.mem_image, Subtype.ext_iff]
  have heven : ∀ x : BB, x.1 ∈ ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun y => (P y.1 y.2).1) ∪ ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun y => (Q y.1 y.2).1) ↔
      x ∈ ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun y => P y.1 y.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun y => Q y.1 y.2) := by
    intro x
    simp only [Finset.mem_union, Finset.mem_image, Subtype.ext_iff]
  refine ⟨δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ, χ₀.1, χ₁.1, χ₂.1, χ₃.1, χ₄.1, fun h => (ξ h).1,
    fun r e => (P r e).1, fun r e => (Q r e).1, fun I => (ψ I).1, D, Δ, ?_⟩
  intro Acol Kc Xodd Yzero Cmid Xeven Yeven Cdiag Cgen core evenFam
  refine ⟨hsigns, ?_, fun h hh h' hh' heq => hξinj hh hh' (Subtype.ext heq), ?_,
    fun I hI I' hI' heq => hψinj hI hI' (Subtype.ext heq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hRdet, ⟨hdeg _, hdeg _, hdeg _, hdeg _, hdeg _⟩, hD, hΔ, hdξ, hdPQ, hdψ, e1, e2, e3,
    e4, e5, e6, ?_, ?_⟩
  · have hv : (![χ₀.1, χ₁.1, χ₂.1, χ₃.1, χ₄.1] : Fin 5 → ι) =
        Subtype.val ∘ ![χ₀, χ₁, χ₂, χ₃, χ₄] := by
      funext t
      fin_cases t <;> rfl
    rw [hv]
    exact Subtype.val_injective.comp hcinj
  · intro r hr r' hr' e e'
    obtain ⟨h1, h2, h3⟩ := hPQ r hr r' hr' e e'
    exact ⟨fun heq => h1 (Subtype.ext heq), fun heq => h2 (Subtype.ext heq),
      fun heq => h3 (Subtype.ext heq)⟩
  · intro h hh hmem
    exact hξcore h hh ((hcore _).mp hmem)
  · intro r hr e
    obtain ⟨h1, h2, h3, h4⟩ := hPQcore r hr e
    exact ⟨fun hm => h1 ((hcore _).mp hm), fun hm => h2 ((hcore _).mp hm),
      fun hm => h3 ((hodd _).mp hm), fun hm => h4 ((hodd _).mp hm)⟩
  · intro I hI
    obtain ⟨h1, h2, h3⟩ := hψfam I hI
    exact ⟨fun hm => h1 ((hcore _).mp hm), fun hm => h2 ((hodd _).mp hm),
      fun hm => h3 ((heven _).mp hm)⟩
  · intro h hh χ hχ
    rw [hX _ (ColumnData.oddIdx_ne_zero hh) ⟨χ, hχ⟩, hXodd h hh]
    simp only [Pi.add_apply, single_subtype_apply, Xodd, Acol]
  · intro χ hχ
    have h := congrFun hY0 ⟨χ, hχ⟩
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, single_subtype_apply] at h
    rw [h]
    simp only [Yzero, Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
  · intro χ hχ
    rw [hc _ _ ⟨χ, hχ⟩, hCmid]
    simp only [Pi.add_apply, Pi.sub_apply, single_subtype_apply, Cmid, Kc]
  · intro r hr χ hχ
    rw [hX _ (neg_two_mul_ne_zero hm hr) ⟨χ, hχ⟩, hXeven r hr]
    simp only [Pi.add_apply, Pi.sub_apply, single_subtype_apply, Xeven, Acol]
  · intro r hr χ hχ
    have h := congrFun (hYeven r hr) ⟨χ, hχ⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, single_subtype_apply] at h
    rw [h]
    simp only [Yeven, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  · intro r hr
    obtain ⟨e, h1, h2⟩ := hdiag r hr
    refine ⟨e, fun χ hχ => ?_, fun χ hχ => ?_⟩
    · rw [hc _ _ ⟨χ, hχ⟩, h1]
      simp only [Pi.add_apply, Pi.sub_apply, single_subtype_apply, Cdiag, Kc]
    · rw [hc _ _ ⟨χ, hχ⟩, h2]
      simp only [Pi.add_apply, Pi.sub_apply, single_subtype_apply, Cdiag, Kc]
  · intro I hI χ hχ
    rw [hc _ _ ⟨χ, hχ⟩, hgen I hI]
    simp only [Pi.add_apply, Pi.sub_apply, single_subtype_apply, Cgen, Kc]


  · ext χ
    constructor
    · intro hχ
      have hmem : (⟨χ, hχ⟩ : BB) ∈ (Finset.univ : Finset BB) := Finset.mem_univ _
      rw [hexh] at hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl ((hcore ⟨χ, hχ⟩).mpr h)))
      · exact Or.inl (Or.inl (Or.inr ((hodd ⟨χ, hχ⟩).mpr h)))
      · exact Or.inl (Or.inr ((heven ⟨χ, hχ⟩).mpr (Finset.mem_union.mpr h)))
      · obtain ⟨I, hI, hIχ⟩ := Finset.mem_image.mp h
        exact Or.inr (Finset.mem_image.mpr ⟨I, hI, by rw [hIχ]⟩)
    · intro hχ
      simp only [core, evenFam, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
        Finset.mem_singleton] at hχ
      rcases hχ with (((h | h | h | h | h) | ⟨h', -, h⟩) | (⟨y, -, h⟩ | ⟨y, -, h⟩)) |
          ⟨I, -, h⟩
      all_goals first | (rw [h]; exact Subtype.prop _) | (rw [← h]; exact Subtype.prop _)
  · rw [← Fintype.card_coe BB, hcard]
end Support

end CFSG.Wreathed.FlatComplete
