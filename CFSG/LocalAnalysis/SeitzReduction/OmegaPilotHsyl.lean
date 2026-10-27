module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHsylBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace mem_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section General

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b a₂ b₂ a₃ b₃ : Fin d}

theorem exists_card_eq_two_pow [Finite K] [CharP K 2] : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem IsHypCoord.pairTorusOf_le_centralizer_pairPerpOf (h : IsHypCoord Q a b) :
    pairTorusOf Q a b ≤ centralizer (pairPerpOf Q a b : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨y, ⟨c, hc⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) * y = y * z
  have hc1 : torusLin a b c = (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hc
  rw [← hc1]
  exact h.commute_torusLin_of_mem_stabSub (Subgroup.commutator_le_self _ z.2) hz c

theorem IsHypCoord.linearEquiv_ext (h : IsHypCoord Q a b) {g g' : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (ha : g (Pi.single a 1) = g' (Pi.single a 1)) (hb : g (Pi.single b 1) = g' (Pi.single b 1))
    (hU : ∀ x ∈ perpSub K a b, g x = g' x) : g = g' := by
  apply LinearEquiv.ext
  intro x
  rw [eq_add_perpPart a b x, map_add, map_add, map_smul, map_smul, ha, hb,
    hU _ (perpPart_mem h.ne x), map_add, map_add, map_smul, map_smul]

variable [Finite K] [CharP K 2]

theorem exists_mem_pairTorusOf_eq_conj (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    (hq : 3 ≤ Nat.card K) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q) (hX : ∀ x ∈ pairTorusOf Q a b, β x = x)
    (hD : ∀ x ∈ pairPerpOf Q a b, β x = x) :
    ∃ x ∈ pairTorusOf Q a b, β = MulAut.conj x := by
  have hT := exists_threeSingular_of_isHypCoord h h₂ h₃ d₂ d₃ d₂₃
  have hQ' := h.exists_ne_zero
  obtain ⟨g, rfl⟩ := hβE
  obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) hq
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a b := h₂.hypPair_mem_perpSub d₂
  have hDcomm : ∀ u ∈ perpSub K a b, ∀ w ∈ perpSub K a b, ∀ x,
      simMap g (eichler Q u w x) = eichler Q u w (simMap g x) := by
    intro u hu w hw x
    exact commute_of_kappa_projHom_eq hQ' g
      (E := ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩)
      (hD _ ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, h.eichler_mem_stabSub hu hw,
        rfl⟩) x
  have hXcomm : ∀ x, simMap g (torusLin a b c₀ x) = torusLin a b c₀ (simMap g x) :=
    commute_of_kappa_projHom_eq hQ' g (E := ⟨torusLin a b c₀, h.torusLin_mem_orthDerived c₀⟩)
      (hX _ ⟨_, ⟨c₀, rfl⟩, rfl⟩)
  obtain ⟨-, γ, α, hγ0, hφ⟩ := eq_smul_torusLin_of_commute hQ h h₂ h₃ d₂ d₃ d₂₃
    (Units.ne_zero (multiplier Q g)) (simMap_smul g) (map_simMap g)
    (fun w hw _ x => hDcomm _ hu₂.1 w hw x) (fun w hw _ x => hDcomm _ hu₂.2 w hw x) hc₀ hXcomm
  exact ⟨projHom Q ⟨torusLin a b α, h.torusLin_mem_orthDerived α⟩, ⟨_, ⟨α, rfl⟩, rfl⟩,
    kappa_eq_conj_of_eq_smul g _ hγ0 hφ⟩

theorem eq_one_of_two_pow_fix_pairTorusOf (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    (hq : 3 ≤ Nat.card K) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q) {m : ℕ} (hβ : β ^ 2 ^ m = 1)
    (hX : ∀ x ∈ pairTorusOf Q a b, β x = x) (hD : ∀ x ∈ pairPerpOf Q a b, β x = x) : β = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_pairTorusOf_eq_conj hQ h h₂ h₃ d₂ d₃ d₂₃ hq hβE hX hD
  obtain ⟨f, hK⟩ := exists_card_eq_two_pow (K := K)
  have hodd := odd_card_pairTorusOf h hK
  have hx1 : x ^ Nat.card (pairTorusOf Q a b) = 1 := by
    have h1 := pow_card_eq_one' (G := pairTorusOf Q a b) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val h1
  have h1 : MulAut.conj x ^ Nat.card (pairTorusOf Q a b) = 1 := by rw [← map_pow, hx1, map_one]
  have hcop : Nat.Coprime (2 ^ m) (Nat.card (pairTorusOf Q a b)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hβ)
    (orderOf_dvd_of_pow_eq_one h1))

theorem centralizer_pairPerpOf (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃) :
    centralizer (pairPerpOf Q a b : Set (matrixProjectiveDerived Q)) = pairTorusOf Q a b := by
  refine le_antisymm (fun z hz => ?_) h.pairTorusOf_le_centralizer_pairPerpOf
  have hT := exists_threeSingular_of_isHypCoord h h₂ h₃ d₂ d₃ d₂₃
  have hQ' := h.exists_ne_zero
  obtain ⟨g, rfl⟩ := projHom_surjective Q z
  set G := (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) with hG
  have hgO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ g.2
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a b := h₂.hypPair_mem_perpSub d₂
  have hcomm : ∀ u ∈ perpSub K a b, ∀ w ∈ perpSub K a b, ∀ x,
      G (eichler Q u w x) = eichler Q u w (G x) := by
    intro u hu w hw x
    have h1 := mem_centralizer_iff.mp hz _
      ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, h.eichler_mem_stabSub hu hw, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg (fun A : orthDerived Q => (A : (Fin d → K) ≃ₗ[K] (Fin d → K)) x)
      (projHom_injective hQ' h1)
    exact h2.symm
  obtain ⟨-, ⟨γ, -, hgγ⟩, hea, heb⟩ := eq_smul_on_perpSub_of_commute (φ := G.toAddEquiv)
    (σ := RingEquiv.refl K) (μ := 1) hQ h h₂ h₃ d₂ d₃ d₂₃ one_ne_zero (fun c x => by simp)
    (fun x => by simp [map_of_mem hgO]) (fun w hw _ x => hcomm _ hu₂.1 w hw x)
    (fun w hw _ x => hcomm _ hu₂.2 w hw x)
  have hgγ' : ∀ x ∈ perpSub K a b, G x = γ • x := hgγ
  have hea' : G (Pi.single a 1) = G (Pi.single a 1) a • Pi.single a 1 +
      G (Pi.single a 1) b • Pi.single b 1 := hea
  have heb' : G (Pi.single b 1) = G (Pi.single b 1) a • Pi.single a 1 +
      G (Pi.single b 1) b • Pi.single b 1 := heb
  have hγ : γ = 1 := by
    apply eq_one_of_mul_self_eq_one
    have h1 := map_of_mem hgO (Pi.single a₂ 1 + Pi.single b₂ 1)
    rw [hgγ' _ ((perpSub K a b).add_mem hu₂.1 hu₂.2), map_smul_eq_sq, h₂.map_single_add] at h1
    linear_combination h1
  have hGU : ∀ x ∈ perpSub K a b, G x = x := fun x hx => by rw [hgγ' x hx, hγ, one_smul]
  set s := G (Pi.single a 1) a with hs
  set t := G (Pi.single a 1) b with ht
  set s'' := G (Pi.single b 1) a with hs''
  set s' := G (Pi.single b 1) b with hs'
  have hQW : ∀ x y : K, Q (x • Pi.single a 1 + y • Pi.single b 1) = x * y := by
    intro x y
    have := h.map_add_smul x y (p := 0) rfl rfl
    simpa using this
  have hpolW : ∀ x y x' y' : K, polar Q (x • Pi.single a 1 + y • Pi.single b 1)
      (x' • Pi.single a 1 + y' • Pi.single b 1) = x * y' + y * x' := by
    intro x y x' y'
    rw [polar_add_left, polar_smul_left, polar_smul_left, h.polar_left, h.polar_right]
    simp [h.ne, h.ne.symm]
  have hst : s * t = 0 := by
    have h1 := map_of_mem hgO (Pi.single a 1)
    rw [hea', hQW, h.map_left] at h1
    exact h1
  have hs's'' : s'' * s' = 0 := by
    have h1 := map_of_mem hgO (Pi.single b 1)
    rw [heb', hQW, h.map_right] at h1
    exact h1
  have hB : s * s' + t * s'' = 1 := by
    have h1 := polar_map_of_mem hgO (Pi.single a 1) (Pi.single b 1)
    rw [hea', heb', hpolW, h.polar_left, Pi.single_eq_same] at h1
    exact h1
  by_cases ht0 : t = 0
  ·
    have hss' : s * s' = 1 := by rw [ht0, zero_mul, add_zero] at hB; exact hB
    have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hss'
    have hs'0 : s' ≠ 0 := right_ne_zero_of_mul_eq_one hss'
    have hs''0 : s'' = 0 := (mul_eq_zero.mp hs's'').resolve_right hs'0
    refine ⟨g, ⟨Units.mk0 s hs0, ?_⟩, rfl⟩
    change torusLin a b (Units.mk0 s hs0) = G
    refine h.linearEquiv_ext ?_ ?_ fun x hx => ?_
    · rw [torusLin_single_left h.ne, hea', ht0, zero_smul, add_zero, Units.val_mk0]
    · rw [torusLin_single_right h.ne, heb', hs''0, zero_smul, zero_add, Units.val_inv_eq_inv_val,
        Units.val_mk0, eq_inv_of_mul_eq_one_right hss']
    · rw [torusLin_eq_self_of hx.1 hx.2, hGU x hx]
  ·
    exfalso
    have hs0 : s = 0 := (mul_eq_zero.mp hst).resolve_right ht0
    have hts'' : t * s'' = 1 := by rw [hs0, zero_mul, zero_add] at hB; exact hB
    have hs''0 : s'' ≠ 0 := right_ne_zero_of_mul_eq_one hts''
    have hs'0 : s' = 0 := (mul_eq_zero.mp hs's'').resolve_left hs''0
    set v₀ : Fin d → K := Pi.single a 1 - t • Pi.single b 1 with hv₀
    have hv₀0 : v₀ ≠ 0 := by
      intro h0
      have := congrFun h0 a
      simp [hv₀, h.ne] at this
    have hcs : commSpace G = K ∙ v₀ := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [Submodule.mem_span_singleton]
        refine ⟨x b * s'' - x a, ?_⟩
        change _ = G x - x
        have hp := perpPart_mem h.ne x
        conv_rhs => rw [eq_add_perpPart a b x]
        rw [map_add, map_add, map_smul, map_smul, hea', heb', hGU _ hp, hs0, hs'0, hv₀,
          eq_inv_of_mul_eq_one_right hts'']
        have ht' : t ≠ 0 := ht0
        match_scalars <;> field_simp <;> ring
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine mem_commSpace.mpr ⟨-Pi.single a 1, ?_⟩
        rw [map_neg, hea', hs0, zero_smul, zero_add, hv₀]
        abel
    have hev := (mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ g.2)).2
    rw [hcs, finrank_span_singleton hv₀0] at hev
    exact Nat.not_even_one hev

end General

section Coordinates

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizer_pairPerp {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    centralizer (pairPerp (K := K) k : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) =
      pairTorus k := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne hn k
  exact centralizer_pairPerpOf (regular_coordinateQuadPlus n K hn).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij)

theorem centralizer_minusPairPerp {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    centralizer (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) =
      minusPairTorus (by omega) b c k := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  exact centralizer_pairPerpOf (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij)

theorem exists_mem_pairTorus_eq_conj (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    ∃ x ∈ pairTorus (K := K) k, β = MulAut.conj x := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n) k
  refine exists_mem_pairTorusOf_eq_conj (regular_coordinateQuadPlus n K (by omega)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) (by omega) ?_ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
  exact Subgroup.mem_top β

theorem eq_one_of_two_pow_fix_pairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} {m : ℕ} (hβ : β ^ 2 ^ m = 1)
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    β = 1 := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n) k
  refine eq_one_of_two_pow_fix_pairTorusOf (regular_coordinateQuadPlus n K (by omega)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) (by omega) ?_ hβ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
  exact Subgroup.mem_top β

theorem exists_mem_minusPairTorus_eq_conj (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hX : ∀ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β x = x)
    (hD : ∀ x ∈ minusPairPerp (K := K) (one_le_of_four_le hn) b c k, β x = x) :
    ∃ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β = MulAut.conj x := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  refine exists_mem_pairTorusOf_eq_conj (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij) (by omega) ?_ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

theorem eq_one_of_two_pow_fix_minusPairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))} {m : ℕ}
    (hβ : β ^ 2 ^ m = 1) (hX : ∀ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β x = x)
    (hD : ∀ x ∈ minusPairPerp (K := K) (one_le_of_four_le hn) b c k, β x = x) : β = 1 := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  refine eq_one_of_two_pow_fix_pairTorusOf (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij) (by omega) ?_ hβ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

end Coordinates

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem eq_one_of_fix_map_of_mulEquiv (e : L ≃* C) {XC DC : Subgroup C}
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1) :
    ∀ β : MulAut L,
      (∀ a : L, (a : G) ∈ (XC.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      (∀ a : L, (a : G) ∈ (DC.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hβX hβD m hβm
  have hmem : ∀ {YC : Subgroup C} {x : C}, x ∈ YC →
      ((e.symm x : L) : G) ∈ (YC.map e.symm.toMonoidHom).map L.subtype :=
    fun {YC} {x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have key : MulAut.congr e β = 1 := by
    refine hC _ (fun x hx => ?_) (fun x hx => ?_) m ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβm, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem mem_of_odd_of_commute_of_mulEquiv [Finite C] (e : L ≃* C) {XC DC : Subgroup C}
    (hodd : Odd (Nat.card XC))
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∃ x ∈ XC, β = MulAut.conj x)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ c ∈ centralizer (((XC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ⊓
        centralizer (((DC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      Odd (orderOf c) → c ∈ (XC.map e.symm.toMonoidHom).map L.subtype := by
  intro c ⟨⟨hcX, hct⟩, hcD⟩ hco
  set β : MulAut L := L.normalizerMonoidHom ⟨c, hCtN hct⟩ with hβdef
  have hβ : ∀ l : L, ((β l : L) : G) = c * l * c⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨c, hCtN hct⟩ l
  have hmem : ∀ {YC : Subgroup C} {x : C}, x ∈ YC →
      ((e.symm x : L) : G) ∈ (YC.map e.symm.toMonoidHom).map L.subtype :=
    fun {YC} {x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have hfix : ∀ {YC : Subgroup C},
      c ∈ centralizer (((YC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) →
      ∀ x ∈ YC, MulAut.congr e β x = x := by
    intro YC hc x hx
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have h1 : β (e.symm x) = e.symm x := by
      apply Subtype.ext
      rw [hβ, ← mem_centralizer_iff.mp hc _ (hmem hx), mul_inv_cancel_right]
    rw [h1, MulEquiv.apply_symm_apply]
  obtain ⟨x₀, hx₀, hβx₀⟩ := hC _ (hfix hcX) (hfix hcD)
  set l₀ : G := ((e.symm x₀ : L) : G) with hl₀
  have hxl : ∀ y ∈ L, c * y * c⁻¹ = l₀ * y * l₀⁻¹ := by
    intro y hy
    have h1 : β = MulAut.conj (e.symm x₀) := by
      apply (MulAut.congr e).injective
      rw [hβx₀]
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have h2 := congrArg (fun γ : MulAut L => ((γ ⟨y, hy⟩ : L) : G)) h1
    simp only [hβ, MulAut.conj_apply] at h2
    rw [h2]
    rfl
  rcases F4Pilot.eq_or_eq_mul_of_conj_eq htC ht hK hct (e.symm x₀).2 hxl with h | h
  · rw [h]
    exact hmem hx₀
  · exfalso
    have hl₀o : Odd (orderOf l₀) := by
      have h1 : orderOf l₀ = orderOf x₀ := by
        rw [hl₀, orderOf_submonoid, MulEquiv.orderOf_eq]
      have h2 : orderOf x₀ ∣ Nat.card XC := by
        have h3 := orderOf_dvd_natCard (⟨x₀, hx₀⟩ : XC)
        rw [← Subgroup.orderOf_coe] at h3
        exact h3
      rw [h1]
      exact hodd.of_dvd_nat h2
    have hcomm : Commute l₀ t := mem_centralizer_iff.mp htC l₀ (e.symm x₀).2
    set N := orderOf c * orderOf l₀ with hN
    have hNo : Odd N := hco.mul hl₀o
    have hcN : c ^ N = 1 := by rw [hN, pow_mul, pow_orderOf_eq_one, one_pow]
    have hlN : l₀ ^ N = 1 := by rw [hN, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have htN : t ^ N = t := by
      obtain ⟨k, hk⟩ := hNo
      have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
      rw [hk, pow_succ, pow_mul, ht2, one_pow, one_mul]
    have h1 : t = 1 := by
      have := hcN
      rw [h, hcomm.mul_pow, hlN, one_mul, htN] at this
      exact this
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

end Transport

section TransportCoordinates

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_fix_map_pairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {X D : Subgroup G}
    (hXe : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ a : L, (a : G) ∈ X → β a = a) → (∀ a : L, (a : G) ∈ D → β a = a) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  subst hXe hDe
  exact eq_one_of_fix_map_of_mulEquiv e fun β hX hD m hβ =>
    eq_one_of_two_pow_fix_pairTorus hq hn k hβ hX hD

theorem card_le_two_of_pairTorus [Finite G] {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ht : orderOf t = 2)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {X D : Subgroup G}
    (hXe : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hK ht
    (eq_one_of_fix_map_pairTorus hq hn k e hXe hDe) hU hUC

theorem mem_of_odd_of_commute_pairTorus {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {X D : Subgroup G}
    (hXe : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  subst hXe hDe
  obtain ⟨f, hKf⟩ := exists_card_eq_two_pow (K := K)
  exact mem_of_odd_of_commute_of_mulEquiv e (odd_card_pairTorus hKf k)
    (fun β hX hD => exists_mem_pairTorus_eq_conj hq hn k hX hD) htC ht hCtN hK

theorem eq_one_of_fix_map_minusPairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_four_le hn) b c))
    {X D : Subgroup G}
    (hXe : X = ((minusPairTorus (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((minusPairPerp (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ a : L, (a : G) ∈ X → β a = a) → (∀ a : L, (a : G) ∈ D → β a = a) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  subst hXe hDe
  exact eq_one_of_fix_map_of_mulEquiv e fun β hX hD m hβ =>
    eq_one_of_two_pow_fix_minusPairTorus hq hn hirr k hβ hX hD

theorem card_le_two_of_minusPairTorus [Finite G] {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ht : orderOf t = 2)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_four_le hn) b c))
    {X D : Subgroup G}
    (hXe : X = ((minusPairTorus (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((minusPairPerp (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hK ht
    (eq_one_of_fix_map_minusPairTorus hq hn hirr k e hXe hDe) hU hUC

theorem mem_of_odd_of_commute_minusPairTorus {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_four_le hn) b c))
    {X D : Subgroup G}
    (hXe : X = ((minusPairTorus (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((minusPairPerp (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype) :
    ∀ x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf x) → x ∈ X := by
  subst hXe hDe
  obtain ⟨f, hKf⟩ := exists_card_eq_two_pow (K := K)
  exact mem_of_odd_of_commute_of_mulEquiv e (odd_card_minusPairTorus hKf _ b c k)
    (fun β hX hD => exists_mem_minusPairTorus_eq_conj hq hn hirr k hX hD) htC ht hCtN hK

end TransportCoordinates

end CFSG.SeitzReduction.OmegaPilot
