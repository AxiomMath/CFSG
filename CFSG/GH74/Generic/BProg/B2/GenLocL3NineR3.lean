module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineTypes
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineAsm

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine
open scoped MatrixGroups Classical

namespace GenLocL3NineR3

variable {K : Type} [Field K]

@[expose] noncomputable def blkAct (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (m : Fin 3) : ↥D →* MulAut SL(2, K) :=
  (restM m).comp (toFrame D.subtype (by rw [Subgroup.range_subtype]; exact hfs))

@[expose] def GoodBlk (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (m : Fin 3) : Prop := gammaAct (blkAct D hfs m) = ⊤

theorem goodBlk_of_ker_not_inner [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) (m : Fin 3) (y : D) (hy1 : y ≠ 1)
    (hker : restM m ⟨(y : MulAut (LinearFlag.projectiveSL 3 K)), hfs y.2⟩ = 1)
    (hni : ¬ (blkAct D hfs m).range ≤ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range) :
    GoodBlk D hfs m := by
  have hK' : Nat.card K = 3 ^ 2 := by simpa using hK
  refine gammaAct_sl2_of_not_inner_small Nat.prime_three (by norm_num) hK' (by norm_num) _ hA hni ?_
  have hyker : y ∈ (blkAct D hfs m).ker := hker
  have h1 := Subgroup.card_mul_index (blkAct D hfs m).ker
  rw [Subgroup.index_ker, h8] at h1
  have hlt : 1 < Nat.card (blkAct D hfs m).ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨y, hyker⟩, fun h => hy1 (congrArg Subtype.val h)⟩
  have : Nat.card (blkAct D hfs m).range * 2 ≤ 8 := by
    calc Nat.card (blkAct D hfs m).range * 2 ≤ Nat.card (blkAct D hfs m).range *
          Nat.card (blkAct D hfs m).ker := Nat.mul_le_mul_left _ hlt
      _ = 8 := by rw [mul_comm]; exact h1
  omega

@[expose] def ShapeE3 (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) : Prop :=
  (∃ (y : D) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
    (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε ∧ σ ≠ 1) ∧
  (∃ z : D, z ≠ 1 ∧ (z : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K) ∧
  ∀ z z' : D, z ≠ 1 → z' ≠ 1 → (z : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K →
    (z' : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K → z = z'

@[expose] def ShapeE2 (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) : Prop :=
  (∀ (y : D) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 →
    (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε → σ = 1) ∧
  (∀ m : Fin 3, ∃ (z : D) (w : Fin 3 → Kˣ), z ≠ 1 ∧
    (z : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 w) ∧
      w (crd m 0) = w (crd m 1)) ∧
  ∃ (r : D) (v : Fin 3 → Kˣ), (r : MulAut (LinearFlag.projectiveSL 3 K)) =
    LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ 1 ∧
    ∀ m : Fin 3, IsSquare ((v (crd m 0) : K) * v (crd m 1))

theorem isSquare_of_mid (x y z : Kˣ) (h1 : IsSquare ((x : K) * y)) (h2 : IsSquare ((y : K) * z)) :
    IsSquare ((x : K) * z) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a * b / y, ?_⟩
  have hy : (y : K) ≠ 0 := y.ne_zero
  field_simp
  have : ((x : K) * y) * ((y : K) * z) = (a * a) * (b * b) := by rw [ha, hb]
  linear_combination this

theorem rank3_cases [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) :
    (∃ m m' : Fin 3, m ≠ m' ∧ GoodBlk D hfs m ∧ GoodBlk D hfs m') ∨ ShapeE3 D ∨ ShapeE2 D := by
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have : Fintype ↥D := Fintype.ofFinite _
  have hD := hA.1
  have hcardD : (Finset.univ : Finset ↥D).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h8]
  have hmul := card_le_mul_T1D D hK hfs hD
  rw [hcardD] at hmul
  have hne : ∀ (y : D) (w : Fin 3 → Kˣ), y ≠ 1 → (y : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 w) → LinearFlag.conjAut 3 K (diag3 w) ≠ 1 := by
    intro y w hy1 hyw h1
    apply hy1
    apply Subtype.ext
    rw [hyw, h1]; rfl
  by_cases hF : ∃ (y : D) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
        LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε ∧ σ ≠ 1
  · have himg : ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 4 := by
      calc _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_le_univ _
        _ = 4 := by simp
    have hT1 : 1 < (T1D D).card := by
      by_contra h
      push Not at h
      have : (T1D D).card * ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 1 * 4 :=
        Nat.mul_le_mul h himg
      omega
    obtain ⟨τ, hτ, hτ1⟩ := Finset.exists_mem_ne hT1 1
    by_cases h2 : ∃ z z' : D, z ≠ 1 ∧ z' ≠ 1 ∧ z ≠ z' ∧
        (z : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K ∧
        (z' : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K
    · left
      obtain ⟨z, z', hz1, hz1', hzz', hz, hz'⟩ := h2
      obtain ⟨m, u, hu, hm, hs⟩ := T1D_data D hD ((mem_T1D D).2 hz)
      obtain ⟨m', u', hu', hm', hs'⟩ := T1D_data D hD ((mem_T1D D).2 hz')
      have hmm' : m ≠ m' := by
        rintro rfl
        apply hzz'
        have e := eq_of_trivial_block m hs hs' hm hm' (hne z u hz1 hu) (hne z' u' hz1' hu')
        apply Subtype.ext
        rw [hu, hu', e]
      obtain ⟨y, u0, σ0, ε0, hε0, hy0, hσ0⟩ := hF
      have hni : ∀ m : Fin 3, ¬ (blkAct D hfs m).range ≤
          (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := fun m h =>
        rho_not_inner_of_field m (hfs y.2) hε0 hy0 hσ0 (h ⟨y, rfl⟩)
      exact ⟨m, m', hmm', goodBlk_of_ker_not_inner hK D hfs hA h8 m z hz1
          (rho_eq_one_of_eq m (hfs z.2) hu hm) (hni m),
        goodBlk_of_ker_not_inner hK D hfs hA h8 m' z' hz1'
          (rho_eq_one_of_eq m' (hfs z'.2) hu' hm') (hni m')⟩
    · right; left
      refine ⟨hF, ⟨τ, hτ1, (mem_T1D D).1 hτ⟩, fun z z' hz hz' hzd hz'd => ?_⟩
      by_contra hne'
      exact h2 ⟨z, z', hz, hz', hne', hzd, hz'd⟩
  push Not at hF
  have nd : ∀ y : D, (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ noDual K →
      (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K := by
    intro y hy
    obtain ⟨x, σ, hx, hax⟩ := hy
    obtain ⟨u, rfl⟩ := exists_diag3 hx
    have := hF y u σ 0 (Nat.zero_le 1) (by rw [pow_zero, mul_one]; exact hax)
    refine ⟨diag3 u, isDiag_diag3 u, ?_⟩
    rw [hax, this, map_one, mul_one]
  have himg : ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 2 := by
    have hsub : ((Finset.univ : Finset ↥D).image (typ D hfs)) ⊆
        ({(true, true), (true, false)} : Finset (Bool × Bool)) := by
      intro t ht
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨u, σ, ε, hε, hy, hty⟩ := typ_spec D hfs y
      have hσ := hF y u σ ε hε hy
      rw [hty]
      subst hσ
      by_cases h0 : ε = 0 <;> simp [h0]
    exact (Finset.card_le_card hsub).trans (by decide)
  have hT4 : 4 ≤ (T1D D).card := by
    by_contra h
    push Not at h
    have : (T1D D).card * ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 3 * 2 :=
      Nat.mul_le_mul (by omega) himg
    omega
  have hT4' : (T1D D).card = 4 := le_antisymm (card_T1D_le D hD) hT4
  have hK3 : ∀ m : Fin 3, ∃ (z : D) (w : Fin 3 → Kˣ), z ≠ 1 ∧
      (z : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 w) ∧
        w (crd m 0) = w (crd m 1) := by
    intro m
    obtain ⟨z, hz, hzm⟩ := exists_T1_block D hD hT4' m
    obtain ⟨u, hu, hm, -⟩ := blockFun_spec D hD (Finset.mem_erase.1 hz).2
    rw [hzm] at hm
    exact ⟨z, u, (Finset.mem_erase.1 hz).1, hu, hm⟩
  obtain ⟨r, hr⟩ : ∃ r : D, (r : MulAut (LinearFlag.projectiveSL 3 K)) ∉ noDual K := by
    by_contra h
    push Not at h
    have : T1D D = Finset.univ :=
      Finset.eq_univ_of_forall fun z => (mem_T1D D).2 (nd z (h z))
    rw [this, hcardD] at hT4'
    omega
  obtain ⟨v, σ, ε, hε, hrv⟩ := exists_data (hfs r.2)
  have hσ := hF r v σ ε hε hrv
  have hε1 : ε = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · exact absurd ⟨diag3 v, σ, isDiag_diag3 v, by rw [hrv, pow_zero, mul_one]⟩ hr
    · rfl
  subst hσ hε1
  by_cases h2 : ∃ m m' : Fin 3, m ≠ m' ∧ ¬ IsSquare ((v (crd m 0) : K) * v (crd m 1)) ∧
      ¬ IsSquare ((v (crd m' 0) : K) * v (crd m' 1))
  · left
    obtain ⟨m, m', hmm', hs, hs'⟩ := h2
    have hni : ∀ m : Fin 3, ¬ IsSquare ((v (crd m 0) : K) * v (crd m 1)) →
        ¬ (blkAct D hfs m).range ≤ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range :=
      fun m hs h => hs (isSquare_of_rho_inner m (hfs r.2) le_rfl hrv (h ⟨r, rfl⟩))
    obtain ⟨z, wz, hz1, hzw, hzm⟩ := hK3 m
    obtain ⟨z', wz', hz1', hzw', hzm'⟩ := hK3 m'
    exact ⟨m, m', hmm',
      goodBlk_of_ker_not_inner hK D hfs hA h8 m z hz1 (rho_eq_one_of_eq m (hfs z.2) hzw hzm) (hni m hs),
      goodBlk_of_ker_not_inner hK D hfs hA h8 m' z' hz1' (rho_eq_one_of_eq m' (hfs z'.2) hzw' hzm')
        (hni m' hs')⟩
  · right; right
    refine ⟨hF, hK3, r, v, hrv, fun m => ?_⟩
    by_contra hm
    have key : ∀ m' : Fin 3, m' ≠ m → IsSquare ((v (crd m' 0) : K) * v (crd m' 1)) := by
      intro m' hne'
      by_contra hm'
      exact h2 ⟨m, m', hne'.symm, hm, hm'⟩
    fin_cases m
    · have h1 := key 1 (by decide)
      have h2' := key 2 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 1) (v 0) (v 2) (by simpa [mul_comm] using h2') h1)
    · have h1 := key 0 (by decide)
      have h2' := key 2 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 0) (v 1) (v 2) h2' h1)
    · have h1 := key 0 (by decide)
      have h2' := key 1 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 0) (v 2) (v 1) h2' (by simpa [mul_comm] using h1))

@[expose] def ExcE3 (K : Type) [Field K] : Prop :=
  ∀ (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K), IsRank23 ↥D →
    Nat.card ↥D = 8 → ShapeE3 D → gammaAct D.subtype = ⊤

@[expose] def ExcE2 (K : Type) [Field K] : Prop :=
  ∀ (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K), IsRank23 ↥D →
    Nat.card ↥D = 8 → ShapeE2 D → gammaAct D.subtype = ⊤

theorem rank3_of_exc [Finite K] (hK : Nat.card K = 9) (hE3 : ExcE3 K)
    (hE2 : ExcE2 K) : Rank3 K := by
  intro D hfs hA h8
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  rcases rank3_cases hK D hfs hA h8 with ⟨m, m', hmm', h, h'⟩ | h3 | h2
  · exact gammaAct_eq_top_of_two_good D.subtype hα hmm' h h'
  · exact hE3 D hfs hA h8 h3
  · exact hE2 D hfs hA h8 h2

end GenLocL3NineR3

end CFSG.GH74.Generic.BProg.B2
