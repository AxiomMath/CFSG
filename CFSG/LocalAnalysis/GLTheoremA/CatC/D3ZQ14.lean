module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ13
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ11
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ7

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Common

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem eq_one_of_mul_self_radical {q : ModGL τ K} (hq : q ∈ parabolicRadical τ K J) (h : q * q = 1) :
    q = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ K J
  have hP := (hfin 3).2.1
  by_contra hne
  have h3 : (3 : ℕ) ∣ orderOf (⟨q, hq⟩ : parabolicRadical τ K J) :=
    hP.dvd_orderOf (fun h' => hne (congrArg Subtype.val h'))
  have h2 : orderOf (⟨q, hq⟩ : parabolicRadical τ K J) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    show q ^ 2 = 1
    rw [sq]; exact h
  have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
  omega

theorem conj_eq_of_radical_sq {q : ModGL τ K} (hq : q ∈ parabolicRadical τ K J)
    (hsq : ∀ x ∈ adjointGroup τ K, q * q * x * (q * q)⁻¹ = x) {x : ModGL τ K}
    (hx : x ∈ adjointGroup τ K) : q * x * q⁻¹ = x := by
  have hqd : q ∈ degSeries τ K J 1 := by rw [degSeries_one]; exact hq
  have hqC : q ∈ adjointGroup τ K := degSeries_le_adjointGroup (K := K) (J := J) 1 hqd
  have hcen : (⟨q * q, mul_mem hqC hqC⟩ : adjointGroup τ K) ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hsq g.1 g.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g : ModGL τ K) * (q * q) = ((q * q) * g * (q * q)⁻¹) * (q * q) := by rw [this]
      _ = (q * q) * g := by group
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcen
  have h1 : q * q = 1 := congrArg Subtype.val hcen
  have := eq_one_of_mul_self_radical hq h1
  rw [this]; group

end Common

section J013

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem rootChar_J013 (b' : Fin Tag.D4.rank → Kˣ) (h0 : b' 0 = 1) (h1 : b' 1 = 1) (h3 : b' 3 = 1)
    (γ : Fin Tag.D4.rank → ℤ) : rootChar b' γ = b' 2 ^ γ 2 := by
  unfold rootChar
  have h : (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [h0, h1, h3]

theorem nonempty_layer_J013_one :
    Nonempty (degLayerRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 1) := by
  have h8 : (degLayerRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 1).ncard = 8 :=
    ncard_layer_J013_one
  have h : (degLayerRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 1).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h8]; norm_num)
  obtain ⟨x, hx⟩ := h
  exact ⟨⟨x, hx⟩⟩

local notation "Jout" => ({0, 1, 3} : Set (Fin Tag.D4.rank))

theorem J013_not_typeS (hK2 : ringChar K ≠ 2) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ : ModGL Tag.D4 K} (G : A4Grp Jout φ Γ₁ Γ₂)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {q : ModGL Tag.D4 K} (hq : q ∈ parabolicRadical Tag.D4 K Jout) {b' : Fin Tag.D4.rank → Kˣ}
    (h0 : b' 0 = 1) (h1 : b' 1 = 1) (h3 : b' 3 = 1) (hΓ : Γ₁ = q * rootDiagUnit Tag.D4 b') :
    False := by
  have hd : (1 : ℤ) ≤ 1 := le_rfl
  obtain ⟨i₀⟩ := nonempty_layer_J013_one
  have hq' : NormAll Jout q := NormAll.of_radical hq
  have hT : ∀ z, lconj G.n₁ hd z = conjL b' hd z := by
    intro z
    calc lconj G.n₁ hd z = lconj (hq'.mul (NormAll.of_rootDiagUnit b')) hd z :=
          lconj_congr G.n₁ _ (by rw [hΓ]) hd z
      _ = lconj hq' hd (lconj (NormAll.of_rootDiagUnit b') hd z) := lconj_mul hq' _ hd z
      _ = conjL b' hd z := by rw [lconj_radical hq hd]; rfl
  have hχ : ∀ i : degLayerRoots Tag.D4 Jout 1, ((rootChar b' i.1 : Kˣ) : K) = ((b' 2 : Kˣ) : K) := by
    intro i
    have hdeg := (mem_degLayerRoots.1 i.2).2
    have hdeg2 : (i.1 : Fin Tag.D4.rank → ℤ) 2 = 1 := (parabolicDegree_J013 i.1).symm.trans hdeg
    rw [rootChar_J013 b' h0 h1 h3, hdeg2, zpow_one]
  have hcoord : ∀ c : degLayerRoots Tag.D4 Jout 1 → K, lconj G.n₁ hd (coordMap hd c) =
      coordMap hd (fun i => ((b' 2 : Kˣ) : K) * c i) := by
    intro c
    rw [hT, conjL_coordMap]
    congr 1
    funext i
    rw [hχ]
  have hinj := (coordMap_bijective (τ := Tag.D4) (K := K) (J := Jout) hd).1
  have hsq : ((b' 2 : Kˣ) : K) * ((b' 2 : Kˣ) : K) = 1 := by
    have h := G.layer_inv₁ hd (coordMap hd (Pi.single i₀ 1))
    rw [hcoord, hcoord] at h
    have h' := congrFun (hinj h) i₀
    simpa using h'
  rcases mul_self_eq_one_iff.1 hsq with hε | hε
  ·
    have hb2 : b' 2 = 1 := Units.ext (by simpa using hε)
    have hb' : b' = 1 := by
      funext k
      have h4 : ∀ k : Fin Tag.D4.rank, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
      rcases h4 k with rfl | rfl | rfl | rfl <;> simp [h0, h1, hb2, h3]
    have hΓq : Γ₁ = q := by rw [hΓ, hb', rootDiagUnit_one, mul_one]
    obtain ⟨x, hx, hxne⟩ := hne₁
    refine hxne ?_
    rw [hΓq]
    exact conj_eq_of_radical_sq hq (fun y hy => by rw [← hΓq]; exact G.sq₁ y hy) hx
  ·
    have hT1 : ∀ z, lconj G.n₁ hd z = -z := by
      intro z
      obtain ⟨c, rfl⟩ := (coordMap_bijective (τ := Tag.D4) (K := K) (J := Jout) hd).2 z
      rw [hcoord, ← map_neg]
      congr 1
      funext i
      rw [hε]; simp
    have hB := G.layerB hd
    have hT2 : ∀ w, lconj G.n₂ hd w = -w := by
      intro w
      obtain ⟨z, rfl⟩ := (G.layerB hd).surjective w
      rw [← G.layer_B₁ hd, hT1, map_neg]
    have hz : ∀ z, G.layerB hd z = 0 := by
      intro z
      have e1 := G.layer_B₂ hd z
      rw [hT2, map_neg, hT2, map_neg, hT1, neg_neg] at e1
      have e2 : (2 : ZMod 3) • G.layerB hd z = 0 := by
        rw [two_smul]
        have : G.layerB hd z + G.layerB hd z = 0 := by
          nth_rewrite 1 [← e1]; abel
        exact this
      exact eq_zero_of_two_smul e2
    have hBz : G.layerB hd (coordMap hd (Pi.single i₀ (1 : K))) = G.layerB hd 0 := by
      rw [hz, map_zero]
    have h0' : coordMap hd (Pi.single i₀ (1 : K)) = 0 := (G.layerB hd).injective hBz
    have h00 := congrFun (hinj (h0'.trans (map_zero _).symm)) i₀
    simp at h00

theorem J013_card_fix (hK2 : ringChar K ≠ 2) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ c₁ : ModGL Tag.D4 K} {a₁ : Fin Tag.D4.rank → Kˣ} (G : A4Grp Jout φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K Jout) (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x) :
    Nat.card (fixSp (lconj G.n₁ (le_refl (1 : ℤ))) ⊓ fixSp (lconj G.n₂ (le_refl (1 : ℤ))) :
        Submodule (ZMod 3) (Lyr (isLayer_degSeries (K := K) (J := Jout) (le_refl (1 : ℤ))))) ^ 4 ≤
      Nat.card (Lyr (isLayer_degSeries (K := K) (J := Jout) (le_refl (1 : ℤ)))) := by
  have hΓ2 : ∀ x ∈ parabolicLevi Tag.D4 K Jout,
      (c₁ * rootDiagUnit Tag.D4 a₁) * (c₁ * rootDiagUnit Tag.D4 a₁) * x *
        ((c₁ * rootDiagUnit Tag.D4 a₁) * (c₁ * rootDiagUnit Tag.D4 a₁))⁻¹ = x := fun x hx => by
    rw [← hΓ₁]; exact G.sq₁ x (parabolicLevi_le_adjointGroup _ _ _ hx)
  rcases gamma_dichotomy_three hK2 hc₁ a₁ hΓ2 with ⟨y, q, hy, hq, hyeq⟩ | ⟨q, hq, b', h0, h1, h3, hΓeq⟩
  · refine G.card_fix_le (le_refl (1 : ℤ)) ?_
    have := card_fix_sq_of_N G.n₁ hy hq (by rw [hΓ₁]; exact hyeq) (le_refl (1 : ℤ))
      (by decide : Odd (1 : ℤ)) (fun x hx => G.sq₁ x (degSeries_le_adjointGroup 1 hx))
    exact this.le
  · exact (J013_not_typeS hK2 G hne₁ hq h0 h1 h3 (by rw [hΓ₁]; exact hΓeq)).elim

theorem J013_card_A (hK2 : ringChar K ≠ 2) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ c₁ : ModGL Tag.D4 K} {a₁ : Fin Tag.D4.rank → Kˣ} (G : A4Grp Jout φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K Jout) (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {A : Subgroup (ModGL Tag.D4 K)} (hA : A ≤ parabolicRadical Tag.D4 K Jout)
    (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a) (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a) :
    Nat.card A ≤ Nat.card K ^ 3 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hd1 : (1 : ℤ) ≤ 1 := le_refl 1
  have hd2 : (1 : ℤ) ≤ 2 := by norm_num
  have hL1 := isLayer_degSeries (K := K) (J := Jout) hd1
  have hL2 := isLayer_degSeries (K := K) (J := Jout) hd2
  have hfix := J013_card_fix hK2 G hc₁ hΓ₁ hne₁
  have hL1card : Nat.card (Lyr hL1) = Nat.card K ^ 8 := by
    rw [card_layer hd1]
    have h8 : (degLayerRoots Tag.D4 Jout 1).ncard = 8 := ncard_layer_J013_one
    rw [h8]
  have hL2card : Nat.card (Lyr hL2) = Nat.card K := by
    rw [card_layer hd2]
    have h1 : (degLayerRoots Tag.D4 Jout 2).ncard = 1 := ncard_layer_J013_two
    rw [h1, pow_one]
  have hS1 : Nat.card (fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
      Submodule (ZMod 3) (Lyr hL1)) ≤ Nat.card K ^ 2 := by
    have h4 : Nat.card (fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
        Submodule (ZMod 3) (Lyr hL1)) ^ 4 ≤ (Nat.card K ^ 2) ^ 4 := by
      calc _ ≤ Nat.card (Lyr hL1) := hfix
        _ = (Nat.card K ^ 2) ^ 4 := by rw [hL1card, ← pow_mul]
    exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).1 h4
  have hAH : A ⊓ degSeries Tag.D4 K Jout 1 = A := inf_eq_left.2 (by rwa [degSeries_one])
  have hmem1 : ∀ a (ha : a ∈ A) (haH : a ∈ degSeries Tag.D4 K Jout 1),
      Lyr.mk hL1 ⟨a, haH⟩ ∈ ((fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
        Submodule (ZMod 3) (Lyr hL1)) : Set (Lyr hL1)) := by
    intro a ha haH
    refine ⟨mem_fixSp.2 ?_, mem_fixSp.2 ?_⟩
    · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₁ a ha)
    · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₂ a ha)
  have h1 := card_inf_le_mul hL1 A _ hmem1
  have h2 := card_inf_le_mul hL2 A (Set.univ : Set (Lyr hL2)) (fun _ _ _ => Set.mem_univ _)
  have h3 : degSeries Tag.D4 K Jout (2 + 1) = ⊥ := degSeries_J013_three (by norm_num)
  have hbot : Nat.card ↥(A ⊓ degSeries Tag.D4 K Jout (2 + 1)) = 1 := by
    rw [h3, inf_bot_eq]; exact Subgroup.card_bot
  rw [hAH] at h1
  rw [hbot, mul_one, Nat.card_univ, hL2card] at h2
  calc Nat.card A ≤ _ := h1
    _ ≤ Nat.card K ^ 2 * Nat.card K := by
        refine le_trans (Nat.mul_le_mul hS1 h2) ?_
        exact le_refl _
    _ = Nat.card K ^ 3 := by ring

end J013

end CFSG.LocalAnalysis.GLTheoremA
