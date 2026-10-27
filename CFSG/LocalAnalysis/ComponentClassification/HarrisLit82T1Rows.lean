module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows
public import CFSG.ClassicalInvolution.Q3.M11Multiplier
public import CFSG.Sporadic.Schreier.M11
public import CFSG.LargeExtraspecial.OutSixBasic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def LieChar (r : ℕ) (S : Type) [Group S] : Prop :=
  ∃ (τ : StatedLieTag) (n f : ℕ), Blueprint.LieModel S τ n r f

@[expose] def RowFor (C : ℕ → (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) →
      z ∈ L → ∀ p : ℕ, p.Prime → p ≠ 2 → IsMTypeSchur p ↥L → InductionTypeField p ↥L →
      C p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G)) →
        IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
            pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
          Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11)

theorem rowFor_lieChar_self : RowFor (fun p S => LieChar p S) := by
  intro G _ _ hY _ _ _ _ _ p _ _ _ _ ⟨τ, n, f, hm⟩
  obtain ⟨e⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥(GH74.GLS.oPrimeResidual 2 G)
  exact .inl (.inl ⟨hY.2, τ, n, f, GSThmB.OddQuot.lieModel_of_equiv e hm⟩)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidual_two_normal : (GH74.GLS.oPrimeResidual 2 G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    exact subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem odd_index_oPrimeResidual_two : Odd (GH74.GLS.oPrimeResidual 2 G).index := by
  have := oPrimeResidual_two_normal (G := G)
  set Y := GH74.GLS.oPrimeResidual 2 G
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, Subgroup.index_eq_card]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgY : g ^ m ∈ Y := subset_closure ⟨a, by rw [← pow_mul, mul_comm, ← hgm,
    pow_orderOf_eq_one]⟩
  have hu2 : (g : G ⧸ Y) ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one _
  have h1 : ((g : G ⧸ Y)) ^ m = (g : G ⧸ Y) := by
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, hu2, one_pow, one_mul]
  have h2' : ((g : G ⧸ Y)) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hgY
  have : orderOf (g : G ⧸ Y) = 1 := by rw [orderOf_eq_one_iff, ← h1, h2']
  omega

theorem nonempty_quotient_equiv_m11
    (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (e₀ : ↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G) ≃*
      ↥Blueprint.NativeSporadic.M11) :
    Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  have hYn : Y.Normal := oPrimeResidual_two_normal
  set Q := ↥Y ⧸ pPrimeCore 2 ↥Y with hQdef
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
  have hQ : IsQuasisimple Q := hY.2
  let π : Q →* ↥Blueprint.NativeSporadic.M11 :=
    (eZ.symm.trans e₀).toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hπs : Function.Surjective π :=
    (eZ.symm.trans e₀).surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ (eZ.symm.trans e₀).injective, QuotientGroup.ker_mk']
  have hZ2 : IsPGroup 2 ↥(center Q) :=
    N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hπi := ClassicalInvolution.Q3.injective_of_perfect_central_two π hπs hQ.1 hπk.le
    (hπk ▸ hZ2)
  let eQ : Q ≃* ↥Blueprint.NativeSporadic.M11 := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  set φ : ↥Y →* G ⧸ pPrimeCore 2 G := (QuotientGroup.mk' (pPrimeCore 2 G)).comp Y.subtype
    with hφ
  have hφk : φ.ker = pPrimeCore 2 ↥Y := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 Y
      (Subgroup.Normal.isSubnormal hYn), hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  set Yb := φ.range with hYb
  let eY : ↥Yb ≃* ↥Blueprint.NativeSporadic.M11 :=
    ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).symm.trans eQ
  have hYbmap : Yb = Y.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    rw [hYb, hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hYbn : Yb.Normal := hYbmap ▸ hYn.map _ (QuotientGroup.mk'_surjective _)
  have hodd : Odd Yb.index := by
    have h := Subgroup.index_map_dvd (H := Y) (QuotientGroup.mk'_surjective (pPrimeCore 2 G))
    rw [← hYbmap] at h
    exact Odd.of_dvd_nat odd_index_oPrimeResidual_two h
  have hZQ : center Q = ⊥ := hπk ▸ (MonoidHom.ker_eq_bot_iff π).mpr hπi
  let eYQ : ↥Yb ≃* Q :=
    ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).symm
  have hC : centralizer (Yb : Set (G ⧸ pPrimeCore 2 G)) ≤ Yb := by
    set C := centralizer (Yb : Set (G ⧸ pPrimeCore 2 G)) with hCdef
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hCY : ∀ x ∈ C, x ∈ Yb → x = 1 := by
      intro x hxC hxY
      have hxZ : eYQ ⟨x, hxY⟩ ∈ center Q := by
        rw [mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := eYQ.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg eYQ (Subtype.ext ((mem_centralizer_iff.mp hxC) y y.2))
      rw [hZQ, mem_bot, map_eq_one_iff _ eYQ.injective] at hxZ
      exact congrArg Subtype.val hxZ
    let f : ↥C →* (G ⧸ pPrimeCore 2 G) ⧸ Yb := (QuotientGroup.mk' Yb).comp C.subtype
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact Subtype.ext (hCY x x.2 hx)
    have hCodd : Odd (Nat.card C) := by
      have h := Subgroup.card_dvd_of_injective f hf
      rw [← Subgroup.index_eq_card] at h
      exact Odd.of_dvd_nat hodd h
    have hCO : C ≤ pPrimeCore 2 (G ⧸ pPrimeCore 2 G) :=
      le_sSup ⟨hCn, Nat.coprime_two_left.mpr hCodd⟩
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hCO
    exact hCO.trans bot_le
  have hdvd := CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv Yb hC eY
  have hle := (CFSG.Sporadic.Schreier.at_m11_schreier).1
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥Blueprint.NativeSporadic.M11) := Nat.card_pos
  have h1 : Yb.index = 1 := by
    have := Nat.le_of_dvd hpos hdvd
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [Subgroup.index_eq_one] at h1
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h1.symm)).trans eY⟩

theorem rowFor_m11 :
    RowFor (fun _ S => Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11)) := by
  intro G _ _ hY _ _ _ _ _ _ _ _ _ _ ⟨e₀⟩
  exact .inr (nonempty_quotient_equiv_m11 hY e₀)

@[expose] def RowLieOther : Prop :=
  RowFor (fun p S => (∃ r : ℕ, r ≠ p ∧ LieChar r S) ∧ ¬ LieChar p S)

@[expose] def RowAlt : Prop :=
  RowFor (fun p S => (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∧
    ¬ LieChar p S)

@[expose] def RowSpor : Prop :=
  RowFor (fun _ S => Blueprint.NativeSporadic.SporadicRep S ∧
    ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11))

theorem knownRow_of_rows
    (hLo : RowLieOther) (hA : RowAlt) (hS : RowSpor) :
    KnownRow := by
  intro G _ _ hY hcat z hz L hL hzL p hp hp2 hM hI
  set Y := GH74.GLS.oPrimeResidual 2 G
  by_cases hp' : LieChar p (↥Y ⧸ Open.fusionZStar ↥Y)
  · exact rowFor_lieChar_self G hY z hz L hL hzL p hp hp2 hM hI hp'
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, r, f, hm⟩ | hex | hsp
  ·
    exfalso
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
    obtain ⟨a, b, hab⟩ := hY.2.2.2
    apply hab
    apply (eZ.symm.trans e).injective
    rw [map_mul, map_mul, mul_comm]
  · exact hA G hY z hz L hL hzL p hp hp2 hM hI ⟨⟨n, hn, ⟨e⟩⟩, hp'⟩
  · have hLie : LieChar r (↥Y ⧸ Open.fusionZStar ↥Y) :=
      ⟨t, n, f, .inl ⟨by
        rcases Milestones.statedClassicalModel_tag_mem _ t n r f hm with h | h | h | h | h | h <;>
          subst h <;> decide, hm⟩⟩
    exact hLo G hY z hz L hL hzL p hp hp2 hM hI
      ⟨⟨r, fun h => hp' (h ▸ hLie), hLie⟩, hp'⟩
  · have hLie : ∃ r : ℕ, LieChar r (↥Y ⧸ Open.fusionZStar ↥Y) := by
      rcases hex with ⟨t, r, f, ht, hm⟩ | ⟨t, r, f, ht, hm⟩ | ⟨r, f, hm⟩
      · exact ⟨r, t, 0, f, .inr (.inl ⟨rfl, ht, hm⟩)⟩
      · exact ⟨r, t, 0, f, .inr (.inr (.inl ⟨rfl, ht, hm⟩))⟩
      · exact ⟨r, .twistedB2, 0, f, .inr (.inr (.inr ⟨rfl, rfl, hm⟩))⟩
    obtain ⟨r, hLie⟩ := hLie
    exact hLo G hY z hz L hL hzL p hp hp2 hM hI
      ⟨⟨r, fun h => hp' (h ▸ hLie), hLie⟩, hp'⟩
  · by_cases hm11 : Nonempty (↥Y ⧸ Open.fusionZStar ↥Y ≃* ↥Blueprint.NativeSporadic.M11)
    · exact rowFor_m11 G hY z hz L hL hzL p hp hp2 hM hI hm11
    · exact hS G hY z hz L hL hzL p hp hp2 hM hI ⟨hsp, hm11⟩

end T1

end CFSG.ComponentClassification.HarrisLit
