module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourInd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourPSL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSol
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

theorem exists_sl23_quaternion_pair : ∃ x y : SL(2, ZMod 3), x * x = -1 ∧ y * y = -1 ∧
    ⁅x, y⁆ = -1 ∧ x ^ 2 ^ 2 = 1 ∧ y ^ 2 ^ 2 = 1 :=
  ⟨⟨!![0, 2; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩,
    ⟨!![1, 1; 1, 2], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide, by decide,
    by decide, by decide⟩

theorem orderOf_neg_one_sl23 : orderOf (-1 : SL(2, ZMod 3)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_mk_pPrimeCore_eq_two {X : Type*} [Group X] [Finite X] {w : X}
    (hw : orderOf w = 2) : orderOf (QuotientGroup.mk w : X ⧸ pPrimeCore 2 X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, ← hw, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · intro h
    have h1 := Subgroup.orderOf_dvd_natCard _ ((QuotientGroup.eq_one_iff w).mp h)
    rw [hw] at h1
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 X)))))
      (even_iff_two_dvd.mpr h1)

theorem nonempty_slTwoThree_of_inductionType
    {G : Type} [Group G] [Finite G] {L A : Subgroup G} (hL : IsSolvableTwoComponentIn L A)
    (hI : InductionType 3 ↥L) : Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) := by
  rcases hI with ⟨f, hf, h⟩ | ⟨-, ⟨τ, n, hm⟩ | he⟩
  · exfalso
    have hQ : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
      rcases h with h | h | h | h | ⟨hev, hsl⟩
      · exact h.1
      · exact h.1
      · exact h.1
      · exact h.1
      · have hf2 : 2 ≤ f := by
          obtain ⟨k, hk⟩ := hev
          omega
        have h5 : 5 ≤ 3 ^ f :=
          le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hf2)
        exact (Lemma47.sl2_facts Nat.prime_three (by norm_num) hf h5 hsl).1
    exact false_of_isQuasisimple_of_sl2Three hQ hL.2.2.2
  · exact (false_of_lieModel_three_of_card_dvd hm (card_fusionZStar_dvd hL.2.2.2)).elim
  · exact he

theorem false_of_lieModel_psl2
    {G : Type} [Group G] [Finite G] {z₂ : G} (hz₂ : orderOf z₂ = 2) {K L₂ A : Subgroup G}
    (hKq : IsTwoQuasisimple ↥K) (hz₂K : z₂ ∈ K)
    (hz₂Z : (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K))
    (hA : A ≤ Subgroup.centralizer {z₂})
    (hL₂ : IsTwoComponentIn L₂ A ∨ IsSolvableTwoComponentIn L₂ A)
    (hz₂L : z₂ ∈ L₂) (hI : InductionType 3 ↥L₂) (hO₂ : GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K)
    {f : ℕ} (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 2 3 f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  have hm' := GSThmB.OddQuot.lieModel_of_equiv eZ hm
  have ht2 : orderOf (ρ ⟨z₂, hz₂K⟩) = 2 :=
    orderOf_mk_pPrimeCore_eq_two (by rw [Subgroup.orderOf_mk]; exact hz₂)
  obtain ⟨S, hSab, hScomm, hSsq⟩ := exists_abelian_of_psl2 hKq.2
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hm' ht2 hz₂Z
  have hL₂A : L₂ ≤ A := hL₂.elim (·.1) (·.1)
  have hcen : ∀ (g : G) (hg : g ∈ K), g ∈ L₂ →
      ρ ⟨g, hg⟩ ∈ Subgroup.centralizer {ρ ⟨z₂, hz₂K⟩} := by
    intro g hg hgL
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hA (hL₂A hgL)))
  rcases hL₂ with hL₂ | hL₂
  ·
    have hp : Group.IsPerfect ↥L₂ := hL₂.2.2.1
    have hLK : L₂ ≤ K := by
      have h1 : GH74.GLS.oPrimeResidualOf 2 L₂ = L₂ := by
        rw [GH74.GLS.oPrimeResidualOf, T23.oPrimeResidual_two_eq_top hp, ← MonoidHom.range_eq_map,
          range_subtype]
      exact h1 ▸ hO₂
    set φ : ↥L₂ →* ↥K ⧸ pPrimeCore 2 ↥K := ρ.comp (Subgroup.inclusion hLK) with hφ
    have hφC : ∀ x, φ x ∈ Subgroup.centralizer {ρ ⟨z₂, hz₂K⟩} := fun x => hcen x (hLK x.2) x.2
    have htop : _root_.commutator ↥L₂ = ⊤ := Group.IsPerfect.commutator_eq_top
    have hφS : ∀ x, φ x ∈ S := by
      have h1 : _root_.commutator ↥L₂ ≤ S.comap φ := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [mem_comap, map_commutatorElement]
        exact hScomm _ (hφC a) _ (hφC b)
      intro x
      exact h1 (htop ▸ mem_top x)
    have h1 : _root_.commutator ↥L₂ ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hSab _ (hφS a) _ (hφS b)
    have h2 : φ ⟨z₂, hz₂L⟩ = 1 := h1 (htop ▸ mem_top _)
    have h3 : φ ⟨z₂, hz₂L⟩ = ρ ⟨z₂, hz₂K⟩ := rfl
    rw [h3] at h2
    rw [h2, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  ·
    obtain ⟨e₂⟩ := nonempty_slTwoThree_of_inductionType hL₂ hI
    set π₂ : ↥L₂ →* SL(2, ZMod 3) := e₂.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₂
    have hπ₂s : Function.Surjective π₂ := e₂.surjective.comp (QuotientGroup.mk'_surjective _)
    obtain ⟨x, y, hxx, hyy, hxy, hx4, hy4⟩ := exists_sl23_quaternion_pair
    obtain ⟨a, ⟨ka, hka⟩, hax⟩ := exists_pow_eq_one_of_surjective Nat.prime_two hπ₂s hx4
    obtain ⟨b, ⟨kb, hkb⟩, hby⟩ := exists_pow_eq_one_of_surjective Nat.prime_two hπ₂s hy4
    have hmemK : ∀ c : ↥L₂, (∃ k : ℕ, c ^ 2 ^ k = 1) → (c : G) ∈ K := by
      rintro c ⟨k, hk⟩
      exact hO₂ (GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element c.2
        ⟨k, by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩)
    have haK := hmemK a ⟨ka, hka⟩
    have hbK := hmemK b ⟨kb, hkb⟩
    have key : ∀ (c : ↥L₂) (hcK : (c : G) ∈ K), π₂ c = -1 → ρ ⟨(c : G), hcK⟩ ≠ 1 := by
      intro c hcK hc h1
      have h2 : (⟨(c : G), hcK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h1
      have h3 : Odd (orderOf (⟨(c : G), hcK⟩ : ↥K)) :=
        Odd.of_dvd_nat (Nat.coprime_two_left.mp
          (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥K))))
          (Subgroup.orderOf_dvd_natCard _ h2)
      have h4 : orderOf (π₂ c) ∣ orderOf c := orderOf_map_dvd π₂ c
      rw [hc, orderOf_neg_one_sl23] at h4
      have h5 : orderOf c = orderOf (⟨(c : G), hcK⟩ : ↥K) :=
        (Subgroup.orderOf_coe c).symm.trans (Subgroup.orderOf_mk (c : G) hcK).symm
      rw [h5] at h4
      exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr h4)
    have hsq : ∀ (c : ↥L₂) (hcK : (c : G) ∈ K), π₂ c * π₂ c = -1 →
        ρ ⟨(c : G), hcK⟩ ∈ S := by
      intro c hcK hc
      refine hSsq _ (hcen _ hcK c.2) fun h1 => ?_
      refine key (c * c) (mul_mem hcK hcK) (by rw [map_mul, hc]) ?_
      exact (map_mul ρ _ _).trans h1
    have haS := hsq a haK (by rw [hax, hxx])
    have hbS := hsq b hbK (by rw [hby, hyy])
    have hab := hSab _ haS _ hbS
    have hcK : ((⁅a, b⁆ : ↥L₂) : G) ∈ K := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem haK hbK) (inv_mem haK)) (inv_mem hbK)
    apply key ⁅a, b⁆ hcK (by rw [map_commutatorElement, hax, hby, hxy])
    have h1 : (⟨((⁅a, b⁆ : ↥L₂) : G), hcK⟩ : ↥K) = ⁅(⟨(a : G), haK⟩ : ↥K), ⟨(b : G), hbK⟩⁆ :=
      rfl
    rw [h1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab

theorem nonempty_fusionZStar_equiv_m11 {K : Type} [Group K]
    (eM : K ⧸ pPrimeCore 2 K ≃* ↥Blueprint.NativeSporadic.M11) :
    Nonempty (K ⧸ Open.fusionZStar K ≃* ↥Blueprint.NativeSporadic.M11) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv K
  let e1 := QuotientGroup.congr _ _ eM (OuterAutomorphisms.center_map_equiv eM)
  let e2 : ↥Blueprint.NativeSporadic.M11 ⧸ center ↥Blueprint.NativeSporadic.M11 ≃*
      ↥Blueprint.NativeSporadic.M11 :=
    (QuotientGroup.quotientMulEquivOfEq RankTwoSporadic.M11.m11_center_eq_bot).trans
      QuotientGroup.quotientBot
  exact ⟨(eZ.trans e1).trans e2⟩

theorem false_of_m11_of_le_centralizer {G : Type} [Group G]
    [Finite G] {z₁ : G} (hz₁ : orderOf z₁ = 2) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer {z₁}) (hz₁K : z₁ ∈ K)
    (eM : ↥K ⧸ pPrimeCore 2 ↥K ≃* ↥Blueprint.NativeSporadic.M11) : False := by
  have hZ : (QuotientGroup.mk ⟨z₁, hz₁K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∈
      center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hK g.2))
  have h1 : eM (QuotientGroup.mk ⟨z₁, hz₁K⟩) ∈ center ↥Blueprint.NativeSporadic.M11 := by
    rw [← OuterAutomorphisms.center_map_equiv eM]
    exact mem_map_of_mem _ hZ
  rw [RankTwoSporadic.M11.m11_center_eq_bot, mem_bot, map_eq_one_iff _ eM.injective] at h1
  have h2 := orderOf_mk_pPrimeCore_eq_two (X := ↥K) (w := ⟨z₁, hz₁K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₁)
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem harris82FourGroupThree_of_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hK3 : KnownRowThree)
    (h226 : Harris82Lemma226Three) (hres : FourGroupResidualStep) : Harris82FourGroupThree := by
  intro G _ _ _ hnonab hKP hcat z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ hL₁ hL₂ hz₁L hz₂L he₁ hI
  obtain ⟨e₁⟩ := he₁
  have hsub := not_isSubnormal_sup_oPrimeResidualOf_three hCI hnonab hcat hz₁
    (hL₁.1.trans inf_le_left) hz₁L e₁
  obtain ⟨K, hKc, hO₂, hN, hcomm, hz₂K, hz₂Z⟩ :=
    h226 G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ hL₁ hL₂ hz₂L hsub
  have hind := isSimpleChevalleyOver_or_m11 hK3 hnonab hKP hz₁ hz₂ hL₂ hz₂L hI hKc hO₂ hN
  have htype : (IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) ∧
        ∀ f : ℕ, ¬ Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 2 3 f) ∨
      Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥Blueprint.NativeSporadic.M11) := by
    rcases hind with hch | ⟨⟨eM⟩⟩
    · exact .inl ⟨hch, fun f hf => false_of_lieModel_psl2 hz₂ hKc.2.2 hz₂K hz₂Z inf_le_right hL₂
        hz₂L hI hO₂ hf⟩
    · exact .inr (nonempty_fusionZStar_equiv_m11 eM)
  have hO₁ := hres G hnonab hKP hcat z₁ z₂ hz₁ hz₂ hne hc L₁ K hL₁ hz₁L ⟨e₁⟩ hKc hN hcomm
    ⟨hz₂K, hz₂Z⟩ htype
  have hz₁K : z₁ ∈ K := hO₁ (GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element hz₁L
    ⟨1, by rw [pow_one, ← hz₁, pow_orderOf_eq_one]⟩)
  have hch : IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) := by
    rcases hind with hch | ⟨⟨eM⟩⟩
    · exact hch
    · exact (false_of_m11_of_le_centralizer hz₁ hKc.1 hz₁K eM).elim
  exact ⟨K, hKc, hO₁, hO₂, hN, hch, hz₂K, hz₂Z⟩

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
