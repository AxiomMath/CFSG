module

public import CFSG.ClassicalInvolution.Asc77.AscT8S2Odd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf_normalizer_contains)

namespace T8T

section Three

variable {G : Type} [Group G]

omit [Group G] in
theorem mem_closure_three_involutions {G : Type} [Group G] {a b c : G} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) {w : G} (hw : w ∈ Subgroup.closure ({a, b, c} : Set G)) :
    w = 1 ∨ w = a ∨ w = b ∨ w = c ∨ w = a * b ∨ w = a * c ∨ w = b * c ∨ w = a * b * c := by
  have ha' : ∀ t : G, a * (a * t) = t := fun t => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ t : G, b * (b * t) = t := fun t => by rw [← mul_assoc, hb, one_mul]
  have hc' : ∀ t : G, c * (c * t) = t := fun t => by rw [← mul_assoc, hc, one_mul]
  have h1 : ∀ t : G, b * (a * t) = a * (b * t) := fun t => by
    rw [← mul_assoc, ← hab, mul_assoc]
  have h2 : ∀ t : G, c * (a * t) = a * (c * t) := fun t => by
    rw [← mul_assoc, ← hac, mul_assoc]
  have h3 : ∀ t : G, c * (b * t) = b * (c * t) := fun t => by
    rw [← mul_assoc, ← hbc, mul_assoc]
  have hab' : b * a = a * b := hab.symm
  have hac' : c * a = a * c := hac.symm
  have hbc' : c * b = b * c := hbc.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  induction hw using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl | rfl <;> simp
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, h1, h2, h3, hab', hac', hbc', ha', hb', ha, hb, hc]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, mul_inv_rev, hai, hbi, hci, h1, hab', hac', hbc']

end Three

section Section

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {M M' : Subgroup G}


theorem secFam_nbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    {b b' : G} (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b')
    (hbb' : b ≠ b') {R' : Subgroup G} (hR' : IsSylow2In R' M')
    (hR'c : R' ≤ Subgroup.centralizer ({c} : Set G))
    (hR'N : R' ≤ Subgroup.normalizer (M : Set G)) :
    modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M') ∈
      omegaNbr (secFam Ω c)
        (modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M)) := by
  classical
  set Y := centralizingLayer (exactFamily Ω c) {c} with hY
  have hMc : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM, exactCore_le_centralizer c M⟩
  have hM'c : exactCore c M' ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM', exactCore_le_centralizer c M'⟩
  have hMY : exactCore c M ≤ Y := le_centLayer hMc
  have hM'Y : exactCore c M' ≤ Y := le_centLayer hM'c
  have hb : b ∈ exactCore c M := mem_exactCore hMb hc2 hM.2
  have hb' : b' ∈ exactCore c M' := mem_exactCore hM'b hc2 hM'.2
  have hbY : b ∈ Y := hMY hb
  have hb'Y : b' ∈ Y := hM'Y hb'
  have hU := TwinVertex.isUniqueInvolution_exactCore hp hq hMb hc2 hM.2
  have hU' := TwinVertex.isUniqueInvolution_exactCore hp hq hM'b hc2 hM'.2
  have hΛ : HypOmegaMod p f (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) Y) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hK' : (exactCore c M').subgroupOf Y ∈
      restrictFamily (centralizingMembers (exactFamily Ω c) {c}) Y :=
    ⟨exactCore c M', hM'c, hM'Y, rfl⟩
  have hzK : IsUniqueInvolution ((exactCore c M).subgroupOf Y) ⟨b, hbY⟩ :=
    isUniqueInvolution_subgroupOf hU hMY
  have hzK' : IsUniqueInvolution ((exactCore c M').subgroupOf Y) ⟨b', hb'Y⟩ :=
    isUniqueInvolution_subgroupOf hU' hM'Y
  have hne : (exactCore c M').subgroupOf Y ≠ (exactCore c M).subgroupOf Y := by
    intro h
    have h1 : exactCore c M' = exactCore c M := by
      have := congrArg (Subgroup.map Y.subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hM'Y, Subgroup.map_subgroupOf_eq_of_le hMY] at this
    have hb'M : b' ∈ exactCore c M := h1 ▸ hb'
    rcases hU.unique b' hb'M hU'.sq with h2 | h2
    · exact hU'.ne_one h2
    · exact hbb' h2.symm
  have hSyl : IsSylow2In R' (exactCore c M') :=
    (isSylow2In_exactCore_iff hΩ hc2 hM'.1 hM'.2).mpr ⟨hR', hR'c⟩
  have hR'N' : R' ≤ Subgroup.normalizer ((exactCore c M : Subgroup G) : Set G) := by
    intro r hr
    have hnorm : r ∈ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (hR'N hr) (Subgroup.le_normalizer (hR'c hr))
    exact perfectResidualOf_normalizer_contains _ hnorm
  have hnbrΛ : (exactCore c M').subgroupOf Y ∈
      omegaNbr (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) Y)
        ((exactCore c M).subgroupOf Y) :=
    ⟨hK', hne, R'.subgroupOf Y, mem_RSet_restrict hM'c hM'Y hSyl,
      Subgroup.subgroupOf_mono Y hSyl.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hMY).mp (hR'N' (Subgroup.mem_subgroupOf.mp hx))⟩
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hnt : (exactCore c M').subgroupOf Y ∈
      twinSet (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) Y)
        ((exactCore c M).subgroupOf Y) → (exactCore c M').subgroupOf Y =
          (exactCore c M).subgroupOf Y := by
    rintro ⟨-, z', hz'K, hz'J⟩
    exact absurd (congrArg Subtype.val ((hz'K.eq hzK).symm.trans (hz'J.eq hzK'))) hbb'
  exact T8S2.omegaNbr_map_odd hp hΛ hNodd hnbrΛ
    (T8S2.map_ne_of_noTwins hp hΛ hNodd hzK hzK' hnbrΛ hnt)

theorem commutes_modOdd_of_nbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (hM : M ∈ tqMembers Ω c)
    (hM' : M' ∈ tqMembers Ω c)
    (hnbr : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M') ∈
      omegaNbr (secFam Ω c)
        (modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M))) :
    Commutes (modOdd c (exactCore c M)) (modOdd c (exactCore c M')) := by
  have hMc : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM, exactCore_le_centralizer c M⟩
  have hM'c : exactCore c M' ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM', exactCore_le_centralizer c M'⟩
  have hMY : exactCore c M ≤ centralizingLayer (exactFamily Ω c) {c} := le_centLayer hMc
  have hΦ : HypOmega p f (secFam Ω c) := hypOmega_secFam hp hq hΩ hc2 hs D
  have hK : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M) ∈ secFam Ω c :=
    ⟨_, ⟨exactCore c M, hMc, hMY, rfl⟩, rfl⟩
  have hcomm := AscE186.commutes_of_mem_omegaNbr hp hq hΦ hK hnbr
  rw [← map_sectionQuotientHom_modOddIn hs.normalizes hMc,
    ← map_sectionQuotientHom_modOddIn hs.normalizes hM'c]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (hcomm x hx y hy)

end Section

end T8T

end CFSG.ClassicalInvolution.Asc77
