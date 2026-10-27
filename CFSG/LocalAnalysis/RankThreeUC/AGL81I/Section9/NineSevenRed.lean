module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98ThreeEleven
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFieldAut
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOrbit
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.Quasithin.Background.A1cRank
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import TauCeti.Algebra.Group.Coprime
public import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Pattern
import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open
open scoped Pointwise

structure NineSevenRed (p : ℕ) (X : Type) [Group X] [Finite X] (E Y S : Subgroup X) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  core : CFSG.pPrimeCore p X = ⊥
  elem_E : IsElemAbelian p E
  card_E : Nat.card E = p ^ 2
  E_le : E ≤ Y
  gamma_le : rankThreeGamma 1 p E ≤ Y
  rank_Y : CFSG.pRank p ↥Y ≤ 3
  rank23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
    CFSG.pRank p ↥(Subgroup.normalizer (T : Set X)) ≤ 3
  two_S : IsPGroup 2 S
  S_le : S ≤ Y
  normal_S : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S

namespace NineSevenRed

variable {p : ℕ} {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}

theorem le_normalizer_E (h : NineSevenRed p X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) : E ≤ Subgroup.normalizer (L : Set X) := by
  have hpL : p ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card h.prime h.core hL
  have hrank : 2 ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl h.elem_E h.card_E
  rcases CFSG.LocalAnalysis.AGL81TheoremCD.Section15.le_gamma_or_le_normalizer h.prime hL hpL
    h.elem_E hrank with hΓ | hN
  · exact absurd (hΓ.trans h.gamma_le) hLY
  · exact hN

theorem mem_of_mem_centralizer (h : NineSevenRed p X E Y S) {z : X}
    (hz : z ∈ Subgroup.centralizer (E : Set X)) : z ∈ Y := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    have hc := h.card_E
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h.prime.one_lt
    omega
  have hzC : z ∈ Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hz y heE
  exact h.gamma_le (CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := p)
    (A := E) (M := rankThreeGamma 1 p E) le_rfl heE (orderOf_eq_prime (h.elem_E.2 e heE) he1)
    hzC)

omit [Finite X] in
theorem pow_mem_center_of_inner {L : Subgroup X} {e k : X} (hkL : k ∈ L) (hep : e ^ p = 1)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) :
    (⟨k, hkL⟩ : L) ^ p ∈ Subgroup.center ↥L := by
  let c : X := k⁻¹ * e
  have hc_cent : c ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcy : c * y = y * c := by
      calc c * y = k⁻¹ * (e * y) := by simp only [c]; group
        _ = k⁻¹ * ((e * y * e⁻¹) * e) := by group
        _ = k⁻¹ * ((k * y * k⁻¹) * e) := by rw [hrel y hy]
        _ = y * c := by simp only [c]; group
    exact hcy.symm
  have hkce : k * c = e := by simp only [c]; group
  have hck : Commute k c := Subgroup.mem_centralizer_iff.mp hc_cent k hkL
  have hep' : (k * c) ^ p = 1 := by rw [hkce]; exact hep
  have hpow : k ^ p * c ^ p = 1 := (hck.mul_pow p).symm.trans hep'
  have hkp : k ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hkp_cent : k ^ p ∈ Subgroup.centralizer (L : Set X) := by
    rw [hkp]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc_cent p)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hkp_cent (g : X) g.2

theorem mem_of_inner (hp : p.Prime) (hE : IsElemAbelian p E) {L : Subgroup X} {e k : X}
    (heE : e ∈ E) (he1 : e ≠ 1) (hγ : rankThreeGamma 1 p E ≤ Y) (hkL : k ∈ L)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) : k ∈ Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkC : k ∈ Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : e * k * e⁻¹ = k := by simpa using hrel k hkL
    calc e * k = (e * k * e⁻¹) * e := by group
      _ = k * e := by rw [h1]
  exact hγ (CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := p)
    (A := E) (M := rankThreeGamma 1 p E) le_rfl heE (orderOf_eq_prime (hE.2 e heE) he1) hkC)

theorem not_mem_center_of_inner (hp : p.Prime) (hE : IsElemAbelian p E) {L : Subgroup X}
    {e k : X} (heE : e ∈ E) (he1 : e ≠ 1) (hγ : rankThreeGamma 1 p E ≤ Y) (hkL : k ∈ L)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) (hLY : ¬ L ≤ Y) :
    (⟨k, hkL⟩ : L) ∉ Subgroup.center ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hkZ
  have hEL : L ≤ Subgroup.centralizer ({e} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hky : k * y * k⁻¹ = y := by
      have h := Subgroup.mem_center_iff.mp hkZ (⟨y, hy⟩ : L)
      have h' : k * y = y * k := (congrArg Subtype.val h).symm
      rw [h']
      group
    have h := hrel y hy
    rw [hky] at h
    calc e * y = (e * y * e⁻¹) * e := by group
      _ = y * e := by rw [h]
  have hC : Subgroup.centralizer ({e} : Set X) ≤ rankThreeGamma 1 p E :=
    CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := p) (A := E)
      (M := rankThreeGamma 1 p E) le_rfl heE (orderOf_eq_prime (hE.2 e heE) he1)
  exact hLY (hEL.trans (hC.trans hγ))

theorem le_normalizer_of_moved (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hS2 : IsPGroup 2 S) {k : X} (hkL : k ∈ L)
    (hkp : (⟨k, hkL⟩ : L) ^ p ∈ Subgroup.center ↥L)
    (hkZ : (⟨k, hkL⟩ : L) ∉ Subgroup.center ↥L)
    (hconj : ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ S) :
    S ≤ Subgroup.normalizer (L : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  by_contra hsN
  let Ls : Subgroup X := L.map (MulAut.conj s).toMonoidHom
  have hLs : CFSG.IsComponent Ls :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hL
  have hne : Ls ≠ L := by
    intro h
    exact hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hne' : L ≠ Ls := fun h => hne h.symm
  have hcomm : L ≤ Subgroup.centralizer (Ls : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hLs).resolve_left hne')
  let k' : X := s * k⁻¹ * s⁻¹
  have hk' : k' ∈ Ls := by
    refine Subgroup.mem_map.mpr ⟨k⁻¹, L.inv_mem hkL, ?_⟩
    simp [k', MulAut.conj_apply]
  have hck : Commute k k' :=
    (Subgroup.mem_centralizer_iff.mp (hcomm hkL) k' hk').symm
  let c : X := k * s * k⁻¹ * s⁻¹
  have hcS : c ∈ S := hconj s hs
  have hc_eq : c = k * k' := by simp only [c, k']; group
  obtain ⟨m, hm⟩ := hS2.exists_card_eq
  have hc_pow : c ^ (2 ^ m) = 1 := by
    have h := pow_card_eq_one' (G := ↥S) (x := ⟨c, hcS⟩)
    rw [hm] at h
    simpa using congrArg Subtype.val h
  have hmul : k ^ (2 ^ m) * k' ^ (2 ^ m) = 1 := by
    rw [← hck.mul_pow (2 ^ m), ← hc_eq]
    exact hc_pow
  have hkpowLs : k ^ (2 ^ m) ∈ Ls := by
    rw [eq_inv_of_mul_eq_one_left hmul]
    exact Ls.inv_mem (Ls.pow_mem hk' _)
  have hkpow_center : (⟨k, hkL⟩ : L) ^ (2 ^ m) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : X) * k ^ (2 ^ m) = k ^ (2 ^ m) * (g : X)
    exact (Subgroup.mem_centralizer_iff.mp (hcomm g.2) (k ^ (2 ^ m)) hkpowLs).symm
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨i, j, hij⟩ :=
    TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := ↥L) hcop
  have hmem : ((⟨k, hkL⟩ : L) ^ p) ^ i * ((⟨k, hkL⟩ : L) ^ (2 ^ m)) ^ j ∈
      Subgroup.center ↥L :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hkp i) (Subgroup.zpow_mem _ hkpow_center j)
  rw [hij (⟨k, hkL⟩ : L)] at hmem
  exact hkZ hmem

theorem exists_inner_or_dvd_center (h : NineSevenRed p X E Y S) {L L' : Subgroup X}
    (hL : CFSG.IsComponent L) (hL' : CFSG.IsComponent L') (hne : L ≠ L')
    (hEL : E ≤ Subgroup.normalizer (L : Set X)) (hEL' : E ≤ Subgroup.normalizer (L' : Set X)) :
    (∃ e ∈ E, e ≠ 1 ∧ ∃ k ∈ L, ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) ∨
      p ∣ Nat.card (Subgroup.center ↥L) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hEp : IsPGroup p E := h.elem_E.isPGroup
  have hpL : p ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card h.prime h.core hL
  have hpL' : p ∣ Nat.card L' :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card h.prime h.core hL'
  obtain ⟨z₁, hz₁L, hz₁o, hz₁c⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hEp hEL hpL
  obtain ⟨z₂, hz₂L, hz₂o, hz₂c⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hEp hEL' hpL'
  have hcommLL' : L ≤ Subgroup.centralizer (L' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hL').resolve_left hne)
  have h12 : z₁ * z₂ = z₂ * z₁ :=
    (Subgroup.mem_centralizer_iff.mp (hcommLL' hz₁L) z₂ hz₂L).symm
  by_cases hz₁E : z₁ ∈ E
  · left
    have hz₁1 : z₁ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz₁o
      exact h.prime.one_lt.ne hz₁o
    exact ⟨z₁, hz₁E, hz₁1, z₁, hz₁L, fun y _ => rfl⟩
  have hz₁p : z₁ ^ p = 1 := by rw [← hz₁o]; exact pow_orderOf_eq_one z₁
  have hz₁comm : ∀ b ∈ E, b * z₁ = z₁ * b := Subgroup.mem_centralizer_iff.mp hz₁c
  obtain ⟨hA, hAc⟩ :=
    isElemAbelian_sup_zpowers_of_notMem h.prime h.elem_E h.card_E hz₁E hz₁p hz₁comm
  by_cases hz₂A : z₂ ∈ E ⊔ Subgroup.zpowers z₁
  · have hEN : E ≤ Subgroup.normalizer ((Subgroup.zpowers z₁ : Subgroup X) : Set X) := by
      have h1 : E ≤ Subgroup.centralizer ({z₁} : Set X) :=
        fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hz₁comm b hb)
      have h2 : Subgroup.centralizer ({z₁} : Set X) ≤
          Subgroup.normalizer ((Subgroup.zpowers z₁ : Subgroup X) : Set X) := by
        rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
        exact Subgroup.centralizer_le_normalizer _
      exact h1.trans h2
    have hmem : z₂ ∈ (E : Set X) * (Subgroup.zpowers z₁ : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E (Subgroup.zpowers z₁) hEN]
      exact hz₂A
    obtain ⟨e, he, y, hy, hz₂eq⟩ := Set.mem_mul.mp hmem
    have hyL : y ∈ L := (Subgroup.zpowers_le.mpr hz₁L) hy
    by_cases he1 : e = 1
    · right
      have hz₂L1 : z₂ ∈ L := by
        rw [← hz₂eq, he1, one_mul]
        exact hyL
      have hcen : (⟨z₂, hz₂L1⟩ : L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hcommLL' g.2) z₂ hz₂L).symm
      have hord : orderOf (⟨⟨z₂, hz₂L1⟩, hcen⟩ : Subgroup.center ↥L) = p := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz₂o]
      rw [← hord]
      exact orderOf_dvd_natCard _
    · left
      refine ⟨e, he, he1, y⁻¹, L.inv_mem hyL, fun l hl => ?_⟩
      have he_eq : e = z₂ * y⁻¹ := by rw [← hz₂eq]; group
      have hm : y⁻¹ * l * y ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hyL) hl) hyL
      have hc : z₂ * (y⁻¹ * l * y) = (y⁻¹ * l * y) * z₂ :=
        Subgroup.mem_centralizer_iff.mp (hcommLL' hm) z₂ hz₂L
      rw [he_eq]
      calc z₂ * y⁻¹ * l * (z₂ * y⁻¹)⁻¹ = (z₂ * (y⁻¹ * l * y)) * z₂⁻¹ := by group
        _ = ((y⁻¹ * l * y) * z₂) * z₂⁻¹ := by rw [hc]
        _ = y⁻¹ * l * y⁻¹⁻¹ := by group
  · exfalso
    have hz₂p : z₂ ^ p = 1 := by rw [← hz₂o]; exact pow_orderOf_eq_one z₂
    have hAC : E ⊔ Subgroup.zpowers z₁ ≤ Subgroup.centralizer ({z₂} : Set X) := by
      refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr ?_) ?_
      · exact Subgroup.mem_centralizer_iff.mp hz₂c b hb
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr h12
    obtain ⟨hA₂, hA₂c⟩ := isElemAbelian_sup_zpowers_of_notMem h.prime hA hAc hz₂A hz₂p
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mp (hAC hb))
    have hA₂Y : E ⊔ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤ Y := by
      refine sup_le (sup_le h.E_le ?_) ?_
      · rw [Subgroup.zpowers_le]
        exact h.mem_of_mem_centralizer hz₁c
      · rw [Subgroup.zpowers_le]
        exact h.mem_of_mem_centralizer hz₂c
    have h4 : 2 + 1 + 1 ≤ CFSG.Open.pRank p Y :=
      CFSG.SectionRank.le_pRank h.prime.one_lt hA₂Y hA₂ hA₂c
    have h3 : CFSG.Open.pRank p Y ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact h.rank_Y
    omega

theorem not_dvd_card_center_of_moved (h : NineSevenRed p X E Y S)
    (h5c : KFactCenterRankFive) (h2c : KFactCenterRankTwo) (h5 : 5 ≤ p)
    (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) {L : Subgroup X} (hL : CFSG.IsComponent L)
    {s : X} (hne : L ≠ L.map (MulAut.conj s).toMonoidHom) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hK : CFSG.Open.IsKGroup X :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp h.catalog
  have h3L : 3 ≤ CFSG.Open.pRank p L := h5c X hK L hL p h.prime h5 hdvd
  have hLle : CFSG.Open.pRank p L ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans hX
  have hZ : CFSG.Open.pRank p (Subgroup.center ↥L) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 := h2c X hK L hL p h.prime h.ne_two hcon
    omega
  obtain ⟨A, hAL, hA, hAc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 3) h3L
  obtain ⟨a, haA, c, hcL, hac⟩ : ∃ a ∈ A, ∃ c ∈ L, a * c ≠ c * a := by
    by_contra hcon
    push Not at hcon
    have hA' : IsElemAbelian p (A.subgroupOf L) := hA.subgroupOf L
    have hA'c : Nat.card (A.subgroupOf L) = p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hAc]
    have hA'Z : A.subgroupOf L ≤ Subgroup.center ↥L := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hcon (x : X) (Subgroup.mem_subgroupOf.mp hx) (g : X) g.2).symm
    have h3Z := CFSG.SectionRank.le_pRank h.prime.one_lt hA'Z hA' hA'c
    omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hac (by rw [one_mul, mul_one])
  have hao : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  let L' : Subgroup X := L.map (MulAut.conj s).toMonoidHom
  have hL' : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hL
  have hcommLL' : L ≤ Subgroup.centralizer (L' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hL').resolve_left hne)
  have hmemL' : ∀ x ∈ L, s * x * s⁻¹ ∈ L' := fun x hx =>
    Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hao' : orderOf (s * a * s⁻¹) = p := by
    rw [show s * a * s⁻¹ = MulAut.conj s a by simp [MulAut.conj_apply], MulEquiv.orderOf_eq, hao]
  have hac' : (s * a * s⁻¹) * (s * c * s⁻¹) ≠ (s * c * s⁻¹) * (s * a * s⁻¹) := by
    intro heq
    apply hac
    have h1 : s * (a * c) * s⁻¹ = s * (c * a) * s⁻¹ := by
      calc s * (a * c) * s⁻¹ = (s * a * s⁻¹) * (s * c * s⁻¹) := by group
        _ = (s * c * s⁻¹) * (s * a * s⁻¹) := heq
        _ = s * (c * a) * s⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hcount := add_card_le_pRank_of_components h.prime hA hAc {L'} (by
    intro C hC
    rw [Finset.mem_singleton] at hC
    subst hC
    exact ⟨hL', hAL.trans hcommLL', s * a * s⁻¹, hmemL' a (hAL haA), hao',
      s * c * s⁻¹, hmemL' c hcL, hac'⟩)
  rw [Finset.card_singleton] at hcount
  omega

theorem le_normalizer_S (h : NineSevenRed p X E Y S) (h5c : KFactCenterRankFive)
    (h2c : KFactCenterRankTwo) (h5 : 5 ≤ p) (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    S ≤ Subgroup.normalizer (L : Set X) := by
  by_contra hSN
  obtain ⟨s, hsS, hsN⟩ := SetLike.not_le_iff_exists.mp hSN
  let L' : Subgroup X := L.map (MulAut.conj s).toMonoidHom
  have hL' : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hL
  have hne : L ≠ L' := fun heq => hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hsY : s ∈ Y := h.S_le hsS
  have hL'Y : ¬ L' ≤ Y := by
    intro hL'Y
    apply hLY
    intro l hl
    have hl' : s * l * s⁻¹ ∈ Y :=
      hL'Y (Subgroup.mem_map.mpr ⟨l, hl, by simp [MulAut.conj_apply]⟩)
    have hmem := Y.mul_mem (Y.mul_mem (Y.inv_mem hsY) hl') hsY
    rwa [show s⁻¹ * (s * l * s⁻¹) * s = l by group] at hmem
  have hEL := h.le_normalizer_E hL hLY
  have hEL' := h.le_normalizer_E hL' hL'Y
  rcases h.exists_inner_or_dvd_center hL hL' hne hEL hEL' with
    ⟨e, heE, he1, k, hkL, hrel⟩ | hdvd
  · have hkY : k ∈ Y := mem_of_inner h.prime h.elem_E heE he1 h.gamma_le hkL hrel
    have hkp := pow_mem_center_of_inner hkL (h.elem_E.2 e heE) hrel
    have hkZ := not_mem_center_of_inner h.prime h.elem_E heE he1 h.gamma_le hkL hrel hLY
    have hconj : ∀ t ∈ S, k * t * k⁻¹ * t⁻¹ ∈ S :=
      fun t ht => S.mul_mem (h.normal_S k hkY t ht) (S.inv_mem ht)
    exact hSN (le_normalizer_of_moved h.prime h.ne_two hL h.two_S hkL hkp hkZ hconj)
  · exact h.not_dvd_card_center_of_moved h5c h2c h5 hX hL hne hdvd

theorem pPrimeCore_subgroupOf_normalizer_eq_bot (h : NineSevenRed p X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) :
    CFSG.pPrimeCore p ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hcoreL : CFSG.pPrimeCore p ↥L = ⊥ := by
    have hsub : ((CFSG.pPrimeCore p ↥L).map L.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.step _ L (Subgroup.map_subtype_le _) hL.2 ?_
      have h1 : (Subgroup.map L.subtype (CFSG.pPrimeCore p ↥L)).subgroupOf L =
          CFSG.pPrimeCore p ↥L := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rw [h1]
      exact CFSG.pPrimeCore_normal
    have hcop : Nat.Coprime p (Nat.card ↥((CFSG.pPrimeCore p ↥L).map L.subtype)) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hsub hcop
    have hbot : (CFSG.pPrimeCore p ↥L).map L.subtype = ⊥ := by
      rw [h.core] at hle
      exact le_bot_iff.mp hle
    have hrec := Subgroup.comap_map_eq_self_of_injective L.subtype_injective
      (CFSG.pPrimeCore p ↥L)
    rw [hbot] at hrec
    simpa using hrec.symm
  let K : Subgroup X' := L.subgroupOf X'
  change CFSG.pPrimeCore p ↥K = ⊥
  let e : ↥K ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX'
  have hmap := CFSG.pPrimeCore_map_iso p e
  rw [hcoreL] at hmap
  exact Subgroup.map_injective e.injective (hmap.trans (Subgroup.map_bot _).symm)

theorem Y_le_normalizer_S (h : NineSevenRed p X E Y S) : Y ≤ Subgroup.normalizer (S : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h.normal_S y hy s, fun hs => ?_⟩
  have := h.normal_S y⁻¹ (Y.inv_mem hy) (y * s * y⁻¹) hs
  rwa [show y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s by group] at this

theorem rankThreeGamma_subgroupOf_le (h : NineSevenRed p X E Y S) (X' : Subgroup X) :
    rankThreeGamma 1 p (E.subgroupOf X') ≤ Y.subgroupOf X' := by
  let E' : Subgroup X' := E.subgroupOf X'
  change CFSG.Open.GLBCore p 1 E' ≤ Y.subgroupOf X'
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q hQE' hQrank
  let Q0 : Subgroup X := Q.map X'.subtype
  have hQ0E : Q0 ≤ E := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQE' hq
  have hQ0rank : 1 ≤ CFSG.Open.pRank p Q0 :=
    hQrank.trans (CFSG.SectionRank.pRank_le_map h.prime.one_lt X'.subtype
      X'.subtype_injective Q)
  have hNQ0 : Subgroup.normalizer (Q0 : Set X) ≤ Y :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQ0E hQ0rank).trans
      h.gamma_le
  have hmapN : (Subgroup.normalizer (Q : Set X')).map X'.subtype ≤
      Subgroup.normalizer (Q0 : Set X) :=
    Subgroup.le_normalizer_map (f := X'.subtype) (H := Q)
  intro n hn
  exact hNQ0 (hmapN (Subgroup.apply_coe_mem_map X'.subtype _ ⟨n, hn⟩))

theorem rank23_subgroup (h : NineSevenRed p X E Y S) (X' : Subgroup X) :
    ∀ T' : Subgroup X', T' ≠ ⊥ → IsPGroup 2 T' →
      CFSG.pRank p ↥(Subgroup.normalizer (T' : Set X')) ≤ 3 := by
  have hrank23open : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (Subgroup.normalizer (T : Set X)) ≤ 3 := by
    intro T hTne hT2
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h.rank23 T hTne hT2
  intro T' hT'ne hT'2
  let T : Subgroup X := T'.map X'.subtype
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hT'ne
    have hbot' : Subgroup.map X'.subtype T' = ⊥ := hbot
    have h := Subgroup.comap_map_eq_self_of_injective X'.subtype_injective T'
    rw [hbot'] at h
    simpa using h.symm
  have hT2 : IsPGroup 2 T := IsPGroup.map hT'2 X'.subtype
  have hNle : (Subgroup.normalizer (T' : Set X')).map X'.subtype ≤
      Subgroup.normalizer (T : Set X) :=
    Subgroup.le_normalizer_map (f := X'.subtype) (H := T')
  have h := (CFSG.SectionRank.pRank_le_map h.prime.one_lt X'.subtype X'.subtype_injective
    (Subgroup.normalizer (T' : Set X'))).trans
    ((CFSG.SectionRank.pRank_mono h.prime.one_lt hNle).trans (hrank23open T hTne hT2))
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact h

theorem pRank_rankThreeGamma_subgroupOf_le (h : NineSevenRed p X E Y S) (X' : Subgroup X) :
    CFSG.pRank p ↥(rankThreeGamma 1 p (E.subgroupOf X')) ≤ 3 := by
  have hΓle : rankThreeGamma 1 p (E.subgroupOf X') ≤ Y.subgroupOf X' :=
    h.rankThreeGamma_subgroupOf_le X'
  have hYrankY : CFSG.Open.pRank p Y ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h.rank_Y
  have hYrank : CFSG.Open.pRank p (Y.subgroupOf X') ≤ 3 := by
    have h1 := CFSG.SectionRank.pRank_le_map h.prime.one_lt X'.subtype
      X'.subtype_injective (Y.subgroupOf X')
    rw [Subgroup.subgroupOf_map_subtype] at h1
    exact h1.trans ((CFSG.SectionRank.pRank_mono h.prime.one_lt inf_le_left).trans hYrankY)
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact (CFSG.SectionRank.pRank_mono h.prime.one_lt hΓle).trans hYrank

omit [Finite X] in
theorem subgroupOf_normalizer_not_le_centralizer {S L : Subgroup X}
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    ¬ S.subgroupOf (Subgroup.normalizer (L : Set X)) ≤
      Subgroup.centralizer ((L.subgroupOf (Subgroup.normalizer (L : Set X))) :
        Set (Subgroup.normalizer (L : Set X))) := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  change ¬ S.subgroupOf X' ≤ Subgroup.centralizer ((L.subgroupOf X' : Subgroup X') : Set X')
  intro hSC
  apply hSL
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hs' : (⟨s, hSN hs⟩ : X') ∈ S.subgroupOf X' := hs
  have hcent := Subgroup.mem_centralizer_iff.mp (hSC hs') (⟨l, hLX' hl⟩ : X') hl
  exact congrArg Subtype.val hcent

theorem fi22_of_kFact (h : NineSevenRed p X E Y S) (hB5 : KFactThreeSevenTwoGe5) (h5 : 5 ≤ p)
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hEN : E ≤ Subgroup.normalizer (L : Set X)) (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    p = 5 ∧ CFSG.AGLEmbedding.IsFi22 ↥L := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hSX' : S ≤ X' := hSN
  let K : Subgroup X' := L.subgroupOf X'
  let E' : Subgroup X' := E.subgroupOf X'
  let S' : Subgroup X' := S.subgroupOf X'
  have hΓle : rankThreeGamma 1 p E' ≤ Y.subgroupOf X' := h.rankThreeGamma_subgroupOf_le X'
  have hΓN : rankThreeGamma 1 p E' ≤ Subgroup.normalizer (S' : Set X') := by
    refine hΓle.trans ?_
    change Y.subgroupOf X' ≤ Subgroup.normalizer ((S.subgroupOf X' : Subgroup X') : Set X')
    rw [← Subgroup.subgroupOf_normalizer_eq hSX']
    intro y hy
    exact h.Y_le_normalizer_S hy
  have hnotΓ : ¬ K ≤ rankThreeGamma 1 p E' := by
    intro hKΓ
    have hKY : K ≤ Y.subgroupOf X' := hKΓ.trans hΓle
    apply hLY
    intro l hl
    exact hKY (show (⟨l, hLX' hl⟩ : X') ∈ K from hl)
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, h.card_E]
  obtain ⟨hp5, hFi⟩ := hB5 X' (h.catalog.subgroup X') p h.prime h5 K E' S'
    Subgroup.normal_in_normalizer (CFSG.LocalCores.component_overgroup hL hLX').1
    (h.pPrimeCore_subgroupOf_normalizer_eq_bot hL) (h.elem_E.subgroupOf X') hE'card
    (h.rank23_subgroup X') (h.pRank_rankThreeGamma_subgroupOf_le X') hnotΓ
    (IsPGroup.of_equiv h.two_S (Subgroup.subgroupOfEquivOfLe hSX').symm) hΓN
    (subgroupOf_normalizer_not_le_centralizer hSL hSN)
  obtain ⟨φ⟩ := hFi
  exact ⟨hp5, ⟨(Subgroup.subgroupOfEquivOfLe hLX').symm.trans φ⟩⟩

end NineSevenRed

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
