module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ThreeFourTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQOvergroupsHolds
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.ON.Simple
public import CFSG.Sporadic.ON
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

theorem isPSLType_oPrime_M1 :
    IsPSLType 3 (ZMod 7) (oPrimeModPrimeComplement 19 M1) := by
  have hidx := index_Q0_M1
  have : (Q0.subgroupOf M1).Normal := Subgroup.normal_of_index_eq_two hidx
  have eQ : ↥(Q0.subgroupOf M1) ≃* ↥Q0 := Subgroup.subgroupOfEquivOfLe Q0_le_M1
  have : IsSimpleGroup ↥(Q0.subgroupOf M1) := @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_Q0 eQ
  have hc : Nat.card (Q0.subgroupOf M1) = 1876896 := (Nat.card_congr eQ.toEquiv).trans card_Q0
  obtain ⟨e1⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv (d := 19) (by norm_num)
    (Q0.subgroupOf M1) (by rw [hc]; norm_num) (by rw [hidx]; norm_num)
  exact ⟨((e1.trans eQ).trans Q0_equiv.symm).trans (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 (ZMod 7)))⟩

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ONSchreier CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

theorem conclusion_of_onan
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 7 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .ONan) :
    ThreeNineConclusion K D X₁ 7 d := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ON.isSimpleGroup_ON e
  have hcK : Nat.card ↥K = 460815505920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  obtain ⟨θ⟩ : Nonempty (↥K ≃* ↥Pv) := ⟨e.trans onEquivPv⟩
  have hO : Nat.card (Outer ↥K) ∣ 2 := by
    rw [Nat.card_congr (equivalence θ).toEquiv]
    exact CFSG.Sporadic.SteinbergBI.card_outer_Pv_dvd_two
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hdp := h.d_prime
  have hout7 : ¬ 7 ∣ Nat.card (Outer ↥K) := fun h7 => by
    have := Nat.le_of_dvd (by norm_num) hO
    have := Nat.le_of_dvd hO0 h7
    omega
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    have := Nat.le_of_dvd (by norm_num) (hd.trans hO)
    have := hdp.two_le
    exact h.d_ne_two (by omega)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ houtd
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  obtain ⟨Ebar, -, hEc, -, hN⟩ := h.exists_barE hZ hout7
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  have hNS := hN S S.isPGroup' hES
  obtain ⟨g, hg⟩ := sylow_eq_map_on7F (Sylow.mapSurjective (f := θ.toMonoidHom) θ.surjective S)
  have hg' : (S : Subgroup ↥K).map θ.toMonoidHom =
      (on7F 0).map (MulAut.conj g : Pv ≃* Pv).toMonoidHom := hg
  set φ : ↥K ≃* ↥Pv := θ.trans (MulAut.conj g⁻¹) with hφ
  have hSφ : (S : Subgroup ↥K).map φ.toMonoidHom = on7F 0 := by
    have h1 : ((S : Subgroup ↥K).map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
        (S : Subgroup ↥K).map φ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [← h1, hg', map_map_equiv]
    convert Subgroup.map_id (on7F 0)
    ext x
    simp
  set Y : Subgroup ↥Pv := (X₁.subgroupOf K).map φ.toMonoidHom with hYdef
  have hYc : Nat.card Y = Nat.card (X₁.subgroupOf K) :=
    Subgroup.card_map_of_injective φ.injective
  have hNY : Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) ≤ Y := by
    rw [← hSφ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNS
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    obtain ⟨k, hk, hkx⟩ : φ ⟨x, hx⟩ ∈ Y := htop ▸ Subgroup.mem_top _
    have hk' : k = ⟨x, hx⟩ := φ.injective hkx
    exact Subgroup.mem_subgroupOf.mp (hk' ▸ hk)
  have hYM : Y ≤ M1 ∨ Y ≤ G2 := by
    have h1 := onanNQOvergroups_holds Y hNY hYtop
    rwa [onanM_one_eq, onanM_two_eq] at h1
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [← hYc] at hd1 hd2
  have hYdvd : Nat.card Y ∣ 3753792 := by
    rcases hYM with hle | hle
    · exact card_M1 ▸ Subgroup.card_dvd_of_le hle
    · exact card_G2 ▸ Subgroup.card_dvd_of_le hle
  have hd19 : d = 19 := by
    have h' : d ∣ 2 ^ 6 * (3 ^ 2 * (7 ^ 3 * 19)) := by norm_num; exact hd1.trans hYdvd
    rcases hdp.dvd_mul.1 h' with h2 | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
        h.d_ne_two
    rcases hdp.dvd_mul.1 h' with h3 | h'
    · have h3' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 (hdp.dvd_of_dvd_pow h3)
      subst h3'
      rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 4) Nat.prime_three (by norm_num)
        (by norm_num) (by norm_num)] at hd2
      exact absurd (hd2.trans hYdvd) (by norm_num)
    rcases hdp.dvd_mul.1 h' with h7 | h19
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_seven).1 (hdp.dvd_of_dvd_pow h7))
        h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq hdp (by norm_num)).1 h19
  subst hd19
  have hYN : Y ≠ Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) := by
    intro hYeq
    rw [hYeq, card_normalizer_on7F0] at hd1
    exact absurd hd1 (by norm_num)
  have hcases : Y = M1 ∨ Y = G2 := by
    rcases hYM with hle | hle
    · exact Or.inl ((eq_normalizer_or_eq card_on7F0 card_M1 card_normalizer_on7F0
        normalizer_on7F0_le_M1 noInvariantPlane_on7F0 hNY hle).resolve_left hYN)
    · exact Or.inr ((eq_normalizer_or_eq card_on7F0 card_G2 card_normalizer_on7F0
        normalizer_on7F0_le_G2 noInvariantPlane_on7F0 hNY hle).resolve_left hYN)
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hDc : Nat.card D = 19 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_D
    have hdvd : 19 ^ k ∣ 460815505920 := hk ▸ hcK ▸ Subgroup.card_dvd_of_le hDK
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact absurd ((pow_dvd_pow 19 (by omega : 2 ≤ k)).trans hdvd) (by norm_num)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨isCyclic_of_prime_card hDc, hDK,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ⟨e⟩, ?_⟩))))⟩
  obtain ⟨e3⟩ : Nonempty (↥Y ≃* ↥M1) := by
    rcases hcases with hY | hY
    · exact ⟨MulEquiv.subgroupCongr hY⟩
    · exact ⟨(MulEquiv.subgroupCongr (hY.trans G2_eq_map)).trans
        (M1.equivMapOfInjective _ (MulEquiv.injective _)).symm⟩
  have e1 : ↥X₁ ≃* ↥(X₁.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hX₁K).symm
  have e2 : ↥(X₁.subgroupOf K) ≃* ↥Y :=
    (X₁.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective
  obtain ⟨e4⟩ := oPrimeModPrimeComplement_congr 19 ((e1.trans e2).trans e3)
  obtain ⟨e5⟩ := SporCent.isPSLType_oPrime_M1
  exact ⟨e4.trans e5⟩

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
