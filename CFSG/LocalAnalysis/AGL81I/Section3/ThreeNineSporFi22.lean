module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.Monster.B.Fischer.Fi22OmegaMax
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open Subgroup
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Certificates.SetOrbit CFSG.EvenSmallLie.OmegaEight
open scoped Pointwise

section Group

variable {G : Type*} [Group G] [Finite G]

theorem normal_subgroupOf_of_isSimpleGroup_of_factorial_lt {D M : Subgroup G} (hDM : D ≤ M)
    (hD : IsSimpleGroup ↥D) {k : ℕ} (hidx : (D.subgroupOf M).index = k)
    (hcard : k.factorial < Nat.card M) : (D.subgroupOf M).Normal := by
  set D' := D.subgroupOf M with hD'
  have : IsSimpleGroup ↥D' := @MulEquiv.isSimpleGroup _ _ _ _ hD (subgroupOfEquivOfLe hDM)
  have hdvd := index_normalCore_dvd_factorial_index D'
  rw [hidx] at hdvd
  set N := D'.normalCore
  have hNle : N ≤ D' := normalCore_le D'
  have hN : N ≠ ⊥ := by
    intro h
    rw [h, index_bot] at hdvd
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos k) hdvd) (by omega)
  have hNn : (N.subgroupOf D').Normal := (normalCore_normal D').subgroupOf D'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf D') with h | h
  · exfalso
    apply hN
    rw [subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNle
  · rw [subgroupOf_eq_top] at h
    have : N = D' := le_antisymm hNle h
    rw [← this]
    exact normalCore_normal D'

theorem le_sup_normalizer_of_sylow_le {p : ℕ} [Fact p.Prime] {D M : Subgroup G}
    (S : Sylow p G) (hSD : (S : Subgroup G) ≤ D) (hDM : D ≤ M) (hDn : (D.subgroupOf M).Normal) :
    M ≤ D ⊔ normalizer ((S : Subgroup G) : Set G) := by
  intro m hm
  have hSM : (S : Subgroup G) ≤ M := hSD.trans hDM
  let P : Sylow p ↥M := S.subtype hSM
  have hPD : (P : Subgroup ↥M) ≤ D.subgroupOf M := by
    rw [Sylow.coe_subtype]
    intro x hx
    exact mem_subgroupOf.2 (hSD (mem_subgroupOf.1 hx))
  have := hDn
  have hF := Sylow.normalizer_sup_eq_top' P hPD
  have hmem : (⟨m, hm⟩ : ↥M) ∈ normalizer ((P : Subgroup ↥M) : Set ↥M) ⊔ D.subgroupOf M :=
    hF ▸ mem_top _
  have hmap := mem_map_of_mem M.subtype hmem
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hDM] at hmap
  refine (sup_le ?_ le_sup_left : _ ≤ D ⊔ _) hmap
  rintro _ ⟨n, hn, rfl⟩
  refine le_sup_right (a := D) ?_
  rw [SetLike.mem_coe, mem_normalizer_iff] at hn
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 := (hn ⟨s, hSM hs⟩).1 (by rw [Sylow.coe_subtype]; exact mem_subgroupOf.2 hs)
    rw [Sylow.coe_subtype, mem_subgroupOf] at h1
    simpa using h1
  · intro hs
    have hsM : s ∈ M := by
      have h1 := M.mul_mem (M.mul_mem (M.inv_mem n.2) (hSM hs)) n.2
      simpa [mul_assoc] using h1
    have h1 := (hn ⟨s, hsM⟩).2 (by
      rw [Sylow.coe_subtype, mem_subgroupOf]
      simpa using hs)
    rw [Sylow.coe_subtype, mem_subgroupOf] at h1
    simpa using h1

theorem le_of_isPGroup_of_not_dvd_index {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] {D' P : Subgroup M} [D'.Normal] (hP : IsPGroup p P) (hcop : ¬ p ∣ D'.index) :
    P ≤ D' := by
  have h1 : IsPGroup p ↥(P.map (QuotientGroup.mk' D')) := hP.map _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h1
  have h2 : Nat.card ↥(P.map (QuotientGroup.mk' D')) ∣ D'.index := by
    rw [index_eq_card]
    exact card_subgroup_dvd_card _
  have hn0 : n = 0 := by
    by_contra h
    exact hcop (dvd_trans (dvd_pow_self p h) (hn ▸ h2))
  rw [hn0, pow_zero] at hn
  have hbot : P.map (QuotientGroup.mk' D') = ⊥ := eq_bot_of_card_eq _ hn
  intro x hx
  have hmem : QuotientGroup.mk' D' x ∈ P.map (QuotientGroup.mk' D') := ⟨x, hx, rfl⟩
  rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

end Group

theorem fi22_D_le_M :
    i242Y.subgroupOf fi22P ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) := by
  intro x hx
  rw [mem_subgroupOf] at hx
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact MulAction.mem_stabilizer_iff.1 (i242Y_le_stabilizer_U0 hx)

theorem fi22_Q_le_M :
    fi22FiveQ.subgroupOf fi22P ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) := by
  intro q hq
  rw [mem_subgroupOf] at hq
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact MulAction.mem_stabilizer_iff.1 (fi22FiveQ_le_stabilizer_U0 hq)

theorem fi22_index_D_M :
    ((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).index = 6 := by
  have h := ((i242Y.subgroupOf fi22P).subgroupOf
    (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe fi22_D_le_M).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe i242Y_le_fi22P).toEquiv, i242_card_Y,
    fi22Omega_card_stabilizer,
    show (1045094400 : ℕ) = 174182400 * 6 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem fi22_nonempty_D_equiv :
    Nonempty (↥(i242Y.subgroupOf fi22P) ≃* ↥omegaT) :=
  ⟨(subgroupOfEquivOfLe i242Y_le_fi22P).trans (i242YEquiv.trans omegaRestrictEquiv.symm)⟩

theorem fi22_D_simple :
    IsSimpleGroup ↥(i242Y.subgroupOf fi22P) := by
  have : IsSimpleGroup ↥omegaT := CFSG.Timmesfeld.isSimpleGroup_of_lieModel lieModel_omegaT
  obtain ⟨f⟩ := fi22_nonempty_D_equiv
  exact f.isSimpleGroup

theorem fi22_D_normal :
    ((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).Normal :=
  normal_subgroupOf_of_isSimpleGroup_of_factorial_lt fi22_D_le_M fi22_D_simple fi22_index_D_M
    (by rw [fi22Omega_card_stabilizer]; decide)

theorem fi22_D_le_iSup :
    i242Y.subgroupOf fi22P ≤ ⨆ i : Fin 6,
      centralizer {(⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P)} := by
  have h1 : ∀ i : Fin 6, fi22FiveD i ≤
      (centralizer {(⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P)}).map fi22P.subtype := by
    intro i g hg
    refine ⟨⟨g, fi22FiveD_le_P i hg⟩, ?_, rfl⟩
    have hc := mem_centralizer_singleton_iff.1
      (fi22FiveC_le_centralizer_line i (fi22FiveD_le_C i hg))
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact Subtype.ext hc
  have h2 : i242Y ≤ (⨆ i : Fin 6,
      centralizer {(⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P)}).map fi22P.subtype := by
    refine i242Y_le_J.trans ?_
    rw [Subgroup.map_iSup]
    exact iSup_mono h1
  intro d hd
  rw [mem_subgroupOf] at hd
  obtain ⟨y, hy, hyd⟩ := h2 hd
  have : y = d := Subtype.ext hyd
  rw [← this]
  exact hy

theorem fi22_eq_stabilizer_of_le
    {Y : Subgroup ↥fi22P}
    (hY : Y ≠ ⊤) (hNY : normalizer ((fi22FiveQ.subgroupOf fi22P : Subgroup ↥fi22P) : Set ↥fi22P) ≤ Y)
    (hCY : ∀ i : Fin 6, centralizer {(⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P)} ≤ Y) :
    Y = MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := fi22FiveQ_sylow
  have hDY : i242Y.subgroupOf fi22P ≤ Y := fi22_D_le_iSup.trans (iSup_le hCY)
  have hQM : (Q : Subgroup ↥fi22P) ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) :=
    hQ ▸ fi22_Q_le_M
  have hQD : (Q : Subgroup ↥fi22P) ≤ i242Y.subgroupOf fi22P := by
    have := fi22_D_normal
    have h := le_of_isPGroup_of_not_dvd_index (p := 5)
      (P := (Q : Subgroup ↥fi22P).subgroupOf
        (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)))
      (Q.isPGroup'.of_equiv (subgroupOfEquivOfLe hQM).symm)
      (by rw [fi22_index_D_M]; decide)
    intro q hq
    exact mem_subgroupOf.1 (h (mem_subgroupOf.2 (show q ∈ (Q : Subgroup _) from hq) :
      (⟨q, hQM hq⟩ : ↥(MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) ∈ _))
  have hMY : MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) ≤ Y :=
    (le_sup_normalizer_of_sylow_le Q hQD fi22_D_le_M fi22_D_normal).trans
      (sup_le hDY (hQ ▸ hNY))
  exact ((fi22Omega_isCoatom).le_iff.1 hMY).resolve_left hY

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Certificates.SetOrbit CFSG.EvenSmallLie.OmegaEight
open scoped Pointwise

theorem conclusion_of_fi22
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi22) :
    ThreeNineConclusion K D X₁ 5 d := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
  have hcK : Nat.card ↥K = 64561751654400 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22
  have hdp := h.d_prime
  have hout5 : ¬ 5 ∣ Nat.card (Outer ↥K) := by rw [hO]; norm_num
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    rw [hO] at hd
    exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 hd)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ houtd
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  obtain ⟨Ebar, -, hEc, hEC, hEN⟩ := h.exists_barE hZ hout5
  have hEbarc : Nat.card Ebar = 5 ^ (Nat.card ↥K).factorization 5 := by
    rw [hEc, hcK, SporCent.factorization_eq_of_pow_dvd (e := 2) Nat.prime_five (by norm_num)
      (by norm_num) (by norm_num)]
  let θ : ↥K ≃* ↥fi22P := e.trans fi22PermEquiv
  obtain ⟨Q, hQ⟩ := fi22FiveQ_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥fi22P
    (Sylow.mapSurjective (f := θ.toMonoidHom) θ.surjective (Sylow.ofCard Ebar hEbarc)) Q
  let φ : ↥K ≃* ↥fi22P := θ.trans (MulAut.conj g)
  have hEφ : Ebar.map φ.toMonoidHom = fi22FiveQ.subgroupOf fi22P := by
    have h1 : (Q : Subgroup ↥fi22P) =
        (Ebar.map θ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    rw [← hQ, h1, Subgroup.map_map]
    rfl
  set W : Subgroup ↥fi22P := (X₁.subgroupOf K).map φ.toMonoidHom with hWdef
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    obtain ⟨k, hk, hkx⟩ : φ ⟨x, hx⟩ ∈ W := by rw [htop]; exact Subgroup.mem_top _
    have hk' : k = ⟨x, hx⟩ := φ.injective hkx
    exact Subgroup.mem_subgroupOf.mp (hk' ▸ hk)
  have hNW : Subgroup.normalizer
      ((fi22FiveQ.subgroupOf fi22P : Subgroup ↥fi22P) : Set ↥fi22P) ≤ W := by
    rw [← hEφ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hEN Ebar (IsPGroup.of_card hEc) le_rfl)
  have hCW : ∀ i : Fin 6,
      Subgroup.centralizer {(⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P)} ≤ W := by
    intro i y hy
    have hxi : (⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩ : ↥fi22P) ∈ Ebar.map φ.toMonoidHom := by
      rw [hEφ]
      exact Subgroup.mem_subgroupOf.mpr (fi22FiveLine_mem_Q i)
    obtain ⟨v, hv, hvx⟩ := hxi
    have hv1 : v ≠ 1 := by
      rintro rfl
      apply fi22FiveLine_ne_one i
      have h1 := congrArg Subtype.val hvx
      rw [map_one] at h1
      exact h1.symm
    refine ⟨φ.symm y, hEC v hv hv1 ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    rw [← hvx] at hy
    exact hy
  have hWM := SporCent.fi22_eq_stabilizer_of_le hWtop hNW hCW
  have hWc : Nat.card (X₁.subgroupOf K) = 1045094400 := by
    have hc : Nat.card W = Nat.card (X₁.subgroupOf K) := Subgroup.card_map_of_injective φ.injective
    rw [← hc, hWM, fi22Omega_card_stabilizer]
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [hWc] at hd1 hd2
  have hd7 : d = 7 := by
    have h' : d ∣ 2 ^ 13 * (3 ^ 6 * (5 ^ 2 * 7)) := by norm_num; exact hd1
    rcases hdp.dvd_mul.1 h' with h2 | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
        h.d_ne_two
    rcases hdp.dvd_mul.1 h' with h3 | h'
    · have h3' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 (hdp.dvd_of_dvd_pow h3)
      subst h3'
      rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 9) Nat.prime_three (by norm_num)
        (by norm_num) (by norm_num)] at hd2
      exact absurd hd2 (by norm_num)
    rcases hdp.dvd_mul.1 h' with h5 | h7
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 (hdp.dvd_of_dvd_pow h5))
        h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq hdp (by norm_num)).1 h7
  subst hd7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hDc : Nat.card D = 7 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_D
    have hdvd : 7 ^ k ∣ 64561751654400 := hk ▸ hcK ▸ Subgroup.card_dvd_of_le hDK
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact absurd ((pow_dvd_pow 7 (by omega : 2 ≤ k)).trans hdvd) (by norm_num)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨isCyclic_of_prime_card hDc, hDK, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ⟨e⟩, ?_⟩))⟩
  have := SporCent.fi22_D_normal
  have : IsSimpleGroup ↥((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) :=
    @MulEquiv.isSimpleGroup _ _ _ _ SporCent.fi22_D_simple
      (Subgroup.subgroupOfEquivOfLe SporCent.fi22_D_le_M)
  have hDc' : Nat.card ↥((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) = 174182400 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe SporCent.fi22_D_le_M).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe i242Y_le_fi22P).toEquiv, i242_card_Y]
  obtain ⟨e1⟩ := SporCent.nonempty_oPrimeModPrimeComplement_mulEquiv (G := ↥fi22P) (d := 7)
    (by norm_num) (Y := MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))
    ((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)))
    (by rw [hDc']; norm_num) (by rw [SporCent.fi22_index_D_M]; norm_num)
  have e2 : ↥X₁ ≃* ↥(MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)) :=
    ((Subgroup.subgroupOfEquivOfLe hX₁K).symm.trans
      ((X₁.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective)).trans
      (MulEquiv.subgroupCongr hWM)
  obtain ⟨e3⟩ := oPrimeModPrimeComplement_congr 7 e2
  obtain ⟨f⟩ := SporCent.fi22_nonempty_D_equiv
  exact i242_isDFourTwo_of_equiv
    (((e3.trans e1).trans (Subgroup.subgroupOfEquivOfLe SporCent.fi22_D_le_M)).trans f)

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem threeNineFiveFi22_holds :
    ThreeNineFiveFi22 :=
  fun _ _ _ _ _ _ _ _ h hs => h.conclusion_of_fi22 hs

end CFSG.LocalAnalysis.AGL81I.Section3
