module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepA
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepB
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepC
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Main
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartTwo.KFacts

variable {G : Type} [Group G] [Finite G]

private theorem isKleinOrQ8Central_w (h627 : GL83SmallRankProp627W G) {P : Sylow 3 G}
    {M : Subgroup G} (hs : SmallRankSituation G 3 P M) {x : G} (hx : SmallRankPoint P M x)
    {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    IsKleinOrQ8Central (T ⊓ centralizer ({x} : Set G)) := by
  rcases (h627 3 P M hs).2 x hx T hT with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem exists_transvection_w (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    ∃ g ∈ (P : Subgroup G), ∃ b : ℕ, ¬ 3 ∣ b ∧ g * x * g⁻¹ = x * z ^ b := by
  have hB := SmallRankPlane.of_situation hS hs hx hz
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hA : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ 3 := by
    obtain ⟨A, hAP, hAe, hAc⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
    exact ⟨A, hAP, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe,
      by rwa [hP3] at hAc⟩
  obtain ⟨hcomm, h, hh, hne⟩ := hB.exists_transvection Nat.prime_three P.isPGroup'
    hz.centralizes hz.ne_one hz.pow_eq_one hA
  obtain ⟨k, hk⟩ : ∃ k : ℕ, z ^ k = h * x * h⁻¹ * x⁻¹ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hcomm h hh))
  refine ⟨h, hh.1, k, ?_, ?_⟩
  · rintro ⟨j, rfl⟩
    apply hne
    rw [← hk, pow_mul, hz.pow_eq_one, one_pow]
  · have hxz : Commute x z := mem_centralizer_iff.mp hz.centralizes x hx.mem
    rw [(hxz.pow_right k).eq, hk]
    group

private theorem not_le_centralizer_w (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    ¬ (T ⊓ centralizer ({x} : Set G)) ≤ centralizer ({z} : Set G) := by
  intro hle
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute hS hs hx hz hT
  exact hzv (mem_centralizer_singleton_iff.mp (hle hv)).symm

private theorem mem_normalizer_inf_centralizer_w {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : SmallRankSylowTwo P M T) :
    z ∈ normalizer ((T ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes x hx.mem).symm
  exact inf_normalizer_le_normalizer_inf ⟨hT.normalized hz.mem, le_normalizer hzx⟩

omit [Finite G] in
private theorem centralizer_sup_zpowers_w (x z : G) :
    centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) := by
  rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, centralizer_closure]
  ext g
  simp [mem_centralizer_iff, and_comm]

private theorem exists_smallRank3Data_w (hS : Setting G) (hU0 : FullCoreLocal G)
    (h627 : GL83SmallRankProp627W G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) :
    ∃ (x z g : G) (T : Subgroup G), SmallRank3Data P M x z g T := by
  obtain ⟨x, hx⟩ := exists_smallRankPoint hS hU0 hs.mem_sigmaA hs.isCoreMaxLocal
    hs.not_gamma_one_le hs.largeObstruction_empty
  have hP : (P : Subgroup G) ≠ ⊥ := fun h => hx.ne_one (by simpa [h] using hx.mem)
  obtain ⟨z, hz⟩ := exists_smallRankCentral hP
  obtain ⟨T, hT⟩ := exists_smallRankSylowTwo hS hs.mem_sigmaA hs.isCoreMaxLocal
  obtain ⟨g, hgP, hg⟩ := exists_transvection_w hS hs hx hz
  have hKQ := isKleinOrQ8Central_w h627 hs hx hT
  have hnc := not_le_centralizer_w hS hs hx hz hT
  have hcyc := isCyclic_inf_centralizer_of_isKleinOrQ8Central hKQ hz.pow_eq_one
    (mem_normalizer_inf_centralizer_w hx hz hT) hnc
  refine ⟨x, z, g, T, hx, hz, hT, hgP, hg, hKQ, hnc, NearCyclic.of_isKleinOrQ8Central hKQ, ?_⟩
  rwa [centralizer_sup_zpowers_w, ← inf_assoc]

theorem prop632_of_prop627W (hKP : KPSz)
    (hK : SmallRankConstraintKFact3) (hS : Setting G) (hU0 : FullCoreLocal G)
    (h : GL83SmallRankProp627W G) : GL83SmallRankProp632 G := by
  intro P M hs
  obtain ⟨x, z, g, T, hd⟩ := exists_smallRank3Data_w hS hU0 h hs
  have hO3 := no_normal_index_three_of_situation hS hU0 hs
  have hD := isSolvable_primeCore_of_data hKP hS hs hd hO3
  obtain ⟨e⟩ := nonempty_mulEquiv_wreath_of_data hS hs hd
  have hQ := isSolvable_quotient_of_kfact hK hS hU0 hs hd.point e
  exact ⟨isSolvable_of_primeCore_of_quotient hD hQ, ⟨e⟩⟩

private theorem fit627W_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem fit627W_mem_normalizer_primeCore (q : ℕ) [Fact q.Prime] (D : Subgroup G) {g : G}
    (hg : g ∈ normalizer (D : Set G)) : g ∈ normalizer (rankThreePrimeCore q D : Set G) := by
  obtain ⟨hOD, hDO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec q D
  have key : ∀ g ∈ normalizer (D : Set G), ∀ y ∈ rankThreePrimeCore q D,
      g * y * g⁻¹ ∈ rankThreePrimeCore q D := by
    intro g hg y hy
    have h1 : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
    have h2 : (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer (((rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) :=
      Subgroup.map_equiv_normalizer_eq (rankThreePrimeCore q D) (MulAut.conj g)
    have hle : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤
        rankThreePrimeCore q D := by
      have hsub : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤ D := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg y).mp (hOD hy)
      refine le_sSup ⟨hsub, (normal_subgroupOf_iff_le_normalizer hsub).mpr ?_, ?_⟩
      · calc D = D.map (MulAut.conj g).toMonoidHom := h1.symm
          _ ≤ (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom :=
            map_mono hDO
          _ = _ := h2
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
private theorem fit627W_normalizer_le_of_characteristic {H : Subgroup G} (K : Subgroup H)
    [hK : K.Characteristic] :
    normalizer (H : Set G) ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ x ∈ K.map H.subtype,
      g * x * g⁻¹ ∈ K.map H.subtype := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : H ≃* H := H.normalizerMonoidHom ⟨g, hg⟩
    have hfix := Subgroup.characteristic_iff_map_eq.mp hK φ
    have hyK : φ y ∈ K := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    exact Subgroup.mem_map.mpr ⟨φ y, hyK, H.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

private theorem fit627W_isNilpotent (H : Subgroup G) :
    Group.IsNilpotent (CFSG.fittingSubgroupOf H) := by
  have h : Group.IsNilpotent (CFSG.fittingSubgroup H) := inferInstance
  exact Group.nilpotent_of_mulEquiv
    ((CFSG.fittingSubgroup H).equivMapOfInjective H.subtype H.subtype_injective)

private theorem fit627W_exists_pGroup {F : Subgroup G} [Group.IsNilpotent F] {q : ℕ}
    [Fact q.Prime] {g : G} (hgF : g ∈ F) (hg : orderOf g = q) :
    ∃ Q : Subgroup G, IsPGroup q Q ∧ Q ≤ F ∧ g ∈ Q ∧
      normalizer (F : Set G) ≤ normalizer (Q : Set G) := by
  have hzp : IsPGroup q (zpowers (⟨g, hgF⟩ : F)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, pow_one]
    exact hg
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S inferInstance
  exact ⟨(S : Subgroup F).map F.subtype, S.isPGroup'.map F.subtype, Subgroup.map_subtype_le _,
    ⟨⟨g, hgF⟩, hS (mem_zpowers _), rfl⟩, fit627W_normalizer_le_of_characteristic _⟩

theorem fitting_inf_eq_bot_of_prop65 {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) (h65 : GL83SmallRankProp65 G) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (rankThreePrimeCore 3
      (centralizer ({x} : Set G)))) ⊓ M = ⊥ := by
  set C : Subgroup G := centralizer ({x} : Set G)
  set D : Subgroup G := rankThreePrimeCore 3 C
  set O : Subgroup G := rankThreePrimeCore 2 D
  set F : Subgroup G := CFSG.fittingSubgroupOf O
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(F ⊓ M) ≠ 1 from fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hgo : orderOf (g : G) = q := by rw [Subgroup.orderOf_coe]; exact hg
  have hgF : (g : G) ∈ F := g.2.1
  have hgM : (g : G) ∈ M := g.2.2
  have hDspec := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 C
  have hOspec := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := fun c hc =>
    fit627W_mem_normalizer_primeCore 2 D (hDspec.2.1 hc)
  have hOF : normalizer (O : Set G) ≤ normalizer (F : Set G) :=
    fit627W_normalizer_le_of_characteristic (CFSG.fittingSubgroup O)
  have := fit627W_isNilpotent O
  obtain ⟨Q, hQp, hQF, hgQ, hFQ⟩ := fit627W_exists_pGroup hgF hgo
  have hCQ : C ≤ normalizer (Q : Set G) := hCO.trans (hOF.trans hFQ)
  have hFO : F ≤ O := Subgroup.map_subtype_le _
  have hxz : x * z = z * x := mem_centralizer_iff.mp h.central.centralizes x h.point.mem
  have hBC : zpowers x ⊔ zpowers z ≤ C :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).1
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    (sup_le (zpowers_le.mpr h.point.mem) (zpowers_le.mpr h.central.mem)).trans hPM
  have hBQ₁ : zpowers x ⊔ zpowers z ≤ normalizer ((Q ⊓ M : Subgroup G) : Set G) :=
    (le_inf (hBC.trans hCQ) (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hQ₁ne : Q ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ (⊥ : Subgroup G) := hbot ▸ (⟨hgQ, hgM⟩ : (g : G) ∈ Q ⊓ M)
    rw [Subgroup.mem_bot] at hmem
    have h1 : orderOf (g : G) = 1 := by rw [hmem, orderOf_one]
    exact hq.one_lt.ne' (hgo.symm.trans h1)
  have hcop : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 6 := by
    have hdvd : Nat.card ↥(Q ⊓ M) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le ((inf_le_left.trans hQF).trans hFO)
    have hdvd' : Nat.card O ∣ Nat.card D := Subgroup.card_dvd_of_le hOspec.1
    have h2 : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 2 :=
      (Nat.Coprime.coprime_dvd_right hdvd hOspec.2.2).symm
    have h3 : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 3 :=
      (Nat.Coprime.coprime_dvd_right (hdvd.trans hdvd') hDspec.2.2).symm
    exact (show (6 : ℕ) = 2 * 3 by norm_num) ▸ Nat.Coprime.mul_right h2 h3
  have hN₁ : normalizer ((Q ⊓ M : Subgroup G) : Set G) ≤ M :=
    h65 P M h.situation h.solvable h.wreath x z h.point h.central (Q ⊓ M) inf_le_right hQ₁ne
      hcop hBQ₁
  have hQM : Q ≤ M := by
    by_contra hQM
    have hlt : Q ⊓ M < Q :=
      lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyQ, hyN, hyY⟩ := fit627W_exists_mem_normalizer_not_mem hQp hlt
    exact hyY ⟨hyQ, hN₁ hyN⟩
  rw [inf_eq_left.mpr hQM] at hN₁
  exact h.point.not_centralizer_le (hCQ.trans hN₁)

theorem prop627_of_prop627W (hKP : KPSz)
    (hK : SmallRankConstraintKFact3) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (hS : Setting G) (hU0 : FullCoreLocal G)
    (h : GL83SmallRankProp627W G) : GL83SmallRankProp627 G := by
  intro p P M hs
  obtain ⟨rfl, hpt⟩ := h p P M hs
  refine ⟨rfl, fun x hx T hT => ?_⟩
  rcases hpt x hx T hT with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h2, h3, ?_⟩
    obtain ⟨hsolv, he⟩ := prop632_of_prop627W hKP hK hS hU0 h P M hs
    have hP : (P : Subgroup G) ≠ ⊥ := fun h0 => hx.ne_one (by simpa [h0] using hx.mem)
    obtain ⟨z, hz⟩ := exists_smallRankCentral hP
    exact fitting_inf_eq_bot_of_prop65 ⟨hS, hU0, hs, hsolv, he, hx, hz⟩
      (prop65_of_kfacts hS hU0 hK1 hK2)

end CFSG.LocalAnalysis.RankThreeTheoremC
