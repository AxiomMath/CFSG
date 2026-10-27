module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtQuotKer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKerFrame
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
import CFSG.Quasithin.Background.A1cSL2Facts
import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem branchB_false_of_dvd_four {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (h : d ∣ 3 + 1) : False :=
  hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp
    (hd.dvd_of_dvd_pow (n := 2) (by simpa using h)))

private theorem branchB_isSLType_or_isPSLType [Fact p.Prime] (hp5 : 5 ≤ p) {T : Type} [Group T]
    [Nontrivial T] (ψ : SL(2, ZMod p) →* T) (hψ : Function.Surjective ψ) :
    IsSLType 2 (ZMod p) T ∨ IsPSLType 2 (ZMod p) T := by
  rcases CFSG.Quasithin.A1c.normal_le_center_or_eq_top hp5 ψ.ker with hc | ht
  · by_cases hk : ψ.ker = ⊥
    · exact Or.inl ⟨(MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hk, hψ⟩).symm⟩
    obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
    have hneg : CFSG.Quasithin.A1c.sl2NegOne p ∈ ψ.ker := by
      rcases CFSG.Quasithin.A1c.eq_one_or_eq_sl2NegOne_of_mem_center (hc g.2) with h1 | h1
      · exact absurd (Subtype.ext h1) hg1
      · exact h1 ▸ g.2
    have hkc : ψ.ker = Subgroup.center (SL(2, ZMod p)) := by
      refine le_antisymm hc fun z hz => ?_
      rcases CFSG.Quasithin.A1c.eq_one_or_eq_sl2NegOne_of_mem_center hz with rfl | rfl
      · exact one_mem _
      · exact hneg
    exact Or.inr ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkc)⟩
  · obtain ⟨x, hx⟩ := exists_ne (1 : T)
    obtain ⟨g, rfl⟩ := hψ x
    exact absurd (MonoidHom.mem_ker.mp (ht ▸ Subgroup.mem_top g)) hx

private theorem branchB_false_of_isSLType_three [Fact p.Prime] {T : Type} [Group T]
    (ψ : SL(2, ZMod p) →* T) (hψ : Function.Surjective ψ) (hT : IsSLType 3 (ZMod p) T) :
    False := by
  obtain ⟨e⟩ := hT
  have hp := Fact.out (p := p.Prime)
  have hdvd := Subgroup.card_dvd_of_surjective hψ
  rw [Nat.card_congr e.toEquiv, CFSG.GroupTheory.card_SL3_zmod hp, CFSG.PSL2Table.card_SL,
    ZMod.card] at hdvd
  have h2 := hp.two_le
  have ha : 0 < p ^ 2 - 1 := by
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hp3 : p < p ^ 3 := by simpa using Nat.pow_lt_pow_right h2 (show 1 < 3 by norm_num)
  have hb : 0 < p ^ 3 - 1 := by omega
  have hle := Nat.le_of_dvd (Nat.mul_pos hp.pos ha) hdvd
  have hlt : p * (p ^ 2 - 1) < p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) :=
    calc p * (p ^ 2 - 1) < p ^ 3 * (p ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hp3 ha
      _ ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hb)
  omega

private theorem branchB_exists_sl2_map {A B : Type} [Group A] [Group B] {X : Subgroup A}
    [X.Normal] {N : Subgroup X} [N.Normal] (hN : IsPGroup p N) (e : X ⧸ N ≃* SL(2, ZMod p))
    (f : A →* B) (hf : CFSG.pCore p A ≤ f.ker) :
    ∃ ψ : SL(2, ZMod p) →* ↥(X.map f), Function.Surjective ψ := by
  have hNp : N ≤ CFSG.pCore p X := le_sSup ⟨inferInstance, hN⟩
  have hcore : (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p A :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      (CFSG.pCore_isPGroup (p := p) (G := X)).map X.subtype⟩
  have hker : N ≤ (f.subgroupMap X).ker := fun n hn =>
    MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp (hf (hcore ⟨n, hNp hn, rfl⟩))))
  refine ⟨(QuotientGroup.lift N _ hker).comp e.symm.toMonoidHom, ?_⟩
  rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (QuotientGroup.lift_surjective_of_surjective N _ (f.subgroupMap_surjective X) hker).comp
    e.symm.surjective

private theorem branchB_exists_starToQuotKer (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hle : pLayerIn p H ≤ M) :
    ∃ φ : StarGroup p H →* QuotKer M H, Function.Surjective φ ∧
      CFSG.pCore p (StarGroup p H) ≤ φ.ker ∧ (starImg p H (pLayerIn p H)).map φ = ⊥ := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hO := Subgroup.ker_le_comap (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    (CFSG.pCore p (StarGroup p H))
  rw [QuotientGroup.ker_mk'] at hO
  let φ : StarGroup p H →* QuotKer M H := QuotientGroup.map _ _ (MonoidHom.id _)
    (hO.trans (comap_pCore_starGroup_le_normalCore hI h))
  have hφ : ∀ x : ↥H, φ (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x := fun _ => rfl
  have hLK : (pLayerIn p H).subgroupOf H ≤ Subgroup.normalCore ((M ⊓ H).subgroupOf H) := by
    have : (CFSG.pLayer ↥H p).Characteristic :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
    have hsub : (pLayerIn p H).subgroupOf H = CFSG.pLayer ↥H p :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hsub, Subgroup.normal_le_normalCore, ← hsub]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨hle (Subgroup.mem_subgroupOf.mp hx), x.2⟩)
  refine ⟨φ, fun y => ?_, fun z hz => ?_, (Subgroup.map_eq_bot_iff _).mpr fun z hz => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨_, hφ x⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact comap_pCore_starGroup_le_normalCore hI h hz
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hLK hx

private theorem branchB_exists_sl2_quotKer (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hle : pLayerIn p H ≤ M)
    (hO : oPPrimeHull p (⊤ : Subgroup (StarGroup p H)) =
      starImg p H (pLayerIn p H) ⊔ oPPrimeHull p (cStarL p H))
    (hext : IsExtNotation (fun A _ => IsSLType 2 (ZMod p) A) (fun B _ => IsHomocyclicRank2 p B)
      ↥(oPPrimeHull p (cStarL p H))) :
    ∃ ψ : SL(2, ZMod p) →* ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H))),
      Function.Surjective ψ := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨φ, hφs, hφp, hφL⟩ := branchB_exists_starToQuotKer hI h hle
  have hIX : oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) = (oPPrimeHull p (cStarL p H)).map φ := by
    rw [← Subgroup.map_top_of_surjective φ hφs, ← S631.map_oPPrimeHull, hO, Subgroup.map_sup, hφL,
      bot_sup_eq]
  obtain ⟨N, hNn, hNh, ⟨e⟩, -⟩ := hext
  have : (oPPrimeHull p (cStarL p H)).Normal :=
    oPPrimeHull_normal p (cStarL_normal_of_prime h.p_prime H)
  rw [hIX]
  exact branchB_exists_sl2_map (isPGroup_of_isHomocyclicRank2 hNh) e φ hφp

theorem false_of_nineTen_branchB (h10 : NineTenGen) (h310 : ThreeTen) (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hne : pLayerIn p H ≠ ⊥)
    (hle : pLayerIn p H ≤ M) : False := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
  have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
    hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hD.card_eq] at hcard
    exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcard
  obtain ⟨P, hp, hp2, hdp', hd2, hdne, hIeq, hDsyl, hDne, hPsyl, hY, hγ, hN⟩ :=
    exists_threeTenHyp_quotKer hI h hns hd hle hD hD1
  have h3 := h310 _ _ _ P _ p d hp hp2 hdp' hd2 hdne hIeq hDsyl hDne hPsyl hY hγ hN
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  rcases nineTen_branchB_of_twelveCtx h10 h hEQ hE hEc hΓ hne hle with
    ⟨rfl, -, -, hpsl⟩ | ⟨hp3, -, -, hO, hext⟩ | ⟨rfl, -, -, -, hpsl⟩
  · exact branchB_false_of_dvd_four hdp' hd2 (h3 (Or.inl (Or.inr (Or.inl hpsl)))).2.2.2.1
  · have hp5 : 5 ≤ p := by
      rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h5
      · exact absurd (h4 ▸ hp) (by decide)
      · exact h5
    have hI1 : oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ≠ ⊥ := by
      intro hb
      rw [hb, bot_sup_eq] at hY
      have hDM : quotKerImg M H D ≤ quotKerImg M H M := Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mp (hD.le (Subgroup.mem_subgroupOf.mp hx))).2
      exact lt_irrefl _ (lt_of_le_of_lt (le_inf hDM le_rfl) hY)
    have := (Subgroup.nontrivial_iff_ne_bot _).mpr hI1
    obtain ⟨ψ, hψ⟩ := branchB_exists_sl2_quotKer hI h hle hO hext
    have hcase := branchB_isSLType_or_isPSLType hp5 ψ hψ
    exact branchB_false_of_isSLType_three ψ hψ
      (h3 (Or.inl (hcase.elim Or.inl fun h' => Or.inr (Or.inl h')))).2.2.1
  · exact branchB_false_of_dvd_four hdp' hd2 (h3 (Or.inl (Or.inr (Or.inl hpsl)))).2.2.2.1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
