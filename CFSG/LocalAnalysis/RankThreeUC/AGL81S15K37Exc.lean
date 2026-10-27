module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSplit
public import CFSG.LieType.SeitzGeneration.QuasiHigh
import CFSG.LocalAnalysis.UniquenessCase.UC6K316Sp
import CFSG.RankThree.PartOne.HNB.InnerAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)

variable {X : Type} [Group X] [Finite X] {K E S : Subgroup X}

namespace K37Setting

theorem center_eq_bot_of_not_coverIndex
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h : K37Setting X K E S) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : 3 ≠ d.1.characteristic) (hci : ¬ QuasiHigh.CoverIndex 3 d.1) :
    Subgroup.center ↥K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h.isPGroup_center.card_eq_or_dvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (QuasiHigh.coverIndex_of_dvd_card_center hGA Nat.prime_three (by norm_num)
      ⟨Group.isPerfect_def.mp h.quasi.1, h.quasi.2.1⟩ d e hpd h3) hci

theorem center_eq_bot (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h : K37Setting X K E S) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hexc : (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨ d.1 = .tits) :
    Subgroup.center ↥K = ⊥ := by
  rcases hexc with ⟨q, hq, -, hdq⟩ | ⟨q, hq, -, hdq⟩ | hdq
  · refine h.center_eq_bot_of_not_coverIndex hGA d e ?_ ?_ <;> rw [hdq]
    · rw [TauCeti.LieTypeIndex.characteristic_A, hq]
      norm_num
    · exact fun hci => absurd hci.1 (by norm_num)
  · refine h.center_eq_bot_of_not_coverIndex hGA d e ?_ ?_ <;> rw [hdq]
    · rw [TauCeti.LieTypeIndex.characteristic_B, hq]
      norm_num
    · exact fun hci => hci
  · refine h.center_eq_bot_of_not_coverIndex hGA d e ?_ ?_ <;> rw [hdq]
    · rw [TauCeti.LieTypeIndex.characteristic_tits]
      norm_num
    · exact fun hci => hci

theorem orderOf_of_inner (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥) {e k : X}
    (he : e ∈ E) (he1 : e ≠ 1) (hk : k ∈ K) (hek : ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹) :
    orderOf (⟨k, hk⟩ : ↥K) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
  set n : ↥(Subgroup.normalizer (K : Set X)) := ⟨e, h.le_normalizer_K he⟩ with hn
  have hφ : K.normalizerMonoidHom n = MulAut.conj (⟨k, hk⟩ : ↥K) :=
    MulEquiv.ext fun y => Subtype.ext (by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      exact hek y y.2)
  have hn3 : n ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.elem.2 e he)
  refine orderOf_eq_prime (hinj ?_) fun h1 => he1 ?_
  · rw [map_pow, ← hφ, ← map_pow, hn3, map_one, map_one]
  · have hker : n ∈ K.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, hφ, h1, map_one]
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    have hmem : e ∈ E ⊓ Subgroup.centralizer (K : Set X) := ⟨he, Subgroup.mem_subgroupOf.mp hker⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem

theorem exists_card_eq_le_gamma (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥)
    (hin : autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) (h27 : 3 ^ 3 ∣ Nat.card ↥K) :
    ∃ R : Subgroup ↥K, Nat.card R = 3 ^ 3 ∧ ∀ g ∈ R, (g : X) ∈ rankThreeGamma 1 3 E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
  set F : Subgroup ↥K := (autIm E K).comap (MulAut.conj : ↥K →* MulAut ↥K) with hF
  have hF9 : Nat.card F = 3 ^ 2 := by
    rw [← h.card_autIm, ← Subgroup.map_comap_eq_self hin, Subgroup.card_map_of_injective hinj]
  obtain ⟨R, hR, hFR⟩ := Sylow.exists_subgroup_card_pow_prime_le 3 h27 F hF9 (by norm_num)
  refine ⟨R, hR, ?_⟩
  haveI : Group.IsNilpotent ↥R := (IsPGroup.of_card hR).isNilpotent
  have hrel : (F.subgroupOf R).index = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := F) (K := R)
    rw [inf_of_le_left hFR, hF9, hR] at h1
    change F.relIndex R = 3
    norm_num at h1
    omega
  haveI : (F.subgroupOf R).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hrel, hR]; norm_num)
  have hne : F.subgroupOf R ≠ ⊥ := by
    intro hb
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv
    rw [hb, Subgroup.card_bot, hF9] at hc
    norm_num at hc
  obtain ⟨⟨z, hzF, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hz1' : (z : ↥K) ≠ 1 := fun h1 => hz1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨n, hnE, hn⟩ :=
    Subgroup.mem_map.mp (Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hzF))
  have hek : ∀ y ∈ K, (n : X) * y * (n : X)⁻¹ = ((z : ↥K) : X) * y * ((z : ↥K) : X)⁻¹ := by
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) hn
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h1
    exact h1
  have hn1 : (n : X) ≠ 1 := by
    intro h1
    have hn' : n = 1 := Subtype.ext h1
    rw [hn', map_one] at hn
    exact hz1' (hinj (hn.symm.trans (map_one _).symm))
  intro g hg
  exact h.mem_gamma_of_inner (Subgroup.mem_subgroupOf.mp hnE) hn1 hek g.2
    (congrArg (fun x : ↥R => ((x : ↥K) : X)) (Subgroup.mem_center_iff.mp hzZ ⟨g, hg⟩))

theorem le_centralizer_l28 (hL28 : CFSG.AGLEmbedding.KFactCaseTwoNoTwoL28)
    (hK35 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeFiveInner)
    (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q)
    (e : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) : S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨g, hg, hg1, k, hk, hgk⟩ := hK35 X h.catalog K E h.normal h.quasi h.core h.elem h.card
    h.rank23 h.rank_gamma h.not_le
  have hkΓ : k ∈ rankThreeGamma 1 3 E := h.mem_gamma_of_inner hg hg1 hgk hk rfl
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
    (hL28 3 ↥K ⟨rfl, d, hd, ⟨e⟩⟩ ⟨k, hk⟩ (h.orderOf_of_inner hZ hg hg1 hk hgk) (autIm S K)
      (isPGroup_autIm h.two) (h.conj_mem_normalizer_autIm hk hkΓ))

end K37Setting

section Sp6

variable {F : Type} [Field F] [Finite F]

theorem eq_bot_of_normalizes_sp6 (hF : Nat.card F = 2) {U R : Subgroup (StatedSp 3 F)}
    (hU : IsPGroup 2 U) (hR : Nat.card R = 3 ^ 3)
    (hRU : R ≤ Subgroup.normalizer (U : Set (StatedSp 3 F))) : U = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨a, ha1, ha3, hdvd⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.exists_card_dvd_of_normalizes_sp hF hU hne
      (IsPGroup.of_card hR) hRU
  rw [hR] at hdvd
  revert hdvd
  interval_cases a <;> decide

theorem exists_eq_conj_sp6 (hF : Nat.card F = 2) {L : Type} [Group L]
    (eP : L ≃* StatedProj (StatedSp 3 F)) (α : MulAut L) : ∃ k : L, α = MulAut.conj k := by
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.exists_eq_conj_statedProj_sp hF le_rfl (MulAut.congr eP α)
  refine ⟨eP.symm x, (MulAut.congr eP).injective ?_⟩
  rw [hx, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]

end Sp6

namespace K37Setting

theorem le_centralizer_sp6 (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) (hq1 : q.exponent = 1)
    {hv : (TauCeti.LieTypeIndex.B 3 q).Valid}
    (e : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  obtain ⟨-, F, _, _, hF, ⟨eP⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2 le_rfl e
  have hF2 : Nat.card F = 2 := by rw [hF, hq2, hq1, pow_one]
  have hinn : ∀ α : MulAut ↥K, α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun α =>
    (exists_eq_conj_sp6 hF2 eP α).elim fun k hk => ⟨k, hk.symm⟩
  have hinj := CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
  have h27 : 3 ^ 3 ∣ Nat.card ↥K := by
    rw [Nat.card_congr eP.toEquiv,
      CFSG.LocalAnalysis.UniquenessCase.UCK.card_statedProj_sp hF2 3 (by norm_num)]
    decide
  obtain ⟨R, hR, hRΓ⟩ := h.exists_card_eq_le_gamma hZ (fun α _ => hinn α) h27
  set U : Subgroup ↥K := (autIm S K).comap (MulAut.conj : ↥K →* MulAut ↥K) with hU
  have hUmap : U.map (MulAut.conj : ↥K →* MulAut ↥K) = autIm S K :=
    Subgroup.map_comap_eq_self fun α _ => hinn α
  have hRU : R ≤ Subgroup.normalizer (U : Set ↥K) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hc : MulAut.conj (g * u * g⁻¹) = MulAut.conj g * MulAut.conj u * (MulAut.conj g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    change MulAut.conj u ∈ autIm S K ↔ MulAut.conj (g * u * g⁻¹) ∈ autIm S K
    rw [hc]
    exact Subgroup.mem_normalizer_iff.1 (h.conj_mem_normalizer_autIm g.2 (hRΓ g hg)) _
  have hpi := CFSG.RankThree.PartOne.proj_injective_sp (r := 3) (K := F) (f := 1)
    (by rw [hF2]; norm_num) le_rfl (by norm_num)
  set eS : ↥K ≃* StatedSp 3 F := eP.trans (MulEquiv.ofBijective
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 3 F)
    ⟨hpi, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩).symm with heS
  have hbot := eq_bot_of_normalizes_sp6 hF2 (U := U.map eS.toMonoidHom) (R := R.map eS.toMonoidHom)
    (((isPGroup_autIm h.two).comap_of_injective _ hinj).map _)
    (by rw [Subgroup.card_map_of_injective eS.injective, hR])
    ((Subgroup.map_mono hRU).trans (Subgroup.le_normalizer_map _))
  have hUb : U = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective U (f := eS.toMonoidHom) eS.injective).mp hbot
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K (by rw [← hUmap, hUb, Subgroup.map_bot])

end K37Setting

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
