module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Reduce
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

private theorem max614_fusionIsSylowIn (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    fusionIsSylowIn 2 T (GLBPrimeCore 3 M) := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore 3 M
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBM : B ≤ M := (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hPM
  obtain ⟨⟨hTM, hT2, hBT⟩, hmax⟩ := hT
  have hT3 : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hTD : T ≤ D := by
    have : Group.IsSolvable M := hsolv
    exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
      (solvable_hasPrimeConstraint (G := M) 3 Nat.prime_three) hB3 hBM
      (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
        rw [← hord]
        exact pow_orderOf_eq_one y)) hTM hT3 hBT
  have hD3 : ¬ 3 ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)
  have hBD : B ≤ normalizer (D : Set G) :=
    hBM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  obtain ⟨R, hRsyl, hTR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hTD hT2 hBT
  have hRT : R = T :=
    hmax R ⟨hRsyl.1.trans (CFSG.AGLEmbedding.glbPrimeCore_le 3 M), hRsyl.2.1, hBR⟩ hTR
  rwa [← hRT]

set_option linter.unusedVariables false in
theorem exists_conj_le_normalizer_of_isMax (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    ∃ g : G, g ∈ M ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ normalizer (T : Set G) := by
  set D : Subgroup G := GLBPrimeCore 3 M
  have hTD : fusionIsSylowIn 2 T D := max614_fusionIsSylowIn hS hsit hsolv hx hz hT
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hD3 : ¬ 3 ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)
  have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) :=
    hPM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hbot3 : IsPGroup 3 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hSsyl, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two P.isPGroup' hD3 hPD bot_le hbot2 hPbot
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three Nat.prime_two hbot3 hD3 bot_le hSsyl hTD bot_le bot_le
  refine ⟨c, CFSG.AGLEmbedding.glbPrimeCore_le 3 M (mem_inf.mp hc).1, ?_⟩
  rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
  exact map_mono hPS

private theorem max614_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

omit [Finite G] in
private theorem max614_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) : Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, wreath_card_zmod_three]
  norm_num

theorem isMax_top_of_isMax (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) (hT1 : T ≠ ⊥) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set G) := hT.1.2.2
  refine ⟨⟨le_top, hT2, hBT⟩, fun R hR hTR => ?_⟩
  obtain ⟨-, hR2, hBR⟩ := hR
  by_contra hne
  have hlt : T < R := lt_of_le_of_ne hTR (Ne.symm hne)
  obtain ⟨y, hyR, hyN, hyT⟩ := max614_exists_mem_normalizer_not_mem hR2 hlt
  set L : Subgroup G := normalizer (T : Set G)
  have hL : IsTwoLocal L := ⟨T, hT1, hT2, rfl⟩
  obtain ⟨g, hgM, hYL⟩ := exists_conj_le_normalizer_of_isMax hS hU0 hsit hsolv hx hz hT
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  set Y : Subgroup G := (P : Subgroup G).map (MulAut.conj g).toMonoidHom
  have hYM : Y ≤ M := by
    rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hPM ha)) (M.inv_mem hgM)
  have hY3 : IsPGroup 3 Y := P.isPGroup'.map _
  have hYc : Nat.card Y = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact max614_card_eq_eighty_one e
  have hLM : L ≤ M := le_of_twentySeven_le_card hS hU0 hD2 hsit hsolv e hL hYL hYM hY3 (by omega)
  have hBL : B ≤ normalizer (L : Set G) := hBT.trans le_normalizer
  have hR₁ : IsTwoInvariantIn B M (R ⊓ L) :=
    ⟨inf_le_right.trans hLM, hR2.to_le inf_le_left,
      (le_inf hBR hBL).trans inf_normalizer_le_normalizer_inf⟩
  have hR₁T := hT.2 (R ⊓ L) hR₁ (le_inf hTR le_normalizer)
  exact hyT (hR₁T ▸ mem_inf.mpr ⟨hyR, hyN⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
