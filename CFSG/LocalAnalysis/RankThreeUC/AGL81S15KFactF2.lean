module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89Sp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactF2Mod
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactF2A4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreAction
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrob
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace KFactF2Proof

open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)

theorem act_mul_apply {Z M : Type*} [Group Z] [Group M] (ρ : Z →* MulAut M) (a b : Z) (x : M) :
    ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul, MulAut.mul_apply]

theorem trivial_of_fpf {Z : Type} [Group Z] [Finite Z] (hZ : IsLThreeTwo Z) {c : Z}
    (hc : orderOf c = 3) {M : Type*} [CommGroup M] (hodd : ∀ x : M, x * x = 1 → x = 1)
    (ρ : Z →* MulAut M) (hfix : ∀ x : M, ρ c x = x → x = 1) (x : M) : x = 1 := by
  obtain ⟨u, v, d, hu1, huu, hvv, huv, hd3, hdc, hdu, hdv⟩ := exists_a4_pair hZ hc
  have hfixd : ∀ m : M, ρ d m = m → m = 1 := by
    intro m hm
    rcases hdc with rfl | rfl
    · exact hfix m hm
    · apply hfix m
      calc ρ c m = ρ c (ρ c⁻¹ m) := by rw [hm]
        _ = m := by rw [← act_mul_apply, mul_inv_cancel, map_one, MulAut.one_apply]
  have hd3' : d * d * d = 1 := by rw [← pow_two, ← pow_succ]; exact hd3
  have hrel : A4Rel (ρ u) (ρ v) (ρ d) :=
    { sq_σ := fun m => by rw [← act_mul_apply, huu, map_one, MulAut.one_apply]
      sq_τ := fun m => by rw [← act_mul_apply, hvv, map_one, MulAut.one_apply]
      comm := fun m => by rw [← act_mul_apply, ← act_mul_apply, huv]
      cube := fun m => by
        rw [← act_mul_apply, ← act_mul_apply, hd3', map_one, MulAut.one_apply]
      ασ := fun m => by rw [← act_mul_apply, ← act_mul_apply, hdu]
      ατ := fun m => by
        rw [← act_mul_apply, ← act_mul_apply, ← act_mul_apply, hdv, mul_assoc] }
  have hσ : ∀ m : M, ρ u m = m := fun m => hrel.apply_eq hodd hfixd m
  have hsimple : IsSimpleGroup Z := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple hZ
  have hker : ρ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exfalso
      have hu : u ∈ ρ.ker := MulEquiv.ext hσ
      rw [h, Subgroup.mem_bot] at hu
      exact hu1 hu
    · exact h
  have hρc : ρ c = 1 := by
    have : c ∈ ρ.ker := by rw [hker]; trivial
    exact this
  exact hfix x (by rw [hρc]; rfl)

theorem no_two_torsion {W : Type*} [Group W] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpW : ∀ w : W, w ^ p = 1) (w : W) (hw : w * w = 1) : w = 1 := by
  have hk : p = 2 * (p / 2) + 1 := by
    have := hp.eq_two_or_odd.resolve_left hp2
    omega
  calc w = (w * w) ^ (p / 2) * w := by rw [hw, one_pow, one_mul]
    _ = w ^ p := by rw [← pow_two, ← pow_mul, ← pow_succ, ← hk]
    _ = 1 := hpW w

end KFactF2Proof

open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex (ActInv actSub)
open KFactF2Proof (no_two_torsion trivial_of_fpf)

theorem KFactL32OddFix_holds : KFactL32OddFix := by
  unfold KFactL32OddFix
  intro Y _ _ hY a ha S hS I _ _ hcomm hexp ρ hfix x hx
  obtain ⟨p, hp, hp2, hpI⟩ := hexp
  letI : CommGroup I := { ‹Group I› with mul_comm := hcomm }
  set P := CFSG.pCore 2 Y
  have hPn : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : P ≤ S := by
    have hsup : IsPGroup 2 ↥(S ⊔ P) := hS.isPGroup.to_sup_of_normal_right hP2
    have hq := hS.eq_of_le le_sup_left le_top hsup
    rw [← hq]
    exact le_sup_right
  let W : Subgroup I :=
    { carrier := {x | ∀ q ∈ P, ρ q x = x}
      mul_mem' := fun {x y} hx hy q hq => by rw [map_mul, hx q hq, hy q hq]
      one_mem' := fun q _ => map_one _
      inv_mem' := fun {x} hx q hq => by rw [map_inv, hx q hq] }
  have hPW : ∀ q ∈ P, ∀ w ∈ W, ρ q w = w := fun q hq w hw => hw q hq
  have hW : ActInv ρ W := by
    intro y x hx q hq
    have hq' : y⁻¹ * q * y ∈ P := by
      have := hPn.conj_mem q hq y⁻¹
      simpa using this
    have e : ρ q (ρ y x) = ρ y (ρ (y⁻¹ * q * y) x) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hx _ hq']
  have hodd : ∀ w : ↥W, w * w = 1 → w = 1 :=
    no_two_torsion hp hp2 (fun w => Subtype.ext (by simpa using hpI w))
  let ρ' : Y ⧸ P →* MulAut ↥W :=
    QuotientGroup.lift P (actSub ρ W hW) (fun q hq =>
      MulEquiv.ext fun w => Subtype.ext (hPW q hq w w.2))
  have hmk : ∀ y : Y, ρ' (QuotientGroup.mk y) = actSub ρ W hW y := fun y =>
    QuotientGroup.lift_mk _ _ y
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  have haP : a ∉ P := by
    intro h
    obtain ⟨k, hk⟩ := hP2 ⟨a, h⟩
    have h1 : orderOf a ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [ha] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hc : orderOf (QuotientGroup.mk a : Y ⧸ P) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ha3, QuotientGroup.mk_one]
    · intro h
      exact haP ((QuotientGroup.eq_one_iff _).1 h)
  have hfixW : ∀ w : ↥W, ρ' (QuotientGroup.mk a) w = w → w = 1 := by
    intro w hw
    rw [hmk] at hw
    exact Subtype.ext (hfix w (congrArg Subtype.val hw))
  have key := trivial_of_fpf hY hc hodd ρ' hfixW ⟨x, fun q hq => hx q (hPS hq)⟩
  exact congrArg Subtype.val key

end CFSG.LocalAnalysis.RankThreeUC.S15
