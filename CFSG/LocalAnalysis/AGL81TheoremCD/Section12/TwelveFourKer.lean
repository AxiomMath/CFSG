module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveFrattini
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.GroupTheory.PCore.RelPPrimeCoreMap
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem relPPrimeCore_le_of_le_normal (hp : p.Prime) {K H : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).Normal) :
    relPPrimeCore p K ≤ relPPrimeCore p H := by
  have hNleH : relPPrimeCore p K ≤ H :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le K).trans
      hKH
  refine le_sSup (s := {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧
    Nat.Coprime p (Nat.card N)}) ⟨hNleH, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hNleH]
    intro x k hx hk
    have hKmap : K.map (MulAut.conj k).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK hk)
    have hmap : (relPPrimeCore p K).map (MulAut.conj k).toMonoidHom = relPPrimeCore p K := by
      rw [← CFSG.Open.relPPrimeCore_map_mulEquiv (MulAut.conj k) K p, hKmap]
    have hxmap : k * x * k⁻¹ ∈ (relPPrimeCore p K).map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, MulAut.conj_apply k x⟩
    rwa [hmap] at hxmap
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      hp K

theorem kerIn_eq (M K : Subgroup G) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.kerIn M K =
      CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M K := by
  unfold CFSG.LocalAnalysis.RankThreeUC.AGL81C.kerIn
    CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn
  have hsub : (M ⊓ K).subgroupOf K = M.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [hsub]

theorem p_ne_five_of_dvd_p_add_one {d : ℕ} (hd : d.Prime) (h5 : 5 ≤ d)
    (hdvd : d ∣ p + 1) : p ≠ 5 := by
  intro hp
  subst hp
  have hd6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) (by simpa using hdvd)
  have hcases : d = 5 ∨ d = 6 := by omega
  rcases hcases with rfl | rfl
  · norm_num at hdvd
  · norm_num at hd

theorem commutator_le_relPPrimeCore_kSub_of_le_xSub
    (h : TwelveCtx G M p Q H) (hK : ((kSub p M H).subgroupOf H).Normal)
    {W : Subgroup G} (hW : W ≤ xSub p M H) :
    ⁅W, kSub p M H⁆ ≤ relPPrimeCore p (kSub p M H) := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hkH : k ∈ H := kSub_le p M H hk
  have hwX : w ∈ CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H) := hW hw
  obtain ⟨wH, hwCent, rfl⟩ := Subgroup.mem_map.mp hwX
  let π : ↥H →* (↥H ⧸ primeComplementCore (G := ↥H) p) :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let kH : ↥H := ⟨k, hkH⟩
  have hkKstar : π kH ∈ kStar p M H := by
    refine Subgroup.mem_map.mpr ⟨kH, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hk
  have hcomm : π kH * π wH = π wH * π kH :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hwCent)) (π kH) hkKstar
  have hker : π (wH * kH * wH⁻¹ * kH⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π wH * π kH * (π wH)⁻¹ * (π kH)⁻¹
        = (π kH * π wH) * (π wH)⁻¹ * (π kH)⁻¹ := by rw [← hcomm]
      _ = 1 := by group
  have hmemO : ((wH * kH * wH⁻¹ * kH⁻¹ : ↥H) : G) ∈ relPPrimeCore p H := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      h.p_prime H]
    refine Subgroup.mem_map.mpr ⟨(wH * kH * wH⁻¹ * kH⁻¹ : ↥H), ?_, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) _).mp hker
  have hmemK : ((wH * kH * wH⁻¹ * kH⁻¹ : ↥H) : G) ∈ kSub p M H := by
    have hnorm := (Subgroup.normal_subgroupOf_iff (kSub_le p M H)).mp hK
    have h1 : (wH : G) * k * (wH : G)⁻¹ ∈ kSub p M H := hnorm k wH hk wH.2
    have h2 : ((wH * kH * wH⁻¹ * kH⁻¹ : ↥H) : G) =
        (wH : G) * k * (wH : G)⁻¹ * k⁻¹ := by
      simp [kH]
    rw [h2]
    exact (kSub p M H).mul_mem h1 ((kSub p M H).inv_mem hk)
  exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.inf_relPPrimeCore_le_relPPrimeCore h.p_prime
    (kSub_le p M H) hK ⟨hmemK, hmemO⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12