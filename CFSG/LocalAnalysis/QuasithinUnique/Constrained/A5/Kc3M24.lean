module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3X1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24Inputs
public import Certificates.Certificate4119
public import Certificates.Certificate3017
public import Certificates.Certificate17029
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3StructureBasic
public meta import CFSG.Quasithin.Background.B1Basic
public meta import CFSG.Quasithin.Background.C1GNInputs
public meta import CFSG.Quasithin.Background.C1GNNotation
public meta import CFSG.Quasithin.EmptyFaithful.QTKELocal
public meta import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public meta import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.A5.Kc3M24

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.A5.Kc3M24Data

theorem isEnc : IsEnc enc :=
  ⟨RN.enc_inj.comp Subtype.val_injective, fun _ _ => RN.enc_mul _ _, RN.enc_one⟩

theorem card_m24 : Nat.card ↥NativeSporadic.M24 = 244823040 := card_M24

theorem hexE_core : hexE.coreCheckT gR 244823040 = true :=
  Certificates.certificate4119.1

theorem octE1_core : octE1.coreCheckT gR 244823040 = true :=
  Certificates.certificate4119.2.1

theorem octE2_core : octE2.coreCheckT gR 244823040 = true :=
  Certificates.certificate4119.2.2.1

theorem octE3_core : octE3.coreCheckT gR 244823040 = true :=
  Certificates.certificate4119.2.2.2.1

theorem octE4_core : octE4.coreCheckT gR 244823040 = true :=
  Certificates.certificate4119.2.2.2.2.1

theorem hexE_V : hexE.hypVCheck gR omW = true :=
  Certificates.certificate4119.2.2.2.2.2.1

theorem octE1_D : octE1.hypDCheck gR = true :=
  Certificates.certificate4119.2.2.2.2.2.2.1

theorem octE2_D : octE2.hypDCheck gR = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.1

theorem octE3_D : octE3.hypDCheck gR = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.1

theorem octE4_D : octE4.hypDCheck gR = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.1

theorem x0_check : (xPow X 5 == 1 && X != 1) = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.1

theorem x0N_hex : (hexE.Ns gR).contains X = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0N_oct1 : (octE1.Ns gR).contains X = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0N_oct2 : (octE2.Ns gR).contains X = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0N_oct3 : (octE3.Ns gR).contains X = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0N_oct4 : (octE4.Ns gR).contains X = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem P_check : subgroupCheck gR pW pDepth 1024 = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem I_closed :
    conjClosed (enc m24a) (enc m24b) (enc m24a⁻¹) (enc m24b⁻¹) Iset = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem I_seeds :
    (invSeeds Ps).all (fun x => Iset.contains x) = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem y_check :
    Iset.toList.all (yCheck X (hexE.Es gR) (octE1.Es gR) (octE2.Es gR) (octE3.Es gR)
    (octE4.Es gR)) = true :=
  Certificates.certificate4119.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem mem_invSeeds {x : RN 24} (hx : x ∈ Ps) (h1 : x * x = 1) (h2 : x ≠ 1) :
    x ∈ invSeeds Ps := by
  unfold invSeeds
  rw [List.mem_filter]
  exact ⟨Std.HashSet.mem_toList.2 hx, by simp [h1, h2]⟩

theorem locClass2_m24 : LocClass2 ↥NativeSporadic.M24 := by
  obtain ⟨E₀, N₀, hs₀⟩ := hexE.exists_soundT isEnc m24a m24b 244823040 card_m24 hexE_core
  obtain ⟨E₁, N₁, hs₁⟩ := octE1.exists_soundT isEnc m24a m24b 244823040 card_m24 octE1_core
  obtain ⟨E₂, N₂, hs₂⟩ := octE2.exists_soundT isEnc m24a m24b 244823040 card_m24 octE2_core
  obtain ⟨E₃, N₃, hs₃⟩ := octE3.exists_soundT isEnc m24a m24b 244823040 card_m24 octE3_core
  obtain ⟨E₄, N₄, hs₄⟩ := octE4.exists_soundT isEnc m24a m24b 244823040 card_m24 octE4_core
  obtain ⟨P, hPcard, hPmem⟩ := subgroup_sound isEnc m24a m24b pW pDepth 1024 P_check
  have hP : IsPGroup 2 P := IsPGroup.of_card (n := 10) (by rw [hPcard]; norm_num)
  have hPi : ¬ 2 ∣ P.index := by
    have h1 := Subgroup.card_mul_index P
    rw [hPcard, card_m24] at h1
    intro ⟨m, hm⟩
    omega
  have hab : Subgroup.closure ({m24a, m24b} : Set ↥NativeSporadic.M24) = ⊤ :=
    closure_pair_eq_top m24_eq _ _
  have hI : ∀ t : ↥NativeSporadic.M24, t * t = 1 → t ≠ 1 → enc t ∈ Iset := by
    intro t ht ht1
    refine involution_mem isEnc hab I_closed P hP hPi Ps hPmem ?_ t ht ht1
    intro x hx h1 h2
    have := List.all_eq_true.1 I_seeds x (mem_invSeeds hx h1 h2)
    simpa using this
  set x₀ : ↥NativeSporadic.M24 := evalW [m24a, m24b, m24a⁻¹, m24b⁻¹] xW with hx₀def
  have hencx : enc x₀ = X := enc_evalW isEnc _ xW
  have hx0 := x0_check
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx0
  obtain ⟨hX5, hX1⟩ := hx0
  have hx5 : x₀ ^ 5 = 1 := by
    apply isEnc.inj
    rw [enc_pow isEnc, hencx, isEnc.map_one]
    exact hX5
  have hx1 : x₀ ≠ 1 := by
    intro h
    apply hX1
    rw [← hencx, h, isEnc.map_one]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx₀ : orderOf x₀ = 5 := orderOf_eq_prime hx5 hx1
  have h25 : ¬ 25 ∣ Nat.card ↥NativeSporadic.M24 := by
    rw [card_m24]
    norm_num
  refine locClass2_of_x0 x₀ hx₀ h25 {t | enc t ∈ Iset} (fun t ht ht1 => hI t ht ht1)
    [E₀, E₁, E₂, E₃, E₄] ?_ ?_ ?_ ?_
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl
    · exact hs₀.cardE
    · exact hs₁.cardE
    · exact hs₂.cardE
    · exact hs₃.cardE
    · exact hs₄.cardE
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    have key : ∀ {c : ECert} {E N : Subgroup ↥NativeSporadic.M24},
        ECert.Sound enc m24a m24b c E N → (c.Ns gR).contains X = true →
          x₀ ∈ Subgroup.normalizer (E : Set ↥NativeSporadic.M24) := by
      intro c E N hs hX
      rw [← hs.hN, hs.memN, hencx]
      exact Std.HashSet.contains_iff_mem.1 hX
    rcases hF with rfl | rfl | rfl | rfl | rfl
    · exact key hs₀ x0N_hex
    · exact key hs₁ x0N_oct1
    · exact key hs₂ x0N_oct2
    · exact key hs₃ x0N_oct3
    · exact key hs₄ x0N_oct4
  · intro y hy
    have hy' := List.all_eq_true.1 y_check (enc y) (Std.HashSet.mem_toList.2 hy)
    exact yCheck_sound isEnc x₀ hx5 _ _ _ _ _ E₀ E₁ E₂ E₃ E₄ hs₀.memE hs₁.memE hs₂.memE hs₃.memE
      hs₄.memE y (by rw [hencx]; exact hy')
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (hs₀.hypV isEnc omW hexE_V))
    · exact Or.inr (Or.inl (hs₁.hypD isEnc octE1_D))
    · exact Or.inr (Or.inl (hs₂.hypD isEnc octE2_D))
    · exact Or.inr (Or.inl (hs₃.hypD isEnc octE3_D))
    · exact Or.inr (Or.inl (hs₄.hypD isEnc octE4_D))

end CFSG.QuasithinUnique.A5.Kc3M24

namespace CFSG.QuasithinUnique.A5

open CFSG.Blueprint

theorem kc3LocalFor_m24 : Kc3LocalFor (Kc3Spor .M24) := by
  intro X _ _ ⟨e⟩
  exact kc3LocalData_of_locClass2 (LocClass2.of_equiv e Kc3M24.locClass2_m24)

end CFSG.QuasithinUnique.A5
