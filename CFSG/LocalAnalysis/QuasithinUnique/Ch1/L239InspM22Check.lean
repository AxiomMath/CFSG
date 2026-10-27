module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Block
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22CheckInputs
public import Certificates.Certificate4087
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public meta import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Block
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Structure318Red
public meta import CFSG.Quasithin.Background.A3Structure36A
public meta import CFSG.Quasithin.Background.A3Structure36BAction
public meta import CFSG.Quasithin.Background.A3Structure36BBase
public meta import CFSG.Quasithin.Background.A3Structure36BCase3Base
public meta import CFSG.Quasithin.Background.A3Structure36BCasesBase
public meta import CFSG.Quasithin.Background.A3Structure36BCommonBase
public meta import CFSG.Quasithin.Background.A3Structure36BFrattini
public meta import CFSG.Quasithin.Background.A3Structure36BHeisBase
public meta import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public meta import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public meta import CFSG.Quasithin.Background.A3Structure36BStarBase
public meta import CFSG.Quasithin.Background.A3Structure36Base
public meta import CFSG.Quasithin.Background.A3Structure37Base
public meta import CFSG.Quasithin.Background.A3Structure37Comm
public meta import CFSG.Quasithin.Background.A3Structure37Frattini
public meta import CFSG.Quasithin.Background.A3Structure37KeyBase
public meta import CFSG.Quasithin.Background.A3Structure37Schur
public meta import CFSG.Quasithin.Background.A3Structure38Part3
public meta import CFSG.Quasithin.Background.B1MoreElevenE
public meta import CFSG.Quasithin.Background.B1MoreNineG
public meta import CFSG.Quasithin.Background.B4ModelsAction
public meta import CFSG.Quasithin.Background.B4ModelsIso
public meta import CFSG.Quasithin.Background.C2Basic
public meta import CFSG.Quasithin.Background.C2Inputs
public meta import CFSG.Quasithin.Background.E1
public meta import CFSG.Quasithin.Background.E1Sec4
public meta import CFSG.Quasithin.Background.E1Sec5
public meta import CFSG.Quasithin.Background.E1Sec8
public meta import CFSG.Quasithin.Background.E1Solv
public meta import CFSG.Quasithin.Background.E1Twelve
public meta import CFSG.Quasithin.Background.E3Cent
public meta import CFSG.Quasithin.Vol2.Ch1Local
public meta import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public meta import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Setup.X1

namespace M22Insp

theorem chk_card : data.B₀.card = 6 :=
  Certificates.certificate4087.1

theorem chk_H_reach :
    Reach data.gens data.B₀ data.H data.hp data.hl :=
  Certificates.certificate4087.2.1

theorem chk_H_closed : ClosedUnder data.gens data.H :=
  Certificates.certificate4087.2.2.1

theorem chk_H_nodup : data.H.Nodup :=
  Certificates.certificate4087.2.2.2.1

theorem chk_ks_fix : ∀ g ∈ data.ks, g • data.B₀ = data.B₀ :=
  Certificates.certificate4087.2.2.2.2.1

theorem chk_R₁_reach :
    Reach data.ks data.r₁ data.R₁ data.p₁ data.l₁ :=
  Certificates.certificate4087.2.2.2.2.2.1

theorem chk_R₂_reach :
    Reach data.ks data.r₂ data.R₂ data.p₂ data.l₂ :=
  Certificates.certificate4087.2.2.2.2.2.2.1

theorem chk_R₁_nodup : data.R₁.Nodup :=
  Certificates.certificate4087.2.2.2.2.2.2.2.1

theorem chk_R₂_nodup : data.R₂.Nodup :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.1

theorem chk_R₁_sub : AllMem data.R₁ (fun B => B ∈ data.H) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.1

theorem chk_R₂_sub : AllMem data.R₂ (fun B => B ∈ data.H) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.1

theorem chk_B₀_not₁ : data.B₀ ∉ data.R₁ :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_B₀_not₂ : data.B₀ ∉ data.R₂ :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_cover :
    AllMem data.H (fun B => B ≠ data.B₀ → B ∈ data.R₁ ∨ B ∈ data.R₂) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_lev₁ : AllMem data.H
    (fun B => B ≠ data.B₀ → (B ∈ data.R₁ ↔ (B ∩ data.B₀).card = data.c₁)) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_lev₂ : AllMem data.H
    (fun B => B ≠ data.B₀ → (B ∈ data.R₂ ↔ (B ∩ data.B₀).card = data.c₂)) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_harith :
    ∀ k ∈ List.range data.H.length, k ∣ data.H.length →
    k < 1 + data.R₁.length ∧ k < 1 + data.R₂.length :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_T_reach : Reach data.ks data.t₀ data.T data.tp data.tl :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_T_nodup_map : (data.T.map enc).Nodup :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_T_nodup : data.T.Nodup :=
  List.Nodup.of_map enc chk_T_nodup_map

theorem chk_t₀_mem : ∀ i, data.t₀ i ∈ data.B₀ :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_Es_len : data.Es.length = 16 :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_Es_nodup : data.Es.Nodup :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_Es_fix : ∀ e ∈ data.Es, ∀ x ∈ data.B₀, e • x = x :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_Es_sq : ∀ e ∈ data.Es, e * e = 1 :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_Es_comm : ∀ e ∈ data.Es, ∀ f ∈ data.Es, e * f = f * e :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_noncentral :
    ∃ k ∈ data.ks, ∃ e ∈ data.Es, k * e ≠ e * k :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_T_len : data.T.length * 2 = Nat.factorial 6 :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_num_M :
    data.H.length * (16 * data.T.length) = 2 ^ data.e * data.u :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_num_K : 16 * data.T.length = 2 ^ data.e * data.u' :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_div₁ :
    ¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₁.length :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_div₂ :
    ¬ 2 ^ data.e ∣ (2 ^ data.e * data.u') / data.R₂.length :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_delta :
    AllMem data.H (fun B => delta • B ∈ data.H) :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem valid : data.Valid where
  card_B₀ := chk_card
  H_reach := chk_H_reach
  H_closed := chk_H_closed
  H_nodup := chk_H_nodup
  ks_fix := chk_ks_fix
  R₁_reach := chk_R₁_reach
  R₂_reach := chk_R₂_reach
  R₁_nodup := chk_R₁_nodup
  R₂_nodup := chk_R₂_nodup
  R₁_sub := chk_R₁_sub
  R₂_sub := chk_R₂_sub
  B₀_not₁ := chk_B₀_not₁
  B₀_not₂ := chk_B₀_not₂
  cover := chk_cover
  lev₁ := chk_lev₁
  lev₂ := chk_lev₂
  harith := chk_harith
  T_reach := chk_T_reach
  T_nodup := chk_T_nodup
  t₀_mem := chk_t₀_mem
  Es_len := chk_Es_len
  Es_nodup := chk_Es_nodup
  Es_fix := chk_Es_fix
  Es_sq := chk_Es_sq
  Es_comm := chk_Es_comm
  noncentral := chk_noncentral
  T_len := chk_T_len
  num_M := chk_num_M
  odd_u := by decide
  num_K := chk_num_K
  odd_u' := by decide
  div₁ := chk_div₁
  div₂ := chk_div₂

theorem chk_H_len : data.H.length = 77 :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chk_T_len' : data.T.length = 360 :=
  Certificates.certificate4087.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end M22Insp

end CFSG.QuasithinUnique.Vol2Native.L239
