module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
public import CFSG.Quasithin.Vol2.KGFactC31M24Nor
public import CFSG.Quasithin.Vol2.KGFactC31M24Lat
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.SectionRank.QTK.Insp443.M24

open CFSG.Open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24 _root_.Certificates

private theorem row_of_le
    {X Y : Subgroup G₀} (hXY : X ≤ Y)
    (hX : 1024 ∣ Nat.card X) (hY : Y ≠ ⊤) :
    ∃ m ∈ m24Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 := by
  have hYdvd : 1024 ∣ Nat.card Y := hX.trans (Subgroup.card_dvd_of_le hXY)
  obtain ⟨T, hT, hTY⟩ :=
    exists_sylow_le (A := G₀) (by rw [CFSG.Sporadic.Mathieu.card_M24]) hYdvd
  rcases m24_overgroups (X := G₀) ⟨MulEquiv.refl _⟩ hT hTY with h | ⟨m, hm, h1, h2, -⟩
  · exact absurd h hY
  · exact ⟨m, hm, h1, h2⟩

private theorem order_eq_of_dvd_322560 {m : Mem} (hm : m ∈ m24Mems)
    (h : 322560 ∣ m.order) : m.order = 322560 := by
  simp only [m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem order_eq_of_dvd_138240 {m : Mem} (hm : m ∈ m24Mems)
    (h : 138240 ∣ m.order) : m.order = 138240 := by
  simp only [m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem order_eq_of_dvd_21504_of_dvd_o2 {m : Mem} (hm : m ∈ m24Mems)
    (h1 : 21504 ∣ m.order) (h2 : 128 ∣ m.o2) : m.order = 21504 := by
  simp only [m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h1
  · norm_num at h2
  · norm_num at h2
  · norm_num at h1
  · rfl
  · norm_num at h1
  · rfl
  · norm_num at h1
  · norm_num at h1
  · norm_num at h1
  · norm_num at h1
  · norm_num at h1
  · norm_num at h1

private theorem o2_eq_of_order_21504 {m : Mem} (hm : m ∈ m24Mems)
    (h : m.order = 21504) : m.o2 = 128 := by
  simp only [m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rfl
  · norm_num at h
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem ne_bot_of_card {R : Subgroup G₀} {n : ℕ} (h : Nat.card R = n) (hn : 1 < n) :
    R ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at h
  omega

private theorem ne_top_of_card {R : Subgroup G₀} {n : ℕ}
    (h : Nat.card R = n) (hn : n < 244823040) : R ≠ ⊤ := by
  intro htop
  rw [htop, Subgroup.card_top, CFSG.Sporadic.Mathieu.card_M24] at h
  omega

theorem eNorm_o :
    eNorm basis_o = Mo := by
  haveI : IsSimpleGroup G₀ := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hdvd : 322560 ∣ Nat.card (eNorm basis_o) := by
    rw [← card_Mo]
    exact Subgroup.card_dvd_of_le Mo_le
  have hne : eNorm basis_o ≠ ⊤ :=
    normalizer_ne_top (ne_bot_of_card (card_eSub basis_o) (by norm_num))
      (ne_top_of_card (card_eSub basis_o) (by norm_num))
  obtain ⟨m, hm, h1, h2⟩ := row_of_le Mo_le (by rw [card_Mo]; norm_num) hne
  rw [h1] at hdvd
  have hord : m.order = 322560 := order_eq_of_dvd_322560 hm hdvd
  rw [hord] at h1
  exact (Subgroup.eq_of_le_of_card_ge Mo_le (by rw [h1, card_Mo])).symm

theorem o_le_Mo :
    eSub basis_o ≤ Mo := by
  rw [← eNorm_o]
  exact Subgroup.le_normalizer

theorem eNorm_s :
    eNorm basis_s = Ns := by
  haveI : IsSimpleGroup G₀ := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hdvd : 138240 ∣ Nat.card (eNorm basis_s) := by
    rw [← card_Ns]
    exact Subgroup.card_dvd_of_le Ns_le
  have hne : eNorm basis_s ≠ ⊤ :=
    normalizer_ne_top (ne_bot_of_card (card_eSub basis_s) (by norm_num))
      (ne_top_of_card (card_eSub basis_s) (by norm_num))
  obtain ⟨m, hm, h1, h2⟩ := row_of_le Ns_le (by rw [card_Ns]; norm_num) hne
  rw [h1] at hdvd
  have hord : m.order = 138240 := order_eq_of_dvd_138240 hm hdvd
  rw [hord] at h1
  exact (Subgroup.eq_of_le_of_card_ge Ns_le (by rw [h1, card_Ns])).symm

theorem Ls_le_Ns :
    Ls ≤ Ns :=
  Ls_le.trans eNorm_s.le

theorem relIndex_Ls_Ns :
    Ls.relIndex Ns = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Ls) (K := Ns)
  rw [inf_eq_left.mpr Ls_le_Ns, card_Ls, card_Ns] at h
  have h' : Ls.relIndex Ns * 69120 = 2 * 69120 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

private theorem isPGroup_Qg : IsPGroup 2 Qg :=
  IsPGroup.of_card (n := 7) (by rw [card_Qg]; norm_num)

private theorem Qg_le_eNorm_u5 : Qg ≤ eNorm basis_u5 :=
  Qg_le.trans (Subgroup.centralizer_le_normalizer (eSub basis_u5 : Set G₀))

private theorem eNorm_u5_le_normalizer_Qg :
    eNorm basis_u5 ≤ Subgroup.normalizer (Qg : Set G₀) := by
  rw [← cent_u5]
  exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _

theorem eNorm_u5 :
    eNorm basis_u5 = Nq := by
  haveI : IsSimpleGroup G₀ := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hdvd : 21504 ∣ Nat.card (eNorm basis_u5) := by
    rw [← card_Nq]
    exact Subgroup.card_dvd_of_le Nq_le
  have hQgO2 : Qg ≤ pCoreOf 2 (eNorm basis_u5) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Qg_le_eNorm_u5
      eNorm_u5_le_normalizer_Qg isPGroup_Qg
  have ho2dvd : 128 ∣ Nat.card (pCoreOf 2 (eNorm basis_u5)) := by
    rw [← card_Qg]
    exact Subgroup.card_dvd_of_le hQgO2
  have hne : eNorm basis_u5 ≠ ⊤ :=
    normalizer_ne_top (ne_bot_of_card (card_eSub basis_u5) (by norm_num))
      (ne_top_of_card (card_eSub basis_u5) (by norm_num))
  obtain ⟨m, hm, h1, h2⟩ := row_of_le Nq_le (by rw [card_Nq]; norm_num) hne
  rw [h1] at hdvd
  rw [h2] at ho2dvd
  have hord : m.order = 21504 := order_eq_of_dvd_21504_of_dvd_o2 hm hdvd ho2dvd
  rw [hord] at h1
  exact (Subgroup.eq_of_le_of_card_ge Nq_le (by rw [h1, card_Nq])).symm

theorem Lq_le_Nq :
    Lq ≤ Nq :=
  Lq_le.trans eNorm_u5.le

theorem relIndex_Lq_Nq :
    Lq.relIndex Nq = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Lq) (K := Nq)
  rw [inf_eq_left.mpr Lq_le_Nq, card_Lq, card_Nq] at h
  have h' : Lq.relIndex Nq * 10752 = 2 * 10752 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem eNorm_r2 :
    eNorm basis_r2 = CB0 := by
  exact (Subgroup.eq_of_le_of_card_ge CB0_le (by rw [card_CB0]; exact card_eNorm_r2_le)).symm

theorem card_pCoreOf_CB0 :
    Nat.card (pCoreOf 2 CB0) = 128 := by
  have hne : CB0 ≠ ⊤ := ne_top_of_card card_CB0 (by norm_num)
  obtain ⟨m, hm, h1, h2⟩ :=
    row_of_le (X := CB0) le_rfl (by rw [card_CB0]; norm_num) hne
  rw [card_CB0] at h1
  have ho2 : m.o2 = 128 := o2_eq_of_order_21504 hm h1.symm
  rw [ho2] at h2
  exact h2

end CFSG.SectionRank.QTK.Insp443.M24

end
