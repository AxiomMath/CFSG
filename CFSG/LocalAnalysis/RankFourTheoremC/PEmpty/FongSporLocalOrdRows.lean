module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalOrd
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem hcard_M11 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) → Nat.card L = 7920 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M11

theorem row_M11_11 :
    KFactSporLocalRow .M11 11 :=
  row_of_ord .M11 11 7920 hcard_M11
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_M12 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M12).Group) → Nat.card L = 95040 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M12

theorem row_M12_11 :
    KFactSporLocalRow .M12 11 :=
  row_of_ord .M12 11 95040 hcard_M12
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_M22 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) → Nat.card L = 443520 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem row_M22_11 :
    KFactSporLocalRow .M22 11 :=
  row_of_ord .M22 11 443520 hcard_M22
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_M23 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M23).Group) → Nat.card L = 10200960 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Schreier.m23_card

theorem row_M23_11 :
    KFactSporLocalRow .M23 11 :=
  row_of_ord .M23 11 10200960 hcard_M23
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_M23_23 :
    KFactSporLocalRow .M23 23 :=
  row_of_ord .M23 23 10200960 hcard_M23
    (by rw [orderOf_two_zmod_eq 23 11 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_M24 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M24).Group) → Nat.card L = 244823040 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

theorem row_M24_23 :
    KFactSporLocalRow .M24 23 :=
  row_of_ord .M24 23 244823040 hcard_M24
    (by rw [orderOf_two_zmod_eq 23 11 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_J3 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → Nat.card L = 50232960 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.J3.card_J3

theorem row_J3_17 :
    KFactSporLocalRow .J3 17 :=
  row_of_ord .J3 17 50232960 hcard_J3
    (by rw [orderOf_two_zmod_eq 17 8 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_J3_19 :
    KFactSporLocalRow .J3 19 :=
  row_of_ord .J3 19 50232960 hcard_J3
    (by rw [orderOf_two_zmod_eq 19 18 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_J4 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) → Nat.card L = 86775571046077562880 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.J4.card_J4

theorem row_J4_29 :
    KFactSporLocalRow .J4 29 :=
  row_of_ord .J4 29 86775571046077562880 hcard_J4
    (by rw [orderOf_two_zmod_eq 29 28 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_J4_37 :
    KFactSporLocalRow .J4 37 :=
  row_of_ord .J4 37 86775571046077562880 hcard_J4
    (by rw [orderOf_two_zmod_eq 37 36 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_HS :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) → Nat.card L = 44352000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.HS.card_HS

theorem row_HS_11 :
    KFactSporLocalRow .HS 11 :=
  row_of_ord .HS 11 44352000 hcard_HS
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_McL :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) → Nat.card L = 898128000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.McL.card_McL

theorem row_McL_11 :
    KFactSporLocalRow .McL 11 :=
  row_of_ord .McL 11 898128000 hcard_McL
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_Ru :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group) → Nat.card L = 145926144000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Ru.card_Ru

theorem row_Ru_29 :
    KFactSporLocalRow .Ru 29 :=
  row_of_ord .Ru 29 145926144000 hcard_Ru
    (by rw [orderOf_two_zmod_eq 29 28 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_ON :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) → Nat.card L = 460815505920 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.ON.card_ON

theorem row_ON_11 :
    KFactSporLocalRow .ONan 11 :=
  row_of_ord .ONan 11 460815505920 hcard_ON
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_ON_19 :
    KFactSporLocalRow .ONan 19 :=
  row_of_ord .ONan 19 460815505920 hcard_ON
    (by rw [orderOf_two_zmod_eq 19 18 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_Co3 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group) → Nat.card L = 495766656000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Co3.card_Co3

theorem row_Co3_23 :
    KFactSporLocalRow .Co3 23 :=
  row_of_ord .Co3 23 495766656000 hcard_Co3
    (by rw [orderOf_two_zmod_eq 23 11 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_HN :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) → Nat.card L = 273030912000000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.HN.card_HN

theorem row_HN_19 :
    KFactSporLocalRow .HN 19 :=
  row_of_ord .HN 19 273030912000000 hcard_HN
    (by rw [orderOf_two_zmod_eq 19 18 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_Ly :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Ly).Group) → Nat.card L = 51765179004000000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Ly.card_Ly

theorem row_Ly_11 :
    KFactSporLocalRow .Ly 11 :=
  row_of_ord .Ly 11 51765179004000000 hcard_Ly
    (by rw [orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_Ly_37 :
    KFactSporLocalRow .Ly 37 :=
  row_of_ord .Ly 37 51765179004000000 hcard_Ly
    (by rw [orderOf_two_zmod_eq 37 36 (by norm_num) (by decide) (by decide)]; norm_num)

theorem row_Ly_67 :
    KFactSporLocalRow .Ly 67 :=
  row_of_ord .Ly 67 51765179004000000 hcard_Ly
    (by rw [orderOf_two_zmod_eq 67 66 (by norm_num) (by decide) (by decide)]; norm_num)

theorem hcard_Th :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) → Nat.card L = 90745943887872000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.RankThree.OddKernel.card_Th_eq

theorem row_Th_19 :
    KFactSporLocalRow .Th 19 :=
  row_of_ord .Th 19 90745943887872000 hcard_Th
    (by rw [orderOf_two_zmod_eq 19 18 (by norm_num) (by decide) (by decide)]; norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
