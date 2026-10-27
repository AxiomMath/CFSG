module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516J

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB

theorem leafAt_M11
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M11) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 7920)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M11) =
        Nat.card NativeSporadic.M11 from rfl, Sporadic.Mathieu.card_M11])
    [(2, 4), (3, 2), (5, 1), (11, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_M12
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M12) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 95040)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M12) =
        Nat.card NativeSporadic.M12 from rfl, Sporadic.Mathieu.card_M12])
    [(2, 6), (3, 3), (5, 1), (11, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_M22
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M22) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 443520)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M22) =
        Nat.card NativeSporadic.M22 from rfl, Sporadic.Mathieu.card_M22])
    [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_M23
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M23) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 10200960)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M23) =
        Nat.card NativeSporadic.M23 from rfl, Sporadic.Schreier.m23_card])
    [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_M24
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M24) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 244823040)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M24) =
        Nat.card NativeSporadic.M24 from rfl, Sporadic.Mathieu.card_M24])
    [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_J1
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J1) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 175560)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J1) =
        Nat.card NativeSporadic.J1 from rfl, Sporadic.J1.card_J1])
    [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_J2
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J2) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 604800)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J2) =
        Nat.card NativeSporadic.J2 from rfl, Sporadic.J2.card_J2])
    [(2, 7), (3, 3), (5, 2), (7, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_J3
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J3) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 50232960)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J3) =
        Nat.card NativeSporadic.J3 from rfl, Sporadic.J3.card_J3])
    [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_J4
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J4) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 86775571046077562880)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J4) =
        Nat.card NativeSporadic.J4 from rfl, Sporadic.J4.card_J4])
    [(2, 21), (3, 3), (5, 1), (7, 1), (11, 3), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_HS
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .HS) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 44352000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .HS) =
        Nat.card NativeSporadic.HS from rfl, Sporadic.HS.card_HS])
    [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_McL
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .McL) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 898128000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .McL) =
        Nat.card NativeSporadic.McL from rfl, Sporadic.McL.card_McL])
    [(2, 7), (3, 6), (5, 3), (7, 1), (11, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_He
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .He) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 4030387200)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .He) =
        Nat.card NativeSporadic.He from rfl, Sporadic.He.card_He])
    [(2, 10), (3, 3), (5, 2), (7, 3), (17, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_Ru
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Ru) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 145926144000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Ru) =
        Nat.card NativeSporadic.Ru from rfl, Sporadic.Ru.card_Ru])
    [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_ONan
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .ONan) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 460815505920)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .ONan) =
        Nat.card NativeSporadic.ON from rfl, Sporadic.ONOddCore.card_native_ON])
    [(2, 9), (3, 4), (5, 1), (7, 3), (11, 1), (19, 1), (31, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_Co2
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Co2) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 42305421312000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Co2) =
        Nat.card NativeSporadic.Co2 from rfl, Sporadic.Co2.card_Co2])
    [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_Co3
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Co3) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 495766656000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Co3) =
        Nat.card NativeSporadic.Co3 from rfl, Sporadic.Co3.card_Co3])
    [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_HN
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .HN) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 273030912000000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .HN) =
        Nat.card NativeSporadic.HN from rfl, Sporadic.HNSchreier.card_HN])
    [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]
    (by decide) (by decide) (by decide)

theorem leafAt_Ly
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Ly) :
    CF516LeafAt S :=
  leafAt_of_filter_empty (N := 51765179004000000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Ly) =
        Nat.card NativeSporadic.Ly from rfl, Sporadic.Ly.card_Ly])
    [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)]
    (by decide) (by decide) (by decide)

end CFSG.ComponentClassification.SolMax.Spor516
