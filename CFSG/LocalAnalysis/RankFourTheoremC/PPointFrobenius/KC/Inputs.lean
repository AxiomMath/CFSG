module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

@[expose] def KCFiveParts : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (d.1 = .tits ∨ d.1 = .suzuki 2) →
    ¬ 5 ^ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group

@[expose] def kcSporOrd : TauCeti.SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => 145926144000
  | .Suz => 448345497600
  | .ONan => 460815505920
  | .Co1 => 4157776806543360000
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24Prime => 1255205709190661721292800
  | .HN => 273030912000000
  | .Ly => 51765179004000000
  | .Th => 90745943887872000
  | .B => 4154781481226426191177580544000000
  | .M => 808017424794512875886459904961710757005754368000000000

@[expose] def KCSporadicOrders : Prop :=
  ∀ s : TauCeti.SporadicName, Nat.card (TauCeti.CFSGIndex.sporadic s).Group = kcSporOrd s

@[expose] def KCThFive : Prop :=
  ∃ x y : (TauCeti.CFSGIndex.sporadic .Th).Group, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y ≠ y * x ∧
    IsPGroup 5 (Subgroup.closure ({x, y} : Set (TauCeti.CFSGIndex.sporadic .Th).Group))

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
