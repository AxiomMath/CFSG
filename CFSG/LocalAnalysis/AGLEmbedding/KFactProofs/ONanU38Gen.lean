module

public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Arr
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerNormalizer

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Monster.B.Fischer
open scoped Matrix

structure GenData where
  gens : Array (Array GF64)
  v0 : Array ℕ
  words : List (List ℕ)
  fuel1 : ℕ
  fuel2 : ℕ

@[expose] def letterArr3 (G : Array (Array GF64)) (l : ℕ) : Array GF64 :=
  if l % 2 = 0 then G.getD (l / 2) #[] else conjTrArr3 (G.getD (l / 2) #[])

@[expose] def wordArr3 (G : Array (Array GF64)) (w : List ℕ) : Array GF64 :=
  w.foldr (fun l A => mulArr3 (letterArr3 G l) A) oneArr3

@[expose] def validV (a : Array ℕ) : Bool :=
  a.size == 3 && decide (a.getD 0 0 < 64) && decide (a.getD 1 0 < 64) &&
    decide (a.getD 2 0 < 64)

end CFSG.AGLEmbedding.ChevOuter.U38
