module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.RankThree.Native

theorem nonempty_equiv_mclP
    {K : Type} [Group K]
    (hs : IsSimpleGroup K) (hK : IsSporadicGroup .McL K) : Nonempty (K ≃* mclP) := by
  obtain ⟨e⟩ := hK
  have := hs
  have : IsSimpleGroup TauCeti.SporadicName.McL.Group := e.symm.isSimpleGroup
  obtain ⟨β⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
  exact ⟨(e.trans β).trans mclPermEquiv⟩

theorem sylowCube_of_isMcL
    {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSporadicGroup .McL K) : SylowCube 5 K := by
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  have hfin : Finite mclP := Finite.of_equiv K e.toEquiv
  have hcard : Nat.card K = 5 ^ 3 * 7185024 := by
    rw [Nat.card_congr e.toEquiv, card_mclP]
    norm_num
  obtain ⟨-, ⟨S, hS⟩, -, hexp⟩ := (R3E_McL_full_five_centralizer_structures).1
  refine sylowCube_of_equiv (by norm_num) e hcard (by norm_num) S fun s hs' => ?_
  rw [hS] at hs'
  have h5 : (⟨(s : Equiv.Perm (Fin 275)), hs'⟩ : mcl275FiveQ) ^ 5 = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one _
  exact Subtype.ext (by simpa using congrArg Subtype.val h5)

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
