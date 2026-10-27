module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint

theorem nonempty_equiv_fi22
    {K : Type} [Group K] (hs : IsSimpleGroup K) (hK : IsFi22 K) :
    Nonempty (K ≃* NativeSporadic.Fi22) := by
  obtain ⟨e⟩ := hK
  have := hs
  have : IsSimpleGroup TauCeti.SporadicName.Fi22.Group := e.symm.isSimpleGroup
  obtain ⟨β⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Fi22
  exact ⟨e.trans β⟩

theorem card_of_isFi22 {K : Type}
    [Group K] (hs : IsSimpleGroup K) (hK : IsFi22 K) : Nat.card K = 64561751654400 := by
  obtain ⟨e⟩ := nonempty_equiv_fi22 hs hK
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Fi22.card_Fi22

theorem sylowSq_of_isFi22
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K) (hK : IsFi22 K) : SylowSq 5 K := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro T
  have h := card_of_isFi22 hs hK
  exact card_sylow_eq_pow_of_card_eq (k := 2) (m := 2582470066176) (by rw [h]; norm_num)
    (by norm_num) T

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
