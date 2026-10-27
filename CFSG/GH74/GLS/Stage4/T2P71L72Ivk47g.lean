module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
public import CFSG.GH74.GLS.Stage4.T2P71L72Def47g
public import CFSG.GH74.GLS.Stage4.T2P71L72G2

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem ivk_4_7g : IVK_4_7g := by
  intro K _ _ n hn hK P B hBP hBab hcard
  obtain ⟨F, hFfield, hFfin, hF, ⟨e⟩⟩ :=
    exists_mulEquiv_sylow_G2 Nat.prime_three (untwisted_of_lieModel_G2 hK) P
  have hchar : CharP F 3 := charP_of_natCard_eq_pow Nat.prime_three hF
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  set B₀ : Subgroup ↥(P : Subgroup K) := B.subgroupOf (P : Subgroup K) with hB₀
  set B₁ : Subgroup ↥(posUnipotent .G2 F) := B₀.map e.toMonoidHom with hB₁
  refine g2_no_abelian_index_le_three hn hF h3 B₁ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab _ ha _ hb)
  · have h1 : Nat.card ↥B₁ = Nat.card ↥B :=
      (Nat.card_congr (Subgroup.equivMapOfInjective B₀ e.toMonoidHom e.injective).toEquiv).symm.trans
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv)
    have h2 : Nat.card ↥(posUnipotent .G2 F) = Nat.card ↥(P : Subgroup K) :=
      (Nat.card_congr e.toEquiv).symm
    rw [h1, h2]
    exact hcard

end CFSG.GH74.GLS.Stage4.Rest.L72
