module

public import CFSG.LargeExtraspecial.ConjCountTwoPow
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.GF2Type.Smith1980Orth.IndexCount

public section

namespace CFSG.GF2Type.Smith1979.TriConf

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 Module

variable {G : Type*} [Group G] [Finite G]

theorem index_mod_eight_eq_seven {S : Setting G} {g : G} (H : Hyp4 S g) (hno : S11.NoA2All S)
    (hw : S.width = 4)
    (horb : Nat.card (MulAction.orbit S.Mbar (S.cl (g * S.z * g⁻¹))) = 27)
    (hdim : ∀ y : G, IsConj S.z y → (hyM : y ∈ S.M) → y ∉ S.QG →
      3 ≤ finrank (ZMod 2)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace
          ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    S.M.index % 8 = 7 := by
  have h := card_conj_mod_two_pow S (k := 3) (by omega) hdim
  rw [card_conj_inter_QG_eq H (S6.fusionCtl_of_lemma_3_13 H hno), horb,
    CFSG.GF2Type.Smith1980Orth.card_conj_eq_index S] at h
  simpa using h

end CFSG.GF2Type.Smith1979.TriConf
