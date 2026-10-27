module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNBase
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

theorem sec9d_eq_inf_conj (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (hE : Asc82E16Inner)
    (hR : Asc82RankOm6M) (hctx : Sec9Ctx G t L S z g B t₀) :
    B = Asub9 t t₀ B ⊓ CFSG.conjugate L g := by
  have hBle : B ≤ CFSG.conjugate L g :=
    sec9d_B_le_conj h36 h37 h66 h82 hT6 hB8 hE hctx.toSec8Base
  have hBA : B ≤ Asub9 t t₀ B := by
    rw [Asub9]
    exact le_sup_right
  have hLgM : IsOm6M (CFSG.conjugate L g) := sec9d_isOm6M_conj hctx.toSec8Base
  have hUel : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B ⊓ CFSG.conjugate L g) :=
    (sec9n_A_elem hctx).mono inf_le_left
  have hcard : Nat.card ↥(Asub9 t t₀ B ⊓ CFSG.conjugate L g) ≤ 16 :=
    hR G (CFSG.conjugate L g) _ hLgM inf_le_right hUel
  have hB16 : Nat.card ↥B = 16 := by
    rw [hctx.B_e16.2]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge (le_inf hBA hBle) (by rw [hB16]; exact hcard)

theorem sec9Choice_of_sec9Ctx (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (hE : Asc82E16Inner)
    (hR : Asc82RankOm6M) (hctx : Sec9Ctx G t L S z g B t₀) : Sec9Choice G t L S z g B t₀ :=
  ⟨hctx, sec9d_eq_inf_conj h36 h37 h66 h82 hT6 hB8 hE hR hctx⟩

theorem asc82Lemma91_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (hE : Asc82E16Inner)
    (hR : Asc82RankOm6M) : Asc82Lemma91 := by
  intro G _ _ t L S z g B t₀ hctx
  exact ⟨B, t₀, sec9Choice_of_sec9Ctx h36 h37 h66 h82 hT6 hB8 hE hR hctx⟩

end CFSG.OddStandard.SmallF3.Omega
