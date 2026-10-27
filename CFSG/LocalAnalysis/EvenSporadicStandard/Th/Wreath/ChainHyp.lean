module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.TypeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.EndgameHyp

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

structure ChainHyp (L A D : Subgroup G) (t : G) (F : Subgroup G) : Prop where
  D_le : D ≤ F
  le_centralizer : F ≤ centralizer (D : Set G)
  comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  typeA : IsTypeA L A ⊥ F
  conj_t_mem : ∀ x ∈ F, t * x * t⁻¹ ∈ F
  mem_of_sq_eq_one : ∀ x ∈ F, x ^ 2 = 1 → x ∈ D

theorem ChainHyp.conj_mem {F : Subgroup G} (hF : ChainHyp L A D t F) :
    ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ F, n * x * n⁻¹ ∈ F :=
  hF.typeA.conj_mem

theorem ChainHyp.pgroup (W : ThLocalIn L S A B z) {F : Subgroup G} (hF : ChainHyp L A D t F) :
    IsPGroup 2 F := by
  obtain ⟨r, hr⟩ := hF.typeA.exists_card_eq W
  rw [Subgroup.card_bot, mul_one] at hr
  exact IsPGroup.of_card (n := 4 * r) (by rw [hr, pow_mul]; norm_num)

theorem ChainHyp.qHyp (W : ThLocalIn L S A B z) {F : Subgroup G} (hF : ChainHyp L A D t F)
    (hmax : ∀ Y : Subgroup G, Y ≤ centralizer (D : Set G) → IsPGroup 2 Y → F ≤ Y → Y ≤ F) :
    QHyp L A D t F :=
  ⟨hF.D_le, hF.le_centralizer, hF.pgroup W, hF.comm, hF.mem_of_sq_eq_one, hF.conj_mem,
    hF.conj_t_mem, hmax⟩

theorem ThCyc.chainHyp_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    ChainHyp L A D t D where
  D_le := le_rfl
  le_centralizer := fun x hx => mem_centralizer_iff.2 fun y hy => hD.comm y hy x hx
  comm := hD.comm
  typeA := H.isTypeA_bot_D W W2 hD h4
  conj_t_mem := fun x hx => hD.norm t (H.t_mem_normalizer W W2 hD) x hx
  mem_of_sq_eq_one := fun x hx _ => hx

end CFSG.EvenSporadicStandard.ThStd
