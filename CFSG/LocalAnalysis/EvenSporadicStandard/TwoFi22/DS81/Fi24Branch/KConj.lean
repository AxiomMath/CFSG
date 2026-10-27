module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.StdBasic
public import CFSG.Monster.B.Fischer.Fi22Model

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

variable {G : Type*} [Group G] {L M : Subgroup G}

@[expose] noncomputable def conjQuotHom (L M : Subgroup G) (hM : M ≤ normalizer (L : Set G)) :
    M →* MulAut (L ⧸ center L) :=
  (CFSG.EvenSporadicStandard.normalizerAction L).comp (Subgroup.inclusion hM)

theorem conjQuotHom_apply (hM : M ≤ normalizer (L : Set G)) (g : M) (x l : L)
    (h : (l : G) = (g : G) * x * (g : G)⁻¹) :
    conjQuotHom L M hM g (x : L ⧸ center L) = (l : L ⧸ center L) :=
  CFSG.EvenSporadicStandard.normalizerAction_apply (Subgroup.inclusion hM g) x l h

theorem ker_conjQuotHom (hL : commutator L = ⊤) (hM : M ≤ normalizer (L : Set G)) :
    (conjQuotHom L M hM).ker = (centralizer (L : Set G)).subgroupOf M := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact CFSG.EvenSporadicStandard.normalizerAction_eq_one_iff hL (Subgroup.inclusion hM g)

theorem conjQuotHom_surjective_of_card [Finite M] (hL : commutator L = ⊤)
    (hM : M ≤ normalizer (L : Set G))
    (hcard : Nat.card ((centralizer (L : Set G)).subgroupOf M) *
      Nat.card (MulAut (L ⧸ center L)) = Nat.card M) :
    Function.Surjective (conjQuotHom L M hM) := by
  have h1 := Subgroup.card_ker_mul_card_range (conjQuotHom L M hM)
  rw [ker_conjQuotHom hL hM, ← hcard] at h1
  have hpos : 0 < Nat.card ((centralizer (L : Set G)).subgroupOf M) := Nat.card_pos
  have h2 : Nat.card (conjQuotHom L M hM).range = Nat.card (MulAut (L ⧸ center L)) :=
    Nat.eq_of_mul_eq_mul_left hpos h1
  haveI : Finite (conjQuotHom L M hM).range :=
    Finite.of_surjective _ (conjQuotHom L M hM).rangeRestrict_surjective
  have hfin : Finite (MulAut (L ⧸ center L)) := by
    have : 0 < Nat.card (MulAut (L ⧸ center L)) := by
      rw [← h2]
      exact Nat.card_pos
    exact Nat.finite_of_card_ne_zero this.ne'
  have htop : (conjQuotHom L M hM).range = ⊤ := Subgroup.eq_top_of_card_eq _ h2
  exact MonoidHom.range_eq_top.1 htop

end General

section StdBasics

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.H_le_normalizer (h : Std G L E t) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) := h.facts.centralizer_le

theorem Std.commutator_L (h : Std G L E t) : commutator L = ⊤ := h.std.standard.1.1

end StdBasics

section Fi22

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

@[expose] noncomputable def piR (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* fi22P) : centralizer ({t} : Set G) →* fi22R :=
  ((MulAut.congr e).trans fi22RAut.symm).toMonoidHom.comp
    (conjQuotHom L (centralizer ({t} : Set G)) hH)

theorem piR_eq_one_iff (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* fi22P) (g : centralizer ({t} : Set G)) :
    piR hH e g = 1 ↔ conjQuotHom L (centralizer ({t} : Set G)) hH g = 1 := by
  rw [piR, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem fi22RAut_piR (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* fi22P) (g : centralizer ({t} : Set G)) :
    fi22RAut (piR hH e g) =
      MulAut.congr e (conjQuotHom L (centralizer ({t} : Set G)) hH g) := by
  rw [piR, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

theorem piR_apply_of_mem_L (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* fi22P) (l : L) (hl : (l : G) ∈ centralizer ({t} : Set G)) :
    ((piR hH e ⟨l, hl⟩ : fi22R) : Equiv.Perm (Fin 3510)) =
      ((e (l : L ⧸ center L) : fi22P) : Equiv.Perm (Fin 3510)) := by
  set r' : fi22R := ⟨(e (l : L ⧸ center L) : fi22P), fi22P_le_R (e (l : L ⧸ center L)).2⟩
    with hr'
  suffices hsuff : piR hH e ⟨l, hl⟩ = r' by rw [hsuff]
  apply fi22RAut.injective
  rw [fi22RAut_piR]
  refine MulEquiv.ext fun p => Subtype.ext ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm p)
  have hp : p = e (x : L ⧸ center L) := by rw [hx, MulEquiv.apply_symm_apply]
  have hconj : conjQuotHom L (centralizer ({t} : Set G)) hH ⟨l, hl⟩ (x : L ⧸ center L) =
      ((l * x * l⁻¹ : L) : L ⧸ center L) :=
    conjQuotHom_apply hH ⟨l, hl⟩ x (l * x * l⁻¹) (by simp)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hp, MulEquiv.symm_apply_apply,
    hconj, fi22RAut_apply, fi22ConjHom_apply]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rfl

theorem Std.card_H_eq (h : Std G L E t) (e : (L ⧸ center L) ≃* fi22P) :
    Nat.card ((centralizer (L : Set G)).subgroupOf (centralizer ({t} : Set G))) *
      Nat.card (MulAut (L ⧸ center L)) = Nat.card (centralizer ({t} : Set G)) := by
  have ht : t ∈ centralizer ({t} : Set G) := by simp [Subgroup.mem_centralizer_iff]
  have hzt : zpowers t ≤ centralizer ({t} : Set G) := (Subgroup.zpowers_le).2 ht
  have h1 : Nat.card ((zpowers t).subgroupOf (centralizer ({t} : Set G))) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzt).toEquiv, Nat.card_zpowers, h.orderOf_t]
  have h2 : Nat.card (MulAut (L ⧸ center L)) = 129123503308800 := by
    rw [Nat.card_congr ((MulAut.congr e).trans fi22RAut.symm).toEquiv, card_fi22R]
  rw [h.cent, h1, h2, h.card_H]
  norm_num

theorem Std.piR_surjective (h : Std G L E t) (e : (L ⧸ center L) ≃* fi22P) :
    Function.Surjective (piR h.H_le_normalizer e) := by
  have hκ : Function.Surjective (conjQuotHom L (centralizer ({t} : Set G)) h.H_le_normalizer) :=
    conjQuotHom_surjective_of_card h.commutator_L h.H_le_normalizer (h.card_H_eq e)
  exact ((MulAut.congr e).trans fi22RAut.symm).surjective.comp hκ

theorem Std.ker_piR (h : Std G L E t) (e : (L ⧸ center L) ≃* fi22P) :
    (piR h.H_le_normalizer e).ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, piR_eq_one_iff, ← MonoidHom.mem_ker,
    ker_conjQuotHom h.commutator_L h.H_le_normalizer, h.cent]

end Fi22

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
