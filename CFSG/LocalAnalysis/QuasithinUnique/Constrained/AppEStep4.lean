module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep3
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Transfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEBaum

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

namespace Dbl

variable (D : Dbl T M H S L n t)
include D

theorem U_ne_bot : blockU L ≠ ⊥ := C56.blockU_ne_bot D.hL

theorem Z_le_comm : blockU L ⊓ centralizer (L : Set G) ≤ ⁅blockU L, baum S⁆ := by
  have hLX : L ≤ L ⊔ baum S := le_sup_left
  have hXN : L ⊔ baum S ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer D.baum_le_normalizer
  have hTsyl : IsSylowTwoOf (baum S ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal D.isSylowTwoOf_baum hLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN).isSubnormal
  exact (C1.blockZ_le_commutator_sylow D.hL hTsyl).trans
    (Subgroup.commutator_mono le_rfl inf_le_left)

theorem H_le_normalizer {X : Subgroup G} (hL : L ≤ normalizer (X : Set G))
    (hL₂ : conjR L t ≤ normalizer (X : Set G)) (hS : S ≤ normalizer (X : Set G)) :
    H ≤ normalizer (X : Set G) := by
  rw [D.hcs.eq_join, D.hjoin]
  exact sup_le (sup_le hL hL₂) hS

end Dbl

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem inv : Setup T M H S L n t M₀ x⁻¹ q W where
  D := P.D
  hSM := P.hSM
  hMT := P.hMT
  h2 := P.h2
  hx := M₀.inv_mem P.hx
  hxS := fun h => P.hxS (by simpa using S.inv_mem h)
  loc := P.loc
  good := not_conj_inv_le P.loc.rk P.hxB P.good

theorem Z_le_W : blockU L ⊓ centralizer (L : Set G) ≤ W := by
  have h1 := P.D.Z_le_comm
  rwa [P.loc.rk.comm_UB] at h1

theorem Z₂_le_W₂ : conjSubgroup (blockU L) t ⊓
    centralizer ((conjSubgroup L t : Subgroup G) : Set G) ≤ conjSubgroup W t := by
  have := conjSubgroup_mono P.Z_le_W t
  rwa [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer] at this

theorem eq_bot_of_normalized {X : Subgroup G} (hXS : X ≤ S) (hL : L ≤ normalizer (X : Set G))
    (hL₂ : conjR L t ≤ normalizer (X : Set G)) (hSX : S ≤ normalizer (X : Set G))
    (hxX : x ∈ normalizer (X : Set G)) : X = ⊥ :=
  C5.eq_bot_of_noCommonNormal' (C56.noCommonNormal P.D.hcs P.hSM P.hMT P.hne) hXS
    (P.D.H_le_normalizer hL hL₂ hSX) hSX hxX (le_sup_zpowers_of_relIndex_two P.h2 P.hx P.hxS)

theorem U₁_inf_U₂ : blockU L ⊓ conjSubgroup (blockU L) t = ⊥ := by
  have hle : blockU L ⊓ conjSubgroup (blockU L) t ≤
      conjSubgroup (blockU L ⊓ conjSubgroup (blockU L) t) x := by
    intro y hy
    have hy1 : y ∈ blockU L := hy.1
    have hy2 : y ∈ conjSubgroup (blockU L) t := hy.2
    have hyC : y ∈ centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => P.D.comm_elem l hl y (P.U₂_le_L₂ hy2)
    have hyC₂ : y ∈ centralizer ((conjSubgroup L t : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun m hm =>
        (P.D.comm_elem y (P.U₁_le_L hy1) m hm).symm
    have h1 : y ∈ conjSubgroup (blockU L) x := P.W_le_X (P.Z_le_W ⟨hy1, hyC⟩)
    have h2 : y ∈ conjSubgroup (conjSubgroup (blockU L) t) x :=
      P.W₂_le_Y (P.Z₂_le_W₂ ⟨hy2, hyC₂⟩)
    rw [C5.conjSubgroup_inf]
    exact ⟨h1, h2⟩
  have heq : blockU L ⊓ conjSubgroup (blockU L) t =
      conjSubgroup (blockU L ⊓ conjSubgroup (blockU L) t) x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  have hxX : x ∈ normalizer ((blockU L ⊓ conjSubgroup (blockU L) t : Subgroup G) : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp heq.symm
  have hLU₂ : L ≤ normalizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun l hl a ha => P.D.comm_elem l hl a (P.U₂_le_L₂ ha)
  have hL₂U₁ : conjR L t ≤ normalizer (blockU L : Set G) :=
    C5.le_normalizer_of_commute fun a ha u hu => (P.D.comm_elem u (P.U₁_le_L hu) a ha).symm
  have hL₂U₂ : conjR L t ≤ normalizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
    have h := C1.le_normalizer_blockU (conjR L t)
    rw [blockU_conjR] at h
    exact h
  refine P.eq_bot_of_normalized (inf_le_left.trans (P.U₁_le_B.trans inf_le_left))
    (fun l hl => C5.mem_normalizer_inf (C1.le_normalizer_blockU L hl) (hLU₂ hl))
    (fun l hl => C5.mem_normalizer_inf (hL₂U₁ hl) (hL₂U₂ hl)) ?_ hxX
  intro g hg
  rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf]
  rcases P.D.U_cases₂ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, inf_comm]

theorem U₁_ne_U₂ : blockU L ≠ conjSubgroup (blockU L) t := by
  intro h
  have h1 := P.U₁_inf_U₂
  rw [← h, inf_idem] at h1
  exact P.D.U_ne_bot h1

theorem W_inf_W₂ : W ⊓ conjSubgroup W t = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have : y ∈ blockU L ⊓ conjSubgroup (blockU L) t :=
    ⟨P.loc.rk.W_le_U hy.1, conjSubgroup_mono P.loc.rk.W_le_U t hy.2⟩
  rw [P.U₁_inf_U₂] at this
  exact this

theorem R1_fixes_X₁ {s : G} (hs : s ∈ R1 S L) :
    conjSubgroup (conjSubgroup (blockU L) x) s = conjSubgroup (blockU L) x := by
  have hsS : s ∈ S := R1_le_S hs
  have hsN : s ∈ normalizer (L : Set G) := R1_le_normalizer_L hs
  have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 P.hxN s).1 hsS
  have e1 : conjSubgroup (conjSubgroup (blockU L) x) s =
      conjSubgroup (conjSubgroup (blockU L) (x * s * x⁻¹)) x := by
    simp only [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
  rcases P.D.U_cases hs' with h | h
  · rw [e1, h]
  · exfalso
    have hle : conjSubgroup (conjSubgroup (blockU L) x) s ≤
        baum S ⊓ centralizer (blockU L : Set G) := by
      rw [e1, h]; exact P.U₂x_le_Q₁
    have hsQ : s ∈ normalizer ((baum S ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) :=
      C5.mem_normalizer_inf (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hsS))
        (C5.mem_normalizer_centralizer (C1.mem_normalizer_blockU hsN))
    have h3 := conjSubgroup_mono hle s⁻¹
    rw [C5.conjSubgroup_conjSubgroup_inv, C5.conjSubgroup_eq_self (inv_mem hsQ)] at h3
    exact P.good h3

theorem x_normalizes_R1 : x ∈ normalizer ((R1 S L : Subgroup G) : Set G) := by
  have hle : R1 S L ≤ conjSubgroup (R1 S L) x := by
    intro r hr
    rw [mem_conjSubgroup_iff]
    have hrS : x * r * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 P.hxN r).1 (R1_le_S hr)
    refine mem_R1_iff.2 ⟨hrS, ?_⟩
    rcases P.D.conjR_cases hrS with h | h
    · exact h
    · exfalso
      have e : conjSubgroup (blockU L) (x * r * x⁻¹) = blockU L := by
        have e1 : conjSubgroup (blockU L) (x * r * x⁻¹) =
            conjSubgroup (conjSubgroup (conjSubgroup (blockU L) x) r) x⁻¹ := by
          simp only [conjSubgroup_conjSubgroup, mul_assoc]
        rw [e1, P.R1_fixes_X₁ hr, C5.conjSubgroup_conjSubgroup_inv]
      have h1 := blockU_conjR L (x * r * x⁻¹)
      rw [h, blockU_conjR L t] at h1
      have h3 : conjSubgroup (blockU L) t = blockU L := h1.trans e
      exact P.U₁_ne_U₂ h3.symm
  have heq : R1 S L = conjSubgroup (R1 S L) x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  exact conjSubgroup_eq_iff_mem_normalizer.mp heq.symm

end Setup

end CFSG.QuasithinUnique.AppE
