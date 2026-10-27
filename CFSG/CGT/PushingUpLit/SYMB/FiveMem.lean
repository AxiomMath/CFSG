module

public import CFSG.CGT.PushingUpLit.SYMB.FiveCfix
public import CFSG.CGT.PushingUpLit.SYMB.ElemAb
public import CFSG.CGT.PushingUpLit.SYMB.ImgCard
public import CFSG.CGT.PushingUpLit.SYMB.BlockFacts
public import CFSG.CGT.PushingUpLit.SYMB.ProdCard

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ}

omit [Finite Γ] in
theorem V_le_kerG (S : SymSetting G T V 5 φ ψ T') : V ≤ kerG G φ := by
  intro v hv
  have hvG : v ∈ G := (sym_V_le_pCore S |>.trans
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G)) hv
  refine mem_kerG.2 ⟨hvG, ?_⟩
  have h : (⟨v, hvG⟩ : ↥G) ∈ φ.ker := by
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨hvG, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (S.data.elemAbelian.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  exact h

omit [Finite Γ] in
theorem V_le_T (S : SymSetting G T V 5 φ ψ T') : V ≤ T :=
  (sym_V_le_pCore S).trans S.sylow.pCoreOf_le

omit [Finite Γ] in
theorem V₁_elemAbelian (S : SymSetting G T V 5 φ ψ T') (hV : V1Iso S V₁) :
    IsElemAbelian 2 V₁ :=
  isElemAbelian_of_le' S.data.elemAbelian hV.le

omit [Finite Γ] in
theorem V₁_comm_ker (S : SymSetting G T V 5 φ ψ T') (hV : V1Iso S V₁) {v r : Γ} (hv : v ∈ V₁)
    (hr : r ∈ kerG G φ) : v * r = r * v := by
  have hrC : r ∈ Subgroup.centralizer (V : Set Γ) := by
    obtain ⟨hrG, hr1⟩ := mem_kerG.1 hr
    have h2 : (⟨r, hrG⟩ : ↥G) ∈ φ.ker := hr1
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    exact h2.2
  exact Subgroup.mem_centralizer_iff.1 hrC v (hV.le hv)

omit [Finite Γ] in
theorem card_V₁ (hV : V1Iso S V₁) : Nat.card ↥V₁ = 16 := by
  rw [Nat.card_congr hV.toEquiv.toEquiv]
  exact Delta5Swaps.card_core

theorem V₁_inf_eq (S : SymSetting G T V 5 φ ψ T') (hV : V1Iso S V₁) {A : Subgroup Γ}
    (hA : IsMaxElemAbelian T A) : V₁ ⊓ A = Cfix ψ V₁ (imgG G φ A) := by
  have hAG : A ≤ G := hA.1.trans S.sylow.1
  rw [← hV.inf_centralizer_eq_Cfix hAG]
  apply le_antisymm
  · intro v hv
    exact ⟨hv.1, Subgroup.mem_centralizer_iff.2 fun a ha => elemAb_comm hA.2.1 ha hv.2⟩
  · intro v hv
    refine ⟨hv.1, ?_⟩
    have hX : V₁ ⊓ Subgroup.centralizer (A : Set Γ) ≤ A := by
      refine maxElemAb_le_of_commute hA (isElemAbelian_of_le' (V₁_elemAbelian S hV) inf_le_left)
        (inf_le_left.trans (hV.le.trans (V_le_T S))) fun x hx a ha => ?_
      exact (Subgroup.mem_centralizer_iff.1 hx.2 a ha).symm
    exact hX hv

theorem sixteen_le (S : SymSetting G T V 5 φ ψ T') (hV : V1Iso S V₁) {A : Subgroup Γ}
    (hA : IsMaxElemAbelian T A) :
    16 ≤ Nat.card ↥(imgG G φ A) * Nat.card ↥(Cfix ψ V₁ (imgG G φ A)) := by
  have hAG : A ≤ G := hA.1.trans S.sylow.1
  have hV₁R : V₁ ≤ kerG G φ := hV.le.trans (V_le_kerG S)
  set AR : Subgroup Γ := A ⊓ kerG G φ with hAR
  have hARA : AR ≤ A := inf_le_left
  have hARel : IsElemAbelian 2 AR := isElemAbelian_of_le' hA.2.1 hARA
  have hjoin : IsElemAbelian 2 (V₁ ⊔ AR) :=
    isElemAbelian_sup_of_commute (V₁_elemAbelian S hV) hARel fun v hv r hr =>
      V₁_comm_ker S hV hv (Subgroup.mem_inf.1 hr).2
  have hle : Nat.card ↥(V₁ ⊔ AR) ≤ Nat.card ↥A :=
    hA.2.2 _ (sup_le (hV.le.trans (V_le_T S)) (hARA.trans hA.1)) hjoin
  have hprod := card_sup_mul_card_inf_of_commute (C := V₁) (D := AR) fun v hv r hr =>
    V₁_comm_ker S hV hv (Subgroup.mem_inf.1 hr).2
  have hinf : V₁ ⊓ AR = Cfix ψ V₁ (imgG G φ A) := by
    rw [← V₁_inf_eq S hV hA, hAR, ← inf_assoc, inf_eq_left.2 (inf_le_left.trans hV₁R)]
  rw [hinf, card_V₁ hV] at hprod
  have hM1 := card_eq_img_mul_ker φ hAG
  have hpos : 0 < Nat.card ↥AR := Nat.card_pos
  rw [← hAR] at hM1
  have h1 : 16 * Nat.card ↥AR ≤ (Nat.card ↥(imgG G φ A) * Nat.card ↥(Cfix ψ V₁ (imgG G φ A))) *
      Nat.card ↥AR := by
    calc 16 * Nat.card ↥AR = Nat.card ↥(V₁ ⊔ AR) * Nat.card ↥(Cfix ψ V₁ (imgG G φ A)) := hprod.symm
      _ ≤ Nat.card ↥A * Nat.card ↥(Cfix ψ V₁ (imgG G φ A)) :=
        Nat.mul_le_mul_right _ hle
      _ = (Nat.card ↥(imgG G φ A) * Nat.card ↥(Cfix ψ V₁ (imgG G φ A))) * Nat.card ↥AR := by
        rw [hM1]; ring
  exact Nat.le_of_mul_le_mul_right h1 hpos

end CFSG.CGT.PushingUpLit.SYMB
