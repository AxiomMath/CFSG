module

public import CFSG.CGT.PushingUpLit.BHS7.Basic
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem cenIn_autOn_eq {V A W : Subgroup Γ} (hV : IsElemAbelian 2 V) (hW : W ≤ V) :
    @cenIn ↥V (commGroupOfElemAbelian hV) (autOn A V) (W.subgroupOf V) =
      autOn (A ⊓ Subgroup.centralizer (W : Set Γ)) V := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  ext x
  rw [mem_cenIn]
  constructor
  · rintro ⟨hx, hxW⟩
    obtain ⟨a, haA, rfl⟩ := mem_autOn_iff.mp hx
    refine mem_autOn_iff.mpr ⟨a, ⟨haA, ?_⟩, rfl⟩
    show (a : Γ) ∈ Subgroup.centralizer (W : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := hxW ⟨w, hW hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
    have h2 := congrArg (fun v : ↥V => (v : Γ)) h1
    simp only [conjAct_apply'] at h2
    calc w * (a : Γ) = ((a : Γ) * w * (a : Γ)⁻¹) * a := by rw [h2]
      _ = (a : Γ) * w := by group
  · intro hx
    obtain ⟨a, ⟨haA, haW⟩, rfl⟩ := mem_autOn_iff.mp hx
    refine ⟨mem_autOn_iff.mpr ⟨a, haA, rfl⟩, ?_⟩
    intro w hw
    apply Subtype.ext
    rw [conjAct_apply']
    have h1 := Subgroup.mem_centralizer_iff.mp haW w (Subgroup.mem_subgroupOf.mp hw)
    calc (a : Γ) * (w : Γ) * (a : Γ)⁻¹ = ((w : Γ) * a) * (a : Γ)⁻¹ := by rw [h1]
      _ = w := by group

section Finite

variable [Finite Γ]

theorem relIndex_cenIn_autOn {V A W : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set Γ)) (hW : W ≤ V) :
    (@cenIn ↥V (commGroupOfElemAbelian hV) (autOn A V) (W.subgroupOf V)).relIndex (autOn A V) =
      (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A := by
  rw [cenIn_autOn_eq hV hW]
  set A' : Subgroup Γ := A ⊓ Subgroup.centralizer (W : Set Γ) with hA'
  have hA'A : A' ≤ A := inf_le_left
  have hA'V : A' ≤ Subgroup.normalizer (V : Set Γ) := hA'A.trans hA
  have hCV : Subgroup.centralizer (V : Set Γ) ≤ Subgroup.centralizer (W : Set Γ) :=
    Subgroup.centralizer_le hW
  have hinf : A' ⊓ Subgroup.centralizer (V : Set Γ) = A ⊓ Subgroup.centralizer (V : Set Γ) := by
    ext x
    simp only [hA', Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCV h.2⟩, h.2⟩⟩
  have h1 := Subgroup.relIndex_mul_card (autOn A' V) (autOn A V)
  rw [inf_eq_left.mpr (autOn_le_autOn V hA'A)] at h1
  rw [card_autOn_eq_relIndex hA'V, card_autOn_eq_relIndex hA, hinf] at h1
  have hle : A ⊓ Subgroup.centralizer (V : Set Γ) ≤ A' := by
    rw [← hinf]
    exact inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex (A ⊓ Subgroup.centralizer (V : Set Γ)) A' A hle hA'A
  have hpos : 0 < (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A' := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h4 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set Γ)) A'
    rw [h0, zero_mul] at h4
    exact (Nat.card_pos (α := ↥A')).ne' h4.symm
  have h3 : (autOn A' V).relIndex (autOn A V) * (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A' =
      A'.relIndex A * (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A' :=
    h1.trans (h2.symm.trans (mul_comm _ _))
  exact Nat.eq_of_mul_eq_mul_right hpos h3

omit [Finite Γ] in
theorem relIndex_fixV_autOn {V A W : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set Γ)) (hW : W ≤ V) :
    (@fixV ↥V (commGroupOfElemAbelian hV) (autOn A V)).relIndex (W.subgroupOf V) =
      (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W := by
  have h1 : @fixV ↥V (commGroupOfElemAbelian hV) (autOn A V) =
      (Subgroup.centralizer (A : Set Γ)).subgroupOf V := fixOn_eq hV hA
  rw [h1, Subgroup.relIndex_subgroupOf hW, inf_comm, Subgroup.inf_relIndex_right]

theorem offender_card_lt_or_G {V A W : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set Γ)) (hOff : IsOffG V A)
    (hwt : Nat.card V < wtG V A) (hW : W ≤ V) :
    (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W <
        (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A ∨
      (IsOffG V (A ⊓ Subgroup.centralizer (W : Set Γ)) ∧
        Nat.card V < wtG V (A ⊓ Subgroup.centralizer (W : Set Γ))) := by
  have hOffA : @IsOff ↥V (commGroupOfElemAbelian hV) (autOn A V) :=
    (isOffG_iff_isOff_autOn hV hA).mp hOff
  have hStar : @IsOffStar ↥V (commGroupOfElemAbelian hV) (autOn A V) :=
    ⟨hOffA, by rw [wt_autOn hV hA]; exact hwt⟩
  rcases @offender_card_lt_or ↥V (commGroupOfElemAbelian hV) _ (autOn A V) hStar
      (W.subgroupOf V) with h | h
  · left
    rwa [relIndex_fixV_autOn hV hA hW, relIndex_cenIn_autOn hV hA hW] at h
  · right
    have hA' : A ⊓ Subgroup.centralizer (W : Set Γ) ≤ Subgroup.normalizer (V : Set Γ) :=
      inf_le_left.trans hA
    rw [cenIn_autOn_eq hV hW] at h
    exact ⟨(isOffG_iff_isOff_autOn hV hA').mpr h.1, by rw [← wt_autOn hV hA']; exact h.2⟩

end Finite

@[expose] def IsOffStarG (V A : Subgroup Γ) : Prop :=
  IsOffG V A ∧ Nat.card V < wtG V A

@[expose] def offStarT (V T : Subgroup Γ) : Set (Subgroup Γ) :=
  {A | A ≤ T ∧ IsOffStarG V A}

@[expose] def offStarMin (V T : Subgroup Γ) : Set (Subgroup Γ) :=
  {A | A ∈ offStarT V T ∧ ∀ B ∈ offStarT V T, B ≤ A → B = A}

@[expose] def qSub (V T : Subgroup Γ) : Subgroup Γ :=
  ⨆ A ∈ offStarMin V T, A

open Classical in
@[expose] noncomputable def tZero (G T : Subgroup Γ) : Subgroup Γ :=
  if ⁅vSub G T, zSub T⁆ = ⊥ then qSub (vSub G T) T else zSub T

theorem tZero_of_ne {G T : Subgroup Γ} (h : ⁅vSub G T, zSub T⁆ ≠ ⊥) : tZero G T = zSub T := by
  simp [tZero, h]

theorem tZero_of_eq {G T : Subgroup Γ} (h : ⁅vSub G T, zSub T⁆ = ⊥) :
    tZero G T = qSub (vSub G T) T := by
  simp [tZero, h]

theorem le_qSub {V T A : Subgroup Γ} (hA : A ∈ offStarMin V T) : A ≤ qSub V T :=
  le_iSup₂ (f := fun (A : Subgroup Γ) (_ : A ∈ offStarMin V T) => A) A hA

theorem qSub_le {V T : Subgroup Γ} : qSub V T ≤ T :=
  iSup₂_le fun _ hA => hA.1.1

section Finite

variable [Finite Γ]

theorem exists_offStarMin_le {V T A : Subgroup Γ} (hA : A ∈ offStarT V T) :
    ∃ B ∈ offStarMin V T, B ≤ A := by
  obtain ⟨B, ⟨hBT, hBA⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Γ)).has_min
    {B : Subgroup Γ | B ∈ offStarT V T ∧ B ≤ A} ⟨A, hA, le_rfl⟩
  refine ⟨B, ⟨hBT, fun C hC hCB => ?_⟩, hBA⟩
  by_contra hne
  exact hmin C ⟨hC, hCB.trans hBA⟩ (lt_of_le_of_ne hCB hne)

end Finite

end CFSG.CGT.PushingUpLit.BHS7
