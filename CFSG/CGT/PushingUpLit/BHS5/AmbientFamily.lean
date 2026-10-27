module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientHyp51
public import CFSG.CGT.PushingUpLit.BHS5.JPart

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ] [Finite Γ] {G T M V : Subgroup Γ} (hv : VHyp G T M V)

include hv

theorem VHyp.family_off {A : Subgroup Γ}
    (hA : IsMaxElemAbelian T A) (hne : autOn A V ≠ ⊥) :
    @IsOff ↥V (commGroupOfElemAbelian hv.elem) (autOn A V) ∧
      @wt ↥V (commGroupOfElemAbelian hv.elem) (autOn A V) = Nat.card V := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hv.minpar.T_le.trans hv.normalized
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := hA.1.trans hTN
  have hnc : ¬ A ≤ Subgroup.centralizer (V : Set Γ) := fun hc =>
    hne (autOn_eq_bot_of_le_centralizer hc)
  have hoff : IsOff (autOn A V) := (isOffG_iff_isOff_autOn hv.elem hAN).1
    (isOffG_of_isMaxElemAbelian hv.elem hv.le_T hTN hA hnc)
  have hXP : autOn A V ≤ autOn G V := autOn_le_autOn V (hA.1.trans hv.minpar.T_le)
  have h51 := hv.hyp51
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  refine ⟨hoff, le_antisymm ?_ hoff.card_le_wt⟩
  rw [← offMax_eq_card h51 hV2]
  exact le_csSup (bddAbove_wt _) ⟨autOn A V, hXP, hoff, rfl⟩

omit [Finite Γ] hv in
theorem autOn_sup_of_le {X Z : Subgroup Γ} (hX : X ≤ Subgroup.normalizer (V : Set Γ))
    (hZ : Z ≤ Subgroup.normalizer (V : Set Γ)) : autOn (X ⊔ Z) V = autOn X V ⊔ autOn Z V := by
  unfold autOn
  rw [Subgroup.subgroupOf_sup hX hZ, Subgroup.map_sup]

omit [Finite Γ] hv in
@[expose] noncomputable def liftSub (V A : Subgroup Γ) (Y : Subgroup (MulAut ↥V)) : Subgroup Γ :=
  A ⊓ (Y.comap (conjAct V)).map (Subgroup.normalizer (V : Set Γ)).subtype

omit [Finite Γ] hv in
theorem liftSub_le (A : Subgroup Γ) (Y : Subgroup (MulAut ↥V)) : liftSub V A Y ≤ A := inf_le_left

omit [Finite Γ] hv in
theorem autOn_liftSub {A : Subgroup Γ} {Y : Subgroup (MulAut ↥V)} (hY : Y ≤ autOn A V) :
    autOn (liftSub V A Y) V = Y := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, haA₀, rfl⟩ := mem_autOn_iff.1 hy
    obtain ⟨x, hxY, hxa⟩ := haA₀.2
    have : x = a := Subtype.ext hxa
    rw [← this]
    exact hxY
  · intro hy
    obtain ⟨a, haA, rfl⟩ := mem_autOn_iff.1 (hY hy)
    exact mem_autOn_iff.2 ⟨a, ⟨haA, a, hy, rfl⟩, rfl⟩

omit [Finite Γ] hv in
theorem cen_le_liftSub {A : Subgroup Γ} (hA : A ≤ Subgroup.normalizer (V : Set Γ))
    (Y : Subgroup (MulAut ↥V)) : A ⊓ Subgroup.centralizer (V : Set Γ) ≤ liftSub V A Y := by
  intro g hg
  refine ⟨hg.1, ⟨(⟨g, hA hg.1⟩ : ↥(Subgroup.normalizer (V : Set Γ))), ?_, rfl⟩⟩
  show conjAct V ⟨g, hA hg.1⟩ ∈ Y
  rw [(conjAct_eq_one_iff V ⟨g, hA hg.1⟩).2 hg.2]
  exact Y.one_mem

theorem VHyp.family_sub {A : Subgroup Γ} (hA : IsMaxElemAbelian T A)
    (Y : Subgroup (MulAut ↥V)) (hY : Y ≤ autOn A V)
    (hw : @wt ↥V (commGroupOfElemAbelian hv.elem) (autOn A V) ≤
      @wt ↥V (commGroupOfElemAbelian hv.elem) Y) :
    ∃ A', IsMaxElemAbelian T A' ∧ autOn A' V = Y := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  set N : Subgroup Γ := Subgroup.normalizer (V : Set Γ) with hN
  have hTN : T ≤ N := hv.minpar.T_le.trans hv.normalized
  have hAN : A ≤ N := hA.1.trans hTN
  have hAel : IsElemAbelian 2 A := hA.2.1
  set A₀ : Subgroup Γ := liftSub V A Y with hA₀
  have hA₀A : A₀ ≤ A := liftSub_le A Y
  have hA₀N : A₀ ≤ N := hA₀A.trans hAN
  have hautA₀ : autOn A₀ V = Y := autOn_liftSub hY
  have hcenA₀ : A ⊓ Subgroup.centralizer (V : Set Γ) ≤ A₀ := cen_le_liftSub hAN Y
  have hw' : wtG V A ≤ wtG V A₀ := by
    rw [← wt_autOn hv.elem hAN, ← wt_autOn hv.elem hA₀N, hautA₀]
    exact hw
  set C : Subgroup Γ := V ⊓ Subgroup.centralizer (A₀ : Set Γ) with hC
  have hCV : C ≤ V := inf_le_left
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy.2 x hx
  have hA₀el : IsElemAbelian 2 A₀ := isElemAbelian_mono' hAel hA₀A
  have hCel : IsElemAbelian 2 C := isElemAbelian_mono' hv.elem hCV
  have hA'el : IsElemAbelian 2 (A₀ ⊔ C) := isElemAbelian_sup' hA₀el hCel hcomm
  have hA'T : A₀ ⊔ C ≤ T := sup_le (hA₀A.trans hA.1) (hCV.trans hv.le_T)
  have hcard : Nat.card A ≤ Nat.card ↥(A₀ ⊔ C) := by
    have hApos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) := Nat.card_pos
    have hcA : (A₀ ⊓ Subgroup.centralizer (V : Set Γ)) = A ⊓ Subgroup.centralizer (V : Set Γ) :=
      le_antisymm (inf_le_inf_right _ hA₀A) (le_inf (hcenA₀) inf_le_right)
    have hA1 := Subgroup.relIndex_mul_card (H := A ⊓ Subgroup.centralizer (V : Set Γ)) (K := A)
    rw [inf_eq_left.2 (inf_le_left : A ⊓ Subgroup.centralizer (V : Set Γ) ≤ A)] at hA1
    have hA01 := Subgroup.relIndex_mul_card
      (H := A₀ ⊓ Subgroup.centralizer (V : Set Γ)) (K := A₀)
    rw [inf_eq_left.2 (inf_le_left : A₀ ⊓ Subgroup.centralizer (V : Set Γ) ≤ A₀)] at hA01
    have hcardeq : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (V : Set Γ)) =
        Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set Γ)) := by rw [hcA]
    rw [hcardeq] at hA01
    have hsup := card_sup_mul_card_inf' hcomm
    have hinf : Nat.card ↥(A₀ ⊓ C) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) := by
      refine Subgroup.card_le_of_le fun x hx => ⟨hx.2.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      exact isElemAbelian_comm' hAel ha (hA₀A hx.1)
    have hw'' : (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) ≤
        (A₀ ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A₀ *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A₀ : Set Γ)) := hw'
    set c := Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set Γ)) with hc
    set r := (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A with hr
    set r₀ := (A₀ ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A₀ with hr₀
    refine Nat.le_of_mul_le_mul_right ?_ hApos
    calc Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ))
        = c * (r * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ))) := by rw [← hA1]; ring
      _ ≤ c * (r₀ * Nat.card ↥(V ⊓ Subgroup.centralizer (A₀ : Set Γ))) :=
        Nat.mul_le_mul_left _ hw''
      _ = Nat.card A₀ * Nat.card C := by rw [← hA01]; ring
      _ = Nat.card ↥(A₀ ⊔ C) * Nat.card ↥(A₀ ⊓ C) := hsup.symm
      _ ≤ Nat.card ↥(A₀ ⊔ C) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) :=
        Nat.mul_le_mul_left _ hinf
  refine ⟨A₀ ⊔ C, ⟨hA'T, hA'el, fun B hBT hBel => (hA.2.2 B hBT hBel).trans hcard⟩, ?_⟩
  have hCN : C ≤ N := hCV.trans Subgroup.le_normalizer
  have hCbot : autOn C V = ⊥ := by
    refine autOn_eq_bot_of_le_centralizer fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.2 fun v hv' => isElemAbelian_comm' hv.elem hv' hx.1
  rw [autOn_sup_of_le hA₀N hCN, hautA₀, hCbot, sup_bot_eq]

end CFSG.CGT.PushingUpLit.BHS5
