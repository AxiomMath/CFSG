module

public import CFSG.CGT.PushingUpLit.BHS.FourSixA
public import CFSG.CGT.PushingUpLit.BHS.FourSymA

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def ConnD (D : Set (Subgroup (MulAut V))) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D,
    Relation.ReflTransGen (fun A B => A ∈ D ∧ B ∈ D ∧ NonComm A B) X Y

section Basic

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem Hyp41.exists_conj_of_connD (h : Hyp41 P D) (hc : ConnD D) {X Y : Subgroup (MulAut V)}
    (hX : X ∈ D) (hY : Y ∈ D) : ∃ g ∈ P, Y = conjSub g X := by
  have hxy := hc X hX Y hY
  induction hxy with
  | refl => exact ⟨1, P.one_mem, (conjSub_one _).symm⟩
  | tail _ hbc ih =>
    obtain ⟨hB, hC, hnc⟩ := hbc
    obtain ⟨g, hg, hb⟩ := ih hB
    rcases h.four_eight_conj hB hC with hcomm | ⟨g', hg', hC'⟩
    · exfalso
      obtain ⟨a, ha, b, hb', hne⟩ := hnc
      exact hne (hcomm a ha b hb')
    · refine ⟨g' * g, P.mul_mem ((sup_le (h.le _ hB) (h.le _ hC)) hg') hg, ?_⟩
      rw [conjSub_mul, ← hb]
      exact hC'

theorem four_fifteen_M (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    {A B L : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D) (hAM : A ≤ M) (hBM : B ≤ M)
    (hne : A ≠ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hL : L ∈ lamSet P D M)
    (hAL : A ≤ L) (hLM : ¬ L ≤ M) : ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := by
  have hAB : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup (h.elemAb A hA) (h.elemAb B hB) hcomm
  have hAB2 : IsPGroup 2 ↥(A ⊔ B) :=
    Glauberman.isPGroup_two_of_sq_eq_one hAB.2
  obtain ⟨T', hT', hh⟩ := Hyp42.exists_conj h.toHyp42 (g := 1) P.one_mem hAB2
    (by rw [conjSub_one]; exact sup_le hAM hBM)
  rw [conjSub_one] at hh
  have hh43 : Hyp43 P D T' M := ⟨hh, h.max⟩
  exact four_fifteen hh43 hV ⟨hA, le_sup_left.trans hT'⟩ ⟨hB, le_sup_right.trans hT'⟩ hne hL hAL
    hLM

theorem exists_pivot (h : Hyp42 P D T M) (hV : ∀ v : V, v ^ 2 = 1) :
    ∃ A ∈ D, A ≤ T ∧ ∃ L ∈ lamSet P D M, A ≤ L ∧ ¬ L ≤ M := by
  obtain ⟨A₀, hA₀, hA₀c⟩ : ∃ A ∈ D, A ∉ dCore P D M := by
    by_contra hall
    push Not at hall
    exact h.ne_core (Set.Subset.antisymm (fun A hA => hall A hA) (fun A hA => hA.1))
  obtain ⟨g, hg, L, hL, hA₀L, hA₀g, hLg⟩ := four_twelve h hV hA₀ hA₀c
  have hA₁ : conjSub g⁻¹ A₀ ≤ M := by
    have := conjSub_mono g⁻¹ hA₀g
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  have hA₁D : conjSub g⁻¹ A₀ ∈ D := h.conj_mem A₀ hA₀ g⁻¹ (P.inv_mem hg)
  have hA₁2 : IsPGroup 2 (conjSub g⁻¹ A₀) :=
    Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb _ hA₁D).2
  have hTM : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le
  obtain ⟨m, hm, hAm⟩ := FourTwoTools.exists_conjSub_ge hTM hA₁2 hA₁
  have hmP : m ∈ P := h.M_le hm
  have hAT : conjSub m⁻¹ (conjSub g⁻¹ A₀) ≤ T := by
    have := conjSub_mono m⁻¹ hAm
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  refine ⟨conjSub m⁻¹ (conjSub g⁻¹ A₀), h.conj_mem _ hA₁D m⁻¹ (P.inv_mem hmP), hAT,
    conjSub m⁻¹ (conjSub g⁻¹ L), ?_, conjSub_mono _ (conjSub_mono _ hA₀L), ?_⟩
  · have := lamSet_conj h.toHyp41 (lamSet_conj h.toHyp41 hL (P.inv_mem hg)) (P.inv_mem hmP)
    exact this
  · intro hle
    apply hLg
    have hmM : conjSub m M = M := conjSub_self_of_mem hm
    have h1 := conjSub_mono m hle
    rw [FourTwoTools.conjSub_conjSub_inv, hmM] at h1
    have h2 := conjSub_mono g h1
    rwa [FourTwoTools.conjSub_conjSub_inv] at h2

end Basic

section TwoOne

variable {Γ : Type} [Group Γ]

theorem two_one_rel {P M N : Subgroup Γ} {D : Set (Subgroup Γ)} (hMP : M ≤ P) (hNP : N ≤ P)
    (hnorm : ∀ A ∈ D, ∀ g ∈ P, conjSub g A ∈ D)
    (hclass : ∀ A ∈ D, ∀ B ∈ D, ∃ g ∈ P, B = conjSub g A)
    (hgen : P ≤ ⨆ A ∈ D, A) (hcover : ∀ A ∈ D, A ≤ M ∨ A ≤ N) : M = P ∨ N = P := by
  by_cases hall : ∀ A ∈ D, A ≤ M
  · left
    exact le_antisymm hMP (hgen.trans (iSup₂_le hall))
  · right
    push Not at hall
    obtain ⟨A₀, hA₀, hA₀M⟩ := hall
    set D₀ : Set (Subgroup Γ) := {A | A ∈ D ∧ ¬ A ≤ M} with hD₀
    set Dt : Subgroup Γ := ⨆ A ∈ D₀, A with hDt
    have hDtN : Dt ≤ N := iSup₂_le fun A hA => (hcover A hA.1).resolve_left hA.2
    have hMnorm : ∀ A ∈ D₀, ∀ g ∈ M, conjSub g A ∈ D₀ := by
      intro A hA g hg
      refine ⟨hnorm A hA.1 g (hMP hg), fun hle => hA.2 ?_⟩
      have := conjSub_mono g⁻¹ hle
      rwa [FourTwoTools.conjSub_inv_conjSub, conjSub_self_of_mem (M.inv_mem hg)] at this
    have hMle : M ≤ Subgroup.normalizer (Dt : Set Γ) := FourTwoTools.le_normalizer_iSup hMnorm
    have hD₀le : ∀ A ∈ D₀, A ≤ Dt := fun A hA =>
      le_iSup₂_of_le (f := fun (B : Subgroup Γ) (_ : B ∈ D₀) => B) A hA le_rfl
    have hPnorm : P ≤ Subgroup.normalizer (Dt : Set Γ) := by
      refine hgen.trans (iSup₂_le fun A hA => ?_)
      by_cases hAM : A ≤ M
      · exact hAM.trans hMle
      · exact (hD₀le A ⟨hA, hAM⟩).trans Subgroup.le_normalizer
    have hDtP : P ≤ Dt := by
      refine hgen.trans (iSup₂_le fun A hA => ?_)
      obtain ⟨g, hg, rfl⟩ := hclass A₀ hA₀ A hA
      intro x hx
      rw [mem_conjSub_iff] at hx
      have hgn : g⁻¹ ∈ Subgroup.normalizer (Dt : Set Γ) :=
        (Subgroup.normalizer _).inv_mem (hPnorm hg)
      have := (Subgroup.mem_normalizer_iff.1 hgn x).2
      rw [inv_inv] at this
      exact (this (hDt ▸ hD₀le A₀ ⟨hA₀, hA₀M⟩ hx))
    exact le_antisymm hNP (hDtP.trans hDtN)

end TwoOne

section Cover

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem exists_comm_member (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    {B : Subgroup (MulAut V)} (hB : B ∈ D) (hBL : ¬ B ≤ L) :
    ∃ X ∈ dInter D L, ∀ x ∈ X, ∀ b ∈ B, x * b = b * x := by
  by_cases hnc : ∃ l ∈ L, ∃ b ∈ B, l * b ≠ b * l
  · obtain ⟨A, hAD, hAL, hAB, -⟩ := four_thirteen h hV hL hB hnc hBL
    exact ⟨A, ⟨hAD, hAL⟩, hAB⟩
  · push Not at hnc
    obtain ⟨S, hS, -⟩ := Glauberman.exists_isSylowOf_ge (K := L) (Q := ⊥)
      (fun g => ⟨0, by simp [Subsingleton.elim g 1]⟩) bot_le
    refine ⟨S, (hL.2.2.1 S).2 hS, fun x hx b hb => hnc x (hS.1 hx) b hb⟩

theorem four_thirteen_cover (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L U A : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M) (hLU : L ≤ U)
    (hAD : A ∈ D) (hAL : A ≤ L)
    (hcover : ∀ B ∈ D, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B ≤ U) : ∀ B ∈ D, B ≤ U := by
  intro B hB
  by_contra hBU
  have hBL : ¬ B ≤ L := fun hle => hBU (hle.trans hLU)
  obtain ⟨X, hX, hXB⟩ := exists_comm_member h hV hL hB hBL
  have hAS : IsSylowOf 2 A L := (hL.2.2.1 A).1 ⟨hAD, hAL⟩
  have hXS : IsSylowOf 2 X L := (hL.2.2.1 X).1 hX
  obtain ⟨l, hl, rfl⟩ := IsSLNatSection.sylow_conj hAS hXS
  have hlP : l ∈ P := hL.1 hl
  have hB' : conjSub l⁻¹ B ∈ D := h.conj_mem B hB l⁻¹ (P.inv_mem hlP)
  refine hBU ?_
  have hB'U : conjSub l⁻¹ B ≤ U := by
    refine hcover _ hB' fun a ha b' hb' => ?_
    have hb : l * b' * l⁻¹ ∈ B := by
      have := mem_conjSub_iff.1 hb'
      simpa using this
    have h2 := hXB (l * a * l⁻¹) (mem_conjSub_of_mem ha) _ hb
    calc a * b' = l⁻¹ * (l * a * l⁻¹ * (l * b' * l⁻¹)) * l := by group
      _ = l⁻¹ * (l * b' * l⁻¹ * (l * a * l⁻¹)) * l := by rw [h2]
      _ = b' * a := by group
  have h1 := conjSub_mono l hB'U
  rw [FourTwoTools.conjSub_conjSub_inv, conjSub_self_of_mem (hLU hl)] at h1
  exact h1

theorem four_thirteen_conn (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    (hAD : A ∈ D) (hAL : A ≤ L)
    (hX : ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ l ∈ L, ∀ b ∈ B, l * b = b * l)
    (hconn : ConnD D) : ∀ B ∈ D, B ≤ L := by
  have hAS : IsSylowOf 2 A L := (hL.2.2.1 A).1 ⟨hAD, hAL⟩
  have hcentral : ∀ B ∈ D, ¬ B ≤ L → ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := by
    intro B hB hBL
    obtain ⟨X, hXD, hXB⟩ := exists_comm_member h hV hL hB hBL
    have hXS : IsSylowOf 2 X L := (hL.2.2.1 X).1 hXD
    obtain ⟨l₀, hl₀, rfl⟩ := IsSLNatSection.sylow_conj hAS hXS
    have hl₀P : l₀ ∈ P := hL.1 hl₀
    have hB' : conjSub l₀⁻¹ B ∈ D := h.conj_mem B hB l₀⁻¹ (P.inv_mem hl₀P)
    have hB'ne : conjSub l₀⁻¹ B ≠ A := by
      intro heq
      apply hBL
      have h1 : B = conjSub l₀ A := by
        rw [← heq, FourTwoTools.conjSub_conjSub_inv]
      rw [h1]
      exact hXD.2
    have hB'comm : ∀ a ∈ A, ∀ b' ∈ conjSub l₀⁻¹ B, a * b' = b' * a := by
      intro a ha b' hb'
      have hb : l₀ * b' * l₀⁻¹ ∈ B := by
        have := mem_conjSub_iff.1 hb'
        simpa using this
      have h2 := hXB (l₀ * a * l₀⁻¹) (mem_conjSub_of_mem ha) _ hb
      calc a * b' = l₀⁻¹ * (l₀ * a * l₀⁻¹ * (l₀ * b' * l₀⁻¹)) * l₀ := by group
        _ = l₀⁻¹ * (l₀ * b' * l₀⁻¹ * (l₀ * a * l₀⁻¹)) * l₀ := by rw [h2]
        _ = b' * a := by group
    have hcen := hX _ hB' hB'ne hB'comm
    intro l hl b hb
    have hl' : l₀⁻¹ * l * l₀ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl₀) hl) hl₀
    have hb' : l₀⁻¹ * b * l₀ ∈ conjSub l₀⁻¹ B := by
      rw [mem_conjSub_iff]
      have e : l₀⁻¹⁻¹ * (l₀⁻¹ * b * l₀) * l₀⁻¹ = b := by group
      rw [e]
      exact hb
    have h3 := hcen _ hl' _ hb'
    calc l * b = l₀ * ((l₀⁻¹ * l * l₀) * (l₀⁻¹ * b * l₀)) * l₀⁻¹ := by group
      _ = l₀ * ((l₀⁻¹ * b * l₀) * (l₀⁻¹ * l * l₀)) * l₀⁻¹ := by rw [h3]
      _ = b * l := by group
  intro B hB
  have hchain := hconn A hAD B hB
  induction hchain with
  | refl => exact hAL
  | tail _ hbc ih =>
    obtain ⟨hY, hZ, ⟨a, ha, b, hb, hne⟩⟩ := hbc
    by_contra hZL
    exact hne (hcentral _ hZ hZL a (ih hY ha) b hb)

end Cover

end CFSG.CGT.PushingUpLit.BHS
