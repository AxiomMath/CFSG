module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Side
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78ActTw
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l78_twoRes_le_twoRes {N N' : Subgroup G} (h : twoRes N ≤ N') :
    twoRes N ≤ twoRes N' := by
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  exact sec7l78_odd_mem_twoRes (h (sec7l78_odd_mem_twoRes hg.1 hg.2)) hg.2

theorem sec7l78_BD_eq_of_le [Finite G] (hP : Asc82Tab6P) {L L' K P P' B D A : Subgroup G}
    {t s : G} (hsL : Sec7L78Side L P B A t) (hsL' : Sec7L78Side L' P' D A s) (hKL : K ≤ L)
    (hKL' : K ≤ L') (hW₁ : twoRes (L ⊓ normalizer (B : Set G)) ≤ K)
    (hW₂ : twoRes (L' ⊓ normalizer (D : Set G)) ≤ K) :
    B = D ∧ twoRes (L ⊓ normalizer (B : Set G)) = twoRes (L' ⊓ normalizer (D : Set G)) := by
  obtain ⟨φ₁, h₁⟩ := sec7l78_act_of_aut_B hP hsL.om hsL.syl hsL.norm
  obtain ⟨φ₂, h₂⟩ := sec7l78_act_of_aut_B hP hsL'.om hsL'.syl hsL'.norm
  have hBA : B ≤ A := (le_of_eq hsL.inf_eq.symm).trans inf_le_left
  have hDA : D ≤ A := (le_of_eq hsL'.inf_eq.symm).trans inf_le_left
  have hBL' : B ≤ L' := (h₁.B_le_twoRes.trans hW₁).trans hKL'
  have hDL : D ≤ L := (h₂.B_le_twoRes.trans hW₂).trans hKL
  have hBD : B = D := le_antisymm (hsL'.inf_eq ▸ le_inf hBA hBL')
    (hsL.inf_eq ▸ le_inf hDA hDL)
  refine ⟨hBD, ?_⟩
  subst D
  have hHN₁ : K ⊓ normalizer (B : Set G) ≤ L ⊓ normalizer (B : Set G) :=
    le_inf (inf_le_left.trans hKL) inf_le_right
  have hHN₂ : K ⊓ normalizer (B : Set G) ≤ L' ⊓ normalizer (B : Set G) :=
    le_inf (inf_le_left.trans hKL') inf_le_right
  have hW₁H : twoRes (L ⊓ normalizer (B : Set G)) ≤ K ⊓ normalizer (B : Set G) :=
    le_inf hW₁ ((sec7l78_twoRes_le _).trans inf_le_right)
  have hW₂H : twoRes (L' ⊓ normalizer (B : Set G)) ≤ K ⊓ normalizer (B : Set G) :=
    le_inf hW₂ ((sec7l78_twoRes_le _).trans inf_le_right)
  exact (sec7l78_twoRes_eq_of_le hW₁H hHN₁).symm.trans (sec7l78_twoRes_eq_of_le hW₂H hHN₂)

theorem sec7l78_BD_eq_om6 [Finite G] (hP : Asc82Tab6P) (hE : Asc82E16Good)
    {L L' K P P' B D A : Subgroup G} {t s : G} (hsL : Sec7L78Side L P B A t)
    (hsL' : Sec7L78Side L' P' D A s) (hK : IsOm6P K)
    (hW₁ : twoRes (L ⊓ normalizer (B : Set G)) ≤ K)
    (hW₂ : twoRes (L' ⊓ normalizer (D : Set G)) ≤ K) :
    B = D ∧ twoRes (L ⊓ normalizer (B : Set G)) = twoRes (L' ⊓ normalizer (D : Set G)) := by
  obtain ⟨φ₁, h₁⟩ := sec7l78_act_of_aut_B hP hsL.om hsL.syl hsL.norm
  obtain ⟨φ₂, h₂⟩ := sec7l78_act_of_aut_B hP hsL'.om hsL'.syl hsL'.norm
  have hBA : B ≤ A := (le_of_eq hsL.inf_eq.symm).trans inf_le_left
  have hDA : D ≤ A := (le_of_eq hsL'.inf_eq.symm).trans inf_le_left
  have hBK : B ≤ K := h₁.B_le_twoRes.trans hW₁
  have hDK : D ≤ K := h₂.B_le_twoRes.trans hW₂
  have hW₁N : twoRes (L ⊓ normalizer (B : Set G)) ≤ K ⊓ normalizer (B : Set G) :=
    le_inf hW₁ ((sec7l78_twoRes_le _).trans inf_le_right)
  have hW₂N : twoRes (L' ⊓ normalizer (D : Set G)) ≤ K ⊓ normalizer (D : Set G) :=
    le_inf hW₂ ((sec7l78_twoRes_le _).trans inf_le_right)
  have hdvdB : 5 ∣ Nat.card ↥(K ⊓ normalizer (B : Set G)) := by
    have h9 : 960 ∣ Nat.card ↥(K ⊓ normalizer (B : Set G)) := by
      have h := Subgroup.card_dvd_of_le hW₁N
      rwa [h₁.card_twoRes] at h
    exact dvd_trans (by norm_num) h9
  obtain ⟨PB, hPB, hBnorm⟩ := hE G K hK B h₁.elem hBK hdvdB
  have hCB : K ⊓ centralizer (B : Set G) = B := (hP.aut_B G K hK PB hPB B hBnorm).2.1
  have hDcent : D ≤ centralizer (B : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hsL.A_comm b (hBA hb) d (hDA hd)
  have hDB : D ≤ B := hCB ▸ le_inf hDK hDcent
  have hdvdD : 5 ∣ Nat.card ↥(K ⊓ normalizer (D : Set G)) := by
    have h9 : 960 ∣ Nat.card ↥(K ⊓ normalizer (D : Set G)) := by
      have h := Subgroup.card_dvd_of_le hW₂N
      rwa [h₂.card_twoRes] at h
    exact dvd_trans (by norm_num) h9
  obtain ⟨PD, hPD, hDnorm⟩ := hE G K hK D h₂.elem hDK hdvdD
  have hCD : K ⊓ centralizer (D : Set G) = D := (hP.aut_B G K hK PD hPD D hDnorm).2.1
  have hBcent : B ≤ centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => hsL.A_comm d (hDA hd) b (hBA hb)
  have hBD' : B ≤ D := hCD ▸ le_inf hBK hBcent
  have hBD : B = D := le_antisymm hBD' hDB
  refine ⟨hBD, ?_⟩
  subst D
  obtain ⟨φK, hK_act⟩ := sec7l78_act_of_aut_B hP hK hPB hBnorm
  have hle₁ : twoRes (L ⊓ normalizer (B : Set G)) ≤ twoRes (K ⊓ normalizer (B : Set G)) :=
    sec7l78_twoRes_le_twoRes hW₁N
  have hle₂ : twoRes (L' ⊓ normalizer (B : Set G)) ≤ twoRes (K ⊓ normalizer (B : Set G)) :=
    sec7l78_twoRes_le_twoRes hW₂N
  have e₁ : twoRes (L ⊓ normalizer (B : Set G)) = twoRes (K ⊓ normalizer (B : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hle₁ (by rw [hK_act.card_twoRes, h₁.card_twoRes])
  have e₂ : twoRes (L' ⊓ normalizer (B : Set G)) = twoRes (K ⊓ normalizer (B : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hle₂ (by rw [hK_act.card_twoRes, h₂.card_twoRes])
  exact e₁.trans e₂.symm

theorem sec7l78_finish [Finite G] (hP : Asc82Tab6P) {L L' P P' B D A : Subgroup G} {t s : G}
    (hsL : Sec7L78Side L P B A t) (hsL' : Sec7L78Side L' P' D A s) (hBD : B = D)
    (hW : twoRes (L ⊓ normalizer (B : Set G)) = twoRes (L' ⊓ normalizer (D : Set G)))
    (hne : ∃ n ∈ L' ⊓ normalizer (D : Set G), t * n ≠ n * t) : False := by
  subst D
  obtain ⟨φ₁, h₁⟩ := sec7l78_act_of_aut_B hP hsL.om hsL.syl hsL.norm
  obtain ⟨u, huA, huc, b, hbB, ht⟩ := Sec7L78Side.decomp hP hsL' t hsL.c_mem
  obtain ⟨n, hnN₂, hnne⟩ := hne
  have hb_eq : b = u⁻¹ * t := by rw [ht]; group
  have hb_comm : ∀ x ∈ twoRes (L ⊓ normalizer (B : Set G)), x * b = b * x := by
    intro x hx
    have hxN₁ : x ∈ L ⊓ normalizer (B : Set G) := sec7l78_twoRes_le _ hx
    have hxW₂ : x ∈ twoRes (L' ⊓ normalizer (B : Set G)) := hW ▸ hx
    have hxN₂ : x ∈ L' ⊓ normalizer (B : Set G) := sec7l78_twoRes_le _ hxW₂
    have hxt : x * t = t * x := Subgroup.mem_centralizer_iff.mp hsL.c_cent x hxN₁.1
    have hxu : u * x = x * u := huc x hxN₂
    have hxu' : x * u⁻¹ = u⁻¹ * x := (Commute.inv_right (show Commute x u from hxu.symm)).eq
    rw [hb_eq]
    calc x * (u⁻¹ * t) = (x * u⁻¹) * t := by group
      _ = (u⁻¹ * x) * t := by rw [hxu']
      _ = u⁻¹ * (x * t) := by group
      _ = u⁻¹ * (t * x) := by rw [hxt]
      _ = (u⁻¹ * t) * x := by group
  have hb1 : b = 1 := h₁.cent_twoRes hbB hb_comm
  have ht_eq : t = u := by rw [ht, hb1, mul_one]
  refine hnne ?_
  rw [ht_eq]
  exact huc n hnN₂

end CFSG.OddStandard.SmallF3.Omega
