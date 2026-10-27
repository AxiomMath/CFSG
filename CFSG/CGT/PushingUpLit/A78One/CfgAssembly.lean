module

public import CFSG.CGT.PushingUpLit.A78One.Dict
public import CFSG.CGT.PushingUpLit.A78One.NatExtend
public import CFSG.CGT.PushingUpLit.A78One.SideConj
public import CFSG.CGT.PushingUpLit.A78.JStructure

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K
open CFSG.CGT.PushingUpLit.A78

variable {G : Type} [Group G] [Finite G]
variable {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

namespace CexCtx

theorem cexP_le (c : CexCtx L M n T T' x) : cexP L T ≤ T' := le_sup_right.trans c.ge

theorem inf_centralizer_eq_cexP (c : CexCtx L M n T T' x) :
    T' ⊓ Subgroup.centralizer (blockU L : Set G) = cexP L T :=
  le_antisymm (inf_le_inf_right _ c.le) (le_inf c.cexP_le inf_le_right)

end CexCtx

theorem eq_of_isMax_of_le {H A B : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hB : IsMaxElemAbelian H B) (hle : A ≤ B) : A = B :=
  Subgroup.eq_of_le_of_card_ge hle (hA.2.2 B hB.1 hB.2.1)

theorem eq_of_isMax_of_elem {P B : Subgroup G} (hP : CFSG.Open.IsElemAbelian 2 P)
    (hB : IsMaxElemAbelian P B) : B = P :=
  Subgroup.eq_of_le_of_card_ge hB.1 (hB.2.2 P le_rfl hP)

theorem natExt_of_endData (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) :
    NatExt L (cexP L T) := by
  have hPmax : IsMaxElemAbelian T' (cexP L T) := (e.maxElem _).2 (Or.inl rfl)
  have hAmax : IsMaxElemAbelian T' (cj x⁻¹ (cexP L T)) := (e.maxElem _).2 (Or.inr rfl)
  have hcomm : ∀ a ∈ cexP L T, ∀ b ∈ cexP L T, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm' e.elem ha hb
  have hnt : ¬ cj x⁻¹ (cexP L T) ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro hAC
    have h1 := le_inf hAmax.1 hAC
    rw [c.inf_centralizer_eq_cexP] at h1
    exact e.ne (eq_of_isMax_of_le hAmax hPmax h1).symm
  have H45 := c.hyp45 hAmax hnt
  have hBP := H45.isMaxElemAbelian_B_P
  rw [c.inf_centralizer_eq_cexP] at hBP
  have hB : Hyp45.bGrp L (cj x⁻¹ (cexP L T)) = cexP L T := eq_of_isMax_of_elem e.elem hBP
  have hUP : blockU L ≤ cexP L T := by
    have h1 := H45.V_le_P
    rwa [c.inf_centralizer_eq_cexP] at h1
  have hdec : cexP L T =
      (cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
    calc cexP L T = Hyp45.bGrp L (cj x⁻¹ (cexP L T)) := hB.symm
      _ = (cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (blockU L : Set G)) ⊔ blockU L := rfl
      _ = ((cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (L : Set G)) ⊔
            (blockU L ⊓ cj x⁻¹ (cexP L T))) ⊔ blockU L := by rw [H45.inf_centralizer_eq]
      _ = (cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
          rw [sup_assoc, sup_eq_right.2 (inf_le_left : blockU L ⊓ cj x⁻¹ (cexP L T) ≤ blockU L)]
  have hCP : cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (L : Set G) ≤ cexP L T := by
    intro a ha
    have h2 : a ∈ Subgroup.centralizer (blockU L : Set G) :=
      Subgroup.centralizer_le (fun u hu => blockU_le L hu) ha.2
    have h3 : a ∈ T' ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hAmax.1 ha.1, h2⟩
    rwa [c.inf_centralizer_eq_cexP] at h3
  refine ⟨hUP, hcomm, ?_, ?_⟩
  · intro p hp
    rw [hdec, sup_comm] at hp
    have hnorm : ∀ h ∈ cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (L : Set G), ∀ k ∈ blockU L,
        h * k * h⁻¹ ∈ blockU L := by
      intro h hh k hk
      have h0 : h * k = k * h := hcomm h (hCP hh) k (hUP hk)
      rw [h0]
      simpa using hk
    obtain ⟨k, hk, h, hh, rfl⟩ := (mem_sup_iff_of_normalizes hnorm).1 hp
    exact ⟨k, hk, h, ⟨hCP hh, hh.2⟩, rfl⟩
  · apply le_antisymm
    · calc L ⊓ Subgroup.centralizer (cexP L T : Set G)
          ≤ L ⊓ Subgroup.centralizer (blockU L : Set G) :=
            inf_le_inf_left L (Subgroup.centralizer_le (fun u hu => hUP hu))
        _ = oTwoIn L := NatBlock.inf_centralizer_blockU c.hyp.natBlock
    · intro o ho
      have hoP : o ∈ cexP L T := by
        have h0 := c.inf_P
        rw [← h0] at ho
        exact ho.2
      exact ⟨oTwoIn_le L ho, Subgroup.mem_centralizer_iff.2 fun p hp => hcomm p hp o hoP⟩

omit [Finite G] in
theorem cj_eq_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cj g H = H := by
  ext y
  rw [mem_cj_iff]
  have h1 := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)
  have h2 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h2] at h1
  exact h1

theorem sideOne (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) :
    A78Side G L T (cexP L T ⊔ cj x⁻¹ (cexP L T)) n := by
  have hO := c.oTwoIn_LT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c.normalizer_eq]
    exact c.sylow
  · rw [hO]
    exact e.elem
  · rw [hO]
    exact c.exists_phi
  · rw [hO]
    exact NatExt.isNatSL_of_natExt c.hyp.natBlock.natData (natExt_of_endData c e)
  · rw [hO]
    exact e.sylowJ
  · rw [c.normalizer_eq]
    have hu := c.hyp.unique
    ext N
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN, hNle⟩
      have h1 : N ∈ maximalTwoLocalsContaining (L : Set G) :=
        ⟨hN, fun l hl => hNle (Subgroup.mem_sup_left hl)⟩
      rw [hu] at h1
      exact h1
    · rintro rfl
      exact ⟨c.hyp.maxLocal, fun y hy => (sup_le c.hyp.le c.sylow.le) hy⟩

theorem a78Cfg_of_endData (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) {x' : G}
    (h1 : x' ∈ Subgroup.normalizer (T : Set G)) (h2 : x' ∉ M)
    (h3 : cj x'⁻¹ (cexP L T) = cj x⁻¹ (cexP L T))
    (h4 : cj x'⁻¹ (cj x⁻¹ (cexP L T)) = cexP L T) :
    A78Cfg G L (cj x'⁻¹ L) T n := by
  have hO := c.oTwoIn_LT
  have hT : cj x'⁻¹ T = T := cj_eq_of_mem_normalizer (Subgroup.inv_mem _ h1)
  have hO2 : oTwoIn (cj x'⁻¹ L ⊔ T) = cj x⁻¹ (cexP L T) := by
    have h5 : cj x'⁻¹ L ⊔ T = cj x'⁻¹ (L ⊔ T) := by rw [cj_sup, hT]
    rw [h5, cj_oTwoIn, hO, h3]
  have hJ : oTwoIn (L ⊔ T) ⊔ oTwoIn (cj x'⁻¹ L ⊔ T) = cexP L T ⊔ cj x⁻¹ (cexP L T) := by
    rw [hO, hO2]
  have s1 := sideOne c e
  have s2 := (sideOne c e).conj x'⁻¹
  rw [hT, cj_sup, h3, h4, sup_comm] at s2
  refine ⟨c.hyp.kproper, c.hyp.simple, c.hyp.charTwo, c.hyp.two_le, ?_, ?_, ?_⟩
  · intro heq
    rw [c.normalizer_eq, cj_normalizer, c.normalizer_eq] at heq
    have hg : x' ∈ Subgroup.normalizer (M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h6 : y ∈ M ↔ y ∈ cj x'⁻¹ M := by rw [← heq]
      rw [h6, mem_cj_iff, inv_inv]
    rw [c.normalizer_M] at hg
    exact h2 hg
  · rw [hJ]
    exact s1
  · rw [hJ]
    exact s2

end CFSG.CGT.PushingUpLit.A78One
