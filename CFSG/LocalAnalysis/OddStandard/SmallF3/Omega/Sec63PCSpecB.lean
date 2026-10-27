module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCRow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ}

theorem mem_centralizer_genOf_of_forall {gs : List Table} {x : Equiv.Perm (Fin n)}
    (h : ∀ g ∈ gs, tp n g * x = x * tp n g) :
    x ∈ centralizer (genOf n gs : Set (Equiv.Perm (Fin n))) := by
  rw [genOf, centralizer_closure, mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  exact h g (by simpa using hg)

theorem innerOK_fact {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n A₀ pg gg sift)
    {cap : ℕ} {t l₁ l₂ : Table} {tg : Equiv.Perm (Fin n)} (ht : Rep n t tg)
    (hl₁ : permOK n l₁ = true) (hl₂ : permOK n l₂ = true)
    (hA : Sec63PCA6 A₀ tg (genOf n [l₁, l₂])) {d : InnerData}
    (h : innerOK n cap sift t l₁ l₂ d = true) : Sec63PCFact A₀ tg := by
  have hn := hD.lt
  have hg2 : ∀ g ∈ [l₁, l₂], permOK n g = true := by
    intro g hg
    rcases List.mem_pair.mp hg with rfl | rfl
    · exact hl₁
    · exact hl₂
  simp only [innerOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨henum, hpb⟩, hib⟩, hmb⟩, hall⟩, hpc⟩, hic⟩, hsc⟩, heq⟩, hp1⟩, hp2⟩, hcc⟩,
    ⟨⟨⟨hpr1, hir1⟩, hmr1⟩, hcr1⟩, ⟨⟨⟨hpr2, hir2⟩, hmr2⟩, hcr2⟩⟩, hen8⟩ := h
  have hb : Rep n d.b (tp n d.b) := rep_tp hpb
  have hc : Rep n d.c (tp n d.c) := rep_tp hpc
  have hci : Rep n (invT n d.c) (tp n d.c)⁻¹ := rep_invT hc hic
  have hbL : tp n d.b ∈ genOf n [l₁, l₂] := tp_mem_genOf_of_memT hn hg2 henum hpb hmb
  have hconj := allInvConj_spec hn hg2 henum hb hall
  have hcA : tp n d.c ∈ A₀ := (hD.sift _ _ hc).1 hsc
  have hct : tp n d.c * tg * (tp n d.c)⁻¹ = tp n d.b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (tblEq_iff_eq (Rep.compT hc ht) (Rep.compT hb hc)).1 heq
  have hcent : Nat.card ↥(genOf n [l₁, l₂] ⊓ centralizer ({tp n d.b} : Set (Equiv.Perm (Fin n))) ⊓
      centralizer ((((genOf n [l₁, l₂]).map (MulAut.conj (tp n d.c)).toMonoidHom :
        Subgroup (Equiv.Perm (Fin n)))) : Set (Equiv.Perm (Fin n)))) ≤ 2 := by
    have hgs : ∀ g ∈ [d.b, conjT n d.c (invT n d.c) l₁, conjT n d.c (invT n d.c) l₂],
        permOK n g = true := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hpb
      · exact hp1
      · exact hp2
    have hcount := centCount_spec hn hg2 henum hgs
    refine le_trans (Subgroup.card_le_of_le ?_) (hcount ▸ hcc)
    intro x hx
    obtain ⟨⟨hxL, hxb⟩, hxc⟩ := mem_inf.mp hx |>.imp_left mem_inf.mp
    refine mem_inf.mpr ⟨hxL, mem_centralizer_genOf_of_forall fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    have hconjmem : ∀ l : Table, l ∈ [l₁, l₂] → tp n (conjT n d.c (invT n d.c) l) ∈
        ((genOf n [l₁, l₂]).map (MulAut.conj (tp n d.c)).toMonoidHom : Subgroup _) := by
      intro l hl
      have hlp := hg2 l hl
      rw [rep_unique (rep_tp (by
        rcases List.mem_pair.mp hl with rfl | rfl
        · exact hp1
        · exact hp2)) (rep_conjT hc hci (rep_tp hlp))]
      exact ⟨tp n l, tp_mem_genOf hl, rfl⟩
    rcases hg with rfl | rfl | rfl
    · exact (mem_centralizer_singleton_iff.mp hxb).symm
    · exact mem_centralizer_iff.mp hxc _ (hconjmem l₁ (by simp))
    · exact mem_centralizer_iff.mp hxc _ (hconjmem l₂ (by simp))
  have hgr : ∀ g ∈ [d.r₁, d.r₂], permOK n g = true := by
    intro g hg
    rcases List.mem_pair.mp hg with rfl | rfl
    · exact hpr1
    · exact hpr2
  have hrL : ∀ r ∈ [d.r₁, d.r₂], tp n r ∈ genOf n [l₁, l₂] := by
    intro r hr
    rcases List.mem_pair.mp hr with rfl | rfl
    · exact tp_mem_genOf_of_memT hn hg2 henum hpr1 hmr1
    · exact tp_mem_genOf_of_memT hn hg2 henum hpr2 hmr2
  have hrc : ∀ r ∈ [d.r₁, d.r₂], tp n r ∈ centralizer ({tp n d.b} : Set (Equiv.Perm (Fin n))) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    rcases List.mem_pair.mp hr with rfl | rfl
    · exact (commTT_iff (rep_tp hpr1) hb).mp hcr1
    · exact (commTT_iff (rep_tp hpr2) hb).mp hcr2
  have hr2 : ∀ r ∈ [d.r₁, d.r₂], orderOf (tp n r) = 2 := by
    intro r hr
    rcases List.mem_pair.mp hr with rfl | rfl
    · exact orderOf_eq_two_of_involOK hn (rep_tp hpr1) hir1
    · exact orderOf_eq_two_of_involOK hn (rep_tp hpr2) hir2
  have hRle : genOf n [d.r₁, d.r₂] ≤ genOf n [l₁, l₂] ⊓
      centralizer ({tp n d.b} : Set (Equiv.Perm (Fin n))) := by
    rw [genOf, closure_le]
    rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ [d.r₁, d.r₂] := by simpa using hr
    exact mem_inf.mpr ⟨hrL r hr', hrc r hr'⟩
  have hR8 : Nat.card ↥(genOf n [d.r₁, d.r₂]) = 8 := (enumOK_spec hn hgr hen8).1
  have hRgen : genOf n [d.r₁, d.r₂] =
      closure {r | r ∈ genOf n [d.r₁, d.r₂] ∧ orderOf r = 2} := by
    apply le_antisymm
    · rw [genOf, closure_le]
      rintro _ ⟨r, hr, rfl⟩
      have hr' : r ∈ [d.r₁, d.r₂] := by simpa using hr
      exact subset_closure ⟨tp_mem_genOf hr', hr2 r hr'⟩
    · rw [closure_le]
      exact fun r hr => hr.1
  exact sec63PC_fact_inner hA hbL hconj hcA hct hcent hRle hR8 hRgen

end CFSG.OddStandard.SmallF3.Omega
