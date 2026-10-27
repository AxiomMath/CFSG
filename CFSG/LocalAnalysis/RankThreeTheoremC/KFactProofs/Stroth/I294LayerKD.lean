module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.HardMathSupport.Dickson.KD.CharP
public import CFSG.GH74.GLS.Stage2.Local.GHSchLie
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem glaPComponent_ne_bot_of {G : Type*} [Group G] {p : ℕ} {X K : Subgroup G}
    (h : GLAPComponent p X K) : K ≠ ⊥ := by
  intro hK
  have h3 := h.2.2.1
  subst hK
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

private theorem coprime_ker_subtype_aux {G : Type*} [Group G] (p : ℕ) (L : Subgroup G)
    (A : Subgroup ↥L) : Nat.Coprime p (Nat.card ↥(A ⊓ L.subtype.ker)) := by
  rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right _

private theorem coprime_ker_mulEquiv_aux {A B : Type*} [Group A] [Group B] (p : ℕ) (e : A ≃* B)
    (S : Subgroup A) : Nat.Coprime p (Nat.card ↥(S ⊓ e.toMonoidHom.ker)) := by
  have hke : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective
  rw [hke, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right _

section Holds


theorem glaPLayer_centralizer_eq_bot_of_charP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type}
    [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = p) (hLe : Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group))
    {w : Y} (hwL : w ∈ L) (hwp : w ^ p = 1) (hw1 : w ≠ 1) :
    GLAPLayer p (Subgroup.centralizer ({w} : Set Y)) = ⊥ := by
  obtain ⟨e⟩ := hLe
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w', hw'⟩ : ∃ w' : L, (w' : Y) = w := ⟨⟨w, hwL⟩, rfl⟩
  have hw'p : w' ^ p = 1 := Subtype.ext (by simpa [hw'] using hwp)
  have hw'1 : w' ≠ 1 := fun h => hw1 (by rw [← hw', h, Subgroup.coe_one])
  have hw'o : orderOf w' = p := orderOf_eq_prime hw'p hw'1
  have hou : orderOf (e w') = p := by
    rw [← hw'o]
    exact orderOf_injective e.toMonoidHom e.injective w'
  have hK : GLAPLayer p (Subgroup.centralizer ({e w'} : Set (TauCeti.CFSGIndex.lie d).Group)) = ⊥ :=
    CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp hp2 d hd (e w') hou
  have hd' : d.1.characteristic ≠ 2 := by
    rw [hd]
    exact hp2
  obtain ⟨t, n, f, hmod⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd d hd' e
  have ht : t ≠ StatedLieTag.twistedF4 ∧ t ≠ StatedLieTag.Tits := by
    have hadm := hmod.admissible
    constructor
    · rintro rfl
      have h3 : n = 0 ∧ d.1.characteristic = 2 ∧ Odd f ∧ 3 ≤ f := hadm.2.2
      exact hd' h3.2.1
    · rintro rfl
      have h3 : n = 0 ∧ d.1.characteristic = 2 ∧ f = 1 := hadm.2.2
      exact hd' h3.2.1
  have hS : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
    CFSG.GH74.GLS.Stage2.Local.GHSch.lieModel_outer_solvable ht hmod
  let Ψ : Y →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp
      (MulAut.conjNormal (H := L))
  have hΨ : ∀ y : Y, Ψ y = 1 → y ∈ L := by
    intro y hy
    have h1 : MulAut.conjNormal (H := L) y ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
      (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := L) y)).1 hy
    obtain ⟨l, hl⟩ := h1
    have h2 : MulAut.conjNormal (H := L) (l : Y) = MulAut.conjNormal (H := L) y := by
      rw [MulAut.conjNormal_val]
      exact hl
    have h3 : (l : Y) = y := i294_conjNormal_injective hC h2
    rw [← h3]
    exact l.2
  have hJL : ∀ J : Subgroup Y, GLAPComponent p (Subgroup.centralizer ({w} : Set Y)) J → J ≤ L := by
    intro J hJ
    have hperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
    have hJ' : ⁅J.map Ψ, J.map Ψ⁆ = J.map Ψ := by
      rw [← Subgroup.map_commutator, hperf]
    haveI : Group.IsPerfect ↥(J.map Ψ) := Subgroup.isPerfect_iff.2 hJ'
    have htriv : J.map Ψ = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥(J.map Ψ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      exact Group.IsPerfect.not_isSolvable (↥(J.map Ψ)) inferInstance
    intro j hj
    apply hΨ j
    have hmem : Ψ j ∈ J.map Ψ := Subgroup.mem_map_of_mem Ψ hj
    rw [htriv, Subgroup.mem_bot] at hmem
    exact hmem
  have hmain : ∀ J : Subgroup Y, GLAPComponent p (Subgroup.centralizer ({w} : Set Y)) J → False := by
    intro J hJ
    have hJL' : J ≤ L := hJL J hJ
    have hJc : GLAPComponent p (Subgroup.centralizer ({w} : Set Y) ⊓ L) J :=
      CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp hJ (le_inf hJ.1 hJL') inf_le_left
    have hAL : ((Subgroup.centralizer ({w} : Set Y)).subgroupOf L).map L.subtype =
        Subgroup.centralizer ({w} : Set Y) ⊓ L := Subgroup.subgroupOf_map_subtype _ _
    obtain ⟨J₁, hJ₁, -⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_glaPComponent_map_eq (K' := J)
      hp L.subtype (coprime_ker_subtype_aux p L _) (by rw [hAL]; exact hJc)
    have hJ₂ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp e.toMonoidHom
      (coprime_ker_mulEquiv_aux p e _) hJ₁
    have hCent : ((Subgroup.centralizer ({w} : Set Y)).subgroupOf L).map e.toMonoidHom =
        Subgroup.centralizer ({e w'} : Set (TauCeti.CFSGIndex.lie d).Group) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxw : x * w' = w' * x := Subtype.ext (by simpa [hw'] using hx)
        show e x * e w' = e w' * e x
        rw [← map_mul, ← map_mul, hxw]
      · intro hg
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        refine ⟨e.symm g, ?_, by simp⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
        have h1 : e.symm g * w' = w' * e.symm g := by
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact hg
        have h2 := congrArg Subtype.val h1
        simpa [hw'] using h2
    rw [hCent] at hJ₂
    have hle : J₁.map e.toMonoidHom ≤
        GLAPLayer p (Subgroup.centralizer ({e w'} : Set (TauCeti.CFSGIndex.lie d).Group)) :=
      le_sSup hJ₂
    rw [hK, le_bot_iff] at hle
    exact glaPComponent_ne_bot_of hJ₂ hle
  refine eq_bot_iff.2 (sSup_le fun J hJ => ?_)
  exact (hmain J hJ).elim

theorem i294InnerLieLayer_holds : I294InnerLieLayer := by
  intro p Y _ _ L _ z g D cfg hDL d hd hLe w hwD hw1
  exact glaPLayer_centralizer_eq_bot_of_charP cfg.prime cfg.odd cfg.cent d hd hLe (hDL hwD)
    (cfg.elem.2 w hwD) hw1

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
