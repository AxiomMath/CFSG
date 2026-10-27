module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BWc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Coord
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BCount

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62 (mem_normalizer_of_conj_mem)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

abbrev Moved (P : Subgroup Y) : Type := {C : ComponentIndex Y // ¬ Fixed P C}

noncomputable instance (P : Subgroup Y) : Fintype (Moved P) := Fintype.ofFinite _

noncomputable instance movedAction (P : Subgroup Y) : MulAction ↥P (Moved P) where
  smul g C := ⟨cjComp (g : Y) C.1, fun hF => C.2 ((fixed_cjComp_iff g.2 C.1).1 hF)⟩
  one_smul C := Subtype.ext (Lemma213.cjComp_one C.1)
  mul_smul g g' C := Subtype.ext (Lemma213.cjComp_mul (g : Y) (g' : Y) C.1)

theorem Cfg.dvd_card_moved (h : Cfg p P x z) : p ∣ Nat.card (Moved P) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hmod := h.isPGroup.card_modEq_card_fixedPoints (Moved P)
  have hfix : Nat.card (MulAction.fixedPoints ↥P (Moved P)) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨C, hC⟩
    apply C.2
    intro g hg
    have := hC ⟨g, hg⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (congrArg Subtype.val (congrArg Subtype.val this))
  rw [hfix] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

theorem Cfg.center_eq_bot_of_cyclic (h : Cfg p P x z) (h610 : GL83.I_6_10_1)
    {C : ComponentIndex Y} (hcyc : IsCyclic ↥(P ⊓ C.1)) : center C.1 = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hne
  have hpg : IsPGroup p (center C.1) := by
    rw [IsPGroup.iff_orderOf]
    intro a
    have hc : (a : Y) ∈ CFSG.pCore p Y := by
      refine CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.center_comp_le_pCore h.core C
        (a : ↥C.1).2 fun g hg => ?_
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp a.2) ⟨g, hg⟩)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := p) (G := Y)))
      ⟨(a : Y), hc⟩
    exact ⟨n, by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      simpa using hn⟩
  haveI : Nontrivial (center C.1) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨m, hm, hmcard⟩ := hpg.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (center C.1) := hmcard ▸ dvd_pow_self p hm.ne'
  exact h.not_isCyclic_inf_comp h610 C hdvd hcyc


theorem Cfg.moved_family (h : Cfg p P x z)
    (hM : ∀ C : ComponentIndex Y, ¬ Fixed P C → IsCyclic ↥(P ⊓ C.1) ∧ center C.1 = ⊥) :
    ∃ E : Subgroup Y, E = ⨆ i : Moved P, omega1 p P i.1 ∧ E ≤ P ∧ E ≤ layer Y ∧
      IsElemAbelian p E ∧
      (∀ g ∈ P, g ∈ normalizer (E : Set Y)) ∧ p ^ Nat.card (Moved P) ≤ Nat.card E ∧
      (∀ e ∈ E, (∀ i : Moved P, ∀ c ∈ i.1.1, c * e = e * c) → e = 1) := by
  classical
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  let K : Moved P → ComponentIndex Y := fun i => i.1
  have hK : Function.Injective K := Subtype.val_injective
  let U : Moved P → Subgroup Y := fun i => omega1 p P i.1
  have hU : ∀ i, U i ≤ (K i).1 := fun i => (omega1_le p P i.1).trans inf_le_right
  have hUinfo : ∀ i, ∃ a₀ : Y, a₀ ∈ P ⊓ i.1.1 ∧ orderOf a₀ = p ∧ U i = zpowers a₀ :=
    fun i => h.omega1_eq_zpowers (hM i.1 i.2).1
  have hUe : ∀ i, IsElemAbelian p (U i) := by
    intro i
    obtain ⟨a₀, -, ho, he⟩ := hUinfo i
    rw [he]
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one ?_)
    rw [← ho]
    exact pow_orderOf_eq_one a₀
  have hUc : ∀ i, Nat.card (U i) = p := by
    intro i
    obtain ⟨a₀, -, ho, he⟩ := hUinfo i
    rw [he, Nat.card_zpowers, ho]
  obtain ⟨hE1, hE2, -⟩ := card_iSup_components hp K hK U hU hUe
  have hcp : ∀ i, centralPart (K i) (U i) = ⊥ := by
    intro i
    have hz := (hM i.1 i.2).2
    unfold centralPart
    show U i ⊓ (center i.1.1).map i.1.1.subtype = ⊥
    rw [hz, Subgroup.map_bot, inf_bot_eq]
  have hprod : ∏ i, Nat.card (U i) = p ^ Nat.card (Moved P) := by
    rw [Finset.prod_congr rfl (fun i _ => hUc i), Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hprod1 : ∏ i, Nat.card (centralPart (K i) (U i)) = 1 := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [hcp i, Subgroup.card_bot])]
    simp
  refine ⟨⨆ i, U i, rfl, iSup_le fun i => (omega1_le p P i.1).trans inf_le_left,
    iSup_le fun i => (hU i).trans (component_le_layer i.1.2), hE1, ?_, ?_, ?_⟩
  ·
    have hconj : ∀ g ∈ P, ∀ e ∈ ⨆ i, U i, g * e * g⁻¹ ∈ ⨆ i, U i := by
      intro g hg e he
      refine Subgroup.iSup_induction U (C := fun e => g * e * g⁻¹ ∈ ⨆ i, U i) he ?_ ?_ ?_
      · intro i e hei
        have hmap : (U i).map (MulAut.conj g).toMonoidHom = omega1 p P (cjComp g i.1) :=
          map_conj_omega1 p hg i.1
        have hmem : g * e * g⁻¹ ∈ omega1 p P (cjComp g i.1) := hmap ▸ ⟨e, hei, rfl⟩
        let i' : Moved P := ⟨cjComp g i.1, fun hF => i.2 ((fixed_cjComp_iff hg i.1).1 hF)⟩
        exact Subgroup.mem_iSup_of_mem i' hmem
      · simp
      · intro a b ha hb
        rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
        exact mul_mem ha hb
    exact fun g hg => mem_normalizer_of_conj_mem (hconj g hg)
  · calc p ^ Nat.card (Moved P) = ∏ i, Nat.card (U i) := hprod.symm
      _ ≤ Nat.card (⨆ i, U i : Subgroup Y) * ∏ i, Nat.card (centralPart (K i) (U i)) := hE2
      _ = Nat.card (⨆ i, U i : Subgroup Y) := by rw [hprod1, mul_one]
  · intro e he hcomm
    rw [← Count.joinMul_range K U hK hU] at he
    obtain ⟨u, rfl⟩ := he
    have hu : ∀ j, u j = 1 := by
      intro j
      have hcj : (⟨(u j : Y), hU j (u j).2⟩ : ↥(K j).1) ∈ center ↥(K j).1 := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have hcc : Commute (g : Y) (Count.joinMul K U hK hU u) := hcomm j (g : Y) g.2
        have := (Count.commute_joinMul_iff K U hK hU u j g.2).1 hcc
        exact this.eq
      have hz := (hM j.1 j.2).2
      rw [hz, Subgroup.mem_bot] at hcj
      exact Subtype.ext (by simpa using congrArg Subtype.val hcj)
    have hu1 : u = 1 := funext hu
    rw [hu1, map_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
