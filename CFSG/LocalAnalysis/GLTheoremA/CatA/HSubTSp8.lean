module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8A
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
public import CFSG.Sporadic.Co2Schreier.SixGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def GUBlockFacts : Prop :=
  ∀ (E : Type) [Field E] (hE : UnitaryFieldData 2 1 E) (W : Type) [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E), Hf.IsSymm → Hf.SeparatingLeft →
      (Module.finrank E W ≤ 3 → Group.IsSolvable (sesqUnitaryGroup Hf)) ∧
      (Module.finrank E W = 4 → ∀ K : Subgroup (sesqUnitaryGroup Hf), CFSG.Open.IsComponentOf K ⊤ →
        catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two ∧ Nat.card ↥K = 25920 ∧
          Subgroup.center ↥K = ⊥)

@[expose] def Q8 : TauCeti.CFSGIndex → Prop := fun i => S9.isU4two i ∨ S9.isSp6two i ∨ S10.isA6 i

theorem isComponentOf_of_le_factor {G : Type} [Group G] {A B L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L (A ⊔ B)) (hLA : L ≤ A) : CFSG.Open.IsComponentOf L A := by
  refine ⟨hLA, ?_, hL.2.2⟩
  have h := hL.2.1.inf_of_le (le_sup_left : A ≤ A ⊔ B)
  rwa [inf_eq_left.mpr hLA] at h

theorem not_comp_top_of_solvable {G : Type} [Group G] (hs : Group.IsSolvable G) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : False := by
  haveI := hs
  have hX : Group.IsSolvable ↥(⊤ : Subgroup G) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.surjective
  exact not_isComponentOf_of_solvable hX hL

theorem card_of_catalogIs_alt6 {S : Type} [Group S]
    (h : catalogIs S CFSG.LocalAnalysis.GLTheoremA.S10.isA6) : Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | alternating n hn =>
    have hn6 : n = 6 := by simpa [CFSG.LocalAnalysis.GLTheoremA.S10.isA6] using hi
    subst hn6
    have e6 : (TauCeti.CFSGIndex.alternating 6 hn).Group ≃* alternatingGroup (Fin 6) :=
      MulEquiv.refl _
    rw [Nat.card_congr (f.toEquiv.trans e6.toEquiv)]
    rw [nat_card_alternatingGroup]
    have h4 : Nat.card (Fin 6) = 6 := by simp
    rw [h4]
    norm_num [Nat.factorial]
  | _ => exact absurd hi (by simp [CFSG.LocalAnalysis.GLTheoremA.S10.isA6])

theorem not_isMulCommutative_of_quasisimple {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    ¬ IsMulCommutative Q := by
  intro hc
  have hle : commutator Q ≤ ⊥ := by
    show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (IsMulCommutative.is_comm.comm a b)
  have htop : commutator Q = ⊤ := hq.1
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ commutator Q := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ commutator Q := by rw [htop]; exact Subgroup.mem_top y
    have hx' := hle hx
    have hy' := hle hy
    rw [Subgroup.mem_bot] at hx' hy'
    rw [hx', hy']
  haveI := hq.2
  exact (not_subsingleton (Q ⧸ Subgroup.center Q)) hsub

theorem sp8_comp (GU : GUBlockFacts) {s : ↥(StatedSp 4 (ZMod 2))} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {L : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({s} : Set ↥(StatedSp 4 (ZMod 2))))) :
    catalogIs (↥L ⧸ Subgroup.center ↥L) Q8 ∧
      (catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S10.isA6 →
        Nonempty (↥L ≃* alternatingGroup (Fin 6))) := by
  obtain ⟨s₀, m, A₀, A₁, hC⟩ := exists_class hs3 hs1
  have hsum := hC.sum_eq
  have hone := hC.one_le
  have hLC : CFSG.Open.IsComponentOf L (A₀ ⊔ A₁) := by
    rw [← hC.centralizer_eq]
    exact hL
  have hLC' : CFSG.Open.IsComponentOf L (A₁ ⊔ A₀) := by
    rw [sup_comm]
    exact hLC
  haveI := hL.2.2.2
  have hnc : ¬ IsMulCommutative ↥L := not_isMulCommutative_of_quasisimple hL.2.2
  have hnt : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  rcases comp_le_or_le hC.commute hLC with hLA₀ | hLA₁
  ·
    have hcomp0 := isComponentOf_of_le_factor hLC hLA₀
    have hK0 : CFSG.Open.IsComponentOf (L.subgroupOf A₀) ⊤ := isComponentOf_top_subgroupOf hcomp0
    rcases hC.fixed with ⟨hs0, hA0⟩ | ⟨hs0pos, ⟨e0⟩⟩
    ·
      exfalso
      have hLb : L ≤ ⊥ := by rw [← hA0]; exact hLA₀
      exact ((Subgroup.nontrivial_iff_ne_bot L).mp hnt) (le_bot_iff.mp hLb)
    · have hs0le : s₀ ≤ 3 := by
        have := hC.sum_eq
        have := hC.one_le
        omega
      rcases (by omega : s₀ = 1 ∨ s₀ = 2 ∨ s₀ = 3) with h1 | h2 | h3
      ·
        exfalso
        subst h1
        haveI := sp1_solvable
        have hsolA0 : Group.IsSolvable ↥A₀ :=
          Group.isSolvable_of_surjective (f := e0.symm.toMonoidHom) e0.symm.surjective
        exact not_comp_top_of_solvable hsolA0 hK0
      ·
        subst h2
        obtain ⟨eK⟩ := sp2_component_alt e0 hK0
        let eL : ↥L ≃* alternatingGroup (Fin 6) :=
          (Subgroup.subgroupOfEquivOfLe hLA₀).symm.trans eK
        haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
          alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
        haveI : IsSimpleGroup ↥L := eL.isSimpleGroup
        have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_not_comm L hnc
        let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6) :=
          (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans eL)
        exact ⟨KSubT.catalogIs_mono (fun i hi => Or.inr (Or.inr hi)) (catalogIs_alt6_of_equiv eQ),
          fun _ => ⟨eL⟩⟩
      ·
        subst h3
        haveI : IsSimpleGroup (StatedSp 3 (ZMod 2)) :=
          CFSG.Sporadic.Co2Schreier.isSimpleGroup_statedSp_three_two
        haveI : IsSimpleGroup ↥A₀ := e0.isSimpleGroup
        have hK0top : L.subgroupOf A₀ = ⊤ := by
          rcases CFSG.Open.IsSubnormal.eq_bot_or_top hK0.2.1 with hb | ht
          · exfalso
            haveI := hK0.2.2.2
            have hnt0 : Nontrivial ↥(L.subgroupOf A₀) :=
              (QuotientGroup.mk'_surjective (Subgroup.center ↥(L.subgroupOf A₀))).nontrivial
            exact ((Subgroup.nontrivial_iff_ne_bot _).mp hnt0) hb
          · exact ht
        have hA0le : A₀ ≤ L := Subgroup.subgroupOf_eq_top.mp hK0top
        have hLeq : L = A₀ := le_antisymm hLA₀ hA0le
        let eLS : ↥L ≃* StatedSp 3 (ZMod 2) := (MulEquiv.subgroupCongr hLeq).trans e0
        haveI : IsSimpleGroup (StatedSp 3 (ZMod 2)) :=
          CFSG.Sporadic.Co2Schreier.isSimpleGroup_statedSp_three_two
        haveI : IsSimpleGroup ↥L := eLS.isSimpleGroup
        have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_not_comm L hnc
        let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* StatedSp 3 (ZMod 2) :=
          (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans eLS)
        refine ⟨KSubT.catalogIs_mono (fun i hi => Or.inr (Or.inl hi)) (catalogIs_sp6_of_equiv eQ),
          fun hA6 => ?_⟩
        exfalso
        have h360 := card_of_catalogIs_alt6 hA6
        have hcard := Nat.card_congr eQ.toEquiv
        rw [CFSG.Sporadic.Schreier.Co3.card_statedSp_three_two] at hcard
        omega
  ·
    have hcompA1 := isComponentOf_of_le_factor hLC' hLA₁
    obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
    have hK1 : CFSG.Open.IsComponentOf (L.subgroupOf A₁) ⊤ := isComponentOf_top_subgroupOf hcompA1
    have hK2 := isComponentOf_map_mulEquiv hK1 eA1
    rw [Subgroup.map_top_of_surjective _ eA1.surjective] at hK2
    have hGU := GU E hE W Hf hsymm hsep
    rcases (by omega : m ≤ 3 ∨ m = 4) with hm | hm
    ·
      exfalso
      exact not_comp_top_of_solvable (hGU.1 (by rw [hfr]; omega)) hK2
    · obtain ⟨hcat, hcard, hcen⟩ := hGU.2 (by rw [hfr]; exact hm) _ hK2
      let K2 : Subgroup (sesqUnitaryGroup Hf) := (L.subgroupOf A₁).map eA1.toMonoidHom
      let eLK2 : ↥L ≃* ↥K2 :=
        (Subgroup.subgroupOfEquivOfLe hLA₁).symm.trans
          (Subgroup.equivMapOfInjective (L.subgroupOf A₁) eA1.toMonoidHom eA1.injective)
      let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥K2 ⧸ Subgroup.center ↥K2) :=
        QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥K2) eLK2
          (Subgroup.map_center_eq eLK2)
      refine ⟨KSubT.catalogIs_mono (fun i hi => Or.inl hi) (catalogIs_of_mulEquiv eQ.symm hcat),
        fun hA6 => ?_⟩
      exfalso
      have h360 := card_of_catalogIs_alt6 hA6
      have hc1 := Nat.card_congr eQ.toEquiv
      have hcen' : Subgroup.center ↥K2 = ⊥ := hcen
      have hcard' : Nat.card ↥K2 = 25920 := hcard
      have hc2 := Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcen' |>.trans
        QuotientGroup.quotientBot).toEquiv
      omega

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
