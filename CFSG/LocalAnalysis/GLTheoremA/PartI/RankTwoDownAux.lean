module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem rtd_fixSubgroup_one {K : Type*} [Group K] : fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem rtd_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

theorem rtd_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem rtd_nonempty_pSimple_equiv_top {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a) {I : Subgroup T}
    (hI : GLAPComponent p (⊤ : Subgroup T) I) : Nonempty (PSimple p I ≃* T) := by
  have hIeq : I = ⊤ := by
    rcases rtd_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIeq
  have hq : CFSG.Open.IsQuasisimple (PQuot p (⊤ : Subgroup T)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T)) := by
    haveI : Nontrivial (PQuot p (⊤ : Subgroup T) ⧸ Subgroup.center (PQuot p (⊤ : Subgroup T))) :=
      hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (PQuot p (⊤ : Subgroup T)))).nontrivial
  have hOb : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊥ := by
    let ψ : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
    haveI : ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p _) ψ.toMonoidHom ψ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
    · exfalso
      have htop : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊤ := by
        apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
        rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T))
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
  have hZtop : Subgroup.center ↥(⊤ : Subgroup T) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
    rw [rtd_center_eq_bot hnc] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  let e1 : PQuot p (⊤ : Subgroup T) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hOb).trans QuotientGroup.quotientBot
  let e2 : PSimple p (⊤ : Subgroup T) ≃*
      (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  let e3 : (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans QuotientGroup.quotientBot
  exact ⟨e2.trans (e3.trans Subgroup.topEquiv)⟩

theorem rtd_nonempty_pSimple_equiv_of_simple {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {X : Subgroup S} [IsSimpleGroup ↥X] (hnc : ∃ a b : ↥X, a * b ≠ b * a) {I : Subgroup S}
    (hI : GLAPComponent p X I) : Nonempty (PSimple p I ≃* ↥X) := by
  have hI' : GLAPComponent p (⊤ : Subgroup ↥X) (I.subgroupOf X) := by
    have h := glaPComponent_subgroupOf hp (le_refl X) hI
    rwa [Subgroup.subgroupOf_self] at h
  obtain ⟨f⟩ := rtd_nonempty_pSimple_equiv_top hp hnc hI'
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hI.1
  exact ⟨(QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)).symm.trans f⟩

theorem rtd_eq_bot_of_perfect_of_solvable {Y : Type*} [Group Y] {J S : Subgroup Y}
    (hS : Group.IsSolvable ↥S) (hJS : J ≤ S) (hperf : ⁅J, J⁆ = J) : J = ⊥ := by
  by_contra hne
  have hJ'ne : J.subgroupOf S ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJS, h0, Subgroup.map_bot]
  have hlt : ⁅J.subgroupOf S, J.subgroupOf S⁆ < J.subgroupOf S :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅J.subgroupOf S, J.subgroupOf S⁆ = J.subgroupOf S := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJS]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem rtd_false_of_component_of_solvable {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    {F S J : Subgroup Y} (hS : Group.IsSolvable ↥S) (hFS : ⁅F, F⁆ ≤ S)
    (hJ : GLAPComponent p F J) : False := by
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJS : J ≤ S := by
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hJ.1 hJ.1
      _ ≤ S := hFS
  exact glaPComponent_ne_bot' hJ (rtd_eq_bot_of_perfect_of_solvable hS hJS hperf)

theorem rtd_commutator_le_self {Y : Type*} [Group Y] (F : Subgroup Y) : ⁅F, F⁆ ≤ F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem rtd_coprime_three_of_sq {G : Type*} [Group G] [Finite G]
    (hZ : ∀ z ∈ Subgroup.center G, z ^ 2 = 1) :
    Nat.Coprime 3 (Nat.card (Subgroup.center G)) := by
  have hp : IsPGroup 2 ↥(Subgroup.center G) := by
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_one] using hZ z z.2
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem rtd_nonempty_pSimple_equiv_quasisimple {Y : Type} [Group Y] [Finite Y] {X J : Subgroup Y}
    (hJ : GLAPComponent 3 X J) {G : Type} [Group G] (eJ : G ≃* J)
    (hG : CFSG.Open.IsQuasisimple G) (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center G))) :
    Nonempty (PSimple 3 J ≃* G ⧸ Subgroup.center G) := by
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open_of_mulEquiv eJ.symm hG
  have hnt : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro htop
    have e := QuotientGroup.quotientMulEquivOfEq htop
    haveI : Subsingleton (↥J ⧸ (⊤ : Subgroup ↥J)) := QuotientGroup.subsingleton_quotient_top
    have hsub : Subsingleton (PQuot 3 J) := e.toEquiv.subsingleton
    have hntriv : Nontrivial (PQuot 3 J) := by
      have := hQ.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 J))).nontrivial
    exact not_subsingleton _ hsub
  have hZJ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥J)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eJ).toEquiv]
    exact hZ
  have hP1 : GLAPPrimeCore 3 ↥J = Subgroup.center ↥J :=
    le_antisymm (le_center_of_normal_of_isQuasisimple hJq inferInstance hnt)
      (CFSG.le_pPrimeCore_of_normal_coprime inferInstance hZJ)
  let e1 : PQuot 3 J ≃* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.quotientMulEquivOfEq hP1
  let e2 : (↥J ⧸ Subgroup.center ↥J) ≃* G ⧸ Subgroup.center G :=
    QuotientGroup.congr _ _ eJ.symm (Subgroup.map_center_eq eJ.symm)
  let e12 : PQuot 3 J ≃* G ⧸ Subgroup.center G := e1.trans e2
  have hperf : Group.IsPerfect G := (Group.isPerfect_def).2 hG.1
  have hc : Subgroup.center (PQuot 3 J) = ⊥ := by
    have h1 := Subgroup.map_center_eq e12
    rw [Group.IsPerfect.center_quotient_center_eq_bot G] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e12.injective).1 h1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e12⟩

theorem rtd_exists_pSimple_equiv_map {S S' : Type} [Group S] [Group S'] [Finite S] {p : ℕ}
    (hp : p.Prime) (e : S ≃* S') (α : MulAut S) {I : Subgroup S}
    (hI : GLAPComponent p (fixSubgroup α) I) :
    GLAPComponent p (fixSubgroup (MulAut.congr e α)) (I.map e.toMonoidHom) ∧
      Nonempty (PSimple p I ≃* PSimple p (I.map e.toMonoidHom)) := by
  haveI : Finite S' := Finite.of_equiv S e.toEquiv
  have hfix : fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
    ext y'
    rw [Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨e.symm y', ?_, by simp⟩
      rw [mem_fixSubgroup]
      apply e.injective
      have h' := mem_fixSubgroup.1 h
      rw [MulAut.congr_apply] at h'
      simpa using h'
    · rintro ⟨y, hy, rfl⟩
      rw [mem_fixSubgroup, MulAut.congr_apply]
      simp [mem_fixSubgroup.1 hy]
  refine ⟨?_, ?_⟩
  · rw [hfix]
    refine glaPComponent_map hp e.toMonoidHom ?_ hI
    have : (e.toMonoidHom).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [this, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  · exact ⟨QuotientGroup.congr _ _
      (QuotientGroup.congr _ _ (I.equivMapOfInjective e.toMonoidHom e.injective)
        (glaPPrimeCore_map_iso p (I.equivMapOfInjective e.toMonoidHom e.injective)))
      (Subgroup.map_center_eq _)⟩

theorem rtd_kLevel_le_two {S : Type} [Group S] (h : catalogIs S (k2 3)) : kLevel 3 S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

theorem rtd_kLevel_le_three {S : Type} [Group S] (h : catalogIs S (k3 3)) : kLevel 3 S ≤ 3 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

end CFSG.LocalAnalysis.GLTheoremA
