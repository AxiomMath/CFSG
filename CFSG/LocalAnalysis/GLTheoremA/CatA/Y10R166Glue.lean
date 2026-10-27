module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F166
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.RankThree.PartOne.KF.ClsCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem trivialMultiplierT_of_lieModel (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hm : CFSG.Models.LieModel K t n 2 f)
    (h1 : Nat.card (CFSG.Blueprint.Multiplier.generic t n 2 f ×
      CFSG.Blueprint.Multiplier.exceptional t n 2 f) = 1) : TrivialMultiplierT K := by
  intro E _ _ hE π hπ hker
  obtain ⟨hK, hcard⟩ := CFSG.RankThree.PartOne.card_hopfMultiplier_of_model hGA hm
  have hE' : Group.IsPerfect E := ⟨hE⟩
  have hdvd := CFSG.RankThree.PartOne.card_ker_dvd_card_hopfMultiplier hK hE' π hπ hker
  rw [hcard, h1] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

section Certs


theorem largeEvenRawDatum_innSet_subset {lab : GLALabel} {Q : GLARawCont}
    (hlab : GLAInLambda2 lab) (h : GLARawDatum lab Q) :
    GLARawDatum lab fun R _ I F => Q R I F ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        CFSG.Assembly.LargeEvenInnSet R ⊆ I) := by
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_
    (CFSG.LocalAnalysis.GLTheoremA.MI.canonRawInn (p := 3) Nat.prime_three (by norm_num) hlab Q h)
  rintro R _ I F ⟨hQ, hRF⟩
  refine ⟨hQ, fun hs hna => ?_⟩
  rw [CFSG.Assembly.LargeEvenInnSet, Set.range_subset_iff]
  exact (hRF hs hna).2.2.1

end Certs

theorem glaInduces_conj_inv {L R : Type} [Group L] [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (j : L) :
    GLAInduces θ (fun l l' => l' = j⁻¹ * l * j)
      (MulAut.conj ((θ (QuotientGroup.mk j))⁻¹)) := by
  intro l l' hl
  subst hl
  rw [MulAut.conj_apply, inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, map_mul, map_mul, map_inv]

theorem exists_mul_zpow_eq_of_mem_sup_zpowers {K : Type} [Group K] {J : Subgroup K} {x : K}
    (hx : ∀ j ∈ J, j * x = x * j) {b : K} (hb : b ∈ J ⊔ Subgroup.zpowers x) :
    ∃ j ∈ J, ∃ k : ℤ, b = j * x ^ k := by
  let T : Subgroup K :=
    { carrier := {a | ∃ j ∈ J, ∃ k : ℤ, a = j * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨j₁, hj₁, k₁, rfl⟩ ⟨j₂, hj₂, k₂, rfl⟩
        have hc : x ^ k₁ * j₂ = j₂ * x ^ k₁ :=
          ((show Commute j₂ x from hx j₂ hj₂).zpow_right k₁).eq.symm
        refine ⟨j₁ * j₂, J.mul_mem hj₁ hj₂, k₁ + k₂, ?_⟩
        calc j₁ * x ^ k₁ * (j₂ * x ^ k₂) = j₁ * (x ^ k₁ * j₂) * x ^ k₂ := by group
          _ = j₁ * (j₂ * x ^ k₁) * x ^ k₂ := by rw [hc]
          _ = j₁ * j₂ * x ^ (k₁ + k₂) := by rw [zpow_add]; group
      one_mem' := ⟨1, J.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨j, hj, k, rfl⟩
        refine ⟨j⁻¹, J.inv_mem hj, -k, ?_⟩
        have hc0 : Commute (x ^ k) j⁻¹ :=
          ((show Commute j x from hx j hj).inv_left.zpow_right k).symm
        rw [mul_inv_rev, zpow_neg, hc0.inv_left.eq] }
  have hxT : x ∈ T := ⟨1, J.one_mem, 1, by simp⟩
  have hle : J ⊔ Subgroup.zpowers x ≤ T :=
    sup_le (fun j hj => ⟨j, hj, 0, by simp⟩) (Subgroup.zpowers_le.2 hxT)
  obtain ⟨j, hj, k, hk⟩ := hle hb
  exact ⟨j, hj, k, hk⟩

private theorem exists_conj_eq_of_mem_sup {K : Type} [Group K] {J : Subgroup K} {x b : K}
    (hxJ : J ≤ Subgroup.centralizer ({x} : Set K)) (hb : b ∈ J ⊔ Subgroup.zpowers x) :
    ∃ j ∈ J, ∀ l ∈ J, b⁻¹ * l * b = j⁻¹ * l * j := by
  have hx : ∀ j ∈ J, j * x = x * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hxJ hj)
  obtain ⟨j, hj, k, rfl⟩ := exists_mul_zpow_eq_of_mem_sup_zpowers hx hb
  refine ⟨j, hj, fun l hl => ?_⟩
  have hz : Commute (x ^ k) (j⁻¹ * l * j) :=
    (show Commute (j⁻¹ * l * j) x from
      Subgroup.mem_centralizer_singleton_iff.1
        (hxJ (J.mul_mem (J.mul_mem (J.inv_mem hj) hl) hj))).symm.zpow_left k
  calc (j * x ^ k)⁻¹ * l * (j * x ^ k)
      = (x ^ k)⁻¹ * (j⁻¹ * l * j) * x ^ k := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
    _ = j⁻¹ * l * j := by
        rw [mul_assoc, ← hz.eq, inv_mul_cancel_left]

section CertsMarking


theorem innerDiagMarking_of_le_sup {K : Type} [Group K] [Finite K] {B J : Subgroup K} {x : K}
    (hJ : HasLabel ↥J fun _ => True)
    (hxJ : J ≤ Subgroup.centralizer ({x} : Set K)) (hB : B ≤ J ⊔ Subgroup.zpowers x) :
    InnerDiagMarking B J := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hJ
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set K) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc : Commute (x ^ m) k :=
      (show Commute k x from Subgroup.mem_centralizer_singleton_iff.1 (hxJ hk)).symm.zpow_left m
    rw [show x ^ m * k * (x ^ m)⁻¹ = k by rw [hc.eq]; group]
    exact hk
  have hBN : B ≤ Subgroup.normalizer (J : Set K) :=
    hB.trans (sup_le Subgroup.le_normalizer hxN)
  have hraw' : GLARawDatum lab (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : ↥J ⧸ Subgroup.center ↥J ≃* R,
        B ≤ Subgroup.normalizer (J : Set K) ∧
          ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : K) = b⁻¹ * l * b) φ) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (Q' := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥J ⧸ Subgroup.center ↥J ≃* R, B ≤ Subgroup.normalizer (J : Set K) ∧
          ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : K) = b⁻¹ * l * b) φ) ?_
      (largeEvenRawDatum_innSet_subset hlab hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hinn⟩
    refine ⟨hs, hna, θ, ?_⟩
    refine ⟨hBN, ?_⟩
    intro b hb
    obtain ⟨j, hj, hjeq⟩ := exists_conj_eq_of_mem_sup hxJ (hB hb)
    refine ⟨MulAut.conj ((θ (QuotientGroup.mk (⟨j, hj⟩ : ↥J)))⁻¹), hinn hs hna ⟨_, rfl⟩, ?_⟩
    have hind := glaInduces_conj_inv θ (⟨j, hj⟩ : ↥J)
    intro l l' hl
    exact hind l l' (Subtype.ext (by rw [hl]; exact hjeq l l.2))
  exact ⟨hcomm, lab, hlab, hraw'⟩

end CertsMarking

theorem twoLocalRank_eq_of_normalizes {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {B S : Subgroup K} (hB : IsElemAbelian q B)
    (hc : Nat.card B = q ^ evenRank K) (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set K)) :
    GLATwoLocalRank q K = evenRank K := by
  have hloc : IsTwoLocal (Subgroup.normalizer (S : Set K)) := ⟨S, hS, hS2, rfl⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank q H = k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨H, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt H
  have hge : evenRank K ≤ GLATwoLocalRank q K :=
    (CFSG.SectionRank.le_pRank hq.one_lt hBS hB hc).trans
      (le_csSup hbdd ⟨_, hloc, rfl⟩)
  have hle : GLATwoLocalRank q K ≤ evenRank K := by
    refine csSup_le' ?_
    rintro k ⟨H, hH, rfl⟩
    refine le_csSup ?_ ⟨q, H, hq, hq2, hH, rfl⟩
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨p, H, hp, -, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt H
  exact le_antisymm hle hge

theorem isComponentOf_and_glaLayer_eq_of_commutator_mem {X : Type} [Group X] {C J : Subgroup X}
    (hJC : J ≤ C) (hcomm : ∀ g ∈ C, ∀ h ∈ C, g * h * g⁻¹ * h⁻¹ ∈ J)
    (hJ : CFSG.IsQuasisimple ↥J) :
    CFSG.Open.IsComponentOf J C ∧ GLALayer C = J := by
  have hJq : CFSG.Open.IsQuasisimple ↥J := ⟨hJ.1.commutator_eq_top, hJ.2.1⟩
  have hnormal : (J.subgroupOf C).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have h1 := hcomm g g.2 m m.2
    have e : ((g * m * g⁻¹ : ↥C) : X) = (g : X) * m * (g : X)⁻¹ * (m : X)⁻¹ * m := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact J.mul_mem h1 hm
  have hcomp : CFSG.Open.IsComponentOf J C :=
    ⟨hJC, CFSG.Open.IsSubnormal.step hJC hnormal (CFSG.Open.IsSubnormal.refl C), hJq⟩
  haveI : (J.subgroupOf C).Normal := hnormal
  have hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have h := hcomm (y⁻¹ : ↥C) (inv_mem y.2) (x⁻¹ : ↥C) (inv_mem x.2)
        have e : (((x * y)⁻¹ * (y * x) : ↥C) : X) =
            (y : X)⁻¹ * (x : X)⁻¹ * ((y : X)⁻¹)⁻¹ * ((x : X)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact h
  haveI : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := hsolv
  refine ⟨hcomp, le_antisymm ?_ (CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hcomp)⟩
  refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of fun L hL => ?_
  set π : ↥C →* (↥C ⧸ J.subgroupOf C) := QuotientGroup.mk' _
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hperf : Group.IsPerfect ↥(L.subgroupOf C) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hL.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL.1).symm.surjective
  have himg : Group.IsPerfect ↥(Subgroup.map π (L.subgroupOf C)) :=
    Group.IsPerfect.map (f := π)
  have hbot : Subgroup.map π (L.subgroupOf C) = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(Subgroup.map π (L.subgroupOf C)) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact (Group.IsPerfect.not_isSolvable ↥(Subgroup.map π (L.subgroupOf C))) inferInstance
  intro l hl
  have hπ : π (⟨l, hL.1 hl⟩ : ↥C) = 1 := by
    have hmem : π (⟨l, hL.1 hl⟩ : ↥C) ∈ Subgroup.map π (L.subgroupOf C) :=
      ⟨⟨l, hL.1 hl⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hπ)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
