module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import all CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JOneSolvPrimes
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SporBar

open CFSG.Open Subgroup

theorem isQuasisimple_of_isSimpleGroup_of_not_isSolvable {Q : Type*} [Group Q]
    (hs : IsSimpleGroup Q) (hn : ¬ Group.IsSolvable Q) : CFSG.IsQuasisimple Q := by
  have : IsSimpleGroup Q := hs
  have hnc : ¬ ∀ a b : Q, a * b = b * a := fun h => hn (isSolvable_of_comm h)
  have hZ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exact h
    · exact (hnc fun a b => (mem_center_iff.1 (h ▸ mem_top b) a)).elim
  have hC : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · refine (hnc fun a b => ?_).elim
      have hab : a * b * a⁻¹ * b⁻¹ ∈ commutator Q := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot] at hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hab, one_mul]
    · exact h
  refine CFSG.Quasithin.A3.isQuasisimple_iff_open.2 ⟨hC, ?_⟩
  have e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e

theorem le_sup_and_le_centralizer {Q : Type*} [Group Q] [Finite Q] {Y J J₂ : Subgroup Q}
    (hYn : Y.Normal) (hYs : IsSimpleGroup ↥Y) (hYns : ¬ Group.IsSolvable ↥Y) (hYJ : Y ≤ J)
    (hJ₂J : J₂ ≤ J) (hJ₂n : ∀ x ∈ J, ∀ t ∈ J₂, x * t * x⁻¹ ∈ J₂) (hJ₂p : IsPGroup 2 J₂)
    (hq : ∀ N : Subgroup Q, J₂ ≤ N → N ≤ J → (∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N = J ∨ ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ J₂) :
    J ≤ Y ⊔ J₂ ∧ J₂ ≤ centralizer (Y : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup ↥Y := hYs
  have hYJ₂ : Y ⊓ J₂ = ⊥ := by
    have hn : ((Y ⊓ J₂).subgroupOf Y).Normal := by
      refine ⟨fun z hz y => ?_⟩
      rw [mem_subgroupOf] at hz ⊢
      exact ⟨Y.mul_mem (Y.mul_mem y.2 hz.1) (Y.inv_mem y.2), hJ₂n _ (hYJ y.2) _ hz.2⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ J₂).subgroupOf Y) with h | h
    · rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hz.1⟩ : ↥Y) ∈ (Y ⊓ J₂).subgroupOf Y := mem_subgroupOf.2 hz
      rw [h, mem_bot] at hz'
      rw [mem_bot]
      exact congrArg Subtype.val hz'
    · exfalso
      apply hYns
      have hYp : IsPGroup 2 ↥Y := by
        intro y
        have hy : (y : Q) ∈ J₂ := by
          have h' : y ∈ (Y ⊓ J₂).subgroupOf Y := h ▸ mem_top y
          exact (mem_subgroupOf.1 h').2
        obtain ⟨k, hk⟩ := hJ₂p ⟨y, hy⟩
        refine ⟨k, Subtype.ext ?_⟩
        have h' := congrArg Subtype.val hk
        simpa using h'
      have : Group.IsNilpotent ↥Y := hYp.isNilpotent
      exact IsNilpotent.to_isSolvable
  have hcomm : ∀ t ∈ J₂, ∀ y ∈ Y, y * t = t * y := by
    intro t ht y hy
    have hc : t * y * t⁻¹ * y⁻¹ ∈ Y ⊓ J₂ := by
      refine ⟨Y.mul_mem (hYn.conj_mem y hy t) (Y.inv_mem hy), ?_⟩
      have h1 : y * t⁻¹ * y⁻¹ ∈ J₂ := hJ₂n y (hYJ hy) _ (J₂.inv_mem ht)
      have h2 : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
      rw [h2]
      exact J₂.mul_mem ht h1
    rw [hYJ₂, mem_bot] at hc
    calc y * t = (t * y * t⁻¹ * y⁻¹)⁻¹ * (t * y) := by group
      _ = t * y := by rw [hc, inv_one, one_mul]
  refine ⟨?_, fun t ht => mem_centralizer_iff.2 fun y hy => hcomm t ht y hy⟩
  have hNn : ∀ x ∈ J, ∀ n ∈ Y ⊔ J₂, x * n * x⁻¹ ∈ Y ⊔ J₂ := by
    intro x hx n hn
    have hle : Y ⊔ J₂ ≤ (Y ⊔ J₂).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun t ht => ?_)
      · exact mem_sup_left (by simpa using hYn.conj_mem y hy x)
      · exact mem_sup_right (by simpa using hJ₂n x hx t ht)
    simpa using hle hn
  rcases hq (Y ⊔ J₂) le_sup_right (sup_le hYJ hJ₂J) hNn with h | h
  · exact h.ge
  · exfalso
    apply hYns
    refine isSolvable_of_comm fun a b => ?_
    have hc : (a : Q) * b * (a : Q)⁻¹ * (b : Q)⁻¹ ∈ Y ⊓ J₂ :=
      ⟨Y.mul_mem (Y.mul_mem (Y.mul_mem a.2 b.2) (Y.inv_mem a.2)) (Y.inv_mem b.2),
        h a (hYJ a.2) b (mem_sup_left b.2)⟩
    rw [hYJ₂, mem_bot] at hc
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (a : Q) * b = ((a : Q) * b * (a : Q)⁻¹ * (b : Q)⁻¹) * (b * a) := by group
      _ = b * a := by rw [hc, one_mul]

theorem eq_range_or_commutator_mem {J Q : Type*} [Group J] [Group Q] (f : J →* Q)
    (K₂ : Subgroup J) [K₂.Normal] (hq : CFSG.IsQuasisimple (J ⧸ K₂)) (N : Subgroup Q)
    (h₂N : K₂.map f ≤ N) (hNJ : N ≤ f.range)
    (hNn : ∀ x ∈ f.range, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    N = f.range ∨ ∀ x ∈ f.range, ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ K₂.map f := by
  have hN'n : (N.comap f).Normal := ⟨fun n hn j => by
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact hNn (f j) ⟨j, rfl⟩ (f n) hn⟩
  have hÑ : ((N.comap f).map (QuotientGroup.mk' K₂)).Normal :=
    hN'n.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hÑ with htop | hcen
  · left
    refine le_antisymm hNJ ?_
    rintro _ ⟨j, rfl⟩
    have hj : QuotientGroup.mk' K₂ j ∈ (N.comap f).map (QuotientGroup.mk' K₂) := htop ▸ mem_top _
    obtain ⟨n', hn', hnj⟩ := hj
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnj
    have hfj : f j = f n' * f (n'⁻¹ * j) := by rw [← map_mul, mul_inv_cancel_left]
    rw [hfj]
    exact N.mul_mem hn' (h₂N ⟨_, hnj, rfl⟩)
  · right
    rintro _ ⟨j, rfl⟩ n hn
    obtain ⟨n'', rfl⟩ := hNJ hn
    have hc : QuotientGroup.mk' K₂ n'' ∈ center (J ⧸ K₂) := hcen ⟨n'', hn, rfl⟩
    have hcomm : QuotientGroup.mk' K₂ (j * n'' * j⁻¹ * n''⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mem_center_iff.1 hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomm
    exact ⟨_, hcomm, by rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩

theorem center_eq_bot_of_isSimpleGroup_of_not_isSolvable {Q : Type*} [Group Q]
    (hs : IsSimpleGroup Q) (hn : ¬ Group.IsSolvable Q) : center Q = ⊥ := by
  have : IsSimpleGroup Q := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exact (hn (isSolvable_of_comm fun a b => (mem_center_iff.1 (h ▸ mem_top b) a))).elim

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPPrimeHull_subgroupOf_normal (d : ℕ) (B : Subgroup G) :
    ((CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull d B).subgroupOf B).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hle : CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull d B ≤
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull d B).comap
        (MulAut.conj (g : G)).toMonoidHom := by
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨hxB, k, hk⟩ := hx
    refine subset_closure ⟨?_, k, ?_⟩
    · exact B.mul_mem (B.mul_mem g.2 hxB) (B.inv_mem g.2)
    · rw [← hk]
      exact orderOf_injective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective x
  simpa using hle hn

omit [Finite G] in
theorem nonempty_modPrimeComplement_mulEquiv {d : ℕ} {B X Y : Subgroup G} (hYB : Y ≤ B)
    [(X.subgroupOf B).Normal]
    (hO : (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d).map
      Y.subtype ≤ X)
    (hXd : ¬ d ∣ Nat.card X) :
    Nonempty (modPrimeComplement d Y ≃*
      ↥((Y.subgroupOf B).map (QuotientGroup.mk' (X.subgroupOf B)))) := by
  let φ : ↥Y →* ↥B ⧸ X.subgroupOf B :=
    (QuotientGroup.mk' (X.subgroupOf B)).comp (Subgroup.inclusion hYB)
  have hmem : ∀ y : ↥Y, y ∈ φ.ker ↔ (y : G) ∈ X := by
    intro y
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' (X.subgroupOf B)) (Subgroup.inclusion hYB y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have hrange : φ.range = (Y.subgroupOf B).map (QuotientGroup.mk' (X.subgroupOf B)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d =
      φ.ker := by
    refine le_antisymm (fun y hy => (hmem y).2 (hO ⟨y, hy, rfl⟩)) ?_
    refine CFSG.RankThreeEvenClassification.Helpers.le_primeComplementCore d φ.ker
      φ.normal_ker fun hdvd => hXd (hdvd.trans ?_)
    rw [← card_map_of_injective Y.subtype_injective]
    refine card_dvd_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y).1 hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

section Spor

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {M : Subgroup G} {p : ℕ} {H : Subgroup G} {d : ℕ}

omit [Finite G] in
theorem xSub_subgroupOf_inf_normal (hXn : ((xSub p M H).subgroupOf H).Normal) :
    ((xSub p M H).subgroupOf (H ⊓ M)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have h := hXn.conj_mem ⟨n, n.2.1⟩ (mem_subgroupOf.2 hn) ⟨g, g.2.1⟩
  rw [mem_subgroupOf] at h
  exact h

omit [Finite G] in
private theorem card_eq_of_isSimpleOfOrder {n : ℕ} {X : Type} [Group X]
    (h : IsSimpleOfOrder n X) : Nat.card X = n :=
  (show IsSimpleGroup X ∧ ¬ Group.IsSolvable X ∧ Nat.card X = n from h).2.2

omit [Finite G] in
theorem card_modPrimeComplement_of_caseSpor (hs : TwelveThreeCaseSpor M p H d) :
    Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) = 5616 ∨
      Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) = 126000 ∨
      Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) = 5859000000 ∨
      Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) = 1876896 ∨
      Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) = 4030387200 := by
  rcases hs.2.2.1 with ⟨-, -, -, ⟨e⟩⟩ | ⟨-, ⟨-, -, h⟩ | ⟨-, -, h⟩⟩ | ⟨-, ⟨-, -, ⟨e⟩⟩ | ⟨-, -, h⟩⟩
  · left
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_congr e.toEquiv]
    have h := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA (ZMod 3) 2
    rw [Nat.card_zmod] at h
    exact h.trans (by decide)
  · exact Or.inr (Or.inl (card_eq_of_isSimpleOfOrder h))
  · exact Or.inr (Or.inr (Or.inl (card_eq_of_isSimpleOfOrder h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [Nat.card_congr e.toEquiv]
    have h := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA (ZMod 7) 2
    rw [Nat.card_zmod] at h
    exact h.trans (by decide)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (card_eq_of_isSimpleOfOrder h))))

end Spor

section Members

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {M : Subgroup G} {p : ℕ} {H : Subgroup G}

noncomputable abbrev barX (p : ℕ) (M H : Subgroup G) [((xSub p M H).subgroupOf (H ⊓ M)).Normal]
    (A : Subgroup G) : Subgroup (↥(H ⊓ M) ⧸ (xSub p M H).subgroupOf (H ⊓ M)) :=
  (A.subgroupOf (H ⊓ M)).map (QuotientGroup.mk' ((xSub p M H).subgroupOf (H ⊓ M)))

variable [((xSub p M H).subgroupOf (H ⊓ M)).Normal]

omit [Finite G] in
theorem barX_oPPrimeHull_normal (d : ℕ) : (barX p M H (oPPrimeHull d (H ⊓ M))).Normal :=
  (oPPrimeHull_subgroupOf_normal d (H ⊓ M)).map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem oPPrimeHull_le (d : ℕ) (B : Subgroup G) : oPPrimeHull d B ≤ B :=
  (closure_le _).2 fun _ hx => hx.1

theorem nonempty_mulEquiv_barX {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) :
    Nonempty (modPrimeComplement d (oPPrimeHull d (H ⊓ M)) ≃*
      ↥(barX p M H (oPPrimeHull d (H ⊓ M)))) :=
  nonempty_modPrimeComplement_mulEquiv (oPPrimeHull_le d (H ⊓ M)) hs.2.2.2.1
    hdat.common.xSub_dPrime

theorem isSimpleGroup_barX {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) :
    IsSimpleGroup ↥(barX p M H (oPPrimeHull d (H ⊓ M))) ∧
      ¬ Group.IsSolvable ↥(barX p M H (oPPrimeHull d (H ⊓ M))) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_barX hdat hs
  have : IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := hdat.common.y_simple
  refine ⟨MulEquiv.isSimpleGroup e.symm, fun hsol => hdat.common.y_nonsolvable ?_⟩
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

omit [Finite G] [((xSub p M H).subgroupOf (H ⊓ M)).Normal] in
theorem isSubnormal_inf_of_mem_weakBlockSet {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    H ⊓ L ≤ H ⊓ M ∧ IsSubnormal (H ⊓ L) (H ⊓ M) := by
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hLM : IsSubnormal L M := hL'.subnormal
  refine ⟨inf_le_inf le_rfl hLM.le, ?_⟩
  have h := hLM.inf H
  rwa [inf_comm L H, inf_comm M H] at h

omit [Finite G] in
theorem isSubnormal_barX_of_isSubnormal {I : Subgroup G} (hIB : I ≤ H ⊓ M)
    (hI : IsSubnormal I (H ⊓ M)) : (barX p M H I).IsSubnormal :=
  ((IsSubnormal.iff_subgroupOf hIB).1 hI).map (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem isSubnormal_barX_of_mem_cZero {L I : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (hI : I ∈ cZero (H ⊓ L)) : I ≤ H ⊓ M ∧ (barX p M H I).IsSubnormal := by
  obtain ⟨hle, hHLM⟩ := isSubnormal_inf_of_mem_weakBlockSet hL
  have hI' : IsCZeroMember (H ⊓ L) I := hI
  have hIle : I ≤ H ⊓ M := hI'.le.trans hle
  exact ⟨hIle, isSubnormal_barX_of_isSubnormal hIle (hI'.subnormal.trans hHLM)⟩

theorem le_or_commutator_eq_bot_of_isSubnormal {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {I : Subgroup G} (hI : (barX p M H I).IsSubnormal) :
    barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H I ∨
      ⁅barX p M H (oPPrimeHull d (H ⊓ M)), barX p M H I⁆ = ⊥ := by
  obtain ⟨hYs, hYns⟩ := isSimpleGroup_barX hdat hs
  have hcomp : CFSG.IsComponent (barX p M H (oPPrimeHull d (H ⊓ M))) :=
    ⟨isQuasisimple_of_isSimpleGroup_of_not_isSolvable hYs hYns,
      (barX_oPPrimeHull_normal d).isSubnormal⟩
  exact CFSG.LocalCores.component_subnormal_subgroup hcomp hI

theorem le_or_commutator_eq_bot {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {L I : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (hI : I ∈ cZero (H ⊓ L)) :
    barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H I ∨
      ⁅barX p M H (oPPrimeHull d (H ⊓ M)), barX p M H I⁆ = ⊥ :=
  le_or_commutator_eq_bot_of_isSubnormal hdat hs (isSubnormal_barX_of_mem_cZero hL hI).2

omit [Finite G] in
theorem commutator_mem_xSub_of_commutator_eq_bot {d : ℕ} {I : Subgroup G} (hIB : I ≤ H ⊓ M)
    (h : ⁅barX p M H (oPPrimeHull d (H ⊓ M)), barX p M H I⁆ = ⊥) :
    ∀ x ∈ I, ∀ y ∈ oPPrimeHull d (H ⊓ M), x * y * x⁻¹ * y⁻¹ ∈ xSub p M H := by
  intro x hx y hy
  set ρ := QuotientGroup.mk' ((xSub p M H).subgroupOf (H ⊓ M)) with hρ
  let x' : ↥(H ⊓ M) := ⟨x, hIB hx⟩
  let y' : ↥(H ⊓ M) := ⟨y, oPPrimeHull_le d (H ⊓ M) hy⟩
  have hxq : ρ x' ∈ barX p M H I := mem_map_of_mem ρ (mem_subgroupOf.2 hx)
  have hyq : ρ y' ∈ barX p M H (oPPrimeHull d (H ⊓ M)) := mem_map_of_mem ρ (mem_subgroupOf.2 hy)
  have hc := Subgroup.commutator_mem_commutator hyq hxq
  rw [h, mem_bot] at hc
  have hc' : ρ (y' * x' * y'⁻¹ * x'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hc
  rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hc'
  have hinv := (xSub p M H).inv_mem hc'
  have heq : ((y' * x' * y'⁻¹ * x'⁻¹ : ↥(H ⊓ M)) : G)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    simp only [x', y', Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
  rw [heq] at hinv
  exact hinv

end Members

section Big

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {M : Subgroup G} {p : ℕ} {H : Subgroup G} [((xSub p M H).subgroupOf (H ⊓ M)).Normal]

omit [Finite G] [((xSub p M H).subgroupOf (H ⊓ M)).Normal] in
theorem exists_prime_dvd_card_modPrimeComplement {d : ℕ} (hs : TwelveThreeCaseSpor M p H d) :
    ∃ q, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := by
  rcases card_modPrimeComplement_of_caseSpor hs with h | h | h | h | h <;> rw [h]
  · exact ⟨13, by norm_num, by norm_num, by norm_num⟩
  all_goals exact ⟨7, by norm_num, by norm_num, by norm_num⟩

theorem false_of_le_of_primes {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {I : Subgroup G} (hIB : I ≤ H ⊓ M)
    (hpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card I → r = 2 ∨ r = 3)
    (hle : barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H I) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_barX hdat hs
  obtain ⟨q, hq, hq5, hqd⟩ := exists_prime_dvd_card_modPrimeComplement hs
  have h1 : q ∣ Nat.card (barX p M H (oPPrimeHull d (H ⊓ M))) := by
    rwa [← Nat.card_congr e.toEquiv]
  have h2 := card_dvd_of_le hle
  have h3 : Nat.card (barX p M H I) ∣ Nat.card (I.subgroupOf (H ⊓ M)) := card_map_dvd _ _
  have h4 : Nat.card (I.subgroupOf (H ⊓ M)) = Nat.card I :=
    Nat.card_congr (subgroupOfEquivOfLe hIB).toEquiv
  rcases hpr q hq (by rw [← h4]; exact h1.trans (h2.trans h3)) with h | h <;> omega

theorem false_of_le_of_symThree {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {I : Subgroup G} (hIB : I ≤ H ⊓ M)
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I))
    (hle : barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H I) : False :=
  false_of_le_of_primes hdat hs hIB (fun _ hr hrI =>
    CFSG.LocalAnalysis.RankThreeTheoremC.prime_eq_of_dvd_card_of_symThree hb hr hrI) hle

end Big

section BigPerfect

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {M : Subgroup G} {p : ℕ} {H : Subgroup G} [((xSub p M H).subgroupOf (H ⊓ M)).Normal]

omit [Finite G] in
private theorem isQuasisimple_quotient_of_isTwoPrimeComponent_self {I : Subgroup G}
    (h : IsTwoPrimeComponent I I) : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) := by
  have h1 := h.component.2.2
  have htop : barM I I = ⊤ := by
    unfold barM
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
  rw [htop] at h1
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.2
    (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm h1)

omit [Finite G] in
theorem barX_mono {A A' : Subgroup G} (h : A ≤ A') : barX p M H A ≤ barX p M H A' :=
  map_mono fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx))

theorem barX_le_sup_centralizer {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {J : Subgroup G} (hJB : J ≤ H ⊓ M)
    (hJ : IsTwoPrimeComponent J J) (hle : barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H J) :
    barX p M H J ≤ barX p M H (oPPrimeHull d (H ⊓ M)) ⊔
      centralizer (barX p M H (oPPrimeHull d (H ⊓ M)) : Set _) := by
  obtain ⟨hYs, hYns⟩ := isSimpleGroup_barX hdat hs
  let f : ↥J →* ↥(H ⊓ M) ⧸ (xSub p M H).subgroupOf (H ⊓ M) :=
    (QuotientGroup.mk' ((xSub p M H).subgroupOf (H ⊓ M))).comp (Subgroup.inclusion hJB)
  have hrange : f.range = barX p M H J := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hJ₂n : ∀ x ∈ f.range, ∀ t ∈ (CFSG.pCore 2 ↥J).map f,
      x * t * x⁻¹ ∈ (CFSG.pCore 2 ↥J).map f := by
    rintro _ ⟨j, rfl⟩ _ ⟨s, hs', rfl⟩
    refine ⟨j * s * j⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥J)).conj_mem s hs' j, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hYJ : barX p M H (oPPrimeHull d (H ⊓ M)) ≤ f.range := by
    rw [hrange]
    exact hle
  obtain ⟨h1, h2⟩ := le_sup_and_le_centralizer (barX_oPPrimeHull_normal d) hYs hYns hYJ
    (map_le_range f _) hJ₂n (CFSG.pCore_isPGroup.map f)
    (fun N h₂N hNJ hNn => eq_range_or_commutator_mem f (CFSG.pCore 2 ↥J)
      (isQuasisimple_quotient_of_isTwoPrimeComponent_self hJ) N h₂N hNJ hNn)
  rw [← hrange]
  exact h1.trans (sup_le_sup_left h2 _)

theorem exists_perfect_surj_of_le {d : ℕ} (hdat : TwelveThreeData M p H d)
    (hs : TwelveThreeCaseSpor M p H d) {L I : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (hI : I ∈ cZero (H ⊓ L)) (hle : barX p M H (oPPrimeHull d (H ⊓ M)) ≤ barX p M H I) :
    ∃ V : Subgroup G, V ≤ H ⊓ L ∧ H ⊓ L ≤ normalizer (V : Set G) ∧ ⁅V, V⁆ = V ∧
      ∃ ψ : ↥V →* ↥(barX p M H (oPPrimeHull d (H ⊓ M))), Function.Surjective ψ := by
  classical
  obtain ⟨hYs, hYns⟩ := isSimpleGroup_barX hdat hs
  have hYn := barX_oPPrimeHull_normal (p := p) (M := M) (H := H) d
  set Yq := barX p M H (oPPrimeHull d (H ⊓ M)) with hYq
  set ρ := QuotientGroup.mk' ((xSub p M H).subgroupOf (H ⊓ M)) with hρ
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hHLB : H ⊓ L ≤ H ⊓ M := inf_le_inf le_rfl hL'.le
  let 𝒥 : Set (Subgroup G) := {J | J ∈ cZero (H ⊓ L) ∧ Yq ≤ barX p M H J}
  have hJB : ∀ J ∈ 𝒥, J ≤ H ⊓ M := fun J hJ => (isSubnormal_barX_of_mem_cZero (p := p) hL hJ.1).1
  have hJshape : ∀ J ∈ 𝒥, IsTwoPrimeComponent J J := fun J hJ =>
    (show IsCZeroMember (H ⊓ L) J from hJ.1).shape.resolve_right fun h =>
      false_of_le_of_symThree hdat hs (hJB J hJ) h.2 hJ.2
  let V : Subgroup G := ⨆ J ∈ 𝒥, J
  have hJV : ∀ J ∈ 𝒥, J ≤ V := fun J hJ => le_iSup₂ (f := fun J (_ : J ∈ 𝒥) => J) J hJ
  have hVHL : V ≤ H ⊓ L := iSup₂_le fun J hJ => (show IsCZeroMember (H ⊓ L) J from hJ.1).le
  have hVB : V ≤ H ⊓ M := hVHL.trans hHLB
  refine ⟨V, hVHL, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.le_normalizer_iff]
    intro b hb v hv
    have hle' : V ≤ V.comap (MulAut.conj b).toMonoidHom := by
      refine iSup₂_le fun J hJ => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      refine hJV _ ⟨(show IsCZeroMember (H ⊓ L) J from hJ.1).map_conj (le_normalizer hb), ?_⟩
      intro y hy
      let b' : ↥(H ⊓ M) := ⟨b, hHLB hb⟩
      have hy0 : (ρ b')⁻¹ * y * (ρ b')⁻¹⁻¹ ∈ Yq := hYn.conj_mem y hy (ρ b')⁻¹
      obtain ⟨j', hj', hj'y⟩ := hJ.2 hy0
      refine ⟨b' * j' * b'⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        exact ⟨j', mem_subgroupOf.1 hj', by simp [b', MulAut.conj_apply]⟩
      · rw [map_mul, map_mul, map_inv, hj'y, ← hρ]
        group
    simpa [MulAut.conj_apply] using hle' hv
  ·
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (iSup₂_le fun J hJ => ?_)
    · exact V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb)
    · calc J = ⁅J, J⁆ := (hJshape J hJ).perfect.symm
        _ ≤ ⁅V, V⁆ := Subgroup.commutator_mono (hJV J hJ) (hJV J hJ)
  ·
    let β : ↥(H ⊓ M) →* MulAut ↥Yq := (MulAut.conjNormal (H := Yq)).comp ρ
    let α : ↥V →* MulAut ↥Yq := β.comp (Subgroup.inclusion hVB)
    let Inn : Subgroup (MulAut ↥Yq) := (MulAut.conj : ↥Yq →* MulAut ↥Yq).range
    have hInn : Yq ⊔ centralizer (Yq : Set _) ≤ Inn.comap (MulAut.conjNormal (H := Yq)) := by
      refine sup_le (fun y hy => ⟨⟨y, hy⟩, ?_⟩) (fun c hc => ?_)
      · ext z
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      · rw [mem_comap]
        have h1 : MulAut.conjNormal (H := Yq) c = 1 := by
          ext z
          rw [MulAut.conjNormal_apply, MulAut.one_apply, (mem_centralizer_iff.1 hc z z.2).symm,
            mul_inv_cancel_right]
        rw [h1]
        exact one_mem _
    have hαle : ∀ v : ↥V, α v ∈ Inn := by
      have hVT : V ≤ (Inn.comap β).map (H ⊓ M).subtype := by
        refine iSup₂_le fun J hJ j hj => ⟨⟨j, hJB J hJ hj⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_comap]
        exact hInn (barX_le_sup_centralizer hdat hs (hJB J hJ) (hJshape J hJ) hJ.2
          ⟨⟨j, hJB J hJ hj⟩, mem_subgroupOf.2 hj, rfl⟩)
      intro v
      obtain ⟨w, hw, hwv⟩ := hVT v.2
      have hvw : Subgroup.inclusion hVB v = w := Subtype.ext hwv.symm
      show β (Subgroup.inclusion hVB v) ∈ Inn
      rw [hvw]
      exact hw
    have hrange : α.range = Inn := by
      refine le_antisymm (by rintro _ ⟨v, rfl⟩; exact hαle v) ?_
      rintro _ ⟨y, rfl⟩
      obtain ⟨w, hw, hwy⟩ := barX_mono (hJV I ⟨hI, hle⟩) (hle y.2)
      rw [← hρ] at hwy
      refine ⟨⟨w, mem_subgroupOf.1 hw⟩, ?_⟩
      have hw' : Subgroup.inclusion hVB ⟨(w : G), mem_subgroupOf.1 hw⟩ = w := Subtype.ext rfl
      ext z
      simp only [α, β, MonoidHom.comp_apply, hw', hwy, MulAut.conjNormal_apply, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_inv]
    have hZ : center ↥Yq = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_isSolvable hYs hYns
    have hinj : Function.Injective (MulAut.conj : ↥Yq →* MulAut ↥Yq) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hac : a ∈ center ↥Yq := mem_center_iff.2 fun g => by
        have h1 := congrArg (fun φ : MulAut ↥Yq => φ g) ha
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * a = (a * g * a⁻¹) * a := by rw [h1]
          _ = a * g := by group
      rw [hZ, mem_bot] at hac
      exact hac
    let e₁ : ↥α.range ≃* ↥Inn := MulEquiv.subgroupCongr hrange
    let e₂ : ↥Yq ≃* ↥Inn := MonoidHom.ofInjective hinj
    exact ⟨(e₂.symm.toMonoidHom.comp e₁.toMonoidHom).comp α.rangeRestrict,
      (e₂.symm.surjective.comp e₁.surjective).comp α.rangeRestrict_surjective⟩

end BigPerfect

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SporBar
