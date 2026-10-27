module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3EngA
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Facts

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem fStarSimple_subgroupOf (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {G₁ : Subgroup H} (hNG : N ≤ G₁) :
    FStarSimple (N.subgroupOf G₁) ∧ (N.subgroupOf G₁).index ≤ 2 ∧
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥G₁ ∧ Nonempty (↥(N.subgroupOf G₁) ≃* ↥N) := by
  have := hN.normal
  let N' : Subgroup ↥G₁ := N.subgroupOf G₁
  have hNe : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNG
  have hN'simple : IsSimpleGroup ↥N' := by
    have := hN.isSimpleGroup
    exact MulEquiv.isSimpleGroup hNe
  have hna : ∃ a b : ↥N', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact ⟨hNe.symm a, hNe.symm b, fun h => hab (hNe.symm.injective (by simpa [map_mul] using h))⟩
  have hC : centralizer (N' : Set ↥G₁) ≤ N' := by
    intro x hx
    have hxC : (x : H) ∈ centralizer (N : Set H) := by
      rw [mem_centralizer_iff]
      intro n hn
      have := mem_centralizer_iff.1 hx ⟨n, hNG hn⟩ hn
      exact congrArg Subtype.val this
    exact hN.centralizer_le hxC
  have hidx' : N'.index ≤ 2 := by
    have hdvd : N.relIndex G₁ ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N G₁
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd).trans hidx
  exact ⟨fStarSimple_of_normal_simple hN'simple hna hC, hidx',
    kProper_of_section hkp G₁ (MonoidHom.id ↥G₁) Function.surjective_id, ⟨hNe⟩⟩

theorem type_max_v3 (pf : FiPinned) (rf : FiV3RowFacts) (lx : OddLieCompNotSporadic)
    (lit : Sol78Lit) (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {L₁ : Subgroup H} (hL₁L : InL L₁) (hL : IsLS [.Fi24Prime] ↥L₁) :
    Maximal L₁ ∧ ∃ S : Sylow 2 (centralizer (L₁ : Set H)), IsCyclic ↥S := by
  obtain ⟨s', hs', hq, hodd, hsp⟩ := hL
  obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hs'
  have ihS : BelowSec (Sol78PredS [.Fi24Prime]) H :=
    BelowSec.mono_types (by simp [fiTypes]) ih
  have hmax : Maximal L₁ :=
    maximal_of_central_type (Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered))
      ihS noUp_nil hN hidx hkp
      hL₁L (List.mem_singleton_self _) hsp pf.excl24 (fiEvenOut_fi24 pf []) pf.notExc24
  have hstd : StdBare L₁ :=
    stdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax (pf.rank24 ↥L₁ hq hsp)
  have hsol : SolStd L₁ := solStd_of_inL_of_stdBare hL₁L hstd
  exact ⟨hmax, cyclic_sylow_of_lit lit.toSol78LitCore lx hN hidx hkp hsol (by decide)
    ⟨hq, hodd, hsp⟩⟩

theorem not_max_v3 (pf : FiPinned) (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN24 : ¬ IsSporadic ↥N .Fi24Prime)
    {K₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsKFi23 K₁) {G₁ : Subgroup H} (hNG : N ≤ G₁)
    (hG : G₁ ≠ ⊤) : ¬ (K₁ ≤ G₁ ∧ Maximal (K₁.subgroupOf G₁)) := by
  rintro ⟨hKG, hmax⟩
  obtain ⟨hFS', hidx', hkp', ⟨hNe⟩⟩ := fStarSimple_subgroupOf hN hidx hkp hNG
  have hq₁ : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
  obtain ⟨f⟩ := klike_isSporadic_cq hq₁ hK₁
  let eK : ↥(K₁.subgroupOf G₁) ≃* ↥K₁ := Subgroup.subgroupOfEquivOfLe hKG
  have hq' : CFSG.IsQuasisimple ↥(K₁.subgroupOf G₁) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hq₁
  have hcq' : IsSporadic (↥(K₁.subgroupOf G₁) ⧸ center ↥(K₁.subgroupOf G₁)) .Fi23 :=
    ⟨(cqEquivOfMulEquiv eK).trans f⟩
  have hstd : StdBare (K₁.subgroupOf G₁) :=
    stdBare_of_maximal
      (lit.thm22 ↥G₁
        (ih.uHered.of_section (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup G₁)))
      hkp' hFS' hidx' hmax (pf.rank23 _ hq' hcq')
  have hsol : SolStd (K₁.subgroupOf G₁) := solStd_of_inL_of_stdBare hmax.1 hstd
  have hodd : Odd (Nat.card ↥(center ↥(K₁.subgroupOf G₁))) := by
    rw [pf.mult23 _ hq' hcq', Subgroup.card_bot]
    exact odd_one
  have hcard : Nat.card ↥G₁ < Nat.card H :=
    lt_of_le_of_ne (Subgroup.card_le_card_group G₁) fun h =>
      hG ((Subgroup.card_eq_iff_eq_top G₁).1 h)
  obtain ⟨-, ⟨g⟩⟩ := ih.apply (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup G₁) hcard
    (N.subgroupOf G₁) hFS' hidx' hkp' (K₁.subgroupOf G₁) hsol
    ⟨.Fi23, by simp [fiTypes], ⟨hq', hodd, hcq'⟩⟩
  exact hN24 ⟨hNe.symm.trans g⟩

theorem hyp31Core_of_rowFacts (pf : FiPinned) (rf : FiV3RowFacts) (lx : OddLieCompNotSporadic)
    (lit : Sol78Lit) (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hN24 : ¬ IsSporadic ↥N .Fi24Prime) : Hyp31Core H N IsKFi23 (IsLS [.Fi24Prime]) where
  fstar := hN
  index_le_two := hidx
  type_max := fun _ hL₁ hL => type_max_v3 pf rf lx lit ih hN hidx hkp hL₁ hL
  not_max := fun _ hK₁L hK₁ _ hNG hG => not_max_v3 pf lit ih hN hidx hkp hN24 hK₁L hK₁ hNG hG
  desc := fun _ _ hK₁L hK₁ hL₁L h =>
    desc_v3 pf (Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)) ih hN hidx hkp
      hK₁L hK₁ hL₁L h

theorem not_isSolvable_of_quasisimple {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  have : Group.IsPerfect Q := hQ.1
  have hsub : Subsingleton Q := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable Q hs
  obtain ⟨a, b, hab⟩ := hQ.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim a' b'])

theorem hyp31FourAL_of_rowFacts (pf : FiPinned) (rf : FiV3RowFacts)
    (hcore : Hyp31Core H N IsKFi23 (IsLS [.Fi24Prime])) :
    Hyp31FourAL H N IsKFi23 (IsLS [.Fi24Prime]) CanLocV3 where
  four_a := by
    rintro K₁ L₁ hK₁L hmax hL hlt hKL hK N₀ ⟨u, hu, rfl⟩
    have hq : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
    have hcq := isSporadic_cq_of_isKFi23 hq hK
    have hKs : IsSporadic ↥K₁ .Fi23 := isSporadic_of_center_eq_bot (pf.mult23 ↥K₁ hq hcq) hcq
    have hcov : OddCover .Fi24Prime L₁ := by
      obtain ⟨s', hs', hqL, hoddL, hspL⟩ := hL
      obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hs'
      exact ⟨hqL, hoddL, hspL⟩
    have hcyc := cyclic_sylow_all_of_exists (hcore.type_max L₁ hmax.1 hL).2
    have hΛs : Group.IsSolvable ↥(lam L₁ (K₁ ⊓ centralizer ({u} : Set H))) :=
      lam_isSolvable hcyc (rf.autSolv H L₁ K₁ u hcov hKL hKs hu)
    refine ⟨?_, fun K₂ _ _ hperf hiso => ?_⟩
    ·
      rintro ⟨A, f, hf⟩
      have hq₀ : CFSG.IsQuasisimple ↥(K₁ ⊓ centralizer ({u} : Set H)) :=
        (rf.transpositions H K₁ hKs).2 u hu
      have hAs : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective A.subtype_injective
      have hXs : Group.IsSolvable
          ↥(((K₁ ⊓ centralizer ({u} : Set H)).subgroupOf K₁).map
            (QuotientGroup.mk' (center ↥K₁))) := Group.isSolvable_of_surjective hf
      have hinj : Function.Injective (QuotientGroup.mk' (center ↥K₁)) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
          pf.mult23 ↥K₁ hq hcq]
      let e := Subgroup.equivMapOfInjective ((K₁ ⊓ centralizer ({u} : Set H)).subgroupOf K₁)
        (QuotientGroup.mk' (center ↥K₁)) hinj
      have h1 : Group.IsSolvable ↥((K₁ ⊓ centralizer ({u} : Set H)).subgroupOf K₁) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      let e' : ↥((K₁ ⊓ centralizer ({u} : Set H)).subgroupOf K₁) ≃*
          ↥(K₁ ⊓ centralizer ({u} : Set H)) := Subgroup.subgroupOfEquivOfLe inf_le_left
      have h2 : Group.IsSolvable ↥(K₁ ⊓ centralizer ({u} : Set H)) :=
        Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
      exact not_isSolvable_of_quasisimple hq₀ h2
    ·
      obtain ⟨e⟩ := hiso
      obtain ⟨f⟩ := hcq
      exact NoFixedEmbeds.of_nonsolvable
        (fun α h1 h2 => rf.fixed K₂ hperf ⟨e.trans f⟩ α h1 h2) hΛs

end CFSG.EvenSporadicStandard.Induction.Fi.V3
