module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Lemma21
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitX

public section

namespace CFSG.EvenSporadicStandard.HSStd.NoA8.Prop13

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

variable {H : Type} [Group H] [Finite H]

theorem not_normal_of_hsMinCex {A : Subgroup H}
    (hcex : HSMinCex H A) : ¬ A.Normal := by
  intro hn
  have hZ : center ↥A = ⊥ := center_eq_bot_of_isSporadic_hs hcex.sporadic
  obtain ⟨e⟩ := hcex.sporadic
  have hq : IsSporadic (↥A ⧸ center ↥A) .HS :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact hcex.notOutcome ⟨A, A, hn.isSubnormal, hn.isSubnormal, hq, hq, le_sup_left,
    by rwa [sup_idem]⟩

theorem eq_of_below {A M : Subgroup H} (hcex : HSMinCex H A) [M.Normal]
    (hMs : IsSimpleGroup ↥M) (hMc : center ↥M = ⊥) (hAM : A ≤ M) {t : H} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (A : Set H)) (hX : M ⊔ zpowers t ≠ ⊤) : A = M := by
  set X : Subgroup H := M ⊔ zpowers t with hXdef
  have hMX : M ≤ X := le_sup_left
  have htX : t ∈ X := (le_sup_right : zpowers t ≤ X) (mem_zpowers t)
  have hAX : A ≤ X := hAM.trans hMX
  have hlt : Nat.card ↥X < Nat.card H := by
    have h1 : Nat.card ↥X ∣ Nat.card H := Subgroup.card_subgroup_dvd_card X
    have h2 : Nat.card ↥X ≠ Nat.card H := fun h => hX ((Subgroup.card_eq_iff_eq_top X).1 h)
    exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h1) h2
  have hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥X :=
    Transfer.kProper_of_injective (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
      X.subtype X.subtype_injective hcex.kProper
  have hsq : ∀ y ∈ X, y ^ 2 ∈ M := fun y hy => Prop13.sq_mem_of_mem_sup_zpowers ht hy
  have hodd : ∀ y : ↥X, Odd (orderOf y) → (y : H) ∈ M := fun y hy =>
    Prop13.mem_of_odd_orderOf hsq y.2 (by rwa [Subgroup.orderOf_coe])
  have hOX : CFSG.oddCore ↥X = ⊥ :=
    Prop13.oddCore_eq_bot_of_injective X.subtype X.subtype_injective M
      (by rw [Subgroup.range_subtype]; exact hMX) (fun y hy => hodd y hy) hcex.oddCore
  have hbalX : ∀ s : ↥X, orderOf s = 2 →
      CFSG.oddCore ↥(centralizer ({s} : Set ↥X)) = ⊥ := by
    intro s hs
    have hs' : orderOf (s : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
    have hG := hcex.balanced (s : H) hs'
    let ι : ↥(centralizer ({s} : Set ↥X)) →* ↥(centralizer ({(s : H)} : Set H)) :=
      MonoidHom.codRestrict (X.subtype.comp (centralizer ({s} : Set ↥X)).subtype) _ (fun y => by
        have h1 := mem_centralizer_singleton_iff.1 y.2
        exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1))
    have hι : Function.Injective ι := fun a b hab => by
      have h1 := congrArg (fun z : ↥(centralizer ({(s : H)} : Set H)) => (z : H)) hab
      exact Subtype.ext (Subtype.ext h1)
    have hn : (M.subgroupOf (centralizer ({(s : H)} : Set H))).Normal :=
      Subgroup.Normal.subgroupOf inferInstance _
    refine Prop13.oddCore_eq_bot_of_injective ι hι
      (M.subgroupOf (centralizer ({(s : H)} : Set H))) ?_ ?_ hG
    · intro g hg
      have hgM : (g : H) ∈ M := hg
      have hgX : (g : H) ∈ X := hMX hgM
      have hcs : (⟨(g : H), hgX⟩ : ↥X) ∈ centralizer ({s} : Set ↥X) := by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
      exact ⟨⟨⟨(g : H), hgX⟩, hcs⟩, Subtype.ext rfl⟩
    · intro y hy
      have hy' : Odd (orderOf (((y : ↥X)) : H)) := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hy
      exact hodd (y : ↥X) (by rwa [Subgroup.orderOf_coe] at hy')
  have hmain : HSMainHiS ↥X :=
    (hcex.below.apply (IsSectionOf.of_subgroup X) hlt : HSMainHiSKP ↥X) hKP
  obtain ⟨K₁, K₂, hK₁, hK₂, hq₁, hq₂, -, -⟩ :=
    hmain hOX (A.subgroupOf X)
      (Prop13.standard_subgroupOf_of_involution hAX htX ht htC hcex.standard)
      (by obtain ⟨e⟩ := hcex.sporadic; exact ⟨(Subgroup.subgroupOfEquivOfLe hAX).trans e⟩)
      (Prop13.pRank_two_centralizer_subgroupOf hAX htX ht htC hcex.rank) hbalX
  have hM'n : (M.subgroupOf X).Normal := Subgroup.Normal.subgroupOf inferInstance X
  let eM : ↥(M.subgroupOf X) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMX
  have hM's : IsSimpleGroup ↥(M.subgroupOf X) := eM.isSimpleGroup
  have hK₁' : (K₁.subgroupOf (M.subgroupOf X)).IsSubnormal := hK₁.subgroupOf
  have hM'K : M.subgroupOf X ≤ K₁ := by
    rcases hK₁'.eq_bot_or_top_of_isSimpleGroup hM's with hb | hT
    · exfalso
      have hinj : Function.Injective ((QuotientGroup.mk' (M.subgroupOf X)).comp K₁.subtype) := by
        rw [injective_iff_map_eq_one]
        intro k hk
        have hkM : (k : ↥X) ∈ M.subgroupOf X := (QuotientGroup.eq_one_iff _).1 hk
        have : (⟨(k : ↥X), hkM⟩ : ↥(M.subgroupOf X)) ∈ K₁.subgroupOf (M.subgroupOf X) := k.2
        rw [hb, Subgroup.mem_bot] at this
        exact Subtype.ext (congrArg (fun w : ↥(M.subgroupOf X) => (w : ↥X)) this)
      have hK₁card : Nat.card ↥K₁ ≤ 2 :=
        calc Nat.card ↥K₁ ≤ Nat.card (↥X ⧸ M.subgroupOf X) :=
              Nat.card_le_card_of_injective _ hinj
          _ = M.relIndex X := rfl
          _ ≤ 2 := Prop13.relIndex_sup_zpowers_le_two ht
      have hqcard : Nat.card (↥K₁ ⧸ center ↥K₁) = Nat.card ↥A :=
        card_eq_of_isSporadic hq₁ hcex.sporadic
      have hle : Nat.card (↥K₁ ⧸ center ↥K₁) ≤ 2 :=
        (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans hK₁card
      obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hcex.standard.1
      exact hab (Prop13.commute_of_card_le_two (hqcard ▸ hle) a b)
    · exact Subgroup.subgroupOf_eq_top.1 hT
  have hginj : Function.Injective
      ((QuotientGroup.mk' (center ↥K₁)).comp (Subgroup.inclusion hM'K)) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hmc : (Subgroup.inclusion hM'K m : ↥K₁) ∈ center ↥K₁ := (QuotientGroup.eq_one_iff _).1 hm
    have hmM : eM m ∈ center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨z', rfl⟩ := eM.surjective z
      have h1 := Subgroup.mem_center_iff.1 hmc (Subgroup.inclusion hM'K z')
      have h2 : z' * m = m * z' :=
        Subtype.ext (congrArg (fun w : ↥K₁ => (w : ↥X)) h1)
      rw [← map_mul, ← map_mul, h2]
    rw [hMc, Subgroup.mem_bot] at hmM
    exact eM.injective (by rw [hmM, map_one])
  have hcard1 : Nat.card ↥(M.subgroupOf X) ≤ Nat.card ↥A :=
    calc Nat.card ↥(M.subgroupOf X) ≤ Nat.card (↥K₁ ⧸ center ↥K₁) :=
          Nat.card_le_card_of_injective _ hginj
      _ = Nat.card ↥A := card_eq_of_isSporadic hq₁ hcex.sporadic
  have hcard2 : Nat.card ↥M ≤ Nat.card ↥A := by
    rwa [← Nat.card_congr eM.toEquiv]
  exact Subgroup.eq_of_le_of_card_ge hAM hcard2

end CFSG.EvenSporadicStandard.HSStd.NoA8.Prop13

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Junction
  CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

theorem hsMinCexProp13_of_lemma15 (h15 : FS79Lemma15Hered) :
    HSMinCexProp13 := by
  intro H _ _ A hcex
  have hA := hcex.standard
  have hO := hcex.oddCore
  have hAn : ¬ A.Normal := Prop13.not_normal_of_hsMinCex hcex
  have hZ : center H = ⊥ :=
    Prop13.eq_bot_of_normal_le_centralizer hA hO hAn (N := center H)
      (fun z hz => mem_centralizer_iff.2 fun a _ => Subgroup.mem_center_iff.1 hz a)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hA.2.1)
  have htC : (t' : H) ∈ centralizer (A : Set H) := t'.2
  have ht : orderOf (t' : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht'
  generalize (t' : H) = t at htC ht
  obtain ⟨M, hM, hAM⟩ :=
    Prop13.exists_isCompIn_of_involution_at (h15 H hcex.below.uHered) hcex.kProper hO hA ht htC
  have hMt : IsCompIn (M.map (MulAut.conj t).toMonoidHom) ⊤ := hM.map_conj (Subgroup.mem_top t)
  have hAE : A ≤ layerIn (⊤ : Subgroup H) :=
    hAM.trans (sup_le (le_layerIn_of_isCompIn hM) (le_layerIn_of_isCompIn hMt))
  have hcen : ∀ B : Subgroup H, IsCompIn B ⊤ → center ↥B = ⊥ := fun B hB =>
    Prop13.center_eq_bot_of_isCompIn hA hO hAn hAE hB
  have hsimple : ∀ B : Subgroup H, IsCompIn B ⊤ → IsSimpleGroup ↥B := fun B hB =>
    Prop13.isSimpleGroup_of_center_eq_bot hB.isQuasisimple (hcen B hB)
  have hall : ∀ B : Subgroup H, IsCompIn B ⊤ → B = M ∨ B = M.map (MulAut.conj t).toMonoidHom := by
    intro B hB
    by_contra hcon
    push Not at hcon
    exact hAn (Prop13.normal_of_third_component hA hM hAM hB hcon.1 hcon.2)
  have hEeq : layerIn (⊤ : Subgroup H) = M ⊔ M.map (MulAut.conj t).toMonoidHom :=
    le_antisymm
      (layerIn_le_iff.2 fun Z hZ => (hall Z hZ).elim (fun h => h ▸ le_sup_left)
        (fun h => h ▸ le_sup_right))
      (sup_le (le_layerIn_of_isCompIn hM) (le_layerIn_of_isCompIn hMt))
  by_cases hMtM : M.map (MulAut.conj t).toMonoidHom = M
  ·
    have hMn : M.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h1 : IsCompIn (M.map (MulAut.conj g).toMonoidHom) ⊤ :=
        hM.map_conj (Subgroup.mem_top g)
      have h2 : M.map (MulAut.conj g).toMonoidHom = M := (hall _ h1).elim id (fun h => h.trans hMtM)
      have h3 : g * n * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
      rwa [h2] at h3
    have hAM' : A ≤ M := by
      have := hAM
      rwa [hMtM, sup_idem] at this
    have hMs := hsimple M hM
    have hMc := hcen M hM
    have hXtop : M ⊔ zpowers t = ⊤ := by
      by_contra hX
      have hAeq := Prop13.eq_of_below hcex hMs hMc hAM' ht htC hX
      exact hAn (hAeq ▸ hMn)
    have hidx : M.index ≤ 2 := by
      have := Prop13.relIndex_sup_zpowers_le_two (M := M) ht
      rwa [hXtop, Subgroup.relIndex_top_right] at this
    have hcard : Nat.card (H ⧸ M) ≤ 2 := hidx
    have hcomm' : commutator H = M := by
      apply le_antisymm
      · rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' M) ⁅x, y⁆ = 1
        rw [map_commutatorElement, commutatorElement_def,
          Prop13.commute_of_card_le_two hcard (QuotientGroup.mk' M x) (QuotientGroup.mk' M y)]
        simp
      · exact Transfer.le_commutator_of_quasisimple_open M
          ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥M).2.2.1.1 hM.isQuasisimple)
    refine ⟨hZ, ?_, ?_⟩
    · rw [hcomm']
      exact hMs
    · rw [hcomm']
      exact hidx
  ·
    exfalso
    have hcomm : ∀ x ∈ M, ∀ y ∈ M.map (MulAut.conj t).toMonoidHom, x * y = y * x :=
      hM.commute_of_ne hMt (Ne.symm hMtM)
    have hMZ : M ⊓ centralizer (M : Set H) = ⊥ :=
      Prop13.inf_centralizer_eq_bot_of_isCompIn hA hO hAn hAE hM
    have hAt : A ≤ centralizer ({t} : Set H) := fun x hx =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)
    have hA1 : A ≠ ⊥ := by
      intro h
      obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hA.1
      rw [Subgroup.eq_bot_iff_forall] at h
      apply hab
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h (a : H) a.2, one_mul, mul_one]
    obtain ⟨e⟩ := Prop13.exists_mulEquiv_of_swap ht hcomm hMZ (hsimple M hM) hAM hAt
      (Prop13.centralizer_singleton_le_normalizer hA ht htC) hA1
    obtain ⟨f⟩ := hcex.sporadic
    have hq1 : IsSporadic (↥M ⧸ center ↥M) .HS :=
      ⟨((QuotientGroup.quotientMulEquivOfEq (hcen M hM)).trans QuotientGroup.quotientBot).trans
        (e.trans f)⟩
    let eMt : ↥(M.map (MulAut.conj t).toMonoidHom) ≃* ↥M :=
      (M.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm
    have hq2 : IsSporadic (↥(M.map (MulAut.conj t).toMonoidHom) ⧸
        center ↥(M.map (MulAut.conj t).toMonoidHom)) .HS :=
      ⟨((QuotientGroup.quotientMulEquivOfEq (hcen _ hMt)).trans QuotientGroup.quotientBot).trans
        (eMt.trans (e.trans f))⟩
    refine hcex.notOutcome ⟨M, M.map (MulAut.conj t).toMonoidHom,
      (Prop13.isCompIn_top_iff.1 hM).2, (Prop13.isCompIn_top_iff.1 hMt).2, hq1, hq2, hAM, ?_⟩
    rw [← hEeq]
    exact Prop13.layerIn_normal

end CFSG.EvenSporadicStandard.HSStd.NoA8

namespace CFSG.EvenSporadicStandard.HSStd.NoA8.Lemma21

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.HSStd

variable {H : Type} [Group H] [Finite H]

theorem isSporadic_quotient {A : Subgroup H}
    (hcex : HSMinCex H A) : IsSporadic (↥A ⧸ center ↥A) .HS := by
  have hZ : center ↥A = ⊥ := center_eq_bot_of_isSporadic_hs hcex.sporadic
  obtain ⟨e⟩ := hcex.sporadic
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem exists_involution {A : Subgroup H} (hcex : HSMinCex H A) :
    ∃ t : H, t ∈ centralizer (A : Set H) ∧ orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.1 hcex.standard.2.1 : 2 ∣ Nat.card ↥(centralizer (A : Set H)))
  exact ⟨(t : H), t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩

theorem two_le_card_sylow {A : Subgroup H} (hcex : HSMinCex H A)
    (S : Sylow 2 (centralizer (A : Set H))) : 2 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : 2 ∣ Nat.card ↥(centralizer (A : Set H)) := even_iff_two_dvd.1 hcex.standard.2.1
  have hpos : 0 < (Nat.card ↥(centralizer (A : Set H))).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
  rw [Sylow.card_eq_multiplicity]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (Nat.card ↥(centralizer (A : Set H))).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hpos

theorem pRank_sylow_le_one {A : Subgroup H} (hcex : HSMinCex H A)
    (S : Sylow 2 (centralizer (A : Set H))) :
    CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (A : Set H))) ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hinj : Function.Injective
      ((centralizer (A : Set H)).subtype.comp
        (S : Subgroup ↥(centralizer (A : Set H))).subtype) :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have h1 := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two _ hinj
    (⊤ : Subgroup ↥(S : Subgroup ↥(centralizer (A : Set H))))
  have h2 : (⊤ : Subgroup ↥(S : Subgroup ↥(centralizer (A : Set H)))).map
      ((centralizer (A : Set H)).subtype.comp
        (S : Subgroup ↥(centralizer (A : Set H))).subtype) ≤ centralizer (A : Set H) := by
    rintro _ ⟨x, -, rfl⟩
    exact (x : ↥(centralizer (A : Set H))).2
  have h3 := CFSG.SectionRank.pRank_mono (p := 2) one_lt_two h2
  rw [hcex.rank] at h3
  exact h1.trans h3

theorem card_sylow_eq_two_of_ne_top {A : Subgroup H}
    (hcex : HSMinCex H A) (hsimple : IsSimpleGroup ↥(commutator H))
    (hidx : (commutator H).index ≤ 2) (hne : commutator H ≠ ⊤)
    (S : Sylow 2 (centralizer (A : Set H))) : Nat.card S = 2 := by
  have hAM : A ≤ commutator H := Transfer.le_commutator_of_quasisimple_open A hcex.standard.1
  have hMc : center ↥(commutator H) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center ↥(commutator H)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hcex.standard.1
      have ha : (⟨(a : H), hAM a.2⟩ : ↥(commutator H)) ∈ center ↥(commutator H) := by
        rw [h]
        exact Subgroup.mem_top _
      have h2 := Subgroup.mem_center_iff.1 ha ⟨(b : H), hAM b.2⟩
      exact hab (Subtype.ext (congrArg (fun z : ↥(commutator H) => (z : H)) h2.symm))
  have hno : ∀ u ∈ centralizer (A : Set H), u ∈ commutator H → orderOf u = 2 → False := by
    intro u huC huM hu2
    have hX : commutator H ⊔ zpowers u ≠ ⊤ := by
      rw [sup_eq_left.2 (Subgroup.zpowers_le.2 huM)]
      exact hne
    have hAeq := Prop13.eq_of_below hcex hsimple hMc hAM hu2 huC hX
    exact Prop13.not_normal_of_hsMinCex hcex (hAeq ▸ (inferInstance : (commutator H).Normal))
  have hle := Lemma21.card_le_two_of_no_involution (C := centralizer (A : Set H))
    (M := commutator H) hidx ((S.isPGroup').map (centralizer (A : Set H)).subtype)
    (Subgroup.map_subtype_le _) hno
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hle
  exact le_antisymm hle (two_le_card_sylow hcex S)

theorem false_of_genQuaternion [IsSimpleGroup H]
    (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic) {A : Subgroup H}
    (hcex : HSMinCex H A) (S : Sylow 2 (centralizer (A : Set H)))
    (hq : IsGenQuaternion ↥(S : Subgroup ↥(centralizer (A : Set H)))) : False := by
  obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hcex.standard.1
  have hnab : ∃ x y : H, x * y ≠ y * x :=
    ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hfs : FStarSimple (⊤ : Subgroup H) := fStarSimple_top H hnab
  have hord : ¬ Nat.card ↥(⊤ : Subgroup H) ∣ 95040 :=
    not_card_dvd_95040_of_le_of_seven_dvd le_top
      (HSStd.Lemma21.seven_dvd_card_of_isSporadic_hs hcex.sporadic)
  have hodd := thm24_1 H ⊤ hfs hord A (solStd_of_standardComponentIsStandard hcex.standard) ⟨S, hq⟩
  obtain ⟨t, htC, ht⟩ := exists_involution hcex
  exact hlie H ⊤ hfs hodd t ht A (Prop13.isCompIn_centralizer_singleton hcex.standard ht htC)
    .HS (isSporadic_quotient hcex)

theorem card_sylow_eq_two_of_simple
    [IsSimpleGroup H] (thm24_1 : Sol78Thm24_1Use)
    (hlie : Hyp.OddLieCompNotSporadic) {A : Subgroup H} (hcex : HSMinCex H A)
    (S : Sylow 2 (centralizer (A : Set H))) : Nat.card S = 2 := by
  obtain ⟨a, b, hab⟩ := Transfer.exists_noncomm_of_quasisimple_open hcex.standard.1
  have hnab : ∃ x y : H, x * y ≠ y * x :=
    ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hcyc : IsCyclic ↥(S : Subgroup ↥(centralizer (A : Set H))) := by
    rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' (pRank_sylow_le_one hcex S)
      with hc | hq
    · exact hc
    · exact (false_of_genQuaternion thm24_1 hlie hcex S hq).elim
  have hZ : center ↥A = ⊥ := center_eq_bot_of_isSporadic_hs hcex.sporadic
  have hstd : StdHyp H A :=
    ⟨inferInstance, hnab, hcex.kProper, hcex.standard, fun t ht => hcex.balanced t ht, ⟨S, hcyc⟩,
      by rw [hZ]; exact IsPGroup.of_bot⟩
  exact hstd.card_sylow_eq_two_hs hsFacts hcex.sporadic S

end CFSG.EvenSporadicStandard.HSStd.NoA8.Lemma21

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.EvenSporadicStandard.Induction

theorem hsMinCexLemma21_of_inputs
    (hP13 : HSMinCexProp13) (thm24_1 : Sol78Thm24_1Use)
    (hlie : Hyp.OddLieCompNotSporadic) : HSMinCexLemma21 := by
  intro H _ _ A hcex S
  obtain ⟨-, hsimple, hidx⟩ := hP13 H A hcex
  by_cases hne : commutator H = ⊤
  · have hs : IsSimpleGroup H := by
      rw [hne] at hsimple
      exact (Subgroup.topEquiv (G := H)).symm.isSimpleGroup
    exact Lemma21.card_sylow_eq_two_of_simple thm24_1 hlie hcex S
  · exact Lemma21.card_sylow_eq_two_of_ne_top hcex hsimple hidx hne S

end CFSG.EvenSporadicStandard.HSStd.NoA8
