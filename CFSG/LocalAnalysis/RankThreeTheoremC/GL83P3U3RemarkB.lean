module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkA
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2AS
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Maschke
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.RankThree.PartOne.D4RC.Burnside
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
open scoped commutatorElement


private theorem exists_elemAbelian_of_not_isCyclic' {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} (P : Sylow p K)
    (hnc : ¬ IsCyclic (P : Subgroup K)) :
    ∃ B : Subgroup Y, B ≤ K ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 := by
  obtain ⟨B₀, hB₀, hB₀c⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two hodd P.isPGroup' hnc
  have hB₁ : CFSG.IsElementaryAbelian p (B₀.map (P : Subgroup K).subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hB₂ : CFSG.IsElementaryAbelian p ((B₀.map (P : Subgroup K).subtype).map K.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  refine ⟨(B₀.map (P : Subgroup K).subtype).map K.subtype, Subgroup.map_subtype_le _,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hB₂, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective (P : Subgroup K).subtype_injective, hB₀c]

private theorem exists_inv_mul_mem_centralizer3 {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    [Finite Y] (hInn : KFactInnerAction) (hp2 : p ≠ 2) {K : Subgroup Y}
    (hsimple : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    {Q : Subgroup Y} {P : Sylow p K} (hPab : IsMulCommutative (P : Subgroup K))
    (hP : (P : Subgroup K) = Q.subgroupOf K) (hP1 : (P : Subgroup K) ≠ ⊥)
    {y : Y} (hyc : ∀ q ∈ Q, y * q = q * y) (hyN : y ∈ normalizer (K : Set Y))
    (hyp : y ^ p = 1) : ∃ r ∈ Q ⊓ K, r⁻¹ * y ∈ centralizer (K : Set Y) := by
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  set φ : MulAut K := K.normalizerMonoidHom ⟨y, hyN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : Y) = y * k * y⁻¹ := fun _ => rfl
  have hφp : φ ^ p = 1 := by
    have h1 : (⟨y, hyN⟩ : normalizer (K : Set Y)) ^ p = 1 :=
      Subtype.ext (by rw [coe_pow, coe_one]; exact hyp)
    rw [hφdef, ← map_pow, h1, map_one]
  obtain ⟨g, hgP, hg⟩ := hInn p Fact.out hp2 K hsimple hnonab hcat P hP1 hPab
    φ ⟨1, by rw [pow_one, hφp]⟩
    (fun g hg => by
      have hyg : y * (g : Y) = g * y := hyc g ((hmem g).mp hg)
      ext m
      change y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹
      calc y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (y * g) * m * (y * g)⁻¹ := by group
        _ = (g * y) * m * (g * y)⁻¹ := by rw [hyg]
        _ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹ := by group)
  refine ⟨g, ⟨(hmem g).mp hgP, g.2⟩, mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h1 : y * k * y⁻¹ = (g : Y) * k * (g : Y)⁻¹ := by
    rw [← hφ ⟨k, hk⟩, hg]
    rfl
  calc k * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * k * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [h1]
    _ = (g : Y)⁻¹ * y * k := by group

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}


private theorem mem_map_conj_iff (L : Subgroup Y) (g y : Y) :
    y ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ L := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem center_map_conj_ne_bot {L : Subgroup Y} (g : Y) (hc : center L ≠ ⊥) :
    center (L.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  obtain ⟨⟨⟨a, haL⟩, hac⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  have hcomm : ∀ b ∈ L, b * a = a * b := fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp hac ⟨b, hb⟩)
  have hmem : g * a * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj_iff]
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rw [e]
    exact haL
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨g * a * g⁻¹, hmem⟩, ?_⟩, ?_⟩
  · rw [mem_center_iff]
    rintro ⟨b, hb⟩
    apply Subtype.ext
    have hb' : g⁻¹ * b * g ∈ L := (mem_map_conj_iff L g b).mp hb
    have h1 := hcomm _ hb'
    show b * (g * a * g⁻¹) = g * a * g⁻¹ * b
    calc b * (g * a * g⁻¹) = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * b := by group
  · intro e
    have e1 : g * a * g⁻¹ = 1 := congrArg (fun z => z.1.1) e
    exact ha1 (Subtype.ext (Subtype.ext (conj_eq_one_iff.mp e1)))

theorem mem_of_cyclic_sylow (h : Case2Data3 p P T D F x) (hInn : KFactInnerAction)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hZ : center L = ⊥)
    (hcyc : ∀ S : Sylow p L, IsCyclic (S : Subgroup L)) : x ∈ L := by
  haveI := h.fact
  have hp2 : p ≠ 2 := by have := h.three; omega
  have hxP : x ∈ P := h.pdata.D_le h.pdata.x_mem
  have hxN : x ∈ normalizer (L : Set Y) := h.P_le_normalizer hL hxP
  have hxC : x ∉ centralizer (L : Set Y) := by
    intro hxc
    apply h.not_le_centralizer_x hL
    intro l hl
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (mem_centralizer_iff.mp hxc l hl).symm
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hL hZ
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.pdata.x_ord] at this
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P ⊤ := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index
  have hPL : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ L) L :=
    (hPsyl.of_le (le_sup_left : P ≤ P ⊔ L) le_top).inf_of_le_normalizer le_sup_right
      (sup_le (h.P_le_normalizer hL) le_normalizer)
  obtain ⟨PK, hPK⟩ := hPL.exists_sylow_eq_subgroupOf
  have hP : (PK : Subgroup L) = P.subgroupOf L := by
    rw [hPK, Subgroup.inf_subgroupOf_right]
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  have hP1 : (PK : Subgroup L) ≠ ⊥ := by
    obtain ⟨t0, ht0, ht0o, -⟩ := h.exists_mem_P_inf hL
    intro hbot
    have ht : (⟨t0, (mem_inf.mp ht0).2⟩ : L) ∈ (PK : Subgroup L) :=
      (hmem _).mpr (mem_inf.mp ht0).1
    rw [hbot, mem_bot] at ht
    rw [show t0 = 1 from congrArg Subtype.val ht, orderOf_one] at ht0o
    exact h.prime.one_lt.ne ht0o
  have hPc := hcyc PK
  have hPab : IsMulCommutative (PK : Subgroup L) :=
    IsMulCommutative.of_comm fun a b => (hPc.commGroup).mul_comm a b
  obtain ⟨r, hrQK, hc⟩ := exists_inv_mul_mem_centralizer3 hInn hp2 hsimple hnonab
    (h.catalog.simple_subgroup L hsimple hnonab) hPab hP hP1
    (fun q hq => (mem_centralizer_singleton_iff.mp (h.P_le_centralizer hq)).symm) hxN hxp
  have hrc : Commute r (r⁻¹ * x) := mem_centralizer_iff.mp hc r hrQK.2
  have hrp : r ^ p = 1 := by
    have h1 : r ^ p * (r⁻¹ * x) ^ p = 1 := by
      rw [← hrc.mul_pow, mul_inv_cancel_left, hxp]
    exact GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ (pow_mem hrQK.2 p)
      ((eq_inv_of_mul_eq_one_left h1) ▸ inv_mem (pow_mem hc p))
  have hro : orderOf r = p := by
    refine orderOf_eq_prime hrp fun hr1 => hxC ?_
    rwa [hr1, inv_one, one_mul] at hc
  set r' : L := ⟨r, hrQK.2⟩ with hr'
  have hr'P : r' ∈ (PK : Subgroup L) := (hmem r').mpr hrQK.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect
      hL.2.2.1 PK.isPGroup' PK.not_dvd_index hPc hP1
  have ha1 : a ≠ 1 := fun ha => hga (by rw [ha, mul_one, mul_inv_cancel])
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r' ^ j = a := by
    have hr'p : (⟨r', hr'P⟩ : (PK : Subgroup L)) ^ p = 1 :=
      Subtype.ext (Subtype.ext (by simpa [hr'] using hrp))
    have hr'1 : (⟨r', hr'P⟩ : (PK : Subgroup L)) ≠ 1 := fun h1 => by
      have h2 : r = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
      rw [h2, orderOf_one] at hro
      exact h.prime.one_lt.ne hro
    have heq : zpowers (⟨a, haP⟩ : (PK : Subgroup L)) = zpowers ⟨r', hr'P⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime (Subtype.ext hap) (fun h1 => ha1 (congrArg Subtype.val h1)),
        orderOf_eq_prime hr'p hr'1]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers (⟨a, haP⟩ : (PK : Subgroup L)))
    exact ⟨j, congrArg Subtype.val hj⟩
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ P :=
    (hmem _).mp ((mem_normalizer_iff.mp hgN r').mp hr'P)
  obtain ⟨m, hm, hcm⟩ := GL83Generic5MComp.exists_conj_eq_zpow hZ h.wc hxP hrQK.1 hrQK.2 hc g.2 hgr
  have hrm : r ^ (m - 1) ≠ 1 := by
    intro hr1
    apply hga
    have hfix : g * r' * g⁻¹ = r' := Subtype.ext (by
      rw [zpow_sub_one, mul_inv_eq_one] at hr1
      simpa [hr1] using hm)
    rw [← conj_zpow, hfix]
  set c := r⁻¹ * x with hcdef
  have hcp : c ^ p = 1 := by
    have hrx : Commute r⁻¹ x :=
      mem_centralizer_singleton_iff.mp (h.P_le_centralizer (inv_mem (mem_inf.mp hrQK).1))
    rw [hcdef, hrx.mul_pow, inv_pow, hrp, inv_one, one_mul, hxp]
  have hc1 : c = 1 := by
    have hcm1 : c ^ (m - 1) = 1 := by rw [zpow_sub_one, hcm, mul_inv_cancel]
    rcases h.prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcp) with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      refine hrm (orderOf_dvd_iff_zpow_eq_one.mp ?_)
      rw [hro, ← h1]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hcm1
  have hxr : x = r := by
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1.symm
  exact hxr ▸ hrQK.2

theorem isCyclic_sylow_of_moved (h : Case2Data3 p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hZ : center L = ⊥) {f : Y} (hfN : f ∉ normalizer (L : Set Y))
    (S : Sylow p L) : IsCyclic (S : Subgroup L) := by
  by_contra hnc
  haveI := h.fact
  have hodd : Odd p := by rw [h.three]; decide
  obtain ⟨B, hBL, hBel, hBc⟩ := exists_elemAbelian_of_not_isCyclic' hodd S hnc
  have hL₂ : IsComponentOf (L.map (MulAut.conj f).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) L).mpr hL
  have hne : L.map (MulAut.conj f).toMonoidHom ≠ L := fun h' =>
    hfN (mem_normalizer_iff_map_conj_eq.mpr h')
  have hLL : L ≤ centralizer ((L.map (MulAut.conj f).toMonoidHom : Subgroup Y) : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL hL₂ hne.symm)
  have hLL' : L.map (MulAut.conj f).toMonoidHom ≤ centralizer (L : Set Y) :=
    le_centralizer_iff.mp hLL
  set B₂ : Subgroup Y := B.map (MulAut.conj f).toMonoidHom with hB₂
  have hB₂L : B₂ ≤ L.map (MulAut.conj f).toMonoidHom := Subgroup.map_mono hBL
  have hcomm : ∀ b ∈ B, ∀ b' ∈ B₂, b * b' = b' * b := fun b hb b' hb' =>
    (mem_centralizer_iff.mp (hLL (hBL hb)) b' (hB₂L hb')).symm
  have hBB : Disjoint B B₂ := by
    rw [disjoint_iff, eq_bot_iff]
    intro e he
    have h1 : e ∈ L := hBL he.1
    have h2 : e ∈ centralizer (L : Set Y) := hLL' (hB₂L he.2)
    exact mem_bot.mpr (GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ h1 h2)
  have hB₂el : IsElemAbelian p B₂ := by
    have := hBel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := a.2
      obtain ⟨b', hb', hb'e⟩ := b.2
      apply Subtype.ext
      show (a : Y) * b = b * a
      rw [← ha'e, ← hb'e]
      have := congrArg (MulAut.conj f) (setLike_mul_comm ha' hb')
      simpa using this
    · obtain ⟨y', hy', rfl⟩ := hy
      have : y' ^ p = 1 := hBel.2 y' hy'
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, this, map_one]
  have hB₂c : Nat.card B₂ = p ^ 2 := by
    rw [hB₂, Subgroup.card_map_of_injective (MulAut.conj f).injective, hBc]
  have key := add_le_pRank_of_commute (p := p) (P := (⊤ : Subgroup Y)) (E₁ := B) (E₂ := B₂)
    (r := 2) (s := 2) hBel hB₂el hBc hB₂c hcomm hBB le_top le_top
  have := h.rank
  omega

theorem F_mem_normalizer (h : Case2Data3 p P T D F x) (hInn : KFactInnerAction)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) {f : Y} (hf : f ∈ F) :
    f ∈ normalizer (L : Set Y) := by
  classical
  haveI := h.fact
  by_contra hfN
  set L' : Subgroup Y := L.map (MulAut.conj f).toMonoidHom with hL'def
  have hL' : IsComponentOf L' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) L).mpr hL
  have hmem' : ∀ y, y ∈ L' ↔ f⁻¹ * y * f ∈ L := fun y => mem_map_conj_iff L f y
  have hne : L ≠ L' := by
    intro e
    apply hfN
    rw [mem_set_normalizer_iff'']
    intro y
    exact (Iff.of_eq (congrArg (fun S : Subgroup Y => y ∈ S) e)).trans (hmem' y)
  have hLL : ⁅L, L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLL ha) b hb).symm
  have hZL : center L = ⊥ := by
    by_contra hc
    exact hne (h.eq_of_center_ne_bot hL hL' hc (center_map_conj_ne_bot f hc))
  have hinf : ∀ w, w ∈ L → w ∈ L' → w = 1 := fun w hwL hwL' =>
    GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer
      hZL hwL (mem_centralizer_iff.mpr fun g hg => hcomm g hg w hwL')
  have hxL : x ∈ L :=
    h.mem_of_cyclic_sylow hInn hL hZL (fun S => h.isCyclic_sylow_of_moved hL hZL hfN S)
  have hxfix : f⁻¹ * x * f = x := by
    have := h.F_D f⁻¹ (F.inv_mem hf) x h.pdata.x_mem
    simpa using this
  have hxL' : x ∈ L' := (hmem' x).mpr (by rw [hxfix]; exact hxL)
  exact h.x_ne_one (hinf x hxL hxL')


end Case2Data3

private theorem kFactHeis_p {p : ℕ} (hp3 : p = 3) (h123 : KFactWeakClosureHeisThree) :
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
      (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
      p ∣ Nat.card K → ∀ Q : Sylow p X, K ⊔ (Q : Subgroup X) = ⊤ →
        ∀ Q₀ Q₁ : Subgroup X, IsCyclic Q₀ → Q₀ ≠ ⊥ → Nat.card Q₁ = p ^ 3 →
          ¬ IsMulCommutative Q₁ → (∀ q ∈ Q₁, q ^ p = 1) → (∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a) →
          Q₀ ⊓ Q₁ = ⊥ → Q₀ ⊔ Q₁ = (Q : Subgroup X) →
          ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = p →
            ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
              A.map (MulAut.conj g).toMonoidHom ≠ A := by
  subst hp3
  exact h123

private theorem false_isElemAbelian_zpowers {p : ℕ} {X : Type} [Group X] {g : X}
    (hg : g ^ p = 1) : IsElemAbelian p (zpowers g) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem false_x_mem_P (h : Case2Data3 p P T D F x) : x ∈ P := h.pdata.D_le h.pdata.x_mem

private theorem false_x_pow_p (h : Case2Data3 p P T D F x) : x ^ p = 1 := by
  rw [← h.pdata.x_ord]
  exact pow_orderOf_eq_one x

private theorem false_D_comm (h : Case2Data3 p P T D F x) {d d' : Y} (hd : d ∈ D) (hd' : d' ∈ D) :
    d * d' = d' * d := by
  haveI := h.pdata.D_cyc
  exact congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : D) ⟨d', hd'⟩)

private theorem false_P_commutator_mem (h : Case2Data3 p P T D F x) {a b : Y} (ha : a ∈ P)
    (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul a ha
  obtain ⟨t', ht', d', hd', rfl⟩ := h.exists_mul b hb
  have h1 : Commute d t' := (h.pdata.comm t' ht' d hd).symm
  have h2 : Commute d' t := (h.pdata.comm t ht d' hd').symm
  have h3 : d * d' = d' * d := h.false_D_comm hd hd'
  have e1 : t * d * (t' * d') = t * t' * (d * d') := h1.mul_mul_mul_comm t d'
  have e2 : t' * d' * (t * d) = t' * t * (d' * d) := h2.mul_mul_mul_comm t' d
  have hc := h.commutator_mem t ht t' ht'
  have e3 : t * d * (t' * d') = (t * t' * t⁻¹ * t'⁻¹) * (t' * d' * (t * d)) := by
    rw [e1, e2, ← h3]; group
  have e4 : t * d * (t' * d') * (t * d)⁻¹ * (t' * d')⁻¹ = t * t' * t⁻¹ * t'⁻¹ := by
    rw [e3]; group
  rw [e4]; exact hc

private theorem false_exists_not_mem_zOf (h : Case2Data3 p P T D F x) : ∃ t ∈ T, t ∉ zOf T := by
  by_contra hcon
  push Not at hcon
  refine h.pdata.T_nonab (isMulCommutative_iff.2 fun a b => ?_)
  have hz : (a : Y) ∈ T ⊓ centralizer (T : Set Y) := hcon a a.2
  exact Subtype.ext (mem_centralizer_iff.1 hz.2 b b.2).symm

private theorem false_x_not_mem_zOf (h : Case2Data3 p P T D F x) : x ∉ zOf T := by
  intro hxz
  have hx1 : x ∈ T ⊓ zpowers x := ⟨h.zOf_le hxz, Subgroup.mem_zpowers x⟩
  rw [h.T_inf_zpowers] at hx1
  exact h.x_ne_one (Subgroup.mem_bot.1 hx1)

private theorem false_exists_psi (h : Case2Data3 p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (K : Subgroup X) (Q : Sylow p X) (ψ : ↥P →* X),
      K.Normal ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      centralizer (K : Set X) = ⊥ ∧ p ∣ Nat.card K ∧ K ⊔ (Q : Subgroup X) = ⊤ ∧
      (∀ a : ↥P, ψ a = 1 ↔ (a : Y) ∈ centralizer (L : Set Y)) ∧
      ψ.range = (Q : Subgroup X) ∧
      ∀ g : X, (zpowers (ψ ⟨x, h.false_x_mem_P⟩)).map (MulAut.conj g).toMonoidHom ≤
          (Q : Subgroup X) →
        (zpowers (ψ ⟨x, h.false_x_mem_P⟩)).map (MulAut.conj g).toMonoidHom =
          zpowers (ψ ⟨x, h.false_x_mem_P⟩) := by
  haveI := h.fact
  obtain ⟨X, hG, hF, π, K, Q, hπ⟩ :=
    exists_almostSimple h.core h.catalog hL h.sylow (h.P_le_normalizer hL)
  have hPL : P ≤ L ⊔ P := le_sup_right
  have hzp : ((zpowers x).subgroupOf (L ⊔ P)).map π
      = zpowers ((π.comp (Subgroup.inclusion hPL)) ⟨x, h.false_x_mem_P⟩) := by
    ext q
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, ⟨k, hk⟩, rfl⟩
      refine ⟨k, ?_⟩
      have : (Subgroup.inclusion hPL ⟨x, h.false_x_mem_P⟩) ^ k = n := by
        apply Subtype.ext
        simpa using hk
      simp only [MonoidHom.comp_apply]
      rw [← map_zpow, this]
    · rintro ⟨k, rfl⟩
      refine ⟨(Subgroup.inclusion hPL ⟨x, h.false_x_mem_P⟩) ^ k, ⟨k, by simp⟩, ?_⟩
      simp
  refine ⟨X, hG, hF, K, Q, π.comp (Subgroup.inclusion hPL), hπ.normal, hπ.simple,
    hπ.nonab, hπ.catalog,
    hπ.cent, hπ.dvd, hπ.sup, ?_, ?_, ?_⟩
  · intro a
    exact hπ.ker_iff (Subgroup.inclusion hPL a)
  · ext q
    rw [hπ.Q_eq]
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hPL a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  · intro g
    have := hπ.weakClosed_transfer (A := zpowers x) (by simpa using h.false_x_mem_P) h.wc g
    rw [hzp] at this
    exact this

theorem false_of_abelian (h : Case2Data3 p P T D F x) (hK : KFactWeakClosureRank2)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hC : P ⊓ centralizer (L : Set Y) = zOf T) : False := by
  haveI := h.fact
  obtain ⟨X, _, _, K, Q, ψ, hKn, hKs, hKnab, hKcat, hKc, hKdvd, hKsup, hker, hrange, hwc⟩ :=
    h.false_exists_psi hL
  have hker' : ∀ a : ↥P, ψ a = 1 ↔ (a : Y) ∈ zOf T := by
    intro a
    rw [hker a, ← hC, Subgroup.mem_inf]
    exact ⟨fun hc => ⟨a.2, hc⟩, fun hc => hc.2⟩
  set x' : ↥P := ⟨x, h.false_x_mem_P⟩
  have hψx : ψ x' ≠ 1 := fun h1 => h.false_x_not_mem_zOf ((hker' x').1 h1)
  have hψxp : (ψ x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using h.false_x_pow_p)
    rw [this, map_one]
  have hAord : orderOf (ψ x') = p := orderOf_eq_prime hψxp hψx
  have hQab : IsMulCommutative (Q : Subgroup X) := by
    rw [← hrange]
    refine isMulCommutative_iff.2 fun u v => ?_
    obtain ⟨a, ha⟩ := u.2
    obtain ⟨b, hb⟩ := v.2
    apply Subtype.ext
    show (u : X) * v = v * u
    rw [← ha, ← hb]
    have h1 : ψ (a * b * a⁻¹ * b⁻¹) = 1 := (hker' _).2 (h.false_P_commutator_mem a.2 b.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hQrank : 2 ≤ CFSG.Open.pRank p (Q : Subgroup X) := by
    obtain ⟨t, ht, htz⟩ := h.false_exists_not_mem_zOf
    set t' : ↥P := ⟨t, h.pdata.T_le ht⟩
    have hψt : ψ t' ≠ 1 := fun h1 => htz ((hker' t').1 h1)
    have hψtp : (ψ t') ^ p = 1 := by
      rw [← map_pow]
      have : t' ^ p = 1 := Subtype.ext (by simpa using h.pdata.T_exp t ht)
      rw [this, map_one]
    have hcm : Commute (ψ t') (ψ x') := by
      show ψ t' * ψ x' = ψ x' * ψ t'
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (h.pdata.comm t ht x h.pdata.x_mem))
    have hdisj : Disjoint (zpowers (ψ t')) (zpowers (ψ x')) := by
      rw [Subgroup.disjoint_def]
      intro y hy1 hy2
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy2
      have h1 : ψ ((t' ^ i)⁻¹ * x' ^ j) = 1 := by
        rw [map_mul, map_inv, map_zpow, map_zpow, hj, inv_mul_cancel]
      have h2 : (t ^ i)⁻¹ * x ^ j ∈ zOf T := by
        have := (hker' _).1 h1
        simpa using this
      have h3 : x ^ j ∈ T := by
        have := T.mul_mem (T.zpow_mem ht i) (h.zOf_le h2)
        simpa using this
      have h4 : x ^ j ∈ T ⊓ zpowers x := ⟨h3, Subgroup.zpow_mem_zpowers x j⟩
      rw [h.T_inf_zpowers] at h4
      have h5 : x' ^ j = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h4)
      rw [← hj, ← map_zpow, h5, map_one]
    have key := add_le_pRank_of_commute (p := p) (P := (Q : Subgroup X))
      (E₁ := zpowers (ψ t')) (E₂ := zpowers (ψ x')) (r := 1) (s := 1)
      (false_isElemAbelian_zpowers hψtp) (false_isElemAbelian_zpowers hψxp)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hψtp hψt)
      (by rw [Nat.card_zpowers, pow_one]; exact hAord)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (hcm.zpow_zpow k l).eq)
      hdisj
      (Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨t', rfl⟩))
      (Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩))
    simpa using key
  have hAQ : zpowers (ψ x') ≤ (Q : Subgroup X) :=
    Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩)
  have hAcard : Nat.card (zpowers (ψ x')) = p := by rw [Nat.card_zpowers]; exact hAord
  obtain ⟨g, hg1, hg2⟩ :=
    hK p h.prime (by have := h.three; omega) X K hKn hKs hKnab hKcat hKc hKdvd Q
    hKsup hQab hQrank (zpowers (ψ x')) hAQ hAcard
  exact hg2 (hwc g hg1)

theorem false_of_faithful (h : Case2Data3 p P T D F x) (h123 : KFactWeakClosureHeisThree)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hC : P ⊓ centralizer (L : Set Y) = ⊥) : False := by
  haveI := h.fact
  obtain ⟨X, _, _, K, Q, ψ, hKn, hKs, hKnab, hKcat, hKc, hKdvd, hKsup, hker, hrange, hwc⟩ :=
    h.false_exists_psi hL
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : Y) ∈ P ⊓ centralizer (L : Set Y) := ⟨a.2, (hker a).1 ha⟩
    rw [hC] at h1
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  set x' : ↥P := ⟨x, h.false_x_mem_P⟩
  have hψx : ψ x' ≠ 1 := by
    intro h1
    have := hinj (h1.trans (map_one ψ).symm)
    exact h.x_ne_one (congrArg Subtype.val this)
  have hψxp : (ψ x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using h.false_x_pow_p)
    rw [this, map_one]
  have hAord : orderOf (ψ x') = p := orderOf_eq_prime hψxp hψx
  set Q₀ : Subgroup X := (D.subgroupOf P).map ψ with hQ₀
  set Q₁ : Subgroup X := (T.subgroupOf P).map ψ with hQ₁
  have hmem₀ : ∀ {q : X}, q ∈ Q₀ ↔ ∃ a : ↥P, (a : Y) ∈ D ∧ ψ a = q := by
    intro q
    simp only [hQ₀, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hmem₁ : ∀ {q : X}, q ∈ Q₁ ↔ ∃ a : ↥P, (a : Y) ∈ T ∧ ψ a = q := by
    intro q
    simp only [hQ₁, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hcyc : IsCyclic ↥Q₀ := by
    haveI := h.pdata.D_cyc
    haveI : IsCyclic ↥(D.subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h.pdata.D_le).symm
        (Subgroup.subgroupOfEquivOfLe h.pdata.D_le).symm.surjective
    exact isCyclic_of_surjective (ψ.subgroupMap (D.subgroupOf P))
      (ψ.subgroupMap_surjective (D.subgroupOf P))
  have hQ0ne : Q₀ ≠ ⊥ := by
    intro h0
    have : ψ x' ∈ Q₀ := hmem₀.2 ⟨x', h.pdata.x_mem, rfl⟩
    rw [h0] at this
    exact hψx (Subgroup.mem_bot.1 this)
  have hcard : Nat.card Q₁ = p ^ 3 := by
    rw [hQ₁, Subgroup.card_map_of_injective hinj]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.pdata.T_le).toEquiv]
    exact h.pdata.T_card
  have hnab : ¬ IsMulCommutative Q₁ := by
    intro hab
    refine h.pdata.T_nonab (isMulCommutative_iff.2 fun u v => ?_)
    set a : ↥P := ⟨u, h.pdata.T_le u.2⟩
    set b : ↥P := ⟨v, h.pdata.T_le v.2⟩
    have h1 : ψ a * ψ b = ψ b * ψ a :=
      congrArg Subtype.val
        (mul_comm' (⟨ψ a, hmem₁.2 ⟨a, u.2, rfl⟩⟩ : ↥Q₁) ⟨ψ b, hmem₁.2 ⟨b, v.2, rfl⟩⟩)
    rw [← map_mul, ← map_mul] at h1
    have h2 : ((a * b : ↥P) : Y) = ((b * a : ↥P) : Y) := congrArg Subtype.val (hinj h1)
    exact Subtype.ext h2
  have hexp : ∀ q ∈ Q₁, q ^ p = 1 := by
    intro q hq
    obtain ⟨a, haT, rfl⟩ := hmem₁.1 hq
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using h.pdata.T_exp a haT)
    rw [this, map_one]
  have hcomm : ∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hdD, rfl⟩ := hmem₀.1 ha
    obtain ⟨t, htT, rfl⟩ := hmem₁.1 hb
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (h.pdata.comm t htT d hdD).symm)
  have hdisj : Q₀ ⊓ Q₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨d, hdD, hd⟩ := hmem₀.1 hq.1
    obtain ⟨t, htT, ht⟩ := hmem₁.1 hq.2
    have hdt : d = t := hinj (hd.trans ht.symm)
    have : (d : Y) ∈ T ⊓ D := ⟨hdt ▸ htT, hdD⟩
    rw [h.pdata.inf_eq] at this
    have hd1 : d = 1 := Subtype.ext (Subgroup.mem_bot.1 this)
    rw [← hd, hd1, map_one]
  have hsup : Q₀ ⊔ Q₁ = (Q : Subgroup X) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro q hq
        obtain ⟨a, _, rfl⟩ := hmem₀.1 hq
        rw [← hrange]; exact ⟨a, rfl⟩
      · intro q hq
        obtain ⟨a, _, rfl⟩ := hmem₁.1 hq
        rw [← hrange]; exact ⟨a, rfl⟩
    · intro q hq
      rw [← hrange] at hq
      obtain ⟨a, rfl⟩ := hq
      obtain ⟨t, ht, d, hd, had⟩ := h.exists_mul a a.2
      set t' : ↥P := ⟨t, h.pdata.T_le ht⟩
      set d' : ↥P := ⟨d, h.pdata.D_le hd⟩
      have : a = t' * d' := Subtype.ext had
      rw [this, map_mul, sup_comm]
      exact Subgroup.mul_mem_sup (hmem₁.2 ⟨t', ht, rfl⟩) (hmem₀.2 ⟨d', hd, rfl⟩)
  have hAQ : zpowers (ψ x') ≤ (Q : Subgroup X) :=
    Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩)
  have hAcard : Nat.card (zpowers (ψ x')) = p := by rw [Nat.card_zpowers]; exact hAord
  obtain ⟨g, hg1, hg2⟩ := kFactHeis_p h.three h123 X K hKn hKs hKnab hKcat hKc hKdvd Q hKsup Q₀ Q₁
    hcyc hQ0ne hcard hnab hexp hcomm hdisj hsup (zpowers (ψ x')) hAQ hAcard
  exact hg2 (hwc g hg1)

end Case2Data3


private theorem exists_mul_of_mem_sup {Y : Type} [Group Y] (A C : Subgroup Y)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    ∀ v ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, v = a * c := by
  intro v hv
  rw [Subgroup.sup_eq_closure] at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, C.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    obtain ⟨a', ha', c', hc', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
    have h1 := hcomm a' ha' c hc
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [← h1]
      _ = a * a' * (c * c') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
    have h1 := hcomm a ha c hc
    calc (a * c)⁻¹ = (c * a)⁻¹ := by rw [h1]
      _ = a⁻¹ * c⁻¹ := by group

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem comm_T_zpowers (h : Case2Data3 p P T D F x) :
    ∀ t ∈ T, ∀ c ∈ zpowers x, t * c = c * t := by
  intro t ht c hc
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (show Commute t x from h.pdata.comm t ht x h.pdata.x_mem) j).eq

private theorem commutator_T_eq (h : Case2Data3 p P T D F x) : ⁅T, T⁆ = zOf T := by
  haveI := h.fact
  have hle : ⁅T, T⁆ ≤ zOf T :=
    Subgroup.commutator_le.2 (fun a ha b hb => h.commutator_mem a ha b hb)
  have hne : ⁅T, T⁆ ≠ ⊥ := by
    intro hbot
    apply h.pdata.T_nonab
    refine ⟨⟨fun a b => ?_⟩⟩
    have hab : ⁅(a : Y), (b : Y)⁆ ∈ ⁅T, T⁆ := Subgroup.commutator_mem_commutator a.2 b.2
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact Subtype.ext hab
  have hdvd : Nat.card (⁅T, T⁆ : Subgroup Y) ∣ p := h.zOf_card ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime h.prime).1 hdvd with h1 | h1
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.zOf_card, h1])

private theorem V_exp (h : Case2Data3 p P T D F x) : ∀ v ∈ T ⊔ zpowers x, v ^ p = 1 := by
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.pdata.x_ord] at this
  intro v hv
  obtain ⟨t, ht, c, hc, rfl⟩ := exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers v hv
  rw [Commute.mul_pow (h.comm_T_zpowers t ht c hc), h.pdata.T_exp t ht]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

private theorem V_le_P (h : Case2Data3 p P T D F x) : T ⊔ zpowers x ≤ P :=
  sup_le h.pdata.T_le ((Subgroup.zpowers_le).2 (h.pdata.D_le h.pdata.x_mem))

private theorem pCore_le_P (h : Case2Data3 p P T D F x) : CFSG.pCore p Y ≤ P := by
  haveI := h.fact
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS]
  exact (CFSG.pCore_isPGroup (p := p) (G := Y)).le_sylow_of_normal S

theorem eq_of_complements (h : Case2Data3 p P T D F x) {T' : Subgroup Y}
    (hT'V : T' ≤ T ⊔ zpowers x) (hZT' : zOf T ≤ T') (hT'Λ : T' ⊓ zpowers x = ⊥)
    (hT'Λ' : T' ⊔ zpowers x = T ⊔ zpowers x) (hF : ∀ f ∈ F, ∀ a ∈ T', f * a * f⁻¹ ∈ T') :
    T' = T := by
  haveI := h.fact
  have hcommV : ∀ v ∈ T ⊔ zpowers x, ∀ c ∈ zpowers x, v * c = c * v := by
    intro v hv c hc
    obtain ⟨t, ht, c', hc', rfl⟩ := exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers v hv
    have h2 : c' * c = c * c' := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact (Commute.zpow_zpow_self x j i).eq
    calc t * c' * c = t * (c' * c) := mul_assoc _ _ _
      _ = t * (c * c') := by rw [h2]
      _ = (t * c) * c' := (mul_assoc _ _ _).symm
      _ = (c * t) * c' := by rw [h.comm_T_zpowers t ht c hc]
      _ = c * (t * c') := mul_assoc _ _ _
  have hBinv : ∀ f ∈ F, ∀ a ∈ T ⊓ T', f * a * f⁻¹ ∈ T ⊓ T' :=
    fun f hf a ha => ⟨h.torus.F_T f hf a ha.1, hF f hf a ha.2⟩
  rcases h.torus.irred (T ⊓ T') inf_le_left (le_inf h.zOf_le hZT') hBinv with hB | hB
  ·
    exfalso
    have hX_card : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, h.pdata.x_ord]
    have hXV : ∀ c ∈ zpowers x, c ∈ T ⊔ zpowers x := fun c hc => Subgroup.mem_sup_right hc
    have h1 : T'.relIndex (T ⊔ zpowers x) ≤ p := by
      rw [← hX_card]
      let φ : zpowers x → (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x) :=
        fun c => QuotientGroup.mk ⟨c.1, hXV c.1 c.2⟩
      have hφ : Function.Surjective φ := by
        intro q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : (v : Y) ∈ T' ⊔ zpowers x := by rw [hT'Λ']; exact v.2
        obtain ⟨a, ha, c, hc, hvac⟩ := exists_mul_of_mem_sup T' (zpowers x)
          (fun a ha c hc => hcommV a (hT'V ha) c hc) v hv
        refine ⟨⟨c, hc⟩, ?_⟩
        show (QuotientGroup.mk ⟨c, hXV c hc⟩ : (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x))
          = QuotientGroup.mk v
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hac : a * c = c * a := hcommV a (hT'V ha) c hc
        have hmem : c⁻¹ * (v : Y) ∈ T' := by
          rw [hvac, hac, inv_mul_cancel_left]
          exact ha
        exact hmem
      exact Nat.card_le_card_of_surjective φ hφ
    have hne : T'.relIndex (T ⊔ zpowers x) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card ..) Nat.card_pos).ne'
    have h2 : T'.relIndex T ≤ T'.relIndex (T ⊔ zpowers x) :=
      Subgroup.relIndex_le_of_le_right le_sup_left hne
    have h3 : T'.relIndex T * Nat.card (T' ⊓ T : Subgroup Y) = Nat.card T :=
      Subgroup.relIndex_mul_card T' T
    rw [inf_comm, hB, h.zOf_card, h.pdata.T_card] at h3
    have hp0 : 0 < p := h.prime.pos
    have h4 : T'.relIndex T = p ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hp0
      rw [h3]; ring
    have h5 : p ^ 2 ≤ p := h4 ▸ h2.trans h1
    nlinarith [h.prime.two_le]
  ·
    have hTT' : T ≤ T' := inf_eq_left.1 hB
    refine le_antisymm ?_ hTT'
    intro a ha
    obtain ⟨t, ht, c, hc, rfl⟩ :=
      exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers a (hT'V ha)
    have hc' : c ∈ T' := by
      have := T'.mul_mem (T'.inv_mem (hTT' ht)) ha
      simpa using this
    have hc1 : c ∈ T' ⊓ zpowers x := ⟨hc', hc⟩
    rw [hT'Λ, Subgroup.mem_bot] at hc1
    rw [hc1, mul_one]
    exact ht

theorem V_normal (h : Case2Data3 p P T D F x) (hT : T ≤ CFSG.pCore p Y) (hx : x ∈ CFSG.pCore p Y) :
    ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x := by
  haveI := h.fact
  have key : ∀ v : Y, v ∈ T ⊔ zpowers x ↔ v ∈ CFSG.pCore p Y ∧ v ^ p = 1 := by
    intro v
    constructor
    · intro hv
      exact ⟨(sup_le hT ((Subgroup.zpowers_le).2 hx)) hv, h.V_exp v hv⟩
    · rintro ⟨hvO, hvp⟩
      obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul v (h.pCore_le_P hvO)
      rw [Commute.mul_pow (h.pdata.comm t ht d hd), h.pdata.T_exp t ht, one_mul] at hvp
      exact Subgroup.mul_mem_sup ht (h.mem_zpowers_of_pow_eq_one d hd hvp)
  intro y v hv
  rw [key] at hv ⊢
  obtain ⟨hvO, hvp⟩ := hv
  refine ⟨(CFSG.pCore_normal (p := p) (G := Y)).conj_mem v hvO y, ?_⟩
  rw [conj_pow, hvp]
  simp

theorem zpowers_normal (h : Case2Data3 p P T D F x)
    (hV : ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x) :
    ∀ y : Y, ∀ v ∈ zpowers x, y * v * y⁻¹ ∈ zpowers x := by
  intro y v hv
  have hle : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact h.V_le_P (hV y w (Subgroup.mem_sup_right hw))
  have heq := h.wc y hle
  have hmem : y * v * y⁻¹ ∈ (zpowers x).map (MulAut.conj y).toMonoidHom :=
    ⟨v, hv, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

theorem zOf_normal (h : Case2Data3 p P T D F x)
    (hV : ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x) :
    ∀ y : Y, ∀ z ∈ zOf T, y * z * y⁻¹ ∈ zOf T := by
  haveI : (T ⊔ zpowers x).Normal := ⟨fun v hv y => hV y v hv⟩
  have hVV : ⁅T ⊔ zpowers x, T ⊔ zpowers x⁆ = zOf T := by
    apply le_antisymm
    · exact Subgroup.commutator_le.2
        (fun a ha b hb => h.commutator_P (h.V_le_P ha) (h.V_le_P hb))
    · rw [← h.commutator_T_eq]
      exact Subgroup.commutator_mono le_sup_left le_sup_left
  intro y z hz
  have hz' : z ∈ ⁅T ⊔ zpowers x, T ⊔ zpowers x⁆ := hVV ▸ hz
  have := (Subgroup.commutator_normal (T ⊔ zpowers x) (T ⊔ zpowers x)).conj_mem z hz' y
  rwa [hVV] at this

theorem normal_of_le_pCore (h : Case2Data3 p P T D F x) (hT : T ≤ CFSG.pCore p Y) :
    ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  haveI := h.fact
  by_cases hx : x ∈ CFSG.pCore p Y
  ·
    obtain ⟨S, hS⟩ := h.sylow
    have hV := h.V_normal hT hx
    have hΛ := h.zpowers_normal hV
    have hZ := h.zOf_normal hV
    haveI hVn : (T ⊔ zpowers x).Normal := ⟨fun v hv y => hV y v hv⟩
    haveI hΛn : (zpowers x).Normal := ⟨fun v hv y => hΛ y v hv⟩
    haveI hZn : (zOf T).Normal := ⟨fun v hv y => hZ y v hv⟩
    obtain ⟨T', hT'n, hZT', hT'V, hT'Λ, hT'sup⟩ :=
      exists_normal_complement h.prime S (T ⊔ zpowers x) (zpowers x) (zOf T) hVn hΛn hZn
        le_sup_right (h.zOf_le.trans le_sup_left)
        (fun a ha b hb => h.commutator_P (h.V_le_P ha) (h.V_le_P hb))
        h.V_exp
        (fun s hs v hv => h.commutator_P (hS ▸ hs) (h.V_le_P hv))
        (by rw [Nat.card_zpowers, h.pdata.x_ord])
        (by
          rw [eq_bot_iff]
          intro v hv
          have hvT : v ∈ T ⊓ zpowers x := ⟨h.zOf_le hv.2, hv.1⟩
          rw [h.T_inf_zpowers] at hvT
          exact hvT)
    have hTT' : T' = T :=
      h.eq_of_complements hT'V hZT' hT'Λ hT'sup (fun f _ a ha => hT'n.conj_mem a ha f)
    rw [← hTT']
    intro y t ht
    exact hT'n.conj_mem t ht y
  ·
    have hbot : CFSG.pCore p Y ⊓ D = ⊥ := by
      by_contra hne
      exact hx (h.x_mem_of_ne_bot (CFSG.pCore p Y ⊓ D) inf_le_right hne).1
    have hOT : CFSG.pCore p Y ≤ T := by
      intro o ho
      obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul o (h.pCore_le_P ho)
      have hd' : d ∈ CFSG.pCore p Y := by
        have := (CFSG.pCore p Y).mul_mem ((CFSG.pCore p Y).inv_mem (hT ht)) ho
        simpa using this
      have hd1 : d ∈ CFSG.pCore p Y ⊓ D := ⟨hd', hd⟩
      rw [hbot, Subgroup.mem_bot] at hd1
      rw [hd1, mul_one]
      exact ht
    intro y t ht
    exact hOT ((CFSG.pCore_normal (p := p) (G := Y)).conj_mem t (hT ht) y)

end Case2Data3

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem cc_mem_zOf {z : Y} : z ∈ zOf T ↔ z ∈ T ∧ ∀ g ∈ T, g * z = z * g := by
  unfold zOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

private theorem cc_conj_mem_centralizer {L : Subgroup Y} {g c : Y}
    (hg : g ∈ normalizer (L : Set Y)) (hc : c ∈ centralizer (L : Set Y)) :
    g * c * g⁻¹ ∈ centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hm : g⁻¹ * l * g ∈ (L : Set Y) := by
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * l * g)).mpr ?_
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
    exact hl
  have key := hc (g⁻¹ * l * g) hm
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * l := by group

private theorem cc_aux (h : Case2Data3 p P T D F x) {C : Subgroup Y} (hCle : C ≤ P)
    (hCP : ∀ q ∈ P, ∀ c ∈ C, q * c * q⁻¹ ∈ C) (hCF : ∀ f ∈ F, ∀ c ∈ C, f * c * f⁻¹ ∈ C)
    (hxC : x ∉ C) (hTC : ¬ T ≤ C) : C = ⊥ ∨ C = zOf T := by
  have hCD : C ⊓ D = ⊥ := by
    by_contra hne
    exact hxC (h.x_mem_of_ne_bot (C ⊓ D) inf_le_right hne).1
  have hTP : T ≤ P := h.pdata.T_le
  have hnorm : ∀ t ∈ T, ∀ a ∈ C ⊓ T, t * a * t⁻¹ ∈ C ⊓ T := by
    intro t ht a ha
    exact Subgroup.mem_inf.mpr ⟨hCP t (hTP ht) a (Subgroup.mem_inf.mp ha).1,
      T.mul_mem (T.mul_mem ht (Subgroup.mem_inf.mp ha).2) (T.inv_mem ht)⟩
  have hA : C ⊓ T = ⊥ ∨ C ⊓ T = zOf T := by
    by_cases hA0 : C ⊓ T = ⊥
    · exact Or.inl hA0
    · right
      haveI := h.fact
      haveI : Group.IsNilpotent (↥T) := (IsPGroup.of_card (p := p) h.pdata.T_card).isNilpotent
      haveI : ((C ⊓ T).subgroupOf T).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hnorm _ g.2 _ hn⟩
      have hAne : (C ⊓ T).subgroupOf T ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr inf_le_right]
        exact hA0
      have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥T) hAne
      have hK : (C ⊓ T) ⊓ zOf T ≠ ⊥ := by
        intro hK0
        apply hcen
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hzA, hzc⟩ := Subgroup.mem_inf.mp hz
        have hzY : (z : Y) ∈ (C ⊓ T) ⊓ zOf T := by
          refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hzA,
            cc_mem_zOf.mpr ⟨z.2, fun g hg => ?_⟩⟩
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩)
        rw [hK0, Subgroup.mem_bot] at hzY
        rw [Subgroup.mem_bot]
        exact Subtype.ext hzY
      have hzle : zOf T ≤ C ⊓ T := by
        have hdvd : Nat.card ((C ⊓ T) ⊓ zOf T : Subgroup Y) ∣ Nat.card (zOf T) :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [h.zOf_card] at hdvd
        rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hK
        · have heq : (C ⊓ T) ⊓ zOf T = zOf T :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h.zOf_card, h1]))
          rw [← heq]
          exact inf_le_left
      rcases h.torus.irred (C ⊓ T) inf_le_right hzle (fun f hf a ha =>
          Subgroup.mem_inf.mpr ⟨hCF f hf a (Subgroup.mem_inf.mp ha).1,
            h.torus.F_T f hf a (Subgroup.mem_inf.mp ha).2⟩) with h1 | h1
      · exact h1
      · exfalso
        apply hTC
        intro t ht
        have htC : t ∈ C ⊓ T := by
          rw [h1]
          exact ht
        exact (Subgroup.mem_inf.mp htC).1
  have hkey : ∀ t ∈ T, ∀ d ∈ D, ∀ f ∈ F,
      t⁻¹ * (f * t * f⁻¹) = (t * d)⁻¹ * (f * (t * d) * f⁻¹) := by
    intro t ht d hd f hf
    have hfd : f * d * f⁻¹ = d := h.F_D f hf d hd
    have hcomm : (t⁻¹ * (f * t * f⁻¹)) * d = d * (t⁻¹ * (f * t * f⁻¹)) :=
      h.pdata.comm _ (T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)) d hd
    calc t⁻¹ * (f * t * f⁻¹) = d⁻¹ * (d * (t⁻¹ * (f * t * f⁻¹))) := by group
      _ = d⁻¹ * ((t⁻¹ * (f * t * f⁻¹)) * d) := by rw [hcomm]
      _ = (t * d)⁻¹ * (f * (t * d) * f⁻¹) := by
        rw [show f * (t * d) * f⁻¹ = (f * t * f⁻¹) * (f * d * f⁻¹) by group, hfd]
        group
  have hZ : ∀ c ∈ C, ∀ t ∈ T, ∀ d ∈ D, c = t * d → t ∈ zOf T := by
    intro c hc t ht d hd hcd
    have hw : ∀ f ∈ F, t⁻¹ * (f * t * f⁻¹) ∈ zOf T := by
      intro f hf
      have hwC : t⁻¹ * (f * t * f⁻¹) ∈ C := by
        rw [hkey t ht d hd f hf, ← hcd]
        exact C.mul_mem (C.inv_mem hc) (hCF f hf c hc)
      have hwT : t⁻¹ * (f * t * f⁻¹) ∈ T := T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)
      have hwCT : t⁻¹ * (f * t * f⁻¹) ∈ C ⊓ T := Subgroup.mem_inf.mpr ⟨hwC, hwT⟩
      rcases hA with h0 | h0
      · rw [h0, Subgroup.mem_bot] at hwCT
        rw [hwCT]
        exact (zOf T).one_mem
      · rw [h0] at hwCT
        exact hwCT
    apply h.torus.fpf t ht
    intro f hf
    have hw' := hw f hf
    have hcomm : t * (t⁻¹ * (f * t * f⁻¹)) = (t⁻¹ * (f * t * f⁻¹)) * t :=
      (cc_mem_zOf.mp hw').2 t ht
    have hfix : f * t * f⁻¹ * t⁻¹ = t⁻¹ * (f * t * f⁻¹) := by
      calc f * t * f⁻¹ * t⁻¹ = t * (t⁻¹ * (f * t * f⁻¹)) * t⁻¹ := by group
        _ = (t⁻¹ * (f * t * f⁻¹)) * t * t⁻¹ := by rw [hcomm]
        _ = t⁻¹ * (f * t * f⁻¹) := by group
    rw [hfix]
    exact hw'
  rcases hA with h0 | h0
  · left
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨t, ht, d, hd, hcd⟩ := h.exists_mul c (hCle hc)
    have htZ := hZ c hc t ht d hd hcd
    have hfix : ∀ f ∈ F, f * t * f⁻¹ = t := by
      intro f hf
      have hw : t⁻¹ * (f * t * f⁻¹) ∈ C ⊓ T := by
        refine Subgroup.mem_inf.mpr ⟨?_, T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)⟩
        rw [hkey t ht d hd f hf, ← hcd]
        exact C.mul_mem (C.inv_mem hc) (hCF f hf c hc)
      rw [h0, Subgroup.mem_bot] at hw
      calc f * t * f⁻¹ = t * (t⁻¹ * (f * t * f⁻¹)) := by group
        _ = t := by rw [hw, mul_one]
    have ht1 : t = 1 := h.F_fixed t htZ hfix
    have hcD : c ∈ C ⊓ D := Subgroup.mem_inf.mpr ⟨hc, by rw [hcd, ht1, one_mul]; exact hd⟩
    rw [hCD, Subgroup.mem_bot] at hcD
    exact Subgroup.mem_bot.mpr hcD
  · right
    apply le_antisymm
    · intro c hc
      obtain ⟨t, ht, d, hd, hcd⟩ := h.exists_mul c (hCle hc)
      have htZ := hZ c hc t ht d hd hcd
      have htC : t ∈ C := by
        have htCT : t ∈ C ⊓ T := by
          rw [h0]
          exact htZ
        exact (Subgroup.mem_inf.mp htCT).1
      have hdC : d ∈ C := by
        have hde : d = t⁻¹ * c := by rw [hcd, inv_mul_cancel_left]
        rw [hde]
        exact C.mul_mem (C.inv_mem htC) hc
      have hdCD : d ∈ C ⊓ D := Subgroup.mem_inf.mpr ⟨hdC, hd⟩
      rw [hCD, Subgroup.mem_bot] at hdCD
      have hct : c = t := by rw [hcd, hdCD, mul_one]
      rw [hct]
      exact htZ
    · rw [← h0]
      exact inf_le_left

theorem centralizer_cases (h : Case2Data3 p P T D F x) (hInn : KFactInnerAction)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hTL : ¬ T ≤ centralizer (L : Set Y)) :
    P ⊓ centralizer (L : Set Y) = ⊥ ∨ P ⊓ centralizer (L : Set Y) = zOf T := by
  have hPN : P ≤ normalizer (L : Set Y) := h.P_le_normalizer hL
  refine cc_aux (C := P ⊓ centralizer (L : Set Y)) h inf_le_left ?_ ?_ ?_ ?_
  · intro q hq c hc
    exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hq (Subgroup.mem_inf.mp hc).1) (P.inv_mem hq),
      cc_conj_mem_centralizer (hPN hq) (Subgroup.mem_inf.mp hc).2⟩
  · intro f hf c hc
    exact Subgroup.mem_inf.mpr ⟨h.F_mem_normalizer_P f hf c (Subgroup.mem_inf.mp hc).1,
      cc_conj_mem_centralizer (h.F_mem_normalizer hInn hL hf) (Subgroup.mem_inf.mp hc).2⟩
  · intro hx
    apply h.not_le_centralizer_x hL
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl).symm
  · intro hT
    exact hTL (fun t ht => (Subgroup.mem_inf.mp (hT ht)).2)

end Case2Data3

theorem case2_core3 {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}
    (h : Case2Data3 p P T D F x) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h123 : KFactWeakClosureHeisThree) : ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  have hT : T ≤ CFSG.pCore p Y := by
    by_contra hnot
    have hex : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ¬ T ≤ centralizer (L : Set Y) := by
      by_contra hne
      push Not at hne
      exact hnot (h.le_pCore_of_forall_le_centralizer hne)
    obtain ⟨L, hL, hTL⟩ := hex
    rcases h.centralizer_cases hInn hL hTL with hC | hC
    · exact h.false_of_faithful h123 hL hC
    · exact h.false_of_abelian (kFactWeakClosureRank2_of hInn hWC) hL hC
  exact h.normal_of_le_pCore hT

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux
