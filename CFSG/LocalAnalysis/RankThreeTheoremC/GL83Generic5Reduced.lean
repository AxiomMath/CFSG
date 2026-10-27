module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding

private theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [← hZ, mem_center_iff]
  intro m
  have h1 : k * m * k⁻¹ = m := by
    have := congrArg (fun φ : MulAut K => φ m) (MonoidHom.mem_ker.mp hk)
    simpa using this
  calc m * k = k * m * k⁻¹ * k := by rw [h1]
    _ = k * m := by group

namespace GL83Generic5CaseIIHyp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {L U : Subgroup Y} {x : Y}

theorem le_of_not_le_centralizer (h : GL83Generic5CaseIIHyp p L U x) {K : Subgroup Y}
    (hZ : center K = ⊥)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer K))
    (hLN : L ≤ normalizer (K : Set Y)) (hLC : ¬ L ≤ centralizer (K : Set Y)) : L ≤ K := by
  have := h.isSimpleGroup
  have := h.isPerfect
  let α : L →* MulAut K := K.normalizerMonoidHom.comp (inclusion hLN)
  have hα : ∀ (l : L) (k : K), ((α l k : K) : Y) = l * k * (l : Y)⁻¹ := fun _ _ => rfl
  have hinj := conj_injective_of_center_eq_bot hZ
  have hrange : ∀ l : L, α l ∈ (MulAut.conj : K →* MulAut K).range := fun l => by
    obtain ⟨k, hk⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner α l
    exact ⟨k, hk.symm⟩
  let ν : L →* K := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (α.codRestrict _ hrange)
  have hν : ∀ l : L, MulAut.conj (ν l) = α l := fun l =>
    MonoidHom.apply_ofInjective_symm hinj _
  have hνk : ∀ (l : L) (k : K), (ν l : Y) * k * (ν l : Y)⁻¹ = l * k * (l : Y)⁻¹ := fun l k => by
    rw [← hα, ← hν]
    rfl
  have hνinj : Function.Injective ν := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ν.ker with h1 | h1
    · exact (MonoidHom.ker_eq_bot_iff ν).mp h1
    · exfalso
      refine hLC fun l hl => mem_centralizer_iff.mpr fun k hk => ?_
      have h2 : ν ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h1]
        exact mem_top _
      have h3 := hνk ⟨l, hl⟩ ⟨k, hk⟩
      rw [h2] at h3
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h3
      calc k * l = l * k * l⁻¹ * l := by rw [← h3]
        _ = l * k := by group
  have hKL : (K.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.mp (hLN g.2) n).mp hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf L) with h1 | h1
  · exfalso
    have hLK : K ⊓ L = ⊥ := by rw [← subgroupOf_map_subtype, h1, Subgroup.map_bot]
    have hU' : IsElemAbelian p (U.subgroupOf L) :=
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext (h.commute_of_mem a.2 b.2)),
        fun a ha => Subtype.ext (by rw [coe_pow, coe_one]; exact h.isElemAbelian.2 _ ha)⟩
    have hφinj : Function.Injective (K.subtype.comp ν) := K.subtype_injective.comp hνinj
    have hV := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hU' (K.subtype.comp ν)
    have hVc : Nat.card ((U.subgroupOf L).map (K.subtype.comp ν)) = p ^ 2 := by
      rw [card_map_of_injective hφinj, ← h.card_eq]
      exact Nat.card_congr (subgroupOfEquivOfLe h.sylow.le).toEquiv
    have hcomm : ∀ a ∈ U, ∀ b ∈ (U.subgroupOf L).map (K.subtype.comp ν), a * b = b * a := by
      rintro a ha _ ⟨u, hu, rfl⟩
      have hau : (⟨a, h.sylow.le ha⟩ : L) * u = u * ⟨a, h.sylow.le ha⟩ :=
        Subtype.ext (h.commute_of_mem ha hu)
      have h2 := hνk ⟨a, h.sylow.le ha⟩ (ν u)
      have h3 : (ν ⟨a, h.sylow.le ha⟩ : Y) * (ν u : Y) * (ν ⟨a, h.sylow.le ha⟩ : Y)⁻¹ =
          (ν u : Y) := by
        rw [← coe_mul, ← coe_inv, ← coe_mul, ← map_inv, ← map_mul, ← map_mul, hau,
          mul_inv_cancel_right]
      rw [h3] at h2
      change a * (ν u : Y) = (ν u : Y) * a
      calc a * (ν u : Y) = a * (ν u : Y) * a⁻¹ * a := by group
        _ = (ν u : Y) * a := by rw [← h2]
    have hdisj : Disjoint U ((U.subgroupOf L).map (K.subtype.comp ν)) := by
      refine disjoint_def.mpr fun {z} hu hv => ?_
      have hzK : z ∈ K := by
        obtain ⟨u, -, rfl⟩ := hv
        exact (ν u).2
      have : z ∈ K ⊓ L := ⟨hzK, h.sylow.le hu⟩
      rwa [hLK, mem_bot] at this
    have h4 := add_le_pRank_of_commute (P := ⊤) h.isElemAbelian hV h.card_eq hVc hcomm hdisj
      le_top le_top
    have := h.pRank_le
    omega
  · exact subgroupOf_eq_top.mp h1

theorem exists_sylow_isSylowOf_inf (h : GL83Generic5CaseIIHyp p L U x) {K : Subgroup Y}
    (hLK : L ≤ K) (hxN : x ∈ normalizer (K : Set Y)) :
    ∃ Q : Sylow p Y, x ∈ (Q : Subgroup Y) ∧ U ≤ (Q : Subgroup Y) ∧
      IsSylowOf p ((Q : Subgroup Y) ⊓ K) K := by
  have hUx : U ≤ centralizer ((zpowers x : Subgroup Y) : Set Y) :=
    le_centralizer_iff.mpr (zpowers_le.mpr (Subgroup.centralizer_le h.sylow.le h.mem_centralizer))
  have hE : IsPGroup p (U ⊔ zpowers x : Subgroup Y) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.isElemAbelian
        (isElemAbelian_zpowers h.pow_eq_one) hUx)
  have hEN : U ⊔ zpowers x ≤ normalizer (K : Set Y) :=
    sup_le ((h.sylow.le.trans hLK).trans le_normalizer) (zpowers_le.mpr hxN)
  obtain ⟨S, hS⟩ := (hE.comap_subtype (K := normalizer (K : Set Y))).exists_le_sylow
  have hSsyl : IsSylowOf p ((S : Subgroup (normalizer (K : Set Y))).map
      (normalizer (K : Set Y)).subtype) (normalizer (K : Set Y)) := ⟨S, rfl⟩
  have hES : U ⊔ zpowers x ≤ (S : Subgroup (normalizer (K : Set Y))).map
      (normalizer (K : Set Y)).subtype :=
    (map_subgroupOf_eq_of_le hEN).ge.trans (map_mono (f := (normalizer (K : Set Y)).subtype) hS)
  obtain ⟨Q, hQ⟩ := hSsyl.isPGroup.exists_le_sylow
  have hSK := hSsyl.inf_of_le_normalizer le_normalizer le_rfl
  have hQK : (Q : Subgroup Y) ⊓ K = (S : Subgroup (normalizer (K : Set Y))).map
      (normalizer (K : Set Y)).subtype ⊓ K :=
    hSK.eq_of_le (inf_le_inf_right K hQ) inf_le_right (Q.isPGroup'.to_le inf_le_left)
  refine ⟨Q, hQ (hES (mem_sup_right (mem_zpowers x))), (le_sup_left.trans hES).trans hQ, ?_⟩
  rw [hQK]
  exact hSK

omit [Fact p.Prime] [Finite Y] in
private theorem mem_sylow_iff {K : Subgroup Y} {Q : Subgroup Y} {P : Sylow p K}
    (hP : (P : Subgroup K).map K.subtype = Q ⊓ K) (k : K) : k ∈ (P : Subgroup K) ↔ (k : Y) ∈ Q := by
  constructor
  · intro hk
    have : (k : Y) ∈ (P : Subgroup K).map K.subtype := mem_map_of_mem _ hk
    rw [hP] at this
    exact this.1
  · intro hk
    have : (k : Y) ∈ Q ⊓ K := ⟨hk, k.2⟩
    rw [← hP] at this
    obtain ⟨k', hk', hkk'⟩ := this
    rwa [← Subtype.ext hkk']

theorem not_mem_of_le (h : GL83Generic5CaseIIHyp p L U x) (hWC : KFactWeakClosure)
    {K : Subgroup Y} (hsimple : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) (hZ : center K = ⊥) (hLK : L ≤ K) {Q : Sylow p Y}
    (hxQ : x ∈ (Q : Subgroup Y)) (hUQ : U ≤ (Q : Subgroup Y))
    (hQK : IsSylowOf p ((Q : Subgroup Y) ⊓ K) K) : x ∉ K := by
  intro hxK
  obtain ⟨P, hP⟩ := hQK
  have hmem := mem_sylow_iff hP
  have hUK : U ≤ K := h.sylow.le.trans hLK
  have hU' : IsElemAbelian p (U.subgroupOf K) :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext (h.commute_of_mem a.2 b.2)),
      fun a ha => Subtype.ext (by rw [coe_pow, coe_one]; exact h.isElemAbelian.2 _ ha)⟩
  have hU'c : Nat.card (U.subgroupOf K) = p ^ 2 := by
    rw [← h.card_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv
  have hU'P : U.subgroupOf K ≤ (P : Subgroup K) := fun u hu => (hmem u).mpr (hUQ hu)
  have : IsSimpleGroup K := hsimple
  obtain ⟨g, hg1, hg2⟩ := hWC p h.prime h.ne_two K ⊤ inferInstance
    (Subgroup.topEquiv.isSimpleGroup)
    (by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun hba => hab (congrArg Subtype.val hba)⟩)
    (IsCatalogGroup.of_mulEquiv Subgroup.topEquiv hcat)
    (by rw [coe_top, centralizer_univ, hZ])
    (by
      rw [card_top]
      exact (show p ∣ Nat.card U by rw [h.card_eq]; exact dvd_pow_self p two_ne_zero).trans
        (card_dvd_of_le hUK))
    P (top_sup_eq _)
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (h.commute_of_mem_sylow Q ((hmem a).mp a.2) ((hmem b).mp b.2))))
    (by
      rw [inf_top_eq]
      exact le_pRank_of_elemAbelian_card hU'P hU' hU'c)
    (zpowers ⟨x, hxK⟩) (zpowers_le.mpr ((hmem _).mpr hxQ))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_eq])
  apply hg2
  have hmapK : ∀ A : Subgroup K, (A.map K.subtype).map (MulAut.conj (g : Y)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map K.subtype := fun A => by
    rw [map_map, map_map]
    congr 1
  apply map_injective K.subtype_injective
  have h3 : (zpowers ⟨x, hxK⟩ : Subgroup K).map K.subtype = zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← hmapK, h3]
  refine h.weakClosed Q hxQ g ?_
  rw [← h3, hmapK]
  exact (map_mono hg1).trans ((map_le_iff_le_comap.mpr fun k hk => (hmem k).mp hk))

theorem le_centralizer_of_le (h : GL83Generic5CaseIIHyp p L U x) (hInn : KFactInnerAction)
    {K : Subgroup Y} (hsimple : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) (hZ : center K = ⊥) (hLK : L ≤ K)
    (hxN : x ∈ normalizer (K : Set Y)) {Q : Sylow p Y} (hxQ : x ∈ (Q : Subgroup Y))
    (hUQ : U ≤ (Q : Subgroup Y)) (hQK : IsSylowOf p ((Q : Subgroup Y) ⊓ K) K) (hxK : x ∉ K) :
    K ≤ centralizer ({x} : Set Y) := by
  obtain ⟨P, hP⟩ := hQK
  have hmem := mem_sylow_iff hP
  set φ : MulAut K := K.normalizerMonoidHom ⟨x, hxN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : Y) = x * k * x⁻¹ := fun _ => rfl
  have hφp : φ ^ p = 1 := by
    have h1 : (⟨x, hxN⟩ : normalizer (K : Set Y)) ^ p = 1 :=
      Subtype.ext (by rw [coe_pow, coe_one]; exact h.pow_eq_one)
    rw [hφdef, ← map_pow, h1, map_one]
  have hPne : (P : Subgroup K) ≠ ⊥ := by
    intro hbot
    apply h.ne_bot
    refine eq_bot_iff.mpr fun u hu => ?_
    have h1 : (⟨u, h.sylow.le.trans hLK hu⟩ : K) ∈ (P : Subgroup K) := (hmem _).mpr (hUQ hu)
    rw [hbot, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  obtain ⟨g, hgP, hg⟩ := hInn p h.prime h.ne_two K hsimple hnonab hcat P hPne
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (h.commute_of_mem_sylow Q ((hmem a).mp a.2) ((hmem b).mp b.2))))
    φ ⟨1, by rw [pow_one, hφp]⟩
    (fun g hg => by
      have hxg : x * (g : Y) = g * x := h.commute_of_mem_sylow Q hxQ ((hmem g).mp hg)
      ext m
      change x * ((g : Y) * m * (g : Y)⁻¹) * x⁻¹ = (g : Y) * (x * m * x⁻¹) * (g : Y)⁻¹
      calc x * ((g : Y) * m * (g : Y)⁻¹) * x⁻¹ = (x * g) * m * (x * g)⁻¹ := by group
        _ = (g * x) * m * (g * x)⁻¹ := by rw [hxg]
        _ = (g : Y) * (x * m * x⁻¹) * (g : Y)⁻¹ := by group)
  have hgφ : ∀ k : K, x * k * x⁻¹ = (g : Y) * k * (g : Y)⁻¹ := fun k => by
    rw [← hφ, hg]
    rfl
  have hgL : (g : Y) ∈ centralizer (L : Set Y) := mem_centralizer_iff.mpr fun l hl => by
    have h1 := hgφ ⟨l, hLK hl⟩
    have hxl : x * l * x⁻¹ = l := by
      rw [← mem_centralizer_iff.mp h.mem_centralizer l hl, mul_inv_cancel_right]
    change x * l * x⁻¹ = (g : Y) * l * (g : Y)⁻¹ at h1
    rw [hxl] at h1
    calc l * (g : Y) = (g : Y) * l * (g : Y)⁻¹ * g := by rw [← h1]
      _ = g * l := by group
  have hgp : (g : Y) ^ p = 1 := by
    have h1 : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, ← hg, hφp, map_one]
    have h2 := conj_injective_of_center_eq_bot hZ h1
    rw [← coe_pow, h2, coe_one]
  have hgx := h.mem_zpowers_of_mem_centralizer hgL hgp
    (h.commute_of_mem_sylow Q ((hmem g).mp hgP) hxQ)
  have hg1 : g = 1 := by
    by_contra hg1
    have hg1' : (g : Y) ≠ 1 := fun h1 => hg1 (Subtype.ext h1)
    have heq : zpowers (g : Y) = zpowers x := eq_of_le_of_card_ge (zpowers_le.mpr hgx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_eq, orderOf_eq_prime hgp hg1'])
    exact hxK (zpowers_le.mpr g.2 (heq ▸ mem_zpowers x))
  intro k hk
  rw [mem_centralizer_singleton_iff]
  have h1 := hgφ ⟨k, hk⟩
  rw [hg1] at h1
  change x * k * x⁻¹ = 1 * k * 1⁻¹ at h1
  rw [one_mul, inv_one, mul_one] at h1
  calc k * x = x * k * x⁻¹ * x := by rw [h1]
    _ = x * k := by group

theorem eq_of_le (h : GL83Generic5CaseIIHyp p L U x) (hWC : KFactWeakClosure)
    (hInn : KFactInnerAction) {K : Subgroup Y} (hK : IsComponentOf K ⊤) (hZ : center K = ⊥)
    (hLK : L ≤ K) : K = L := by
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat : IsCatalogGroup K := h.catalog.simple_subgroup K hsimple hnonab
  have hxN : x ∈ normalizer (K : Set Y) := mem_normalizer_of_isComponentOf_of_pow_eq_one h.prime
    h.five_le h.core_eq_bot h.pRank_le hK h.pow_eq_one
  obtain ⟨Q, hxQ, hUQ, hQK⟩ := h.exists_sylow_isSylowOf_inf hLK hxN
  have hxK := h.not_mem_of_le hWC hsimple hnonab hcat hZ hLK hxQ hUQ hQK
  have hKx := h.le_centralizer_of_le hInn hsimple hnonab hcat hZ hLK hxN hxQ hUQ hQK hxK
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  exact le_antisymm (h.perfect_le K hKx Subgroup.commutator_eq_self) hLK

theorem map_conj_eq_of_pCore_eq_bot (h : GL83Generic5CaseIIHyp p L U x)
    (hSch : KFactCatalogSchreier) (hWC : KFactWeakClosure) (hInn : KFactInnerAction)
    (hR : CFSG.pCore p Y = ⊥) (g : Y) : L.map (MulAut.conj g).toMonoidHom = L := by
  have hCE := centralizer_layer_eq_bot_of_pCore_eq_bot h.core_eq_bot hR
  obtain ⟨K, hK, hLC⟩ := h.exists_isComponentOf_not_le_centralizer hCE
  have hZ := center_eq_bot_of_centralizer_layer_eq_bot hCE hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hLK := h.le_of_not_le_centralizer hZ
    (hSch K hsimple hnonab (h.catalog.simple_subgroup K hsimple hnonab))
    (h.le_normalizer_of_isComponentOf hK) hLC
  have hKL := h.eq_of_le hWC hInn hK hZ hLK
  rw [hKL] at hK
  exact h.map_conj_eq_of_isComponentOf hK g

end GL83Generic5CaseIIHyp

theorem gl83Generic5CaseII_holds : GL83Generic5CaseII := by
  intro hSch hWC hInn p _ hp5 Y _ _ hcore hcat L U e hU hrank hab x hx1 hxp hxL hCN hperf hweak
    W hcop hN
  have h : GL83Generic5CaseIIHyp p L U x :=
    ⟨hp5, hcore, hcat, ⟨e⟩, hU, hrank, hab, hx1, hxp, hxL, hCN, hperf, hweak⟩
  refine h.le_centralizer_of_normal (fun g => ?_) hcop hN
  by_cases hR : CFSG.pCore p Y = ⊥
  · exact h.map_conj_eq_of_pCore_eq_bot hSch hWC hInn hR g
  · exact h.map_conj_eq_of_pCore_ne_bot hR g

end CFSG.LocalAnalysis.RankThreeTheoremC
