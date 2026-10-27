module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXConfig

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace BaseConfig

variable {Y : Subgroup X} {e v : X}

theorem orderOf_eq_four (hc : BaseConfig Y e) (hv : v * v = e) : orderOf v = 4 := by
  have he1 : e ≠ 1 := fun h1 => by
    have h2 := hc.order
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have h4 : orderOf v = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hv]
      exact he1
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hv, hc.mul_self]
  rw [h4]
  norm_num

theorem isPGroup_zpowers (hc : BaseConfig Y e) (hv : v * v = e) :
    IsPGroup 2 (Subgroup.zpowers v) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hc.orderOf_eq_four hv]; norm_num)

theorem mem_twoCore_of_sq (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) : v ∈ CFSG.Open.pCore 2 X :=
  TheoremC.le_twoCore hvn (hc.isPGroup_zpowers hv) (Subgroup.mem_zpowers v)

theorem mem_sylow_of_sq (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (P : Sylow 2 X) : v ∈ (P : Subgroup X) :=
  twoCore_le_sylow P (hc.mem_twoCore_of_sq hv hvn)

omit [Finite X] in
theorem mem_centralizer_iff_le {K : Subgroup X} :
    v ∈ Subgroup.centralizer (K : Set X) ↔ K ≤ Subgroup.centralizer ({v} : Set X) := by
  constructor
  · intro h k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h k hk)
  · intro h
    exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (h hk)

theorem mem_centralizer_component (hvn : (Subgroup.zpowers v).Normal)
    {L : Subgroup X} (hL : CFSG.IsComponent L) : v ∈ Subgroup.centralizer (L : Set X) := by
  have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L
    (Subgroup.zpowers v) ((CFSG.isComponent_iff_open L).mp hL)
    (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hvn.isSubnormal)
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hle hl) v (Subgroup.mem_zpowers v)).symm

theorem not_isCyclic_sylow_inf (hc : BaseConfig Y e) (P : Sylow 2 X) {L : Subgroup X}
    (hL : CFSG.IsComponent L) : ¬ IsCyclic ((P : Subgroup X) ⊓ L : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.2
  have : Group.IsPerfect L := hL.1.1
  have hnc := CFSG.LocalAnalysis.ComponentInitial.perfect_even_sylow_noncyclic
    (even_card_component hc.oddCore_eq_bot hL) S
  intro hcyc
  rw [← hS] at hcyc
  exact hnc (isCyclic_of_injective ((S : Subgroup L).equivMapOfInjective L.subtype
    L.subtype_injective).toMonoidHom (MulEquiv.injective _))

theorem two_le_pRank_sup (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (P : Sylow 2 X) {L : Subgroup X}
    (hL : CFSG.IsComponent L) :
    2 ≤ CFSG.Open.pRank 2 (((P : Subgroup X) ⊓ L) ⊔ Subgroup.zpowers v) := by
  set R := ((P : Subgroup X) ⊓ L) ⊔ Subgroup.zpowers v with hR
  have hRP : R ≤ (P : Subgroup X) :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr (hc.mem_sylow_of_sq hv hvn P))
  have hR2 : IsPGroup 2 R := P.isPGroup'.to_le hRP
  have hvR : v ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hRC : R ≤ Subgroup.centralizer ({v} : Set X) := by
    refine sup_le (inf_le_right.trans (mem_centralizer_iff_le.mp
      (mem_centralizer_component hvn hL))) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hvZ : (⟨v, hvR⟩ : R) ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun r =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hRC r.2))
  by_contra hlt
  have hrank : twoRank R ≤ 1 := by
    rw [twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      (by decide)]
    omega
  by_cases hab : ∃ a b : R, a * b ≠ b * a
  · have hZ := CFSG.TwoRankLowerBound.Helpers.center_card_eq_two_of_nonabelian_rank_one_two_group
      R hR2 hrank hab
    have hle := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hvZ)
    rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk, hc.orderOf_eq_four hv] at hle
    omega
  · push Not at hab
    let : CommGroup R := { (inferInstance : Group R) with mul_comm := hab }
    have hcyc := CFSG.TwoRankLowerBound.Helpers.abelian_rank_one_two_group_isCyclic R hR2 hrank
    have : IsCyclic R := hcyc
    exact hc.not_isCyclic_sylow_inf P hL
      (Subgroup.isCyclic_of_le (le_sup_left : (P : Subgroup X) ⊓ L ≤ R))

theorem exists_component (hc : BaseConfig Y e) (hrank : 3 ≤ twoRank X) :
    ∃ L : Subgroup X, CFSG.IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hlayer : CFSG.layer X = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun L hL => ?_)
    exact absurd hL (hno L)
  obtain ⟨P, -, hcore⟩ := hc.sylow
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 2
    hc.oddCore_eq_bot hlayer
  have htop := characteristic_two_rank_three_full_core hchar hrank P
  rw [htop] at hcore
  exact hc.ne_top (top_le_iff.mp hcore)

omit [Finite X] in
theorem layer_normal : (CFSG.layer X).Normal := by
  rw [CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.normal X

theorem exists_component_not_le (hc : BaseConfig Y e) (hrank : 3 ≤ twoRank X)
    (hv : v * v = e) (hvn : (Subgroup.zpowers v).Normal) :
    ∃ L : Subgroup X, CFSG.IsComponent L ∧ ¬ L ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set N := CFSG.layer X ⊔ CFSG.Open.pCore 2 X with hN
  have : N.Normal := by
    have := layer_normal (X := X)
    have := TheoremC.twoCore_normal (X := X)
    infer_instance
  have hNY : N ≤ Y := sup_le (sSup_le fun L hL => hall L hL) hc.twoCore_le
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hP₀Y : (P₀ : Subgroup N).map N.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hNY
  have hNrank : CFSG.Open.pRank 2 N ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ CFSG.Open.pRank 2 ((P₀ : Subgroup N).map N.subtype) := by
      rw [sylow_image_two_rank_eq]
      omega
    have hnorm := hc.normalizer_le _ hP₀Y h2
    have hfrat := Sylow.normalizer_sup_eq_top P₀
    exact hc.ne_top (top_le_iff.mp (hfrat ▸ sup_le hnorm hNY))
  obtain ⟨L, hL⟩ := hc.exists_component hrank
  obtain ⟨P, -, -⟩ := hc.sylow
  have hRN : ((P : Subgroup X) ⊓ L) ⊔ Subgroup.zpowers v ≤ N := by
    have hLE : L ≤ CFSG.layer X := le_sSup hL
    refine sup_le (inf_le_right.trans (hLE.trans le_sup_left)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (hc.mem_twoCore_of_sq hv hvn)
  have h2 := hc.two_le_pRank_sup hv hvn P hL
  have hmono := CFSG.SectionRank.pRank_mono (p := 2) (by decide) hRN
  omega

theorem component_unique (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) {L₂ : Subgroup X} (hL₂ : CFSG.IsComponent L₂) : L₂ = L := by
  by_contra hne
  obtain ⟨P, hPY, -⟩ := hc.sylow
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne L₂ L
    ((CFSG.isComponent_iff_open L₂).mp hL₂) ((CFSG.isComponent_iff_open L).mp hL) hne
  have hL₂C : L₂ ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  set R := ((P : Subgroup X) ⊓ L₂) ⊔ Subgroup.zpowers v with hR
  have hRC : R ≤ Subgroup.centralizer (L : Set X) := by
    refine sup_le (inf_le_right.trans hL₂C) ?_
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_component hvn hL
  have hRP : R ≤ (P : Subgroup X) :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr (hc.mem_sylow_of_sq hv hvn P))
  obtain ⟨a, haR, b, hbR, ha, hb, hab, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hc.two_le_pRank_sup hv hvn P hL₂)
  obtain ⟨t, htR, ht, hte⟩ : ∃ t ∈ R, orderOf t = 2 ∧ t ≠ e := by
    by_cases hae : a = e
    · exact ⟨b, hbR, hb, fun hbe => hab (hae.trans hbe.symm)⟩
    · exact ⟨a, haR, ha, hae⟩
  apply hLY
  intro l hl
  refine hc.involution_centralizer_le (hPY (hRP htR)) ht hte ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (hRC htR) l hl)

end BaseConfig

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
