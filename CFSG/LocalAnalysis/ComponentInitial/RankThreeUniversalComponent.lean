module

public import CFSG.LocalAnalysis.ComponentInitial.SelectedEightGroupPropagation
public import CFSG.LocalAnalysis.ComponentInitial.IsolatedInvolutionSplit

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type} [Group G]

theorem relIndex_subgroupOf_eq_of_le {H X Y : Subgroup G} (hXH : X ≤ H) (hYH : Y ≤ H) :
    (X.subgroupOf H).relIndex (Y.subgroupOf H) = X.relIndex Y := by
  rw [← relIndex_map_map_of_injective (X.subgroupOf H) (Y.subgroupOf H) H.subtype_injective,
    map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hYH]

theorem maximal_centralizer_rank_three_universal_component {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {J A : Subgroup G}
    (hAJ : A ≤ centralizer (J : Set G)) (hA : CFSG.Assembly.IsElemAbelian 2 A)
    (hA8 : 8 ≤ Nat.card A)
    (hrank : CFSG.Assembly.pRank 2 (centralizer (J : Set G)) = CFSG.Assembly.pRank 2 A)
    (hJA : ∀ a ∈ A, a ≠ 1 → CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hmax : ∀ s : G, orderOf s = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({s} : Set G)) →
        (center Q).index ≤ (center J).index) :
    ∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
  set Cj := centralizer (J : Set G) with hCj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hfail⟩ :=
    selected_component_eight_group_derived_propagation hC hpump hK hB hAJ hA hA8 hJA hmax
  obtain ⟨P', hP'⟩ :=
    (isPGroup_of_isElemAbelian (isElemAbelian_two_subgroupOf (H := Cj) hA)).exists_le_sylow
  set P : Subgroup G := (P' : Subgroup Cj).map Cj.subtype with hPdef
  have hPC : P ≤ Cj := map_subtype_le _
  have hAP : A ≤ P := fun a ha => ⟨⟨a, hAJ ha⟩, hP' ha, rfl⟩
  have hPp : IsPGroup 2 P :=
    P'.2.of_equiv ((P' : Subgroup Cj).equivMapOfInjective Cj.subtype Cj.subtype_injective)
  obtain ⟨A₀, hA₀A, hA₀card⟩ := exists_card_eight_le_of_isElemAbelian hA hA8
  have hA₀ : CFSG.Assembly.IsElemAbelian 2 A₀ := isElemAbelian_two_of_le hA₀A hA
  have hPnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Subgroup.card_le_of_le (hA₀A.trans hAP)
    omega
  have hZnt : Nontrivial (center P) := hPp.center_nontrivial
  have hZeven : 2 ∣ Nat.card (center P) :=
    ((hPp.to_subgroup (center P)).card_eq_or_dvd).resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' h
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 hZeven
  set z : G := ((zc : P) : G) with hzdef
  have hz2 : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hzc
  have hzP : z ∈ P := (zc : P).2
  have hzcomm : ∀ x ∈ P, x * z = z * x := fun x hx =>
    congrArg Subtype.val (mem_center_iff.1 zc.2 ⟨x, hx⟩)
  have hzA : z ∈ A := by
    by_contra hzA
    obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
    have hAz : CFSG.Assembly.IsElemAbelian 2 (A ⊔ zpowers z) :=
      isElemAbelian_sup_zpowers hA (by rw [← hz2]; exact pow_orderOf_eq_one z)
        fun x hx => hzcomm x (hAP hx)
    have hinf : A ⊓ zpowers z = ⊥ := by
      refine (eq_bot_iff_forall _).2 fun x hx => ?_
      rcases (LocalB.mem_zpowers_iff_of_involution z x hz2).1 (mem_inf.1 hx).2 with h | h
      · exact h
      · exact absurd (h ▸ (mem_inf.1 hx).1) hzA
    have hcard : Nat.card ↥(A ⊔ zpowers z) = 2 ^ (m + 1) := by
      have h := card_sup_mul_card_inf_of_commute (A := A) (B := zpowers z)
        fun x hx y hy => by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
          exact (Commute.zpow_right (hzcomm x (hAP hx)) k)
      rw [hinf, card_bot, mul_one, Nat.card_zpowers, hz2, hm] at h
      rw [h, pow_succ]
    have hle1 : m + 1 ≤ CFSG.Assembly.pRank 2 Cj :=
      SectionRank.le_pRank (p := 2) (by norm_num)
        (sup_le hAJ ((zpowers_le).2 (hPC hzP))) hAz hcard
    have hle2 : CFSG.Assembly.pRank 2 A ≤ m :=
      SectionRank.pRank_le (p := 2) (by norm_num) fun E hEA _ => hm ▸ card_le_of_le hEA
    omega
  have hz1 : z ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hJz := hJA z hzA hz1
  intro t₀ ht₀C ht₀
  by_contra hnot₀
  have ht₀p : IsPGroup 2 (zpowers t₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₀, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow ((zpowers_le).2 ht₀C) ht₀p P'
  have hgP := hg ⟨t₀, ht₀C⟩ (mem_zpowers t₀)
  set t : G := (g : G)⁻¹ * t₀ * g with htdef
  have htP : t ∈ P := ⟨_, hgP, rfl⟩
  have htC : t ∈ Cj := hPC htP
  have ht : orderOf t = 2 := by
    rw [htdef, ← ht₀]
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj (g : G)⁻¹).orderOf_eq t₀
  have hnot : ¬ CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
    intro h
    apply hnot₀
    have h' := isComponentOf_centralizer_conj_of_mem_centralizer g.2 h
    rwa [show (g : G) * t * (g : G)⁻¹ = t₀ by rw [htdef]; group] at h'
  have hno8 := (hfail t htC ht hnot).2
  set H := centralizer ({t} : Set G) with hHdef
  have hJH : J ≤ H := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 htC x hx
  have hzH : z ∈ H := by
    rw [mem_centralizer_singleton_iff]
    exact (hzcomm t htP).symm
  let z' : H := ⟨z, hzH⟩
  have hz'2 : orderOf z' = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hKH : CFSG.Assembly.KProper C H := kProper_subgroup hC hK H
  have hBH : ∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤ :=
    fun Q hQ => AssemblyBLocalB.ordinary_at_involution hB t ht Q hQ
  have hJz' := isComponentOf_subgroupOf_centralizer hJH z' hJz
  obtain ⟨-, L, hL, hcase⟩ := hpump H hKH hBH z' hz'2 (J.subgroupOf H) hJz'
  have hLtop : CFSG.Assembly.IsComponentOf L ⊤ :=
    (AssemblyBPredicates.isComponentOf_top_iff_native L).2 hL
  rcases hcase with ⟨-, hJL⟩ | ⟨hLz, hJset, -, -⟩
  ·
    apply hnot
    have hJ'L : J.subgroupOf H ≤ L := hJL.1.trans inf_le_left
    rcases eq_or_lt_of_le hJ'L with heq | hlt
    · apply isComponentOf_of_subgroupOf_top hJH
      rw [heq]
      exact hLtop
    · exfalso
      have : Group.IsPerfect L := hL.1.1
      have hlt' := index_center_lt_of_lt hlt
      have hle := hmax t ht (L.map H.subtype) (isComponentOf_map_subtype_top hLtop)
      rw [index_center_eq_of_mulEquiv (subgroupOfEquivOfLe hJH),
        index_center_eq_of_mulEquiv (L.equivMapOfInjective H.subtype H.subtype_injective)] at hlt'
      omega
  ·
    obtain ⟨hJdiag, -, -, ⟨-, -, -, hzCM⟩, hCMCJ, -, -, -, hrel, -, -, -⟩ :=
      diagonal_component_centralizer_index_two hL hLz hz'2
    set hAB := commutator_conjSub_eq_bot hL hLz
    have hJeq : J.subgroupOf H = (swapDiag hAB).range := SetLike.ext' (hJset.trans hJdiag.symm)
    set CJ := centralizer (((swapDiag hAB).range : Subgroup H) : Set H)
    set CM := centralizer ((L ⊔ conjSub z'⁻¹ L : Subgroup H) : Set H)
    have hPtH : P ⊓ H ≤ H := inf_le_right
    set D : Subgroup H := (P ⊓ H).subgroupOf H with hDdef
    have hDCJ : D ≤ CJ := by
      show D ≤ centralizer (((swapDiag hAB).range : Subgroup H) : Set H)
      rw [← hJeq]
      intro d hd
      rw [mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (mem_centralizer_iff.1 (hPC (mem_inf.1 hd).1) x hx)
    have hz'D : z' ∈ D := ⟨hzP, hzH⟩
    set R : Subgroup H := D ⊓ CM with hRdef
    have hRD : R.relIndex D = 2 := by
      rw [hRdef, inf_relIndex_left]
      have hle : CM.relIndex D ≤ 2 := hrel ▸ relIndex_le_of_le_right hDCJ (by rw [hrel]; norm_num)
      have hne1 : CM.relIndex D ≠ 1 := fun h => hzCM (relIndex_eq_one.1 h hz'D)
      have hne0 : CM.relIndex D ≠ 0 := index_ne_zero_of_finite
      omega
    have hz'R : z' ∉ R := fun h => hzCM (mem_inf.1 h).2
    let t' : H := ⟨t, by rw [mem_centralizer_singleton_iff]⟩
    have ht'R : t' ∈ R := by
      refine ⟨⟨htP, t'.2⟩, ?_⟩
      show t' ∈ centralizer ((L ⊔ conjSub z'⁻¹ L : Subgroup H) : Set H)
      rw [mem_centralizer_iff]
      intro x _
      exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2)
    let zP : P := ⟨z, hzP⟩
    let tP : P := ⟨t, htP⟩
    have hRG : R.map H.subtype ≤ P ⊓ H :=
      (map_mono inf_le_left).trans (by rw [hDdef, map_subgroupOf_eq_of_le hPtH])
    set RP : Subgroup P := (R.map H.subtype).subgroupOf P with hRPdef
    have hcentP : (centralizer ({tP} : Set P)) = (P ⊓ H).subgroupOf P := by
      apply map_injective P.subtype_injective
      rw [map_subtype_centralizer_singleton, map_subgroupOf_eq_of_le inf_le_left]
    have hRPcent : RP ≤ centralizer ({tP} : Set P) := by
      rw [hcentP]
      intro x hx
      exact hRG hx
    have hRPind : RP.relIndex (centralizer ({tP} : Set P)) = 2 := by
      rw [hcentP, relIndex_subgroupOf_eq_of_le (hRG.trans inf_le_left) inf_le_left,
        ← map_subgroupOf_eq_of_le hPtH, ← hDdef,
        relIndex_map_map_of_injective R D H.subtype_injective, hRD]
    have htRP : tP ∈ RP := ⟨t', ht'R, rfl⟩
    have hzRP : zP ∉ RP := by
      rintro ⟨w, hw, hwz⟩
      have : w = z' := Subtype.ext hwz
      exact hz'R (this ▸ hw)
    have hPrank : 3 ≤ CFSG.pRank 2 P := by
      rw [SectionRank.pRank_eq_open_pRank_top]
      refine SectionRank.le_pRank (p := 2) (by norm_num) le_top
        (isElemAbelian_two_subgroupOf (H := P) hA₀) ?_
      rw [show Nat.card (A₀.subgroupOf P) = Nat.card A₀ from
        Nat.card_congr (subgroupOfEquivOfLe (hA₀A.trans hAP)).toEquiv, hA₀card]
      norm_num
    have hzZ : zP ∈ center P := by
      rw [mem_center_iff]
      intro x
      exact Subtype.ext (hzcomm x x.2)
    have hzP2 : orderOf zP = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
    have htP2 : orderOf tP = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
    have hnoE : ¬ ∃ E : Subgroup P, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ tP ∈ E := by
      rintro ⟨E, hE, hEcard, htE⟩
      have hEG : CFSG.Assembly.IsElemAbelian 2 (E.map P.subtype) :=
        isElemAbelian_map (isElemAbelian_iff_isElementaryAbelian.2 hE) _
      have h4 := hno8 (E.map P.subtype) ((map_subtype_le E).trans hPC) hEG ⟨tP, htE, rfl⟩
      rw [card_map_of_injective P.subtype_injective, hEcard] at h4
      norm_num at h4
    exact isolated_involution_central_split_obstruction hPp hPrank hzZ hzP2 htP2 hnoE
      ⟨RP, hRPcent, hRPind, htRP, hzRP⟩

end CFSG.LocalAnalysis.ComponentInitial
