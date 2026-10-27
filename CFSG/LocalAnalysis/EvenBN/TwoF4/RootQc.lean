module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootQb
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAj

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X] [Finite X]

theorem exists_benderSylow_of_odd (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {a : X} {V : Subgroup X} (hV : IsPGroup 2 (V ⊔ zpowers a : Subgroup X))
    {D Wb : Subgroup (X ⧸ O)}
    (hB : BenderSylow D (QuotientGroup.mk' O a) (V.map (QuotientGroup.mk' O)) Wb) :
    ∃ W : Subgroup X, BenderSylow W a V W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' O with hπ
  set tb := π a with htb
  have hVTmap : (V ⊔ zpowers a).map π = V.map π ⊔ zpowers tb := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  have hVTle : (V ⊔ zpowers a).map π ≤ Wb ⊔ zpowers tb := by
    rw [hVTmap]
    exact sup_le_sup_right hB.le _
  obtain ⟨Q, hVTQ, hQ2, hQmap⟩ := exists_lift_of_odd O hB.isPGroup_sup hV hVTle
  set WX : Subgroup X := Q ⊓ Wb.comap π with hWXdef
  have haQ : a ∈ Q := hVTQ (mem_sup_right (mem_zpowers _))
  have hVQ : V ≤ Q := le_sup_left.trans hVTQ
  have hWXQ : WX ≤ Q := inf_le_left
  have hWXmap : WX.map π = Wb := by
    apply le_antisymm
    · exact (map_mono inf_le_right).trans (map_comap_le _ _)
    · intro w hw
      have hw' : w ∈ Q.map π := by
        rw [hQmap]
        exact mem_sup_left hw
      obtain ⟨q, hq, rfl⟩ := hw'
      exact ⟨q, mem_inf.2 ⟨hq, hw⟩, rfl⟩
  set ψ : Q →* X ⧸ O := π.comp Q.subtype with hψdef
  have hψ : Function.Injective ψ := injective_mk'_comp_of_isPGroup O hO hQ2
  have hVQmap : (V.subgroupOf Q).map ψ = V.map π := by
    rw [hψdef, ← Subgroup.map_map, subgroupOf_map_subtype, inf_eq_left.2 hVQ]
  have hWQmap : (WX.subgroupOf Q).map ψ = Wb := by
    rw [hψdef, ← Subgroup.map_map, subgroupOf_map_subtype, inf_eq_left.2 hWXQ, hWXmap]
  have haQ' : ψ ⟨a, haQ⟩ = tb := rfl
  have hB' := hB
  rw [← hVQmap, ← hWQmap, ← haQ'] at hB'
  have hBX := ((BenderSylow.comap hψ hB').self).map (subtype_injective Q)
  have e1 : (V.subgroupOf Q).map Q.subtype = V := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hVQ]
  have e2 : (WX.subgroupOf Q).map Q.subtype = WX := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hWXQ]
  rw [e1, e2] at hBX
  exact ⟨WX, hBX⟩

end Generic

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem NA_ne_top : d.NA ≠ ⊤ := by
  intro htop
  have hA : d.A.Normal := normalizer_eq_top_iff.1 htop
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.A with h1 | h1
  · apply h.elt_rootElt_one_ne_one .i12
    have : h.elt (rootElt h.K h.a .i12 1) ∈ d.A :=
      d.R_le_A (h.R₁_le_R (h.elt_rootElt_mem_R₁ rfl 1))
    rwa [h1, mem_bot] at this
  · exact d.t_not_mem_A (h1 ▸ mem_top _)

theorem isKGroupCat_Xb (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) :
    CFSG.SectionRank.IsKGroupCat d.Xb :=
  (CFSG.QuasithinUnique.isKGroupCat_of_kProper hK d.NA_ne_top).quotient d.AN

theorem card_le_card_bar_mul {S : Subgroup G} (hSN : S ≤ d.NA) :
    Nat.card S ≤ Nat.card (d.bar S) * Nat.card d.A := by
  set f := d.piA.comp (S.subgroupOf d.NA).subtype with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = d.bar S := by rw [hf, MonoidHom.range_comp, range_subtype]
  have hker : Nat.card f.ker ≤ Nat.card d.A := by
    refine Nat.card_le_card_of_injective (fun x => (⟨(((x : S.subgroupOf d.NA) : d.NA) : G),
      (d.piA_eq_one_iff ((x : S.subgroupOf d.NA) : d.NA)).1 (MonoidHom.mem_ker.1 x.2)⟩ : d.A))
      fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hS : Nat.card (S.subgroupOf d.NA) = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv
  rw [hrange, hS] at h1
  calc Nat.card S = Nat.card f.ker * Nat.card (d.bar S) := h1.symm
    _ ≤ Nat.card d.A * Nat.card (d.bar S) := Nat.mul_le_mul_right _ hker
    _ = _ := mul_comm _ _

abbrev Ob : Subgroup d.Xb := standardComponentOddCore d.Xb

abbrev Phi : d.NA →* d.Xb ⧸ d.Ob := (QuotientGroup.mk' d.Ob).comp d.piA

theorem odd_card_Ob : Odd (Nat.card d.Ob) := GMSK.odd_card_standardComponentOddCore _

theorem bar_map_eq (M : Subgroup G) :
    (d.bar M).map (QuotientGroup.mk' d.Ob) = (M.subgroupOf d.NA).map d.Phi := by
  rw [Subgroup.map_map]

theorem card_bar_N1 : Nat.card (d.bar (h.N .i1)) = Nat.card (h.N .i1) :=
  (Nat.card_congr (d.barEquiv d.N1_le_NA (h.N_le_L _) h.N1_inf_R).toEquiv).symm

theorem injective_Phi_N1 : Function.Injective (d.Phi.comp ((h.N .i1).subgroupOf d.NA).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs0, -⟩ := h.isSimpleGroup_N .i1
  have hs : IsSimpleGroup (d.bar (h.N .i1)) :=
    (d.barEquiv d.N1_le_NA (h.N_le_L _) h.N1_inf_R).symm.isSimpleGroup
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxO : d.piA x ∈ d.Ob := (QuotientGroup.eq_one_iff _).1 hx
  have hxN : d.piA x ∈ d.bar (h.N .i1) := ⟨x, x.2, rfl⟩
  have hO1 : d.piA x = 1 := by
    have hnorm : (d.Ob.subgroupOf (d.bar (h.N .i1))).Normal := inferInstance
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hnorm with h1 | h1
    · have : (⟨d.piA x, hxN⟩ : d.bar (h.N .i1)) ∈ d.Ob.subgroupOf (d.bar (h.N .i1)) :=
        mem_subgroupOf.2 hxO
      rw [h1, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hle : d.bar (h.N .i1) ≤ d.Ob := fun n hn => by
        have : (⟨n, hn⟩ : d.bar (h.N .i1)) ∈ d.Ob.subgroupOf (d.bar (h.N .i1)) := h1 ▸ mem_top _
        exact mem_subgroupOf.1 this
      have hdvd := Subgroup.card_dvd_of_le hle
      have heven : 2 ∣ Nat.card (d.bar (h.N .i1)) := by
        rw [d.card_bar_N1]
        have h2 : 2 ∣ Nat.card (h.V .i1) := by
          rw [h.card_V]
          simp only [Idx.isSz, ↓reduceIte]
          exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
        exact h2.trans (Subgroup.card_dvd_of_le (h.V_le_N .i1))
      exact (Nat.not_even_iff_odd.2 d.odd_card_Ob) (even_iff_two_dvd.2 (heven.trans hdvd))
  exact d.injective_bar (h.N_le_L _) h.N1_inf_R (by simpa using hO1)

theorem card_Phi_map {M : Subgroup G} (hM : M ≤ h.N .i1) :
    Nat.card ((M.subgroupOf d.NA).map d.Phi) = Nat.card M := by
  have hinj : Function.Injective (d.Phi.comp (M.subgroupOf d.NA).subtype) := by
    intro x y hxy
    have hMN : ∀ z : M.subgroupOf d.NA, (z : d.NA) ∈ (h.N .i1).subgroupOf d.NA := fun z =>
      mem_subgroupOf.2 (hM (mem_subgroupOf.1 z.2))
    have := d.injective_Phi_N1 (a₁ := ⟨x, hMN x⟩) (a₂ := ⟨y, hMN y⟩) hxy
    have h2 : ((⟨x, hMN x⟩ : (h.N .i1).subgroupOf d.NA) : d.NA) =
        ((⟨y, hMN y⟩ : (h.N .i1).subgroupOf d.NA) : d.NA) := congrArg Subtype.val this
    exact Subtype.ext h2
  have hr : (d.Phi.comp (M.subgroupOf d.NA).subtype).range = (M.subgroupOf d.NA).map d.Phi := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (subgroupOfEquivOfLe (hM.trans d.N1_le_NA)).toEquiv

theorem isSylowOf_V1bb : IsSylowOf 2 ((d.bar (h.V .i1)).map (QuotientGroup.mk' d.Ob))
    ((d.bar (h.N .i1)).map (QuotientGroup.mk' d.Ob)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [d.bar_map_eq, d.bar_map_eq]
  refine isSylowOf_of_card (map_mono fun x hx => mem_subgroupOf.2 (h.V_le_N .i1
    (mem_subgroupOf.1 hx))) ?_
  rw [d.card_Phi_map (h.V_le_N .i1), d.card_Phi_map le_rfl]
  exact (h.isSylowOf_V_N (i := .i1) rfl).card_eq

theorem card_V1bb : Nat.card ((d.bar (h.V .i1)).map (QuotientGroup.mk' d.Ob)) =
    2 ^ (2 * (2 * h.a + 1)) := by
  rw [d.bar_map_eq, d.card_Phi_map (h.V_le_N .i1), h.card_V]
  simp only [Idx.isSz, ↓reduceIte]
  rw [← pow_mul, mul_comm]

theorem suzukiSylowFacts_V1bb :
    SuzukiSylowFacts ((d.bar (h.V .i1)).map (QuotientGroup.mk' d.Ob)) := by
  have hV1 : h.V .i1 ≤ d.NA := (h.V_le_N .i1).trans d.N1_le_NA
  have h1 := h.suzukiSylowFacts_V (i := .i1) rfl
  have e1 : ((h.V .i1).subgroupOf d.NA).map d.NA.subtype = h.V .i1 := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hV1]
  rw [← e1] at h1
  have h2 := h1.of_map (subtype_injective d.NA)
  set V' := (h.V .i1).subgroupOf d.NA with hV'
  have e2 : (⊤ : Subgroup V').map V'.subtype = V' := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← e2] at h2
  have hinj : Function.Injective (d.Phi.comp V'.subtype) := by
    intro x y hxy
    have hMN : ∀ z : V', (z : d.NA) ∈ (h.N .i1).subgroupOf d.NA := fun z =>
      mem_subgroupOf.2 (h.V_le_N .i1 (mem_subgroupOf.1 z.2))
    have := d.injective_Phi_N1 (a₁ := ⟨x, hMN x⟩) (a₂ := ⟨y, hMN y⟩) hxy
    have h2 : ((⟨x, hMN x⟩ : (h.N .i1).subgroupOf d.NA) : d.NA) =
        ((⟨y, hMN y⟩ : (h.N .i1).subgroupOf d.NA) : d.NA) := congrArg Subtype.val this
    exact Subtype.ext h2
  have h3 := (h2.of_map (subtype_injective V')).map hinj
  rw [← Subgroup.map_map, e2] at h3
  rw [d.bar_map_eq]
  exact h3

theorem not_normal_N1b : ¬ ((d.bar (h.N .i1)).map (QuotientGroup.mk' d.Ob)).Normal := by
  intro hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := d.Ob with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := d.odd_card_Ob
  set Ab := (d.bar (h.N .i1)).map π with hAb
  have hsyl := GMSK.exists_sylow_inf_centralizer_eq_zpowers d.orderOf_tb
    d.tb_mem_centralizer_N1b d.rank_N1b
  obtain ⟨-, hT, -, -, -, hS2⟩ := GMSK.stdData_odd_quotient GMSK.stdTypeFacts_T_Sz
    GMSK.isoInvariant_T_Sz (d.lieModel_N1b : GMSK.T_Sz (2 * h.a + 1) (d.bar (h.N .i1)))
    d.orderOf_tb d.N1b_le_centralizer_tb d.normal_N1b hsyl O hOodd
  have hTA : LieModel Ab .twistedB2 0 2 (2 * h.a + 1) := hT
  have hOut := GMSK.odd_card_outer_of_lieModel_twistedB2 hTA
  have hAs := GMSK.isSimpleGroup_of_lieModel_twistedB2 hTA
  have hAne := GMSK.exists_mul_ne_of_lieModel_twistedB2 hTA
  set CA := centralizer (Ab : Set (d.Xb ⧸ O)) with hCA
  have hAC : Ab ⊓ CA = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    exact (eq_one_of_forall_commute_of_isSimpleGroup hAs hAne hxA fun y hy =>
      (mem_centralizer_iff.1 hxC y hy).symm) ▸ one_mem _
  obtain ⟨S, hSN, hS2', hAS, hcardS⟩ := d.exists_le_normalizer_A
  have hSb2 : IsPGroup 2 (d.bar S) := (hS2'.comap_subtype (K := d.NA)).map _
  set Sb := (d.bar S).map π with hSb
  have hcardSb : Nat.card Sb = Nat.card (d.bar S) := card_map_mk'_of_isPGroup O hOodd hSb2
  have hSbAC : Sb ≤ Ab ⊔ CA := by
    intro s hs
    obtain ⟨k, hk⟩ := (hSb2.map π) ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsN : s ∈ normalizer (Ab : Set (d.Xb ⧸ O)) := by
      rw [normalizer_eq_top_iff.2 hN]
      exact mem_top s
    obtain ⟨l, hl, hlc⟩ := exists_inv_mul_mem_centralizer_of_odd_outer hOut hsN hk'
    have e : s = l * (l⁻¹ * s) := by group
    rw [e]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hlc)
  have hfA : (Nat.card Ab).factorization 2 = 2 * (2 * h.a + 1) := by
    have := d.isSylowOf_V1bb.card_eq
    rw [d.card_V1bb] at this
    exact (Nat.pow_right_injective le_rfl this).symm
  obtain ⟨S₂⟩ := (inferInstance : Nonempty (Sylow 2 CA))
  have hfC : (Nat.card CA).factorization 2 = 1 := by
    have h1 := S₂.card_eq_multiplicity
    rw [hS2 S₂] at h1
    exact (Nat.pow_right_injective le_rfl (h1.symm.trans (pow_one 2).symm))
  have hcardM : Nat.card (Ab ⊔ CA : Subgroup _) = Nat.card Ab * Nat.card CA := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ab CA fun x hx y hy =>
      mem_centralizer_iff.1 hy x hx).1
    rwa [hAC, Subgroup.card_bot, mul_one] at this
  obtain ⟨SM, hSM⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (Ab ⊔ CA)
  have hcardSM : Nat.card SM = 2 ^ (2 * (2 * h.a + 1) + 1) := by
    rw [hSM.card_eq, hcardM, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, hfA, hfC]
  have hle : Nat.card Sb ≤ Nat.card SM := card_le_of_isSylowOf hSM hSbAC (hSb2.map π)
  have h1 : Nat.card d.Ystar ≤ Nat.card (d.bar S) :=
    Nat.le_of_mul_le_mul_right (hcardS.trans (d.card_le_card_bar_mul hSN)) Nat.card_pos
  have h2 := d.card_Ystar
  rw [h.card_V_sup_t, h.card_V] at h2
  simp only [Idx.isSz, ↓reduceIte] at h2
  have hq : 0 < (2 ^ (2 * h.a + 1)) ^ 2 := by positivity
  have e : (2 : ℕ) ^ (2 * (2 * h.a + 1) + 1) = 2 * (2 ^ (2 * h.a + 1)) ^ 2 := by
    rw [pow_succ, ← pow_mul, mul_comm (2 * h.a + 1) 2, mul_comm]
  rw [hcardSM, e] at hle
  rw [hcardSb] at hle
  omega

theorem exists_benderSylow_Xb (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) :
    ∃ W : Subgroup d.Xb, BenderSylow W d.tb (d.bar (h.V .i1)) W := by
  have hS := GMSK.sharpOutcomeSz_oddCore_quotient hGMS (d.isKGroupCat_Xb hK) d.lieModel_N1b
    d.orderOf_tb d.tb_mem_centralizer_N1b d.normal_N1b d.rank_N1b d.not_normal_N1b
  have htt : QuotientGroup.mk' d.Ob d.tb * QuotientGroup.mk' d.Ob d.tb = 1 := by
    rw [← map_mul, ← pow_two, ← d.orderOf_tb, pow_orderOf_eq_one, map_one]
  have hAt : (d.bar (h.N .i1)).map (QuotientGroup.mk' d.Ob) ≤
      centralizer ({QuotientGroup.mk' d.Ob d.tb} : Set (d.Xb ⧸ d.Ob)) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (d.N1b_le_centralizer_tb hn)]
  have hF := d.suzukiSylowFacts_V1bb
  obtain ⟨Wb, hB⟩ := benderSylow_of_sharpOutcome_suzuki hS htt ⟨h.a, rfl⟩
    (by have := h.one_le_a; omega) hAt d.isSylowOf_V1bb d.card_V1bb
    hF.center_mul_self hF.mul_self_mem hF.commutator_le hF.mem_center
  have hV2 : IsPGroup 2 (d.bar (h.V .i1) ⊔ zpowers d.tb : Subgroup d.Xb) := by
    have hVT := h.isPGroup_V1_sup_t
    have hle : h.V .i1 ⊔ zpowers h.t ≤ d.NA :=
      sup_le ((h.V_le_N .i1).trans d.N1_le_NA) (zpowers_le.2 (d.J_le_NA h.t_mem_J))
    have e : ((h.V .i1 ⊔ zpowers h.t).subgroupOf d.NA).map d.piA =
        d.bar (h.V .i1) ⊔ zpowers d.tb := by
      rw [subgroupOf_sup ((h.V_le_N .i1).trans d.N1_le_NA) (zpowers_le.2 (d.J_le_NA h.t_mem_J)),
        Subgroup.map_sup]
      congr 1
      have hz : (zpowers h.t).subgroupOf d.NA = zpowers d.tN := by
        ext x
        rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k, Subtype.ext (by simpa using hk)⟩
        · rintro ⟨k, rfl⟩
          exact ⟨k, by simp⟩
      rw [hz, MonoidHom.map_zpowers]
    rw [← e]
    exact (hVT.comap_subtype (K := d.NA)).map _
  exact exists_benderSylow_of_odd d.Ob d.odd_card_Ob hV2 hB

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
