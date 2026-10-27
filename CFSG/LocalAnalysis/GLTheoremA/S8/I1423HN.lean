module

public import CFSG.LocalAnalysis.GLTheoremA.S8.HNNative
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016ONRow
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Inputs
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma82
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.Sporadic.HNSchreier



variable {G : Type} [Group G] [Finite G]

theorem normalizer_map_subtype_subgroupOf {L : Subgroup G} (T : Subgroup ↥L) :
    (Subgroup.normalizer ((T.map L.subtype : Subgroup G) : Set G)).subgroupOf L =
      Subgroup.normalizer (T : Set ↥L) := by
  apply le_antisymm
  · have h := Subgroup.le_normalizer_comap (H := T.map L.subtype) L.subtype
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h
  · intro g hg
    exact Subgroup.le_normalizer_map L.subtype ⟨g, hg, rfl⟩

theorem card_of_equiv_alt9 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 9)) :
    Nat.card S = 181440 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem card_of_equiv_alt8 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 8)) :
    Nat.card S = 20160 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl


theorem nonempty_pquot_equiv_HN {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hcat : catalogIs (PSimple 3 L) (sporIs .HN)) :
    Subgroup.center (PQuot 3 L) = ⊥ ∧ Nonempty (PQuot 3 L ≃* CFSG.Blueprint.NativeSporadic.HN) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  let eS : PSimple 3 L ≃* CFSG.Blueprint.NativeSporadic.Carrier .HN := e.trans b.symm
  have hq := L84.cfsgQuasisimple_of_open (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL)
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq
    (X := CFSG.Blueprint.NativeSporadic.Carrier .HN) eS
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .HN)) = 1 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_HN
  rw [hM] at h
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.1 h)
  exact ⟨hZ, ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    e).trans b.symm⟩⟩

set_option maxRecDepth 20000 in
theorem i1423At_holds (G : Type) [Group G] [Finite G] : S8.L83.I1423At G := by
  intro x L hx hL hcat
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hZ, ⟨ψ⟩⟩ := nonempty_pquot_equiv_HN hL hcat
  let e : PQuot 3 L ≃* JH := ψ.trans hnEquivJ
  obtain ⟨yb, Tb, A9, A8, hyb, hT2, hT1, hyT, h89, hU9, ⟨e9⟩, hU8, ⟨e8⟩⟩ := hn_native e
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp3 L
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
  obtain ⟨y', T', hyπ, hyo', hT2', hT1', hyN', hTmap, hC, hCN⟩ :=
    lift_data (GLAPPrimeCore 3 ↥L) hN hyb hT2 hT1 hyT
  have hyL : (y' : G) ∈ L := y'.2
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hL.1
  have hyo : orderOf (y' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hyo'
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy3 : (y' : G) ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one _
  have hxy : x * (y' : G) = (y' : G) * x :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hxL hyL)).symm
  have hyne : (y' : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hyo; norm_num at hyo
  have hna : x ∉ Subgroup.zpowers (y' : G) := by
    intro hxz
    have hxL' : x ∈ L := Subgroup.zpowers_le.2 hyL hxz
    have hcen : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨x, hxL'⟩ ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hxL k.2))
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    have h1 : x = 1 := CFSG.LocalAnalysis.GLTheoremA.S8.L84.eq_one_of_mem_core hp3 ⟨_, hcen, rfl⟩ hx3
    rw [h1, orderOf_one] at hx
    norm_num at hx
  obtain ⟨-, hDc⟩ := Prop53.isElemAbelian_card_sup_zpowers hp3 hxy hx3 hy3 hyne hna
  set T : Subgroup G := T'.map L.subtype with hTdef
  have hTL : T ≤ L := Subgroup.map_subtype_le _
  have hDN : altDxy x (y' : G) ≤ Subgroup.normalizer (T : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · have key : ∀ h ∈ L, x * h * x⁻¹ = h := fun h hh => by
        have := Subgroup.mem_centralizer_singleton_iff.1 (hxL hh)
        rw [← this]; group
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        rw [key g (hTL hg)]
        exact hg
      · intro hg
        have hgL : x * g * x⁻¹ ∈ L := hTL hg
        have : g = x * g * x⁻¹ := by
          have h2 := key _ hgL
          calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
            _ = x⁻¹ * (x * (x * g * x⁻¹) * x⁻¹) * x := by rw [h2]
            _ = x * g * x⁻¹ := by group
        rw [this]
        exact hg
    · exact Subgroup.le_normalizer_map L.subtype ⟨y', hyN', rfl⟩
  have hH1 : (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G)).subgroupOf L =
      Subgroup.centralizer ({y'} : Set ↥L) := by
    rw [inf_centralizer_altDxy_eq hxL, subgroupOf_inf_centralizer hyL, Subgroup.subgroupOf_self,
      top_inf_eq]
  have hH2 : (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G) ⊓
      Subgroup.normalizer (T : Set G)).subgroupOf L =
      Subgroup.centralizer ({y'} : Set ↥L) ⊓ Subgroup.normalizer (T' : Set ↥L) := by
    have hinf : ∀ A B : Subgroup G, (A ⊓ B).subgroupOf L = A.subgroupOf L ⊓ B.subgroupOf L :=
      fun A B => by ext; simp [Subgroup.mem_subgroupOf]
    rw [hinf, hH1, normalizer_map_subtype_subgroupOf]
  have hb1 : barX 3 L (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G)) =
      Subgroup.centralizer ({yb} : Set (PQuot 3 L)) := by
    unfold barX
    rw [hH1]
    exact hC
  have hb2 : barX 3 L (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G) ⊓
      Subgroup.normalizer (T : Set G)) =
      Subgroup.centralizer ({yb} : Set (PQuot 3 L)) ⊓ Subgroup.normalizer (Tb : Set (PQuot 3 L)) := by
    unfold barX
    rw [hH2]
    exact hCN
  have hU9' : UniqComp (barX 3 L (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G))) A9 := by
    rw [hb1]; exact hU9
  have hU8' : UniqComp (barX 3 L (L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G) ⊓
      Subgroup.normalizer (T : Set G))) A8 := by
    rw [hb2]; exact hU8
  obtain ⟨J, hJu, hJbar, ⟨eJ⟩⟩ := uniq_lift inf_le_left hU9'
  obtain ⟨I, hIu, hIbar, ⟨eI⟩⟩ := uniq_lift (inf_le_left.trans inf_le_left) hU8'
  have hc9 : Nat.card A9 = 181440 := card_of_equiv_alt9 e9
  have hc8 : Nat.card A8 = 20160 := card_of_equiv_alt8 e8
  haveI : IsSimpleGroup A9 :=
    e9.isSimpleGroup_congr.2 (alternatingGroup.isSimpleGroup (by simp))
  haveI : IsSimpleGroup A8 :=
    e8.isSimpleGroup_congr.2 (alternatingGroup.isSimpleGroup (by simp))
  have eJ9 : PQuot 3 J ≃* alternatingGroup (Fin 9) :=
    eJ.trans ((pQuotEquivSelf A9 (by rw [hc9]; norm_num)).trans e9)
  have eI8 : PQuot 3 I ≃* alternatingGroup (Fin 8) :=
    eI.trans ((pQuotEquivSelf A8 (by rw [hc8]; norm_num)).trans e8)
  have hJn : ∀ g ∈ L ⊓ Subgroup.centralizer (altDxy x (y' : G) : Set G), ∀ j ∈ J,
      g * j * g⁻¹ ∈ J := by
    intro g hg j hj
    have := CFSG.LocalAnalysis.GLTheoremA.S8.L84.mem_normalizer_of_uniq hJu.1 hJu.2 (Subgroup.le_normalizer hg)
    exact (Subgroup.mem_normalizer_iff.1 this j).1 hj
  have hIJ : I ≤ J := by
    haveI : IsSimpleGroup (PQuot 3 I) :=
      eI8.isSimpleGroup_congr.2 (alternatingGroup.isSimpleGroup (by simp))
    refine le_of_cover inf_le_left hJu.1.1 hJn hIu.1 this
      (by rw [card_of_equiv_alt8 eI8]; decide) fun i hi => ?_
    have hle : barX 3 L I ≤ barX 3 L J := by rw [hIbar, hJbar]; exact h89
    have hiL : i ∈ L := hIu.1.1.trans (inf_le_left.trans inf_le_left) hi
    obtain ⟨j, hj, hjc⟩ := exists_of_barX_le hle hi hiL
    refine ⟨j, hj, ?_⟩
    have hd := Subgroup.orderOf_dvd_natCard _ hjc
    exact Nat.Coprime.coprime_dvd_right hd
      ((Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 L))
  refine ⟨y', T, J, I, hyL, hyo, hDc, hTL, ?_, hT2'.map _, hDN,
    (CFSG.LocalAnalysis.GLTheoremA.S8.L84.glaPLayer_eq_of_uniq hJu.1 hJu.2).symm, hJu.1, ⟨eJ9⟩,
    (CFSG.LocalAnalysis.GLTheoremA.S8.L84.glaPLayer_eq_of_uniq hIu.1 hIu.2).symm, hIu.1, hIJ, ⟨eI8⟩⟩
  intro h
  exact hT1' ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
