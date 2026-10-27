module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3Target
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverA6
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12E9
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeSporBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Sporadic.Bridge.M12
public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public import CFSG.Sporadic.J3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem inf_centralizer_eq_bot_of_center {Y : Type*} [Group Y] {K : Subgroup Y}
    (hZ : center K = ⊥) : K ⊓ centralizer (K : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzC⟩
  have h : (⟨z, hzK⟩ : K) ∈ center K :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hzC g g.2)
  rw [hZ, mem_bot] at h
  exact mem_bot.mpr (congrArg Subtype.val h)

private theorem center_eq_bot_of_mulEquiv {K X : Type*} [Group K] [Group X] [IsSimpleGroup X]
    (e : K ≃* X) (hnab : ∃ a b : X, a * b ≠ b * a) : center K = ⊥ := by
  haveI : IsSimpleGroup K := MulEquiv.isSimpleGroup e
  obtain ⟨a, b, hab⟩ := hnab
  exact CFSG.ComponentClassification.Helpers.center_eq_bot K
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

private theorem isSolvable_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) : Group.IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hp : IsPGroup 2 G := by
    rcases (by omega : Nat.card G = 2 ^ 0 ∨ Nat.card G = 2 ^ 1) with hc | hc
    · exact IsPGroup.of_card hc
    · exact IsPGroup.of_card hc
  haveI := hp.isNilpotent
  infer_instance

section M12

open CFSG.AGLEmbedding.KFactProofs.M12Cover CFSG.AGLEmbedding.KFactProofs.M12Z2


theorem m12_isSolvable_of_sylow_le {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .M12).Group)) (T : Sylow 3 L)
    (H : Subgroup L) (hTH : (T : Subgroup L) ≤ H) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hL
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  obtain ⟨Φ, hΦ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_mulEquiv_map_eq_sylow
    (e.trans eC.symm) (R := m12HeisKG)
    (IsPGroup.of_card (n := 3) (by rw [card_m12HeisKG]; norm_num)) m12HeisKG_index T
  set H' : Subgroup M12Grp := H.map Φ.symm.toMonoidHom with hH'
  have hKH' : m12HeisKG ≤ H' := fun x hx => by
    have hxT : Φ x ∈ (T : Subgroup L) := by
      rw [hΦ]
      exact mem_map_of_mem _ hx
    exact ⟨Φ x, hTH hxT, by simp⟩
  have hH'ne : H' ≠ ⊤ := by
    intro htop
    refine hH (eq_top_iff.mpr fun l _ => ?_)
    have hl : Φ.symm l ∈ H' := htop ▸ mem_top _
    obtain ⟨h, hh, hhl⟩ := mem_map.mp hl
    have hhl' : h = l := Φ.symm.injective hhl
    exact hhl' ▸ hh
  have hu : (⟨m12CoverU, m12CoverU_mem⟩ : M12Grp) ∈ H' := hKH' (by
    show m12CoverU ∈ m12HeisK
    rw [m12CoverU_eq]
    exact m12HeisC_mem_K)
  have hv : (⟨m12CoverV, m12CoverV_mem⟩ : M12Grp) ∈ H' := hKH' (by
    show m12CoverV ∈ m12HeisK
    rw [m12CoverV_eq]
    exact subset_closure (by simp))
  have hndvd : ∀ q : ℕ, q.Prime → (q = 5 ∨ q = 11) → ¬ q ∣ Nat.card H' := by
    intro q hq hq' hdvd
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
    refine hH'ne (eq_top_of_order hu hv x.2 ?_)
    rw [Subgroup.orderOf_coe, hx]
    exact hq'
  haveI := isSolvable_of_not_dvd H' (hndvd 5 (by norm_num) (Or.inl rfl))
    (hndvd 11 (by norm_num) (Or.inr rfl))
  exact Group.isSolvable_of_isSolvable_injective
    (f := (H.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).toMonoidHom)
    (MulEquiv.injective _)

theorem threeFourTwoNoneAt_m12 :
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.sporadic .M12).Group := by
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  haveI := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  haveI hX : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M12).Group :=
    MulEquiv.isSimpleGroup eC.symm
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic .M12).Group = 95040 := by
    rw [← Nat.card_congr eC.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  haveI := CFSG.Sporadic.Schreier.at_m12_schreier.2.2
  refine threeFourTwoNoneAt_of_inf hX
    (exists_mul_ne_of_sq_dvd_card Nat.prime_three (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num))
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eC) ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ _ _ _ _ hRY₀ hKY₀
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Or.inl (isSolvable_inf_of_forall_sylow_le R
    (fun T H hTH hH => m12_isSolvable_of_sylow_le hKX T H hTH hH) hRY₀ hKY₀)

end M12

section M11

private theorem isElemAbelian_of_forall_not_mem_normalizer {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R : Subgroup X} (hR : Nat.card R = p ^ 2) {t : X}
    (htR : t ∈ normalizer (R : Set X))
    (ht : ∀ Y₀ : Subgroup X, Y₀ ≤ R → Nat.card Y₀ = p → t ∉ normalizer (Y₀ : Set X)) :
    IsElemAbelian p R := by
  have hnc : ¬ IsCyclic R := by
    intro hc
    haveI := hc
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := R) p
      (by rw [hR]; exact dvd_pow_self p two_ne_zero)
    set Y₀ : Subgroup X := zpowers (g : X) with hY₀
    have hY₀R : Y₀ ≤ R := (zpowers_le (H := R)).2 g.2
    have hY₀c : Nat.card Y₀ = p := by rw [hY₀, Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    set Y₁ : Subgroup X := Y₀.map (MulAut.conj t).toMonoidHom with hY₁
    have hY₁R : Y₁ ≤ R := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 htR y).1 (hY₀R hy)
    have hcard : ∀ {W : Subgroup X}, W ≤ R → Nat.card (W.subgroupOf R) = Nat.card W :=
      fun hW => Nat.card_congr (subgroupOfEquivOfLe hW).toEquiv
    have heq : Y₀.subgroupOf R = Y₁.subgroupOf R :=
      IsCyclic.subgroup_eq_iff_card_eq.2 (by
        rw [hcard hY₀R, hcard hY₁R, hY₁, card_map_of_injective (MulAut.conj t).injective])
    rw [subgroupOf_inj, inf_eq_left.2 hY₀R, inf_eq_left.2 hY₁R] at heq
    refine ht Y₀ hY₀R hY₀c (mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · rw [heq]
      exact ⟨y, hy, rfl⟩
    · rw [heq] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzy' : z = y := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
          mul_right_inj] using hzy
      exact hzy' ▸ hz
  obtain ⟨D, hDR, hD, hDc⟩ :=
    GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 (IsPGroup.of_card hR) hnc
  rwa [eq_of_le_of_card_ge hDR (by rw [hR, hDc])] at hD


theorem m11_sylow_three_facts {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)) (T : Sylow 3 K) :
    IsElemAbelian 3 (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = 3 ^ 2 ∧
      (∀ H : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ H →
        H = normalizer ((T : Subgroup K) : Set K) ∨ H = ⊤) ∧
      Group.IsSolvable (normalizer ((T : Subgroup K) : Set K)) ∧ Nat.card (Outer K) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e' : K ≃* CFSG.Blueprint.NativeSporadic.M11 := e.trans eC.symm
  obtain ⟨R₀, hR₀⟩ := CFSG.AGLEmbeddingD2.m11_three_localData
  have hTL := CFSG.AGLEmbeddingD2.torusLocal_of_localData hR₀ (by norm_num)
    CFSG.AGLEmbeddingD2.orderOf_two_zmod_three (by norm_num)
  obtain ⟨hTc, hmax, -, hsol, t, ht, m, -, -, hm, -, -, -, -, hline⟩ :=
    CFSG.AGLEmbeddingD2.torusLocal_sylow e' hTL (by
      rw [hTL.1, CFSG.Sporadic.Mathieu.card_M11,
        CFSG.AGLEmbeddingD2.factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num)
          (by norm_num) (by norm_num)]) T
  refine ⟨isElemAbelian_of_forall_not_mem_normalizer (by norm_num) hTc ht fun Y₀ hY₀ hc => by
      simpa using hline 1 one_pos (by omega) Y₀ hY₀ hc, hTc, hmax, hsol, ?_⟩
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact CFSG.AGLEmbeddingD2.card_outer_m11

theorem threeFourTwoNoneAt_m11 :
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.sporadic .M11).Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  haveI := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  haveI hX : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M11).Group :=
    MulEquiv.isSimpleGroup eC.symm
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic .M11).Group = 7920 := by
    rw [← Nat.card_congr eC.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  have hnab : ∃ a b : (TauCeti.CFSGIndex.sporadic .M11).Group, a * b ≠ b * a :=
    exists_mul_ne_of_sq_dvd_card Nat.prime_three (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num)
  have hout : Group.IsSolvable (Outer (TauCeti.CFSGIndex.sporadic .M11).Group) := by
    have h1 : Nat.card (Outer (TauCeti.CFSGIndex.sporadic .M11).Group) = 1 := by
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eC).toEquiv]
      exact CFSG.AGLEmbeddingD2.card_outer_m11
    haveI : Subsingleton (Outer (TauCeti.CFSGIndex.sporadic .M11).Group) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ hER hE hEc hcore _ hKY₀
  haveI := hKn
  obtain ⟨eK⟩ := hKX
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTel, hTc, hmax, hsol, hO⟩ := m11_sylow_three_facts ⟨eK⟩ T
  have hZK := inf_centralizer_eq_bot_of_center (center_eq_bot_of_mulEquiv eK hnab)
  have hT₀el : IsElemAbelian 3 ((R : Subgroup Y) ⊓ K) :=
    hT ▸ CFSG.SectionRank.isElemAbelian_map hTel K.subtype
  have hT₀c : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = 3 ^ 2 := by
    rw [← hT, card_map_of_injective K.subtype_injective, hTc]
  have hN := normalizer_inf_le_of_isElemAbelian R hER hE hEc hcore hZK
    (by rw [hO]; norm_num) hT₀el (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hT₀el hT₀c)
  refine Or.inl (isSolvable_inf_of_normalizer_le T hmax hsol ?_ hKY₀)
  refine (le_normalizer_map K.subtype).trans ?_
  rw [hT]
  exact hN

end M11

section J3

private theorem centerOf_eq_map_center {G : Type*} [Group G] (T : Subgroup G) :
    CFSG.Quasithin.centerOf T = (center T).map T.subtype := by
  ext x
  constructor
  · rintro ⟨hxT, hxC⟩
    exact ⟨⟨x, hxT⟩, mem_center_iff.mpr fun t => Subtype.ext (mem_centralizer_iff.mp hxC t t.2),
      rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.mpr fun t ht =>
      congrArg Subtype.val (mem_center_iff.mp hy ⟨t, ht⟩)⟩


theorem threeFourTwoNoneAt_j3 :
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.sporadic .J3).Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  haveI := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI hX : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .J3).Group :=
    MulEquiv.isSimpleGroup (H := CFSG.Blueprint.NativeSporadic.J3) β.symm
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic .J3).Group = 50232960 := by
    rw [← Nat.card_congr β.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  haveI : Finite (TauCeti.CFSGIndex.sporadic .J3).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hOR := CFSG.AGLEmbedding.kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hout : Group.IsSolvable (Outer (TauCeti.CFSGIndex.sporadic .J3).Group) := by
    haveI : Finite (MulAut (TauCeti.CFSGIndex.sporadic .J3).Group) := MulEquiv.finite_left
    exact isSolvable_of_card_le_two (hOR _ ⟨MulEquiv.refl _⟩).1
  refine threeFourTwoNoneAt_of_inf hX
    (exists_mul_ne_of_sq_dvd_card Nat.prime_three (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num)) hout ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ _ _ _ hcore _ hKY₀
  haveI := hKn
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hF := CFSG.AGLEmbedding.kFactJ3Sylow K hKX T
  have hrk := (hOR K hKX).2
  set Z : Subgroup K := CFSG.Quasithin.centerOf (T : Subgroup K) with hZdef
  set X : Subgroup Y := Z.map K.subtype with hXdef
  have hZT : Z ≤ T := inf_le_left
  have hXR : X ≤ R := by
    rintro _ ⟨z, hz, rfl⟩
    have h : (z : Y) ∈ (R : Subgroup Y) ⊓ K := hT ▸ mem_map_of_mem K.subtype (hZT hz)
    exact (mem_inf.mp h).1
  have hX2 : 2 ≤ CFSG.Open.pRank 3 X :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (CFSG.SectionRank.isElemAbelian_map hF.center_elem.1 K.subtype)
      (by rw [card_map_of_injective K.subtype_injective, hF.center_elem.2]; norm_num)
  have hSX : (R : Subgroup Y) ⊓ K ≤ centralizer (X : Set Y) := by
    rw [← hT]
    rintro _ ⟨t, ht, rfl⟩
    refine mem_centralizer_iff.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact (congrArg Subtype.val (mem_centralizer_iff.mp (mem_inf.mp hz).2 t ht)).symm
  have hS3 : 3 ≤ CFSG.Open.pRank 3 ((R : Subgroup Y) ⊓ K) := by
    rw [← hT]
    calc 3 = CFSG.Open.pRank 3 (T : Subgroup K) := by
          rw [(CFSG.SectionRank.pRank_sylow T).1, hrk]
      _ ≤ _ := CFSG.SectionRank.pRank_le_map (by norm_num) K.subtype K.subtype_injective _
  have hNX := normalizer_le_of_le_centralizer_of_three_le_pRank Nat.prime_three R hcore hXR hX2
    inf_le_left hSX hS3
  refine Or.inl (isSolvable_inf_of_normalizer_le T hF.maximal
    (CFSG.AGLEmbedding.isSolvable_normalizer_of_facts T.isPGroup' hF) ?_ hKY₀)
  have hNZ : normalizer ((T : Subgroup K) : Set K) ≤ normalizer (Z : Set K) := by
    rw [hZdef, centerOf_eq_map_center]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (center T)
  exact (map_mono hNZ).trans ((le_normalizer_map K.subtype).trans hNX)

end J3

theorem threeFourTwoThreeSporadic_holds :
    ThreeFourTwoThreeSporadic := by
  rintro s (rfl | rfl | rfl)
  · exact threeFourTwoNoneAt_m11
  · exact threeFourTwoNoneAt_m12
  · exact threeFourTwoNoneAt_j3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
