module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAbs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPDiag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.GSLitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Outer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedPrimeLayer
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped MatrixGroups

namespace QPUJ

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_not_commute {L M : Subgroup G} (hLM : L ≤ M)
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) {t : G} (htL : t ∈ L) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : ∃ m ∈ M, m * t ≠ t * m := by
  by_contra h
  have hc : ∀ m ∈ M, m * t = t * m := fun m hm => not_not.mp fun hne => h ⟨m, hm, hne⟩
  set T : ↥L := ⟨t, htL⟩
  have hTZ : T ∈ center ↥L := mem_center_iff.mpr fun l => Subtype.ext (hc l (hLM l.2))
  have hTc : QuotientGroup.mk' (pPrimeCore 2 ↥L) T ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [mem_center_iff]
    intro u
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) u
    rw [← map_mul, ← map_mul, mem_center_iff.mp hTZ l]
  rw [hZ, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hTc
  have h2 : IsPGroup 2 (zpowers T) :=
    Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext ht2⟩
  have h3 : T ∈ zpowers T ⊓ pPrimeCore 2 ↥L := mem_inf.mpr ⟨mem_zpowers T, hTc⟩
  rw [OddQuot.inf_pPrimeCore_eq_bot h2, mem_bot] at h3
  exact ht1 (congrArg Subtype.val h3)

omit [Finite G] in
theorem centralizer_mul_of_mem_center {g c : G} (hc : c ∈ center G) :
    centralizer ({g * c} : Set G) = centralizer ({g} : Set G) := by
  ext w
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have hcw : w * c = c * w := mem_center_iff.mp hc w
  constructor
  · intro h
    have h' : w * g * c = g * w * c := by
      calc w * g * c = w * (g * c) := by group
        _ = g * c * w := h
        _ = g * (c * w) := by group
        _ = g * (w * c) := by rw [hcw]
        _ = g * w * c := by group
    exact mul_right_cancel h'
  · intro h
    calc w * (g * c) = w * g * c := by group
      _ = g * w * c := by rw [h]
      _ = g * (w * c) := by group
      _ = g * (c * w) := by rw [hcw]
      _ = g * c * w := by group

theorem nonempty_fixedLayer_quot_equiv {J E : Subgroup G}
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hE : E ≤ coreActionKernel J)
    (hE2 : IsPGroup 2 E) :
    Nonempty (↥(GSLit.fixedLayer J E) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer J E) ≃*
      ↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJEJ : GSLit.fixedLayer J E ≤ J := (GSLit.fixedLayer_le_inf J E).trans inf_le_left
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hE hE2
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp
      ((GSLit.fixedLayer J E).subgroupOf J).subtype) := by
    have h1 : (GSLit.fixedLayer J E).subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h2 : (GSLit.fixedLayer J E ⊔ (pPrimeCore 2 ↥J).map J.subtype).subgroupOf J = ⊤ := by
        rw [hsup]
        exact subgroupOf_self J
      have h3 : ((pPrimeCore 2 ↥J).map J.subtype).subgroupOf J = pPrimeCore 2 ↥J :=
        comap_map_eq_self_of_injective J.subtype_injective _
      rwa [subgroupOf_sup hJEJ (map_subtype_le _), h3] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥J))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, -⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv _ hY
  exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe hJEJ)).symm.trans φ⟩

theorem eq_of_card_psl_two_eq {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (h : a * (a ^ 2 - 1) / 2 = b * (b ^ 2 - 1) / 2) : a = b := by
  have key : ∀ {x y : ℕ}, Odd x → Odd y → x < y →
      x * (x ^ 2 - 1) / 2 < y * (y ^ 2 - 1) / 2 := by
    intro x y hx hy hxy
    have hx1 : 1 ≤ x := hx.pos
    have h1 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 2) 1
    have h2 : 0 < y ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
    have h3 : x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := Nat.mul_lt_mul_of_lt_of_le hxy h1 h2
    have h4 : 2 ∣ y * (y ^ 2 - 1) :=
      Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hy.pow odd_one)) y
    exact Nat.div_lt_div_of_lt_of_dvd h4 h3
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key ha hb hab).ne
  · exact hab
  · exact absurd h (key hb ha hab).ne'

theorem eq_of_isPComponent_psp {p f p₁ f₁ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : Blueprint.LieModel G .PSp 2 p f) {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    (hMt : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G))))
    (hp₁ : p₁.Prime) (hp₁2 : p₁ ≠ 2) (hf₁ : 1 ≤ f₁) (h5₁ : 5 ≤ p₁ ^ f₁)
    (hMLie : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p₁ f₁) : p₁ = p ∧ f₁ = f := by
  obtain ⟨-, hf, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hG
  have hodd := CatFactsSp4.odd_card_of_card_eq hp hp2 hK
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  have hO : pPrimeCore 2 ↥M = ⊥ := CatFactsSp4.cfSp4Comp G p f hp hp2 hf hG t ht M hMt hM
  have hcl : Assembly.LowTwoRank.StatedClassicalModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p₁ f₁ := by
    rcases hMLie with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact h
    all_goals exfalso; revert h; decide
  obtain ⟨-, K₁, _, _, hK₁, ⟨e₁⟩⟩ := hcl
  have hodd₁ := CatFactsSp4.odd_card_of_card_eq hp₁ hp₁2 hK₁
  obtain ⟨φ, hφ⟩ := CatFactsSp4.exists_model_conj hodd
    (show orderOf (e t) = 2 by rw [MulEquiv.orderOf_eq, ht])
  have hM' := CatFactsSp4.isPComponent_map_subgroupOf 2 (e.trans φ) hMt hM
  have hMX' := Subgroup.map_mono (f := (e.trans φ).toMonoidHom) hMt
  rw [CatFactsSp4.map_centralizer_singleton, MulEquiv.trans_apply] at hM' hMX'
  let eM : ↥(M.map (e.trans φ).toMonoidHom) ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 K₁) :=
    (M.equivMapOfInjective (e.trans φ).toMonoidHom (e.trans φ).injective).symm.trans
      (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans e₁)
  rcases hφ with h | h <;> rw [h] at hM' hMX'
  ·
    exfalso
    obtain ⟨hE, -⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd hMX' hM'
    have : IsSimpleGroup (CatFactsSp4.Lsub K₁) :=
      CatFactsSp4.isSimpleGroup_Lsub (by rw [hK₁]; omega)
    have : IsSimpleGroup (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 K₁)) :=
      MulEquiv.isSimpleGroup (CatFactsSp4.LtoStated K₁).symm
    have : IsSimpleGroup ↥(M.map (e.trans φ).toMonoidHom) := MulEquiv.isSimpleGroup eM
    have hu : CatFactsSp4.u1 K ∈ M.map (e.trans φ).toMonoidHom := by
      rcases hE with hE | hE <;> rw [hE]
      exacts [CatFactsSp4.u1_mem_E1, CatFactsSp4.u1_mem_E2]
    have hz : (⟨CatFactsSp4.u1 K, hu⟩ : ↥(M.map (e.trans φ).toMonoidHom)) ∈
        center ↥(M.map (e.trans φ).toMonoidHom) :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp (hMX' g.2))
    rcases (inferInstance : (center ↥(M.map (e.trans φ).toMonoidHom)).Normal).eq_bot_or_eq_top
      with hb | htop
    · rw [hb, mem_bot] at hz
      exact CatFactsSp4.u1_ne_one h2 (congrArg Subtype.val hz)
    · apply CatFactsSp4.ne_bot_of_isPComponent hM'
      rw [← CatFactsSp4.commutator_eq_of_isPComponent hMX' hM',
        commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp
        (htop ▸ mem_top (⟨x, hx⟩ : ↥(M.map (e.trans φ).toMonoidHom))) ⟨y, hy⟩)
  ·
    obtain ⟨hL, -⟩ := CatFactsSp4.pComponent_centralizer_u2 hodd hMX' hM'
    have hcard : Nat.card K * (Nat.card K ^ 2 - 1) / 2 =
        Nat.card K₁ * (Nat.card K₁ ^ 2 - 1) / 2 := by
      rw [← CatFactsSp4.card_Lsub hodd, ← CatFactsSp4.card_statedProj_statedSL_two_odd hodd₁,
        ← hL]
      exact Nat.card_congr eM.toEquiv
    have hq := eq_of_card_psl_two_eq hodd hodd₁ hcard
    rw [hK, hK₁] at hq
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    obtain ⟨m₁, rfl⟩ : ∃ m₁, f₁ = m₁ + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨hpp, hmm⟩ := Nat.Prime.pow_inj hp hp₁ hq
    exact ⟨hpp.symm, by rw [hmm]⟩

end General

section Quotient

variable {Y : Type} [Group Y] [Finite Y]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Y)

theorem le_and_equiv_or_config {M P K J JB : Subgroup Y} {t : Y} (hM : IsPComponent 2 M)
    (hP : IsPGroup 2 P) (hKC : K ≤ centralizer (P : Set Y))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))))
    (hKM : K ≤ M ⊔ pPrimeCore 2 Y) {p' f' p f : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hf' : 1 ≤ f') (h5' : 5 ≤ p' ^ f')
    (hKLie : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSp 2 p' f')
    (htK : t ∈ K) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hJC : J ≤ centralizer ({t} : Set Y))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set Y))))
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hpp : p = p') (hff : f = f')
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f)
    (hJBK : JB ≤ K) (hJBJ : JB ≤ J) (hJBp : ⁅JB, JB⁆ = JB) (hJB1 : JB ≠ ⊥)
    (hJB : JB ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    K ≤ M ∧ J ≤ M ∧ (Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* ↥K ⧸ pPrimeCore 2 ↥K) ∨
      QPUJConfig ↥(M.map π) p' f' p f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (π).ker := OddQuot.not_two_dvd_card_ker
  obtain ⟨Mb, hMb, hMs, hMbeq, -⟩ := id hM
  subst hMbeq
  have hsol : Group.IsSolvable (pPrimeCore 2 Y) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ OddQuot.odd_card_pPrimeCore
  have hKp : Group.IsPerfect ↥K := B5a.isPerfect_of_isPComponent_subgroupOf hKC hK
  have hJp : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJ
  have hKM' : K ≤ M :=
    RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hMs hKp hKM
  have hKMb : K.map π ≤ M.map π := map_mono hKM'
  have hJBbp : ⁅JB.map π, JB.map π⁆ = JB.map π := by rw [← map_commutator, hJBp]
  have hJBb1 : JB.map π ≠ ⊥ := by
    intro h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact hJB1 (Pump516.eq_bot_of_perfect_of_le_odd hJBp h1 OddQuot.odd_card_pPrimeCore)
  obtain ⟨hJbC, hJbpc⟩ :=
    Pump516.isPComponent_map_centralizer ⟨1, by rw [pow_one, pow_two, ht2]⟩ hJC hJ
  have hJBO : ¬ JB.map π ≤ (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype := by
    intro hle
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype)) := by
      rw [card_map_of_injective (J.map π).subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    exact hJBb1 (Pump516.eq_bot_of_perfect_of_le_odd hJBbp hle hodd)
  have hJMb : J.map π ≤ M.map π := Pump516.le_of_isPComponent_of_perfect hJbC hJbpc hMb.2
    (map_mono hJBJ) ((map_mono hJBK).trans hKMb) hJBbp hJBO
  have hJM : J ≤ M := RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hMs
    hJp (Seven.le_sup_pPrimeCore_of_map_le hJMb)
  obtain ⟨eK⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker K
  refine ⟨hKM', hJM, ?_⟩
  by_cases hKMeq : K.map π = M.map π
  · obtain ⟨eM⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker M
    exact Or.inl ⟨eM.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (MulEquiv.subgroupCongr hKMeq.symm)).trans eK.symm)⟩
  refine Or.inr ?_
  have hO : pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hPM : P.map π ≤ normalizer ((M.map π : Subgroup (Y ⧸ pPrimeCore 2 Y)) :
      Set (Y ⧸ pPrimeCore 2 Y)) := by
    rintro _ ⟨β, hβ, rfl⟩
    refine Pump516.mem_normalizer_of_le_centralizer hMb ((map_mono hJBK).trans hKMb) hJBbp
      hJBb1 ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_iff.mp (hKC (hJBK hj)) β hβ]
  have hLC : K.map π ≤ centralizer ((P.map π : Subgroup (Y ⧸ pPrimeCore 2 Y)) :
      Set (Y ⧸ pPrimeCore 2 Y)) := (map_mono hKC).trans (OddQuot.centralizer_map_eq hP).ge
  have hLpc := OddQuot.isPComponent_map π hker hKC hK
  rw [← OddQuot.centralizer_map_eq hP] at hLpc
  have hKLieb := OddQuot.lieModel_of_equiv eK hKLie
  have hZ : center (↥(K.map π) ⧸ pPrimeCore 2 ↥(K.map π)) = ⊥ := by
    have := Seven.isSimpleGroup_of_lieModel_psp hKLieb
    have : Group.IsPerfect ↥(K.map π) := Subgroup.isPerfect_iff.mpr (by
      rw [← map_commutator, Subgroup.isPerfect_iff.mp hKp])
    have : Group.IsPerfect (↥(K.map π) ⧸ pPrimeCore 2 ↥(K.map π)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Seven.center_eq_bot_of_isPerfect
  have ht2b : π t * π t = 1 := by rw [← map_mul, ht2, map_one]
  have ht1b : π t ≠ 1 := by
    intro h1
    apply ht1
    have h2 : IsPGroup 2 (zpowers t) :=
      Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, ht2]⟩
    exact OddQuot.injOn_of_isPGroup h2 (mem_zpowers t) (one_mem _) (by rw [h1, map_one])
  have htZ := exists_not_commute hKMb hZ (mem_map_of_mem π htK) ht2b ht1b
  obtain ⟨eJ⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker J
  have hJ₀ : JB.map π ⊔ (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype = J.map π := by
    have h1 : ((pPrimeCore 2 ↥J).map J.subtype).map π =
        (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype := OddQuot.map_oddCoreIn π hker J
    rw [← h1, ← Subgroup.map_sup, hJB]
  exact config_of_component hO hMb (hP.map π) hPM hKMb hLC hLpc hKMeq hp' hp2' hf' h5' hKLieb
    (mem_map_of_mem π htK) ht2b htZ hJMb hJbC hJbpc hp hp2 hf h5 hpp hff
    (OddQuot.lieModel_of_equiv eJ hJLie) (map_mono hJBK) (map_mono hJBJ) hJ₀

end Quotient

end QPUJ

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem Setting.exists_sl2_inf_of_catalog (hQ : CFQPUJStatement71) (hConj : CFSp4Conj)
    (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent) [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (s : Setting X) (hNS : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) {b : X}
    (hb : Lemma61Case2 s.h s.y b) {M : Subgroup X} (hMC : M ≤ centralizer ({b} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hLM : Lay s.h s.y ≤ M ⊔ oddCoreIn (centralizer ({b} : Set X))) {z : X} (hzD : z ∈ s.h.D)
    (hzS : ∀ t ∈ s.h.S, t * z = z * t) (hz2 : orderOf z = 2) :
    ∃ N : Subgroup X, N ≤ centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * z} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓
        centralizer ({s.h.a * b * z} : Set X))) ∧ s.h.a * b * z ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb0 := hb
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩ := hb
  have hb' : d.Case2 b := ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩
  have hbB0 : b ∈ B0 s.h s.y := hb4
  have habL : s.h.a * b ∈ Lay s.h s.y := by
    have h1 := hb'.ab_mem_L hNS
    rwa [hd, Setting.toData_h, Setting.toData_y] at h1
  have hbb : b * b = 1 := by rw [← pow_two, ← hb1, pow_orderOf_eq_one]
  have hab2 : s.h.a * b * (s.h.a * b) = 1 := s.ac_mul_ac hbB0 hbb
  have hab1 : s.h.a * b ≠ 1 := s.ac_ne_one hbB0
  set Y := centralizer ({b} : Set X)
  have hbne : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb1
    exact absurd hb1 (by norm_num)
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hbne
    have hcen : b ∈ center X := by
      rw [mem_center_iff]
      intro w
      have hw : w ∈ Y := by
        rw [htop]
        exact mem_top w
      exact mem_centralizer_singleton_iff.mp hw
    have hbot : center X = ⊥ := by
      rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨u, v, huv⟩ := hnonab
        exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center X)) u)
    rw [hbot] at hcen
    exact mem_bot.mp hcen
  have hKY : SectionRank.IsKGroupCat ↥Y := isKGroupCat_of_ne_top' hK hYne
  have hB0Y : B0 s.h s.y ≤ Y := fun c hc =>
    normalizer_B0_le_U hb0 (mem_inf.mpr ⟨s.B0_le_S hc, le_normalizer hc⟩)
  have hCB0Y : centralizer (B0 s.h s.y : Set X) ≤ Y :=
    centralizer_le (Set.singleton_subset_iff.mpr hbB0)
  have hLY : Lay s.h s.y ≤ Y := s.L_le_centralizer.trans hCB0Y
  have haY : s.h.a ∈ Y :=
    mem_centralizer_singleton_iff.mpr (s.h.comm_a (s.B0_le_S hbB0)).symm
  have hbY : b ∈ Y := mem_centralizer_singleton_iff.mpr rfl
  have hJq := B5a.isQuasisimple_J s.h
  have hbJ : zpowers b ≤ coreActionKernel s.h.J := (zpowers_le.mpr hbB0).trans s.B0_le_kernel
  have hb2g : IsPGroup 2 (zpowers b) :=
    Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, hbb]⟩
  have hbCa : zpowers b ≤ centralizer ({s.h.a} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (s.h.comm_a (s.B0_le_S hbB0)))
  obtain ⟨-, -, hJs, -, -⟩ := id s.h.isPComponent_J
  set Jb := GSLit.fixedLayer s.h.J (zpowers b)
  have hJb : IsPComponent 2 (Jb.subgroupOf (centralizer ({s.h.a} : Set X) ⊓ Y)) := by
    have h1 := GSLit.fixedLayer_isPComponent s.h.J_le hJs hbCa hbJ hb2g hJq
    rwa [centralizer_zpowers_eq] at h1
  have hJbC : Jb ≤ centralizer ({s.h.a} : Set X) ⊓ Y := by
    refine le_inf (((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans s.h.J_le) ?_
    have h1 := (GSLit.fixedLayer_le_inf s.h.J (zpowers b)).trans inf_le_right
    rwa [centralizer_zpowers_eq] at h1
  have hJbY : Jb ≤ Y := hJbC.trans inf_le_right
  obtain ⟨hJ0Jb, hJ0sup⟩ :=
    GSLit.fixedLayer_nested hJq s.B0_le_kernel s.isPGroup_B0 (zpowers_le.mpr hbB0)
  have hJ0C : J0 s.h s.y ≤ centralizer ({s.h.a} : Set X) ⊓ centralizer (B0 s.h s.y : Set X) :=
    le_inf s.J0_le_centralizer_a s.J0_le_centralizer_B0
  have hJ0p : ⁅J0 s.h s.y, J0 s.h s.y⁆ = J0 s.h s.y := Subgroup.isPerfect_iff.mp
    (B5a.isPerfect_of_isPComponent_subgroupOf hJ0C s.isPComponent_J0)
  have hJ01 : J0 s.h s.y ≠ ⊥ := by
    intro hbot
    have := B5a.nontrivial_of_isPComponent_subgroupOf hJ0C s.isPComponent_J0
    rw [hbot] at this
    exact not_nontrivial _ this
  set a' : Y := ⟨s.h.a, haY⟩
  set b' : Y := ⟨b, hbY⟩
  have hbZ : b' ∈ center Y := mem_center_iff.mpr fun w => Subtype.ext
    (mem_centralizer_singleton_iff.mp w.2)
  have hab2' : a' * b' * (a' * b') = 1 := Subtype.ext hab2
  have hab1' : a' * b' ≠ 1 := fun h1 => hab1 (congrArg Subtype.val h1)
  set P : Subgroup Y := (B0 s.h s.y).subgroupOf Y
  have hP : IsPGroup 2 P := s.isPGroup_B0.comap_subtype
  have hCP : centralizer (P : Set Y) = (centralizer (B0 s.h s.y : Set X)).subgroupOf Y :=
    B5a.centralizer_subgroupOf hB0Y
  set K : Subgroup Y := (Lay s.h s.y).subgroupOf Y
  have hKC : K ≤ centralizer (P : Set Y) := by
    rw [hCP]
    exact fun w hw => s.L_le_centralizer hw
  have hKpc : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))) := by
    rw [hCP]
    exact (isPComponent_subgroupOf_subgroupOf_iff' hCB0Y 2 Nat.prime_two).mpr s.isPComponent_Lay
  have htK : a' * b' ∈ K := habL
  set J : Subgroup Y := Jb.subgroupOf Y
  have hCtY : (centralizer ({s.h.a} : Set X) ⊓ Y).subgroupOf Y =
      centralizer ({a' * b'} : Set Y) := by
    rw [QPUJ.centralizer_mul_of_mem_center hbZ]
    ext w
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true,
      mem_centralizer_singleton_iff]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hJC : J ≤ centralizer ({a' * b'} : Set Y) := by
    rw [← hCtY]
    exact fun w hw => hJbC hw
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({a' * b'} : Set Y))) := by
    rw [← hCtY]
    exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two).mpr hJb
  set JB : Subgroup Y := (J0 s.h s.y).subgroupOf Y
  have hJ0Y : J0 s.h s.y ≤ Y := s.J0_le_L.trans hLY
  have hJBK : JB ≤ K := fun w hw => s.J0_le_L hw
  have hJBJ : JB ≤ J := fun w hw => hJ0Jb hw
  have hJBp : ⁅JB, JB⁆ = JB := by
    apply map_injective Y.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJ0Y, hJ0p]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    apply hJ01
    have h1 : JB.map Y.subtype = J0 s.h s.y := map_subgroupOf_eq_of_le hJ0Y
    rw [← h1, hbot, Subgroup.map_bot]
  have hJB : JB ⊔ (pPrimeCore 2 ↥J).map J.subtype = J := by
    apply map_injective Y.subtype_injective
    have hcomp : Y.subtype.comp J.subtype =
        Jb.subtype.comp (subgroupOfEquivOfLe hJbY).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJ0Y, map_subgroupOf_eq_of_le hJbY, map_map,
      hcomp, ← map_map, pPrimeCore_map_iso]
    exact hJ0sup
  have hKM : K ≤ M.subgroupOf Y ⊔ pPrimeCore 2 ↥Y := by
    rw [← map_le_map_iff_of_injective Y.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLY, map_subgroupOf_eq_of_le hMC]
    exact hLM
  have hKLie : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSp 2 s.p' s.f' :=
    OddQuot.lieModel_of_equiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hLY).symm) s.hLLie
  obtain ⟨eJb⟩ := QPUJ.nonempty_fixedLayer_quot_equiv hJq hbJ hb2g
  have hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 s.p s.f :=
    OddQuot.lieModel_of_equiv ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJbY)).trans eJb).symm s.hJLie
  have hq : s.p = s.p' ∧ s.f = s.f' := by
    set tL : ↥(Lay s.h s.y) := ⟨s.h.a * b, habL⟩
    have htL2 : tL * tL = 1 := Subtype.ext hab2
    have htL1 : tL ≠ 1 := fun h1 => hab1 (congrArg Subtype.val h1)
    have hJ0Lt : J0 s.h s.y ≤ Lay s.h s.y ⊓ centralizer ({s.h.a * b} : Set X) :=
      le_inf s.J0_le_L (Setting.J0_le_centralizer_ac hbB0)
    have hpc1 : IsPComponent 2 ((J0 s.h s.y).subgroupOf
        (Lay s.h s.y ⊓ centralizer ({s.h.a * b} : Set X))) :=
      UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt (s.L_inf_centralizer_le hbB0)
        s.isPComponent_J0
    have hpc2 : IsPComponent 2 (((J0 s.h s.y).subgroupOf (Lay s.h s.y)).subgroupOf
        (centralizer ({tL} : Set ↥(Lay s.h s.y)))) := by
      rw [← inf_centralizer_subgroupOf habL]
      exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
        Nat.prime_two).mpr hpc1
    have hMt : (J0 s.h s.y).subgroupOf (Lay s.h s.y) ≤
        centralizer ({tL} : Set ↥(Lay s.h s.y)) := by
      rw [← inf_centralizer_subgroupOf habL]
      intro v hv
      exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
    obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map htL2 hMt hpc2
    obtain ⟨e0⟩ := QPUJ.nonempty_fixedLayer_quot_equiv hJq s.B0_le_kernel s.isPGroup_B0
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv
      (QuotientGroup.mk' (pPrimeCore 2 ↥(Lay s.h s.y))) OddQuot.not_two_dvd_card_ker
      ((J0 s.h s.y).subgroupOf (Lay s.h s.y))
    exact QPUJ.eq_of_isPComponent_psp s.hp' s.hp2' s.hLLie (orderOf_mk_eq_two htL2 htL1) hMbt
      hMbpc s.hp s.hp2 s.hf s.h5 (OddQuot.lieModel_of_equiv
        ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
          (subgroupOfEquivOfLe s.J0_le_L)).symm.trans e1)
        (OddQuot.lieModel_of_equiv e0.symm s.hJLie))
  have h5' : 5 ≤ s.p' ^ s.f' := by
    rw [← hq.1, ← hq.2]
    exact s.h5
  obtain ⟨hKM', hJM', hcase⟩ := QPUJ.le_and_equiv_or_config hMpc hP hKC hKpc hKM s.hp' s.hp2'
    s.hf' h5' hKLie htK hab2' hab1' hJC hJpc s.hp s.hp2 s.hf s.h5 hq.1 hq.2 hJLie hJBK hJBJ hJBp
    hJB1 hJB
  have hLayM : Lay s.h s.y ≤ M := fun x hx => hKM' (show (⟨x, hLY hx⟩ : Y) ∈ K from hx)
  have hJbM : Jb ≤ M := fun x hx => hJM' (show (⟨x, hJbY hx⟩ : Y) ∈ J from hx)
  rcases hcase with heM | hconf
  ·
    obtain ⟨eM⟩ := heM
    have hLieM : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSp 2 s.p' s.f' :=
      OddQuot.lieModel_of_equiv ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (subgroupOfEquivOfLe hMC).symm).trans (eM.trans
          (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
            (subgroupOfEquivOfLe hLY)))).symm s.hLLie
    have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have habz : s.h.a * b * z = z * (s.h.a * b) := Setting.commute_z hzS hbB0
    have hzP : z ∉ s.h.P := by
      intro hzP
      have : z ∈ s.h.D ⊓ s.h.P := mem_inf.mpr ⟨hzD, hzP⟩
      rw [s.h.D_inf_P_eq_bot s.hZJ, mem_bot] at this
      exact hz1 this
    have habP : s.h.a * b ∈ s.h.P := mul_mem s.h.a_mem_P (s.h.B_le_P (s.B0_le_B hbB0))
    have hzab : z ≠ s.h.a * b := fun h1 => hzP (h1 ▸ habP)
    have hJbt : Jb ≤ centralizer ({s.h.a * b} : Set X) := by
      intro j hj
      obtain ⟨hja, hjb⟩ := mem_inf.mp (hJbC hj)
      have h1 : j * s.h.a = s.h.a * j := mem_centralizer_singleton_iff.mp hja
      have h2 : j * b = b * j := mem_centralizer_singleton_iff.mp hjb
      rw [mem_centralizer_singleton_iff]
      calc j * (s.h.a * b) = j * s.h.a * b := by group
        _ = s.h.a * (j * b) := by rw [h1]; group
        _ = s.h.a * b * j := by rw [h2]; group
    have hYt : M ⊓ centralizer ({s.h.a * b} : Set X) ≤ centralizer ({s.h.a} : Set X) ⊓ Y := by
      intro m hm
      obtain ⟨hmM, hmab⟩ := mem_inf.mp hm
      have h1 : m * b = b * m := mem_centralizer_singleton_iff.mp (hMC hmM)
      have h2 : m * (s.h.a * b) = s.h.a * b * m := mem_centralizer_singleton_iff.mp hmab
      have h3 : m * s.h.a * b = s.h.a * m * b := by
        calc m * s.h.a * b = m * (s.h.a * b) := by group
          _ = s.h.a * b * m := h2
          _ = s.h.a * (b * m) := by group
          _ = s.h.a * (m * b) := by rw [h1]
          _ = s.h.a * m * b := by group
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (mul_right_cancel h3), hMC hmM⟩
    obtain ⟨N, hNX, hNpc, habzN, p', n, hp', hp'2, hn, ⟨eN⟩⟩ :=
      exists_sl2_of_cf hComp s.hp' s.hp2' s.hf' hLieM (hLayM habL) hab2
        hab1 hzz hz1 habz hzab hJbM hJbt hYt hJb (hJ0Jb (s.mem_J0 hzD hzS hz2))
    obtain ⟨-, -, hMs, -⟩ := id hMpc
    exact ⟨N, le_inf (hNX.trans (inf_le_left.trans hMC)) (hNX.trans inf_le_right),
      isPComponent_inf_of_isSubnormal hMC hMs hNX hNpc, habzN, p', n, hp', hp'2, hn, ⟨eN⟩⟩
  ·
    exfalso
    have hKYb : SectionRank.IsKGroupCat (↥Y ⧸ pPrimeCore 2 ↥Y) :=
      OddQuot.isKGroupCat_of_surjective hKY _ (QuotientGroup.mk'_surjective _)
    have := hconf.1.2.1
    exact hQ _ s.p' s.f' s.p s.f hconf (SectionRank.catalog_of_isKGroupCat_of_surjective hKYb
      ((M.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)))
      (QuotientGroup.mk' (center _)) (QuotientGroup.mk'_surjective _))

end Seven

theorem quasisimplePumpUpStatement71_of_catalog (hQ : CFQPUJStatement71) (hConj : CFSp4Conj)
    (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent) :
    QuasisimplePumpUpStatement71 := by
  intro X _ _ _ hnonab hK _ _ _ _ _ _ _ _ _ s _ _ hNS b hb M hMC hMpc hLM _ z hzD hzS hz2
  exact s.exists_sl2_inf_of_catalog hQ hConj hComp hOut hCent hnonab hK hNS hb hMC hMpc hLM hzD
    hzS hz2

end CFSG.ComponentClassification.GSThmB
