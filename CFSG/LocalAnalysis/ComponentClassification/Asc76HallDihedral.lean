module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76HallDihedralGW
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourCases
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22
public import CFSG.LocalAnalysis.ComponentClassification.Asc75Theorem3
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D14

public section

namespace CFSG.ComponentClassification.Asc76X.HallDihedral

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec4
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (dihedral_cover_generation_holds)

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {Ω : Set (Subgroup G)} {S K R U : Subgroup G} {t z : G}

theorem false_of_simple
    (h : Hyp Ω S K R U t z) (hB : IsSylowOf 2 h.rPrime (normalClosure (h.rPrime : Set G)))
    (hKn : ¬ K.Normal) {L : Subgroup G} [hLn : L.Normal]
    (hLG : L ≤ normalClosure (h.rPrime : Set G)) (hLs : IsSimpleGroup L) (hZ : center L = ⊥)
    (hq : CFSG.Open.IsQuasisimple L)
    (hd : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo (L ⧸ center L))
    (hCL : ∀ c ∈ normalClosure (h.rPrime : Set G), (∀ x ∈ L, c * x = x * c) → c = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG₁n : (normalClosure (h.rPrime : Set G)).Normal := normalClosure_normal
  have hQ : IsSylowOf 2 (S ⊓ L) L :=
    h.sylow.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hLn])
  have hLS : L ⊓ S ≠ ⊥ := by
    intro hb
    have hb' : S ⊓ L = ⊥ := by rw [inf_comm]; exact hb
    have hodd : Odd (Nat.card L) := by
      have h1 := (isSylowOf_iff.mp hQ).2.2
      rw [hb', Subgroup.relIndex_bot_left] at h1
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
    have h1 : L ≤ CFSG.Open.standardComponentOddCore G := le_sSup ⟨hLn, hodd⟩
    rw [h.asm.oddCore, le_bot_iff] at h1
    have : Nontrivial L := hLs.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : L)
    apply ha
    have h2 : (a : G) ∈ (⊥ : Subgroup G) := h1 ▸ a.2
    exact Subtype.ext (mem_bot.mp h2)
  have hzL : z ∈ L := h.z_mem_of_normal hB hLG hLS
  obtain ⟨E, hER, hE, hE4⟩ := h.rot.exists_fourGroup
  have hgen : ¬ L ≤ CFSG.ComponentClassification.AschbacherKnownGroup.centralizerJoin E L := by
    intro hle
    have hLN : L ≤ normalizer (K : Set G) := hle.trans (iSup_le fun e => iSup_le fun he =>
      iSup_le fun he1 => inf_le_right.trans
        (CFSG.ComponentClassification.Asc75T4.centralizer_le_of_involution h.tight
          (h.sylowR.le (hER he)) (orderOf_eq_prime (hE.2 e he) he1)))
    have hn : ((K ⊓ L).subgroupOf L).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx => ?_
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyK, hyL⟩
        exact ⟨(mem_normalizer_iff.mp (hLN hx) y).mp hyK, hLn.conj_mem y hyL x⟩
      · rintro ⟨hyK, hyL⟩
        refine ⟨(mem_normalizer_iff.mp (hLN hx) y).mpr hyK, ?_⟩
        have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [e]
        have := hLn.conj_mem _ hyL x⁻¹
        simpa using this
    rcases hn.eq_bot_or_eq_top with hb | ht
    · have h1 : (⟨z, hzL⟩ : L) ∈ (K ⊓ L).subgroupOf L := ⟨h.z_mem_K, hzL⟩
      rw [hb, mem_bot] at h1
      exact h.z_ne (congrArg Subtype.val h1)
    · have hLK : L ≤ K := fun x hx => by
        have h1 : (⟨x, hx⟩ : L) ∈ (K ⊓ L).subgroupOf L := by rw [ht]; exact mem_top _
        exact h1.1
      apply hKn
      rw [← normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have heven : Even (Nat.card L) := by
        have h1 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.z_mul) h.z_ne
        have h2 : orderOf (⟨z, hzL⟩ : L) = 2 := by rw [← Subgroup.orderOf_coe]; exact h1
        exact even_iff_two_dvd.mpr (h2 ▸ orderOf_dvd_natCard _)
      refine CFSG.ComponentClassification.Asc75T4.mem_normalizer_of_le_rightConjugate h.tight hLK
        heven fun x hx => ?_
      rw [mem_rightConjugate_iff]
      exact hLK (hLn.conj_mem x hx g)
  have hz2 : (Nat.card (center L)).factorization 2 ≤ 1 := by
    rw [hZ, card_bot, Nat.factorization_one]
    simp
  have hEN : E ≤ normalizer (L : Set G) := by
    rw [normalizer_eq_top_iff.mpr hLn]
    exact le_top
  obtain ⟨-, hEL⟩ := dihedral_cover_generation_holds G L E hq hd hz2 hEN ⟨hE, hE4⟩ hgen
  obtain ⟨r, hrE, hr1, hrz⟩ := Thm3Four.exists_mem_ne_ne' (T := E) (by omega) 1 z
  have hrR : r ∈ R := hER hrE
  have hrr : r * r = 1 := by
    have := hE.2 r hrE
    rwa [pow_two] at this
  have hrU : r ∉ U := fun hrU => by
    rcases h.z_unique r hrU hrr with e | e
    · exact hr1 e
    · exact hrz e
  have hrS : r ∈ S := h.le hrR
  have h1 : r ∈ ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := hEL hrE
  rw [normal_mul] at h1
  obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.mp h1
  have hcx : ∀ x ∈ L, c * x = x * c := fun x hx => (mem_centralizer_iff.mp hc x hx).symm
  have hcl : c * l = l * c := hcx l hl
  have hcc : c * c = 1 := by
    have hsq : l * c * (l * c) = l * l * (c * c) := by
      calc l * c * (l * c) = l * (c * l) * c := by group
        _ = l * (l * c) * c := by rw [hcl]
        _ = l * l * (c * c) := by group
    have hc2L : c * c ∈ L := by
      have e : c * c = (l * l)⁻¹ * (l * c * (l * c)) := by rw [hsq]; group
      rw [e, hlc, hrr, mul_one]
      exact inv_mem (mul_mem hl hl)
    have hc2C : c * c ∈ centralizer (L : Set G) := mul_mem hc hc
    have h2 : (⟨c * c, hc2L⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hc2C y y.2)
    rw [hZ, mem_bot] at h2
    exact congrArg Subtype.val h2
  have hll : l * l = 1 := by
    have e : l * l = l * c * (l * c) * (c * c)⁻¹ := by
      calc l * l = l * l * (c * c) * (c * c)⁻¹ := by group
        _ = l * (l * c) * c * (c * c)⁻¹ := by group
        _ = l * (c * l) * c * (c * c)⁻¹ := by rw [hcl]
        _ = l * c * (l * c) * (c * c)⁻¹ := by group
    rw [e, hlc, hrr, hcc, inv_one, mul_one]
  have hcG₁ : ∀ g ∈ normalClosure (h.rPrime : Set G), c * g = g * c := by
    intro g hg
    have hcomm : c * g * c⁻¹ * g⁻¹ ∈ normalClosure (h.rPrime : Set G) :=
      mul_mem (hG₁n.conj_mem g hg c) (inv_mem hg)
    have h2 := hCL _ hcomm fun x hx => by
      have hy : g⁻¹ * x * g ∈ L := by
        have := hLn.conj_mem x hx g⁻¹
        simpa using this
      have hcy : c⁻¹ * (g⁻¹ * x * g) = (g⁻¹ * x * g) * c⁻¹ :=
        (Commute.inv_left (hcx _ hy)).eq
      calc c * g * c⁻¹ * g⁻¹ * x = c * g * (c⁻¹ * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = c * g * ((g⁻¹ * x * g) * c⁻¹) * g⁻¹ := by rw [hcy]
        _ = c * x * (g * c⁻¹ * g⁻¹) := by group
        _ = x * c * (g * c⁻¹ * g⁻¹) := by rw [hcx x hx]
        _ = x * (c * g * c⁻¹ * g⁻¹) := by group
    calc c * g = c * g * c⁻¹ * g⁻¹ * (g * c) := by group
      _ = g * c := by rw [h2, one_mul]
  have hconj : ∀ x ∈ L, l * x * l⁻¹ = r * x * r⁻¹ := by
    intro x hx
    rw [← hlc]
    calc l * x * l⁻¹ = l * (c * x * c⁻¹) * l⁻¹ := by rw [hcx x hx, mul_inv_cancel_right]
      _ = l * c * x * (l * c)⁻¹ := by group
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  have hfwd : ∀ y ∈ S ⊓ L, l * y * l⁻¹ ∈ S ⊓ L := by
    rintro y ⟨hyS, hyL⟩
    rw [hconj y hyL]
    exact mem_inf.mpr ⟨mul_mem (mul_mem hrS hyS) (inv_mem hrS), hLn.conj_mem y hyL r⟩
  have hlN : l ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hfwd y, fun hy => ?_⟩
    have h2 := hfwd _ hy
    have e : l * (l * y * l⁻¹) * l⁻¹ = y := by
      calc l * (l * y * l⁻¹) * l⁻¹ = l * l * y * (l * l)⁻¹ := by group
        _ = y := by rw [hll]; group
    rwa [e] at h2
  have hlQ : l ∈ S ⊓ L := by
    have hl2 : IsPGroup 2 (zpowers l) :=
      isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hll)
    have hP : IsPGroup 2 (zpowers l ⊔ (S ⊓ L) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hl2 hQ.isPGroup ((zpowers_le).mpr hlN)
    have e := hQ.eq_of_le le_sup_right (sup_le ((zpowers_le).mpr hl) inf_le_right) hP
    rw [← e]
    exact mem_sup_left (mem_zpowers l)
  have hlR' : l ∈ h.rPrime := by
    rw [← h.inf_normalClosure hB]
    exact mem_inf.mpr ⟨hlQ.1, hLG hl⟩
  have hlinvU : ∀ u ∈ U, l * u * l⁻¹ = u⁻¹ := by
    intro u hu
    have hcu : c * u = u * c := hcG₁ u (hB.le (h.rot_rPrime.le hu))
    calc l * u * l⁻¹ = l * (c * u * c⁻¹) * l⁻¹ := by rw [hcu, mul_inv_cancel_right]
      _ = l * c * u * (l * c)⁻¹ := by group
      _ = u⁻¹ := by rw [hlc]; exact h.rot.conj_eq r hrR hrU u hu
  have hlU : l ∉ U := fun hlU => by
    obtain ⟨ρ, hρ, hρo⟩ := h.rot.exists_gen
    have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
    have h2 := hlinvU ρ hρU
    have h3 : l * ρ = ρ * l := h.rot.commute_of_mem hlU hρU
    rw [h3, mul_assoc, mul_inv_cancel, mul_one] at h2
    apply h.rot.gen_mul_self_ne_one hρo
    calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h2]
      _ = 1 := inv_mul_cancel ρ
  have hl' : Outer Ω S U l := ⟨h.zinv_of_mem_rPrime hlR' hlU, hlQ.1, hlU⟩
  have hlr : l * r = r * l := by
    rw [← hlc]
    calc l * (l * c) = l * (c * l) := by rw [hcl]
      _ = l * c * l := by group
  rcases hl'.cent h hrR hlr with e | e
  · exact hrU (e ▸ U.one_mem)
  · exact hrU (e ▸ h.z_mem)

theorem normal
    (h : Hyp Ω S K R U t z) :
    K.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hKn
  have hB := h.isSylowOf_rPrime
  have hG₁n : (normalClosure (h.rPrime : Set G)).Normal := normalClosure_normal
  have hO := h.oddCore_eq_bot
  have hDih := h.hasDihedralSylowTwo hB
  by_cases hNC : CFSG.HasNormalPComplement 2 (normalClosure (h.rPrime : Set G))
  ·
    obtain ⟨N, hN, hcop, hq⟩ := hNC
    have hN1 : N = ⊥ := by
      have h1 : N ≤ CFSG.oddCore (normalClosure (h.rPrime : Set G)) :=
        le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩
      rw [hO] at h1
      exact le_bot_iff.mp h1
    subst hN1
    have hM2 : IsPGroup 2 (normalClosure (h.rPrime : Set G)) :=
      hq.of_equiv QuotientGroup.quotientBot
    exact hKn (h.normal_of_eq (hB.eq_of_le hB.le le_rfl hM2))
  rcases CFSG.ABGDGroups.aSeven_or_exists_normal_psl2 hDih hNC hO with
    he7 | ⟨F, _, _, hF, N, hNn, ⟨eN⟩, hCN⟩
  ·
    obtain ⟨e7⟩ := he7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : IsSimpleGroup (normalClosure (h.rPrime : Set G)) := e7.isSimpleGroup
    have hcard : Nat.card (normalClosure (h.rPrime : Set G)) = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hZ : center (normalClosure (h.rPrime : Set G)) = ⊥ :=
      Thm3Four.center_eq_bot_of_simple (p := 2) (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    have hq : CFSG.Open.IsQuasisimple (normalClosure (h.rPrime : Set G)) :=
      CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_of_mulEquiv e7.symm
        (CFSG.ComponentClassification.CatalogueBAlternating.alternating_quasisimple (by simp))
    set eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := normalClosure (h.rPrime : Set G))) with heZ
    have hd := CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_mulEquiv' eZ.symm
      (CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_gw hDih)
    refine h.false_of_simple hB hKn le_rfl hs hZ hq hd fun c hc hcx => ?_
    have h1 : (⟨c, hc⟩ : normalClosure (h.rPrime : Set G)) ∈
        center (normalClosure (h.rPrime : Set G)) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hcx y y.2).symm
    rw [hZ, mem_bot] at h1
    exact congrArg Subtype.val h1
  ·
    set N' := N.map (normalClosure (h.rPrime : Set G)).subtype with hN'def
    have eN' : N' ≃* CFSG.GorensteinWalter.PSL2 F :=
      (N.equivMapOfInjective _ (normalClosure (h.rPrime : Set G)).subtype_injective).symm.trans eN
    have hN'M : N' ≤ normalClosure (h.rPrime : Set G) := map_subtype_le N
    have hN'n : ∀ m ∈ normalClosure (h.rPrime : Set G), ∀ x ∈ N', m * x * m⁻¹ ∈ N' := by
      rintro m hm _ ⟨y, hy, rfl⟩
      exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hNn.conj_mem y hy ⟨m, hm⟩, rfl⟩
    have hCN' : ∀ c ∈ normalClosure (h.rPrime : Set G), (∀ x ∈ N', c * x = x * c) → c = 1 :=
      fun c hc hcx => by
        have h1 : (⟨c, hc⟩ : normalClosure (h.rPrime : Set G)) ∈ centralizer (N : Set _) := by
          rw [mem_centralizer_iff]
          intro y hy
          apply Subtype.ext
          exact (hcx y ⟨y, hy, rfl⟩).symm
        rw [hCN, mem_bot] at h1
        exact congrArg Subtype.val h1
    by_cases h3 : Nat.card F = 3
    ·
      have : Fintype F := Fintype.ofFinite F
      let eK : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
        (by simpa [Nat.card_eq_fintype_card] using h3)
      have eA : N ≃* alternatingGroup (Fin 4) :=
        eN.trans ((CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
          CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup)
      have hpN : CFSG.pCore 2 N ≠ ⊥ := Thm3Four.pCore_ne_bot_of_equiv_alternating_four eA
      have hV : ((CFSG.pCore 2 N).map N.subtype).Normal :=
        ConjAct.normal_of_characteristic_of_normal
      have hV2 : IsPGroup 2 ((CFSG.pCore 2 N).map N.subtype) := CFSG.pCore_isPGroup.map _
      have hle : (CFSG.pCore 2 N).map N.subtype ≤
          CFSG.pCore 2 (normalClosure (h.rPrime : Set G)) := le_sSup ⟨hV, hV2⟩
      set Q := (CFSG.pCore 2 (normalClosure (h.rPrime : Set G))).map
        (normalClosure (h.rPrime : Set G)).subtype with hQdef
      have hQn : Q.Normal := ConjAct.normal_of_characteristic_of_normal
      have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
      have hQ1 : Q ≠ ⊥ := by
        intro hb
        apply hpN
        rw [hQdef, map_eq_bot_iff_of_injective _ (normalClosure _).subtype_injective] at hb
        rw [hb, le_bot_iff, map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
        exact hle
      have hQS : Q ≤ S := by
        have hp : IsPGroup 2 ↥(Q ⊔ S) := hQ2.to_sup_of_normal_left h.sylow.isPGroup
        have h1 := h.sylow.eq_of_le le_sup_right le_top hp
        rw [← h1]
        exact le_sup_left
      have hzQ : z ∈ Q := h.z_mem_of_normal hB (map_subtype_le _)
        (by rwa [inf_eq_left.mpr hQS])
      have hM2 : IsPGroup 2 (normalClosure (h.rPrime : Set G)) := hQ2.to_le (h.le_of_z_mem hzQ)
      exact hKn (h.normal_of_eq (hB.eq_of_le hB.le le_rfl hM2))
    ·
      have h5 : 5 ≤ Nat.card F := by
        obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hF
        have hodd : Odd (Nat.card F) := hq ▸ hpodd.pow
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      have h4 : 4 ≤ Nat.card F := by omega
      have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
      have hNs : IsSimpleGroup N' := eN'.isSimpleGroup
      have hNnG : N'.Normal := Thm3Four.normal_of_simple hN'M hN'n hNs hCN'
      have hq : CFSG.Open.IsQuasisimple N' :=
        CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_of_mulEquiv eN'.symm
          (CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_psl2 h4)
      have hZ : center N' = ⊥ :=
        CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_psl2 h4 eN'
      have hdP : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo
          (CFSG.GorensteinWalter.PSL2 F) :=
        CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_gw
          (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF)
      set eZ : N' ⧸ center N' ≃* N' :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with heZ
      have hd := CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_mulEquiv'
        (eZ.trans eN').symm hdP
      exact h.false_of_simple hB hKn hN'M hNs hZ hq hd hCN'

end Hyp

theorem hallDihedralFusion :
    HallDihedralFusion := by
  intro G _ _ Ω hΩ hnil hsingle S K R U hS hK hR hRS hU hWU t htZ htS htU
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
  exact (Hyp.mk (Asc76.asc76Lemma22 AschbacherTheorem3.theorem_3_holds) hΩ hnil hsingle hS hK hR
    hRS hU hWU htZ htS htU hzU hz1 hzz).normal

end CFSG.ComponentClassification.Asc76X.HallDihedral
