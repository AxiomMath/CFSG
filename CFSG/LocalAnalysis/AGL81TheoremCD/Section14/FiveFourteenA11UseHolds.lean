module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenTwelve
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11CharNormal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11SylowCharNormal
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.Quasithin.Recognition.F112Crit.Theorem723
import CFSG.ClassicalInvolution.AschTight.Sec7L98G
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.Timmesfeld.Special.TwoCore
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCore_two_eq_pPrimeCore_three_of_quotient_a11 {K : Type} [Group K] [Finite K]
    (hA : Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 11))) :
    CFSG.pCore 2 K = CFSG.pPrimeCore 3 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 11)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  obtain ⟨e⟩ := hA
  have hO2 : CFSG.pCore 2 K ≤ CFSG.pPrimeCore 3 K :=
    CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two Nat.prime_three (by norm_num) K
  refine le_antisymm hO2 ?_
  refine CFSG.GroupTheory.pPrimeCore_le_pCore_of_simple_quotient e ?_ hO2
  intro htop
  have hcard : Nat.card (CFSG.pPrimeCore 3 K) = Nat.card K := by
    rw [htop]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    simpa [hcard] using CFSG.pPrimeCore_coprime_card (p := 3) (G := K)
  have h3 : 3 ∣ Nat.card K := by
    have h3q : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    exact h3q.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 K))
  exact ((Nat.prime_three.coprime_iff_not_dvd).mp hcop) h3

private theorem exists_char_normal_map_subtype {G : Type} [Group G] {X T : Subgroup G}
    (hTX : T ≤ X) {C' : Subgroup ↥X} (hne : C' ≠ ⊥) (hC'T : C' ≤ T.subgroupOf X)
    (hchar : (C'.subgroupOf (T.subgroupOf X)).Characteristic) (hnorm : C'.Normal) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧
      X ≤ Subgroup.normalizer (C : Set G) := by
  obtain ⟨hCT, hCchar⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.map_subtype_characteristic hTX hC'T hchar
  refine ⟨C'.map X.subtype, ?_, hCT, hCchar, ?_⟩
  · intro hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective C' X.subtype_injective).mp hbot)
  · intro x hx
    have hxn : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer (C' : Set ↥X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact (CFSG.Glauberman.mem_normalizer_map_subtype_iff C' ⟨x, hx⟩).mp hxn

private theorem closure_odd_properties {K X : Subgroup G} (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) :
    ∃ L : Subgroup G, L = Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} ∧
      L ≤ X ∧ (L.subgroupOf X).Normal ∧
      L.subgroupOf X = Subgroup.closure {x : ↥X | x ∈ L.subgroupOf X ∧ Odd (orderOf x)} := by
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  refine ⟨Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}, rfl,
    (Subgroup.closure_le X).mpr fun x hx => hKX hx.1, ?_, ?_⟩
  · have hconj : ∀ {s : G}, s ∈ {x : G | x ∈ K ∧ Odd (orderOf x)} →
        ∀ g ∈ X, g * s * g⁻¹ ∈ {x : G | x ∈ K ∧ Odd (orderOf x)} := by
      rintro s ⟨hsK, hso⟩ g hgX
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hXK hgX) s).mp hsK, ?_⟩
      have hord : orderOf (g * s * g⁻¹) = orderOf s := by
        rw [← MulAut.conj_apply]
        exact MulEquiv.orderOf_eq (MulAut.conj g) s
      rw [hord]
      exact hso
    have hLeq : (Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}).subgroupOf X =
        Subgroup.closure (X.subtype ⁻¹' {x : G | x ∈ K ∧ Odd (orderOf x)}) := by
      rw [show (Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}).subgroupOf X =
          (Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}).comap X.subtype from rfl,
        ← Subgroup.closure_coe_preimage_of_subset (K := X)
          (s := {x : G | x ∈ K ∧ Odd (orderOf x)}) (fun x hx => hKX hx.1)]
      rfl
    rw [hLeq]
    exact Subgroup.closure_normal_of_forall_conj_mem (fun g s hs => by
      change (g : G) * (s : G) * (g : G)⁻¹ ∈ K ∧
        Odd (orderOf ((g : G) * (s : G) * (g : G)⁻¹))
      exact hconj hs g g.2)
  · have hgen : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} ≤
        Subgroup.closure {x : G | x ∈ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} ∧
          Odd (orderOf x)} :=
      Subgroup.closure_mono (fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
    refine le_antisymm ?_ ?_
    · exact CFSG.Quasithin.F112Crit.T723.subgroupOf_odd_gen
        ((Subgroup.closure_le X).mpr fun x hx => hKX hx.1) hgen
    · exact (Subgroup.closure_le _).mpr fun x hx => hx.1

private theorem not_le_ker_of_odd_gen {K X L : Subgroup G} (hKX : K ≤ X) (hLX : L ≤ X)
    (hLdef : L = Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)})
    (φ : ↥X →* Equiv.Perm (Fin 11))
    (hker : φ.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf X)
    (e : threeStar K ≃* alternatingGroup (Fin 11)) :
    ¬ L.subgroupOf X ≤ φ.ker := by
  intro hle
  have h3dvd : 3 ∣ Nat.card (alternatingGroup (Fin 11)) := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 11)) 3 h3dvd
  obtain ⟨q, hq⟩ := e.surjective a
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) q
  let n : ℕ := orderOf k
  let tK : ↥K := k ^ 4 ^ n
  have htK : (tK : G) ∈ K := tK.2
  have hodd : Odd (orderOf (tK : G)) := by
    rw [Subgroup.orderOf_coe]
    exact CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.odd_orderOf_pow_four_pow k
  have ha3 : a ^ 3 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have h4mod : 4 ^ n ≡ 1 [MOD 3] := by
    have h : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    simpa using Nat.ModEq.pow n h
  have ha4 : a ^ (4 ^ n) = a := by
    simpa using pow_eq_pow_of_modEq h4mod ha3
  have hek : e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) k) = a := by
    rw [hk, hq]
  have hmkt : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) tK =
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) k) ^ 4 ^ n := by
    rw [show tK = k ^ 4 ^ n from rfl]
    exact map_pow (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) k (4 ^ n)
  have htne : (tK : G) ≠ 1 := by
    intro h1
    have htK1 : tK = 1 := Subtype.ext h1
    have heq : e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) tK) = a := by
      rw [hmkt, map_pow, hek, ha4]
    rw [htK1] at heq
    have ha1 : a = 1 := by simpa using heq.symm
    rw [ha1, orderOf_one] at ha
    omega
  have htL : (tK : G) ∈ L := by
    rw [hLdef]
    exact Subgroup.subset_closure ⟨htK, hodd⟩
  have htker : (⟨(tK : G), hKX htK⟩ : ↥X) ∈ φ.ker :=
    hle (Subgroup.mem_subgroupOf.mpr htL)
  rw [hker] at htker
  have htP : (tK : G) ∈ pCoreOf 2 X := Subgroup.mem_subgroupOf.mp htker
  have hone : (tK : G) = 1 :=
    CFSG.Timmesfeld.Special.eq_one_of_mem_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) htP hodd
  exact htne hone

private theorem isSylowTwoOf_subgroupOf_top_of_isSylowOf {T X : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf X) (⊤ : Subgroup ↥X) := by
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hQ]
    exact Q.isPGroup'
  · rw [← hQ]
    have hidx : ((Q : Subgroup ↥X).subgroupOf (⊤ : Subgroup ↥X)).index =
        (Q : Subgroup ↥X).index := by
      have hmap : ((Q : Subgroup ↥X).subgroupOf (⊤ : Subgroup ↥X)).map
          (⊤ : Subgroup ↥X).subtype = (Q : Subgroup ↥X) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
      have hbij : Function.Bijective (⊤ : Subgroup ↥X).subtype :=
        ⟨Subgroup.subtype_injective ⊤, fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩⟩
      have h := Subgroup.index_map_of_bijective (f := (⊤ : Subgroup ↥X).subtype) hbij
        ((Q : Subgroup ↥X).subgroupOf (⊤ : Subgroup ↥X))
      rw [hmap] at h
      exact h.symm
    rw [hidx]
    exact Q.not_dvd_index

private theorem range_index_dvd_two {K X : Subgroup G} (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) (φ : ↥X →* Equiv.Perm (Fin 11))
    (hker : φ.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf X)
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 11)) :
    φ.range.index ∣ 2 := by
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hP : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three_of_quotient_a11 ⟨eK⟩
  have hO : pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    unfold CFSG.Open.pCoreOf
    rw [hP]
  have hO2K_le_X : pCoreOf 2 K ≤ X := (Subgroup.map_subtype_le _).trans hKX
  have hO2K_normal_X : ((pCoreOf 2 K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2K_le_X).mpr
      (hXK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hO2K_le_O2X : pCoreOf 2 K ≤ pCoreOf 2 X :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hO2K_le_X
      hO2K_normal_X (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hO2X_normal_K : ((pCoreOf 2 X ⊓ K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf (hKX.trans (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 X))
        Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hO2X_inf_le : pCoreOf 2 X ⊓ K ≤ pCoreOf 2 K :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 inf_le_right
      hO2X_normal_K ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
  have hO2XK : pCoreOf 2 X ⊓ K = pCoreOf 2 K :=
    le_antisymm hO2X_inf_le (le_inf hO2K_le_O2X (Subgroup.map_subtype_le _))
  have hkerK : (pCoreOf 2 X).subgroupOf K = CFSG.pCore 2 ↥K := by
    rw [← Subgroup.inf_subgroupOf_right (pCoreOf 2 X) K, hO2XK, hO, ← hP]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  let φK : ↥K →* Equiv.Perm (Fin 11) := φ.comp (Subgroup.inclusion hKX)
  have hφKker : φK.ker = CFSG.pCore 2 ↥K := by
    change φ.ker.comap (Subgroup.inclusion hKX) = _
    rw [hker, Subgroup.comap_inclusion_subgroupOf, hkerK]
  have hcardK : Nat.card φK.range = Nat.card (alternatingGroup (Fin 11)) := by
    have h1 : Nat.card φK.range = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φK).toEquiv, hφKker]
    rw [h1, Nat.card_congr eK.toEquiv]
  have hidxK : φK.range.index = 2 := by
    have hApos : 0 < Nat.card (alternatingGroup (Fin 11)) := Nat.card_pos
    have hmul : φK.range.index * Nat.card (alternatingGroup (Fin 11)) =
        2 * Nat.card (alternatingGroup (Fin 11)) := by
      rw [← hcardK, Subgroup.index_mul_card, ← two_mul_nat_card_alternatingGroup, ← hcardK]
    exact Nat.mul_right_cancel hApos hmul
  have hrange_le : φK.range ≤ φ.range := by
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨⟨(k : G), hKX k.2⟩, rfl⟩
  have h := Subgroup.index_dvd_of_le hrange_le
  rwa [hidxK] at h

theorem fiveFourteenA11Use_holds :
    FiveFourteenA11Use := by
  intro G _ _ X K T hcharX hT hKX hKn hKT hKq hnoX
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eK⟩ := hKq
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.le.trans hXK
  have hP : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three_of_quotient_a11 ⟨eK⟩
  have hO : pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    unfold CFSG.Open.pCoreOf
    rw [hP]
  let e : threeStar K ≃* alternatingGroup (Fin 11) :=
    (QuotientGroup.quotientMulEquivOfEq hP).symm.trans eK
  let φ : ↥X →* Equiv.Perm (Fin 11) :=
    (actPermSup e hTK).comp (Subgroup.inclusion (le_of_eq hKT.symm))
  have hcoreX : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) =
      (CFSG.Open.pCoreOf 2 X).subgroupOf X := by
    rw [← Subgroup.subgroupOf_self (H := X)]
    exact (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 X X le_rfl).symm
  have hkerφ : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) := by
    have hkerAct : φ.ker = ((CFSG.Open.pCoreOf 2 (K ⊔ T)).subgroupOf (K ⊔ T)).comap
        (Subgroup.inclusion (le_of_eq hKT.symm)) := by
      change ((actPermSup e hTK).ker.comap
        (Subgroup.inclusion (le_of_eq hKT.symm))) = _
      rw [actPermSup_ker_eq e hTK hT.isPGroup hO]
    rw [hkerAct, Subgroup.comap_inclusion_subgroupOf, hKT, ← hcoreX]
  obtain ⟨L, hLdef, hLX, hLnorm, hLodd⟩ := closure_odd_properties hKX hKn
  have hnoX' : ¬ CFSG.AGLEmbedding.InClassXBlock (L.subgroupOf X) := by
    intro hbad
    have hIn1 : CFSG.RankThree.PartOne.InClassX ↥(L.subgroupOf X) :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hbad
    have hIn2 : CFSG.RankThree.PartOne.InClassX ↥L :=
      (CFSG.CGT.PushingUpLit.inClassX_subgroupOf_iff hLX).mp hIn1
    exact hnoX L hLX ((CFSG.Open.IsSubnormal.iff_subgroupOf hLX).mpr hLnorm.isSubnormal)
      (CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hIn2)
  have hLker : ¬ L.subgroupOf X ≤ φ.ker :=
    not_le_ker_of_odd_gen hKX hLX hLdef φ (by rw [hkerφ, hcoreX]) e
  have hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥X) :=
    CFSG.AGLEmbeddingD2.McLaughlin.charTwo_top_of_le hcharX
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X) le_rfl
  have hQT : CFSG.Open.pCoreOf 2 X ≤ T :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.le_of_normal_isPGroup_of_isSylowOf hT
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X)
      (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 X)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hQT' : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) ≤ T.subgroupOf X := by
    rw [hcoreX]
    exact Subgroup.subgroupOf_mono X hQT
  have hT2' : IsPGroup 2 (T.subgroupOf X) := hT.isPGroup.comap_subtype
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf X) (⊤ : Subgroup ↥X) :=
    isSylowTwoOf_subgroupOf_top_of_isSylowOf hT
  have hidx_dvd : φ.range.index ∣ 2 :=
    range_index_dvd_two hKX hKn φ (by rw [hkerφ, hcoreX]) eK
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx_dvd with h1 | h2
  · have hrange : φ.range = ⊤ := Subgroup.index_eq_one.mp h1
    have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange
    obtain ⟨C', hCne, hCT, hCchar, hnorm⟩ :=
      exists_char_normal_of_s11_sylow (X := ↥X) hC hLnorm hLodd φ hφsurj hkerφ hLker
        hTsyl hnoX'
    exact exists_char_normal_map_subtype hT.le hCne hCT hCchar hnorm
  · have hrange : φ.range = alternatingGroup (Fin 11) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
    obtain ⟨C', hCne, hCT, hCchar, hnorm⟩ :=
      exists_char_normal_of_a11 (X := ↥X) hC hLnorm φ hkerφ hrange hLker hQT' hT2'
    exact exists_char_normal_map_subtype hT.le hCne hCT hCchar hnorm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
