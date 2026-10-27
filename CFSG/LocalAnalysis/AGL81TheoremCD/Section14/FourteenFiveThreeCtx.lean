module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoPerm
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11GammaTwoSet
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenEmbedded

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD

variable {G : Type} [Group G] [Finite G]

structure Ctx (G : Type) [Group G] [Finite G] (M H E Q : Subgroup G) where
  choice : S14Choice G M H E Q (kSub 3 M H)
  caseTwo : CaseTwo M H
  kNormal : KNormalAt M
  nineNineOne : NineNineOneAt M
  pLayerNotLe : PLayerNotLeAt M
  f : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11)
  map_inf : (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map f.toMonoidHom =
    a11TwoSetStab 9 10
  mbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
    Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
    Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11))

theorem exists_ctx {M H E Q J : Subgroup G} (hpre : PreambleTypes M) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (h : S14Choice G M H E Q J) (hA : ¬ TypeA M H)
    (hB : TypeB M H)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11))) :
    J = kSub 3 M H ∧ Nonempty (Ctx G M H E Q) := by
  obtain ⟨h2, hJK⟩ := h.caseTwo hpre hA hB
  have h' : S14Choice G M H E Q (kSub 3 M H) := hJK ▸ h
  obtain ⟨e, i, j, hij, heq⟩ := h'.exists_twoSet h2 hK hU hL kFactA11GammaTwoSet_holds
  obtain ⟨c, hc⟩ := exists_mulAut_map_a11TwoSetStab hij
  refine ⟨hJK, ⟨h', h2, hK, hU, hL, e.trans c, ?_, hMbar⟩⟩
  show (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map (e.trans c).toMonoidHom =
    a11TwoSetStab 9 10
  rw [show (e.trans c).toMonoidHom = c.toMonoidHom.comp e.toMonoidHom from rfl,
    ← Subgroup.map_map, heq, hc]

private lemma not_isSolvable_alternatingGroup_eleven :
    ¬ Group.IsSolvable (alternatingGroup (Fin 11)) := by
  intro hsol
  haveI := hsol
  haveI : Group.IsSolvable ℤˣ := Group.isSolvable_of_comm fun a b => mul_comm a b
  exact Equiv.Perm.not_isSolvable (Fin 11) (by rw [Cardinal.mk_fin]; norm_num)
    (Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 11)).subtype Equiv.Perm.sign
      (by rw [Subgroup.range_subtype]; exact le_rfl))

namespace Ctx

variable {M H E Q : Subgroup G} (c : Ctx G M H E Q)

@[expose] noncomputable def φ : ↥(kSub 3 M H) →* alternatingGroup (Fin 11) :=
  c.f.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))

theorem ker_φ : c.φ.ker = CFSG.pPrimeCore 3 ↥(kSub 3 M H) := by
  rw [show c.φ = c.f.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) from rfl,
    MonoidHom.ker_comp_of_injective _ _ c.f.injective, QuotientGroup.ker_mk']

theorem map_φ_inf : ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map c.φ = a11TwoSetStab 9 10 := by
  rw [show c.φ = c.f.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) from rfl, ← Subgroup.map_map]
  exact c.map_inf

theorem pPrimeCore_map_le (c : Ctx G M H E Q) :
    (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ≤ M :=
  c.choice.hypCGen.pPrimeCore_map_le c.kNormal

theorem not_three_dvd_card_pPrimeCore (c : Ctx G M H E Q) :
    ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(kSub 3 M H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

theorem mem_M_iff (x : ↥(kSub 3 M H)) : (x : G) ∈ M ↔ c.φ x ∈ a11TwoSetStab 9 10 := by
  constructor
  · intro hx
    rw [← c.map_φ_inf]
    exact Subgroup.mem_map_of_mem c.φ (Subgroup.mem_subgroupOf.mpr ⟨x.2, hx⟩)
  · intro hx
    rw [← c.map_φ_inf] at hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hyM : (y : G) ∈ M := (Subgroup.mem_subgroupOf.mp hy).2
    have hker : x * y⁻¹ ∈ c.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [c.ker_φ] at hker
    have hzM : ((x * y⁻¹ : ↥(kSub 3 M H)) : G) ∈ M :=
      c.pPrimeCore_map_le (Subgroup.mem_map_of_mem (kSub 3 M H).subtype hker)
    have hxy' : (x : G) = ((x * y⁻¹ : ↥(kSub 3 M H)) : G) * (y : G) := by
      rw [show ((x * y⁻¹ : ↥(kSub 3 M H)) : G) = (x : G) * (y : G)⁻¹ from rfl]
      group
    rw [hxy']
    exact M.mul_mem hzM hyM

theorem Q_le (c : Ctx G M H E Q) : Q ≤ kSub 3 M H ⊓ M :=
  le_inf (c.choice.isSylowOf_kSub c.caseTwo).le (c.choice.Q_le_M c.nineNineOne)

theorem E_le (c : Ctx G M H E Q) : E ≤ kSub 3 M H ⊓ M :=
  le_inf (c.choice.E_le_kSub c.caseTwo) c.choice.hypCGen.E_le_M

theorem orderOf_φ {x : ↥(kSub 3 M H)} (hx : orderOf (x : G) = 3) : orderOf (c.φ x) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxK : orderOf x = 3 := by rw [← Subgroup.orderOf_coe]; exact hx
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxK] at h
  have hφ3 : c.φ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  refine orderOf_eq_prime hφ3 fun h1 => ?_
  have hker : x ∈ c.φ.ker := by simpa using h1
  rw [c.ker_φ] at hker
  have hdvd : orderOf x ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :=
    Subgroup.orderOf_dvd_natCard (s := CFSG.pPrimeCore 3 ↥(kSub 3 M H)) hker
  rw [hxK] at hdvd
  exact c.not_three_dvd_card_pPrimeCore hdvd

theorem map_φ_centralizer {U : Subgroup G} (hUK : U ≤ kSub 3 M H) (hU : IsPGroup 3 U) :
    ((Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H)).map c.φ =
      Subgroup.centralizer
        (((U.subgroupOf (kSub 3 M H)).map c.φ : Subgroup (alternatingGroup (Fin 11))) :
          Set (alternatingGroup (Fin 11))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU' : IsPGroup 3 (U.subgroupOf (kSub 3 M H)) := hU.comap_subtype
  have hcen : Subgroup.centralizer ((U.subgroupOf (kSub 3 M H) : Set ↥(kSub 3 M H))) =
      (Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      have h1 := h ⟨g, hUK hg⟩ (Subgroup.mem_subgroupOf.mpr hg)
      simpa using congrArg Subtype.val h1
    · intro h y hy
      exact Subtype.ext (by simpa using h (y : G) (Subgroup.mem_subgroupOf.mp hy))
  rw [← hcen, show c.φ = c.f.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) from rfl, ← Subgroup.map_map,
    ← CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3)
      c.not_three_dvd_card_pPrimeCore hU',
    ← CFSG.GroupTheory.CoprimeTransport.centralizer_map_mulEquiv, Subgroup.map_map]

theorem map_φ_inf_centralizer {U : Subgroup G} (hUK : U ≤ kSub 3 M H) (hU : IsPGroup 3 U) :
    ((M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H)).map c.φ =
      a11TwoSetStab 9 10 ⊓ Subgroup.centralizer
        (((U.subgroupOf (kSub 3 M H)).map c.φ : Subgroup (alternatingGroup (Fin 11))) :
          Set (alternatingGroup (Fin 11))) := by
  have hMmap : (M.subgroupOf (kSub 3 M H)).map c.φ = a11TwoSetStab 9 10 := by
    rw [← Subgroup.inf_subgroupOf_right (H := M) (K := kSub 3 M H), inf_comm]
    exact c.map_φ_inf
  have hinf : (M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H) =
      M.subgroupOf (kSub 3 M H) ⊓
        (Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H) := by
    ext z
    simp [Subgroup.mem_subgroupOf]
  refine le_antisymm ?_ ?_
  · calc ((M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H)).map c.φ
        = ((M.subgroupOf (kSub 3 M H)) ⊓
            (Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H)).map c.φ := by
            rw [hinf]
      _ ≤ (M.subgroupOf (kSub 3 M H)).map c.φ ⊓
            ((Subgroup.centralizer (U : Set G)).subgroupOf (kSub 3 M H)).map c.φ :=
            Subgroup.map_inf_le _ _ _
      _ = a11TwoSetStab 9 10 ⊓ Subgroup.centralizer
            (((U.subgroupOf (kSub 3 M H)).map c.φ : Subgroup (alternatingGroup (Fin 11))) :
              Set (alternatingGroup (Fin 11))) := by
            rw [hMmap, c.map_φ_centralizer hUK hU]
  · intro y hy
    obtain ⟨hyStab, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [← hMmap] at hyStab
    rw [← c.map_φ_centralizer hUK hU] at hyC
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hyStab
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyC
    have hzm : z * m⁻¹ ∈ c.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, hmy, mul_inv_cancel]
    rw [c.ker_φ] at hzm
    have hzmSub : z * m⁻¹ ∈ M.subgroupOf (kSub 3 M H) :=
      Subgroup.mem_subgroupOf.mpr
        (c.pPrimeCore_map_le (Subgroup.mem_map_of_mem (kSub 3 M H).subtype hzm))
    have hzM : z ∈ M.subgroupOf (kSub 3 M H) := by
      have h1 : z = (z * m⁻¹) * m := by group
      rw [h1]
      exact (M.subgroupOf (kSub 3 M H)).mul_mem hzmSub hm
    have hzMC : (z : G) ∈ M ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨Subgroup.mem_subgroupOf.mp hzM, Subgroup.mem_subgroupOf.mp hz⟩
    exact Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr hzMC, hzy⟩

theorem map_φ_centralizer_singleton {x : G} (hxK : x ∈ kSub 3 M H) (hx : orderOf x = 3) :
    ((Subgroup.centralizer ({x} : Set G)).subgroupOf (kSub 3 M H)).map c.φ =
      Subgroup.centralizer ({c.φ ⟨x, hxK⟩} : Set (alternatingGroup (Fin 11))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : IsPGroup 3 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hx]; norm_num⟩
  have hUK : Subgroup.zpowers x ≤ kSub 3 M H := Subgroup.zpowers_le.mpr hxK
  have hgen : (Subgroup.zpowers x).subgroupOf (kSub 3 M H) =
      Subgroup.zpowers ⟨x, hxK⟩ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩, fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
  have hcen : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcen, c.map_φ_centralizer hUK hU, hgen, MonoidHom.map_zpowers,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem map_φ_inf_centralizer_singleton {x : G} (hxK : x ∈ kSub 3 M H) (hx : orderOf x = 3) :
    ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (kSub 3 M H)).map c.φ =
      a11TwoSetStab 9 10 ⊓
        Subgroup.centralizer ({c.φ ⟨x, hxK⟩} : Set (alternatingGroup (Fin 11))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : IsPGroup 3 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hx]; norm_num⟩
  have hUK : Subgroup.zpowers x ≤ kSub 3 M H := Subgroup.zpowers_le.mpr hxK
  have hgen : (Subgroup.zpowers x).subgroupOf (kSub 3 M H) =
      Subgroup.zpowers ⟨x, hxK⟩ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩, fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
  have hcen : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcen, c.map_φ_inf_centralizer hUK hU, hgen, MonoidHom.map_zpowers,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem not_isSolvable_M (c : Ctx G M H E Q) : ¬ IsSolvable ↥M := by
  rintro hsol
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsSolvable ↥M := hsol
  rcases c.mbar with h | h | h
  · obtain ⟨e⟩ := h
    exact Equiv.Perm.not_isSolvable (Fin 9) (by rw [Cardinal.mk_fin]; norm_num)
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨e⟩ := h
    exact not_isSolvable_alternatingGroup_eleven
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨e⟩ := h
    exact Equiv.Perm.not_isSolvable (Fin 11) (by rw [Cardinal.mk_fin]; norm_num)
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem five_le (c : Ctx G M H E Q) {p : ℕ} (hp : p ∈ sigmaSet G M) : 5 ≤ p := by
  have hprime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hodd : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have h3 : p ≠ 3 := by
    rintro rfl
    exact c.choice.hypCGen.not_mem_sigmaSet hp
  have h4 : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) hprime
  have h2 : 2 ≤ p := hprime.two_le
  omega

theorem isStronglyPEmbedded (c : Ctx G M H E Q) {r : ℕ} (hr : r ∈ sigmaSet G M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded r M := by
  refine c.choice.cstar.isStronglyPEmbedded_of_not_isSolvable c.choice.maxLocal hr ?_
    c.not_isSolvable_M
  rintro rfl
  exact c.choice.hypCGen.not_mem_sigmaSet hr

end Ctx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree
