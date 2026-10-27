module

public import CFSG.GH74.GLS.C3.Layer1.Th2L163
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Layer
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19A

public section

namespace CFSG.GH74.GLS.Th2.PU3Q

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_of_ne_bot {R : Subgroup G} (hR2 : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) :
    1 ≤ pRank 2 ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hR2.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.1 h1) hR1
  · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2
    have hyG : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    have hz : zpowers (y : G) ≤ R := Subgroup.zpowers_le.2 y.2
    exact (C3.Layer1.U1a.one_le_pRank_zpowers hyG).trans (C3.Layer1.Back.pRank_mono' hz)

omit [Finite G] in
theorem conj_mem_normalizer_cj {R : Subgroup G} {n : G} (hn : n ∈ normalizer (R : Set G)) (g : G) :
    g * n * g⁻¹ ∈ normalizer ((cj g R : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_cj_iff, mem_cj_iff]
  have e : g⁻¹ * (g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * h * g) * n⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.1 hn (g⁻¹ * h * g)

theorem normalizer_le_of_le_cmbar {K M Q R : Subgroup G} (hQ : IsSylowOf 2 Q (CMbar M K))
    (hgam : gammaK 2 Q 1 ≤ M) (hRC : R ≤ CMbar M K) (hR2 : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) :
    normalizer (R : Set G) ≤ M := by
  obtain ⟨g, hg, hgR⟩ := Th2.exists_cj_le_of_isSylowOf hQ hRC hR2
  have hgM : g ∈ M := hg.1
  have h2 : IsPGroup 2 ↥(cj g R) := hR2.of_equiv ((MulAut.conj g).subgroupMap R)
  have h1 : cj g R ≠ ⊥ := by
    intro h
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj g).injective).1 h)
  have hrank : 1 ≤ pRank 2 ↥(cj g R) := one_le_pRank_of_ne_bot h2 h1
  have hN : normalizer ((cj g R : Subgroup G) : Set G) ≤ gammaK 2 Q 1 := by
    unfold gammaK
    exact le_iSup₂_of_le (cj g R) hgR (le_iSup_of_le hrank le_rfl)
  intro n hn
  have hM1 : g * n * g⁻¹ ∈ M := hgam (hN (conj_mem_normalizer_cj hn g))
  have e : n = g⁻¹ * (g * n * g⁻¹) * g := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hM1) hgM

theorem normalizer_le_of_le_L {K L M Q R : Subgroup G} (hLM : IsPCompIn 2 M L)
    (hsub : IsSubnormalIn L M) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hQ : IsSylowOf 2 Q (CMbar M K)) (hgam : gammaK 2 Q 1 ≤ M)
    {m : G} (hm : m ∈ M) (hne : cj m L ≠ L)
    (hRL : R ≤ L) (hR2 : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) : normalizer (R : Set G) ≤ M := by
  have hL' : IsPCompIn 2 M (cj m L) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hLM m
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hm] at this
  have hle : cj m L ≤ Stage1.Thm2.Recip.cSec L :=
    Stage1.Thm2.Recip.le_cSec_of_ne hL' hLM hne
  have hRL' : cj m R ≤ cj m L := Subgroup.map_mono hRL
  have hRM : cj m R ≤ M := by
    intro c hc
    have h1 : m⁻¹ * c * m ∈ R := (mem_cj_iff m R c).1 hc
    have h2 : m⁻¹ * c * m ∈ M := hLM.1 (hRL h1)
    have e : c = m * (m⁻¹ * c * m) * m⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hm h2) (M.inv_mem hm)
  have hRC : cj m R ≤ CMbar M K := fun c hc =>
    Th2.P812A7.cmk_le_cmbar hLM.1 hsub hLeq ⟨hRM hc, hle (hRL' hc)⟩
  have h2 : IsPGroup 2 ↥(cj m R) := hR2.of_equiv ((MulAut.conj m).subgroupMap R)
  have h1 : cj m R ≠ ⊥ := by
    intro h
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj m).injective).1 h)
  have hN := normalizer_le_of_le_cmbar hQ hgam hRC h2 h1
  intro n hn
  have hmn : m * n * m⁻¹ ∈ M := hN (conj_mem_normalizer_cj hn m)
  have e : n = m⁻¹ * (m * n * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) hmn) hm

omit [Finite G] in
theorem isSubnormal_subgroupOf_trans' {E Y X : Subgroup G} (hEY : E ≤ Y) (hYX : Y ≤ X)
    (hE : (E.subgroupOf Y).IsSubnormal) (hY : (Y.subgroupOf X).IsSubnormal) :
    (E.subgroupOf X).IsSubnormal := by
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (E.subgroupOf Y).comap ι = (E.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((E.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hE.comap ι
  exact Subgroup.IsSubnormal.trans (fun x hx => hEY hx) h1 hY

theorem eq_and_quasisimple_of_central {K L M : Subgroup G} (hKM : K ≤ M) (hL : IsMinSubnormalIn K M L)
    (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hcen : ∀ u ∈ pPrimeCoreOf 2 L, ∀ l ∈ L, u * l = l * u) :
    K = L ∧ CFSG.IsQuasisimple ↥L := by
  have hKL : K ≤ L := hL.1
  have hLN : L ≤ normalizer (K : Set G) := by
    refine hLeq.le.trans (sup_le ?_ Subgroup.le_normalizer)
    intro u hu
    refine Subgroup.centralizer_le_normalizer (K : Set G) ?_
    rw [mem_centralizer_iff]
    intro k hk
    exact (hcen u hu k (hKL hk)).symm
  have hKnorm : (K.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLN
  have hKsub : IsSubnormalIn K M :=
    ⟨hKM, isSubnormal_subgroupOf_trans' hKL hL.2.1.1 (Subgroup.Normal.isSubnormal hKnorm) hL.2.1.2⟩
  have hKL' : K = L := hL.2.2 K le_rfl hKL hKsub
  refine ⟨hKL', ?_⟩
  obtain ⟨-, hL2⟩ := TwoThin.isPCompIn_two_iff.1 hLcomp
  have hperfSub : ⁅L, L⁆ = L := TwoThin.commutator_self_of_isTwoComponent hLcomp.1 hL2
  have hperf : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff (H := L)).mpr hperfSub
  refine Stage2.Final.Thm4.isQuasisimple_of_perfect_central_cover
    (QuotientGroup.mk' (pPrimeCore 2 ↥L)) (QuotientGroup.mk'_surjective _) hperf ?_
    (TwoThin.isQuasisimple_hat hLcomp)
  intro z hz
  rw [QuotientGroup.ker_mk'] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hzO : (z : G) ∈ pPrimeCoreOf 2 L := ⟨z, hz, rfl⟩
  exact Subtype.ext (hcen z.1 hzO g.1 g.2).symm

theorem isCompIn_centralizer_of_preuniq {L M : Subgroup G}
    (hsub : IsSubnormalIn L M)
    (hpre : ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M)
    (hNL : normalizer (L : Set G) ≤ M) (hLq : CFSG.IsQuasisimple ↥L)
    {t : G} (ht : orderOf t = 2) (htL : t ∈ centralizer (L : Set G)) :
    IsCompIn (centralizer ({t} : Set G)) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN : t ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) htL
  have htM : t ∈ M := hNL htN
  have htcs : t ∈ CMK M L := by
    refine ⟨htM, htN, TwoThin.mem_normalizer_pPrimeCoreOf htN, fun k hk => ?_⟩
    have hkt : k * t = t * k := mem_centralizer_iff.1 htL k hk
    rw [commutatorElement_eq_one_iff_mul_comm.2 hkt]
    exact one_mem _
  have hCt : centralizer ({t} : Set G) ≤ M := hpre t htcs ht
  have hLC : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL l hl)
  refine ⟨hLC, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hLC).symm hLq, ?_⟩
  have h := hsub.2.comap (Subgroup.inclusion hCt)
  rwa [Subgroup.comap_inclusion_subgroupOf] at h

theorem terminal_of_preuniq {K L M : Subgroup G} {x : G}
    (hsub : IsSubnormalIn L M)
    (hpre : ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M)
    (hNL : normalizer (L : Set G) ≤ M)
    (hKL : K = L) (hqK : CFSG.IsQuasisimple ↥K)
    (hIL2 : IsIL2Pair x K) :
    IsTerminalPair 2 x K := by
  subst hKL
  have hcompK : IsCompIn (centralizer ({x} : Set G)) K := by
    refine ⟨hIL2.2.1, CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hIL2.2.1).symm hqK, ?_⟩
    obtain ⟨K', -, hsubK, -⟩ := hIL2.2.2
    exact hsubK
  have hdvd : 2 ∣ Nat.card ↥K := C3.Layer1.Bk.B810.two_dvd_card_of_quasisimple hqK
  have hterm : ∀ t : G, orderOf t = 2 → t ∈ centralizer (K : Set G) →
      IsCompIn (centralizer ({t} : Set G)) K := fun t ht htK =>
    isCompIn_centralizer_of_preuniq hsub hpre hNL hqK ht htK
  exact ⟨hIL2.1, hcompK, hdvd, hterm⟩

theorem terminal_of_central_core_of_preuniq {K L M : Subgroup G} {x : G}
    [IsSimpleGroup G] (hM : IsCoatom M)
    (hL : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hcen : ∀ u ∈ pPrimeCoreOf 2 L, ∀ l ∈ L, u * l = l * u)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hIL2 : IsIL2Pair x K) :
    IsTerminalPair 2 x K := by
  have hKM : K ≤ M := hL.1.trans hL.2.1.1
  obtain ⟨hKL, hLq⟩ := eq_and_quasisimple_of_central hKM hL hLcomp hLeq hcen
  have hqK : CFSG.IsQuasisimple ↥K := hKL.symm ▸ hLq
  have hNL : normalizer (L : Set G) ≤ M :=
    CFSG.GH74.GLS.Th2.L163.normalizer_le hM hLcomp hpre
  exact terminal_of_preuniq hL.2.1 hpre hNL hKL hqK hIL2

theorem terminal_of_central_core {K L M Q : Subgroup G} {x : G}
    [IsSimpleGroup G] (hM : IsCoatom M)
    (hL : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hcen : ∀ u ∈ pPrimeCoreOf 2 L, ∀ l ∈ L, u * l = l * u)
    (hQ : IsSylowOf 2 Q (CMbar M K)) (hgam : gammaK 2 Q 1 ≤ M)
    (hIL2 : IsIL2Pair x K) :
    IsTerminalPair 2 x K := by
  have hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M :=
    CFSG.GH74.GLS.Th2.P812A7.centralizer_le_M_of_sylow_cmbar
      hLcomp hL.2.1 hLeq hQ hgam
  exact terminal_of_central_core_of_preuniq hM hL hLcomp hLeq hcen hpre hIL2

end CFSG.GH74.GLS.Th2.PU3Q

