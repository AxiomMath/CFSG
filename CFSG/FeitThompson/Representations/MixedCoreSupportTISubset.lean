module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03
  (mixedSupport cyclicTIsetConjIn hallCoreIn conjSet)
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd hallCoreOf)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

variable {G : Type*} [Group G]

theorem mem_mixedSupport_iff {S W₁ W₂ : Subgroup G} {z : G} :
    z ∈ mixedSupport S W₁ W₂ ↔
      (z ∈ hallCoreIn S ∧ z ≠ 1) ∨
        ∃ s ∈ S, ∃ v ∈ cyclicTIset W₁ W₂, s⁻¹ * v * s = z := by
  simp only [mixedSupport, cyclicTIsetConjIn, conjSet, Set.mem_union, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe, Set.mem_iUnion, Set.mem_image, exists_prop]

theorem mem_cyclicTIsetConjIn_iff {S W₁ W₂ : Subgroup G} {z : G} :
    z ∈ cyclicTIsetConjIn W₁ W₂ S ↔ ∃ s ∈ S, ∃ v ∈ cyclicTIset W₁ W₂, s⁻¹ * v * s = z := by
  simp only [cyclicTIsetConjIn, conjSet, Set.mem_iUnion, Set.mem_image, exists_prop,
    SetLike.mem_coe]

theorem eq_one_of_conj_eq_one {s v : G} (h : s⁻¹ * v * s = 1) : v = 1 := by
  have h2 : s * (s⁻¹ * v * s) * s⁻¹ = s * 1 * s⁻¹ := by rw [h]
  group at h2
  exact h2

theorem orderOf_conj_inv (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x :=
  (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * x = g⁻¹ * x * g * g⁻¹ by group)).symm

theorem orderOf_eq_of_card_prime {W : Subgroup G} (hW : (Nat.card W).Prime) {x : G} (hx : x ∈ W)
    (hx1 : x ≠ 1) : orderOf x = Nat.card W := by
  rcases hW.eq_one_or_self_of_dvd _ (W.orderOf_dvd_natCard hx) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hx1
  · exact h

theorem orderOf_of_mem_cyclicTIset {W₁ W₂ : Subgroup G}
    (hdp : IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂)
    (hq : (Nat.card W₁).Prime) (hp : (Nat.card W₂).Prime) (hpq : Nat.card W₁ ≠ Nat.card W₂)
    {v : G} (hv : v ∈ cyclicTIset W₁ W₂) : orderOf v = Nat.card W₁ * Nat.card W₂ := by
  have hvmul : v ∈ (W₁ : Set G) * (W₂ : Set G) :=
    hdp.coe_eq_mul ▸ (SetLike.mem_coe.2 (mem_cyclicTIset.1 hv).1)
  obtain ⟨x, hx, y, hy, rfl⟩ := hvmul
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact (mem_cyclicTIset.1 hv).2.2 (by simpa using hy)
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact (mem_cyclicTIset.1 hv).2.1 (by simpa using hx)
  have hox : orderOf x = Nat.card W₁ := orderOf_eq_of_card_prime hq hx hx1
  have hoy : orderOf y = Nat.card W₂ := orderOf_eq_of_card_prime hp hy hy1
  rw [(hdp.commute hx hy).orderOf_mul_eq_mul_orderOf_of_coprime (by
    rw [hox, hoy]; exact (Nat.coprime_primes hq hp).2 hpq), hox, hoy]

section Mixed

variable {S W₁ W₂ : Subgroup G}
  (hTIP : IsTIWithNormalizer ((hallCoreIn S : Set G) \ {1}) S)
  (hTIV : IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂))
  (hW : (W₁ ⊔ W₂ : Subgroup G) ≤ S)
  (hdp : IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂)
  (hq : (Nat.card W₁).Prime) (hp : (Nat.card W₂).Prime) (hpq : Nat.card W₁ ≠ Nat.card W₂)
  (hcard : Nat.card (hallCoreIn S) = Nat.card W₂ ^ Nat.card W₁)

theorem one_notMem_mixedSupport : (1 : G) ∉ mixedSupport S W₁ W₂ := by
  rw [mem_mixedSupport_iff]
  rintro (⟨-, h⟩ | ⟨s, -, v, hv, hsv⟩)
  · exact h rfl
  · exact one_notMem_cyclicTIset (eq_one_of_conj_eq_one hsv ▸ hv)

include hW in
theorem mixedSupport_subset : mixedSupport S W₁ W₂ ⊆ (S : Set G) \ {1} := by
  intro z hz
  refine ⟨?_, fun h => one_notMem_mixedSupport ((Set.mem_singleton_iff.1 h) ▸ hz)⟩
  rcases mem_mixedSupport_iff.1 hz with ⟨hzP, -⟩ | ⟨s, hs, v, hv, rfl⟩
  · exact Subgroup.map_subtype_le _ hzP
  · exact S.mul_mem (S.mul_mem (S.inv_mem hs) (hW (cyclicTIset_subset_coe hv))) hs

include hq hp hpq hcard in
theorem not_dvd_orderOf_of_mem_hallCoreIn {z : G} (hz : z ∈ hallCoreIn S) :
    ¬ Nat.card W₁ ∣ orderOf z := by
  intro hdvd
  have h1 : Nat.card W₁ ∣ Nat.card W₂ ^ Nat.card W₁ :=
    hcard ▸ hdvd.trans ((hallCoreIn S).orderOf_dvd_natCard hz)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1))

include hdp hq hp hpq in
theorem dvd_orderOf_of_mem_cyclicTIsetConjIn {z : G} (hz : z ∈ cyclicTIsetConjIn W₁ W₂ S) :
    Nat.card W₁ ∣ orderOf z := by
  obtain ⟨s, -, v, hv, rfl⟩ := mem_cyclicTIsetConjIn_iff.1 hz
  rw [orderOf_conj_inv, orderOf_of_mem_cyclicTIset hdp hq hp hpq hv]
  exact Dvd.intro _ rfl

include hTIP hTIV hW hdp hq hp hpq hcard in
theorem conj_mem_mixedSupport_iff {z : G} (hz : z ∈ mixedSupport S W₁ W₂) (g : G) :
    g⁻¹ * z * g ∈ mixedSupport S W₁ W₂ ↔ g ∈ S := by
  refine ⟨fun hgz => ?_, fun hg => ?_⟩
  · rcases mem_mixedSupport_iff.1 hz with hzP | hzV
    · rcases mem_mixedSupport_iff.1 hgz with hgzP | hgzV
      ·
        by_contra hg
        refine Set.disjoint_left.1 (hTIP.disjoint_image_conj_inv hg) ⟨hgzP.1, ?_⟩ ?_
        · simpa using hgzP.2
        · exact ⟨z, ⟨hzP.1, by simpa using hzP.2⟩, rfl⟩
      ·
        refine absurd (dvd_orderOf_of_mem_cyclicTIsetConjIn hdp hq hp hpq
          (mem_cyclicTIsetConjIn_iff.2 hgzV)) ?_
        rw [orderOf_conj_inv]
        exact not_dvd_orderOf_of_mem_hallCoreIn hq hp hpq hcard hzP.1
    · rcases mem_mixedSupport_iff.1 hgz with hgzP | hgzV
      ·
        refine absurd ?_ (not_dvd_orderOf_of_mem_hallCoreIn hq hp hpq hcard hgzP.1)
        rw [orderOf_conj_inv]
        exact dvd_orderOf_of_mem_cyclicTIsetConjIn hdp hq hp hpq
          (mem_cyclicTIsetConjIn_iff.2 hzV)
      ·
        obtain ⟨s, hs, v, hv, hsv⟩ := hzV
        obtain ⟨t, ht, w, hw, htw⟩ := hgzV
        set k : G := s * g * t⁻¹ with hk
        have hkv : k⁻¹ * v * k = w := by
          have h1 : g⁻¹ * (s⁻¹ * v * s) * g = t⁻¹ * w * t := by rw [hsv, htw]
          have h2 : t * (g⁻¹ * (s⁻¹ * v * s) * g) * t⁻¹ = t * (t⁻¹ * w * t) * t⁻¹ := by rw [h1]
          rw [hk]
          group at h2 ⊢
          exact h2
        have hkW : k ∈ (W₁ ⊔ W₂ : Subgroup G) := by
          by_contra hkn
          exact Set.disjoint_left.1 (hTIV.disjoint_image_conj_inv hkn) hw ⟨v, hv, hkv⟩
        have hgk : g = s⁻¹ * k * t := by rw [hk]; group
        rw [hgk]
        exact S.mul_mem (S.mul_mem (S.inv_mem hs) (hW hkW)) ht
  · rcases mem_mixedSupport_iff.1 hz with ⟨hzP, hz1⟩ | ⟨s, hs, v, hv, rfl⟩
    · refine mem_mixedSupport_iff.2 (Or.inl ⟨?_, ?_⟩)
      · have h := le_normalizer_map_subtype_hallCore S hg
        rw [Subgroup.mem_set_normalizer_iff''] at h
        exact (h z).1 hzP
      · exact fun hc => hz1 (eq_one_of_conj_eq_one hc)
    · exact mem_mixedSupport_iff.2 (Or.inr ⟨s * g, S.mul_mem hs hg, v, hv, by group⟩)

include hTIP hTIV hW hdp hq hp hpq hcard in
theorem isTIWithNormalizer_mixedSupport (hPne : hallCoreIn S ≠ ⊥) :
    IsTIWithNormalizer (mixedSupport S W₁ W₂) S :=
  let ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
  isTIWithNormalizer_of_transporter
    ⟨(x : G), mem_mixedSupport_iff.2 (Or.inl ⟨x.2, fun h => hx1 (Subtype.ext h)⟩)⟩
    one_notMem_mixedSupport
    fun _ hz g => conj_mem_mixedSupport_iff hTIP hTIV hW hdp hq hp hpq hcard hz g

end Mixed

theorem FCH_type_p_core_mixed_ti
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FCH_type_p_core_mixed_ti.{u} := by
  intro G _ _ hG S U W₁ W₂ hS
  have hG' : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  obtain ⟨-, hp, hq, -, -, hpq, -, -, -, -, -, -, -, hcard, -, -, hPne, -, -, -, -, -, hTIP, -⟩ :=
    h₁ G hG' S U W₁ W₂ hS.isCoatom hS.config (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have hHC : ∀ M : Subgroup G, hallCoreIn M = hallCoreOf M := fun _ => rfl
  rw [← hHC] at hTIP hcard hPne
  have hW : (W₁ ⊔ W₂ : Subgroup G) ≤ S := sup_le hS.config.le_M_W₁ hS.config.le_M_W₂
  have hTI : IsTIWithNormalizer (mixedSupport S W₁ W₂) S :=
    isTIWithNormalizer_mixedSupport hTIP hS.config.isTIWithNormalizer_cyclicTIset hW
      hS.config.isInternalDirectProduct_sup hq hp (Ne.symm hpq) hcard hPne
  refine ⟨hTI.nonempty, fun s hs => ?_, mixedSupport_subset hW, hTI, fun a ha => ?_,
    fun f t hfc htc hf ht => ?_, fun f hf hfv => ?_, fun A0 J hDA _ _ hD f hfc hf => ?_⟩
  ·
    exact mem_normalizer_iff_conjInv_image_eq.1 (by rw [hTI.normalizer_eq]; exact hs)
  ·
    exact (hTI.inf_centralizer_eq ha).symm
  ·
    exact hTI.cfInner_indClassFun (mem_dadeDomain.2 ⟨hfc, hf⟩) (mem_dadeDomain.2 ⟨htc, ht⟩)
  ·
    exact hTI.indClassFun_mem_virtualChars (mem_dadeZDomain.2 ⟨hf, hfv⟩)
  ·
    exact (dadeMap_apply_coe hD _).symm.trans
      (dadeMap_eq_indClassFun hD hTI hDA f (mem_dadeDomain.2 ⟨hfc, hf⟩))

end

end CFSG.FeitThompson.Proofs
