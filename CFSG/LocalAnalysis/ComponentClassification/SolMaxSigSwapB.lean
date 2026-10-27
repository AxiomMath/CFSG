module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapA
public import CFSG.LocalAnalysis.ComponentClassification.Sol78HMaxComp

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem exists_coreQuot_equiv_of_cover [Finite X] {N K : Subgroup X} {n : ℕ} (hKN : K ≤ N)
    (ρ : ↥K →* alternatingGroup (Fin n)) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = pPrimeCore 2 ↥K)
    (hψ : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (inclusion hKN))) :
    ∃ eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n),
      ∀ x : ↥K, eN ((inclusion hKN x : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = ρ x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (inclusion hKN) with hψdef
  have hker : ψ.ker = ρ.ker := by
    rw [hρker]
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      let g : ψ.ker →* pPrimeCore 2 ↥N := ((inclusion hKN).comp ψ.ker.subtype).codRestrict _
        fun k => by
          have h1 : ψ k = 1 := k.2
          change QuotientGroup.mk' (pPrimeCore 2 ↥N) (inclusion hKN (k : ↥K)) = 1 at h1
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hg : Function.Injective g := fun k₁ k₂ h => by
        have h' := congrArg (fun x : pPrimeCore 2 ↥N => ((x : ↥N) : X)) h
        exact Subtype.ext (Subtype.ext h')
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
        pPrimeCore_coprime_card
    · have hnorm : ((pPrimeCore 2 ↥K).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
      have hodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥K).map ψ)) :=
        Nat.Coprime.coprime_dvd_right ((pPrimeCore 2 ↥K).card_map_dvd ψ) pPrimeCore_coprime_card
      have hle : (pPrimeCore 2 ↥K).map ψ ≤ pPrimeCore 2 (↥N ⧸ pPrimeCore 2 ↥N) :=
        le_sSup ⟨hnorm, hodd⟩
      rwa [pPrimeCore_quotient_pPrimeCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)), fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm
      ((inclusion hKN x : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = (x : ↥K ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, h1]
  rfl

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_kernel (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {z : X} (hz : orderOf z = 2)
    (hzt : z ∈ centralizer ({t} : Set X)) (hzK : z ∈ UnbalancedLayer.coreActionKernel J) :
    centralizer ({z} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.pair.1.1, pow_one])
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ S.pair.1.2.1).mp S.pair.1.2.2.1).2.2
  obtain ⟨hJzJ, hJzz, hJzC, ⟨eJz⟩⟩ := S.fixedLayer_facts hz2 hzt hzK
  set Jz := GSLit.fixedLayer J (zpowers z) with hJzdef
  obtain ⟨hsup, hcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq (zpowers_le.mpr hzK) hz2
  set ρ := (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp (inclusion hJzJ)
    with hρdef
  obtain ⟨hρ, hρk⟩ := restrict_surjective_of_sup e hJzJ hsup
  have hρker : ρ.ker = pPrimeCore 2 ↥Jz := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' _ (inclusion hJzJ x)) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← mem_map_iff_mem Jz.subtype_injective, hcore, mem_inf]
    constructor
    · intro h
      exact ⟨x.2, ⟨inclusion hJzJ x, h, rfl⟩⟩
    · rintro ⟨-, ⟨y, hy, hyx⟩⟩
      have : y = inclusion hJzJ x := Subtype.ext hyx
      rwa [← this]
  obtain ⟨E', hE'Jz, hE', D', hD', hs'⟩ := exists_four_subgroup_of_surjective (by omega) ρ hρ hρk
  have hE'J : E' ≤ J := hE'Jz.trans hJzJ
  have hs : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω :=
    fun x hx ω hω => hs' ⟨x, hE'Jz hx⟩ hx ω hω
  have hW := S.completion_eq_of_four h33 h35 hE'J hE' hD' hs
  have hNE' : normalizer (E' : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
    rw [← hW]
    exact normalizer_le_normalizer_signalizerCompletion_self E'
  have htz : z * t = t * z := mem_centralizer_singleton_iff.mp hzt
  have hT2 : IsPGroup 2 (zpowers t ⊔ zpowers z : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' ht2 hz2
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute htz))
  have hT : (zpowers t ⊔ zpowers z : Subgroup X) ≠ ⊥ := by
    intro h
    have ht : t ∈ zpowers t ⊔ zpowers z := mem_sup_left (mem_zpowers t)
    rw [h, mem_bot] at ht
    have := S.pair.1.1
    rw [ht, orderOf_one] at this
    omega
  set Y := centralizer ({z} : Set X) with hYdef
  have hNY := Sol78H.le_normalizer_core_sup_of_thm13_centralizer hT13 hML hSch S.nonab S.kProper
    S.unbal S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hT hT2 hJzC ⟨eJz⟩ hz
    hJzz
  have hOY := S.core_le_of_kernel h33 h35 hz hzt hzK
  set OY := GH74.GLS.pPrimeCoreOf 2 Y with hOYdef
  set N := OY ⊔ Jz with hNdef
  have hJzN : Jz ≤ N := le_sup_right
  have hNH : N ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    sup_le hOY (hJzJ.trans (S.le_normalizer_completion h33 h35))
  have hψ : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (inclusion hJzN)) := by
    have hOYN : OY.subgroupOf N ≤ pPrimeCore 2 ↥N := by
      refine le_sSup ⟨?_, ?_⟩
      · refine (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le ?_ ?_)
        · exact le_normalizer
        · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer (hJzz hy))
      · rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : OY ≤ N)).toEquiv, hOYdef,
          GH74.GLS.pPrimeCoreOf, card_map_of_injective Y.subtype_injective]
        exact pPrimeCore_coprime_card
    have h1 : Jz.subgroupOf N ⊔ pPrimeCore 2 ↥N = ⊤ := by
      have h2 : N.subgroupOf N = ⊤ := subgroupOf_self N
      rw [hNdef, subgroupOf_sup le_sup_left le_sup_right] at h2
      rw [eq_top_iff, ← h2, sup_comm]
      exact sup_le_sup_left hOYN _
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥N))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨eN, heN⟩ := exists_coreQuot_equiv_of_cover hJzN ρ hρ hρker hψ
  have hE'N : E' ≤ N := hE'Jz.trans hJzN
  have hsN : ∀ x : ↥N, (x : X) ∈ E' → ∀ ω ∉ D',
      ((eN (x : ↥N ⧸ pPrimeCore 2 ↥N) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
        ω := by
    intro x hx ω hω
    have hx' : x = inclusion hJzN ⟨x, hE'Jz hx⟩ := Subtype.ext rfl
    rw [hx', heN]
    exact hs' ⟨x, hE'Jz hx⟩ hx ω hω
  obtain ⟨hE'4, hE'2⟩ := card_sq_of_klein hE'
  have hE'sq : ∀ x ∈ E', x * x = 1 := fun x hx => by rw [← sq]; exact hE'2 x hx
  intro g hg
  have hgN := hNY hg
  obtain ⟨hE'gN, D'', hD'', hs''⟩ := exists_support_conj (by omega) eN hE'N hD' hsN hgN
  have hE'g4 : Nat.card (E'.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE'4]
  have hE'gsq : ∀ x ∈ E'.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE'sq x hx, map_one]
  obtain ⟨x, hxN, hxE⟩ := exists_conj_four_subgroup (by omega) eN hE'N hE'gN hE'4 hE'g4 hE'sq
    hE'gsq hD' hD'' hsN hs''
  have hxg : x⁻¹ * g ∈ normalizer (E' : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change E'.map (MulAut.conj (x⁻¹ * g)).toMonoidHom = E'
    rw [map_conj_mul, ← hxE, ← map_conj_mul, inv_mul_cancel]
    ext y
    simp
  have : g = x * (x⁻¹ * g) := by group
  rw [this]
  exact mul_mem (hNH hxN) (hNE' hxg)

end Sig36

end CFSG.ComponentClassification.SolMax
