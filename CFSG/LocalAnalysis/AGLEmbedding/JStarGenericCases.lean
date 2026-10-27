module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericFacts
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedII
public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace JStarHypOf

variable {Y : Type} [Group Y] [Finite Y] {T : Type} [Group T] [Finite T] {p B : ℕ}
  [Fact p.Prime] {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* T}

theorem false_of_constrained (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T)
    (hcon : ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧ Subgroup.centralizer (O : Set Y) ≤ O) :
    False := by
  obtain ⟨O, hOn, hOp, hOC⟩ := hcon
  have hp : p.Prime := Fact.out
  obtain ⟨ℓ, hℓ, hℓp, hℓT, hprim⟩ := hT.prime_dvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓJ : ℓ ∣ Nat.card Jt := hℓT.trans (Subgroup.card_dvd_of_surjective (f := φ) h.surj)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hℓJ
  let ρ : Jt →* MulAut O := (MulAut.conjNormal : Y →* MulAut O).comp Jt.subtype
  have hρg : ρ g ≠ 1 := by
    intro h1
    have hgC : (g : Y) ∈ Subgroup.centralizer (O : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have := congrArg (fun f : MulAut O => ((f ⟨o, ho⟩ : O) : Y)) h1
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc o * (g : Y) = (g : Y) * o * (g : Y)⁻¹ * g := by rw [this]
        _ = (g : Y) * o := by group
    obtain ⟨k, hk⟩ := hOp ⟨g, hOC hgC⟩
    have hord : orderOf (g : Y) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    rw [Subgroup.orderOf_coe, hg] at hord
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hord))
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hOp
  have hdb : p ^ d ∣ B := hd ▸ h.card_dvd O hOp
  obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hℓ ρ hg hρg hd
  have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd
  have hℓpe : ¬ ℓ ∣ p ^ e := fun h' =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h'))
  exact hprim (d - e) (by omega) ((pow_dvd_pow p (Nat.sub_le d e)).trans hdb)
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓpe) hdvd)

theorem le_pRank_inf (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {k : ℕ}
    (hk : k ≤ Open.pRank p (⊤ : Subgroup T)) : k ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ Jt) := by
  have hp : p.Prime := Fact.out
  have hS : CFSG.ABGLocalTools.IsSylowOf p (Rb : Subgroup Y)
      (Subgroup.normalizer (Jt : Set Y)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨h.le_normalizer, Rb.isPGroup', fun hdvd => Rb.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le h.le_normalizer))⟩
  obtain ⟨Q, hQ⟩ := hS.inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  obtain ⟨E, hEQ, hE, hEcard⟩ := h.exists_elem_le_sylow_of_le_pRank hk Q
  refine le_csSup (pRank_bddAbove p hp _) ⟨E.map Jt.subtype, ?_, elementary_abelian_map p hE _,
    by rw [Subgroup.card_map_of_injective Jt.subtype_injective, hEcard]⟩
  rw [← hQ]
  exact Subgroup.map_mono hEQ

theorem two_le_pRank_inf (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    2 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ Jt) :=
  h.le_pRank_inf hT.two_le_pRank

theorem eq_one_of_inf_centralizer_le_ker (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hker : Jt ⊓ Subgroup.centralizer (K : Set Y) ≤ φ.ker.map Jt.subtype) {z : Y}
    (hzR : z ∈ (Rb : Subgroup Y)) (hzC : z ∈ Subgroup.centralizer (K : Set Y)) : z = 1 := by
  have hNC : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  refine h.faithful z hzR fun j hj => hker ⟨?_, ?_⟩
  · exact Jt.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer hzR) j).mp hj)
      (Jt.inv_mem hj)
  · have hjz : j * z⁻¹ * j⁻¹ ∈ Subgroup.centralizer (K : Set Y) :=
      (Subgroup.mem_normalizer_iff.mp (hNC (h.le_normalizer_component hK hj)) z⁻¹).mp
        (Subgroup.inv_mem _ hzC)
    have heq : z * j * z⁻¹ * j⁻¹ = z * (j * z⁻¹ * j⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hzC hjz

theorem false_of_mem_centralizer (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) {K : Subgroup Y} (hK : IsComponentOf K ⊤) (hKY₀ : ¬ K ≤ Y₀)
    {z : Y} (hzR : z ∈ (Rb : Subgroup Y)) (hzp : orderOf z = p)
    (hzC : z ∈ Subgroup.centralizer (K : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  rcases h.le_centralizer_or_inf_le_ker hT hK with hJC | hker
  · have h1 := h.red.pRank_inf_centralizer_le_one_of_not_le hK hKY₀
    have h2 := (h.two_le_pRank_inf hT).trans (pRank_mono p hp (inf_le_inf_left _ hJC))
    omega
  · have hz1 := h.eq_one_of_inf_centralizer_le_ker hK hker hzR hzC
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp

theorem false_of_forall_le_centralizer (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)) :
    False := by
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.red.isCyclic_pCore_of_component hL
  have hF : CFSG.generalizedFitting Y ≤ Subgroup.centralizer (Jt : Set Y) := by
    refine sup_le ?_ (sSup_le fun K hK => ?_)
    · rw [CFSG.Fitting_eq_pcore Y p h.red.core_eq_bot]
      exact Subgroup.le_centralizer_iff.mp
        (le_centralizer_of_isCyclic_of_normal (h.commutator_eq hT))
    · exact Subgroup.le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK))
  have hJF : Jt ≤ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) :=
    Subgroup.le_centralizer_iff.mp hF
  have hJJ : Jt ≤ Subgroup.centralizer (Jt : Set Y) :=
    hJF.trans (Subgroup.centralizer_le (hJF.trans (CFSG.centralizer_generalizedFitting_le Y)))
  have hbot : Jt = ⊥ := by
    rw [← h.commutator_eq hT]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJJ
  exact (Subgroup.nontrivial_iff_ne_bot Jt).mp (h.nontrivial hT) hbot

theorem false_of_not_le_centralizer (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) (hβ : KFactBeta) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hJL : ¬ Jt ≤ Subgroup.centralizer (L : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  have hker := (h.le_centralizer_or_inf_le_ker hT hL).resolve_left hJL
  have hRC : (Rb : Subgroup Y) ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.mpr (h.eq_one_of_inf_centralizer_le_ker hL hker hz.1 hz.2)
  have hRN : (Rb : Subgroup Y) ≤ Subgroup.normalizer (L : Set Y) :=
    fun x hx => Subgroup.normalCore_le _ (h.red.sylow_le_normalCore_normalizer_component hL hx)
  have h1 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp hRN
  rw [hRC, pRank_bot_eq_zero hp] at h1
  have h2 := h.red.pRank_mulAut_le_two_of_isCyclic h.catalog hβ hL hcyc
  have h3 := h.red.three_le_pRank
  omega

theorem false_of_forall_isCyclic (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) (hβ : KFactBeta) (hE : ∃ L : Subgroup Y, IsComponentOf L ⊤)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : False := by
  obtain ⟨L, hL⟩ := hE
  by_cases hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)
  · exact h.false_of_forall_le_centralizer hT hL hall
  · push Not at hall
    obtain ⟨K, hK, hJK⟩ := hall
    exact h.false_of_not_le_centralizer hT hβ hK (hcyc K hK) hJK

end JStarHypOf

theorem jStarOfO1 : StmtJStarOfO1 := fun hT h hcon => h.false_of_constrained hT hcon

theorem jStarOfI : StmtJStarOfI := fun hT h _ hK _ hKY₀ _ hzR _ hzp hzC =>
  h.false_of_mem_centralizer hT hK hKY₀ hzR hzp hzC

theorem jStarOfII (hβ : KFactBeta) : StmtJStarOfII := fun hT h hE hcyc =>
  h.false_of_forall_isCyclic hT hβ hE hcyc

end CFSG.AGLEmbedding
