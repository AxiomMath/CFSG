module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

@[expose] def I1422Lie2Fact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (β : MulAut H), β ^ 3 = 1 →
    CFSG.Open.IsQuasisimple H → IsChevSimple 2 (H ⧸ Subgroup.center H) →
    Odd (Nat.card (Subgroup.center H)) →
    ∀ J : Subgroup H, GLAPComponent 3 (fixSubgroup β) J →
      CFSG.Open.IsQuasisimple ↥J ∧ Odd (Nat.card (Subgroup.center ↥J))

theorem i1422_quasisimple_alt8_iso {Γ : Type} [Group Γ] [Finite Γ] (hq : CFSG.Open.IsQuasisimple Γ)
    (hodd : Odd (Nat.card (Subgroup.center Γ))) (φ : Γ →* alternatingGroup (Fin 8))
    (hφ : Function.Surjective φ) : Nonempty (Γ ≃* alternatingGroup (Fin 8)) := by
  have hZc : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hZ : Subgroup.center Γ ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hc : φ z ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hφ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
    rw [hZc, Subgroup.mem_bot] at hc
    exact hc
  let ψ : Γ ⧸ Subgroup.center Γ →* alternatingGroup (Fin 8) := QuotientGroup.lift _ φ hZ
  have hψs : Function.Surjective ψ := by
    intro a
    obtain ⟨x, rfl⟩ := hφ a
    exact ⟨(x : Γ ⧸ Subgroup.center Γ), rfl⟩
  have hker : ψ.ker = ⊥ := by
    rcases hq.2.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 8))
      obtain ⟨x, hx⟩ := hψs a
      have hxk : x ∈ ψ.ker := by
        rw [h]
        exact Subgroup.mem_top x
      rw [MonoidHom.mem_ker, hx] at hxk
      exact ha hxk
  have hψi : Function.Bijective ψ := ⟨(MonoidHom.ker_eq_bot_iff ψ).1 hker, hψs⟩
  let e : Γ ⧸ Subgroup.center Γ ≃* alternatingGroup (Fin 8) := MulEquiv.ofBijective ψ hψi
  have hZb : Subgroup.center Γ = ⊥ :=
    CFSG.ComponentClassification.RankTwoAlt.center_eq_bot_of_odd hq.1 (le_refl 8) e hodd
  exact ⟨(QuotientGroup.quotientBot (G := Γ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZb.symm).trans e)⟩

theorem i1422Char2_of_facts (hS1 : I1422Lie2Fact) (G : Type) [Group G] [Finite G] :
    I1422Char2At G := by
  intro X K J y _hX hK hyN hyp _hCM hJ hA hKr
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hyp' : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hJt := glaPComponent_map_pQuotHom Nat.prime_three hyN hyp' hJ
  have hb3 : barAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext hyp
    rw [h1, map_one]
  obtain ⟨hΓq, hΓodd⟩ := hS1 (PQuot 3 K) (barAut 3 K ⟨y, hyN⟩) hb3
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK) hKr (up7a8_odd_center hK) _ hJt
  obtain ⟨e⟩ := hA
  set Γ : Subgroup (PQuot 3 K) := (J.subgroupOf K).map (pQuotHom 3 K) with hΓdef
  have hmem : ∀ x : ↥J, pQuotHom 3 K (Subgroup.inclusion hJK x) ∈ Γ := fun x =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hJK x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let ρ : ↥J →* ↥Γ :=
    { toFun := fun x => ⟨pQuotHom 3 K (Subgroup.inclusion hJK x), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hρs : Function.Surjective ρ := by
    rintro ⟨γ, hγ⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hγ
    exact ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, Subtype.ext rfl⟩
  let f : ↥J →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (pQuotHom 3 J)
  have hOcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf
      Nat.prime_three K
    have hc : Nat.card (GLAPPrimeCoreOf 3 K) = Nat.card (GLAPPrimeCore 3 ↥K) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rwa [hc] at h
  have hle : (GLAPPrimeCore 3 ↥K).comap (Subgroup.inclusion hJK) ≤ GLAPPrimeCore 3 ↥J := by
    have hdvd : Nat.card ((GLAPPrimeCore 3 ↥K).comap (Subgroup.inclusion hJK)) ∣
        Nat.card (GLAPPrimeCore 3 ↥K) := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJK)]
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hcop := Nat.Coprime.coprime_dvd_right hdvd hOcop
    exact le_sSup (show (GLAPPrimeCore 3 ↥K).comap (Subgroup.inclusion hJK) ∈
      {L : Subgroup ↥J | L.Normal ∧ Nat.Coprime 3 (Nat.card L)} from ⟨inferInstance, hcop⟩)
  have hker : ρ.ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : pQuotHom 3 K (Subgroup.inclusion hJK x) = 1 := congrArg Subtype.val hx
    have h2 : Subgroup.inclusion hJK x ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : x ∈ GLAPPrimeCore 3 ↥J := hle (Subgroup.mem_comap.2 h2)
    have h4 : pQuotHom 3 J x = 1 := (QuotientGroup.eq_one_iff _).2 h3
    show e (pQuotHom 3 J x) = 1
    rw [h4, map_one]
  let φ0 : (↥J ⧸ ρ.ker) →* alternatingGroup (Fin 8) := QuotientGroup.lift ρ.ker f hker
  let φ : ↥Γ →* alternatingGroup (Fin 8) :=
    φ0.comp (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.toMonoidHom
  have hφs : Function.Surjective φ := by
    intro a
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J)) q
    refine ⟨ρ x, ?_⟩
    have hinv : (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm (ρ x) =
        (x : ↥J ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show φ0 ((QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm (ρ x)) = e (pQuotHom 3 J x)
    rw [hinv]
    rfl
  exact i1422_quasisimple_alt8_iso hΓq hΓodd φ hφs

end CFSG.LocalAnalysis.GLTheoremA
