module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpA3
import CFSG.ClassicalInvolution.Q3.TL3T26

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem perpStar_partIHypG (h : EndHyp Ω) : Q3CL.PartIHypG Ω :=
  ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩

private theorem perpStar_isSylow2In_self {J : Subgroup G} (h2 : IsPGroup 2 ↥J) :
    IsSylow2In J J :=
  ⟨le_rfl, h2, fun _ hVJ _ hJV => le_antisymm hVJ hJV⟩

private theorem perpStar_mem_dComp_of_omegaNbr {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    J ∈ dComp Ω K :=
  Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩

private theorem perpStar_mem_dComp_of_kPerp {K M : Subgroup G} (hM : M ∈ KPerp Ω K) :
    M ∈ dComp Ω K := by
  rcases Set.mem_insert_iff.mp hM with rfl | hM'
  · exact Relation.ReflTransGen.refl
  · exact perpStar_mem_dComp_of_omegaNbr hM'

private theorem perpStar_mem_of_mem_dComp {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) : M ∈ Ω := by
  have hM' : Relation.ReflTransGen
      (fun A B : Subgroup G => B ∈ Ω ∧ CFSG.ClassicalInvolution.Disconnected.dAdj Ω A B) K M :=
    hM
  induction hM' with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

private theorem perpStar_inf_eq_bot_of_odd {X Q : Subgroup G} (hX : Odd (Nat.card X))
    (hQ : IsPGroup 2 Q) : X ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX)

private theorem perpStar_conj_pullback (h : EndHyp Ω) {W : Subgroup G} {g : G}
    {R : Subgroup G} (hR : R ∈ DSet Ω (conjSub g W)) : conjSub g⁻¹ R ∈ DSet Ω W := by
  obtain ⟨hRΩ, hRN⟩ := h.mem_dSet_iff.mp hR
  refine h.mem_dSet_iff.mpr ⟨h.thmD.hyp.conjInvariant g⁻¹ R hRΩ, fun y hy => ?_⟩
  rw [mem_conjSub_iff, inv_inv] at hy
  have e := mem_normalizer_iff_conjSub_eq.mp (hRN hy)
  rw [← conjSub_mul, show g * y * g⁻¹ * g = g * y by group] at e
  have e2 : conjSub y W = W := by
    have h1 : conjSub g⁻¹ (conjSub (g * y) W) = conjSub y W := by
      rw [← conjSub_mul, show g⁻¹ * (g * y) = y by group]
    rw [← h1, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  exact mem_normalizer_iff_conjSub_eq.mpr e2

private theorem perpStar_local (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {K J : Subgroup G} (hKD : K ∈ DSet Ω W) (hJD : J ∈ DSet Ω W) (hKJ : K ≠ J)
    (hJn : J ∉ omegaNbr Ω K) (hJS : J ∈ dComp Ω K) :
    ∀ R ∈ DSet Ω W, R ∈ dComp Ω K := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hKD).1
  have hJΩ : J ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf (perpStar_partIHypG h) hW
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hKD
  obtain ⟨t, ht, htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hJD
  let ρ : Thompson.Rep Ω W :=
    ⟨K, K, r, hKΩ, hKD, perpStar_isSylow2In_self (h.thmD.two K hKΩ), hr, hrW⟩
  let σ : Thompson.Rep Ω W :=
    ⟨J, J, t, hJΩ, hJD, perpStar_isSylow2In_self (h.thmD.two J hJΩ), ht, htW⟩
  have hrt : Thompson.piG W r * Thompson.piG W t ≠ Thompson.piG W t * Thompson.piG W r :=
    c.noncomm ρ σ hKJ hJn
  intro R hRD
  have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hRD).1
  obtain ⟨s, hs, hsW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hRD
  let τ : Thompson.Rep Ω W :=
    ⟨R, R, s, hRΩ, hRD, perpStar_isSylow2In_self (h.thmD.two R hRΩ), hs, hsW⟩
  by_cases hA : Thompson.piG W s * Thompson.piG W r = Thompson.piG W r * Thompson.piG W s
  ·
    by_cases hRK : R = K
    · rw [hRK]
      exact Relation.ReflTransGen.refl
    · exact perpStar_mem_dComp_of_omegaNbr
        (Q3T6.Mu.ctx_omega_of_comm c ρ τ (Ne.symm hRK) hA.symm)
  by_cases hB : Thompson.piG W s * Thompson.piG W t = Thompson.piG W t * Thompson.piG W s
  ·
    by_cases hRJ : R = J
    · rw [hRJ]
      exact hJS
    · exact Relation.ReflTransGen.trans hJS
        (perpStar_mem_dComp_of_omegaNbr (Q3T6.Mu.ctx_omega_of_comm c σ τ (Ne.symm hRJ) hB.symm))
  have h3 := Q3T6.Mu.piG_comm_third hΩ hW c.hkey hKΩ hJΩ hRΩ hKD hJD hRD
    (perpStar_isSylow2In_self (h.thmD.two K hKΩ))
    (perpStar_isSylow2In_self (h.thmD.two J hJΩ))
    (perpStar_isSylow2In_self (h.thmD.two R hRΩ)) hr ht hs hrW htW hsW hrt hA hB
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hKD).2 hr
  have hJ'D : conjSub r J ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hJD hrN
  have hJ'Ω : conjSub r J ∈ Ω := h.thmD.hyp.conjInvariant r J hJΩ
  have hxJ' : r * t * r⁻¹ ∈ conjSub r J := conj_mem_conjSub ht
  have hxW : r * t * r⁻¹ ∉ W := fun hx => htW ((Subgroup.mem_normalizer_iff.mp hrN t).mpr hx)
  have hrS : r ∈ sigmaNorm Ω K :=
    T8.normalizer_le_sigmaNorm_of_mem h.thmD.hyp.conjInvariant hKΩ
      Relation.ReflTransGen.refl (Subgroup.le_normalizer hr)
  have hJ'S : conjSub r J ∈ dComp Ω K := (hrS J).mp hJS
  by_cases hRJ' : conjSub r J = R
  · rw [← hRJ']
    exact hJ'S
  · let ρ' : Thompson.Rep Ω W :=
      ⟨conjSub r J, conjSub r J, r * t * r⁻¹, hJ'Ω, hJ'D,
        perpStar_isSylow2In_self (h.thmD.two _ hJ'Ω), hxJ', hxW⟩
    exact Relation.ReflTransGen.trans hJ'S
      (perpStar_mem_dComp_of_omegaNbr (Q3T6.Mu.ctx_omega_of_comm c ρ' τ hRJ' h3.symm))

private theorem perpStar_transport (h : EndHyp Ω) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hL : ∀ R ∈ DSet Ω W₀, R ∈ dComp Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ g : G, ∀ R ∈ DSet Ω W, R ∈ dComp Ω (conjSub g K) := by
  obtain ⟨g, hg⟩ := wSet_conj h hW₀ hW
  refine ⟨g, fun R hR => ?_⟩
  have hR' : R ∈ DSet Ω (conjSub g W₀) := by
    rw [hg]
    exact hR
  have h1 := hL (conjSub g⁻¹ R) (perpStar_conj_pullback h hR')
  have h2 := Thompson.mem_dComp_conjSub h.thmD.hyp.conjInvariant h1 g
  rwa [conjSub_conjSub_inv] at h2

theorem not_mem_dComp_of_omegaStar (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) : J ∉ dComp Ω K := by
  intro hJS
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  obtain ⟨W₀, hW₀, hKD, hJD, -⟩ := exists_wSet_of_omegaStar h hK hJ hJn
  have hL := perpStar_local h hW₀ hKD hJD hKJ hJn hJS
  have hstep : ∀ A ∈ dComp Ω K, ∀ B, dstarAdj Ω A B → B ∈ dComp Ω K := by
    intro A hA B hAB
    have hAΩ : A ∈ Ω := perpStar_mem_of_mem_dComp hK hA
    have hdA : dComp Ω A = dComp Ω K := T8.dComp_eq_of_mem hK hA
    obtain ⟨hBΩ, hB⟩ := hAB
    have hBA : B ∈ dComp Ω A := by
      by_cases hn : B ∈ omegaNbr Ω A ∨ A ∈ omegaNbr Ω B
      · exact Relation.ReflTransGen.single ⟨hBΩ, hn⟩
      · push Not at hn
        obtain ⟨W, hW, hAD, hBD⟩ : ∃ W ∈ WSet Ω, A ∈ DSet Ω W ∧ B ∈ DSet Ω W := by
          rcases hB with hB | hB
          · obtain ⟨W, hW, h1, h2, -⟩ := exists_wSet_of_omegaStar h hAΩ hB hn.1
            exact ⟨W, hW, h1, h2⟩
          · obtain ⟨W, hW, h1, h2, -⟩ := exists_wSet_of_omegaStar h hBΩ hB hn.2
            exact ⟨W, hW, h2, h1⟩
        obtain ⟨g, hg⟩ := perpStar_transport h hW₀ hK hL hW
        have hA' : A ∈ dComp Ω (conjSub g K) := hg A hAD
        have hB' : B ∈ dComp Ω (conjSub g K) := hg B hBD
        rw [T8.dComp_eq_of_mem (h.thmD.hyp.conjInvariant g K hK) hA']
        exact hB'
    rw [hdA] at hBA
    exact hBA
  have hall : ∀ L, Relation.ReflTransGen (dstarAdj Ω) K L → L ∈ dComp Ω K := by
    intro L hL'
    induction hL' with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact hstep _ ih _ hbc
  apply h.disc
  intro K₁ hK₁ J₁ hJ₁
  have h1 : K₁ ∈ dComp Ω K := hall K₁ (h.star K hK K₁ hK₁)
  have h2 : J₁ ∈ dComp Ω K := hall J₁ (h.star K hK J₁ hJ₁)
  exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK h1) h2

private theorem perpStar_conj_mem_kPerp (h : EndHyp Ω) {M : Subgroup G} (hM : M ∈ Ω)
    {q : G} (hq : q ∈ pCore 2 G) : conjSub q M ∈ KPerp Ω M := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hPn : (pCore 2 G).Normal := inferInstance
  have hP2 : IsPGroup 2 ↥(pCore 2 G) := CFSG.pCore_isPGroup
  have hMN : M ≤ Subgroup.normalizer ((pCore 2 G : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact le_top
  have hM2 : IsPGroup 2 ↥M := h.thmD.two M hM
  obtain ⟨S, hS⟩ := (hM2.to_sup_of_normal_right' hP2 hMN).exists_le_sylow
  have hMS : M ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hPS : pCore 2 G ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hconjS : conjSub q M ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hx' : x = q * (q⁻¹ * x * q) * q⁻¹ := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPS hq) (hMS hx))
      (Subgroup.inv_mem _ (hPS hq))
  by_cases hne : M = conjSub q M
  · rw [← hne]
    exact Set.mem_insert _ _
  · have hqM : conjSub q M ∈ Ω := hΩ.conjInvariant q M hM
    have hcomm := Q3CP.l67Gen G Ω hΩ S M (TC.mem_RSet_of_isPGroup hM hM2) (conjSub q M)
      (TC.mem_RSet_of_isPGroup hqM (h.thmD.two _ hqM)) hMS hconjS hne
    have hnorm : conjSub q M ≤ Subgroup.normalizer (M : Set G) := by
      intro y hy
      refine Subgroup.centralizer_le_normalizer (M : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcomm x hx y hy
    have hnbr : conjSub q M ∈ omegaNbr Ω M :=
      (TC.mem_omegaNbr_iff hΩ (fun J hJ => h.thmD.two J hJ)).mpr
        ⟨hqM, Ne.symm hne, hnorm⟩
    exact Set.mem_insert_of_mem _ hnbr

private theorem perpStar_pCore_le_sigmaNorm (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {q : G} (hq : q ∈ pCore 2 G) : q ∈ sigmaNorm Ω K :=
  T8.mem_sigmaNorm_of_mem_dComp h.thmD.hyp.conjInvariant hK Relation.ReflTransGen.refl
    (perpStar_mem_dComp_of_kPerp (perpStar_conj_mem_kPerp h hK hq))

private theorem perpStar_centralizer_le_sigmaNorm (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : c ∈ sigmaNorm Ω K := by
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hk : conjSub c K ∈ KPerp Ω K :=
    TC.Thin.conjSub_mem_kPerp h.thmD.hyp hK hz hcz (Set.mem_insert K _)
  exact T8.mem_sigmaNorm_of_mem_dComp h.thmD.hyp.conjInvariant hK Relation.ReflTransGen.refl
    (perpStar_mem_dComp_of_kPerp hk)

theorem oddCore_pSpan_dComp (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    classicalInvolutionOddCore ↥(pSpan (dComp Ω K)) = ⊥ := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hzQ : z ∈ pCore 2 G := h.mem_pCore hK hz
  have hPn : (pCore 2 G).Normal := inferInstance
  have hNH : sigmaNorm Ω K ≤ Subgroup.normalizer ((pSpan (dComp Ω K) : Subgroup G) : Set G) :=
    Thompson.le_normalizer_biSup_of_acts (fun r hr U hU => (hr U).mp hU)
  have hQN : ∀ q ∈ pCore 2 G,
      q ∈ Subgroup.normalizer ((pSpan (dComp Ω K) : Subgroup G) : Set G) :=
    fun q hq => hNH (perpStar_pCore_le_sigmaNorm h hK hq)
  have hCN : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      c ∈ Subgroup.normalizer ((pSpan (dComp Ω K) : Subgroup G) : Set G) :=
    fun c hc => hNH (perpStar_centralizer_le_sigmaNorm h hK hz hc)
  have hXodd : Odd (Nat.card (oddCoreImg (pSpan (dComp Ω K)))) := odd_natCard_oddCoreImg _
  have hXQ : ∀ o ∈ oddCoreImg (pSpan (dComp Ω K)), ∀ q ∈ pCore 2 G, o * q = q * o := by
    intro o ho q hq
    have hq' : q⁻¹ ∈ Subgroup.normalizer ((pSpan (dComp Ω K) : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ (hQN q hq)
    have hc1 : o⁻¹ * (q⁻¹ * o * q) ∈ oddCoreImg (pSpan (dComp Ω K)) := by
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ho) ?_
      have := conj_mem_oddCoreImg hq' ho
      rwa [inv_inv] at this
    have hc2 : o⁻¹ * (q⁻¹ * o * q) ∈ pCore 2 G := by
      have hconj := hPn.conj_mem q⁻¹ (Subgroup.inv_mem _ hq) o⁻¹
      rw [inv_inv] at hconj
      have e : o⁻¹ * (q⁻¹ * o * q) = (o⁻¹ * q⁻¹ * o) * q := by group
      rw [e]
      exact Subgroup.mul_mem _ hconj hq
    have hinf := perpStar_inf_eq_bot_of_odd hXodd (CFSG.pCore_isPGroup (p := 2) (G := G))
    have hmem : o⁻¹ * (q⁻¹ * o * q) ∈ oddCoreImg (pSpan (dComp Ω K)) ⊓ pCore 2 G :=
      ⟨hc1, hc2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have key : q⁻¹ * o * q = o := by
      have h1 : q⁻¹ * o * q = o * (o⁻¹ * (q⁻¹ * o * q)) := by group
      rw [h1, hmem, mul_one]
    calc o * q = q * (q⁻¹ * o * q) := by group
      _ = q * o := by rw [key]
  have hXC : oddCoreImg (pSpan (dComp Ω K)) ≤ Subgroup.centralizer ({z} : Set G) := fun o ho =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hXQ o ho z hzQ)
  have hXle := TC.le_oddCoreImg_of_normalizes hXC
    (fun e he n hn => conj_mem_oddCoreImg (hCN e he) hn) hXodd
  rw [TC.oddCoreImg_centralizer_eq_bot h.thmD.odd hPn CFSG.pCore_isPGroup hzQ] at hXle
  rw [eq_bot_iff]
  intro x hx
  have hxX : (x : G) ∈ oddCoreImg (pSpan (dComp Ω K)) := ⟨x, hx, rfl⟩
  have hxbot : (x : G) ∈ (⊥ : Subgroup G) := hXle hxX
  rw [Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

end CFSG.ClassicalInvolution.Q3.Sec13
