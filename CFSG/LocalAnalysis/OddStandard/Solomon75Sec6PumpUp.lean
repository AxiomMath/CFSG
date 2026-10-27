module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Parts
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Elementary

variable {X : Type} [Group X]

private theorem pumpUp_card_eq {A B : Type} [Group A] [Group B] {n : ℕ}
    (hA : IsDoubleCoverOfAlt A n) (hB : IsDoubleCoverOfAlt B n) : Nat.card A = Nat.card B := by
  obtain ⟨-, hA2, ⟨eA⟩⟩ := hA
  obtain ⟨-, hB2, ⟨eB⟩⟩ := hB
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center B), hA2, hB2,
    Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]

private theorem pumpUp_conj_mem {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M) {x : X}
    (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem pumpUp_mem_normalizer {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨pumpUp_conj_mem h, fun hx => ?_⟩
  have := pumpUp_conj_mem h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private theorem pumpUp_isSubnormal_inf {K D D' H : Subgroup X} (hHD : H ≤ D) (hHD' : H ≤ D')
    (hK : (K.subgroupOf D).IsSubnormal) : ((K ⊓ D').subgroupOf H).IsSubnormal := by
  have h1 : (K ⊓ D').subgroupOf H = (K.subgroupOf D).comap (Subgroup.inclusion hHD) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hHD' x.2⟩⟩
  rw [h1]
  exact hK.comap _

end Elementary

section PumpUp

variable {X : Type} [Group X] [Finite X]

private theorem pumpUp_isPCompIn_oTwoPrimeOf {H A : Subgroup X} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).IsSubnormal) (hq : IsTwoGenQuasi ↥(oTwoPrimeOf A)) :
    IsPCompIn 2 H (oTwoPrimeOf A) := by
  have hEH : oTwoPrimeOf A ≤ H := (oTwoPrimeOf_le A).trans hAH
  refine ⟨hEH, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hEH).2 hq⟩⟩
  exact isSubnormal_subgroupOf_of_normal_of_subnormal hAH (oTwoPrimeOf_le A) hA
    (normal_subgroupOf_oTwoPrimeOf A)

private theorem pumpUp_commutatorElement_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    ⁅m, j⁆ ∈ pPrimeCoreOf 2 M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : M.subgroupOf H ≠ J.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM.1, inf_of_le_left hJ.1] at h
    exact h
  obtain ⟨-, -, hcore, -⟩ :=
    (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hM.2 hJ.2).2 hne'
  have hc : ⁅(⟨m, hM.1 hm⟩ : ↥H), (⟨j, hJ.1 hj⟩ : ↥H)⁆ ∈
      (pPrimeCore 2 ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype :=
    (hcore.trans inf_le_left) (Subgroup.commutator_mem_commutator hm hj)
  obtain ⟨y, hy, hyeq⟩ := hc
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hM.1
  have hey : e y ∈ pPrimeCore 2 ↥M := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨y, hy, rfl⟩
  refine ⟨e y, hey, ?_⟩
  change ((y : ↥H) : X) = ⁅m, j⁆
  exact congrArg Subtype.val hyeq

private theorem pumpUp_mem_of_le_sSup {H M E : Subgroup X} {S : Set (Subgroup X)}
    (hM : IsPCompIn 2 H M) (hS : ∀ J ∈ S, IsPCompIn 2 H J) (hEM : E ≤ M) (hES : E ≤ sSup S)
    (hEq : IsTwoGenQuasi ↥E) : M ∈ S := by
  by_contra hMS
  have hOM : pPrimeCoreOf 2 M ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hM.1 (isPComponent_two_iff.1 hM.2).1
  have hOMM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hle : sSup S ≤ centralizerSection M (oddCoreOf H) := by
    refine sSup_le fun J hJ => ?_
    intro j hj
    have hne : M ≠ J := fun h => hMS (by rw [h]; exact hJ)
    have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ pPrimeCoreOf 2 M := fun g hg m hm =>
      pumpUp_commutatorElement_mem hM (hS J hJ) hne hm hg
    exact ⟨pumpUp_mem_normalizer (fun m hm => hOMM (hc j hj m hm))
        (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm)),
      le_normalizer_oddCoreOf H ((hS J hJ).1 hj), fun m hm => hOM (hc j hj m hm)⟩
  refine not_commutator_le_of_odd hEq (odd_card_oddCoreOf H) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨-, -, hab⟩ := hle (hES hb)
  exact hab a (hEM ha)

private theorem exists_isIntrinsicIn_twist {s t u : X} {K : Subgroup X}
    (hK : IsIntrinsicIn X (cen s) K u)
    (hcovE : (oTwoPrimeOf (K ⊓ cen t)).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤)
    (hEpc : IsPCompIn 2 (cen t ⊓ cen s) (oTwoPrimeOf (K ⊓ cen t))) :
    ∃ v, IsIntrinsicIn X (cen t ⊓ cen s) (oTwoPrimeOf (K ⊓ cen t)) v := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup X := oTwoPrimeOf (K ⊓ cen t) with hEdef
  have hKs : K ≤ cen s := hK.2.2.1.1
  have hKq : IsTwoGenQuasi ↥K :=
    (isTwoGenQuasi_subgroupOf_iff hKs).1 (isPComponent_two_iff.1 hK.2.2.1.2).2
  have hEK : E ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hK.1] at this
  have hu2' : (⟨u, hK.2.1⟩ : ↥K) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hu2)
  have hmem : (⟨u, hK.2.1⟩ : ↥K) ∈ E.subgroupOf K ⊔ pPrimeCore 2 ↥K := by
    rw [hcovE]
    exact Subgroup.mem_top _
  obtain ⟨o, -, a, ha, -, hua⟩ := exists_conj_twoElt_of_mem_sup_odd
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hmem hu2'
  have hua' : u = (o : X) * (a : X) * (o : X)⁻¹ := by
    simpa using congrArg Subtype.val hua
  obtain ⟨φ, hφ⟩ : ∃ φ : X ≃* X, φ = MulAut.conj (o : X)⁻¹ := ⟨_, rfl⟩
  have hφS : (cen s).map φ.toMonoidHom = cen s := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ((cen s).inv_mem (hKs o.2)))
  have hφK : K.map φ.toMonoidHom = K := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (K.inv_mem o.2))
  have hφu : φ u = (a : X) := by
    rw [hφ, MulAut.conj_apply, hua']
    group
  have hK' := hK.map_mulEquiv φ
  rw [hφS, hφK, hφu] at hK'
  have haE : (a : X) ∈ E := ha
  obtain ⟨hv, hvK, -, hKeq, Lv, hLv, hLveq⟩ := hK'
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hKeq hLveq
  have hGK : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hGv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ cen (a : X) := (oTwoPrimeOf_le _).trans inf_le_right
  have hcovG : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
    rw [covers_subgroupOf_iff hGK, sup_comm]
    exact hKeq.symm
  have hGq : IsTwoGenQuasi ↥(oTwoPrimeOf (K ⊓ cen (a : X))) :=
    isTwoGenQuasi_of_covers hGK hcovG (primeResidual_oTwoPrimeOf _) hKq
  have hGLv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ Lv := le_sup_right.trans hLveq.ge
  have hcovGL : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ := by
    rw [covers_subgroupOf_iff hGLv, sup_comm]
    exact hLveq.symm
  have hvs : (a : X) * s = s * (a : X) := Subgroup.mem_centralizer_singleton_iff.1 (hKs hvK)
  have hvK' : (a : X) ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    mem_centralizerSection_of_covers hvs hK.2.2.1 hGK hGv hGq hcovG
  have hEO : E ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 E :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun e he => mem_normalizer_inf (Subgroup.le_normalizer he)
        (mem_normalizer_pPrimeCoreOf_of_mem (hEK he)))
      ((odd_card_oddCoreOf K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  have hvE : (a : X) ∈ centralizerSection E (pPrimeCoreOf 2 E) := by
    refine ⟨Subgroup.le_normalizer haE, mem_normalizer_pPrimeCoreOf_of_mem haE,
      fun e he => hEO ⟨?_, hvK'.2.2 e (hEK he)⟩⟩
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem he haE) (E.inv_mem he)) (E.inv_mem haE)
  have hv2 : (a : X) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (a : X)
    rwa [hv] at this
  have hFE : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ E := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovF : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf E ⊔ pPrimeCore 2 ↥E = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hv2 (primeResidual_oTwoPrimeOf _) hvE
  have hFLv : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ Lv :=
    (oTwoPrimeOf_mono (inf_le_inf_right _ hEK)).trans hGLv
  have hc1 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hFE hcovF).some.toEquiv
  have hc2 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hEK hcovE).some.toEquiv
  have hc3 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGK hcovG).some.toEquiv
  have hc4 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGLv hcovGL).some.toEquiv
  have hcovFL : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ :=
    covers_of_card_le hFLv (by omega)
  refine ⟨(a : X), hv, haE, hEpc, ?_, Lv, hLv, ?_⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFE).1 hcovF).symm.trans (sup_comm _ _)
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFLv).1 hcovFL).symm.trans (sup_comm _ _)

private theorem pumpUp_lPrec {s t : X} {E K M : Subgroup X} {n : ℕ}
    (hs : orderOf s = 2) (ht : orderOf t = 2) (hst : s * t = t * s) (hne : s ≠ t)
    (hKpc : IsPCompIn 2 (cen s) K) (hM : IsPCompIn 2 (cen t) M) (hEK : E ≤ K) (hEM : E ≤ M)
    (hEs : E ≤ cen s) (hEq : IsTwoGenQuasi ↥E) (hEpc : IsPCompIn 2 (cen t ⊓ cen s) E)
    (hEn : IsDoubleCoverOfAlt (↥E ⧸ pPrimeCore 2 ↥E) n)
    (hMn : IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n) : LPrec X M K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcovEM : E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ :=
    covers_of_card_le hEM (pumpUp_card_eq hMn hEn).le
  have hMq : IsTwoGenQuasi ↥M :=
    (isTwoGenQuasi_subgroupOf_iff hM.1).1 (isPComponent_two_iff.1 hM.2).2
  have hsM : s ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
    mem_centralizerSection_of_covers hst hM hEM hEs hEq hcovEM
  have hEself : oTwoPrimeOf E = E := oTwoPrimeOf_eq_self_of_primeResidual hEq.1
  have hEEM : E ≤ oTwoPrimeOf (M ⊓ cen s) := by
    have := oTwoPrimeOf_mono (le_inf hEM hEs)
    rwa [hEself] at this
  have hEMM : oTwoPrimeOf (M ⊓ cen s) ≤ M := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovEMM : (oTwoPrimeOf (M ⊓ cen s)).subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := by
    rw [eq_top_iff, ← hcovEM]
    exact sup_le_sup_right (Subgroup.subgroupOf_mono M hEEM) _
  have hEMq : IsTwoGenQuasi ↥(oTwoPrimeOf (M ⊓ cen s)) :=
    isTwoGenQuasi_of_covers hEMM hcovEMM (primeResidual_oTwoPrimeOf _) hMq
  have hEMpc : IsPCompIn 2 (cen t ⊓ cen s) (oTwoPrimeOf (M ⊓ cen s)) :=
    pumpUp_isPCompIn_oTwoPrimeOf (inf_le_inf_right _ hM.1)
      (pumpUp_isSubnormal_inf inf_le_left inf_le_right (isPComponent_two_iff.1 hM.2).1) hEMq
  have heq : E = oTwoPrimeOf (M ⊓ cen s) := eq_of_isPCompIn_of_le hEpc hEMpc le_rfl hEEM hEq
  have hlt : lTwist M s ≤ K := lTwist_le_of_isPCompIn hKpc (heq ▸ hEK)
  exact Or.inr ⟨t, s, ht, hs, hst.symm, hne.symm, hM, hKpc, hsM, hlt⟩

end PumpUp

theorem sec6PumpUpHolds : Sec6PumpUpHolds := by
  intro X _ _ n hX _ h51 s t u K M hs ht hst hne hK hKn hM htK hlt
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup X := hX.simple
  set E : Subgroup X := oTwoPrimeOf (K ⊓ cen t) with hEdef
  have hKs : K ≤ cen s := hK.2.2.1.1
  have hKq : IsTwoGenQuasi ↥K :=
    (isTwoGenQuasi_subgroupOf_iff hKs).1 (isPComponent_two_iff.1 hK.2.2.1.2).2
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hEK : E ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hEs : E ≤ cen s := hEK.trans hKs
  have hEM : E ≤ M := by
    have h1 : E ≤ lTwist K t := by
      rw [lTwist, oPrimeResidualOf_two_eq_oTwoPrimeOf]
      exact oTwoPrimeOf_mono le_sup_left
    exact h1.trans hlt
  have hcovE : E.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers ht2 hKq.1 htK
  have hEq : IsTwoGenQuasi ↥E :=
    isTwoGenQuasi_of_covers hEK hcovE (primeResidual_oTwoPrimeOf _) hKq
  have hEn : IsDoubleCoverOfAlt (↥E ⧸ pPrimeCore 2 ↥E) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hEK hcovE n).2 hKn
  have hEpc : IsPCompIn 2 (cen t ⊓ cen s) E :=
    pumpUp_isPCompIn_oTwoPrimeOf (le_inf inf_le_right (inf_le_left.trans hKs))
      (pumpUp_isSubnormal_inf inf_le_right inf_le_left (isPComponent_two_iff.1 hK.2.2.1.2).1)
      hEq
  obtain ⟨v, hv⟩ := exists_isIntrinsicIn_twist hK hcovE hEpc
  have hE1 : E ≤ Sec6K X n (cen t ⊓ cen s) := le_sSup (Or.inl ⟨⟨v, hv⟩, hEn⟩)
  have hsCt : s ∈ cen t := Subgroup.mem_centralizer_singleton_iff.2 hst
  have hCt : cen t ≠ ⊤ := centralizer_ne_top_of_involution hX.nonabelian ht
  have hE2 : E ≤ Sec6K X n (cen t) := hE1.trans (h51.b (cen t) hCt s hsCt hs).1
  have hMK : Sec6KComp X n (cen t) M := by
    refine pumpUp_mem_of_le_sSup (S := {L | Sec6KComp X n (cen t) L}) hM ?_ hEM hE2 hEq
    rintro J (⟨⟨w, hw⟩, -⟩ | ⟨hJ, -⟩)
    · exact hw.2.2.1
    · exact hJ.1
  rcases hMK with ⟨⟨w, hw⟩, hMn⟩ | hMc
  · exact Or.inl ⟨⟨w, hw⟩, hMn,
      pumpUp_lPrec hs ht hst hne hK.2.2.1 hM hEK hEM hEs hEq hEpc hEn hMn⟩
  · exact Or.inr hMc

end CFSG.OddStandard.Solomon75
