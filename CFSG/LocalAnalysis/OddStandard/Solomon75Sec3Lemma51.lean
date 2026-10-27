module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Pick
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Final
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cal
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Max

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Kp

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizerSection_of_covers {u s : X} {Lu E : Subgroup X}
    (hus : s * u = u * s) (hLu : IsPCompIn 2 (centralizer ({u} : Set X)) Lu) (hEL : E ≤ Lu)
    (hEs : E ≤ centralizer ({s} : Set X)) (hEq : IsTwoGenQuasi ↥E)
    (hcov : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤) :
    s ∈ centralizerSection Lu (pPrimeCoreOf 2 Lu) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  have hsCu : s ∈ Cu := Subgroup.mem_centralizer_singleton_iff.2 hus
  set φ : X ≃* X := MulAut.conj s with hφ
  have hCuφ : Cu.map φ.toMonoidHom = Cu :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsCu)
  have hLuφ : IsPComponent 2 ((Lu.map φ.toMonoidHom).subgroupOf Cu) := by
    have := (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hLu.1).2 hLu.2
    rwa [hCuφ] at this
  have hLuφle : Lu.map φ.toMonoidHom ≤ Cu := by
    rw [← hCuφ]
    exact Subgroup.map_mono hLu.1
  have hEφ : E ≤ Lu.map φ.toMonoidHom := by
    intro x hx
    refine ⟨x, hEL hx, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hEs hx)
    show s * x * s⁻¹ = x
    rw [this.symm, mul_inv_cancel_right]
  have heq : Lu.map φ.toMonoidHom = Lu := by
    by_contra hne
    have hK : IsPComponent 2 (Lu.subgroupOf Cu) := hLu.2
    have hne' : Lu.subgroupOf Cu ≠ (Lu.map φ.toMonoidHom).subgroupOf Cu := by
      intro h
      apply hne
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hLuφle, inf_of_le_left hLu.1] at h
      exact h.symm
    obtain ⟨-, -, hcore, -⟩ :=
      (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hK hLuφ).2 hne'
    have hEC : E ≤ Cu := hEL.trans hLu.1
    have hEC' : IsTwoGenQuasi ↥(E.subgroupOf Cu) := (isTwoGenQuasi_subgroupOf_iff hEC).2 hEq
    have h1 : E.subgroupOf Cu ≤ Lu.subgroupOf Cu := Subgroup.subgroupOf_mono Cu hEL
    have h2 : E.subgroupOf Cu ≤ (Lu.map φ.toMonoidHom).subgroupOf Cu :=
      Subgroup.subgroupOf_mono Cu hEφ
    have h3 : ⁅E.subgroupOf Cu, E.subgroupOf Cu⁆ ≤
        (pPrimeCore 2 ↥(Lu.subgroupOf Cu)).map (Lu.subgroupOf Cu).subtype :=
      (Subgroup.commutator_mono h1 h2).trans (hcore.trans inf_le_left)
    refine not_commutator_le_of_odd hEC' ?_ h3
    have hc : Nat.card ((pPrimeCore 2 ↥(Lu.subgroupOf Cu)).map (Lu.subgroupOf Cu).subtype) =
        Nat.card (pPrimeCore 2 ↥(Lu.subgroupOf Cu)) :=
      Subgroup.card_map_of_injective (Lu.subgroupOf Cu).subtype_injective
    rw [hc]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hsN : s ∈ normalizer (Lu : Set X) := mem_normalizer_of_map_conj_eq heq
  have hOφ : (pPrimeCoreOf 2 Lu).map φ.toMonoidHom = pPrimeCoreOf 2 Lu := by
    rw [← pPrimeCoreOf_map_mulEquiv, heq]
  have hsO : s ∈ normalizer (pPrimeCoreOf 2 Lu : Set X) := mem_normalizer_of_map_conj_eq hOφ
  refine ⟨hsN, hsO, fun k hk => ?_⟩
  have hk' : (⟨k, hk⟩ : ↥Lu) ∈ E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu := hcov ▸ Subgroup.mem_top _
  obtain ⟨f, hf, o, ho, hfo⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
  have hkfo : k = (f : X) * (o : X) := by
    have := congrArg Subtype.val hfo
    exact this.symm
  have hfE : (f : X) ∈ E := hf
  have hoO : (o : X) ∈ pPrimeCoreOf 2 Lu := ⟨o, ho, rfl⟩
  have hfs : ⁅(f : X), s⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hEs hfE))
  have hid : ⁅(f : X) * (o : X), s⁆ = (f : X) * ⁅(o : X), s⁆ * (f : X)⁻¹ * ⁅(f : X), s⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hkfo, hid, hfs, mul_one]
  have hos : ⁅(o : X), s⁆ ∈ pPrimeCoreOf 2 Lu := by
    have h1 : s * (o : X)⁻¹ * s⁻¹ ∈ pPrimeCoreOf 2 Lu :=
      (Subgroup.mem_normalizer_iff.1 hsO _).1 ((pPrimeCoreOf 2 Lu).inv_mem hoO)
    have : ⁅(o : X), s⁆ = (o : X) * (s * (o : X)⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (pPrimeCoreOf 2 Lu).mul_mem hoO h1
  have hfN : (f : X) ∈ normalizer (pPrimeCoreOf 2 Lu : Set X) :=
    mem_normalizer_pPrimeCoreOf_of_mem f.2
  have := (Subgroup.mem_normalizer_iff.1 hfN _).1 hos
  exact this


theorem eq_of_isPCompIn_of_le {H K L E : Subgroup X} (hK : IsPCompIn 2 H K) (hL : IsPCompIn 2 H L)
    (hEK : E ≤ K) (hEL : E ≤ L) (hEq : IsTwoGenQuasi ↥E) : K = L := by
  by_contra hne
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : K.subgroupOf H ≠ L.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hK.1, inf_of_le_left hL.1] at h
    exact h
  obtain ⟨-, -, hcore, -⟩ :=
    (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hK.2 hL.2).2 hne'
  have hEH : E ≤ H := hEK.trans hK.1
  have hEq' : IsTwoGenQuasi ↥(E.subgroupOf H) := (isTwoGenQuasi_subgroupOf_iff hEH).2 hEq
  have h1 : E.subgroupOf H ≤ K.subgroupOf H := Subgroup.subgroupOf_mono H hEK
  have h2 : E.subgroupOf H ≤ L.subgroupOf H := Subgroup.subgroupOf_mono H hEL
  have h3 : ⁅E.subgroupOf H, E.subgroupOf H⁆ ≤
      (pPrimeCore 2 ↥(K.subgroupOf H)).map (K.subgroupOf H).subtype :=
    (Subgroup.commutator_mono h1 h2).trans (hcore.trans inf_le_left)
  refine not_commutator_le_of_odd hEq' ?_ h3
  have hc : Nat.card ((pPrimeCore 2 ↥(K.subgroupOf H)).map (K.subgroupOf H).subtype) =
      Nat.card (pPrimeCore 2 ↥(K.subgroupOf H)) :=
    Subgroup.card_map_of_injective (K.subgroupOf H).subtype_injective
  rw [hc]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card


theorem exists_isPCompIn_above {u s : X} {Lu E : Subgroup X} (hu : orderOf u = 2)
    (hus : s * u = u * s) (hLu : IsPCompIn 2 (centralizer ({u} : Set X)) Lu)
    (hEL : E ≤ Lu) (hEs : E ≤ centralizer ({s} : Set X)) (hEgen : primeResidual 2 ↥E = ⊤)
    (huE : u ∈ E) (hcov : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤) :
    IsPCompIn 2 (centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X))
        (oTwoPrimeOf (Lu ⊓ centralizer ({s} : Set X))) ∧
      ∃ M : Subgroup X, IsPCompIn 2 (centralizer ({s} : Set X)) M ∧
        oTwoPrimeOf (Lu ⊓ centralizer ({s} : Set X)) ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  set D : Subgroup X := centralizer ({s} : Set X) with hD
  set A : Subgroup X := Lu ⊓ D with hA
  set E' : Subgroup X := oTwoPrimeOf A with hE'
  have hLq : IsTwoGenQuasi ↥Lu :=
    (isTwoGenQuasi_subgroupOf_iff hLu.1).1 (isPComponent_two_iff.1 hLu.2).2
  have hEself : oTwoPrimeOf E = E := oTwoPrimeOf_eq_self_of_primeResidual hEgen
  have hEA : E ≤ A := le_inf hEL hEs
  have hEE' : E ≤ E' := by
    have := oTwoPrimeOf_mono hEA
    rwa [hEself] at this
  have hE'A : E' ≤ A := oTwoPrimeOf_le A
  have hE'Lu : E' ≤ Lu := hE'A.trans inf_le_left
  have hE'D : E' ≤ D := hE'A.trans inf_le_right
  have hE'Cu : E' ≤ Cu := hE'Lu.trans hLu.1
  have hcov' : E'.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [eq_top_iff, ← hcov]
    exact sup_le_sup_right (Subgroup.subgroupOf_mono Lu hEE') _
  have hE'q : IsTwoGenQuasi ↥E' :=
    isTwoGenQuasi_of_covers hE'Lu hcov' (primeResidual_oTwoPrimeOf A) hLq
  set H : Subgroup X := Cu ⊓ D with hH
  have hAH : A ≤ H := le_inf (inf_le_left.trans hLu.1) inf_le_right
  have hE'H : E' ≤ H := hE'A.trans hAH
  have hAsub : (A.subgroupOf H).IsSubnormal := by
    have h1 : A.subgroupOf H =
        (Lu.subgroupOf Cu).comap (Subgroup.inclusion (inf_le_left : H ≤ Cu)) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hA, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
    rw [h1]
    exact (isPComponent_two_iff.1 hLu.2).1.comap _
  have hE'sub : (E'.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_of_subnormal hAH hE'A hAsub (normal_subgroupOf_oTwoPrimeOf A)
  have hE'comp : IsPComponent 2 (E'.subgroupOf H) :=
    isPComponent_two_iff.2 ⟨hE'sub, (isTwoGenQuasi_subgroupOf_iff hE'H).2 hE'q⟩
  have huD : u ∈ D := Subgroup.mem_centralizer_singleton_iff.2 hus.symm
  set uD : ↥D := ⟨u, huD⟩ with huDdef
  have hcen : centralizer ({uD} : Set ↥D) = Cu.subgroupOf D := centralizer_singleton_subgroup huD
  have hEC_D : E'.subgroupOf D ≤ centralizer ({uD} : Set ↥D) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono D hE'Cu
  have huE' : uD ∈ E'.subgroupOf D := hEE' huE
  have hu2 : uD ^ 2 = 1 := by
    apply Subtype.ext
    show u ^ 2 = 1
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hE_D : IsPComponent 2 ((E'.subgroupOf D).subgroupOf (centralizer ({uD} : Set ↥D))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hE'Cu hE'D).2 hE'comp
  have hEL_D : E'.subgroupOf D ≤ pLayer ↥D 2 := by
    have hB : IsPGroup 2 (Subgroup.zpowers uD) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using orderOf_dvd_of_pow_eq_one hu2 : orderOf uD ∣ 2 ^ 1)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hbal := layer_balance (Subgroup.zpowers uD) hB
    have hcz : centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) =
        centralizer ({uD} : Set ↥D) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hEC_D' : E'.subgroupOf D ≤ centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) := by
      rw [hcz]
      exact hEC_D
    have hE_D' : IsPComponent 2 ((E'.subgroupOf D).subgroupOf
        (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D))) := by
      rw [hcz]
      exact hE_D
    have h1 := le_sSup (s := {L | IsPComponent 2 L}) hE_D'
    have h2 := Subgroup.map_mono (f := (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) :
      Set ↥D)).subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hEC_D'] at h2
    exact h2.trans hbal
  obtain ⟨M_D, hM_D, hEM_D⟩ := exists_isPComponent_le_of_mem_pLayer hEC_D huE' hu2 hE_D hEL_D
  refine ⟨⟨hE'H, hE'comp⟩, M_D.map D.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have h := Subgroup.comap_map_eq_self_of_injective D.subtype_injective M_D
    change IsPComponent 2 ((M_D.map D.subtype).comap D.subtype)
    rw [h]
    exact hM_D
  · have h1 := Subgroup.map_mono (f := D.subtype) hEM_D
    rwa [Subgroup.map_subgroupOf_eq_of_le hE'D] at h1


theorem lTwist_le_of_isPCompIn {Lu M : Subgroup X} {s : X}
    (hM : IsPCompIn 2 (centralizer ({s} : Set X)) M)
    (hAM : oTwoPrimeOf (Lu ⊓ centralizer ({s} : Set X)) ≤ M) : lTwist Lu s ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := centralizer ({s} : Set X) with hD
  set A : Subgroup X := Lu ⊓ D with hA
  unfold lTwist
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, oTwoPrimeOf_le_iff]
  intro x hx hx2
  obtain ⟨j, hj⟩ := hx2
  have hAD : A ≤ D := inf_le_right
  have hOD : oddCoreOf D ≤ D := oddCoreOf_le D
  have hxD : x ∈ D := (sup_le hAD hOD) hx
  have hxsup : (⟨x, hxD⟩ : ↥D) ∈ A.subgroupOf D ⊔ pPrimeCore 2 ↥D := by
    have h1 : (A ⊔ oddCoreOf D).subgroupOf D = A.subgroupOf D ⊔ (oddCoreOf D).subgroupOf D :=
      Subgroup.subgroupOf_sup hAD hOD
    have h2 : (oddCoreOf D).subgroupOf D = pPrimeCore 2 ↥D := by
      unfold oddCoreOf
      exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
    rw [← h2, ← h1]
    exact hx
  have hxj : (⟨x, hxD⟩ : ↥D) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
  obtain ⟨o, ho, a, ha, haj, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hxsup hxj
  have haA : (a : X) ∈ A := ha
  have haj' : (a : X) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val haj
  have haM : (a : X) ∈ M := hAM (mem_oTwoPrimeOf haA j haj')
  have hMD : IsPComponent 2 (M.subgroupOf D) := hM.2
  have hnorm := pPrimeCore_le_normalizer_of_isPComponent hMD ho
  have haMD : a ∈ M.subgroupOf D := haM
  have := (Subgroup.mem_normalizer_iff.1 hnorm a).1 haMD
  have hxM : (⟨x, hxD⟩ : ↥D) ∈ M.subgroupOf D := by
    rw [hxa]
    exact this
  exact hxM


theorem exists_isIntrinsicIn_centralizer {n : ℕ} (hA : HypA X) (hn : IsMaxAhatDeg X n) {s u : X}
    {H L : Subgroup X} (hs : orderOf s = 2) (hHs : H ≤ centralizer ({s} : Set X))
    (hL : IsIntrinsicIn X H L u) (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    ∃ M : Subgroup X, IsIntrinsicIn X (centralizer ({s} : Set X)) M u ∧
      IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n ∧
        oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hu, huL, ⟨hLH, hLpc⟩, hLeq, Lu, hLuI, hLuEq⟩ := hL
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  set D : Subgroup X := centralizer ({s} : Set X) with hD
  set E : Subgroup X := oTwoPrimeOf (L ⊓ Cu) with hE
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq hLuEq
  have hEL : E ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hELu : E ≤ Lu := by
    rw [hLuEq]
    exact le_sup_right
  have hEs : E ≤ D := hEL.trans (hLH.trans hHs)
  have hEgen : primeResidual 2 ↥E = ⊤ := primeResidual_oTwoPrimeOf _
  have hEself : oTwoPrimeOf E = E := oTwoPrimeOf_eq_self_of_primeResidual hEgen
  have huCu : u ∈ L ⊓ Cu :=
    ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have huE : u ∈ E := mem_oTwoPrimeOf huCu 1 (by simpa using hu2)
  have hLuCu : IsPCompIn 2 Cu Lu := ⟨hLuI.1, hLuI.2.2.1⟩
  have hLq : IsTwoGenQuasi ↥Lu :=
    (isTwoGenQuasi_subgroupOf_iff hLuCu.1).1 (isPComponent_two_iff.1 hLuCu.2).2
  have hcovL : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    exact hLeq.symm
  have hcovLu : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [covers_subgroupOf_iff hELu, sup_comm]
    exact hLuEq.symm
  have hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hELu hcovLu n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEL hcovL n).2 hLn)
  have hEq : IsTwoGenQuasi ↥E := isTwoGenQuasi_of_covers hELu hcovLu hEgen hLq
  by_cases hsu : s = u
  ·
    subst hsu
    exact ⟨Lu, hLuI.isIntrinsicIn hu, hLun, hELu⟩
  have hus : s * u = u * s := (Subgroup.mem_centralizer_singleton_iff.1 (hLH.trans hHs huL)).symm
  obtain ⟨hE'pc, M, hMpc, hAM⟩ := exists_isPCompIn_above hu hus hLuCu hELu hEs hEgen huE hcovLu
  have hEAle : E ≤ oTwoPrimeOf (Lu ⊓ D) := by
    have := oTwoPrimeOf_mono (le_inf hELu hEs : E ≤ Lu ⊓ D)
    rwa [hEself] at this
  have hEM : E ≤ M := hEAle.trans hAM
  have hMq : IsTwoGenQuasi ↥M :=
    (isTwoGenQuasi_subgroupOf_iff hMpc.1).1 (isPComponent_two_iff.1 hMpc.2).2
  have hsec : s ∈ centralizerSection Lu (pPrimeCoreOf 2 Lu) :=
    mem_centralizerSection_of_covers hus hLuCu hELu hEs hEq hcovLu
  have hlt : lTwist Lu s ≤ M := lTwist_le_of_isPCompIn hMpc hAM
  have hMcomp : IsLComp X M := ⟨⟨s, hs, hMpc⟩, not_isSolvable_of_isTwoGenQuasi hMq⟩
  have hprec : LPrec X Lu M := Or.inr ⟨u, s, hu, hs, hus.symm, fun h => hsu h.symm, hLuCu, hMpc,
    hsec, hlt⟩
  have hcard1 := hA.card_quot_le_of_lPrec hn hu hLuI hLun hMcomp hprec
  have hcard2 : Nat.card (↥Lu ⧸ pPrimeCore 2 ↥Lu) ≤ Nat.card (↥E ⧸ pPrimeCore 2 ↥E) :=
    card_quot_pPrimeCore_le_of_covers hELu le_rfl hcovLu
  have hcovM : E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := covers_of_card_le hEM (hcard1.trans hcard2)
  have hMn : IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hEM hcovM n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEL hcovL n).2 hLn)
  refine ⟨M, ?_, hMn, hEM⟩
  have hECu : E ≤ Cu := (oTwoPrimeOf_le _).trans inf_le_right
  have hEMC : E ≤ M ⊓ Cu := le_inf hEM hECu
  set EM : Subgroup X := oTwoPrimeOf (M ⊓ Cu) with hEMdef
  have hEEM : E ≤ EM := by
    have := oTwoPrimeOf_mono hEMC
    rwa [hEself] at this
  have hEMM : EM ≤ M := (oTwoPrimeOf_le _).trans inf_le_left
  have hEMA : EM ≤ M ⊓ Cu := oTwoPrimeOf_le _
  have hMD : M ≤ D := hMpc.1
  set H₂ : Subgroup X := Cu ⊓ D with hH₂
  have hAMH : M ⊓ Cu ≤ H₂ := le_inf inf_le_right (inf_le_left.trans hMD)
  have hEMH : EM ≤ H₂ := hEMA.trans hAMH
  have hAMsub : ((M ⊓ Cu).subgroupOf H₂).IsSubnormal := by
    have h1 : (M ⊓ Cu).subgroupOf H₂ =
        (M.subgroupOf D).comap (Subgroup.inclusion (inf_le_right : H₂ ≤ D)) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2.1⟩⟩
    rw [h1]
    exact (isPComponent_two_iff.1 hMpc.2).1.comap _
  have hEMsub : (EM.subgroupOf H₂).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_of_subnormal hAMH hEMA hAMsub
      (normal_subgroupOf_oTwoPrimeOf (M ⊓ Cu))
  have hcovEM : EM.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := by
    rw [eq_top_iff, ← hcovM]
    exact sup_le_sup_right (Subgroup.subgroupOf_mono M hEEM) _
  have hEMq : IsTwoGenQuasi ↥EM :=
    isTwoGenQuasi_of_covers hEMM hcovEM (primeResidual_oTwoPrimeOf _) hMq
  have hEMpc : IsPCompIn 2 H₂ EM :=
    ⟨hEMH, isPComponent_two_iff.2 ⟨hEMsub, (isTwoGenQuasi_subgroupOf_iff hEMH).2 hEMq⟩⟩
  have hEMeq : oTwoPrimeOf (Lu ⊓ D) = EM :=
    eq_of_isPCompIn_of_le hE'pc hEMpc hEAle hEEM hEq
  have hEMLu : EM ≤ Lu := by
    rw [← hEMeq]
    exact (oTwoPrimeOf_le _).trans inf_le_left
  refine ⟨hu, hEM huE, hMpc, ?_, Lu, hLuI, ?_⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    refine le_antisymm ?_ (sup_le (Subgroup.map_subtype_le _) hEMM)
    have h1 := (covers_subgroupOf_iff hEM).1 hcovM
    exact h1.symm.le.trans (sup_le (hEEM.trans le_sup_right) le_sup_left)
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    refine le_antisymm ?_ (sup_le (Subgroup.map_subtype_le _) hEMLu)
    exact hLuEq.le.trans (sup_le_sup_left hEEM _)


theorem K0_le_K0_centralizer {n : ℕ} (hA : HypA X) (hn : IsMaxAhatDeg X n) {s : X}
    (hs : orderOf s = 2) {H : Subgroup X} (hHs : H ≤ centralizer ({s} : Set X)) :
    K0 X n H ≤ K0 X n (centralizer ({s} : Set X)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sSup_le fun L hLmem => ?_
  obtain ⟨⟨u, hL⟩, hLn⟩ := hLmem
  obtain ⟨M, hM, hMn, hEM⟩ := exists_isIntrinsicIn_centralizer hA hn hs hHs hL hLn
  have hMK : M ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup ⟨⟨u, hM⟩, hMn⟩
  obtain ⟨hu, huL, ⟨hLH, hLpc⟩, hLeq, -⟩ := hL
  have hEL : oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ L :=
    (oTwoPrimeOf_le _).trans inf_le_left
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLH).1 (isPComponent_two_iff.1 hLpc).2
  have hcovL : (oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))).subgroupOf L ⊔
      pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq
    exact hLeq.symm
  refine le_of_covers_of_normalized hEL hcovL hLq.1 (hEM.trans hMK) fun c hc => ?_
  exact mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer (hHs (hLH hc))))

theorem K0_inf_centralizer_le {n : ℕ} (hA : HypA X) (hn : IsMaxAhatDeg X n) {s : X}
    (hs : orderOf s = 2) (t : X) :
    K0 X n (centralizer ({s} : Set X) ⊓ centralizer ({t} : Set X)) ≤
      K0 X n (centralizer ({s} : Set X)) :=
  K0_le_K0_centralizer hA hn hs inf_le_left

theorem lemma51c_of_hypA {n : ℕ} (hA : HypA X) (hn : IsMaxAhatDeg X n) : Lemma51c X n := by
  intro s t hs ht _ _
  refine le_inf (K0_inf_centralizer_le hA hn hs t) ?_
  rw [inf_comm]
  exact K0_inf_centralizer_le hA hn ht s

end Kp

end CFSG.OddStandard.Solomon75
