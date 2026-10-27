module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type*} [Group G]

theorem coe_mul_coe_of_isSemidirect {X Y Z : Subgroup G} (h : IsSemidirect X Y Z) :
    (Y : Set G) * (Z : Set G) = (X : Set G) := by
  obtain ⟨hY, hZ, hnorm, hsup, hinf⟩ := h
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y Z (hZ.trans hnorm), hsup]

theorem natCard_mul_natCard_of_isSemidirect [Finite G] {X Y Z : Subgroup G}
    (h : IsSemidirect X Y Z) : Nat.card ↥Y * Nat.card ↥Z = Nat.card ↥X := by
  have h2 := natCard_mul_mul_natCard_inf Y Z
  rw [coe_mul_coe_of_isSemidirect h, h.2.2.2.2, Subgroup.card_bot, mul_one] at h2
  simpa using h2.symm

theorem index_subgroupOf_of_isSemidirect [Finite G] {X Y Z : Subgroup G}
    (h : IsSemidirect X Y Z) : (Y.subgroupOf X).index = Nat.card ↥Z := by
  have h1 : Nat.card ↥(Y.subgroupOf X) * (Y.subgroupOf X).index = Nat.card ↥X :=
    Subgroup.card_mul_index _
  rw [natCard_subgroupOf_eq h.1] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
    (h1.trans (natCard_mul_natCard_of_isSemidirect h).symm)

theorem isSemidirect_inf_of_le [Finite G] {X Y Z W : Subgroup G} (h : IsSemidirect X Y Z)
    (hYW : Y ≤ W) (hWX : W ≤ X) : IsSemidirect W Y (W ⊓ Z) := by
  obtain ⟨hY, hZ, hnorm, hsup, hinf⟩ := h
  refine ⟨hYW, inf_le_left, hWX.trans hnorm, le_antisymm (sup_le hYW inf_le_left) ?_, ?_⟩
  · intro w hw
    have hwX : (w : G) ∈ (X : Set G) := hWX hw
    obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.1
      (by rw [coe_mul_coe_of_isSemidirect ⟨hY, hZ, hnorm, hsup, hinf⟩]; exact hwX)
    have hzW : z ∈ W := by
      have : a⁻¹ * (a * z) ∈ W := W.mul_mem (W.inv_mem (hYW ha)) hw
      simpa using this
    exact Subgroup.mul_mem_sup ha (mem_inf.2 ⟨hzW, hz⟩)
  · exact le_bot_iff.1 (le_trans (inf_le_inf_left Y inf_le_right) (le_of_eq hinf))

theorem notMem_kappaPrimes_of_elementaryAbelianPRank_eq_two [Finite G] {p : ℕ} {M : Subgroup G}
    (hp : p.Prime) (hrank : elementaryAbelianPRank p ↥M = 2) : p ∉ kappaPrimes M := by
  intro hmem
  obtain ⟨-, hdvd, -, S, hcyc, -⟩ := mem_kappaPrimes_iff.1 hmem
  rw [elementaryAbelianPRank_eq_one_of_isCyclic_sylow hp hdvd ⟨S, hcyc⟩] at hrank
  exact absurd hrank (by decide)

theorem natCard_dvd_relIndex [Finite G] {M E U K : Subgroup G} (hKM : K ≤ M)
    (hM : IsSemidirect M (sigmaCore M) E) (hE : IsSemidirect E U K) :
    Nat.card ↥U ∣ K.relIndex M := by
  have h1 : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  rw [natCard_subgroupOf_eq hKM] at h1
  have h2 : Nat.card ↥(sigmaCore M) * (Nat.card ↥U * Nat.card ↥K) = Nat.card ↥M := by
    rw [natCard_mul_natCard_of_isSemidirect hE, natCard_mul_natCard_of_isSemidirect hM]
  have h3 : Nat.card ↥K * (K.subgroupOf M).index
      = Nat.card ↥K * (Nat.card ↥(sigmaCore M) * Nat.card ↥U) := by
    rw [h1, ← h2]; ring
  have h4 : (K.subgroupOf M).index = Nat.card ↥(sigmaCore M) * Nat.card ↥U :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  exact ⟨Nat.card ↥(sigmaCore M), by rw [Subgroup.relIndex, h4]; ring⟩

theorem isMulCommutative_of_map_subtype {U : Subgroup G} {S : Subgroup ↥U}
    (h : IsMulCommutative ↥(S.map U.subtype)) : IsMulCommutative ↥S := by
  have := h
  refine IsMulCommutative.of_comm fun a b => ?_
  have ha : ((a : ↥U) : G) ∈ S.map U.subtype := ⟨a, a.2, rfl⟩
  have hb : ((b : ↥U) : G) ∈ S.map U.subtype := ⟨b, b.2, rfl⟩
  exact Subtype.ext (Subtype.ext (setLike_mul_comm ha hb))

theorem sylow_isMulCommutative_of_le [Finite G] {p : ℕ} (hp : p.Prime) {U E : Subgroup G}
    (hUE : U ≤ E) (hab : ∀ P : Subgroup G, IsSylowOf p P E → IsMulCommutative ↥P)
    (S : Sylow p ↥U) : IsMulCommutative ↥(S : Subgroup ↥U) := by
  have : Fact p.Prime := ⟨hp⟩
  set T : Subgroup G := (S : Subgroup ↥U).map U.subtype with hT
  have hTU : T ≤ U := Subgroup.map_subtype_le _
  have hTE : T ≤ E := hTU.trans hUE
  have hTp : IsPGroup p ↥T := S.isPGroup'.map U.subtype
  have hTp' : IsPGroup p ↥(T.subgroupOf E) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTE).symm
  obtain ⟨Q, hQ⟩ := hTp'.exists_le_sylow
  have hPcard : Nat.card ↥((Q : Subgroup ↥E).map E.subtype)
      = p ^ (Nat.card ↥E).factorization p := by
    rw [Subgroup.card_subtype]; exact Q.card_eq_multiplicity
  have hPab : IsMulCommutative ↥((Q : Subgroup ↥E).map E.subtype) :=
    hab _ ⟨Subgroup.map_subtype_le _, hPcard⟩
  have hTQ : T ≤ (Q : Subgroup ↥E).map E.subtype := by
    have := Subgroup.map_mono (f := E.subtype) hQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hTE] at this
  have := hPab
  exact isMulCommutative_of_map_subtype (isMulCommutative_of_le hTQ)

theorem mem_kappaPrimes_of_orderOf_eq [Finite G] {q : ℕ} {M : Subgroup G} {z : G}
    (hq : q.Prime) (hodd : Odd q) (hzM : z ∈ M) (hz : orderOf z = q)
    (hrank : elementaryAbelianPRank q ↥M = 1) (hnotσ : q ∉ sigmaPrimes M)
    (hcent : sigmaCore M ⊓ centralizer ({z} : Set G) ≠ ⊥) : q ∈ kappaPrimes M := by
  have : Fact q.Prime := ⟨hq⟩
  have hzord : orderOf (⟨z, hzM⟩ : ↥M) = q := by
    rw [← hz]; exact (Subgroup.orderOf_coe (⟨z, hzM⟩ : ↥M)).symm
  have hpg : IsPGroup q ↥(zpowers (⟨z, hzM⟩ : ↥M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hzS : z ∈ ((S : Subgroup ↥M).map M.subtype : Subgroup G) :=
    ⟨⟨z, hzM⟩, hS (Subgroup.mem_zpowers _), rfl⟩
  have hcyc : IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    rw [isCyclic_map_subtype_iff]
    exact isCyclic_of_elementaryAbelianPRank_le_one hq hodd S.isPGroup'
      (le_trans (elementaryAbelianPRank_subgroup_le hq.one_lt _) hrank.le)
  refine mem_kappaPrimes_iff.2 ⟨hq, ?_, hnotσ, S, hcyc, z, hzS, ?_, hcent⟩
  · rw [← hz]; exact Subgroup.orderOf_dvd_natCard M hzM
  · intro h1
    rw [h1, orderOf_one] at hz
    exact hq.one_lt.ne hz

theorem FNI_nonabelian_ambient_normal_hall_free_complement
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_nonabelian_ambient_prime_kernel_complement.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FNI_nonabelian_ambient_normal_hall_free_complement.{u} := by
  intro G _ _ hG p M A E K U hplane hnonab hK hKE hUE hsemi A₀ hA₀
  have hG' : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hG'' : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hplaneA : IsOutsideSigmaPlane p M A :=
    ⟨hplane.isCoatom, hplane.prime, hplane.notMem_sigma, hplane.le_M_A, hplane.isPlane⟩
  obtain ⟨hrank, -, -, -⟩ := h₃ G hG'' p M A hplaneA
  have hpκ : p ∉ kappaPrimes M :=
    notMem_kappaPrimes_of_elementaryAbelianPRank_eq_two hplane.prime hrank
  obtain ⟨hA₀card, hMnorm, hA₀cent, hsylab, E₀, hE₀semi, hpE₀, hE₀tau⟩ :=
    h₂ G hG p M A E hplane hnonab A₀ hA₀
  obtain ⟨-, hSbot⟩ := FBG_sigma_core_nontrivial h₁ G hG' M hplane.isCoatom
  have hEM : E ≤ M := hplane.decomp.2.1
  have hUM : U ≤ M := hUE.trans hEM
  have hA₀A : A₀ ≤ A := by rw [hA₀]; exact inf_le_left
  have hA₀E : A₀ ≤ E := hA₀A.trans hplane.le_E_A
  have hrelne : K.relIndex M ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have hUprimes : ∀ r ∈ (Nat.card ↥U).primeFactors, r ∉ kappaPrimes M := fun r hr =>
    hK.2.2 r (Nat.primeFactors_mono (natCard_dvd_relIndex hK.1 hplane.decomp hsemi) hrelne hr)
  have hUhall : IsHallPiSubgroup ((kappaPrimes M)ᶜ) (U.subgroupOf E) := by
    refine ⟨isPiSubgroup_iff.2 fun r hr => ?_, fun r hr => ?_⟩
    · rw [natCard_subgroupOf_eq hUE] at hr
      exact hUprimes r hr
    · rw [index_subgroupOf_of_isSemidirect hsemi] at hr
      simpa using hK.2.1 r hr
  have hUnormal : (U.subgroupOf E).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUE).2 hsemi.2.2.1
  have hA₀U : A₀ ≤ U := by
    have hpi : IsPiSubgroup ((kappaPrimes M)ᶜ) (A₀.subgroupOf E) := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [natCard_subgroupOf_eq hA₀E, hA₀card] at hr
      have hrp : r = p := by
        obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
        exact (Nat.prime_dvd_prime_iff_eq hrp hplane.prime).1 hrd
      rw [hrp]; exact hpκ
    have h4 := hUhall.le_of_isPiSubgroup hpi
    have h5 := Subgroup.map_mono (f := E.subtype) h4
    rwa [map_subgroupOf_eq_of_le hA₀E, map_subgroupOf_eq_of_le hUE] at h5
  set V : Subgroup G := U ⊓ E₀ with hVdef
  have hUsemi : IsSemidirect U A₀ V := isSemidirect_inf_of_le hE₀semi hA₀U hUE
  have hVE₀ : V ≤ E₀ := inf_le_right
  have hVU : V ≤ U := inf_le_left
  have hpK : ¬ p ∣ Nat.card ↥K := fun hd =>
    hpκ (hK.2.1 p (Nat.mem_primeFactors.2 ⟨hplane.prime, hd, Nat.card_pos.ne'⟩))
  have hcards : Nat.card ↥V * Nat.card ↥K = Nat.card ↥E₀ := by
    have e1 := natCard_mul_natCard_of_isSemidirect hUsemi
    have e2 := natCard_mul_natCard_of_isSemidirect hE₀semi
    have e3 := natCard_mul_natCard_of_isSemidirect hsemi
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥A₀)) ?_
    calc Nat.card ↥A₀ * (Nat.card ↥V * Nat.card ↥K)
        = (Nat.card ↥A₀ * Nat.card ↥V) * Nat.card ↥K := by ring
      _ = Nat.card ↥E := by rw [e1, e3]
      _ = Nat.card ↥A₀ * Nat.card ↥E₀ := e2.symm
  have hpV : p ∣ Nat.card ↥V := by
    have hdm : p ∣ Nat.card ↥V * Nat.card ↥K := hcards ▸ hpE₀
    exact (hplane.prime.dvd_mul.1 hdm).resolve_right hpK
  have hfree : ∀ v ∈ V, v ≠ 1 → cent1 (sigmaCore M) v = ⊥ := by
    intro v hv hv1
    by_contra hne
    obtain ⟨h, hhmem, hh1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    obtain ⟨hhS, hhc⟩ := mem_inf.1 hhmem
    have hcomm : v * h = h * v := (Subgroup.mem_centralizer_singleton_iff.1 hhc).symm
    set W : Subgroup G := V ⊓ centralizer ({h} : Set G) with hWdef
    have hvW : v ∈ W := mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    have hWbot : W ≠ ⊥ := fun hb => hv1 (by simpa [hb] using (hb ▸ hvW : v ∈ (⊥ : Subgroup G)))
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥W)
      (fun hone => hWbot (Subgroup.card_eq_one.1 hone))
    obtain ⟨z, hzW, hzord⟩ := exists_mem_orderOf_eq_of_dvd hq hqd
    obtain ⟨hzV, hzc⟩ := mem_inf.1 hzW
    have hzE₀ : z ∈ cent1 E₀ h := mem_inf.2 ⟨hVE₀ hzV, hzc⟩
    have hqdvd : q ∣ Nat.card ↥(cent1 E₀ h) := by
      rw [← hzord]; exact Subgroup.orderOf_dvd_natCard _ hzE₀
    have hqτ : q ∈ tau1Primes M :=
      hE₀tau h hhS hh1 q (Nat.mem_primeFactors.2 ⟨hq, hqdvd, Nat.card_pos.ne'⟩)
    have hzM : z ∈ M := hUM (hVU hzV)
    have hqodd : Odd q := hG.odd_natCard.of_dvd_nat (by
      rw [← hzord]; exact orderOf_dvd_natCard z)
    have hcentz : sigmaCore M ⊓ centralizer ({z} : Set G) ≠ ⊥ := by
      intro hb
      have hmem : h ∈ sigmaCore M ⊓ centralizer ({z} : Set G) :=
        mem_inf.2 ⟨hhS, Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hzc).symm⟩
      rw [hb] at hmem
      exact hh1 (by simpa using hmem)
    have hqκ : q ∈ kappaPrimes M := mem_kappaPrimes_of_orderOf_eq hq hqodd hzM hzord
      (elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ)
      (notMem_sigmaPrimes_of_mem_tau1Primes hqτ) hcentz
    have hqU : q ∣ Nat.card ↥U := by
      rw [← hzord]; exact Subgroup.orderOf_dvd_natCard _ (hVU hzV)
    exact hUprimes q (Nat.mem_primeFactors.2 ⟨hq, hqU, Nat.card_pos.ne'⟩) hqκ
  have hUnormA₀ : U ≤ normalizer (A₀ : Set G) := hUM.trans hMnorm
  have hkernel : IsSplitCentralizingPrimeKernel p (sigmaCore M) U A₀ V :=
    { prime := hplane.prime
      H_ne_bot := hSbot
      U_le_normalizer := hUM.trans (le_normalizer_sigmaCore M)
      A_le_U := hA₀U
      V_le_U := hVU
      A_normal := (normal_subgroupOf_iff_le_normalizer hA₀U).2 hUnormA₀
      natCard_A := hA₀card
      sup_eq := hUsemi.2.2.2.1
      inf_eq := hUsemi.2.2.2.2
      A_le_centralizer := hA₀cent
      dvd_natCard_V := hpV
      exists_sylow_isMulCommutative :=
        ⟨default, sylow_isMulCommutative_of_le hplane.prime hUE hsylab default⟩
      centralizer_inf_eq_bot := hfree }
  exact ⟨hA₀U, hkernel.isMulCommutative, hUnormA₀, V, hUsemi, hpV, hkernel.exponent_eq,
    hfree, fun h hh hh1 => hkernel.inf_centralizer_eq hh hh1⟩

end

end CFSG.FeitThompson.Proofs
