module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFForm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveT
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Props
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallN
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem IsPermAction.eq_of_isPComponent_of_onto (hρ : IsPermAction θ ρ) [Finite X] (hn : 5 ≤ n)
    {Y : Subgroup X} (hYN : Y ≤ normalizer (M : Set X)) {L P : Subgroup X} (hLY : L ≤ Y)
    (hLpc : IsPComponent 2 (L.subgroupOf Y))
    (hLsurj : ∀ b : alternatingGroup (Fin n), ∃ (z : X) (hz : z ∈ L),
      ρ ⟨z, hYN (hLY hz)⟩ = (b : Perm (Fin n)))
    (hPY : P ≤ Y) (hPpc : IsPComponent 2 (P.subgroupOf Y))
    (hPK : ¬ P ≤ UnbalancedLayer.coreActionKernel M) : P = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OY := (pPrimeCore 2 ↥Y).map Y.subtype with hOYdef
  have hOYY : OY ≤ Y := map_subtype_le _
  have hOYN : OY ≤ normalizer (M : Set X) := fun w hw => hYN (hOYY hw)
  have hOYodd : Odd (Nat.card OY) := by
    rw [hOYdef, card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOYA : ∀ w : ↥OY, ρ (inclusion hOYN w) ∈ alternatingGroup (Fin n) := by
    intro w
    have hwo : (w : X) ∈ oddGen OY := by
      refine mem_oddGen w.2 (hOYodd.of_dvd_nat ?_)
      have := orderOf_dvd_natCard w
      rwa [← Subgroup.orderOf_coe] at this
    exact mem_alternatingGroup_of_mem_oddGen (ρ := ρ) hOYN hwo _
  let ψ : ↥OY →* alternatingGroup (Fin n) := (ρ.comp (inclusion hOYN)).codRestrict _ hOYA
  have hψ : ∀ w : ↥OY, ((ψ w : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ρ (inclusion hOYN w) := fun _ => rfl
  have hψodd : Odd (Nat.card ψ.range) := by
    have h1 := Subgroup.card_map_dvd (H := (⊤ : Subgroup ↥OY)) ψ
    rw [← MonoidHom.range_eq_map, Subgroup.card_top] at h1
    exact hOYodd.of_dvd_nat h1
  have hψn : ∀ b ∈ fixAlt (1 : Perm (Fin n)), ∀ g ∈ ψ.range, b * g * b⁻¹ ∈ ψ.range := by
    rintro b - _ ⟨w, rfl⟩
    obtain ⟨z, hz, hzb⟩ := hLsurj b
    have hzY : z ∈ Y := hLY hz
    obtain ⟨w', hw', hw'e⟩ := w.2
    have hc := (inferInstance : (pPrimeCore 2 ↥Y).Normal).conj_mem w' hw' ⟨z, hzY⟩
    have hzw : z * (w : X) * z⁻¹ ∈ OY := ⟨_, hc, by rw [← hw'e]; rfl⟩
    refine ⟨⟨_, hzw⟩, Subtype.ext ?_⟩
    rw [hψ]
    change ρ ⟨z * (w : X) * z⁻¹, hOYN hzw⟩ = (b : Perm (Fin n)) * ρ (inclusion hOYN w) *
      (b : Perm (Fin n))⁻¹
    rw [← hzb]
    have h1 : (⟨z * (w : X) * z⁻¹, hOYN hzw⟩ : ↥(normalizer (M : Set X))) =
        ⟨z, hYN hzY⟩ * inclusion hOYN w * (⟨z, hYN hzY⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hbot := eq_bot_of_odd_of_commute (τ := 1) (by rw [mul_one]) (by simp)
    (by simp; omega) hψodd (fun g _ => by rw [mul_one, one_mul]) hψn
  have hOY1 : ∀ (w : X) (hw : w ∈ OY), ρ ⟨w, hOYN hw⟩ = 1 := by
    intro w hw
    have h1 : ψ ⟨w, hw⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot, mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [hψ] at h2
    exact h2
  by_contra hne
  have hne' : P.subgroupOf Y ≠ L.subgroupOf Y := fun h => by
    rw [subgroupOf_inj, inf_of_le_left hPY, inf_of_le_left hLY] at h
    exact hne h
  obtain ⟨-, -, hc', -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hPpc hLpc).2
      hne'
  obtain ⟨-, -, hsP, -, -⟩ := id hPpc
  have hPL : ∀ (p : X) (hp : p ∈ P) (z : X) (hz : z ∈ L),
      ρ ⟨p, hYN (hPY hp)⟩ * ρ ⟨z, hYN (hLY hz)⟩ = ρ ⟨z, hYN (hLY hz)⟩ * ρ ⟨p, hYN (hPY hp)⟩ := by
    intro p hp z hz
    have h1 : ⁅(⟨p, hPY hp⟩ : ↥Y), (⟨z, hLY hz⟩ : ↥Y)⁆ ∈ pPrimeCore 2 ↥Y := by
      have h2 := hc' (commutator_mem_commutator (show (⟨p, hPY hp⟩ : ↥Y) ∈ P.subgroupOf Y from hp)
        (show (⟨z, hLY hz⟩ : ↥Y) ∈ L.subgroupOf Y from hz))
      have h3 := (mem_inf.1 h2).1
      rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsP] at h3
      exact (mem_inf.1 h3).2
    have h4 : ρ ⁅(⟨p, hYN (hPY hp)⟩ : ↥(normalizer (M : Set X))), ⟨z, hYN (hLY hz)⟩⁆ = 1 :=
      hOY1 (p * z * p⁻¹ * z⁻¹) ⟨_, h1, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  apply hPK
  intro p hp
  refine hρ.mem_coreActionKernel (hYN (hPY hp)) (eq_one_of_commute_fixAlt (τ := 1)
    (fun x hx => by simp at hx) (by simp; omega) fun b _ => ?_)
  obtain ⟨z, hz, hzb⟩ := hLsurj b
  rw [← hzb]
  exact hPL p hp z hz

theorem mem_coreActionKernel_of_support_subset_fix [Finite X] {J Jc : Subgroup X}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)}
    {θJ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} (hρJ : IsPermAction θJ ρJ)
    {c : X} {τ : Perm (Fin n)} (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θJ hx).support ⊆ τ.supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θJ hx).support ⊆ τ.supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥(τ.supportᶜ : Finset (Fin n))) = coreImage θJ hx)
    {w : X} (hwN : w ∈ normalizer (J : Set X)) (hwc : w * c = c * w)
    (hwD : (ρJ ⟨w, hwN⟩).support ⊆ τ.support) :
    w ∈ normalizer (Jc : Set X) ∧ w ∈ UnbalancedLayer.coreActionKernel Jc := by
  classical
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hconj : ∀ (x : X) (hx : x ∈ J), (coreImage θJ hx).support ⊆ τ.supportᶜ →
      coreImage θJ ((mem_normalizer_iff.mp hwN x).mp hx) = coreImage θJ hx := by
    intro x hx hxs
    have h1 := hρJ ⟨w, hwN⟩ ⟨x, hx⟩
    have h2 : (J.normalizerMonoidHom ⟨w, hwN⟩ ⟨x, hx⟩ : ↥J) =
        ⟨w * x * w⁻¹, (mem_normalizer_iff.mp hwN x).mp hx⟩ := rfl
    rw [h2] at h1
    change coreImage θJ _ = ρJ ⟨w, hwN⟩ * coreImage θJ hx * (ρJ ⟨w, hwN⟩)⁻¹ at h1
    rw [h1]
    have hd : (ρJ ⟨w, hwN⟩).Disjoint (coreImage θJ hx) := by
      rw [Perm.disjoint_iff_disjoint_support]
      exact Finset.disjoint_of_subset_left hwD
        (Finset.disjoint_of_subset_right hxs disjoint_compl_right)
    rw [hd.commute.eq]
    group
  have hwJc : w ∈ normalizer (Jc : Set X) :=
    mem_normalizer_of_fixed_component θJ hJcC hres hinv hsubP hwN hwc fun x hx hxs => by
      rw [hconj x hx hxs]
      exact hxs
  refine ⟨hwJc, hwJc, fun l hl => ?_⟩
  have hlJ := hJcJ' hl
  obtain ⟨hlJ', hls'⟩ := hsubP l hl
  have hls : (coreImage θJ hlJ).support ⊆ τ.supportᶜ := hls'
  have hwinv : w⁻¹ ∈ normalizer (J : Set X) := inv_mem hwN
  have hwl : w⁻¹ * l * w⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp hwinv l).mp hlJ
  have h1 := hρJ ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩
  have h2 : (J.normalizerMonoidHom ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩ : ↥J) = ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ := rfl
  rw [h2] at h1
  change coreImage θJ hwl = ρJ ⟨w⁻¹, hwinv⟩ * coreImage θJ hlJ * (ρJ ⟨w⁻¹, hwinv⟩)⁻¹ at h1
  have hd : (ρJ ⟨w⁻¹, hwinv⟩).Disjoint (coreImage θJ hlJ) := by
    rw [Perm.disjoint_iff_disjoint_support]
    have h9 : ρJ ⟨w⁻¹, hwinv⟩ = (ρJ ⟨w, hwN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h9, Perm.support_inv]
    exact Finset.disjoint_of_subset_left hwD
      (Finset.disjoint_of_subset_right hls disjoint_compl_right)
  have h3 : coreImage θJ hwl = coreImage θJ hlJ := by
    rw [h1, hd.commute.eq, mul_inv_cancel_right]
  have hwlJc : w⁻¹ * l * w⁻¹⁻¹ ∈ Jc := (mem_normalizer_iff.mp (inv_mem hwJc) l).mp hl
  have hz : l⁻¹ * w⁻¹ * l * w ∈ Jc := by
    have h4 : l⁻¹ * w⁻¹ * l * w = l⁻¹ * (w⁻¹ * l * w⁻¹⁻¹) := by group
    rw [h4]
    exact mul_mem (inv_mem hl) hwlJc
  have h5 : coreImage θJ (hJcJ' hz) = 1 := by
    have h6 : (⟨l⁻¹ * w⁻¹ * l * w, hJcJ' hz⟩ : ↥J) =
        (⟨l, hlJ⟩ : ↥J)⁻¹ * ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    have h7 : coreImage θJ (hJcJ' hz) = (coreImage θJ hlJ)⁻¹ * coreImage θJ hwl := by
      unfold coreImage
      rw [h6, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      rfl
    rw [h7, h3, inv_mul_cancel]
  have h8 : ((χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) :
      alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))) :
        Perm ↥(τ.supportᶜ : Finset (Fin n))) = 1 := by
    apply Perm.ofSubtype_injective
    rw [hχ ⟨_, hz⟩ (hJcJ' hz), h5, map_one]
  have h9 : χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 := Subtype.ext h8
  rw [map_eq_one_iff _ χ.injective, QuotientGroup.eq_one_iff] at h9
  exact ⟨_, h9, rfl⟩

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem exists_alt_of_five_fix (S : Sig36 X t J n e E D) (hn : 11 ≤ n) {H : Subgroup X}
    (hMH : M ≤ H) (hMpc : IsPComponent 2 (M.subgroupOf H)) (hHN : H ≤ normalizer (M : Set X))
    (hρ : IsPermAction θ ρ) {Q : Subgroup X} (hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M)
    (hQ2 : IsPGroup 2 Q)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ H)
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ → normalizer (T : Set X) ≤ H) {a g : X}
    (ha : a ∈ Q) (ha1 : a ≠ 1) (hs : g⁻¹ * a * g ∈ H)
    (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1) {x : X} (hxM : x ∈ M)
    (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X))) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    (hxf : FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hxM⟩))
    (hx' : g * x * g⁻¹ ∈ H) (hx'5 : n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card < 5)
    (h5 : 5 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card)
    (h9 : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card < 6 →
      9 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card) :
    ∃ (T : Subgroup X) (r : ℕ), 5 ≤ r ∧
      T ≤ centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) ∧
      ∃ f : ↥T →* alternatingGroup (Fin r), Function.Surjective f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hodd : Odd n := S.pair.2.1
  set s := g⁻¹ * a * g with hsdef
  have hsN : s ∈ normalizer (M : Set X) := hHN hs
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, hLapc, -, ⟨θLa, hθLa⟩, hLaN⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  have hx'N : g * x * g⁻¹ ∈ normalizer (M : Set X) := hHN hx'
  have hx'o : g * x * g⁻¹ ∈ oddGen (centralizer ({a} : Set X)) := by
    have h1 := conj_mem_oddGen_centralizer (g := g) hxo
    rwa [show g * s * g⁻¹ = a by rw [hsdef]; group] at h1
  have hx'A : ρ ⟨g * x * g⁻¹, hx'N⟩ ∈ alternatingGroup (Fin n) :=
    mem_alternatingGroup_of_mem_oddGen (ρ := ρ) (hCa.trans hHN) hx'o hx'N
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'a : g * x * g⁻¹ * a = a * (g * x * g⁻¹) :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ hx'o)
  have hx'La : g * x * g⁻¹ ∈ normalizer (La : Set X) := hLaN _ hx'N hx'a
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, le_normalizer hxM⟩ = 1 := map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hx4
    omega
  have hx'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hx'o2 : orderOf (g * x * g⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hx'2) hx'1
  have hCx : centralizer ({x} : Set X) ≤ H := hA x hxM hx2 hx4
  have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (oddGen_le _ hxo)
  set σ := ρ ⟨s, hsN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 from
      Subtype.ext hs2, map_one]
  have hσev : 2 ∣ σ.support.card := Perm.two_dvd_card_support (by rw [sq]; exact hσ2)
  obtain ⟨Ms, hMsle, hMspc, hinvs, hsubPs, χs, hχs⟩ :=
    exists_fixed_component_of_perm hMH hMpc hρ hsN hs2 h5
  have hk : Fintype.card ↥(σ.supportᶜ : Finset (Fin n)) = n - σ.support.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  set θs := χs.trans (Fintype.equivFinOfCardEq hk).altCongrHom with hθsdef
  have hMsH : Ms ≤ H ⊓ centralizer ({s} : Set X) := fun z hz =>
    mem_inf.mpr ⟨hMH (mem_inf.mp (hMsle hz)).1, (mem_inf.mp (hMsle hz)).2⟩
  have hamb : H ⊓ centralizer ({s} : Set X) ⊓ centralizer ({x} : Set X) =
      centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X) := by
    ext z
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hCx h1, h2⟩, h1⟩
  obtain ⟨R₀, r, hr5, hR₀le, hR₀pc, ⟨χ₀⟩⟩ : ∃ (R₀ : Subgroup X) (r : ℕ), 5 ≤ r ∧
      R₀ ≤ centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X) ∧
      IsPComponent 2 (R₀.subgroupOf (centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X))) ∧
      Nonempty (↥R₀ ⧸ pPrimeCore 2 ↥R₀ ≃* alternatingGroup (Fin r)) := by
    have hres := primeResidual_eq_top_of_isPComponent hMsH hMspc
    rcases hxf with ⟨h6, i, hi, i', hi', hii', hii'σ, hδ⟩ | ⟨h6, hδs⟩
    ·
      have hxD : (ρ ⟨x, le_normalizer hxM⟩).support ⊆ σ.support := by
        rw [hδ]
        intro v hv
        have h1 := Perm.support_mul_le _ _ hv
        rw [Finset.sup_eq_union, Finset.mem_union] at h1
        have hiσ : σ i ≠ i := Perm.mem_support.mp hi
        have hi'σ : σ i' ≠ i' := Perm.mem_support.mp hi'
        have hσσ : ∀ w, σ (σ w) = w := fun w => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
        rcases h1 with h1 | h1
        · rw [Perm.support_swap hiσ.symm, Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · exact hi
          · exact Perm.mem_support.mpr (by rw [hσσ]; exact hiσ.symm)
        · rw [Perm.support_swap hi'σ.symm, Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · exact hi'
          · exact Perm.mem_support.mpr (by rw [hσσ]; exact hi'σ.symm)
      obtain ⟨hxNs, hxK⟩ := mem_coreActionKernel_of_support_subset_fix hρ hMsle hres hinvs
        hsubPs χs hχs (le_normalizer hxM) hxs hxD
      have hce : x * (1 : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel Ms := by
        rw [inv_one, mul_one]
        exact hxK
      obtain ⟨R₀, hR₀, hR₀pc, -, -, χ₀, -⟩ := exists_fixed_component_of_acts hMsH hMspc θs hxNs
        hx2 (one_mem Ms) hce (by
          have h1 : coreImage θs (one_mem Ms) = 1 := by
            have h2 : ((⟨1, one_mem Ms⟩ : ↥Ms) : ↥Ms ⧸ pPrimeCore 2 ↥Ms) = 1 :=
              QuotientGroup.mk_one _
            unfold coreImage
            rw [h2, map_one]
            rfl
          rw [h1, Perm.support_one, Finset.card_empty, Nat.sub_zero]
          exact h5)
      have hcard : Fintype.card ↥((coreImage θs (one_mem Ms)).supportᶜ :
          Finset (Fin (n - σ.support.card))) = n - σ.support.card := by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        have h1 : coreImage θs (one_mem Ms) = 1 := by
          have h2 : ((⟨1, one_mem Ms⟩ : ↥Ms) : ↥Ms ⧸ pPrimeCore 2 ↥Ms) = 1 :=
            QuotientGroup.mk_one _
          unfold coreImage
          rw [h2, map_one]
          rfl
        rw [h1, Perm.support_one, Finset.card_empty, Nat.sub_zero]
      refine ⟨R₀, n - σ.support.card, h5, ?_, ?_, ⟨χ₀.trans
        (Fintype.equivFinOfCardEq hcard).altCongrHom⟩⟩
      · rw [← hamb]
        exact fun z hz => mem_inf.mpr ⟨hMsH (mem_inf.mp (hR₀ hz)).1, (mem_inf.mp (hR₀ hz)).2⟩
      · rw [← hamb]
        exact hR₀pc
    ·
      have h4s : σ.support.card ≤ 4 := by
        obtain ⟨q, hq⟩ := hσev
        omega
      have h9' := h9 h6
      have hxMs : x ∈ Ms := hinvs x hxM hxs ⟨1, by rw [pow_one, sq]; exact hx2⟩ (by
        have h1 := hρ.apply_of_mem (by omega) ⟨x, hxM⟩
        change (θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin n)).support ⊆ _
        rw [← h1]
        exact hδs)
      have hce : x * x⁻¹ ∈ UnbalancedLayer.coreActionKernel Ms := by
        rw [mul_inv_cancel]
        exact one_mem _
      have h4 : (coreImage θs hxMs).support.card = 4 := by
        unfold coreImage
        rw [hθsdef, MulEquiv.trans_apply, Equiv.altCongrHom_apply_coe,
          card_support_permCongr, ← card_support_ofSubtype, hχs ⟨x, hxMs⟩ hxM]
        unfold coreImage
        rw [← hρ.apply_of_mem (by omega) ⟨x, hxM⟩]
        exact hx4
      obtain ⟨R₀, hR₀, hR₀pc, -, -, χ₀, -⟩ := exists_fixed_component_of_acts hMsH hMspc θs
        (le_normalizer hxMs) hx2 hxMs hce (by rw [h4]; omega)
      have hcard : Fintype.card ↥((coreImage θs hxMs).supportᶜ :
          Finset (Fin (n - σ.support.card))) = n - σ.support.card - 4 := by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
      refine ⟨R₀, n - σ.support.card - 4, by omega, ?_, ?_, ⟨χ₀.trans
        (Fintype.equivFinOfCardEq hcard).altCongrHom⟩⟩
      · rw [← hamb]
        exact fun z hz => mem_inf.mpr ⟨hMsH (mem_inf.mp (hR₀ hz)).1, (mem_inf.mp (hR₀ hz)).2⟩
      · rw [← hamb]
        exact hR₀pc
  have hCmap : (centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X)).map
      (MulAut.conj g).toMonoidHom =
      centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X) := by
    rw [map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_centralizer_singleton,
      map_conj_centralizer_singleton, inf_comm, show g * s * g⁻¹ = a by rw [hsdef]; group]
  set T := R₀.map (MulAut.conj g).toMonoidHom with hTdef
  have hTY : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X) := by
    rw [← hCmap]
    exact map_mono hR₀le
  have hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X))) := by
    rw [← hCmap]
    exact isPComponent_map_conj hR₀le hR₀pc g
  have hx'Ca : g * x * g⁻¹ ∈ centralizer ({a} : Set X) := oddGen_le _ hx'o
  obtain ⟨M₁, hM₁Y, hM₁pc, hTM, hTpc'⟩ := pump_location_in hx'Ca hx'o2 hTY hTpc
  by_cases hM₁K : M₁ ≤ UnbalancedLayer.coreActionKernel M
  ·
    have hM₁' : M₁.map (MulAut.conj (g * x * g⁻¹)).toMonoidHom ≤
        centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzC := hM₁Y hz
      have h1 : (MulAut.conj (g * x * g⁻¹)).toMonoidHom z ∈ centralizer ({a} : Set X) :=
        mul_mem (mul_mem hx'Ca hzC) (inv_mem hx'Ca)
      refine mem_inf.mpr ⟨h1, mem_inf.mpr ⟨hCa h1, ?_⟩⟩
      exact UnbalancedLayer.conj_mem_coreActionKernel hx'N (hM₁K hz)
    have hM₁le : M₁ ≤ centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      fun z hz => mem_inf.mpr ⟨hM₁Y hz, mem_inf.mpr ⟨hCa (hM₁Y hz), hM₁K hz⟩⟩
    refine ⟨T, r, hr5, hTM.trans (sup_le hM₁le hM₁'), ?_⟩
    set eT : ↥R₀ ≃* ↥T := R₀.equivMapOfInjective _ (MulAut.conj g).injective with heTdef
    refine ⟨χ₀.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥R₀)).comp
      eT.symm.toMonoidHom), ?_⟩
    intro b
    obtain ⟨q, rfl⟩ := χ₀.surjective b
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨eT z, by simp⟩
  ·
    exfalso
    have hLsurj : ∀ b : alternatingGroup (Fin n), ∃ (z : X) (hz : z ∈ La),
        ρ ⟨z, (hCa.trans hHN) (hLaC hz)⟩ = (b : Perm (Fin n)) := by
      intro b
      obtain ⟨q, hq⟩ := θLa.surjective b
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨l, l.2, ?_⟩
      have h1 := hρ.apply_of_mem (by omega) ⟨l, hLaM l.2⟩
      change ρ ⟨(l : X), le_normalizer (hLaM l.2)⟩ = _
      rw [h1, ← hθLa l l.2 (hLaM l.2)]
      exact congrArg Subtype.val hq
    have hM₁La := hρ.eq_of_isPComponent_of_onto (by omega) (hCa.trans hHN) hLaC hLapc hLsurj
      hM₁Y hM₁pc hM₁K
    subst hM₁La
    have hLmap : M₁.map (MulAut.conj (g * x * g⁻¹)).toMonoidHom = M₁ := by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact (mem_normalizer_iff.mp hx'La z).mp hz
      · intro z hz
        refine ⟨(g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹)⁻¹⁻¹,
          (mem_normalizer_iff.mp (inv_mem hx'La) z).mp hz, ?_⟩
        change g * x * g⁻¹ * ((g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹)⁻¹⁻¹) * (g * x * g⁻¹)⁻¹ = z
        group
    rw [hLmap, sup_idem] at hTM hTpc'
    have hTLY : T ≤ M₁ ⊓ centralizer ({g * x * g⁻¹} : Set X) :=
      fun z hz => mem_inf.mpr ⟨hTM hz, (mem_inf.mp (hTY hz)).2⟩
    exact hρ.not_isPComponent_layer_of_noFix (by omega) hodd (hCa.trans hHN) hLaM θLa hθLa hLaN
      hx'N hx'2 hx'a hx'A hx'5 le_rfl
      (fun z hz => mem_inf.mpr ⟨hLaC (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩) hTM hTLY hTpc'

end Sig36

end CFSG.ComponentClassification.SolMax
