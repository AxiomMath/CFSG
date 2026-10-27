module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.CorePacketDerivedSupportCentralizer
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
import CFSG.FeitThompson.OddOrder.SigmaSylowTransporterFusion
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep05

universe u

variable {G : Type*} [Group G]

theorem map_toMonoidHom_conj (Y : Subgroup G) (g : G) :
    Y.map (MulAut.conj g).toMonoidHom = Y.map (MulAut.conj g : G →* G) := (rfl)

theorem centralizerIn_map_conj (X Y : Subgroup G) (g : G) :
    (centralizerIn X Y).map (MulAut.conj g : G →* G)
      = centralizerIn (X.map (MulAut.conj g : G →* G)) (Y.map (MulAut.conj g : G →* G)) := by
  rw [centralizerIn_eq, centralizerIn_eq, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    map_centralizer_eq_centralizer_image]
  rfl

theorem sigmaPrimes_map_conj [Finite G] (M : Subgroup G) (g : G) :
    sigmaPrimes (M.map (MulAut.conj g : G →* G)) = sigmaPrimes M := by
  rw [← coe_conj_smul_eq_map]
  exact CFSG.FeitThompson.sigmaPrimes_conj_smul M g

theorem kappaPrimes_map_conj_subset [Finite G] (M : Subgroup G) (g : G) :
    kappaPrimes M ⊆ kappaPrimes (M.map (MulAut.conj g : G →* G)) := by
  intro p hp
  have hprime := prime_of_mem_kappaPrimes hp
  rw [mem_kappaPrimes_iff_exists_subgroup hprime] at hp ⊢
  obtain ⟨hdvd, hσ, P, hPM, hPcard, hPcyc, x, hxP, hx1, hxne⟩ := hp
  have hinj : Function.Injective (MulAut.conj g : G →* G) := (MulAut.conj g).injective
  have hcard : Nat.card ↥(M.map (MulAut.conj g : G →* G)) = Nat.card ↥M :=
    Subgroup.card_map_of_injective hinj
  refine ⟨by rw [hcard]; exact hdvd, by rw [sigmaPrimes_map_conj]; exact hσ,
    P.map (MulAut.conj g : G →* G), Subgroup.map_mono hPM, ?_,
    (isCyclic_map_conj_iff P g).2 hPcyc, MulAut.conj g x,
    Subgroup.mem_map_of_mem _ hxP, by simpa using hx1, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hPcard, hcard]
  · have hkey : (sigmaCore M ⊓ centralizer ({x} : Set G)).map (MulAut.conj g : G →* G)
        = sigmaCore (M.map (MulAut.conj g : G →* G)) ⊓
          centralizer ({MulAut.conj g x} : Set G) := by
      rw [Subgroup.map_inf _ _ _ hinj, sigmaCore_map_conj, map_centralizer_eq_centralizer_image]
      simp
    rw [← hkey]
    exact fun hc => hxne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hc)

theorem kappaPrimes_map_conj [Finite G] (M : Subgroup G) (g : G) :
    kappaPrimes (M.map (MulAut.conj g : G →* G)) = kappaPrimes M := by
  refine le_antisymm ?_ (kappaPrimes_map_conj_subset M g)
  intro p hp
  have := kappaPrimes_map_conj_subset (M.map (MulAut.conj g : G →* G)) g⁻¹ hp
  rwa [map_conj_map_conj, inv_mul_cancel, map_conj_eq_self (Subgroup.one_mem M)] at this

theorem fixedSet_map_conj {Y X : Subgroup G} {a : G} (ha : a ∈ fixedSet Y X) (g : G) :
    MulAut.conj g a ∈
      fixedSet (Y.map (MulAut.conj g : G →* G)) (X.map (MulAut.conj g : G →* G)) := by
  obtain ⟨haY, ha1, hane⟩ := ha
  refine ⟨Subgroup.mem_map_of_mem _ haY, by simpa using ha1, ?_⟩
  have key := centralizerIn_map_conj X (zpowers a) g
  rw [MonoidHom.map_zpowers] at key
  exact fun hc => hane ((Subgroup.map_eq_bot_iff_of_injective _
    (MulAut.conj g).injective).1 (key.trans hc))

theorem FPF_kappa_positive_core_derived_support_disjoint
    (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₄ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₅ : Statements.FTS_core_centralizing_external_element_dichotomy.{u})
    (h₆ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₇ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FPF_kappa_positive_core_derived_support_disjoint.{u} := by
  intro G _ _ hG M N hM hN hconj hkM hkN
  have hamb7 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  rw [Set.disjoint_left]
  rintro z hz hzN
  simp only [Set.mem_iUnion, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
    conjClosure, mem_conjSet, mem_leftCosetSet] at hz hzN
  obtain ⟨x, ⟨hxS, hx1⟩, g, y, ⟨r, hr, hxr⟩, hzr⟩ := hz
  obtain ⟨h, a, ha, hza⟩ := hzN
  set c : G := g * h⁻¹ with hc
  have hconjeq : MulAut.conj c a = x * r := by
    have hgh : g⁻¹ * (x * r) * g = h⁻¹ * a * h := by rw [hxr, hzr, hza]
    rw [MulAut.conj_apply, hc]
    calc g * h⁻¹ * a * (g * h⁻¹)⁻¹ = g * (h⁻¹ * a * h) * g⁻¹ := by group
      _ = g * (g⁻¹ * (x * r) * g) * g⁻¹ := by rw [hgh]
      _ = x * r := by group
  have hN₀coatom : IsCoatom (N.map (MulAut.conj c : G →* G)) := by
    have := isCoatom_map_conj hN c
    rwa [map_toMonoidHom_conj] at this
  have hkN₀ : (kappaPrimes (N.map (MulAut.conj c : G →* G))).Nonempty := by
    rw [kappaPrimes_map_conj]; exact hkN
  have hconj₀ : ¬ IsConjugateSubgroup M (N.map (MulAut.conj c : G →* G)) := by
    rintro ⟨b, hb⟩
    rw [map_toMonoidHom_conj] at hb
    refine hconj ⟨c⁻¹ * b, ?_⟩
    rw [map_toMonoidHom_conj, ← map_conj_map_conj, ← hb, map_conj_map_conj, inv_mul_cancel,
      map_conj_eq_self (Subgroup.one_mem N)]
  have hmem : x * r ∈ fixedSet
      (⁅N.map (MulAut.conj c : G →* G), N.map (MulAut.conj c : G →* G)⁆ : Subgroup G)
      (sigmaCore (N.map (MulAut.conj c : G →* G))) := by
    rw [sigmaCore_map_conj, ← Subgroup.map_commutator, ← hconjeq]
    exact fixedSet_map_conj ha c
  obtain ⟨-, -, -, huniq, hnotle⟩ :=
    FPF_core_packet_derived_support_centralizer h₁ h₂ h₃ h₄ h₅ h₇ G hG M
      (N.map (MulAut.conj c : G →* G)) hM hN₀coatom hconj₀ hkM hkN₀ x hxS hx1 r hr hmem
  have hkempty := (h₆ G hamb7 M hM (N.map (MulAut.conj c : G →* G)) hN₀coatom x hxS hx1
    hnotle huniq.le hkN₀).1
  exact absurd hkempty (Set.nonempty_iff_ne_empty.1 hkM)

end

end CFSG.FeitThompson.Proofs
