module

public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

theorem normalizer_zpowers_eq_centralizer_of_orderOf_eq_two {X : Type*} [Group X] {x : X}
    (hx : orderOf x = 2) : normalizer (zpowers x : Set X) = centralizer ({x} : Set X) := by
  ext g
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 hg x).1 (mem_zpowers x))
    rw [← zpow_mod_orderOf, hx] at hk
    rcases Int.emod_two_eq k with h0 | h1
    · exfalso
      rw [Nat.cast_ofNat, h0, zpow_zero] at hk
      have h1 : x = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) hk
        simpa [mul_assoc] using this.symm
      rw [h1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · rw [Nat.cast_ofNat, h1, zpow_one] at hk
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [← hk]
  · intro hg
    have hc : ∀ n : ℤ, g * x ^ n * g⁻¹ = x ^ n := fun n => by
      rw [(Commute.zpow_right (show Commute g x from hg) n).eq, mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_zpowers_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hc n).symm⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h' : g * h * g⁻¹ = g * x ^ n * g⁻¹ := by rw [hc n, hn]
      simpa using h'.symm

theorem orderOf_mk_eq_two_of_odd {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {z : G} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk' N z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]) fun h1 => ?_
  have hzN : z ∈ N := (QuotientGroup.eq_one_iff z).1 h1
  have hdvd := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 hdvd)

theorem kProper_solvable_odd_quotient_ordinary_local_image_enters_two_layer
    {C : CFSG.Assembly.GroupProp} (hS : SchreierFor C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLz : L ≤ centralizer ({z} : Set G))
    (hLp : Group.IsPerfect L)
    (hLc : CFSG.Assembly.IsComponentOf (L.map (QuotientGroup.mk' N))
      (centralizer ({QuotientGroup.mk' N z} : Set (G ⧸ N)))) :
    L ≤ CFSG.pLayer G 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.pPrimeCore 2 G with hRdef
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hRsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
  have hNR : N ≤ R := le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hNodd⟩
  set πR := QuotientGroup.mk' R with hπR
  set t := πR z with ht_def
  have ht : orderOf t = 2 := orderOf_mk_eq_two_of_odd R hRodd hz
  let f : G ⧸ N →* G ⧸ R := QuotientGroup.map N R (MonoidHom.id G) (by simpa using hNR)
  have hf : ∀ g : G, f (QuotientGroup.mk' N g) = πR g := fun g => rfl
  have hfcomp : f.comp (QuotientGroup.mk' N) = πR := MonoidHom.ext hf
  have hCR : (centralizer ({z} : Set G)).map πR = centralizer ({t} : Set (G ⧸ R)) := by
    have h := CFSG.GroupTheory.normal_coprime_quotient_normalizer 2 R
      (fun h2 => (Nat.not_even_iff_odd.2 hRodd) (even_iff_two_dvd.2 h2)) (zpowers z)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]))
    rwa [normalizer_zpowers_eq_centralizer_of_orderOf_eq_two hz, MonoidHom.map_zpowers,
      normalizer_zpowers_eq_centralizer_of_orderOf_eq_two ht] at h
  have hCmap : (centralizer ({QuotientGroup.mk' N z} : Set (G ⧸ N))).map f =
      centralizer ({t} : Set (G ⧸ R)) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.1 hy
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [ht_def, ← hf, ← map_mul, ← map_mul, hy']
    · rw [← hCR, ← hfcomp, ← Subgroup.map_map]
      refine Subgroup.map_mono ?_
      rintro _ ⟨g, hg, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul, hg']
  have hJmap : (L.map (QuotientGroup.mk' N)).map f = L.map πR := by
    rw [Subgroup.map_map, hfcomp]
  have hJsub : CFSG.Assembly.IsSubnormal (L.map πR) (centralizer ({t} : Set (G ⧸ R))) := by
    have := assembly_isSubnormal_map f hLc.2.1
    rwa [hJmap, hCmap] at this
  have hJne : L.map πR ≠ ⊥ := by
    intro hbot
    have hLR : L ≤ R := by
      rw [← QuotientGroup.ker_mk' R, ← Subgroup.map_eq_bot_iff]
      exact hbot
    have : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hLR)
    have hLbot : L = ⊥ := by
      by_contra hne
      have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      exact Group.IsPerfect.not_isSolvable L ‹_›
    have hq := (AssemblyBPredicates.isQuasisimple_iff_native _).1 hLc.2.2
    rw [hLbot, Subgroup.map_bot] at hq
    obtain ⟨-, hsimple, -⟩ := hq
    have : Subsingleton (⊥ : Subgroup (G ⧸ N)) := inferInstance
    exact hsimple.toNontrivial.exists_pair_ne.elim fun a ha => by
      obtain ⟨b, hb⟩ := ha
      exact hb (Subsingleton.elim _ _)
  have hJq : CFSG.Assembly.IsQuasisimple (L.map πR) := by
    have hq := (AssemblyBPredicates.isQuasisimple_iff_native _).1 hLc.2.2
    rcases quasisimple_homomorphic_images hq (f.comp (L.map (QuotientGroup.mk' N)).subtype) with
      h | h
    · exfalso
      apply hJne
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hJmap] at h
      exact h
    · rw [MonoidHom.range_comp, Subgroup.range_subtype, hJmap] at h
      exact (AssemblyBPredicates.isQuasisimple_iff_native _).2 h
  have hJle : L.map πR ≤ centralizer ({t} : Set (G ⧸ R)) := by
    rw [← hCR]
    exact Subgroup.map_mono hLz
  have hJ : CFSG.Assembly.IsComponentOf (L.map πR) (centralizer ({t} : Set (G ⧸ R))) :=
    ⟨hJle, hJsub, hJq⟩
  have hcore : CFSG.pPrimeCore 2 (G ⧸ R) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hJE : L.map πR ≤ CFSG.layer (G ⧸ R) := by
    by_cases hE : CFSG.layer (G ⧸ R) = ⊤
    · rw [hE]
      exact le_top
    have hout : ∀ K : Subgroup (G ⧸ R), CFSG.IsComponent K →
        Group.IsSolvable (Outer (K ⧸ center K)) := by
      intro K hKc
      have hKtop : K ≠ ⊤ := fun h => hE (eq_top_iff.2 (h ▸ le_sSup hKc))
      have hpre : K.comap πR ≠ ⊤ := by
        intro h
        apply hKtop
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) K, h,
          ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective R)]
      obtain ⟨-, hsimple, hnab⟩ := hKc.1
      let ρ : K.comap πR →* K := (πR.comp (K.comap πR).subtype).codRestrict K fun x => x.2
      have hρ : Function.Surjective ρ := by
        rintro ⟨y, hy⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R y
        exact ⟨⟨g, hy⟩, rfl⟩
      exact outer_solvable_of_kProper_image hS hK hpre hnab
        ((QuotientGroup.mk' (center K)).comp ρ) ((QuotientGroup.mk'_surjective _).comp hρ)
    have h := odd_core_free_Schreier_involution_component_enters_layer hcore ht hout
      ((L.map πR).subgroupOf (centralizer ({t} : Set (G ⧸ R))))
      ((isComponentOf_iff_isComponent_subgroupOf hJle).1 hJ)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJle] at h
  exact CatalogueBPrimeJoin.solvable_prime_complement_core_perfect_layer_lift hRsolv hLp hJE

end CFSG.LocalAnalysis.ComponentInitial
