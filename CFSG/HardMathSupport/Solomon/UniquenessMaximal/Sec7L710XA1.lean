module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.KCoreOpen
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.SignalizerFunctor.Helpers

theorem isKGroup_of_surjective {H X : Type*} [Group H] [Group X] (f : H →* X)
    (hf : Function.Surjective f) (hH : CFSG.Open.IsKGroup H) : CFSG.Open.IsKGroup X :=
  hH.of_surjective f hf

theorem le_pCore_of_normal {p : ℕ} {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hp : IsPGroup p ↥N) : N ≤ CFSG.Open.pCore p X :=
  le_sSup ⟨hN, hp⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_sylow_containing_of_pGroup {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {A K T : Subgroup G} (hA : IsPGroup p ↥A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcop : ¬ p ∣ Nat.card K) (hTK : T ≤ K) (hT : IsPGroup q ↥T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    ∃ Q : Subgroup G, T ≤ Q ∧ Q ≤ K ∧ IsPGroup q ↥Q ∧
      ¬ q ∣ Q.relIndex K ∧ A ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  let _action := conjugationAction A K hAK
  obtain ⟨Q, hTQ, hQInv⟩ := invariant_sylow_containing p q hp hq hA
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop) (T.subgroupOf K) (hT.comap_subtype)
    (by
      intro a z hz
      exact Subgroup.le_normalizer_iff.mp hAT a a.2 z.1 hz)
  refine ⟨(Q : Subgroup K).map K.subtype, ?_, Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := K.subtype) hTQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hTK] at h
  · have : ((Q : Subgroup K).map K.subtype).relIndex K = (Q : Subgroup K).index := by
      unfold Subgroup.relIndex Subgroup.subgroupOf
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [this]
    exact Q.not_dvd_index
  · apply invariant_subgroup_map_normalized A K hAK (Q : Subgroup K)
    change ∀ a : A, ∀ z ∈ (Q : Subgroup K), a • z ∈ (Q : Subgroup K)
    intro a z hz
    have himage := Subgroup.smul_mem_pointwise_smul z a (Q : Subgroup K) hz
    rw [← Sylow.pointwise_smul_def, hQInv] at himage
    exact himage

omit [Finite G] in
theorem le_sup_of_relIndex {M : Type*} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (U : Subgroup (M ⧸ N)) (hU : IsPGroup 2 ↥U) (T : Subgroup M)
    (hodd : ¬ 2 ∣ T.relIndex (U.comap (QuotientGroup.mk' N))) :
    U.comap (QuotientGroup.mk' N) ≤ T ⊔ N := by
  set q := QuotientGroup.mk' N with hq
  set K := U.comap q with hK
  have hker : q.ker = N := QuotientGroup.ker_mk' N
  have hcomap : ((T ⊔ N).map q).comap q = T ⊔ N := by
    rw [Subgroup.comap_map_eq, hker]
    exact sup_eq_left.2 le_sup_right
  have hmapK : K.map q = U := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective N) U
  have h1 : (T ⊔ N).relIndex K = ((T ⊔ N).map q).relIndex U := by
    rw [← hmapK, ← Subgroup.relIndex_comap, hcomap]
  have h2 : ((T ⊔ N).map q).relIndex U ∣ Nat.card U := Subgroup.relIndex_dvd_card _ _
  have h3 : (T ⊔ N).relIndex K ∣ T.relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_left
  obtain ⟨b, hb⟩ := hU.exists_card_eq
  have h4 : (T ⊔ N).relIndex K ∣ 2 ^ b := hb ▸ h1 ▸ h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  have hi0 : i = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans (hi ▸ h3))
  rw [hi0, pow_zero] at hi
  exact Subgroup.relIndex_eq_one.1 hi

theorem le_of_normalizes_sylow {S P U : Subgroup G} (hS : IsPGroup 2 ↥S) (hSP : S ≤ P)
    (hodd : ¬ 2 ∣ S.relIndex P) (hUP : U ≤ P) (hU : IsPGroup 2 ↥U)
    (hN : U ≤ Subgroup.normalizer (S : Set G)) : U ≤ S := by
  have hprod := Lemma85Aux.card_sup_mul_card_inf' hN
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  obtain ⟨b, hb⟩ := hU.exists_card_eq
  have hMP : U ⊔ S ≤ P := sup_le hUP hSP
  have hdvd : Nat.card (U ⊔ S : Subgroup G) ∣ 2 ^ (b + a) := by
    refine Dvd.intro (Nat.card (U ⊓ S : Subgroup G)) ?_
    rw [hprod, hb, ha, pow_add]
  have h1 : S.relIndex (U ⊔ S) ∣ 2 ^ (b + a) :=
    (Subgroup.relIndex_dvd_card _ _).trans hdvd
  have h2 : S.relIndex (U ⊔ S) ∣ S.relIndex P := by
    rw [← Subgroup.relIndex_mul_relIndex S (U ⊔ S) P le_sup_right hMP]
    exact Dvd.intro _ rfl
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hi0 : i = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans (hi ▸ h2))
  rw [hi0, pow_zero] at hi
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 hi)

theorem eq_one_of_mem_two_of_mem_odd {S Z : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hZ : ¬ 2 ∣ Nat.card Z) {x : G} (hxS : x ∈ S) (hxZ : x ∈ Z) : x = 1 := by
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) (Nat.card Z) := by
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hZ)
  have hd := Subgroup.disjoint_of_coprime_natCard hcop
  have := hd.le_bot ⟨hxS, hxZ⟩
  exact (Subgroup.mem_bot).1 this

theorem exists_pow_two_mem_primeCore {C : Subgroup G}
    (hcent : ∀ Q : Subgroup G, Q ≤ C → IsPGroup 2 ↥Q → ∀ c ∈ C, ∀ q ∈ Q, q * c = c * q)
    {c : G} (hc : c ∈ C) : ∃ n : ℕ, c ^ (2 ^ n) ∈ GLAPPrimeCoreOf 2 C := by
  classical
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hQ : Subgroup.normalizer (Q : Set ↥C) ≤ Subgroup.centralizer (Q : Set ↥C) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hcent ((Q : Subgroup ↥C).map C.subtype) (Subgroup.map_subtype_le _)
      (Q.isPGroup'.map _) n.1 n.2 h.1 ⟨h, hh, rfl⟩
    exact Subtype.ext h1
  obtain ⟨K, hKn, hK2, hKindex, -⟩ := CFSG.GroupTheory.burnside_normal_complement Q hQ
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  refine ⟨n, ?_⟩
  have hKle : K.map C.subtype ≤ GLAPPrimeCoreOf 2 C := by
    refine Subgroup.map_mono (le_sSup ⟨hKn, ?_⟩)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hK2
  have hpow : ((⟨c, hc⟩ : C) : C ⧸ K) ^ (2 ^ n) = 1 := by
    have h1 : ((⟨c, hc⟩ : C) : C ⧸ K) ^ Nat.card (C ⧸ K) = 1 := pow_card_eq_one'
    have h2 : Nat.card (C ⧸ K) = 2 ^ n := by
      rw [← Subgroup.index, hKindex]
      exact hn
    rwa [h2] at h1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
  exact hKle ⟨_, hpow, rfl⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
