module

public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

private lemma mem_conjugate_iff_cfsg {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    have h1 : (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * (g⁻¹)⁻¹ := rfl
    rw [h1]
    have : g * (g⁻¹ * y * (g⁻¹)⁻¹) * g⁻¹ = y := by group
    rwa [this]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹)
        = g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
    rw [h1]
    group

private lemma mem_map_mk'_iff {X : Type} [Group X] {K U Z : Subgroup G}
    (π : ↥K →* X) (hker : π.ker = Z.subgroupOf K) (hZU : Z ≤ U) (u : ↥K) :
    π u ∈ (U.subgroupOf K).map π ↔ u ∈ U.subgroupOf K := by
  constructor
  · intro hu
    rcases Subgroup.mem_map.mp hu with ⟨s, hs, hsu⟩
    have h1 : u * s⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsu, mul_inv_cancel]
    have hZ : ((u * s⁻¹ : ↥K) : G) ∈ Z := by
      rw [hker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hmul : u = (u * s⁻¹) * s := by group
    rw [hmul]
    exact (U.subgroupOf K).mul_mem (Subgroup.mem_subgroupOf.mpr (hZU hZ)) hs
  · intro hu
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩

private lemma isPGroup_map_index_of_sylow {X : Type} [Group X] {K S Z : Subgroup G}
    (π : ↥K →* X) (hsurj : Function.Surjective π) (hker : π.ker = Z.subgroupOf K)
    (hSK : S ≤ K) (hp : IsPGroup 2 S) (hndvd : ¬ 2 ∣ S.relIndex K) (hZS : Z ≤ S) :
    IsPGroup 2 ((S.subgroupOf K).map π) ∧ ¬ 2 ∣ ((S.subgroupOf K).map π).index := by
  have hS'2 : IsPGroup 2 (S.subgroupOf K) := hp.comap_subtype (K := K)
  refine ⟨hS'2.map π, ?_⟩
  have hker_le : π.ker ≤ S.subgroupOf K := by
    intro x hx
    rw [hker] at hx
    exact Subgroup.mem_subgroupOf.mpr (hZS (Subgroup.mem_subgroupOf.mp hx))
  have hidx : ((S.subgroupOf K).map π).index = (S.subgroupOf K).index :=
    Subgroup.index_map_eq (f := π) (H := S.subgroupOf K) hsurj hker_le
  rw [hidx]
  change ¬ 2 ∣ S.relIndex K
  exact hndvd

private lemma commutator_map_comm {X : Type} [Group X] {K U Z : Subgroup G}
    (π : ↥K →* X) (hker : π.ker = Z.subgroupOf K)
    (hab : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z) :
    ∀ x ∈ (U.subgroupOf K).map π, ∀ y ∈ (U.subgroupOf K).map π, x * y = y * x := by
  intro x hx y hy
  rcases Subgroup.mem_map.mp hx with ⟨w1, hw1, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨w2, hw2, rfl⟩
  have hw1U : (w1 : G) ∈ U := Subgroup.mem_subgroupOf.mp hw1
  have hw2U : (w2 : G) ∈ U := Subgroup.mem_subgroupOf.mp hw2
  have hc := hab _ hw1U _ hw2U
  have hcZ : w1 * w2 * w1⁻¹ * w2⁻¹ ∈ Z.subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr (by simpa using hc)
  have hc1 : π (w1 * w2 * w1⁻¹ * w2⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hcZ
  have hc1' : π w1 * π w2 * (π w1)⁻¹ * (π w2)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using hc1
  calc π w1 * π w2
      = (π w1 * π w2 * (π w1)⁻¹ * (π w2)⁻¹) * (π w2 * π w1) := by group
    _ = 1 * (π w2 * π w1) := by rw [hc1']
    _ = π w2 * π w1 := by rw [one_mul]

private lemma conjugate_map_weaklyClosed {X : Type} [Group X]
    {K S U Z : Subgroup G} (π : ↥K →* X) (hker : π.ker = Z.subgroupOf K)
    (hsurj : Function.Surjective π) (hSK : S ≤ K) (hUK : U ≤ K) (hUS : U ≤ S)
    (hZS : Z ≤ S)
    (hweak : ∀ k ∈ K, CFSG.conjugate U k ≤ S → CFSG.conjugate U k = U) :
    ∀ x : X, CFSG.conjugate ((U.subgroupOf K).map π) x ≤ (S.subgroupOf K).map π →
      CFSG.conjugate ((U.subgroupOf K).map π) x = (U.subgroupOf K).map π := by
  intro x hx
  obtain ⟨h, rfl⟩ := hsurj x
  let U' : Subgroup ↥K := U.subgroupOf K
  have hUS_conj : CFSG.conjugate U (h : G) ≤ S := by
    intro y hy
    rw [mem_conjugate_iff_cfsg] at hy
    have hyK : y ∈ K := by
      have hyU : (h : G) * y * (h : G)⁻¹ ∈ U := hy
      have : y = (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) := by group
      rw [this]
      exact K.mul_mem (K.mul_mem (K.inv_mem h.2) (hUK hyU)) h.2
    let u : ↥K := ⟨y, hyK⟩
    have hmem_conj : π u ∈ CFSG.conjugate (U'.map π) (π h) := by
      rw [mem_conjugate_iff_cfsg]
      have heq : π h * π u * (π h)⁻¹ = π (h * u * h⁻¹) := by
        simp only [map_mul, map_inv]
      rw [heq]
      exact Subgroup.mem_map.mpr ⟨h * u * h⁻¹,
        Subgroup.mem_subgroupOf.mpr (by simpa [u] using hy), rfl⟩
    have huP : π u ∈ (S.subgroupOf K).map π := hx hmem_conj
    have huS : u ∈ S.subgroupOf K := (mem_map_mk'_iff π hker hZS u).mp huP
    simpa [u] using Subgroup.mem_subgroupOf.mp huS
  have hcomp : (MulAut.conj (π h)⁻¹).toMonoidHom.comp π
      = π.comp (MulAut.conj h⁻¹).toMonoidHom := by
    ext v
    simp [MulAut.conj_apply]
  have hconj : CFSG.conjugate (U'.map π) (π h) = (CFSG.conjugate U' h).map π := by
    rw [CFSG.conjugate, CFSG.conjugate]
    change (U'.map π).map (MulAut.conj (π h)⁻¹).toMonoidHom
      = (U'.map (MulAut.conj h⁻¹).toMonoidHom).map π
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hcompK : K.subtype.comp (MulAut.conj h⁻¹).toMonoidHom
      = (MulAut.conj (h : G)⁻¹).toMonoidHom.comp K.subtype := by
    ext v
    simp [MulAut.conj_apply]
  have hconjK : (CFSG.conjugate U' h).map K.subtype = CFSG.conjugate U (h : G) := by
    rw [CFSG.conjugate, CFSG.conjugate, ← Subgroup.map_subgroupOf_eq_of_le hUK]
    rw [Subgroup.map_map, Subgroup.map_map, hcompK]
  have hU'_conj : CFSG.conjugate U' h = U' := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hconjK, hweak (h : G) h.2 hUS_conj, Subgroup.map_subgroupOf_eq_of_le hUK]
  change CFSG.conjugate (U'.map π) (π h) = U'.map π
  rw [hconj, hU'_conj]

variable [Finite G]

theorem y63_burn_modZ {K Q U Z : Subgroup G} (hQ : IsSylowIn 2 K Q) (hUQ : U ≤ Q) (hZU : Z ≤ U)
    (hZK : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ = z) (hcomm : ⁅U, U⁆ ≤ Z)
    (hweak : ∀ k ∈ K, conjSub k U ≤ Q → conjSub k U = U)
    {a g : G} (ha : a ∈ U) (hg : g ∈ K) (hga : g * a * g⁻¹ ∈ U) :
    ∃ n ∈ K, n ∈ normalizer (U : Set G) ∧ ∃ w ∈ Z, n * a * n⁻¹ = g * a * g⁻¹ * w := by
  have hZK_le_K : Z ≤ K := hZU.trans (hUQ.trans hQ.1)
  have hU_le_K : U ≤ K := hUQ.trans hQ.1
  let ZK : Subgroup ↥K := Z.subgroupOf K
  haveI : ZK.Normal :=
    (Subgroup.normal_subgroupOf_iff hZK_le_K).mpr fun z k hz hk => by
      rw [hZK k hk z hz]
      exact hz
  let Γ := ↥K ⧸ ZK
  let π : ↥K →* Γ := QuotientGroup.mk' ZK
  have hker : π.ker = Z.subgroupOf K := QuotientGroup.ker_mk' ZK
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective ZK
  haveI : Finite Γ := Finite.of_surjective π hsurj
  obtain ⟨hQb_pgroup, hQb_ndvd⟩ :=
    isPGroup_map_index_of_sylow π hsurj hker hQ.1 hQ.2.1 hQ.2.2 (hZU.trans hUQ)
  let P : Sylow 2 Γ := hQb_pgroup.toSylow hQb_ndvd
  have hAbarP : (U.subgroupOf K).map π ≤ (P : Subgroup Γ) := by
    change (U.subgroupOf K).map π ≤ (Q.subgroupOf K).map π
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hUQ)
  have hab : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro c hc d hd
    have h := Subgroup.commutator_le.mp hcomm c hc d hd
    simpa [commutatorElement_def] using h
  have hweak_conj : ∀ k ∈ K, CFSG.conjugate U k ≤ Q → CFSG.conjugate U k = U := by
    intro k hk hle
    have hle' : conjSub k⁻¹ U ≤ Q := hle
    have h := hweak k⁻¹ (K.inv_mem hk) hle'
    exact h
  have hweakX := conjugate_map_weaklyClosed π hker hsurj hQ.1 hU_le_K hUQ
    (hZU.trans hUQ) hweak_conj
  have hweak_burn : ∀ x : Γ, CFSG.conjugate ((U.subgroupOf K).map π) x ≤ (P : Subgroup Γ) →
      CFSG.conjugate ((U.subgroupOf K).map π) x = (U.subgroupOf K).map π := by
    intro x hx
    exact hweakX x hx
  let a' : Γ := π ⟨a, hU_le_K ha⟩
  let g' : Γ := π ⟨g, hg⟩
  have ha' : a' ∈ (U.subgroupOf K).map π :=
    Subgroup.mem_map.mpr ⟨⟨a, hU_le_K ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hga' : g' * a' * g'⁻¹ ∈ (U.subgroupOf K).map π := by
    have hmap : π (⟨g, hg⟩ * ⟨a, hU_le_K ha⟩ * ⟨g, hg⟩⁻¹) = g' * a' * g'⁻¹ := by
      simp only [g', a', map_mul, map_inv]
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * ⟨a, hU_le_K ha⟩ * ⟨g, hg⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using hga), rfl⟩
  obtain ⟨n', hn'norm, hn'eq⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion P ((U.subgroupOf K).map π)
      hAbarP (commutator_map_comm π hker hab) hweak_burn ha' hga'
  obtain ⟨n, hn⟩ := hsurj n'
  replace hn : π n = n' := hn
  refine ⟨(n : G), n.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    have forward : ∀ v : ↥K, v ∈ U.subgroupOf K → n * v * n⁻¹ ∈ U.subgroupOf K := by
      intro v hv
      have hvA : π v ∈ (U.subgroupOf K).map π := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
      have hconjA : π (n * v * n⁻¹) ∈ (U.subgroupOf K).map π := by
        have hmap : π (n * v * n⁻¹) = n' * π v * n'⁻¹ := by
          simp only [map_mul, map_inv, hn]
        rw [hmap]
        exact (Subgroup.mem_normalizer_iff.mp hn'norm (π v)).mp hvA
      exact (mem_map_mk'_iff π hker hZU _).mp hconjA
    have forward' : ∀ v : ↥K, v ∈ U.subgroupOf K → n⁻¹ * v * n ∈ U.subgroupOf K := by
      intro v hv
      have hn'inv : (n')⁻¹ ∈ Subgroup.normalizer ((U.subgroupOf K).map π : Set Γ) :=
        (Subgroup.normalizer ((U.subgroupOf K).map π : Set Γ)).inv_mem hn'norm
      have hvA : π v ∈ (U.subgroupOf K).map π := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hn'inv (π v)).mp hvA
      rw [inv_inv] at h2
      have hconjA : π (n⁻¹ * v * n) ∈ (U.subgroupOf K).map π := by
        have hmap : π (n⁻¹ * v * n) = (n')⁻¹ * π v * n' := by
          simp only [map_mul, map_inv, hn]
        rw [hmap]
        exact h2
      exact (mem_map_mk'_iff π hker hZU _).mp hconjA
    intro w
    constructor
    · intro hw
      have h := forward ⟨w, hU_le_K hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
      simpa using Subgroup.mem_subgroupOf.mp h
    · intro hw
      have hwK : w ∈ K := by
        have hwU : (n : G) * w * (n : G)⁻¹ ∈ U := hw
        have : w = (n : G)⁻¹ * ((n : G) * w * (n : G)⁻¹) * (n : G) := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem n.2) (hU_le_K hwU)) n.2
      have hv : n * ⟨w, hwK⟩ * n⁻¹ ∈ U.subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr (by simpa using hw)
      have h := forward' (n * ⟨w, hwK⟩ * n⁻¹) hv
      have heq : n⁻¹ * (n * ⟨w, hwK⟩ * n⁻¹) * n = ⟨w, hwK⟩ := by
        apply Subtype.ext
        show (n : G)⁻¹ * ((n : G) * w * (n : G)⁻¹) * (n : G) = w
        group
      rw [heq] at h
      exact Subgroup.mem_subgroupOf.mp h
  · let u1 : ↥K := n * ⟨a, hU_le_K ha⟩ * n⁻¹
    let u2 : ↥K := ⟨g, hg⟩ * ⟨a, hU_le_K ha⟩ * ⟨g, hg⟩⁻¹
    have hpi_eq : π u1 = π u2 := by
      have h1 : π u1 = n' * a' * n'⁻¹ := by
        simp only [u1, a', map_mul, map_inv, hn]
      have h2 : π u2 = g' * a' * g'⁻¹ := by
        simp only [u2, a', g', map_mul, map_inv]
      rw [h1, hn'eq, h2]
    have hZ : u2⁻¹ * u1 ∈ ZK := by
      change u2⁻¹ * u1 ∈ Z.subgroupOf K
      rw [← hker, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hpi_eq, inv_mul_cancel]
    refine ⟨((u2⁻¹ * u1 : ↥K) : G), Subgroup.mem_subgroupOf.mp hZ, ?_⟩
    have hcoe : ((u1 : ↥K) : G) = ((u2 : ↥K) : G) * ((u2⁻¹ * u1 : ↥K) : G) := by
      dsimp only [u1, u2]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact hcoe

end CFSG.OddStandard.HigherRank.YamadaG23
