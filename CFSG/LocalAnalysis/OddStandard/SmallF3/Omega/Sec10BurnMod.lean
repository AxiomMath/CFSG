module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma mem_map_mk'_iff {G X : Type} [Group G] [Group X] {H U : Subgroup G}
    (π : ↥H →* X) {z : G} (hker : π.ker = (zpowers z).subgroupOf H)
    (hUH : U ≤ H) (hzU : z ∈ U) (u : ↥H) :
    π u ∈ (U.subgroupOf H).map π ↔ u ∈ U.subgroupOf H := by
  constructor
  · intro hu
    rcases Subgroup.mem_map.mp hu with ⟨s, hs, hsu⟩
    have h1 : u * s⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsu, mul_inv_cancel]
    have hzpow : ((u * s⁻¹ : ↥H) : G) ∈ zpowers z := by
      rw [hker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hU : ((u * s⁻¹ : ↥H) : G) ∈ U := (Subgroup.zpowers_le.mpr hzU) hzpow
    have : u = (u * s⁻¹) * s := by group
    rw [this]
    exact (U.subgroupOf H).mul_mem (Subgroup.mem_subgroupOf.mpr hU) hs
  · intro hu
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩

private lemma isPGroup_map_of_sylow {G X : Type} [Group G] [Group X] {H S : Subgroup G}
    (π : ↥H →* X) (hsurj : Function.Surjective π) {z : G} (hker : π.ker = (zpowers z).subgroupOf H)
    (hSH : S ≤ H) (hp : IsPGroup 2 S) (hndvd : ¬ 2 ∣ S.relIndex H) (hzS : z ∈ S) :
    IsPGroup 2 ((S.subgroupOf H).map π) ∧ ¬ 2 ∣ ((S.subgroupOf H).map π).index := by
  have hS'2 : IsPGroup 2 (S.subgroupOf H) := hp.comap_subtype (K := H)
  refine ⟨hS'2.map π, ?_⟩
  have hker_le : π.ker ≤ S.subgroupOf H := by
    intro x hx
    have hxZ : (x : G) ∈ zpowers z := by
      rw [hker] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.zpowers_le.mpr hzS) hxZ)
  have hidx : ((S.subgroupOf H).map π).index = (S.subgroupOf H).index :=
    Subgroup.index_map_eq (f := π) (H := S.subgroupOf H) hsurj hker_le
  rw [hidx]
  change ¬ 2 ∣ S.relIndex H
  exact hndvd

private lemma commutator_map_comm {G X : Type} [Group G] [Group X] {H W : Subgroup G}
    (π : ↥H →* X) {z : G} (hker : π.ker = (zpowers z).subgroupOf H)
    (hWH : W ≤ H) (hzW : z ∈ W)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) :
    ∀ x ∈ (W.subgroupOf H).map π, ∀ y ∈ (W.subgroupOf H).map π, x * y = y * x := by
  intro x hx y hy
  rcases Subgroup.mem_map.mp hx with ⟨w1, hw1, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨w2, hw2, rfl⟩
  have hw1W : (w1 : G) ∈ W := Subgroup.mem_subgroupOf.mp hw1
  have hw2W : (w2 : G) ∈ W := Subgroup.mem_subgroupOf.mp hw2
  have hc := hab _ hw1W _ hw2W
  have hcZ : w1 * w2 * w1⁻¹ * w2⁻¹ ∈ (zpowers z).subgroupOf H :=
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

private lemma conjugate_map_weaklyClosed {G X : Type} [Group G] [Group X]
    {H S W : Subgroup G} (π : ↥H →* X) {z : G}
    (hker : π.ker = (zpowers z).subgroupOf H) (hsurj : Function.Surjective π)
    (hSH : S ≤ H) (hWH : W ≤ H) (hWS : W ≤ S) (hzS : z ∈ S) (hzW : z ∈ W)
    (hweak : ∀ h ∈ H, CFSG.conjugate W h ≤ S → CFSG.conjugate W h = W) :
    ∀ x : X, CFSG.conjugate ((W.subgroupOf H).map π) x ≤ (S.subgroupOf H).map π →
      CFSG.conjugate ((W.subgroupOf H).map π) x = (W.subgroupOf H).map π := by
  intro x hx
  obtain ⟨h, rfl⟩ := hsurj x
  let W' : Subgroup ↥H := W.subgroupOf H
  have hWS_conj : CFSG.conjugate W (h : G) ≤ S := by
    intro y hy
    rw [mem_conjugate_iff'] at hy
    have hyH : y ∈ H := by
      have hyW : (h : G) * y * (h : G)⁻¹ ∈ W := hy
      have : y = (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem h.2) (hWH hyW)) h.2
    let u : ↥H := ⟨y, hyH⟩
    have hmem_conj : π u ∈ CFSG.conjugate (W'.map π) (π h) := by
      rw [mem_conjugate_iff']
      have heq : π h * π u * (π h)⁻¹ = π (h * u * h⁻¹) := by
        simp only [map_mul, map_inv]
      rw [heq]
      exact Subgroup.mem_map.mpr ⟨h * u * h⁻¹,
        Subgroup.mem_subgroupOf.mpr (by simpa [u] using hy), rfl⟩
    have huP : π u ∈ (S.subgroupOf H).map π := hx hmem_conj
    have huS : u ∈ S.subgroupOf H := (mem_map_mk'_iff π hker hSH hzS u).mp huP
    simpa [u] using Subgroup.mem_subgroupOf.mp huS
  have hcomp : (MulAut.conj (π h)⁻¹).toMonoidHom.comp π
      = π.comp (MulAut.conj h⁻¹).toMonoidHom := by
    ext v
    simp [MulAut.conj_apply]
  have hconj : CFSG.conjugate (W'.map π) (π h) = (CFSG.conjugate W' h).map π := by
    rw [CFSG.conjugate, CFSG.conjugate]
    change (W'.map π).map (MulAut.conj (π h)⁻¹).toMonoidHom
      = (W'.map (MulAut.conj h⁻¹).toMonoidHom).map π
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hcompH : H.subtype.comp (MulAut.conj h⁻¹).toMonoidHom
      = (MulAut.conj (h : G)⁻¹).toMonoidHom.comp H.subtype := by
    ext v
    simp [MulAut.conj_apply]
  have hconjH : (CFSG.conjugate W' h).map H.subtype = CFSG.conjugate W (h : G) := by
    rw [CFSG.conjugate, CFSG.conjugate, ← Subgroup.map_subgroupOf_eq_of_le hWH]
    rw [Subgroup.map_map, Subgroup.map_map, hcompH]
  have hW'_conj : CFSG.conjugate W' h = W' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hconjH, hweak (h : G) h.2 hWS_conj, Subgroup.map_subgroupOf_eq_of_le hWH]
  change CFSG.conjugate (W'.map π) (π h) = W'.map π
  rw [hconj, hW'_conj]

theorem sec10_burnside_mod [Finite G] {H S W : Subgroup G} {z : G}
    (hS : IsSylow2Of S H) (hzS : z ∈ S) (hzH : ∀ h ∈ H, h * z = z * h)
    (hWS : W ≤ S) (hzW : z ∈ W)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ zpowers z)
    (hweak : ∀ h ∈ H, CFSG.conjugate W h ≤ S → CFSG.conjugate W h = W)
    {a g : G} (ha : a ∈ W) (hg : g ∈ H) (hga : g * a * g⁻¹ ∈ W) :
    ∃ n ∈ H ⊓ normalizer (W : Set G), ∃ ε ∈ zpowers z, g * a * g⁻¹ = n * a * n⁻¹ * ε := by
  have hSH : S ≤ H := hS.1
  have hWH : W ≤ H := fun x hx => hSH (hWS hx)
  let Z : Subgroup ↥H := (zpowers z).subgroupOf H
  have hZle_center : Z ≤ Subgroup.center ↥H := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    show (u : G) * (y : G) = (y : G) * (u : G)
    have hyz : (y : G) ∈ zpowers z := Subgroup.mem_subgroupOf.mp hy
    have hzc : z ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzH (u : G) u.2).symm
    have hyc : (y : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) :=
      (Subgroup.zpowers_le.mpr hzc) hyz
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
  haveI : Z.Normal := Subgroup.normal_of_le_center hZle_center
  let X := ↥H ⧸ Z
  let π : ↥H →* X := QuotientGroup.mk' Z
  haveI : Finite X := Finite.of_surjective π (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = (zpowers z).subgroupOf H := QuotientGroup.ker_mk' Z
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hW'S' : W.subgroupOf H ≤ S.subgroupOf H := Subgroup.subgroupOf_mono H hWS
  obtain ⟨hP2, hPndvd⟩ := isPGroup_map_of_sylow π hsurj hker hSH hS.2.1 hS.2.2 hzS
  let P : Sylow 2 X := hP2.toSylow hPndvd
  have hAbarP : (W.subgroupOf H).map π ≤ (P : Subgroup X) := by
    change (W.subgroupOf H).map π ≤ (S.subgroupOf H).map π
    exact Subgroup.map_mono hW'S'
  have hAbar_comm := commutator_map_comm π hker hWH hzW hab
  have hweak_X := conjugate_map_weaklyClosed π hker hsurj hSH hWH hWS hzS hzW hweak
  let a' : X := π ⟨a, hWH ha⟩
  let g' : X := π ⟨g, hg⟩
  have ha' : a' ∈ (W.subgroupOf H).map π :=
    Subgroup.mem_map.mpr ⟨⟨a, hWH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hga' : g' * a' * g'⁻¹ ∈ (W.subgroupOf H).map π := by
    have hmap : π (⟨g, hg⟩ * ⟨a, hWH ha⟩ * ⟨g, hg⟩⁻¹) = g' * a' * g'⁻¹ := by
      simp only [g', a', map_mul, map_inv]
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * ⟨a, hWH ha⟩ * ⟨g, hg⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using hga), rfl⟩
  obtain ⟨n', hn'norm, hn'eq⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion P ((W.subgroupOf H).map π)
      hAbarP hAbar_comm hweak_X ha' hga'
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective Z n'
  replace hn : π n = n' := hn
  refine ⟨(n : G), ?_, ?_⟩
  · rw [Subgroup.mem_inf]
    refine ⟨n.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    have forward : ∀ v : ↥H, v ∈ W.subgroupOf H → n * v * n⁻¹ ∈ W.subgroupOf H := by
      intro v hv
      have hvA : π v ∈ (W.subgroupOf H).map π := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
      have hconjA : π (n * v * n⁻¹) ∈ (W.subgroupOf H).map π := by
        have hmap : π (n * v * n⁻¹) = n' * π v * n'⁻¹ := by
          simp only [map_mul, map_inv, hn]
        rw [hmap]
        exact (Subgroup.mem_normalizer_iff.mp hn'norm (π v)).mp hvA
      exact (mem_map_mk'_iff π hker hWH hzW _).mp hconjA
    have forward' : ∀ v : ↥H, v ∈ W.subgroupOf H → n⁻¹ * v * n ∈ W.subgroupOf H := by
      intro v hv
      have hn'inv : (n')⁻¹ ∈ Subgroup.normalizer ((W.subgroupOf H).map π : Set X) :=
        (Subgroup.normalizer ((W.subgroupOf H).map π : Set X)).inv_mem hn'norm
      have hvA : π v ∈ (W.subgroupOf H).map π := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hn'inv (π v)).mp hvA
      rw [inv_inv] at h2
      have hconjA : π (n⁻¹ * v * n) ∈ (W.subgroupOf H).map π := by
        have hmap : π (n⁻¹ * v * n) = (n')⁻¹ * π v * n' := by
          simp only [map_mul, map_inv, hn]
        rw [hmap]; exact h2
      exact (mem_map_mk'_iff π hker hWH hzW _).mp hconjA
    intro w
    constructor
    · intro hw
      have h := forward ⟨w, hWH hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
      simpa using Subgroup.mem_subgroupOf.mp h
    · intro hw
      have hwH : w ∈ H := by
        have hwW : (n : G) * w * (n : G)⁻¹ ∈ W := hw
        have : w = (n : G)⁻¹ * ((n : G) * w * (n : G)⁻¹) * (n : G) := by group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem n.2) (hWH hwW)) n.2
      have hv : n * ⟨w, hwH⟩ * n⁻¹ ∈ W.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr (by simpa using hw)
      have h := forward' (n * ⟨w, hwH⟩ * n⁻¹) hv
      have heq : n⁻¹ * (n * ⟨w, hwH⟩ * n⁻¹) * n = ⟨w, hwH⟩ := by
        apply Subtype.ext
        show (n : G)⁻¹ * ((n : G) * w * (n : G)⁻¹) * (n : G) = w
        group
      rw [heq] at h
      exact Subgroup.mem_subgroupOf.mp h
  · let u1 : ↥H := n * ⟨a, hWH ha⟩ * n⁻¹
    let u2 : ↥H := ⟨g, hg⟩ * ⟨a, hWH ha⟩ * ⟨g, hg⟩⁻¹
    have hpi_eq : π u1 = π u2 := by
      have h1 : π u1 = n' * a' * n'⁻¹ := by
        simp only [u1, a', map_mul, map_inv, hn]
      have h2 : π u2 = g' * a' * g'⁻¹ := by
        simp only [u2, a', g', map_mul, map_inv]
      rw [h1, hn'eq, h2]
    have hZ : u1⁻¹ * u2 ∈ Z := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show π (u1⁻¹ * u2) = 1
      rw [map_mul, map_inv, hpi_eq, inv_mul_cancel]
    refine ⟨((u1⁻¹ * u2 : ↥H) : G), Subgroup.mem_subgroupOf.mp hZ, ?_⟩
    have hcoe : ((u2 : ↥H) : G) = ((u1 : ↥H) : G) * ((u1⁻¹ * u2 : ↥H) : G) := by
      dsimp only [u1, u2]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact hcoe

end CFSG.OddStandard.SmallF3.Omega
