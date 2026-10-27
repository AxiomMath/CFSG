module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH0

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {z : G} {K : Fin 4 → Subgroup G}

private lemma s888_mem_conjugate_iff {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma s888_conjugate_subgroupOf {X : Type*} [Group X] (Hc : Subgroup X) (x : Hc)
    (A : Subgroup X) :
    CFSG.conjugate (A.subgroupOf Hc) x = (CFSG.conjugate A (x : X)).subgroupOf Hc := by
  ext u
  rw [Subgroup.mem_subgroupOf, s888_mem_conjugate_iff, s888_mem_conjugate_iff,
    Subgroup.mem_subgroupOf]
  simp

private lemma s888_coe_mem_zpowers {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : c ∈ Subgroup.zpowers h) : (c : X) ∈ Subgroup.zpowers (h : X) := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map]
  exact ⟨c, hc, rfl⟩

theorem pocketHyp_of_G (hq : Sec5B517Quad K z) {T : Subgroup G}
    (hNz : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G))
    (hTN : IsSylow2Of T (normalizer (Sec5B517Q8 hq : Set G)))
    (hTH : IsSylow2Of T (centralizer ({z} : Set G))) (hQT : Sec5B517Q8 hq ≤ T)
    (hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) n = K j)
    (htrans : ∀ i j : Fin 4, ∃ n ∈ normalizer (Sec5B517Q8 hq : Set G),
      CFSG.conjugate (K i) n = K j)
    (hclosed : ∀ q ∈ Sec5B517Q8 hq, ∀ x ∈ centralizer ({z} : Set G),
      x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hq : Set G) → x⁻¹ * q * x ∈ Sec5B517Q8 hq)
    (hcentS : ∀ s ∈ T, (∀ q ∈ Sec5B517Q8 hq, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) →
      s ∈ Sec5B517Q8 hq) :
    PocketHyp (zCent z) (fun i => (K i).subgroupOf (centralizer ({z} : Set G)))
      (T.subgroupOf (centralizer ({z} : Set G))) := by
  let Hc : Subgroup G := centralizer ({z} : Set G)
  have hz : z ∈ Hc := (zCent z).2
  change PocketHyp (⟨z, hz⟩ : Hc) (fun i => (K i).subgroupOf Hc) (T.subgroupOf Hc)
  have hK : ∀ i, K i ≤ Hc := fun i => le_centralizer_of_quad hq i
  have hQH : Sec5B517Q8 hq ≤ Hc := hQT.trans (hTN.1.trans hNz)
  have hQ8 : Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc :=
    q8_subgroupOf hq hK hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPg : IsPGroup 2 ↥(T.subgroupOf Hc) :=
    hTH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH.1).symm
  have hnd : ¬ 2 ∣ (T.subgroupOf Hc).index := by
    simpa [Subgroup.relIndex] using hTH.2.2
  refine ⟨quad_subgroupOf hq hK hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hPg.toSylow hnd, IsPGroup.toSylow_coe hPg hnd⟩
  · rw [hQ8]
    exact Subgroup.subgroupOf_mono Hc hQT
  · intro x hx
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH]
    exact hTN.1 (Subgroup.mem_subgroupOf.1 hx)
  · intro x hx i
    have hxN : (x : G) ∈ normalizer (Sec5B517Q8 hq) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨j, hj⟩ := hperm (x : G) hxN i
    refine ⟨j, ?_⟩
    rw [s888_conjugate_subgroupOf Hc x (K i), hj]
  · intro i j
    obtain ⟨x, hxN, hx⟩ := htrans i j
    refine ⟨⟨x, hNz hxN⟩, ?_, ?_⟩
    · rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH]
      exact Subgroup.mem_subgroupOf.2 hxN
    · rw [s888_conjugate_subgroupOf Hc ⟨x, hNz hxN⟩ (K i)]
      exact congrArg (·.subgroupOf Hc) hx
  · intro q hqQ x hx
    have hq' : (q : G) ∈ Sec5B517Q8 hq := by
      rw [hQ8] at hqQ
      exact Subgroup.mem_subgroupOf.1 hqQ
    have hxN : (x : G)⁻¹ * (q : G) * (x : G) ∈ normalizer (Sec5B517Q8 hq) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hx
      have hx' := Subgroup.mem_subgroupOf.1 hx
      simpa using hx'
    have hcl := hclosed (q : G) hq' (x : G) x.2 hxN
    rw [hQ8, Subgroup.mem_subgroupOf]
    simpa using hcl
  · intro s hs hcomm
    have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.1 hs
    have hcommG : ∀ q ∈ Sec5B517Q8 hq,
        (s : G) * q * (s : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      intro q hqQ
      have hqH : q ∈ Hc := hQH hqQ
      have hmem : (⟨q, hqH⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
        rw [hQ8]
        exact hqQ
      have h := hcomm (⟨q, hqH⟩ : Hc) hmem
      have h' := s888_coe_mem_zpowers Hc h
      simpa using h'
    have hsQ : (s : G) ∈ Sec5B517Q8 hq := hcentS (s : G) hsT hcommG
    rw [hQ8, Subgroup.mem_subgroupOf]
    exact hsQ

theorem zCent_mem_center (z : G) :
    zCent z ∈ center ↥(centralizer ({z} : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : G) * z = z * (g : G)
  exact (Subgroup.mem_centralizer_iff.1 g.2 z (Set.mem_singleton z)).symm

end CFSG.OddStandard.SmallF3.Omega
