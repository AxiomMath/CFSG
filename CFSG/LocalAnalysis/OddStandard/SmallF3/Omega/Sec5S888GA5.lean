module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GA4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT2

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private lemma ga5_mem_conjugate_iff {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma ga5_conjugate_subgroupOf {X : Type*} [Group X] (Hc : Subgroup X) (x : Hc)
    (A : Subgroup X) :
    CFSG.conjugate (A.subgroupOf Hc) x = (CFSG.conjugate A (x : X)).subgroupOf Hc := by
  ext u
  rw [Subgroup.mem_subgroupOf, ga5_mem_conjugate_iff, ga5_mem_conjugate_iff,
    Subgroup.mem_subgroupOf]
  simp

private lemma ga5_coe_mem_zpowers {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : c ∈ Subgroup.zpowers h) : (c : X) ∈ Subgroup.zpowers (h : X) := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map]
  exact ⟨c, hc, rfl⟩

private lemma ga5_mem_zpowers_subgroupOf {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : (c : X) ∈ Subgroup.zpowers (h : X)) : c ∈ Subgroup.zpowers h := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map] at hc
  obtain ⟨c', hc', hcc'⟩ := hc
  rw [show c' = c from Subtype.ext hcc'] at hc'
  exact hc'

private lemma ga5_alpha_mem_centralizer_planeV_iff
    {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}
    (hS : PlaneSetup z K α) {x : H} :
    α x ∈ centralizer (planeV hS.quad α : Set X) ↔
      ∀ q ∈ Sec5B517Q8 hS.quad, x * q * x⁻¹ * q⁻¹ ∈ zpowers z := by
  constructor
  · intro hx q hq
    have hqV : α q ∈ planeV hS.quad α := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have hcomm : α q * α x = α x * α q :=
      (Subgroup.mem_centralizer_iff.mp hx) (α q) hqV
    rw [← hS.ker, MonoidHom.mem_ker]
    rw [show α (x * q * x⁻¹ * q⁻¹) = α x * α q * (α x)⁻¹ * (α q)⁻¹ by
      simp only [map_mul, map_inv]]
    rw [← hcomm]
    group
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
    have hker : x * q * x⁻¹ * q⁻¹ ∈ α.ker := by
      rw [hS.ker]
      exact h q hq
    have h1 : α (x * q * x⁻¹ * q⁻¹) = 1 := MonoidHom.mem_ker.mp hker
    have h2 : α (x * q * x⁻¹) = α q := by
      have h1' := h1
      rw [show α (x * q * x⁻¹ * q⁻¹) = α (x * q * x⁻¹) * (α q)⁻¹ by
        simp only [map_mul, map_inv]] at h1'
      exact mul_inv_eq_one.mp h1'
    rw [show α (x * q * x⁻¹) = α x * α q * (α x)⁻¹ by
      simp only [map_mul, map_inv]] at h2
    have h3 := congrArg (· * α x) h2
    simpa [mul_assoc] using h3.symm

theorem lemma519_of_quad [Finite G] (hq : Sec5B517Quad K z)
    (hNz : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G))
    (hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) n = K j)
    (hcent : ∀ s ∈ normalizer (Sec5B517Q8 hq : Set G), s * s ∈ Sec5B517Q8 hq →
      (∀ q ∈ Sec5B517Q8 hq, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hq)
    (hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G), (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (K i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    (h518 : ∀ (U : Subgroup G) (n : ℕ), U ≤ normalizer (Sec5B517Q8 hq : Set G) →
      IsElemAbelianModSub
        (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq)) U →
      (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq)).relIndex U =
        2 ^ n → n ≤ 3)
    (hCd : ∀ d : G, d ∈ Sec5B517Q8 hq → d * d = 1 → d ≠ 1 → d ≠ z →
      (∃ i j : Fin 4, i ≠ j ∧ d ∈ K i ⊔ K j) →
        centralizer ({d} : Set G) ⊓ centralizer ({z} : Set G) ≤
          normalizer (Sec5B517Q8 hq : Set G)) :
    ∀ q ∈ Sec5B517Q8 hq, ∀ x ∈ centralizer ({z} : Set G),
      x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hq : Set G) → x⁻¹ * q * x ∈ Sec5B517Q8 hq := by
  classical
  let Hc : Subgroup G := centralizer ({z} : Set G)
  have hz : z ∈ Hc := (zCent z).2
  have hK : ∀ i, K i ≤ Hc := fun i => le_centralizer_of_quad hq i
  have hQH : Sec5B517Q8 hq ≤ Hc := Subgroup.le_normalizer.trans hNz
  have hQ8 : Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc :=
    q8_subgroupOf hq hK hz
  have hzcenter : (⟨z, hz⟩ : Hc) ∈ Subgroup.center Hc := by
    change zCent z ∈ Subgroup.center Hc
    exact zCent_mem_center z
  haveI : (Subgroup.zpowers (⟨z, hz⟩ : Hc)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hzcenter)
  let α : Hc →* Hc ⧸ Subgroup.zpowers (⟨z, hz⟩ : Hc) := QuotientGroup.mk' _
  have hS : PlaneSetup (⟨z, hz⟩ : Hc) (fun i => (K i).subgroupOf Hc) α :=
    ⟨quad_subgroupOf hq hK hz, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  have hperm' : ∀ x ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      ∀ i : Fin 4, ∃ j, CFSG.conjugate ((K i).subgroupOf Hc) x = (K j).subgroupOf Hc := by
    intro x hx i
    have hxN : (x : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨j, hj⟩ := hperm (x : G) hxN i
    exact ⟨j, by rw [ga5_conjugate_subgroupOf Hc x (K i), hj]⟩
  have hcent' : ∀ s ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      s * s ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        s * q * s⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
      s ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
    intro s hs hs2 hcomm
    have hsN : (s : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hs
      exact Subgroup.mem_subgroupOf.1 hs
    have hs2' : (s : G) * (s : G) ∈ Sec5B517Q8 hq := by
      rw [hQ8, Subgroup.mem_subgroupOf] at hs2
      simpa using hs2
    have hcommG : ∀ q ∈ Sec5B517Q8 hq,
        (s : G) * q * (s : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      intro q hqQ
      have hmem : (⟨q, hQH hqQ⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
        rw [hQ8]
        exact hqQ
      have h' := ga5_coe_mem_zpowers Hc (hcomm (⟨q, hQH hqQ⟩ : Hc) hmem)
      simpa using h'
    have hsQ : (s : G) ∈ Sec5B517Q8 hq := hcent (s : G) hsN hs2' hcommG
    rw [hQ8, Subgroup.mem_subgroupOf]
    exact hsQ
  have hpar' : ∀ w ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      (∀ i, CFSG.conjugate ((K i).subgroupOf Hc) w = (K i).subgroupOf Hc) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
      Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) ⊓
        (K i).subgroupOf Hc, w⁻¹ * q * w ≠ q ∧
        w⁻¹ * q * w ≠ q * (⟨z, hz⟩ : Hc)}) :=
    parity_subgroupOf hq hK hz hparG
  have hCd' : ∀ d : Hc, d ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) → d * d = 1 → d ≠ 1 →
      d ≠ (⟨z, hz⟩ : Hc) →
      (∃ i j : Fin 4, i ≠ j ∧ d ∈ (K i).subgroupOf Hc ⊔ (K j).subgroupOf Hc) →
        centralizer ({d} : Set Hc) ≤
          normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc) := by
    intro d hdQ hd2 hd1 hdz hdij y hy
    obtain ⟨i, j, hij, hdK⟩ := hdij
    have hdQ' : (d : G) ∈ Sec5B517Q8 hq := by
      rw [hQ8, Subgroup.mem_subgroupOf] at hdQ
      exact hdQ
    have hd2' : (d : G) * (d : G) = 1 := by simpa using congrArg Subtype.val hd2
    have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext (by simpa using h))
    have hdz' : (d : G) ≠ z := fun h => hdz (Subtype.ext (by simpa using h))
    have hdK' : (d : G) ∈ K i ⊔ K j := by
      have hmem : (d : G) ∈ ((K i).subgroupOf Hc ⊔ (K j).subgroupOf Hc).map Hc.subtype :=
        Subgroup.mem_map.mpr ⟨d, hdK, rfl⟩
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hK i),
        Subgroup.map_subgroupOf_eq_of_le (hK j)] at hmem
    have hyd : (y : G) ∈ centralizer ({(d : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      simpa using congrArg Subtype.val hy
    have hyN : (y : G) ∈ normalizer (Sec5B517Q8 hq : Set G) :=
      hCd (d : G) hdQ' hd2' hd1' hdz' ⟨i, j, hij, hdK'⟩ ⟨hyd, y.2⟩
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH]
    exact Subgroup.mem_subgroupOf.mpr hyN
  have hmemC : ∀ m : Hc, m ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        m * q * m⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
      (m : G) ∈ centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq) := by
    intro m hm hc
    have hmN : (m : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hm
      exact Subgroup.mem_subgroupOf.1 hm
    refine ⟨hmN, m.2, hmN, fun q hqQ => ?_⟩
    have hmem : (⟨q, hQH hqQ⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
      rw [hQ8]
      exact hqQ
    have h := ga5_coe_mem_zpowers Hc (hc _ hmem)
    simpa using h
  have h518' : ∀ (U' : Subgroup Hc) (n : ℕ),
      U' ≤ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc) →
      (∀ a ∈ U', ∀ b ∈ U',
        (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
          a * b * a⁻¹ * b⁻¹ * q * (a * b * a⁻¹ * b⁻¹)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) ∧
        (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
          a * a * q * (a * a)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc))) →
      ((centralizer (planeV (quad_subgroupOf hq hK hz) α : Set _)).comap α).relIndex U' =
        2 ^ n → n ≤ 3 := by
    intro U' n hU' hab' hrel
    have hUN : U'.map Hc.subtype ≤ normalizer (Sec5B517Q8 hq : Set G) := by
      rintro _ ⟨u, hu, rfl⟩
      have h := hU' hu
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at h
      exact Subgroup.mem_subgroupOf.1 h
    have hPeq : centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq) ⊓
          U'.map Hc.subtype =
        ((centralizer (planeV (quad_subgroupOf hq hK hz) α : Set _)).comap α).map Hc.subtype ⊓
          U'.map Hc.subtype := by
      ext x
      constructor
      · rintro ⟨hxC, hxU⟩
        obtain ⟨x', hx', rfl⟩ := hxU
        refine ⟨Subgroup.mem_map.mpr ⟨x', ?_, rfl⟩, Subgroup.mem_map.mpr ⟨x', hx', rfl⟩⟩
        refine (ga5_alpha_mem_centralizer_planeV_iff hS).mpr fun q hq' => ?_
        have hqG : (q : G) ∈ Sec5B517Q8 hq := by
          rw [hQ8, Subgroup.mem_subgroupOf] at hq'
          exact hq'
        have h := hxC.2.2.2 (q : G) hqG
        exact ga5_mem_zpowers_subgroupOf Hc (by simpa using h)
      · rintro ⟨hxD, hxU⟩
        obtain ⟨x', hx', rfl⟩ := hxU
        obtain ⟨y, hy, hyx⟩ := hxD
        have hyx' : y = x' := Subtype.ext hyx
        subst hyx'
        exact ⟨hmemC y (hU' hx') fun q hq' =>
          (ga5_alpha_mem_centralizer_planeV_iff hS).mp hy q hq', ⟨y, hx', rfl⟩⟩
    refine h518 (U'.map Hc.subtype) n hUN ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨h1, h2⟩ := hab' a ha b hb
      have hab1 : a * b * a⁻¹ * b⁻¹ ∈ U' :=
        U'.mul_mem (U'.mul_mem (U'.mul_mem ha hb) (U'.inv_mem ha)) (U'.inv_mem hb)
      have h1' := hmemC _ (hU' hab1) h1
      have h2' := hmemC _ (hU' (U'.mul_mem ha ha)) h2
      exact ⟨by simpa using h1', by simpa using h2'⟩
    · have h1 : (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq)).relIndex
          (U'.map Hc.subtype) = (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G))
            (Sec5B517Q8 hq) ⊓ U'.map Hc.subtype).relIndex (U'.map Hc.subtype) :=
        (Subgroup.inf_relIndex_right _ _).symm
      rw [h1, hPeq, Subgroup.inf_relIndex_right,
        Subgroup.relIndex_map_map_of_injective _ _ Hc.subtype_injective]
      exact hrel
  intro q hqQ x hx hxN
  have hqH : q ∈ Hc := hQH hqQ
  have hq' : (⟨q, hqH⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
    rw [hQ8]
    exact hqQ
  have hxN' : (⟨x, hx⟩ : Hc)⁻¹ * ⟨q, hqH⟩ * ⟨x, hx⟩ ∈
      normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc) := by
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH, Subgroup.mem_subgroupOf]
    simpa using hxN
  have h := closed_of_setup hS hperm' hcent' hpar' h518' hCd' _ hq' ⟨x, hx⟩ hxN'
  rw [hQ8, Subgroup.mem_subgroupOf] at h
  simpa using h

end CFSG.OddStandard.SmallF3.Omega
