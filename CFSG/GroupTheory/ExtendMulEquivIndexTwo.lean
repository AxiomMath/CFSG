module

public import CFSG.GroupTheory.InternalSemidirectEquiv
public import CFSG.Quasithin.Background.TwoM22TwoOuter

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G G' : Type*} [Group G] [Group G']

theorem mulAut_congr_conj_not_mem_inner
    {N C : Subgroup G} {C' : Type*} [Group C'] {t : G}
    (hCN : C ≤ N) (hN : N ≤ Subgroup.normalizer (C : Set G))
    (hcent : ∀ g ∈ N, (∀ c ∈ C, g * c = c * g) → g ∈ C)
    (htN : t ∈ N) (htC : t ∉ C) (θ : ↥C ≃* C') :
    MulAut.congr θ (conjHom C N hN ⟨t, htN⟩) ∉ inner C' := by
  rintro ⟨d, hd⟩
  let d₀ : ↥C := θ.symm d
  have hd₀ : θ d₀ = d := θ.apply_symm_apply d
  have hval (c : ↥C) : (conjHom C N hN ⟨t, htN⟩) c = MulAut.conj d₀ c := by
    apply θ.injective
    have hleft : ((MulAut.conj d) (θ c) : C') = θ (MulAut.conj d₀ c) := by
      calc (MulAut.conj d) (θ c) = d * θ c * d⁻¹ := MulAut.conj_apply d (θ c)
        _ = θ d₀ * θ c * (θ d₀)⁻¹ := by rw [hd₀]
        _ = θ (d₀ * c * d₀⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = θ (MulAut.conj d₀ c) := by rw [MulAut.conj_apply]
    have hright : ((MulAut.congr θ (conjHom C N hN ⟨t, htN⟩)) (θ c) : C') =
        θ ((conjHom C N hN ⟨t, htN⟩) c) := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply]
    rw [← hleft, ← hright]
    exact congrArg (fun f : MulAut C' => f (θ c)) hd.symm
  have hcomm : ∀ c ∈ C, (d₀⁻¹ * t) * c = c * (d₀⁻¹ * t) := by
    intro c hc
    have h1 : (((conjHom C N hN ⟨t, htN⟩) ⟨c, hc⟩ : ↥C) : G) = t * c * t⁻¹ :=
      conjHom_apply hN ⟨t, htN⟩ ⟨c, hc⟩
    have h2 : (((MulAut.conj d₀) ⟨c, hc⟩ : ↥C) : G) = (d₀ : G) * c * (d₀ : G)⁻¹ := by
      rw [MulAut.conj_apply]
      rfl
    have h3 : t * c * t⁻¹ = (d₀ : G) * c * (d₀ : G)⁻¹ := by
      rw [← h1, congrArg (fun x : ↥C => (x : G)) (hval ⟨c, hc⟩), h2]
    calc (d₀⁻¹ * t) * c = d₀⁻¹ * (t * c * t⁻¹) * t := by group
      _ = d₀⁻¹ * ((d₀ : G) * c * (d₀ : G)⁻¹) * t := by rw [h3]
      _ = c * (d₀⁻¹ * t) := by simp only [Subgroup.coe_inv]; group
  have hgN : d₀⁻¹ * t ∈ N := N.mul_mem (N.inv_mem (hCN d₀.2)) htN
  have hgC : d₀⁻¹ * t ∈ C := hcent (d₀⁻¹ * t) hgN hcomm
  apply htC
  have ht_eq : t = d₀ * (d₀⁻¹ * t) := by simp only [Subgroup.coe_inv]; group
  rw [ht_eq]
  exact C.mul_mem d₀.2 hgC

theorem exists_mulEquiv_extend_of_mul_self_eq_one
    {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {N C : Subgroup G} {N' C' : Subgroup G'} (hCN : C ≤ N) (hCN' : C' ≤ N')
    (hnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hnorm' : ∀ n ∈ N', ∀ c ∈ C', n * c * n⁻¹ ∈ C')
    {t : G} {t' : G'} (htC : t ∉ C) (htC' : t' ∉ C') (htt : t * t = 1) (htt' : t' * t' = 1)
    (hsup : N = C ⊔ Subgroup.zpowers t) (hsup' : N' = C' ⊔ Subgroup.zpowers t')
    (hcent : ∀ g ∈ N, (∀ c ∈ C, g * c = c * g) → g ∈ C)
    (hcent' : ∀ g ∈ N', (∀ c ∈ C', g * c = c * g) → g ∈ C')
    (hperf' : Group.IsPerfect ↥C')
    (hOut' : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥C' ⧸ Subgroup.center ↥C')) ≤ 2)
    (hkey' : ∀ n ∈ N', n ∉ C' → (∀ c ∈ C', n * n * c = c * (n * n)) → n * n = 1)
    (θ : ↥C ≃* ↥C') :
    ∃ θN : ↥N ≃* ↥N', ∀ c : ↥C, (θN ⟨c, hCN c.2⟩ : G') = θ c := by
  have hNnorm : N ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hnorm n hn c, fun hc => ?_⟩
    have h := hnorm n⁻¹ (N.inv_mem hn) (n * c * n⁻¹) hc
    have h' : n⁻¹ * (n * c * n⁻¹) * (n⁻¹)⁻¹ = c := by group
    rwa [h'] at h
  have hN'norm : N' ≤ Subgroup.normalizer (C' : Set G') := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hnorm' n hn c, fun hc => ?_⟩
    have h := hnorm' n⁻¹ (N'.inv_mem hn) (n * c * n⁻¹) hc
    have h' : n⁻¹ * (n * c * n⁻¹) * (n⁻¹)⁻¹ = c := by group
    rwa [h'] at h
  have htN : t ∈ N := by
    rw [hsup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htN' : t' ∈ N' := by
    rw [hsup']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t')
  let α : MulAut ↥C' := MulAut.congr θ (conjHom C N hNnorm ⟨t, htN⟩)
  let β : MulAut ↥C' := conjHom C' N' hN'norm ⟨t', htN'⟩
  have hα : α ∉ inner ↥C' := mulAut_congr_conj_not_mem_inner hCN hNnorm hcent htN htC θ
  have hβ : β ∉ inner ↥C' := by
    have hβc : MulAut.congr (MulEquiv.refl ↥C') (conjHom C' N' hN'norm ⟨t', htN'⟩) ∉
        inner ↥C' :=
      mulAut_congr_conj_not_mem_inner hCN' hN'norm hcent' htN' htC' (MulEquiv.refl ↥C')
    have hc : MulAut.congr (MulEquiv.refl ↥C') (conjHom C' N' hN'norm ⟨t', htN'⟩) =
        conjHom C' N' hN'norm ⟨t', htN'⟩ := by
      ext x
      simp [MulAut.congr_apply]
    rwa [hc] at hβc
  obtain ⟨c₀, hc₀⟩ :=
    exists_inner_mul_of_not_mem_inner_of_card_outer_center_le_two hperf' hOut' hα hβ
  have hα_eq : α = MulAut.conj c₀ * β := by
    rw [← hc₀]
    group
  let m : G' := (c₀ : G') * t'
  have hmN' : m ∈ N' := by
    change (c₀ : G') * t' ∈ N'
    exact N'.mul_mem (hCN' c₀.2) htN'
  have ht'_eq : t' = (c₀ : G')⁻¹ * m := by
    change t' = (c₀ : G')⁻¹ * ((c₀ : G') * t')
    group
  have hmC' : m ∉ C' := by
    intro hm
    apply htC'
    rw [ht'_eq]
    exact C'.mul_mem (C'.inv_mem c₀.2) hm
  have hβ_apply (q : ↥C') : (β q : G') = t' * (q : G') * t'⁻¹ := by
    change ((conjHom C' N' hN'norm ⟨t', htN'⟩) q : G') = _
    rw [conjHom_apply]
  have hconjm : conjHom C' N' hN'norm ⟨m, hmN'⟩ = α := by
    rw [hα_eq]
    ext x
    rw [conjHom_apply, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hβ_apply x]
    simp only [m, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hconj_sq : conjHom C N hNnorm ⟨t, htN⟩ * conjHom C N hNnorm ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have ht2 : (⟨t, htN⟩ : ↥N) * ⟨t, htN⟩ = 1 := Subtype.ext htt
    rw [ht2, map_one]
  have hα_sq : α * α = 1 := by
    calc α * α = MulAut.congr θ (conjHom C N hNnorm ⟨t, htN⟩ *
          conjHom C N hNnorm ⟨t, htN⟩) := by
          rw [map_mul]
      _ = MulAut.congr θ 1 := by rw [hconj_sq]
      _ = 1 := map_one _
  have hm2N' : m * m ∈ N' := N'.mul_mem hmN' hmN'
  have hconj_m2 : conjHom C' N' hN'norm ⟨m * m, hm2N'⟩ = 1 := by
    have hprod : (⟨m, hmN'⟩ : ↥N') * ⟨m, hmN'⟩ = ⟨m * m, hm2N'⟩ := Subtype.ext rfl
    calc conjHom C' N' hN'norm ⟨m * m, hm2N'⟩
        = conjHom C' N' hN'norm (⟨m, hmN'⟩ * ⟨m, hmN'⟩) := by rw [hprod]
      _ = conjHom C' N' hN'norm ⟨m, hmN'⟩ * conjHom C' N' hN'norm ⟨m, hmN'⟩ :=
          map_mul _ _ _
      _ = 1 := by rw [hconjm, hα_sq]
  have hcentral : ∀ c ∈ C', m * m * c = c * (m * m) := by
    intro c hc
    have hfix : (conjHom C' N' hN'norm ⟨m * m, hm2N'⟩) ⟨c, hc⟩ = ⟨c, hc⟩ := by
      rw [hconj_m2, MulAut.one_apply]
    have hval : m * m * c * (m * m)⁻¹ = c := by
      have := congrArg (fun x : ↥C' => (x : G')) hfix
      rwa [conjHom_apply] at this
    calc m * m * c = (m * m * c * (m * m)⁻¹) * (m * m) := by group
      _ = c * (m * m) := by rw [hval]
  have hm2_one : m * m = 1 := hkey' m hmN' hmC' hcentral
  have ht1 : t ≠ 1 := by
    intro h
    exact htC (by rw [h]; exact C.one_mem)
  have hm1 : m ≠ 1 := by
    intro h
    exact hmC' (by rw [h]; exact C'.one_mem)
  have hordt : orderOf t = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact htt) ht1
  have hordm : orderOf m = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hm2_one) hm1
  let gt : ↥(Subgroup.zpowers t) := ⟨t, Subgroup.mem_zpowers t⟩
  let gm : ↥(Subgroup.zpowers m) := ⟨m, Subgroup.mem_zpowers m⟩
  have hgenT : ∀ x : ↥(Subgroup.zpowers t), x ∈ Subgroup.zpowers gt := by
    intro x
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact ⟨j, Subtype.ext hj⟩
  have hgenM : ∀ x : ↥(Subgroup.zpowers m), x ∈ Subgroup.zpowers gm := by
    intro x
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact ⟨j, Subtype.ext hj⟩
  have hordSub : orderOf gt = orderOf gm := by
    rw [show orderOf gt = orderOf t by exact Subgroup.orderOf_mk t (Subgroup.mem_zpowers t),
      show orderOf gm = orderOf m by exact Subgroup.orderOf_mk m (Subgroup.mem_zpowers m),
      hordt, hordm]
  let Λ : ↥(Subgroup.zpowers t) ≃* ↥(Subgroup.zpowers m) :=
    mulEquivOfOrderOfEq hgenT hgenM hordSub
  have hmem_t : ∀ k : G, k ∈ Subgroup.zpowers t ↔ k = 1 ∨ k = t := by
    intro k
    constructor
    · intro hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      obtain ⟨i, hi | hi⟩ := Int.even_or_odd' j
      · left
        rw [hi, zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two, htt], one_zpow]
      · right
        rw [hi, zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two, htt],
          one_zpow, one_mul, zpow_one]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hmem_m : ∀ k : G', k ∈ Subgroup.zpowers m ↔ k = 1 ∨ k = m := by
    intro k
    constructor
    · intro hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      obtain ⟨i, hi | hi⟩ := Int.even_or_odd' j
      · left
        rw [hi, zpow_mul, show m ^ (2 : ℤ) = 1 by rw [zpow_two, hm2_one], one_zpow]
      · right
        rw [hi, zpow_add, zpow_mul, show m ^ (2 : ℤ) = 1 by rw [zpow_two, hm2_one],
          one_zpow, one_mul, zpow_one]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hΛt : Λ ⟨t, Subgroup.mem_zpowers t⟩ = ⟨m, Subgroup.mem_zpowers m⟩ := by
    have hmem : (Λ ⟨t, Subgroup.mem_zpowers t⟩ : G') ∈ Subgroup.zpowers m :=
      (Λ ⟨t, Subgroup.mem_zpowers t⟩).2
    rcases (hmem_m _).mp hmem with h1 | hm
    · have htriv : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) = 1 :=
        Λ.injective (by simpa using h1)
      exact absurd (congrArg (fun x : ↥(Subgroup.zpowers t) => (x : G)) htriv)
        (by simpa using ht1)
    · exact Subtype.ext hm
  have hd : Disjoint C (Subgroup.zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxK
    rcases (hmem_t x).mp hxK with hx1 | hxt
    · exact hx1
    · exact (htC (hxt ▸ hxC)).elim
  have hd' : Disjoint C' (Subgroup.zpowers m) := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxK
    rcases (hmem_m x).mp hxK with hx1 | hxm
    · exact hx1
    · exact (hmC' (hxm ▸ hxC)).elim
  have hK : Subgroup.zpowers t ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.zpowers_le.mpr (hNnorm htN)
  have hK' : Subgroup.zpowers m ≤ Subgroup.normalizer (C' : Set G') :=
    Subgroup.zpowers_le.mpr (hN'norm hmN')
  have hm_sup : m ∈ C' ⊔ Subgroup.zpowers t' := by
    rw [← hsup']
    exact hmN'
  have ht'_sup : t' ∈ C' ⊔ Subgroup.zpowers m := by
    rw [ht'_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C'.inv_mem c₀.2))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))
  have hsupm : C' ⊔ Subgroup.zpowers m = C' ⊔ Subgroup.zpowers t' := by
    apply le_antisymm
    · apply sup_le
      · exact le_sup_left
      · exact Subgroup.zpowers_le.mpr hm_sup
    · apply sup_le
      · exact le_sup_left
      · exact Subgroup.zpowers_le.mpr ht'_sup
  have hα_apply (q : ↥C) : α (θ q) = θ ((conjHom C N hNnorm ⟨t, htN⟩) q) := by
    change (MulAut.congr θ (conjHom C N hNnorm ⟨t, htN⟩)) (θ q) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply]
  have hα_val (q : ↥C) : (α (θ q) : G') = m * (θ q : G') * m⁻¹ := by
    have h1 : (α (θ q) : G') =
        (c₀ : G') * (t' * (θ q : G') * t'⁻¹) * (c₀ : G')⁻¹ := by
      rw [hα_eq, MulAut.mul_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ_apply]
    rw [h1]
    simp only [m, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hθ_val (q : ↥C) :
      (θ ((conjHom C N hNnorm ⟨t, htN⟩) q) : G') = m * (θ q : G') * m⁻¹ := by
    rw [← hα_apply q, hα_val q]
  have hcompat : ∀ (k : ↥(Subgroup.zpowers t)) (q : ↥C)
      (hq : (k : G) * q * (k : G)⁻¹ ∈ C),
      ((θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩ : ↥C') : G') =
        (Λ k : G') * (θ q : G') * (Λ k : G')⁻¹ := by
    intro k q hq
    rcases (hmem_t (k : G)).mp k.2 with hk1 | hkt
    · have hk : k = 1 := Subtype.ext hk1
      subst hk
      have hq1 : (⟨((1 : ↥(Subgroup.zpowers t)) : G) * (q : G) *
          (((1 : ↥(Subgroup.zpowers t)) : G))⁻¹, hq⟩ : ↥C) = q := by
        apply Subtype.ext
        simp
      rw [hq1]
      simp
    · have hk : k = ⟨t, Subgroup.mem_zpowers t⟩ := Subtype.ext hkt
      subst hk
      have hconj : (conjHom C N hNnorm ⟨t, htN⟩) q =
          ⟨t * (q : G) * t⁻¹, hq⟩ := by
        apply Subtype.ext
        rw [conjHom_val]
      rw [← hconj, hΛt]
      exact hθ_val q
  obtain ⟨αN, hαN_C, -⟩ := exists_mulEquiv_sup_extend hK hd hK' hd' θ Λ hcompat
  let eN : ↥N ≃* ↥(C ⊔ Subgroup.zpowers t) := MulEquiv.subgroupCongr hsup
  let eN' : ↥(C' ⊔ Subgroup.zpowers m) ≃* ↥N' :=
    MulEquiv.subgroupCongr (hsupm.trans hsup'.symm)
  refine ⟨eN.trans (αN.trans eN'), ?_⟩
  intro c
  have heN : eN ⟨c, hCN c.2⟩ = ⟨c, Subgroup.mem_sup_left c.2⟩ := by
    apply Subtype.ext
    exact MulEquiv.subgroupCongr_apply hsup ⟨c, hCN c.2⟩
  calc ((eN.trans (αN.trans eN')) ⟨c, hCN c.2⟩ : G')
      = ((eN' (αN (eN ⟨c, hCN c.2⟩)) : ↥N') : G') := rfl
    _ = ((αN (eN ⟨c, hCN c.2⟩) : ↥(C' ⊔ Subgroup.zpowers m)) : G') :=
        MulEquiv.subgroupCongr_apply _ _
    _ = ((αN ⟨c, Subgroup.mem_sup_left c.2⟩ : ↥(C' ⊔ Subgroup.zpowers m)) : G') := by
        rw [heN]
    _ = (θ c : G') := hαN_C c

end CFSG.GroupTheory
