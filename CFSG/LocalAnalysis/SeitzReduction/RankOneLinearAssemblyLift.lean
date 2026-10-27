module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssemblyChain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LinearPushChain

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_of_commute {L T S : Subgroup G} {f : ℕ} {t : G}
    (hS : Endings.Setting G L f t T) (hTS : T ≤ S) (hS2 : IsPGroup 2 S) {s : G} (hs : s ∈ S)
    (hst : s * t = t * s) : s ∈ T := by
  have hNC := normalizer_zpowers_eq_centralizer_of_involution hS.orderOf_t
  have hTH : T ≤ centralizer ({t} : Set G) := hNC ▸ hS.le_normalizer
  have hT' : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G)) := by
    rw [← hNC]
    exact hS.sylow
  have hle : T ≤ S ⊓ centralizer ({t} : Set G) := le_inf hTS hTH
  have hcard := Endings.card_le_of_isPGroup hTH hT' inf_le_right (hS2.to_le inf_le_left)
  have heq : T = S ⊓ centralizer ({t} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  refine mem_inf.mpr ⟨hs, mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff.mp hy]
  exact hst.symm

theorem exists_sylow_of_not_conj (hGold : Goldschmidt1974) {L T : Subgroup G} {f m : ℕ}
    {t d : G} {C : ℕ → Subgroup G} (hS : Endings.Setting G L f t T)
    (h : LinearPushChain t d T (T ⊓ L) f m C) (hm : 1 ≤ m)
    (hdfix : ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hsyl : IsSylowOf 2 (C (m + 1) ⊔ T) (pushNormalizer C (m + 1)))
    (hconj : ∀ y ∈ C (m + 1) ⊔ T, y ∉ C (m + 1) ⊔ zpowers t → y * y = 1 →
      ∀ g : G, g⁻¹ * t * g ≠ y) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = C (m + 1) ⊔ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, htt, -, -, -, hCTU, -, -, -, hsc, -, -, -, -, hTU, -⟩ :=
    Endings.psl2_ending_facts hGold hS
  have hf : 2 ≤ f := by have := hS.three_le; omega
  set S : Subgroup G := C (m + 1) ⊔ T with hSdef
  have hS2 : IsPGroup 2 S := hsyl.isPGroup
  have hTS : T ≤ S := le_sup_right
  have hUS : C (m + 1) ≤ S := le_sup_left
  have hTW : T ≤ normalizer (C (m + 1) : Set G) := h.T_norm (m + 1) le_rfl
  have htU : zpowers t ≤ normalizer (C (m + 1) : Set G) :=
    zpowers_le.mpr (h.t_norm (m + 1) le_rfl)
  have hAm : T ⊓ L ≤ C m := h.base_le hm (by omega)
  have hAU : T ⊓ L ≤ C (m + 1) := h.base_le (by omega) le_rfl
  have hcomm := h.commute_base hf htt hdfix (j := m + 1) (by omega) le_rfl
  set Ω : Set G := {w | w ∈ S ∧ ∃ g : G, g⁻¹ * t * g = w} with hΩ
  set K : Subgroup G := S ⊓ centralizer Ω with hK
  have hUK : T ⊓ L ≤ K := by
    intro a ha
    refine mem_inf.mpr ⟨hTS (mem_inf.mp ha).1, mem_centralizer_iff.mpr ?_⟩
    rintro w ⟨hwS, g, rfl⟩
    have hww : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; group
    have hwH : g⁻¹ * t * g ∈ C (m + 1) ⊔ zpowers t := by
      by_contra hwH
      exact hconj _ hwS hwH hww g rfl
    have hat : t * a = a * t :=
      mem_centralizer_iff.mp (h.base_le_centralizer ha) t (Set.mem_singleton t)
    obtain ⟨u, hu, hw | hw⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hwH
    · rw [← hw]
      exact hcomm u hu a ha
    · rw [← hw]
      calc u * t * a = u * (t * a) := by group
        _ = u * (a * t) := by rw [hat]
        _ = (u * a) * t := by group
        _ = (a * u) * t := by rw [hcomm u hu a ha]
        _ = a * (u * t) := by group
  have hKV : K ≤ T ⊓ L ⊔ zpowers t := by
    intro k hk
    obtain ⟨hkS, hkc⟩ := mem_inf.mp hk
    have htΩ : t ∈ Ω := ⟨hTS htT, 1, by group⟩
    have hkt : t * k = k * t := mem_centralizer_iff.mp hkc t htΩ
    have hkc' : ∀ c ∈ C m, c * k = k * c := by
      intro c hc
      obtain ⟨g, hg⟩ := h.exists_conj_eq_mul hm c hc
      have hcS : t * c ∈ S := mul_mem (hTS htT) (hUS (h.mono m le_rfl hc))
      have h1 : (t * c) * k = k * (t * c) := mem_centralizer_iff.mp hkc (t * c) ⟨hcS, g, hg⟩
      have h2 : t * (c * k) = t * (k * c) := by
        calc t * (c * k) = (t * c) * k := by group
          _ = k * (t * c) := h1
          _ = (k * t) * c := by group
          _ = (t * k) * c := by rw [hkt]
          _ = t * (k * c) := by group
      exact mul_left_cancel h2
    have hkT : k ∈ T := mem_of_mem_of_commute hS hTS hS2 hkS hkt.symm
    rw [← hCTU]
    refine mem_inf.mpr ⟨hkT, mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact hkc' a (hAm ha)
  have hCSU : ∀ s ∈ S, (∀ a ∈ T ⊓ L, s * a = a * s) → s ∈ C (m + 1) ⊔ zpowers t := by
    intro s hs hsa
    obtain ⟨u, hu, τ, hτ, rfl⟩ := Endings.exists_mul_eq_of_mem_sup hTW hs
    have hτa : τ ∈ T ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      refine mem_inf.mpr ⟨hτ, mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := hsa a ha
      have h2 : u * (τ * a) = u * (a * τ) := by
        calc u * (τ * a) = u * τ * a := by group
          _ = a * (u * τ) := h1
          _ = (a * u) * τ := by group
          _ = (u * a) * τ := by rw [hcomm u hu a ha]
          _ = u * (a * τ) := by group
      exact (mul_left_cancel h2).symm
    rw [hCTU] at hτa
    exact mul_mem (mem_sup_left hu) ((sup_le (hAU.trans le_sup_left) le_sup_right) hτa)
  by_cases htop : IsSylowOf 2 S ⊤
  · obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp htop
    rw [relIndex_top_right] at hidx
    exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩
  exfalso
  obtain ⟨S', hSS', z, hzS', hzN, hzS⟩ := GMS28.exists_mem_normalizer_of_not_isSylowOf hS2 htop
  have hzS1 : ∀ x ∈ S, z * x * z⁻¹ ∈ S := fun x hx => (mem_normalizer_iff.mp hzN x).mp hx
  have hzS2 : ∀ x ∈ S, z⁻¹ * x * z ∈ S := fun x hx => by
    have := (mem_normalizer_iff.mp hzN (z⁻¹ * x * z)).mpr
    rw [show z * (z⁻¹ * x * z) * z⁻¹ = x by group] at this
    exact this hx
  have hzK : ∀ k ∈ K, z * k * z⁻¹ ∈ K := by
    intro k hk
    obtain ⟨hkS, hkc⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨hzS1 k hkS, mem_centralizer_iff.mpr ?_⟩
    rintro w ⟨hwS, g, rfl⟩
    have hw' : z⁻¹ * (g⁻¹ * t * g) * z ∈ Ω :=
      ⟨hzS2 _ hwS, g * z, by group⟩
    have h1 := mem_centralizer_iff.mp hkc _ hw'
    calc g⁻¹ * t * g * (z * k * z⁻¹) = z * ((z⁻¹ * (g⁻¹ * t * g) * z) * k) * z⁻¹ := by group
      _ = z * (k * (z⁻¹ * (g⁻¹ * t * g) * z)) * z⁻¹ := by rw [h1]
      _ = z * k * z⁻¹ * (g⁻¹ * t * g) := by group
  have hzU : ∀ a ∈ T ⊓ L, z * a * z⁻¹ ∈ T ⊓ L := by
    intro a ha
    have h1 : z * a * z⁻¹ ∈ T ⊓ L ⊔ zpowers t := hKV (hzK a (hUK ha))
    have h2 := hsc a ha z⁻¹ (by rwa [inv_inv])
    rwa [inv_inv] at h2
  have hzU' : ∀ a ∈ T ⊓ L, z⁻¹ * a * z ∈ T ⊓ L := by
    intro a ha
    have hzN' : z ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      GMS28.mem_normalizer_of_conj_mem_of_finite hzU
    have := (mem_normalizer_iff.mp hzN' (z⁻¹ * a * z)).mpr
    rw [show z * (z⁻¹ * a * z) * z⁻¹ = a by group] at this
    exact this ha
  have hzH : z ∈ normalizer ((C (m + 1) ⊔ zpowers t : Subgroup G) : Set G) := by
    refine GMS28.mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    have hxS : x ∈ S := (sup_le hUS (zpowers_le.mpr (hTS htT))) hx
    refine hCSU _ (hzS1 x hxS) fun a ha => ?_
    have hxa : ∀ b ∈ T ⊓ L, x * b = b * x := by
      intro b hb
      obtain ⟨u, hu, hxu | hxu⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hx
      · rw [← hxu]; exact hcomm u hu b hb
      · have hbt : t * b = b * t :=
          mem_centralizer_iff.mp (h.base_le_centralizer hb) t (Set.mem_singleton t)
        rw [← hxu]
        calc u * t * b = u * (t * b) := by group
          _ = u * (b * t) := by rw [hbt]
          _ = (u * b) * t := by group
          _ = (b * u) * t := by rw [hcomm u hu b hb]
          _ = b * (u * t) := by group
    have h1 := hxa _ (hzU' a ha)
    calc z * x * z⁻¹ * a = z * (x * (z⁻¹ * a * z)) * z⁻¹ := by group
      _ = z * ((z⁻¹ * a * z) * x) * z⁻¹ := by rw [h1]
      _ = a * (z * x * z⁻¹) := by group
  have hzC := h.mem_normalizer_of_mem_normalizer_sup hm htt hzH
  have hzP : z ∈ pushNormalizer C (m + 1) := h.normalizer_le_of_one_le hm htt hzC
  have hle : S ⊔ zpowers z ≤ pushNormalizer C (m + 1) := sup_le hsyl.le (zpowers_le.mpr hzP)
  have hp' : IsPGroup 2 (S ⊔ zpowers z : Subgroup G) :=
    S'.isPGroup'.to_le (sup_le hSS' (zpowers_le.mpr hzS'))
  have heq := hsyl.eq_of_le le_sup_left hle hp'
  exact hzS (heq ▸ mem_sup_right (mem_zpowers z))

end LinearPushChain

end CFSG.SeitzReduction.RankOne
