module

public import CFSG.GH74.E2.Cen
public import CFSG.Adapters.Involutions

public section

namespace CFSG.GH74.E2

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_of_subgroupOf {P H : Subgroup G} (hHP : H ≤ P) {n : G} (hn : n ∈ P)
    (h : (⟨n, hn⟩ : P) ∈ normalizer ((H.subgroupOf P : Subgroup P) : Set P)) :
    n ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff] at h ⊢
  intro x
  by_cases hx : x ∈ P
  · have := h ⟨x, hx⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · have hx' : n * x * n⁻¹ ∉ P := fun hmem => hx (by
      have := mul_mem (mul_mem (inv_mem hn) hmem) hn
      simpa [mul_assoc] using this)
    constructor
    · intro hxH
      exact absurd (hHP hxH) hx
    · intro hH
      exact absurd (hHP hH) hx'

theorem exists_normalizer_moving [Finite G] {t : G} {S₁ : Subgroup G} (hle : S₁ ≤ Cen t)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → S₁ ≤ P → P = S₁) (htS : t ∈ S₁)
    (hns : ∃ P : Subgroup G, IsPGroup 2 P ∧ S₁ ≤ P ∧ P ≠ S₁) :
    ∃ n ∈ normalizer (S₁ : Set G), n⁻¹ * t * n ≠ t ∧ n⁻¹ * t * n ∈ S₁ ∧
      ∀ s ∈ S₁, s * (n⁻¹ * t * n) = (n⁻¹ * t * n) * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP2, hS₁P, hPne⟩ := hns
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hS₁S : S₁ ≤ (S : Subgroup G) := hS₁P.trans hPS
  have hS₁lt : S₁ < (S : Subgroup G) := lt_of_le_of_ne hS₁S (fun h => hPne (by
    apply le_antisymm _ hS₁P
    rw [h]
    exact hPS))
  have hSnil : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G))
  have hlt : S₁.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have : (S : Subgroup G) ≤ S₁ := by
      intro x hx
      have : (⟨x, hx⟩ : (S : Subgroup G)) ∈ S₁.subgroupOf (S : Subgroup G) := by rw [h]; trivial
      exact this
    exact absurd this (not_le_of_gt hS₁lt)
  have h1 := hnc _ hlt
  obtain ⟨n, hnN, hnS⟩ := IsConcreteLE.exists_of_lt h1
  have hnS₁ : (n : G) ∉ S₁ := fun h => hnS (by rw [Subgroup.mem_subgroupOf]; exact h)
  have hnorm : (n : G) ∈ normalizer (S₁ : Set G) :=
    mem_normalizer_of_subgroupOf hS₁S n.2 hnN
  have hnS' : (n : G) ∈ (S : Subgroup G) := n.2
  clear hnN hnS h1 hlt
  generalize (n : G) = m at hnS₁ hnorm hnS'
  have hn' : m⁻¹ ∈ normalizer (S₁ : Set G) := inv_mem hnorm
  have hconj : ∀ s ∈ S₁, m * s * m⁻¹ ∈ S₁ := fun s hs => (mem_normalizer_iff.1 hnorm s).1 hs
  refine ⟨m, hnorm, ?_, ?_, ?_⟩
  · intro heq
    have hnC : m ∈ Cen t := by
      rw [mem_Cen']
      have h5 : m * (m⁻¹ * t * m) = t * m := by group
      rw [heq] at h5
      exact h5
    have hP'S : S₁ ⊔ zpowers m ≤ (S : Subgroup G) :=
      sup_le hS₁S (zpowers_le.2 hnS')
    have hP'2 : IsPGroup 2 ↥(S₁ ⊔ zpowers m) := S.isPGroup'.to_le hP'S
    have hP'C : S₁ ⊔ zpowers m ≤ Cen t := sup_le hle (zpowers_le.2 hnC)
    have h4 := hmax _ hP'2 hP'C le_sup_left
    apply hnS₁
    rw [← h4]
    exact (le_sup_right : zpowers m ≤ S₁ ⊔ zpowers m) (mem_zpowers m)
  · have := (mem_normalizer_iff.1 hn' t).1 htS
    simpa using this
  · intro s hs
    have h2 : m * s * m⁻¹ ∈ S₁ := hconj s hs
    have h3 : t * (m * s * m⁻¹) = (m * s * m⁻¹) * t := mem_Cen.1 (hle h2)
    calc s * (m⁻¹ * t * m) = m⁻¹ * ((m * s * m⁻¹) * t) * m := by group
      _ = m⁻¹ * (t * (m * s * m⁻¹)) * m := by rw [h3]
      _ = (m⁻¹ * t * m) * s := by group

theorem tool_Z {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S : Sylow 2 G} {t : G} (ht : orderOf t = 2) (htS : t ∈ (S : Subgroup G))
    (htc : ∀ s ∈ (S : Subgroup G), s * t = t * s)
    (hcl : ∀ u ∈ (S : Subgroup G), orderOf u = 2 →
      ∃ c : G, c * t = t * c ∧ c⁻¹ * u * c ∈ (S : Subgroup G) ∧
        ∀ s ∈ (S : Subgroup G), s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s)
    (hfix : ∀ n ∈ normalizer (S : Set G), ∀ w ∈ (S : Subgroup G),
      (∀ s ∈ (S : Subgroup G), s * w = w * s) → w = n⁻¹ * t * n → w = t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htcent : t ∈ centralizer ((S : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact htc s hs
  have hwc : ∀ g : G, g⁻¹ * t * g ∈ (S : Subgroup G) → g⁻¹ * t * g = t := by
    intro g hg
    by_contra hne
    set u := g⁻¹ * t * g with hu
    have hu2 : orderOf u = 2 := by
      have ht2 : t ^ 2 = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht] at this
      have hu1 : u ^ 2 = 1 := by
        calc u ^ 2 = g⁻¹ * t ^ 2 * g := by rw [hu, pow_two, pow_two]; group
          _ = 1 := by rw [ht2]; group
      refine orderOf_eq_prime hu1 ?_
      intro h1
      have : t = 1 := by
        calc t = g * u * g⁻¹ := by rw [hu]; group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at ht
      omega
    obtain ⟨c, hct, hcu, hcuc⟩ := hcl u hg hu2
    have hw : (g * c)⁻¹ * t * (g * c) = c⁻¹ * u * c := by
      simp [hu, mul_assoc]
    have hwcent : (g * c)⁻¹ * t * (g * c) ∈ centralizer ((S : Subgroup G) : Set G) := by
      rw [hw, mem_centralizer_iff]
      intro s hs
      exact hcuc s hs
    obtain ⟨n, hn, hn2⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S t (g * c) htcent hwcent
    have := hfix n hn (c⁻¹ * u * c) hcu hcuc (by rw [← hw]; exact hn2)
    apply hne
    calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [this]
      _ = t := by rw [hct]; group
  have hz2 : (⟨t, htS⟩ : (S : Subgroup G)) ^ 2 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hz1 : (⟨t, htS⟩ : (S : Subgroup G)) ≠ 1 := by
    intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  let z : (S : Subgroup G) := ⟨t, htS⟩
  have hzZ : z ∈ Subgroup.center (S : Subgroup G) :=
    Subgroup.mem_center_iff.2 (fun s => Subtype.ext (htc s s.2))
  have hwc' : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z := hwc
  obtain ⟨hG, hcen⟩ := CFSG.Adapters.glauberman_zStar S z hzZ (orderOf_eq_prime hz2 hz1) hwc'
  have hodd : CFSG.oddCore G = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      apply CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht
      rw [h]; trivial
  have htcentG : t ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hG g
    rw [hodd, Subgroup.mem_bot] at hk
    subst hk
    have := mem_centralizer_iff.1 hc t (Set.mem_singleton_iff.2 rfl)
    simpa using this.symm
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at htcentG
    rw [htcentG, orderOf_one] at ht
    omega
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center G := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem exists_swap {t u : G} (hcomm : t * u = u * t) {g₀ : G} (hg₀ : g₀⁻¹ * t * g₀ = u)
    (htinv : t ^ 2 = 1)
    (huniq : ∀ v : G, v ^ 2 = 1 → v * t = t * v →
      Nat.card (centralizer ({t, v} : Set G)) = Nat.card (centralizer ({t, u} : Set G)) →
      ∃ c : G, c * t = t * c ∧ c⁻¹ * u * c = v) :
    ∃ g : G, g⁻¹ * t * g = u ∧ g⁻¹ * u * g = t := by
  set v := g₀ * t * g₀⁻¹ with hv
  have htu : t = g₀ * u * g₀⁻¹ := by rw [← hg₀]; group
  have hvt : v * t = t * v := by
    calc v * t = g₀ * t * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by rw [← htu]
      _ = g₀ * (t * u) * g₀⁻¹ := by group
      _ = g₀ * (u * t) * g₀⁻¹ := by rw [hcomm]
      _ = (g₀ * u * g₀⁻¹) * (g₀ * t * g₀⁻¹) := by group
      _ = t * v := by rw [← htu]
  have hv2 : v ^ 2 = 1 := by
    calc v ^ 2 = g₀ * t ^ 2 * g₀⁻¹ := by rw [hv, pow_two, pow_two]; group
      _ = 1 := by rw [htinv]; group
  have hcard : Nat.card (centralizer ({t, v} : Set G)) = Nat.card (centralizer ({t, u} : Set G)) := by
    have hmap : (centralizer ({t, u} : Set G)).map (MulAut.conj g₀).toMonoidHom =
        centralizer ({t, v} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_iff] at hy
        rw [mem_centralizer_iff]
        intro h hh
        rcases Set.mem_insert_iff.1 hh with h1 | h1
        ·
          rw [h1]
          have hyu := hy u (by simp)
          show t * (g₀ * y * g₀⁻¹) = (g₀ * y * g₀⁻¹) * t
          calc t * (g₀ * y * g₀⁻¹) = (g₀ * u * g₀⁻¹) * (g₀ * y * g₀⁻¹) := by rw [← htu]
            _ = g₀ * (u * y) * g₀⁻¹ := by group
            _ = g₀ * (y * u) * g₀⁻¹ := by rw [hyu]
            _ = (g₀ * y * g₀⁻¹) * (g₀ * u * g₀⁻¹) := by group
            _ = (g₀ * y * g₀⁻¹) * t := by rw [← htu]
        ·
          rw [Set.mem_singleton_iff] at h1
          rw [h1]
          have hyt := hy t (by simp)
          show v * (g₀ * y * g₀⁻¹) = (g₀ * y * g₀⁻¹) * v
          rw [hv]
          calc g₀ * t * g₀⁻¹ * (g₀ * y * g₀⁻¹) = g₀ * (t * y) * g₀⁻¹ := by group
            _ = g₀ * (y * t) * g₀⁻¹ := by rw [hyt]
            _ = (g₀ * y * g₀⁻¹) * (g₀ * t * g₀⁻¹) := by group
      · intro hx
        rw [mem_centralizer_iff] at hx
        refine ⟨g₀⁻¹ * x * g₀, ?_, ?_⟩
        · rw [SetLike.mem_coe, mem_centralizer_iff]
          intro h hh
          rcases Set.mem_insert_iff.1 hh with h1 | h1
          · rw [h1]
            have hxv := hx v (by simp)
            show t * (g₀⁻¹ * x * g₀) = (g₀⁻¹ * x * g₀) * t
            have e : t = g₀⁻¹ * v * g₀ := by rw [hv]; group
            calc t * (g₀⁻¹ * x * g₀) = (g₀⁻¹ * v * g₀) * (g₀⁻¹ * x * g₀) := by rw [← e]
              _ = g₀⁻¹ * (v * x) * g₀ := by group
              _ = g₀⁻¹ * (x * v) * g₀ := by rw [hxv]
              _ = (g₀⁻¹ * x * g₀) * (g₀⁻¹ * v * g₀) := by group
              _ = (g₀⁻¹ * x * g₀) * t := by rw [← e]
          · rw [Set.mem_singleton_iff] at h1
            rw [h1]
            have hxt := hx t (by simp)
            show u * (g₀⁻¹ * x * g₀) = (g₀⁻¹ * x * g₀) * u
            rw [← hg₀]
            calc g₀⁻¹ * t * g₀ * (g₀⁻¹ * x * g₀) = g₀⁻¹ * (t * x) * g₀ := by group
              _ = g₀⁻¹ * (x * t) * g₀ := by rw [hxt]
              _ = (g₀⁻¹ * x * g₀) * (g₀⁻¹ * t * g₀) := by group
        · show g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ = x
          group
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
  obtain ⟨c, hct, hcu⟩ := huniq v hv2 hvt hcard
  refine ⟨c * g₀, ?_, ?_⟩
  · calc (c * g₀)⁻¹ * t * (c * g₀) = g₀⁻¹ * (c⁻¹ * t * c) * g₀ := by group
      _ = g₀⁻¹ * t * g₀ := by rw [show c⁻¹ * t * c = t by
            calc c⁻¹ * t * c = c⁻¹ * (c * t) := by rw [hct, mul_assoc]
              _ = t := by group]
      _ = u := hg₀
  · calc (c * g₀)⁻¹ * u * (c * g₀) = g₀⁻¹ * (c⁻¹ * u * c) * g₀ := by group
      _ = g₀⁻¹ * v * g₀ := by rw [hcu]
      _ = t := by rw [hv]; group

end CFSG.GH74.E2
