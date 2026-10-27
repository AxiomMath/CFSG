module

public import CFSG.GH74.Uniqueness.SU.SU10Hyp
public import CFSG.GH74.Uniqueness.SU.SU10BenderAbs
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8 CFSG.GH74.Uniqueness.Bender

theorem center_le_sylow {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y)
    (hZ : IsPGroup 2 (center Y)) : center Y ≤ (P : Subgroup Y) := by
  intro g hg
  have hgN : g ∈ normalizer ((P : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : g * h * g⁻¹ = h := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_center_iff.mp hg h).symm
    rw [hc]
  have hmem : g ∈ center Y ⊓ normalizer ((P : Subgroup Y) : Set Y) :=
    Subgroup.mem_inf.mpr ⟨hg, hgN⟩
  have key : center Y ⊓ normalizer ((P : Subgroup Y) : Set Y) = center Y ⊓ (P : Subgroup Y) :=
    hZ.inf_normalizer_sylow P
  rw [key] at hmem
  exact (Subgroup.mem_inf.mp hmem).2

variable {X : Type} [Group X] [Finite X]

theorem twoSz8_config
    (hKI5 : K.KI5) (T : Sylow 2 X) {K₁ : Subgroup X} [K₁.Normal]
    (hK : K.IsTwoSz8 ↥K₁) {w : X} (hw2 : orderOf w = 2) (hwc : ∀ x : X, x * w = w * x)
    (hC : Open.pRank 2 (centralizer (K₁ : Set X)) = 1)
    (hle : Subgroup.closure {g : X | g ∈ (T : Subgroup X) ∧ g * g = 1} ≤ K₁) :
    BarCfg X T K₁ w := by
  classical
  obtain ⟨hq, -, hZcard, ⟨e⟩⟩ := hK
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hwC : w ∈ centralizer (K₁ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hwc h
  have huniq : ∀ q ∈ (T : Subgroup X) ⊓ centralizer (K₁ : Set X), q * q = 1 → q = 1 ∨ q = w := by
    intro q hq' hqq
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      by_contra hqw
      have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hqq) hq1
      have h2 := two_le_pRank_of_commuting_involutions (Q := centralizer (K₁ : Set X)) hq'.2 hwC
        hq2 hw2 hqw (hwc q)
      omega
  have hZp : IsPGroup 2 (center ↥K₁) := IsPGroup.of_card (n := 1) (by rw [hZcard]; simp)
  have hZne : center ↥K₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨-, -, -, -, hsq5, hcomm6⟩ := hKI5 ↥K₁ hq hZp hZne ⟨e⟩
  obtain ⟨ζ, hζ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hζ2 : orderOf (((ζ : ↥(center ↥K₁)) : ↥K₁) : X) = 2 := by
    have hdvd : orderOf ζ ∣ 2 := hZcard ▸ orderOf_dvd_natCard ζ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hζ1
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact h2
  have hζC : (((ζ : ↥(center ↥K₁)) : ↥K₁) : X) ∈ centralizer (K₁ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.mp ζ.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hζw : (((ζ : ↥(center ↥K₁)) : ↥K₁) : X) = w := by
    by_contra hne
    have h2 := two_le_pRank_of_commuting_involutions (Q := centralizer (K₁ : Set X)) hζC hwC hζ2
      hw2 hne (hwc _)
    omega
  have hZx : ∀ c : ↥K₁, c ∈ center ↥K₁ → (c : X) = 1 ∨ (c : X) = w := by
    intro c hc
    have hle' : zpowers w ≤ (center ↥K₁).map K₁.subtype := by
      rw [Subgroup.zpowers_le]
      exact ⟨ζ, ζ.2, hζw⟩
    have hcard : Nat.card ((center ↥K₁).map K₁.subtype) = Nat.card (zpowers w) := by
      rw [Subgroup.card_map_of_injective K₁.subtype_injective, hZcard, Nat.card_zpowers, hw2]
    have heq : zpowers w = (center ↥K₁).map K₁.subtype :=
      Subgroup.eq_of_le_of_card_ge hle' hcard.le
    have hmem : (c : X) ∈ zpowers w := by
      rw [heq]
      exact ⟨c, hc, rfl⟩
    exact mem_zpowers_invol hw2 hmem
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 ↥K₁,
      (Q : Subgroup ↥K₁) = ((T : Subgroup X) ⊓ K₁).subgroupOf K₁ :=
    ⟨sylowIn (isSylowIn_inf_normal T K₁), coe_sylowIn (isSylowIn_inf_normal T K₁)⟩
  let ρ : ↥K₁ →* (↥K₁ ⧸ center ↥K₁) := QuotientGroup.mk' (center ↥K₁)
  have hker : ρ.ker = center ↥K₁ := QuotientGroup.ker_mk' _
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hB : BenderType (↥K₁ ⧸ center ↥K₁) (2 * 1 + 1) 2 1 := BenderType.suzuki 1 le_rfl e
  obtain ⟨-, Z₁, y₁, hZ₁Q, hZ₁el, hZ₁card, hZ₁inv, hy₁N, hy₁tr⟩ :=
    benderType_structure hB (Q.mapSurjective hρsurj)
  have hQt : ((Q.mapSurjective hρsurj : Sylow 2 (↥K₁ ⧸ center ↥K₁)) :
      Subgroup (↥K₁ ⧸ center ↥K₁)) = (Q : Subgroup ↥K₁).map ρ :=
    Sylow.coe_mapSurjective hρsurj Q
  have hZcleQ : center ↥K₁ ≤ (Q : Subgroup ↥K₁) := center_le_sylow Q hZp
  have hZ₀Q : Z₁.comap ρ ≤ (Q : Subgroup ↥K₁) := by
    intro g hg
    have hρg : ρ g ∈ ((Q.mapSurjective hρsurj : Sylow 2 (↥K₁ ⧸ center ↥K₁)) :
        Subgroup (↥K₁ ⧸ center ↥K₁)) := hZ₁Q (Subgroup.mem_comap.mp hg)
    rw [hQt] at hρg
    obtain ⟨r, hr, hrg⟩ := hρg
    have h1 : r⁻¹ * g ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel]
    rw [hker] at h1
    have h2 : g = r * (r⁻¹ * g) := by group
    rw [h2]
    exact (Q : Subgroup ↥K₁).mul_mem hr (hZcleQ h1)
  have hZ₀sq : ∀ g ∈ Z₁.comap ρ, g ^ 2 ∈ center ↥K₁ := by
    intro g hg
    have h1 : ρ g ∈ Z₁ := Subgroup.mem_comap.mp hg
    have h2 : ρ (g ^ 2) = 1 := by
      rw [map_pow]
      exact (SU1.isElemAbelian_iff.mp hZ₁el).2 (ρ g) h1
    have h3 : g ^ 2 ∈ ρ.ker := MonoidHom.mem_ker.mpr h2
    rwa [hker] at h3
  have hZ₀XT : ∀ g ∈ (Z₁.comap ρ).map K₁.subtype, g ∈ (T : Subgroup X) ∧ g * g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    have hgQ : g ∈ (Q : Subgroup ↥K₁) := hZ₀Q hg
    have hgT : (g : X) ∈ (T : Subgroup X) := by
      have h1 := hgQ
      rw [hQ, Subgroup.mem_subgroupOf] at h1
      exact (Subgroup.mem_inf.mp h1).1
    have hg2 : g * g = 1 := by
      have := hsq5 Q g hgQ (hZ₀sq g hg)
      rwa [sq] at this
    show (g : X) ∈ (T : Subgroup X) ∧ (g : X) * (g : X) = 1
    exact ⟨hgT, by simpa using congrArg Subtype.val hg2⟩
  have hinvZ₀ : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ (Z₁.comap ρ).map K₁.subtype := by
    intro t htT htt
    have htK : t ∈ K₁ := hle (Subgroup.subset_closure ⟨htT, htt⟩)
    have htQ : (⟨t, htK⟩ : ↥K₁) ∈ (Q : Subgroup ↥K₁) := by
      rw [hQ, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨htT, htK⟩
    have htt' : (⟨t, htK⟩ : ↥K₁) * ⟨t, htK⟩ = 1 := Subtype.ext htt
    have hρtQ : ρ ⟨t, htK⟩ ∈ ((Q.mapSurjective hρsurj : Sylow 2 (↥K₁ ⧸ center ↥K₁)) :
        Subgroup (↥K₁ ⧸ center ↥K₁)) := by
      rw [hQt]
      exact ⟨⟨t, htK⟩, htQ, rfl⟩
    have hρt : ρ ⟨t, htK⟩ ∈ Z₁ := by
      apply hZ₁inv _ hρtQ
      rw [← map_mul, htt', map_one]
    exact ⟨⟨t, htK⟩, Subgroup.mem_comap.mpr hρt, rfl⟩
  have hΩ : omegaOne (T : Subgroup X) = (Z₁.comap ρ).map K₁.subtype := by
    apply le_antisymm
    · unfold omegaOne
      refine (Subgroup.closure_le _).mpr ?_
      rintro t ⟨htT, htt⟩
      exact hinvZ₀ t htT htt
    · intro g hg
      obtain ⟨hgT, hgg⟩ := hZ₀XT g hg
      exact Subgroup.subset_closure ⟨hgT, hgg⟩
  have hcommT : ∀ a ∈ (T : Subgroup X), ∀ b ∈ (T : Subgroup X), a * a = 1 → b * b = 1 →
      a * b = b * a := by
    intro a ha b hb haa hbb
    obtain ⟨a', ha', ha'a⟩ := hinvZ₀ a ha haa
    obtain ⟨b', hb', hb'b⟩ := hinvZ₀ b hb hbb
    have ha'a' : (a' : X) = a := by simpa using ha'a
    have hb'b' : (b' : X) = b := by simpa using hb'b
    subst ha'a' hb'b'
    have := hcomm6 Q a' (hZ₀Q ha') b' (hZ₀Q hb') (hZ₀sq a' ha') (hZ₀sq b' hb')
    simpa using congrArg Subtype.val this
  refine ⟨huniq, hcommT, fun t ht htt => Subgroup.mem_sup_left (hle (Subgroup.subset_closure ⟨ht, htt⟩)), ?_⟩
  have hZ₀card : Nat.card (Z₁.comap ρ) = 2 * Nat.card Z₁ := by
    have h1 : (Z₁.comap ρ).index = Z₁.index := Subgroup.index_comap_of_surjective Z₁ hρsurj
    have h2 : Nat.card (Z₁.comap ρ) * (Z₁.comap ρ).index = Nat.card ↥K₁ :=
      Subgroup.card_mul_index _
    have h3 : Nat.card Z₁ * Z₁.index = Nat.card (↥K₁ ⧸ center ↥K₁) := Subgroup.card_mul_index _
    have h4 : Nat.card ↥K₁ = Nat.card (↥K₁ ⧸ center ↥K₁) * Nat.card (center ↥K₁) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hpos : 0 < Z₁.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have e1 : Nat.card ↥K₁ = Nat.card (Z₁.comap ρ) * Z₁.index := by
      rw [← h1]
      exact h2.symm
    have e2 : Nat.card ↥K₁ = Nat.card Z₁ * Z₁.index * 2 := by
      rw [h4, ← h3, hZcard]
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← e1, e2]; ring)
  obtain ⟨yt, hyt⟩ := hρsurj y₁
  have hytN : yt ∈ normalizer ((Z₁.comap ρ : Subgroup ↥K₁) : Set ↥K₁) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp hy₁N (ρ g)
    have h2 : ρ (yt * g * yt⁻¹) = y₁ * ρ g * y₁⁻¹ := by
      rw [map_mul, map_mul, map_inv, hyt]
    rw [Subgroup.mem_comap, Subgroup.mem_comap, h2]
    exact h1
  refine ⟨2 * 1 + 1, ((yt : ↥K₁) : X), by norm_num, ?_, ?_, hwc _, ?_⟩
  · rw [hΩ, Subgroup.card_map_of_injective K₁.subtype_injective, hZ₀card, hZ₁card]
    norm_num
  · rw [hΩ]
    exact Subgroup.le_normalizer_map K₁.subtype ⟨yt, hytN, rfl⟩
  · intro a ha b hb ha1 haw hb1 hbw
    rw [hΩ] at ha hb
    obtain ⟨a', ha', ha'a⟩ := ha
    obtain ⟨b', hb', hb'b⟩ := hb
    have ha'a' : (a' : X) = a := by simpa using ha'a
    have hb'b' : (b' : X) = b := by simpa using hb'b
    subst ha'a' hb'b'
    have hρ1 : ∀ c : ↥K₁, (c : X) ≠ 1 → (c : X) ≠ w → c ∈ Z₁.comap ρ → ρ c ≠ 1 := by
      intro c hc1 hcw _ h
      have hcZ : c ∈ center ↥K₁ := by
        have h3 : c ∈ ρ.ker := MonoidHom.mem_ker.mpr h
        rwa [hker] at h3
      rcases hZx c hcZ with h' | h'
      · exact hc1 h'
      · exact hcw h'
    obtain ⟨j, hj⟩ := hy₁tr (ρ a') (Subgroup.mem_comap.mp ha') (ρ b') (Subgroup.mem_comap.mp hb')
      (hρ1 a' ha1 haw ha') (hρ1 b' hb1 hbw hb')
    refine ⟨j, ?_⟩
    have hρj : ρ (yt ^ j * a' * (yt ^ j)⁻¹) = ρ b' := by
      simp only [map_mul, map_zpow, map_inv, hyt]
      exact hj
    have hmem : (yt ^ j * a' * (yt ^ j)⁻¹)⁻¹ * b' ∈ center ↥K₁ := by
      have h3 : (yt ^ j * a' * (yt ^ j)⁻¹)⁻¹ * b' ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρj, inv_mul_cancel]
      rwa [hker] at h3
    rcases hZx _ hmem with h | h
    · left
      have h1 : (yt ^ j * a' * (yt ^ j)⁻¹)⁻¹ * b' = 1 := Subtype.ext h
      have h2 := inv_mul_eq_one.mp h1
      simpa using congrArg Subtype.val h2
    · right
      have hbU : b' = (yt ^ j * a' * (yt ^ j)⁻¹) * ((yt ^ j * a' * (yt ^ j)⁻¹)⁻¹ * b') := by group
      have h1 := congrArg Subtype.val hbU
      rw [Subgroup.coe_mul, h] at h1
      push_cast at h1
      calc (yt : X) ^ j * (a' : X) * ((yt : X) ^ j)⁻¹
          = ((yt : X) ^ j * (a' : X) * ((yt : X) ^ j)⁻¹) * (w * w) := by rw [hww, mul_one]
        _ = (b' : X) * w := by rw [h1]; group

end CFSG.GH74.Uniqueness.SU.SU10
