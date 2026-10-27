module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.Foote81L6.Fusion3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mem_sylow_inv_mul_mem (K : Subgroup G) [K.Normal]
    (hK : ∀ g : G, Odd (orderOf g) → g ∈ K) (P : Sylow 2 G) (g : G) :
    ∃ p ∈ (P : Subgroup G), p⁻¹ * g ∈ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have h2 : IsPGroup 2 (G ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := hsurj q
    obtain ⟨e, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨e, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply hK
    rw [orderOf_pow_of_dvd (pow_ne_zero e two_ne_zero) ⟨r, hord⟩, hord,
      Nat.mul_div_cancel_left r (pow_pos two_pos e)]
    exact hr
  set P' := P.mapSurjective hsurj
  have htop : (P' : Subgroup (G ⧸ K)) = ⊤ :=
    (P'.is_maximal' (h2.to_subgroup ⊤) le_top).symm
  have hg : QuotientGroup.mk' K g ∈ (P' : Subgroup (G ⧸ K)) := by
    rw [htop]
    exact mem_top _
  rw [Sylow.coe_mapSurjective] at hg
  obtain ⟨p, hp, hpg⟩ := hg
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hpg
  exact ⟨p, hp, QuotientGroup.eq.1 hpg⟩

theorem exists_conj_eq_of_odd (T : Sylow 2 G) {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    {Ω : Set G} (hΩ : ∀ h ∈ H, ∀ ω ∈ Ω, h * ω * h⁻¹ ∈ Ω)
    (hodd : ∀ h ∈ H, Odd (orderOf h) → ∀ ω ∈ Ω, h * ω * h⁻¹ = ω) {g : G} (hg : g ∈ H) :
    ∃ u ∈ (T : Subgroup G), ∀ ω ∈ Ω, g * ω * g⁻¹ = u * ω * u⁻¹ := by
  let K : Subgroup ↥H :=
    { carrier := {k | ∀ ω ∈ Ω, (k : G) * ω * (k : G)⁻¹ = ω}
      one_mem' := fun ω _ => by simp
      mul_mem' := fun {k₁ k₂} h₁ h₂ ω hω => by
        show (k₁ : G) * k₂ * ω * ((k₁ : G) * k₂)⁻¹ = ω
        calc (k₁ : G) * k₂ * ω * ((k₁ : G) * k₂)⁻¹
            = k₁ * ((k₂ : G) * ω * (k₂ : G)⁻¹) * (k₁ : G)⁻¹ := by group
          _ = ω := by rw [h₂ ω hω, h₁ ω hω]
      inv_mem' := fun {k} hk ω hω => by
        show (k : G)⁻¹ * ω * ((k : G)⁻¹)⁻¹ = ω
        calc (k : G)⁻¹ * ω * ((k : G)⁻¹)⁻¹ = (k : G)⁻¹ * ((k : G) * ω * (k : G)⁻¹) * k := by
              rw [hk ω hω]; group
          _ = ω := by group }
  have hKmem : ∀ k : ↥H, k ∈ K ↔ ∀ ω ∈ Ω, (k : G) * ω * (k : G)⁻¹ = ω := fun _ => Iff.rfl
  haveI : K.Normal := ⟨fun k hk h => by
    rw [hKmem] at hk ⊢
    intro ω hω
    have h1 : (h : G)⁻¹ * ω * h ∈ Ω := by
      have := hΩ _ (inv_mem h.2) ω hω
      rwa [inv_inv] at this
    have h2 := hk _ h1
    simp only [coe_mul, coe_inv]
    calc (h : G) * k * (h : G)⁻¹ * ω * ((h : G) * k * (h : G)⁻¹)⁻¹
        = h * ((k : G) * ((h : G)⁻¹ * ω * h) * (k : G)⁻¹) * (h : G)⁻¹ := by group
      _ = ω := by rw [h2]; group⟩
  have hKodd : ∀ k : ↥H, Odd (orderOf k) → k ∈ K := fun k hk =>
    (hKmem k).2 (hodd k k.2 (by rwa [orderOf_coe]))
  obtain ⟨p, hp, hpK⟩ := exists_mem_sylow_inv_mul_mem K hKodd (T.subtype hTH) ⟨g, hg⟩
  rw [Sylow.coe_subtype, mem_subgroupOf] at hp
  refine ⟨p, hp, fun ω hω => ?_⟩
  have h := (hKmem _).1 hpK ω hω
  simp only [coe_mul, coe_inv] at h
  calc g * ω * g⁻¹ = (p : G) * ((p : G)⁻¹ * g * ω * ((p : G)⁻¹ * g)⁻¹) * (p : G)⁻¹ := by group
    _ = p * ω * (p : G)⁻¹ := by rw [h]

theorem exists_conj_eq_and_conj_le {p : ℕ} [Fact p.Prime] {P Q : Subgroup G} {x y g : G}
    (hg : g * x * g⁻¹ = y)
    (hP : ∃ SK : Sylow p ↥(centralizer ({x} : Set G)),
      (SK : Subgroup _) = P.subgroupOf (centralizer ({x} : Set G)))
    (hQ : IsPGroup p Q) (hQy : Q ≤ centralizer ({y} : Set G)) :
    ∃ h : G, h * x * h⁻¹ = y ∧ ∀ q ∈ Q, h⁻¹ * q * h ∈ P := by
  obtain ⟨SK, hSK⟩ := hP
  have hmemC : ∀ q ∈ Q, g⁻¹ * q * g ∈ centralizer ({x} : Set G) := by
    intro q hq
    rw [mem_centralizer_singleton_iff]
    have h1 : q * y = y * q := mem_centralizer_singleton_iff.1 (hQy hq)
    rw [← hg] at h1
    calc g⁻¹ * q * g * x = g⁻¹ * (q * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * q) * g := by rw [h1]
      _ = x * (g⁻¹ * q * g) := by group
  set Q' : Subgroup ↥(centralizer ({x} : Set G)) :=
    (Q.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (centralizer ({x} : Set G))
  have hQ' : IsPGroup p Q' := (hQ.map _).comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(centralizer ({x} : Set G)) S SK
  refine ⟨g * (c : G)⁻¹, ?_, fun q hq => ?_⟩
  · have hcx : (c : G) * x = x * c := mem_centralizer_singleton_iff.1 c.2
    calc g * (c : G)⁻¹ * x * (g * (c : G)⁻¹)⁻¹ = g * ((c : G)⁻¹ * (x * c)) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [← hcx]; group
      _ = y := hg
  · have hq' : (⟨g⁻¹ * q * g, hmemC q hq⟩ : ↥(centralizer ({x} : Set G))) ∈ Q' := by
      rw [mem_subgroupOf]
      exact ⟨q, hq, by simp [MulAut.conj_apply]⟩
    have hmem : c * ⟨g⁻¹ * q * g, hmemC q hq⟩ * c⁻¹ ∈ (SK : Subgroup _) := by
      rw [← hc, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists]
      exact ⟨_, hS hq', rfl⟩
    rw [hSK, mem_subgroupOf] at hmem
    simp only [coe_mul, coe_inv] at hmem
    convert hmem using 1
    group

private theorem card_le_two_mul_of_cosets {T C : Subgroup G} (hCT : C ≤ T)
    (h : ∀ u ∈ T, ∀ v ∈ T, u ∉ C → v ∉ C → u⁻¹ * v ∈ C) : Nat.card T ≤ 2 * Nat.card C := by
  set C' : Subgroup ↥T := C.subgroupOf T
  have hC' : Nat.card C' = Nat.card C := Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv
  have hidx : C'.index ≤ 2 := by
    by_cases hall : ∀ u ∈ T, u ∈ C
    · have htop : C' = ⊤ := by
        ext ⟨u, hu⟩
        simp only [C', mem_subgroupOf, mem_top, iff_true]
        exact hall u hu
      rw [htop, index_top]
      norm_num
    · push Not at hall
      obtain ⟨u₀, hu₀T, hu₀C⟩ := hall
      rw [index_eq_card]
      have hsurj : Function.Surjective fun b : Bool =>
          if b then ((⟨u₀, hu₀T⟩ : ↥T) : ↥T ⧸ C') else ((1 : ↥T) : ↥T ⧸ C') := by
        intro q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        by_cases hv : (v : G) ∈ C
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true, if_false]
          rw [QuotientGroup.eq, mem_subgroupOf]
          simpa using hv
        · refine ⟨true, ?_⟩
          simp only [if_true]
          rw [QuotientGroup.eq, mem_subgroupOf]
          simpa using h u₀ hu₀T v v.2 hu₀C hv
      have := Nat.card_le_card_of_surjective _ hsurj
      simpa using this
  calc Nat.card T = Nat.card C' * C'.index := C'.card_mul_index.symm
    _ ≤ Nat.card C * 2 := by rw [hC']; exact Nat.mul_le_mul_left _ hidx
    _ = 2 * Nat.card C := mul_comm _ _

theorem exists_conj_comm_of_not_sylow (T : Sylow 2 G) {x : G} (hxT : x ∈ (T : Subgroup G))
    (hcos : ∀ u ∈ (T : Subgroup G), ∀ v ∈ (T : Subgroup G),
      u ∉ (T : Subgroup G) ⊓ centralizer ({x} : Set G) →
      v ∉ (T : Subgroup G) ⊓ centralizer ({x} : Set G) →
      u⁻¹ * v ∈ (T : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hns : ¬ ∃ SK : Sylow 2 ↥(centralizer ({x} : Set G)),
      (SK : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({x} : Set G))) :
    ∃ k : G, k * x * k⁻¹ ∈ (T : Subgroup G) ∧
      ∀ u ∈ (T : Subgroup G), u * (k * x * k⁻¹) = (k * x * k⁻¹) * u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := card_le_two_mul_of_cosets inf_le_left hcos
  set Q : Subgroup ↥(centralizer ({x} : Set G)) :=
    (T : Subgroup G).subgroupOf (centralizer ({x} : Set G))
  have hQ : IsPGroup 2 Q := T.isPGroup'.comap_subtype
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hne : (S : Subgroup ↥(centralizer ({x} : Set G))) ≠ Q := fun h => hns ⟨S, h⟩
  have hcardQ : Nat.card Q = Nat.card ↥((T : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
    rw [← subgroupOf_map_subtype]
    exact (card_map_of_injective (subtype_injective _)).symm
  have hlt : Nat.card Q < Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) := by
    by_contra hle
    push Not at hle
    exact hne (eq_of_le_of_card_ge hQS hle).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 S.isPGroup'
  have hdvd : Nat.card Q ∣ Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) :=
    card_dvd_of_le hQS
  rw [hk] at hdvd hlt
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hjeq] at hlt
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have h2Q : 2 * Nat.card Q ≤ Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) := by
    rw [hk, hjeq, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hjk
  set S' : Subgroup G :=
    (S : Subgroup ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype
  have hS'card : Nat.card S' = Nat.card (S : Subgroup ↥(centralizer ({x} : Set G))) :=
    card_map_of_injective (subtype_injective _)
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'C : S' ≤ centralizer ({x} : Set G) := map_subtype_le _
  have hxS' : x ∈ S' :=
    ⟨⟨x, mem_centralizer_singleton_iff.2 rfl⟩, hQS (by rw [mem_subgroupOf]; exact hxT), rfl⟩
  obtain ⟨P, hP⟩ := hS'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  have hconj : ∀ y ∈ S', g * y * g⁻¹ ∈ (T : Subgroup G) := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists]
    exact ⟨y, hP hy, rfl⟩
  have hle : S'.map (MulAut.conj g).toMonoidHom ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have heq : S'.map (MulAut.conj g).toMonoidHom = T := by
    refine eq_of_le_of_card_ge hle ?_
    rw [card_map_of_injective (MulAut.conj g).injective, hS'card]
    calc Nat.card (T : Subgroup G)
        ≤ 2 * Nat.card ↥((T : Subgroup G) ⊓ centralizer ({x} : Set G)) := hidx
      _ = 2 * Nat.card Q := by rw [hcardQ]
      _ ≤ _ := h2Q
  refine ⟨g, hconj x hxS', fun u hu => ?_⟩
  rw [← heq] at hu
  obtain ⟨y, hy, rfl⟩ := hu
  have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 (hS'C hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
    _ = g * (x * y) * g⁻¹ := by rw [hyx]
    _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

end CFSG.CGT.Foote81L6.Fusion3
