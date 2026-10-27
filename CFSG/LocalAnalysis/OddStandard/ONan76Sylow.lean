module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.OddStandard.ONan76

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le {K P Q : Subgroup G} (hP : IsSylowOf 2 P K) (hQK : Q ≤ K)
    (hQ : IsPGroup 2 Q) : ∃ c ∈ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R P₀
  refine ⟨c, c.2, fun q hq => ?_⟩
  have h1 : MulAut.conj c • (⟨q, hQK hq⟩ : K) ∈ MulAut.conj c • (R : Subgroup K) :=
    smul_mem_pointwise_smul _ (MulAut.conj c) (R : Subgroup K) (hR (mem_subgroupOf.mpr hq))
  rw [← Sylow.coe_subgroup_smul, hc, hP₀, mem_subgroupOf] at h1
  exact h1

theorem exists_isSylowOf_ge {K Q : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup G, IsSylowOf 2 T K ∧ Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  refine ⟨(R : Subgroup K).map K.subtype, ⟨R, rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQK hq⟩, hR (mem_subgroupOf.mpr hq), rfl⟩

theorem exists_conj_eq {K P P' : Subgroup G} (hP : IsSylowOf 2 P K) (hP' : IsSylowOf 2 P' K) :
    ∃ c ∈ K, ∀ x : G, x ∈ P' ↔ c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcK, hc⟩ := exists_conj_le hP hP'.le hP'.isPGroup
  have hle : P'.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact hc q hq
  have heq : P'.map (MulAut.conj c).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj c).injective, hP.card_eq, hP'.card_eq])
  refine ⟨c, hcK, fun x => ⟨fun hx => hc x hx, fun hx => ?_⟩⟩
  rw [← heq] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  have : q = x := by
    have h := congrArg (fun y => c⁻¹ * y * c) hqx
    simpa [mul_assoc] using h
  rwa [← this]

theorem exists_mul_mem_normalizer {L N P : Subgroup G} (hLN : L ≤ normalizer (N : Set G))
    (hP : IsSylowOf 2 P N) {u : G} (hu : u ∈ L) : ∃ c ∈ N, u * c ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P'' := P.map (MulAut.conj u⁻¹).toMonoidHom
  have hu' : u⁻¹ ∈ normalizer (N : Set G) := inv_mem (hLN hu)
  have hP''N : P'' ≤ N := by
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_normalizer_iff.mp hu' p).mp (hP.le hp)
  have hP'' : IsSylowOf 2 P'' N :=
    isSylowOf_of_card hP''N (by rw [card_map_of_injective (MulAut.conj u⁻¹).injective, hP.card_eq])
  obtain ⟨c', hc'N, hc'⟩ := exists_conj_eq hP hP''
  refine ⟨c'⁻¹, inv_mem hc'N, mem_normalizer_iff.mpr fun x => ?_⟩
  have key : ∀ y : G, y ∈ P'' ↔ u * y * u⁻¹ ∈ P := by
    intro y
    constructor
    · rintro ⟨p, hp, rfl⟩
      change u * (u⁻¹ * p * u⁻¹⁻¹) * u⁻¹ ∈ P
      rwa [show u * (u⁻¹ * p * u⁻¹⁻¹) * u⁻¹ = p by group]
    · intro hy
      exact ⟨u * y * u⁻¹, hy, by change u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y; group⟩
  rw [show u * c'⁻¹ * x * (u * c'⁻¹)⁻¹ = u * (c'⁻¹ * x * c') * u⁻¹ by group, ← key,
    hc', show c' * (c'⁻¹ * x * c') * c'⁻¹ = x by group]

theorem isSylowOf_map_conj {P K : Subgroup G} (hP : IsSylowOf 2 P K) (c : G) :
    IsSylowOf 2 (P.map (MulAut.conj c).toMonoidHom) (K.map (MulAut.conj c).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hp, hdvd⟩ := hP
  refine ⟨map_mono hle, hp.map _, ?_⟩
  have hker : (MulAut.conj c).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj c).injective
  rw [relIndex_map_map, hker, sup_bot_eq, sup_bot_eq]
  exact hdvd

theorem le_of_isSylowOf {P K F : Subgroup G} (hP : IsSylowOf 2 P K) (hFK : F ≤ K)
    (hF : IsPGroup 2 F) (hKF : K ≤ normalizer (F : Set G)) : F ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (F ⊔ P : Subgroup G) :=
    hF.to_sup_of_normal_left' hP.isPGroup (hP.le.trans hKF)
  have heq := hP.eq_of_le le_sup_right (sup_le hFK hP.le) hsup
  rw [← heq]
  exact le_sup_left

end Sylow

theorem eq_of_sylow_image {N M : Type*} [Group N] [Finite N] [Group M] (ρ : N →* M)
    (T : Sylow 2 N)
    (hT : ∀ a ∈ (T : Subgroup N), ∀ b ∈ (T : Subgroup N), ρ a ^ 2 = 1 → ρ b ^ 2 = 1 →
      ρ a ≠ 1 → ρ b ≠ 1 → ρ a = ρ b)
    {x y : N} (hx : ρ x ^ 2 = 1) (hy : ρ y ^ 2 = 1) (hxy : ρ x * ρ y = ρ y * ρ x)
    (hx1 : ρ x ≠ 1) (hy1 : ρ y ≠ 1) : ρ x = ρ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have : Finite ρ.range := Finite.of_surjective _ hf
  set T' : Sylow 2 ρ.range := T.mapSurjective hf
  set a : ρ.range := ρ.rangeRestrict x with ha
  set b : ρ.range := ρ.rangeRestrict y with hb
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa [ha] using hx)
  have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa [hb] using hy)
  have hab : a * b = b * a := Subtype.ext (by simpa [ha, hb] using hxy)
  have hpg : ∀ c : ρ.range, c ^ 2 = 1 → IsPGroup 2 (zpowers c) := by
    intro c hc
    have hdvd : orderOf c ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa using hc)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hnorm : zpowers b ≤ normalizer (zpowers a : Set ρ.range) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have hQ : IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup ρ.range) :=
    (hpg a ha2).to_sup_of_normal_left' (hpg b hb2) hnorm
  obtain ⟨Q, hQ⟩ := hQ.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ρ.range T' Q
  have key : ∀ c : ρ.range, c ∈ zpowers a ⊔ zpowers b →
      ∃ s ∈ (T : Subgroup N), ρ.rangeRestrict s = h⁻¹ * c * h := by
    intro c hc
    have hmem : c ∈ ((h • T' : Sylow 2 ρ.range) : Subgroup ρ.range) := by
      rw [hh]
      exact hQ hc
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hmem
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hmem
    refine ⟨s, hs, ?_⟩
    rw [hsy, MulAut.smul_def, MulAut.conj_inv_apply]
  obtain ⟨s₁, hs₁, h₁⟩ := key a (mem_sup_left (mem_zpowers a))
  obtain ⟨s₂, hs₂, h₂⟩ := key b (mem_sup_right (mem_zpowers b))
  have hval : ∀ s : N, (ρ.rangeRestrict s : M) = ρ s := fun s => rfl
  have hsq : ∀ (s : N) (c : ρ.range), ρ.rangeRestrict s = h⁻¹ * c * h → c ^ 2 = 1 →
      ρ s ^ 2 = 1 := by
    intro s c hs hc
    have : ρ.rangeRestrict s ^ 2 = 1 := by
      rw [hs, pow_two, show h⁻¹ * c * h * (h⁻¹ * c * h) = h⁻¹ * (c ^ 2) * h by
        rw [pow_two]; group, hc]
      group
    simpa [hval] using congrArg Subtype.val this
  have hne : ∀ (s : N) (c : ρ.range), ρ.rangeRestrict s = h⁻¹ * c * h → c ≠ 1 → ρ s ≠ 1 := by
    intro s c hs hc h1
    apply hc
    have : ρ.rangeRestrict s = 1 := Subtype.ext (by simpa [hval] using h1)
    rw [hs] at this
    calc c = h * (h⁻¹ * c * h) * h⁻¹ := by group
      _ = 1 := by rw [this]; group
  have ha1 : a ≠ 1 := fun h' => hx1 (by simpa [ha] using congrArg Subtype.val h')
  have hb1 : b ≠ 1 := fun h' => hy1 (by simpa [hb] using congrArg Subtype.val h')
  have heq := hT s₁ hs₁ s₂ hs₂ (hsq s₁ a h₁ ha2) (hsq s₂ b h₂ hb2) (hne s₁ a h₁ ha1)
    (hne s₂ b h₂ hb1)
  have heq' : ρ.rangeRestrict s₁ = ρ.rangeRestrict s₂ := Subtype.ext heq
  rw [h₁, h₂] at heq'
  have hab' : a = b := by
    have := congrArg (fun c => h * c * h⁻¹) heq'
    simpa [mul_assoc] using this
  simpa [ha, hb] using congrArg Subtype.val hab'

end CFSG.OddStandard.ONan76
