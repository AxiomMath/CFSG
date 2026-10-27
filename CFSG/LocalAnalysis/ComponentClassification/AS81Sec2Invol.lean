module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SCoord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

section Small

open Equiv

local instance decEqPerm5 : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

local instance decMemAlt5 : DecidablePred (fun σ : Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Perm.sign.decidableMemKer

theorem perm3_conj : ∀ τ σ : Perm (Fin 3), τ ^ 2 = 1 → τ ≠ 1 → σ ^ 3 = 1 → σ ≠ 1 →
    τ * σ * τ⁻¹ = σ⁻¹ := by
  decide

@[expose] def TwoInv (τ τ' : Perm (Fin 3)) : Prop :=
  τ ^ 2 = 1 ∧ τ' ^ 2 = 1 ∧ τ ≠ 1 ∧ τ' ≠ 1 ∧ τ ≠ τ'

local instance (τ τ' : Perm (Fin 3)) : Decidable (TwoInv τ τ') := by
  unfold TwoInv
  infer_instance

theorem perm3_mul' : ∀ τ τ' : Perm (Fin 3), TwoInv τ τ' → (τ * τ') ^ 3 = 1 ∧ τ * τ' ≠ 1 := by
  decide

theorem perm3_mul {τ τ' : Perm (Fin 3)} (h1 : τ ^ 2 = 1) (h2 : τ' ^ 2 = 1) (h3 : τ ≠ 1)
    (h4 : τ' ≠ 1) (h5 : τ ≠ τ') : (τ * τ') ^ 3 = 1 ∧ τ * τ' ≠ 1 :=
  perm3_mul' τ τ' ⟨h1, h2, h3, h4, h5⟩

theorem perm3_ne : ∀ σ : Perm (Fin 3), σ ^ 3 = 1 → σ ^ 2 = 1 → σ = 1 := by
  decide

theorem perm3_sq_of_sign : ∀ σ : Perm (Fin 3), Perm.sign σ ≠ 1 → σ ^ 2 = 1 ∧ σ ≠ 1 := by
  decide

theorem perm3_sign_of_cube : ∀ σ : Perm (Fin 3), σ ^ 3 = 1 → Perm.sign σ = 1 := by
  decide

@[expose] def NoSix (a c : Perm (Fin 5)) : Prop :=
  a ∈ alternatingGroup (Fin 5) → c ∈ alternatingGroup (Fin 5) → a ^ 2 = 1 → c ^ 3 = 1 → c ≠ 1 →
    a * c = c * a → a = 1

local instance (a c : Perm (Fin 5)) : Decidable (NoSix a c) := by
  unfold NoSix
  infer_instance

theorem noSix : ∀ a c : Perm (Fin 5), NoSix a c := by
  decide +kernel

@[expose] def CentTriv (a : Perm (Fin 5)) : Prop :=
  a * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * a →
    a * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * a → a = 1

local instance (a : Perm (Fin 5)) : Decidable (CentTriv a) := by
  unfold CentTriv
  infer_instance

theorem centTriv : ∀ a : Perm (Fin 5), CentTriv a := by
  decide +kernel

theorem mem_alt_c1 : (swap (0 : Fin 5) 1 * swap 1 2) ∈ alternatingGroup (Fin 5) := by decide

theorem mem_alt_c2 : (swap (2 : Fin 5) 3 * swap 3 4) ∈ alternatingGroup (Fin 5) := by decide

theorem alt5_eq_one_of_comm {a : alternatingGroup (Fin 5)} (h : ∀ b, a * b = b * a) : a = 1 := by
  apply Subtype.ext
  apply centTriv a
  · exact congrArg Subtype.val (h ⟨_, mem_alt_c1⟩)
  · exact congrArg Subtype.val (h ⟨_, mem_alt_c2⟩)

theorem alt5_eq_one_of_comm_three {a c : alternatingGroup (Fin 5)} (ha : a ^ 2 = 1)
    (hc : c ^ 3 = 1) (hc1 : c ≠ 1) (hac : a * c = c * a) : a = 1 := by
  apply Subtype.ext
  exact noSix a c a.2 c.2 (congrArg Subtype.val ha) (congrArg Subtype.val hc)
    (fun h => hc1 (Subtype.ext h)) (congrArg Subtype.val hac)

theorem card_le_four_of_isPGroup {D : Subgroup (alternatingGroup (Fin 5))} (hD : IsPGroup 2 D) :
    Nat.card D ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hdvd : 2 ^ k ∣ 60 := hk ▸ card_alternatingGroup_five ▸ Subgroup.card_subgroup_dvd_card D
  rw [hk]
  have : k ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    _ = 4 := by norm_num

end Small

section Quot

variable {G : Type} [Group G] {S Z H T : Subgroup G} {x : G} (C : Coord S Z H)
  {θ : ↥(H ⊔ zpowers x ⊔ T) →* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)}
  (hθ : Function.Surjective θ) (hker : θ.ker = S.subgroupOf (H ⊔ zpowers x ⊔ T))

theorem H_le_K : H ≤ H ⊔ zpowers x ⊔ T := le_sup_left.trans le_sup_left

theorem T_le_K : T ≤ H ⊔ zpowers x ⊔ T := le_sup_right

theorem x_mem_K : x ∈ H ⊔ zpowers x ⊔ T :=
  (le_sup_right.trans le_sup_left : zpowers x ≤ H ⊔ zpowers x ⊔ T) (mem_zpowers x)

include hker in
theorem mem_ker_iff {k : ↥(H ⊔ zpowers x ⊔ T)} : θ k = 1 ↔ (k : G) ∈ S := by
  rw [← MonoidHom.mem_ker, hker]
  rfl

include C hker in
theorem θ_fst_H {h : G} (hh : h ∈ H) : (θ ⟨h, H_le_K hh⟩).1 = 1 := by
  let ρ : ↥H →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (θ.comp (Subgroup.inclusion H_le_K))
  have hSρ : C.φ.ker ≤ ρ.ker := by
    intro k hk
    rw [C.ker] at hk
    rw [MonoidHom.mem_ker]
    have : θ (Subgroup.inclusion H_le_K k) = 1 := (mem_ker_iff hker).mpr hk
    show (θ (Subgroup.inclusion H_le_K k)).1 = 1
    rw [this]
    rfl
  have hnorm : (ρ.ker.map C.φ).Normal := (MonoidHom.normal_ker ρ).map C.φ C.surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map C.φ) with h0 | h0
  · exfalso
    rw [Subgroup.map_eq_bot_iff] at h0
    have h1 := Subgroup.index_dvd_of_le h0
    rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.surj,
      Subgroup.card_top, card_alternatingGroup_five] at h1
    have h2 : Nat.card ρ.range ≤ 6 := by
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have := Nat.le_of_dvd Nat.card_pos h1
    omega
  · have hmem : C.φ ⟨h, hh⟩ ∈ ρ.ker.map C.φ := by
      rw [h0]
      exact mem_top _
    obtain ⟨k, hk, hkh⟩ := hmem
    have hk' : k⁻¹ * ⟨h, hh⟩ ∈ C.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkh, inv_mul_cancel]
    have hmem' : k * (k⁻¹ * ⟨h, hh⟩) ∈ ρ.ker := ρ.ker.mul_mem hk (hSρ hk')
    rw [mul_inv_cancel_left] at hmem'
    exact hmem'

include C hker in
theorem exists_θ_eq (a : alternatingGroup (Fin 5)) :
    ∃ h, ∃ hh : h ∈ H, θ ⟨h, H_le_K hh⟩ = (1, a) := by
  let ρ : ↥H →* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5) :=
    θ.comp (Subgroup.inclusion H_le_K)
  have hkerρ : ρ.ker = C.φ.ker := by
    ext k
    rw [MonoidHom.mem_ker, C.ker]
    exact mem_ker_iff hker
  have hcard : Nat.card ρ.range = 60 := by
    rw [← Subgroup.index_ker, hkerρ, Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.surj,
      Subgroup.card_top, card_alternatingGroup_five]
  have hle : ρ.range ≤ (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
    rintro _ ⟨k, rfl⟩
    exact ⟨θ_fst_H C hker k.2, mem_top _⟩
  have hcard' : Nat.card ((⊥ : Subgroup (Equiv.Perm (Fin 3))).prod
      (⊤ : Subgroup (alternatingGroup (Fin 5)))) = 60 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      Subgroup.card_top, card_alternatingGroup_five, one_mul]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])
  have hmem : ((1, a) : Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)) ∈ ρ.range := by
    rw [heq]
    exact ⟨mem_bot.mpr rfl, mem_top _⟩
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, k.2, hk⟩

include C hker in
theorem mem_H_of_θ_fst (hSH : S ≤ H) {k : ↥(H ⊔ zpowers x ⊔ T)} (hk : (θ k).1 = 1) :
    (k : G) ∈ H := by
  obtain ⟨h, hh, hθh⟩ := exists_θ_eq C hker (θ k).2
  have h1 : θ (k * (⟨h, H_le_K hh⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hθh]
    exact Prod.ext (by simp [hk]) (by simp)
  have h2 : (k : G) * h⁻¹ ∈ S := (mem_ker_iff hker).mp h1
  have e : (k : G) = ((k : G) * h⁻¹) * h := by group
  rw [e]
  exact H.mul_mem (hSH h2) hh

include C hker in
theorem θ_x (hS2 : IsPGroup 2 S) (hx3 : orderOf x = 3)
    (hxH : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S) :
    (θ ⟨x, x_mem_K⟩).2 = 1 ∧ (θ ⟨x, x_mem_K⟩).1 ^ 3 = 1 ∧ (θ ⟨x, x_mem_K⟩).1 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_⟩
  · apply alt5_eq_one_of_comm
    intro b
    obtain ⟨h, hh, hθh⟩ := exists_θ_eq C hker b
    have h1 : θ (⟨x, x_mem_K⟩⁻¹ * (⟨h, H_le_K hh⟩)⁻¹ * ⟨x, x_mem_K⟩ * ⟨h, H_le_K hh⟩) = 1 :=
      (mem_ker_iff hker).mpr (hxH h hh)
    simp only [map_mul, map_inv, hθh] at h1
    have h2 := congrArg Prod.snd h1
    simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one] at h2
    calc (θ ⟨x, x_mem_K⟩).2 * b = b * (θ ⟨x, x_mem_K⟩).2 * ((θ ⟨x, x_mem_K⟩).2⁻¹ * b⁻¹ *
          (θ ⟨x, x_mem_K⟩).2 * b) := by group
      _ = b * (θ ⟨x, x_mem_K⟩).2 := by rw [h2, mul_one]
  · have h := congrArg Prod.fst (congrArg θ (show (⟨x, x_mem_K⟩ : ↥(H ⊔ zpowers x ⊔ T)) ^ 3 = 1
      from Subtype.ext (by rw [Subgroup.coe_pow, ← hx3, pow_orderOf_eq_one]; rfl)))
    rw [map_pow, map_one] at h
    exact h
  · intro h1
    have hθx : θ ⟨x, x_mem_K⟩ = 1 := Prod.ext h1 (by
      apply alt5_eq_one_of_comm
      intro b
      obtain ⟨h, hh, hθh⟩ := exists_θ_eq C hker b
      have h1 : θ (⟨x, x_mem_K⟩⁻¹ * (⟨h, H_le_K hh⟩)⁻¹ * ⟨x, x_mem_K⟩ * ⟨h, H_le_K hh⟩) = 1 :=
        (mem_ker_iff hker).mpr (hxH h hh)
      simp only [map_mul, map_inv, hθh] at h1
      have h2 := congrArg Prod.snd h1
      simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one] at h2
      calc (θ ⟨x, x_mem_K⟩).2 * b = b * (θ ⟨x, x_mem_K⟩).2 * ((θ ⟨x, x_mem_K⟩).2⁻¹ * b⁻¹ *
            (θ ⟨x, x_mem_K⟩).2 * b) := by group
        _ = b * (θ ⟨x, x_mem_K⟩).2 := by rw [h2, mul_one])
    have hxS : x ∈ S := (mem_ker_iff hker).mp hθx
    obtain ⟨k, hk⟩ := hS2 ⟨x, hxS⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd)
    omega

include C hθ hker in
theorem exists_t₀ (hS2 : IsPGroup 2 S) (hT2 : IsPGroup 2 T) (hx3 : orderOf x = 3)
    (hxH : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S) {P : Subgroup G} (hPT : P ≤ T) (hPH : P ≤ H)
    (hP4 : (P ⊓ S).relIndex P = 4) :
    ∃ t₀, ∃ ht₀ : t₀ ∈ T, (θ ⟨t₀, T_le_K ht₀⟩).1 ^ 2 = 1 ∧ (θ ⟨t₀, T_le_K ht₀⟩).1 ≠ 1 ∧
      (θ ⟨t₀, T_le_K ht₀⟩).2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ', hτ', hsign⟩ : ∃ τ', ∃ hτ' : τ' ∈ T, Equiv.Perm.sign (θ ⟨τ', T_le_K hτ'⟩).1 ≠ 1 := by
    by_contra hall
    push Not at hall
    let K₃ : Subgroup ↥(H ⊔ zpowers x ⊔ T) :=
      (Equiv.Perm.sign.ker).comap ((MonoidHom.fst _ _).comp θ)
    have hK₃ : H ⊔ zpowers x ⊔ T ≤ K₃.map (H ⊔ zpowers x ⊔ T).subtype := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro h hh
        refine ⟨⟨h, H_le_K hh⟩, ?_, rfl⟩
        show Equiv.Perm.sign (θ ⟨h, H_le_K hh⟩).1 = 1
        rw [θ_fst_H C hker hh, map_one]
      · rw [zpowers_le]
        refine ⟨⟨x, x_mem_K⟩, ?_, rfl⟩
        show Equiv.Perm.sign (θ ⟨x, x_mem_K⟩).1 = 1
        exact perm3_sign_of_cube _ (θ_x C hker hS2 hx3 hxH).2.1
      · intro t ht
        exact ⟨⟨t, T_le_K ht⟩, hall t ht, rfl⟩
    obtain ⟨k, hk⟩ := hθ (Equiv.swap 0 1, 1)
    have hkK : k ∈ K₃ := by
      obtain ⟨k', hk', hkk'⟩ := hK₃ k.2
      rwa [show k' = k from Subtype.ext hkk'] at hk'
    have : Equiv.Perm.sign (θ k).1 = 1 := hkK
    rw [hk] at this
    exact absurd this (by decide)
  obtain ⟨hsq, hne⟩ := perm3_sq_of_sign _ hsign
  let π : ↥(H ⊔ zpowers x ⊔ T) →* alternatingGroup (Fin 5) := (MonoidHom.snd _ _).comp θ
  have hP : Nat.card ((P.subgroupOf (H ⊔ zpowers x ⊔ T)).map π) = 4 := by
    let ρ : ↥P →* alternatingGroup (Fin 5) := π.comp (Subgroup.inclusion (hPT.trans T_le_K))
    have hρ : ρ.range = (P.subgroupOf (H ⊔ zpowers x ⊔ T)).map π := by
      ext a
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨Subgroup.inclusion (hPT.trans T_le_K) p, p.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩
    have hkerρ : ρ.ker = (P ⊓ S).subgroupOf P := by
      ext p
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : θ (Subgroup.inclusion (hPT.trans T_le_K) p) = 1 :=
          Prod.ext (θ_fst_H C hker (hPH p.2)) h
        exact ⟨p.2, (mem_ker_iff hker).mp h1⟩
      · intro h
        have h1 := (mem_ker_iff hker).mpr (show ((Subgroup.inclusion (hPT.trans T_le_K) p :
          ↥(H ⊔ zpowers x ⊔ T)) : G) ∈ S from h.2)
        show (θ _).2 = 1
        rw [h1]
        rfl
    rw [← hρ, ← Subgroup.index_ker, hkerρ]
    exact hP4
  have hle : (P.subgroupOf (H ⊔ zpowers x ⊔ T)).map π ≤
      (T.subgroupOf (H ⊔ zpowers x ⊔ T)).map π :=
    Subgroup.map_mono fun k hk => hPT hk
  have hT2' : IsPGroup 2 ((T.subgroupOf (H ⊔ zpowers x ⊔ T)).map π) :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe T_le_K).symm).map π
  have heq : (P.subgroupOf (H ⊔ zpowers x ⊔ T)).map π =
      (T.subgroupOf (H ⊔ zpowers x ⊔ T)).map π :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP]; exact card_le_four_of_isPGroup hT2')
  obtain ⟨p, hp, hpa⟩ : (π ⟨τ', T_le_K hτ'⟩) ∈ (P.subgroupOf (H ⊔ zpowers x ⊔ T)).map π := by
    rw [heq]
    exact ⟨⟨τ', T_le_K hτ'⟩, hτ', rfl⟩
  have hpH : (p : G) ∈ H := hPH hp
  have hθp : (θ p).1 = 1 := θ_fst_H C hker hpH
  refine ⟨τ' * (p : G)⁻¹, T.mul_mem hτ' (T.inv_mem (hPT hp)), ?_⟩
  have e : (⟨τ' * (p : G)⁻¹, T_le_K (T.mul_mem hτ' (T.inv_mem (hPT hp)))⟩ :
      ↥(H ⊔ zpowers x ⊔ T)) = ⟨τ', T_le_K hτ'⟩ * p⁻¹ := rfl
  rw [e, map_mul, map_inv]
  refine ⟨?_, ?_, ?_⟩
  · simp [hθp, hsq]
  · simp [hθp, hne]
  · show (θ ⟨τ', _⟩).2 * (θ p).2⁻¹ = 1
    have : (θ p).2 = (θ ⟨τ', T_le_K hτ'⟩).2 := hpa
    rw [this, mul_inv_cancel]

theorem θ_fst_T (hT2 : IsPGroup 2 T) {t₀ τ : G} (ht₀ : t₀ ∈ T) (hτ : τ ∈ T)
    (h0 : (θ ⟨t₀, T_le_K ht₀⟩).1 ^ 2 = 1) (h1 : (θ ⟨t₀, T_le_K ht₀⟩).1 ≠ 1) :
    (θ ⟨τ, T_le_K hτ⟩).1 = 1 ∨ (θ ⟨τ, T_le_K hτ⟩).1 = (θ ⟨t₀, T_le_K ht₀⟩).1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ g (hg : g ∈ T), (θ ⟨g, T_le_K hg⟩).1 ^ 2 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hT2 ⟨g, hg⟩
    have hg' : g ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : (θ ⟨g, T_le_K hg⟩).1 ^ 2 ^ k = 1 := by
      have h3 : (⟨g, T_le_K hg⟩ : ↥(H ⊔ zpowers x ⊔ T)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hg')
      have h4 := congrArg Prod.fst (congrArg θ h3)
      rwa [map_pow, map_one, Prod.pow_fst, Prod.fst_one] at h4
    have hdvd1 : orderOf (θ ⟨g, T_le_K hg⟩).1 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd2 : orderOf (θ ⟨g, T_le_K hg⟩).1 ∣ 6 := by
      have := orderOf_dvd_natCard (θ ⟨g, T_le_K hg⟩).1
      rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    have hdvd : orderOf (θ ⟨g, T_le_K hg⟩).1 ∣ 2 := by
      have h6 : Nat.gcd (2 ^ k) 6 ∣ 2 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num]
        have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
        calc Nat.gcd (2 ^ k) (2 * 3) = Nat.gcd (2 ^ k) 2 := by
              rw [Nat.Coprime.gcd_mul_right_cancel_right 2 hc.symm]
          _ ∣ 2 := Nat.gcd_dvd_right _ _
      exact (Nat.dvd_gcd hdvd1 hdvd2).trans h6
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  by_contra h
  push Not at h
  obtain ⟨hne1, hne2⟩ := h
  have hm := perm3_mul (hsq τ hτ) h0 hne1 h1 hne2
  have h2 := hsq (τ * t₀) (T.mul_mem hτ ht₀)
  have e : (θ ⟨τ * t₀, T_le_K (T.mul_mem hτ ht₀)⟩).1 =
      (θ ⟨τ, T_le_K hτ⟩).1 * (θ ⟨t₀, T_le_K ht₀⟩).1 := by
    rw [show (⟨τ * t₀, T_le_K (T.mul_mem hτ ht₀)⟩ : ↥(H ⊔ zpowers x ⊔ T)) =
      ⟨τ, T_le_K hτ⟩ * ⟨t₀, T_le_K ht₀⟩ from rfl, map_mul]
    rfl
  rw [e] at h2
  exact hm.2 (perm3_ne _ hm.1 h2)

include C hker in
theorem exists_t (hSH : S ≤ H) (hST : S ≤ T) (hS2 : IsPGroup 2 S) (hT2 : IsPGroup 2 T)
    (hx3 : orderOf x = 3) (hθx : (θ ⟨x, x_mem_K⟩).2 = 1 ∧ (θ ⟨x, x_mem_K⟩).1 ^ 3 = 1 ∧
      (θ ⟨x, x_mem_K⟩).1 ≠ 1)
    (hKN : H ⊔ T ⊔ zpowers x ≤ normalizer (S : Set G))
    (hinf : S ⊓ ((H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G)) = ⊥)
    (hsup : S ⊔ ((H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G)) =
      H ⊔ T ⊔ zpowers x)
    {t₀ : G} (ht₀ : t₀ ∈ T) (h0 : (θ ⟨t₀, T_le_K ht₀⟩).1 ^ 2 = 1)
    (h1 : (θ ⟨t₀, T_le_K ht₀⟩).1 ≠ 1) (h2 : (θ ⟨t₀, T_le_K ht₀⟩).2 = 1) :
    ∃ t, ∃ ht : t ∈ T, t * t = 1 ∧ t * x * t⁻¹ = x⁻¹ ∧ t ∉ S ∧ t ∈ normalizer (S : Set G) ∧
      (∀ h ∈ H, ∃ s ∈ S, ∃ l ∈ H, h = s * l ∧ l * t = t * l) ∧
      (∀ τ ∈ T, τ ∈ H ∨ t * τ ∈ H) ∧ (θ ⟨t, T_le_K ht⟩).1 = (θ ⟨t₀, T_le_K ht₀⟩).1 ∧
      (θ ⟨t, T_le_K ht⟩).2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := (H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G) with hL
  have hLN : L ≤ normalizer (S : Set G) := inf_le_left.trans hKN
  have hmul : ((L ⊔ S : Subgroup G) : Set G) = (L : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right L S hLN ▸ rfl
  have hdec : ∀ k ∈ H ⊔ T ⊔ zpowers x, ∃ l ∈ L, ∃ s ∈ S, l * s = k := by
    intro k hk
    have hk' : k ∈ ((L ⊔ S : Subgroup G) : Set G) := by
      rw [sup_comm, hsup]
      exact hk
    rw [hmul] at hk'
    obtain ⟨l, hl, s, hs, rfl⟩ := hk'
    exact ⟨l, hl, s, hs, rfl⟩
  have hTK : T ≤ H ⊔ T ⊔ zpowers x := le_sup_right.trans le_sup_left
  have hHK : H ≤ H ⊔ T ⊔ zpowers x := le_sup_left.trans le_sup_left
  have hSL : ∀ w ∈ L, w ∈ S → w = 1 := fun w hw hwS => by
    have : w ∈ S ⊓ L := ⟨hwS, hw⟩
    rw [hinf] at this
    exact this
  obtain ⟨t, htL, s, hs, hts⟩ := hdec t₀ (hTK ht₀)
  have htT : t ∈ T := by
    have e : t = t₀ * s⁻¹ := by rw [← hts]; group
    rw [e]
    exact T.mul_mem ht₀ (T.inv_mem (hST hs))
  have hθt : θ ⟨t, T_le_K htT⟩ = θ ⟨t₀, T_le_K ht₀⟩ := by
    have e : (⟨t₀, T_le_K ht₀⟩ : ↥(H ⊔ zpowers x ⊔ T)) =
        ⟨t, T_le_K htT⟩ * ⟨s, T_le_K (hST hs)⟩ := Subtype.ext hts.symm
    rw [e, map_mul, (mem_ker_iff hker (k := ⟨s, T_le_K (hST hs)⟩)).mpr hs, mul_one]
  have hθ1 : (θ ⟨t, T_le_K htT⟩).1 = (θ ⟨t₀, T_le_K ht₀⟩).1 := by rw [hθt]
  have hθ2 : (θ ⟨t, T_le_K htT⟩).2 = 1 := by rw [hθt, h2]
  refine ⟨t, htT, ?_, ?_, ?_, hLN htL, ?_, ?_, hθ1, hθ2⟩
  ·
    apply hSL (t * t) (L.mul_mem htL htL)
    have h3 : θ (⟨t, T_le_K htT⟩ * ⟨t, T_le_K htT⟩) = 1 := by
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, hθ1, ← sq, h0, Prod.fst_one]
      · rw [Prod.snd_mul, hθ2, mul_one, Prod.snd_one]
    have h4 := (mem_ker_iff hker).mp h3
    simpa using h4
  ·
    have hxN : t * x * t⁻¹ ∈ zpowers x :=
      (mem_normalizer_iff.mp htL.2 x).mp (mem_zpowers x)
    have hw : t * x * t⁻¹ * x ∈ zpowers x := mul_mem hxN (mem_zpowers x)
    obtain ⟨hx2, hx3', hx1⟩ := hθx
    have hwS : t * x * t⁻¹ * x ∈ S := by
      have h3 : θ (⟨t, T_le_K htT⟩ * ⟨x, x_mem_K⟩ * ⟨t, T_le_K htT⟩⁻¹ * ⟨x, x_mem_K⟩) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv]
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, hθ1,
            perm3_conj _ _ h0 h1 hx3' hx1, inv_mul_cancel, Prod.fst_one]
        · rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, hθ2, hx2, inv_one, mul_one,
            mul_one, mul_one, Prod.snd_one]
      have h4 := (mem_ker_iff hker).mp h3
      simpa using h4
    have hw1 : t * x * t⁻¹ * x = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw
      have hx3'' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
      have hw3 : (t * x * t⁻¹ * x) ^ 3 = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3'', one_zpow]
      obtain ⟨m, hm⟩ := hS2 ⟨_, hwS⟩
      have hm' : (t * x * t⁻¹ * x) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hd1 := orderOf_dvd_of_pow_eq_one hw3
      have hd2 := orderOf_dvd_of_pow_eq_one hm'
      have hc : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc hd1 hd2)
    calc t * x * t⁻¹ = (t * x * t⁻¹ * x) * x⁻¹ := by group
      _ = x⁻¹ := by rw [hw1, one_mul]
  ·
    intro htS
    have := (mem_ker_iff hker (k := ⟨t, T_le_K htT⟩)).mpr htS
    rw [this] at hθ1
    exact h1 hθ1.symm
  ·
    intro h hh
    obtain ⟨l, hl, s', hs', hls⟩ := hdec h (hHK hh)
    have hlH : l ∈ H := by
      have e : l = h * s'⁻¹ := by rw [← hls]; group
      rw [e]
      exact H.mul_mem hh (H.inv_mem (hSH hs'))
    refine ⟨l * s' * l⁻¹, (mem_normalizer_iff.mp (hLN hl) s').mp hs', l, hlH, by rw [← hls]; group,
      ?_⟩
    have hw : l * t * l⁻¹ * t⁻¹ = 1 := by
      apply hSL _ (L.mul_mem (L.mul_mem (L.mul_mem hl htL) (L.inv_mem hl)) (L.inv_mem htL))
      have hl1 : (θ ⟨l, H_le_K hlH⟩).1 = 1 := θ_fst_H C hker hlH
      have h3 : θ (⟨l, H_le_K hlH⟩ * ⟨t, T_le_K htT⟩ * ⟨l, H_le_K hlH⟩⁻¹ *
          ⟨t, T_le_K htT⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, Prod.fst_inv, hl1, inv_one,
            one_mul, mul_one, mul_inv_cancel, Prod.fst_one]
        · rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, Prod.snd_inv, hθ2, inv_one,
            mul_one, mul_one, mul_inv_cancel, Prod.snd_one]
      have h4 := (mem_ker_iff hker).mp h3
      simpa using h4
    calc l * t = (l * t * l⁻¹ * t⁻¹) * t * l := by group
      _ = t * l := by rw [hw, one_mul]
  ·
    intro τ hτ
    rcases θ_fst_T hT2 ht₀ hτ h0 h1 with h | h
    · exact Or.inl (mem_H_of_θ_fst C hker hSH h)
    · right
      have h3 := mem_H_of_θ_fst C hker hSH (k := ⟨t, T_le_K htT⟩ * ⟨τ, T_le_K hτ⟩) (by
        rw [map_mul, Prod.fst_mul, h, hθ1, ← sq, h0])
      simpa using h3

end Quot

section Act

variable {G : Type} [Group G]

structure XData (S Z : Subgroup G) (x : G) : Prop where
  normS : x ∈ normalizer (S : Set G)
  normZ : x ∈ normalizer (Z : Set G)
  cube : x ^ 3 = 1
  closure : Subgroup.closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = Z
  scalar : ∀ s ∈ S, s * (x⁻¹ * s * x) * (x⁻¹ * x⁻¹ * s * x * x) ∈ Z

structure TData (S H : Subgroup G) (x t : G) : Prop where
  normS : t ∈ normalizer (S : Set G)
  sq : t * t = 1
  inv : t * x * t⁻¹ = x⁻¹
  notS : t ∉ S
  compl : ∀ h ∈ H, ∃ s ∈ S, ∃ l ∈ H, h = s * l ∧ l * t = t * l

variable {S Z H : Subgroup G} {x t : G}

theorem conj_mem_Z_of_normS (hS : Special S Z) {g c : G} (hg : g ∈ normalizer (S : Set G))
    (hc : c ∈ Z) : g * c * g⁻¹ ∈ Z := by
  rw [← hS.center] at hc ⊢
  refine ⟨(mem_normalizer_iff.mp hg c).mp hc.1, mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    simpa using this
  have h1 := mem_centralizer_iff.mp hc.2 _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * s := by group

theorem TData.inv_eq (ht : TData S H x t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right ht.sq

theorem exists_z (hS : Special S Z) (hx : XData S Z x) (ht : TData S H x t) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z) := by
  have hZ4 := hS.card
  obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c ∈ Z, c ≠ 1 := by
    by_contra h
    push Not at h
    have : Z = ⊥ := eq_bot_iff.mpr fun c hc => h c hc
    rw [this, card_bot] at hZ4
    omega
  have htZ : ∀ c ∈ Z, t * c * t⁻¹ ∈ Z := fun c hc => conj_mem_Z_of_normS hS ht.normS hc
  have htt : ∀ c : G, t * (t * c * t⁻¹) * t⁻¹ = c := fun c => by
    calc t * (t * c * t⁻¹) * t⁻¹ = (t * t) * c * (t * t)⁻¹ := by group
      _ = c := by rw [ht.sq]; group
  obtain ⟨z, hz, hz1, htz⟩ : ∃ z ∈ Z, z ≠ 1 ∧ t * z * t⁻¹ = z := by
    by_cases h : t * c₀ * t⁻¹ = c₀
    · exact ⟨c₀, hc₀, hc₀1, h⟩
    · refine ⟨c₀ * (t * c₀ * t⁻¹), Z.mul_mem hc₀ (htZ c₀ hc₀), fun h1 => h ?_, ?_⟩
      · have : t * c₀ * t⁻¹ = c₀⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this, hS.inv_eq hc₀]
      · have e : t * (c₀ * (t * c₀ * t⁻¹)) * t⁻¹ = (t * c₀ * t⁻¹) * (t * (t * c₀ * t⁻¹) * t⁻¹) := by
          group
        rw [e, htt, hS.comm_Z (htZ c₀ hc₀) (hS.le hc₀)]
  refine ⟨z, hz, hz1, fun c hc => ⟨fun hc' => ?_, fun hc' => ?_⟩⟩
  ·
    by_contra hcz
    have hcz' : c ≠ 1 ∧ c ≠ z := ⟨fun e => hcz (e ▸ one_mem _), fun e => hcz (e ▸ mem_zpowers z)⟩
    have hzc : z * c ≠ 1 ∧ z * c ≠ z ∧ z * c ≠ c := by
      refine ⟨fun e => ?_, fun e => hcz'.1 (by simpa using e), fun e => hz1 (by simpa using e)⟩
      have : c = z⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [this, hS.inv_eq hz] at hcz'
      exact hcz'.2 rfl
    have hcent : ∀ w ∈ Z, t * w * t⁻¹ = w := by
      intro w hw
      rcases hS.eq_of_four (one_mem Z) hz hc (Z.mul_mem hz hc) hw hz1.symm hcz'.1.symm hzc.1.symm
          (Ne.symm hcz'.2) hzc.2.1.symm hzc.2.2.symm with rfl | rfl | rfl | rfl
      · group
      · exact htz
      · exact hc'
      · calc t * (z * c) * t⁻¹ = (t * z * t⁻¹) * (t * c * t⁻¹) := by group
          _ = z * c := by rw [htz, hc']
    have hxcent : ∀ w ∈ Z, x * w * x⁻¹ = w := by
      intro w hw
      have hw1 : x * w * x⁻¹ ∈ Z := (mem_normalizer_iff.mp hx.normZ w).mp hw
      have e1 : x⁻¹ * w * x = x * w * x⁻¹ := by
        calc x⁻¹ * w * x = (t * x * t⁻¹) * w * (t * x * t⁻¹)⁻¹ := by rw [ht.inv, inv_inv]
          _ = t * (x * (t⁻¹ * w * t) * x⁻¹) * t⁻¹ := by group
          _ = t * (x * w * x⁻¹) * t⁻¹ := by
              rw [show t⁻¹ * w * t = w by
                rw [ht.inv_eq]
                have := hcent w hw
                rw [ht.inv_eq] at this
                exact this]
          _ = x * w * x⁻¹ := by
              have := hcent _ hw1
              exact this
      have hx2 : x * x = x⁻¹ := by
        calc x * x = x ^ 3 * x⁻¹ := by rw [pow_three]; group
          _ = x⁻¹ := by rw [hx.cube, one_mul]
      have hwx : x⁻¹ * w * x = w := by
        calc x⁻¹ * w * x = (x * x) * w * (x * x)⁻¹ := by rw [hx2]; group
          _ = x * (x * w * x⁻¹) * x⁻¹ := by group
          _ = x * (x⁻¹ * w * x) * x⁻¹ := by rw [e1]
          _ = w := by group
      calc x * w * x⁻¹ = x * (x⁻¹ * w * x) * x⁻¹ := by rw [hwx]
        _ = w := by group
    have hbot : Subgroup.closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro _ ⟨w, hw, rfl⟩
      calc w⁻¹ * x⁻¹ * w * x = w⁻¹ * x⁻¹ * (x * w * x⁻¹) * x := by rw [hxcent w hw]
        _ = 1 := by group
    rw [hx.closure] at hbot
    rw [hbot, card_bot] at hZ4
    omega
  · rcases hS.eq_one_or_eq hz hc' with rfl | rfl
    · group
    · exact htz

@[expose] def Special.Wt (hS : Special S Z) (t : G) : Subgroup G where
  carrier := {s | s ∈ S ∧ s * t * s⁻¹ * t⁻¹ ∈ Z}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, ?_⟩
    have e : a * b * t * (a * b)⁻¹ * t⁻¹ =
        (a * (b * t * b⁻¹ * t⁻¹) * a⁻¹) * (a * t * a⁻¹ * t⁻¹) := by
      group
    rw [e, hS.conj_Z hb' ha]
    exact Z.mul_mem hb' ha'
  one_mem' := ⟨S.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨S.inv_mem ha, ?_⟩
    have e : a⁻¹ * t * a⁻¹⁻¹ * t⁻¹ = a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a := by group
    rw [e, hS.conj_Z' (Z.inv_mem ha') ha]
    exact Z.inv_mem ha'

theorem Special.mem_Wt (hS : Special S Z) {s : G} :
    s ∈ hS.Wt t ↔ s ∈ S ∧ s * t * s⁻¹ * t⁻¹ ∈ Z := Iff.rfl

theorem Special.Wt_le (hS : Special S Z) : hS.Wt t ≤ S := fun _ h => h.1

theorem Special.Z_le_Wt (hS : Special S Z) (ht : t ∈ normalizer (S : Set G)) : Z ≤ hS.Wt t :=
  fun c hc => ⟨hS.le hc, by
    have e : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
    rw [e]
    exact Z.mul_mem hc (conj_mem_Z_of_normS hS ht (Z.inv_mem hc))⟩

theorem Coord.mem_Wt_iff {C : Coord S Z H} (hS : Special S Z) (ht : t ∈ normalizer (S : Set G))
    {s : G} (hs : s ∈ S) : s ∈ hS.Wt t ↔ C.Ψ (t * s * t⁻¹) = C.Ψ s := by
  have hts : t * s * t⁻¹ ∈ S := (mem_normalizer_iff.mp ht s).mp hs
  rw [hS.mem_Wt, eq_comm, C.Ψ_eq_iff hS hs hts]
  have e : s * (t * s * t⁻¹)⁻¹ = s * t * s⁻¹ * t⁻¹ := by group
  rw [e]
  exact and_iff_right hs

theorem Coord.Ψ_conj_eq {C : Coord S Z H} (hS : Special S Z) {g a b : G}
    (hg : g ∈ normalizer (S : Set G)) (ha : a ∈ S) (hb : b ∈ S) (hab : C.Ψ a = C.Ψ b) :
    C.Ψ (g * a * g⁻¹) = C.Ψ (g * b * g⁻¹) := by
  have hga : g * a * g⁻¹ ∈ S := (mem_normalizer_iff.mp hg a).mp ha
  have hgb : g * b * g⁻¹ ∈ S := (mem_normalizer_iff.mp hg b).mp hb
  rw [C.Ψ_eq_iff hS hga hgb]
  rw [C.Ψ_eq_iff hS ha hb] at hab
  have e : g * a * g⁻¹ * (g * b * g⁻¹)⁻¹ = g * (a * b⁻¹) * g⁻¹ := by group
  rw [e]
  exact conj_mem_Z_of_normS hS hg hab

theorem Coord.mem_Z_of_conj_mem_Wt (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) {w : G} (hw : w ∈ hS.Wt t) (hxw : x * w * x⁻¹ ∈ hS.Wt t) : w ∈ Z := by
  have hx3 := hx.cube
  have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp hx.normS s).mp hs
  have hxS' : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs => by
    have := (mem_normalizer_iff.mp (inv_mem hx.normS) s).mp hs
    simpa using this
  have hconjS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp ht.normS s).mp hs
  have hwS := hw.1
  have h1 := (C.mem_Wt_iff hS ht.normS hwS).mp hw
  have h2 := (C.mem_Wt_iff hS ht.normS (hxS w hwS)).mp hxw
  have e : t * (x * w * x⁻¹) * t⁻¹ = x⁻¹ * (t * w * t⁻¹) * x⁻¹⁻¹ := by
    calc t * (x * w * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * w * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
      _ = x⁻¹ * (t * w * t⁻¹) * x⁻¹⁻¹ := by rw [ht.inv]
  rw [e, C.Ψ_conj_eq hS (inv_mem hx.normS) (hconjS w hwS) hwS h1] at h2
  have hsc := hx.scalar w hwS
  have e2 : x⁻¹ * x⁻¹ * w * x * x = x * w * x⁻¹ := by
    have hx2 : x * x = x⁻¹ := by
      calc x * x = x ^ 3 * x⁻¹ := by rw [pow_three]; group
        _ = x⁻¹ := by rw [hx3, one_mul]
    calc x⁻¹ * x⁻¹ * w * x * x = (x * x)⁻¹ * w * (x * x) := by group
      _ = x * w * x⁻¹ := by rw [hx2, inv_inv]
  rw [e2] at hsc
  have h3 := (C.Ψ_eq_zero_iff hS (S.mul_mem (S.mul_mem hwS (hxS' w hwS)) (hxS w hwS))).mpr hsc
  rw [C.Ψ_mul hS (S.mul_mem hwS (hxS' w hwS)) (hxS w hwS), C.Ψ_mul hS hwS (hxS' w hwS)] at h3
  rw [show x⁻¹ * w * x⁻¹⁻¹ = x⁻¹ * w * x by rw [inv_inv]] at h2
  rw [h2, add_assoc, pair_add_self, add_zero] at h3
  exact (C.Ψ_eq_zero_iff hS hwS).mp h3

theorem Special.Wtx_le (hS : Special S Z) (hx : XData S Z x) :
    (hS.Wt t).map (MulAut.conj x).toMonoidHom ≤ S := by
  rintro _ ⟨w, hw, rfl⟩
  exact (mem_normalizer_iff.mp hx.normS w).mp hw.1

theorem Special.Z_le_Wtx (hS : Special S Z) (hx : XData S Z x) (ht : TData S H x t) :
    Z ≤ (hS.Wt t).map (MulAut.conj x).toMonoidHom := by
  intro c hc
  refine ⟨x⁻¹ * c * x, hS.Z_le_Wt ht.normS ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  have := (mem_normalizer_iff.mp (inv_mem hx.normZ) c).mp hc
  simpa using this

theorem Coord.img_Wt_inf (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) :
    C.img hS (hS.Wt t) ⊓ C.img hS ((hS.Wt t).map (MulAut.conj x).toMonoidHom) = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨⟨u, hu, rfl⟩, hm⟩
  have hu' := C.mem_of_Ψ_mem_img hS (hS.Z_le_Wtx hx ht) hu.2 hm
  obtain ⟨w, hw, rfl⟩ := hu'
  rw [AddSubgroup.mem_bot, C.Ψ_eq_zero_iff hS hu.2]
  exact conj_mem_Z_of_normS hS hx.normS (C.mem_Z_of_conj_mem_Wt hS hx ht hw hu.1)

theorem Coord.comm_t_mem_Wt (C : Coord S Z H) (hS : Special S Z) (ht : TData S H x t) {s : G}
    (hs : s ∈ S) : s * t * s⁻¹ * t⁻¹ ∈ hS.Wt t := by
  have htinv := ht.inv_eq
  have hconjS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp ht.normS s).mp hs
  have hcomm : s * t * s⁻¹ * t⁻¹ ∈ S := by
    have e : s * t * s⁻¹ * t⁻¹ = s * (t * s⁻¹ * t⁻¹) := by group
    rw [e]
    exact S.mul_mem hs (hconjS _ (S.inv_mem hs))
  rw [C.mem_Wt_iff hS ht.normS hcomm]
  have e1 : t * (s * t * s⁻¹ * t⁻¹) * t⁻¹ = (t * s * t⁻¹) * s⁻¹ := by
    rw [htinv]
    calc t * (s * t * s⁻¹ * t) * t = t * s * t * s⁻¹ * (t * t) := by group
      _ = (t * s * t) * s⁻¹ := by rw [ht.sq, mul_one]
  have e2 : s * t * s⁻¹ * t⁻¹ = s * (t * s * t⁻¹)⁻¹ := by group
  rw [e1, e2, C.Ψ_mul hS (hconjS s hs) (S.inv_mem hs),
    C.Ψ_mul hS hs (S.inv_mem (hconjS s hs)), C.Ψ_inv hS hs, C.Ψ_inv hS (hconjS s hs),
    add_comm]

theorem Coord.card_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) : Nat.card (hS.Wt t) = 64 := by
  have hZW : Z ≤ hS.Wt t := hS.Z_le_Wt ht.normS
  have hcardS := C.card_S hS
  have hW4 := C.card_eq_four_mul hS hZW hS.Wt_le
  have htinv := ht.inv_eq
  have hconjS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp ht.normS s).mp hs
  have hΨconj : ∀ s ∈ S, ∀ u ∈ S, C.Ψ (s * u * s⁻¹) = C.Ψ u := by
    intro s hs u hu
    have e : s * u * s⁻¹ = (s * u * s⁻¹ * u⁻¹) * u := by group
    rw [e, C.Ψ_mul hS (hS.le (hS.comm_mem hs hu)) hu,
      (C.Ψ_eq_zero_iff hS (hS.le (hS.comm_mem hs hu))).mpr (hS.comm_mem hs hu), zero_add]
  have hcomm : ∀ s ∈ S, s * t * s⁻¹ * t⁻¹ ∈ S := fun s hs => by
    have e : s * t * s⁻¹ * t⁻¹ = s * (t * s⁻¹ * t⁻¹) := by group
    rw [e]
    exact S.mul_mem hs (hconjS _ (S.inv_mem hs))
  have hlow : 64 ≤ Nat.card (hS.Wt t) := by
    let δ : ↥S →* Multiplicative Pair :=
      { toFun := fun s => Multiplicative.ofAdd (C.Ψ ((s : G) * t * (s : G)⁻¹ * t⁻¹))
        map_one' := by
          show Multiplicative.ofAdd (C.Ψ ((1 : G) * t * (1 : G)⁻¹ * t⁻¹)) = _
          rw [one_mul, inv_one, mul_one, mul_inv_cancel, C.Ψ_one]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (C.Ψ ((a * b : G) * t * (a * b : G)⁻¹ * t⁻¹)) = _
          have e : (a * b : G) * t * (a * b : G)⁻¹ * t⁻¹ =
              ((a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹) *
                ((a : G) * t * (a : G)⁻¹ * t⁻¹) := by group
          rw [e, C.Ψ_mul hS (S.mul_mem (S.mul_mem a.2 (hcomm b b.2)) (S.inv_mem a.2))
            (hcomm a a.2), hΨconj a a.2 _ (hcomm b b.2), add_comm]
          rfl }
    have hker : Nat.card δ.ker = Nat.card (hS.Wt t) := by
      refine Nat.card_congr
        { toFun := fun s => ⟨s.1, s.1.2, (C.Ψ_eq_zero_iff hS (hcomm _ s.1.2)).mp
            (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp s.2))⟩
          invFun := fun s => ⟨⟨s.1, s.2.1⟩, MonoidHom.mem_ker.mpr
            (congrArg Multiplicative.ofAdd ((C.Ψ_eq_zero_iff hS (hcomm _ s.2.1)).mpr s.2.2))⟩
          left_inv := fun s => rfl
          right_inv := fun s => rfl }
    have hrange : ∀ s ∈ S, s * t * s⁻¹ * t⁻¹ ∈ hS.Wt t := fun s hs => C.comm_t_mem_Wt hS ht hs
    have hrange' : Nat.card δ.range ≤ Nat.card (C.img hS (hS.Wt t)) := by
      refine Nat.card_le_card_of_injective
        (fun m => ⟨Multiplicative.toAdd m.1, by
          obtain ⟨s, hs⟩ := m.2
          rw [← hs]
          exact C.Ψ_mem_img hS (hrange s s.2) (hcomm s s.2)⟩) fun a b h => ?_
      have := congrArg Subtype.val h
      exact Subtype.ext (Multiplicative.toAdd.injective this)
    have hS' : Nat.card ↥S = Nat.card δ.ker * Nat.card δ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, mul_comm]
    rw [hker, hcardS] at hS'
    nlinarith
  have hinf := C.img_Wt_inf hS hx ht
  have hcardWx : Nat.card ((hS.Wt t).map (MulAut.conj x).toMonoidHom) = Nat.card (hS.Wt t) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hWx4 := C.card_eq_four_mul hS (Special.Z_le_Wtx hS hx ht) (Special.Wtx_le hS hx)
  have hle := card_mul_card_le_of_inf_eq_bot (fun m hm => C.img_even hS hm)
    (fun m hm => C.img_even hS hm) hinf
  have hup : Nat.card (hS.Wt t) ≤ 64 := by nlinarith
  omega

theorem Special.conj_mem_Wt_of_mem_S (hS : Special S Z) (ht : t ∈ normalizer (S : Set G))
    {s w : G} (hs : s ∈ S) (hw : w ∈ hS.Wt t) : s * w * s⁻¹ ∈ hS.Wt t := by
  have e : s * w * s⁻¹ = (s * w * s⁻¹ * w⁻¹) * w := by group
  rw [e]
  exact (hS.Wt t).mul_mem (hS.Z_le_Wt ht (hS.comm_mem hs hw.1)) hw

theorem Coord.conj_mem_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (ht : TData S H x t) {h w : G} (hh : h ∈ H)
    (hw : w ∈ hS.Wt t) : h * w * h⁻¹ ∈ hS.Wt t := by
  obtain ⟨s, hs, l, hl, rfl, hlt⟩ := ht.compl h hh
  have hlw : l * w * l⁻¹ ∈ hS.Wt t := by
    refine ⟨(mem_normalizer_iff.mp (hHS hl) w).mp hw.1, ?_⟩
    have e : l * w * l⁻¹ * t * (l * w * l⁻¹)⁻¹ * t⁻¹ = l * (w * t * w⁻¹ * t⁻¹) * l⁻¹ := by
      have hlt' : l⁻¹ * t = t * l⁻¹ := by
        calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
          _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
          _ = t * l⁻¹ := by group
      calc l * w * l⁻¹ * t * (l * w * l⁻¹)⁻¹ * t⁻¹ = l * w * (l⁻¹ * t) * l * w⁻¹ * l⁻¹ * t⁻¹ := by
            group
        _ = l * w * (t * l⁻¹) * l * w⁻¹ * l⁻¹ * t⁻¹ := by rw [hlt']
        _ = l * (w * t * w⁻¹ * t⁻¹) * (t * l⁻¹ * t⁻¹) := by group
        _ = l * (w * t * w⁻¹ * t⁻¹) * l⁻¹ := by
            rw [show t * l⁻¹ * t⁻¹ = l⁻¹ by rw [← hlt']; group]
    rw [e, C.conj_eq_of_mem_H hS hHS hl hw.2]
    exact hw.2
  have e : s * l * w * (s * l)⁻¹ = s * (l * w * l⁻¹) * s⁻¹ := by group
  rw [e]
  exact hS.conj_mem_Wt_of_mem_S ht.normS hs hlw

theorem Coord.exists_proj_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) :
    ∃ π : Pair →+ (Fin 5 → ZMod 2), (∀ σ m, π (act₂ σ m) = act σ (π m)) ∧
      (∀ m ∈ C.img hS (hS.Wt t), π m = 0 → m = 0) ∧ (∀ m ∈ C.img hS (hS.Wt t), IsEven (π m)) ∧
      ∀ v, IsEven v → ∃ m ∈ C.img hS (hS.Wt t), π m = v := by
  have hcard : Nat.card (C.img hS (hS.Wt t)) = 16 := by
    have h1 := C.card_eq_four_mul hS (hS.Z_le_Wt ht.normS) hS.Wt_le
    rw [C.card_Wt hS hx ht] at h1
    omega
  exact exists_proj_of_pair_invariant (fun m hm => C.img_even hS hm)
    (C.img_invariant hS (fun h hh w hw => C.conj_mem_Wt hS hHS ht hh hw) hHS) hcard

theorem Coord.eq_Wt_of_invariant [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t)
    {U : Subgroup G} (hZU : Z ≤ U) (hUW : U ≤ hS.Wt t)
    (hinv : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hne : ∃ u ∈ U, u ∉ Z) : U = hS.Wt t := by
  obtain ⟨π, hπ, hinj, heven, -⟩ := C.exists_proj_Wt hS hHS hx ht
  have hle : C.img hS U ≤ C.img hS (hS.Wt t) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hUW hu.1, hu.2⟩, rfl⟩
  have hne' : C.img hS U ≠ ⊥ := by
    obtain ⟨u, hu, huZ⟩ := hne
    intro h
    have : C.Ψ u ∈ C.img hS U := C.Ψ_mem_img hS hu (hS.Wt_le (hUW hu))
    rw [h, AddSubgroup.mem_bot, C.Ψ_eq_zero_iff hS (hS.Wt_le (hUW hu))] at this
    exact huZ this
  have heq := eq_of_le_of_invariant hle hne' (C.img_invariant hS hinv hHS) hπ hinj heven
  refine le_antisymm hUW fun w hw => C.mem_of_Ψ_mem_img hS hZU hw.1 ?_
  rw [heq]
  exact C.Ψ_mem_img hS hw hw.1

section Zt

variable {z : G}

theorem comm_t_Z (hS : Special S Z) (ht : TData S H x t)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {c : G} (hc : c ∈ Z) :
    c * t * c⁻¹ * t⁻¹ ∈ zpowers z := by
  have htZ : t * c⁻¹ * t⁻¹ ∈ Z := conj_mem_Z_of_normS hS ht.normS (Z.inv_mem hc)
  have hd : c * t * c⁻¹ * t⁻¹ ∈ Z := by
    have e : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
    rw [e]
    exact Z.mul_mem hc htZ
  refine (hz _ hd).mp ?_
  have htinv := ht.inv_eq
  have e1 : t * (c * t * c⁻¹ * t⁻¹) * t⁻¹ = (c * t * c⁻¹ * t⁻¹)⁻¹ := by
    have h1 : t * (c * t * c⁻¹ * t⁻¹) * t⁻¹ = t * c * t * c⁻¹ * (t⁻¹ * t⁻¹) := by group
    have h2 : t⁻¹ * t⁻¹ = 1 := by rw [htinv, ht.sq]
    have h3 : (c * t * c⁻¹ * t⁻¹)⁻¹ = t * c * t⁻¹ * c⁻¹ := by group
    rw [h1, h2, mul_one, h3, htinv]
  rw [e1, hS.inv_eq hd]

theorem comm_mul_t (a b t : G) :
    a * b * t * (a * b)⁻¹ * t⁻¹ = (a * (b * t * b⁻¹ * t⁻¹) * a⁻¹) * (a * t * a⁻¹ * t⁻¹) := by
  group

theorem Coord.comm_t_mem [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w : G}
    (hw : w ∈ hS.Wt t) : w * t * w⁻¹ * t⁻¹ ∈ zpowers z := by
  let W₁ : Subgroup G :=
    { carrier := {w | w ∈ hS.Wt t ∧ w * t * w⁻¹ * t⁻¹ ∈ zpowers z}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(hS.Wt t).mul_mem ha hb, ?_⟩
        rw [comm_mul_t, hS.conj_Z hb.2 ha.1]
        exact mul_mem hb' ha'
      one_mem' := ⟨(hS.Wt t).one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(hS.Wt t).inv_mem ha, ?_⟩
        have e : a⁻¹ * t * a⁻¹⁻¹ * t⁻¹ = a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a := by group
        rw [e, hS.conj_Z' (Z.inv_mem ha.2) ha.1]
        exact inv_mem ha' }
  have hZW₁ : Z ≤ W₁ := fun c hc => ⟨hS.Z_le_Wt ht.normS hc, comm_t_Z hS ht hz hc⟩
  have hW₁W : W₁ ≤ hS.Wt t := fun _ h => h.1
  have hinv : ∀ h ∈ H, ∀ u ∈ W₁, h * u * h⁻¹ ∈ W₁ := by
    intro h hh u hu
    refine ⟨C.conj_mem_Wt hS hHS ht hh hu.1, ?_⟩
    obtain ⟨s, hs, l, hl, rfl, hlt⟩ := ht.compl h hh
    have hlt' : l⁻¹ * t = t * l⁻¹ := by
      calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
        _ = t * l⁻¹ := by group
    have hlu : l * u * l⁻¹ * t * (l * u * l⁻¹)⁻¹ * t⁻¹ = l * (u * t * u⁻¹ * t⁻¹) * l⁻¹ := by
      calc l * u * l⁻¹ * t * (l * u * l⁻¹)⁻¹ * t⁻¹ = l * u * (l⁻¹ * t) * l * u⁻¹ * l⁻¹ * t⁻¹ := by
            group
        _ = l * u * (t * l⁻¹) * l * u⁻¹ * l⁻¹ * t⁻¹ := by rw [hlt']
        _ = l * (u * t * u⁻¹ * t⁻¹) * (t * l⁻¹ * t⁻¹) := by group
        _ = l * (u * t * u⁻¹ * t⁻¹) * l⁻¹ := by
            rw [show t * l⁻¹ * t⁻¹ = l⁻¹ by rw [← hlt']; group]
    have hlu' : l * u * l⁻¹ * t * (l * u * l⁻¹)⁻¹ * t⁻¹ = u * t * u⁻¹ * t⁻¹ := by
      rw [hlu, C.conj_eq_of_mem_H hS hHS hl hu.1.2]
    have hluS : l * u * l⁻¹ ∈ S := (mem_normalizer_iff.mp (hHS hl) u).mp hu.1.1
    have hc : s * (l * u * l⁻¹) * s⁻¹ * (l * u * l⁻¹)⁻¹ ∈ Z := hS.comm_mem hs hluS
    have e : s * l * u * (s * l)⁻¹ = (s * (l * u * l⁻¹) * s⁻¹ * (l * u * l⁻¹)⁻¹) *
        (l * u * l⁻¹) := by group
    rw [e, comm_mul_t, hlu', hS.conj_Z hu.1.2 (hS.le hc)]
    exact mul_mem hu.2 (comm_t_Z hS ht hz hc)
  have hcard : 32 ≤ Nat.card W₁ := by
    let ρ : ↥(hS.Wt t) →* Multiplicative (ZMod 2) :=
      { toFun := fun w => Multiplicative.ofAdd (Special.ell z ((w : G) * t * (w : G)⁻¹ * t⁻¹))
        map_one' := by
          show Multiplicative.ofAdd (Special.ell z ((1 : G) * t * (1 : G)⁻¹ * t⁻¹)) = _
          rw [one_mul, inv_one, mul_one, mul_inv_cancel,
            (Special.ell_eq_zero_iff z 1).mpr (one_mem _)]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (Special.ell z ((a * b : G) * t * (a * b : G)⁻¹ * t⁻¹)) = _
          rw [comm_mul_t, hS.conj_Z b.2.2 a.2.1, hS.ell_mul hzZ hz1 b.2.2 a.2.2, add_comm]
          rfl }
    have hker : Nat.card ρ.ker = Nat.card W₁ := by
      refine Nat.card_congr
        { toFun := fun w => ⟨w.1, w.1.2, (Special.ell_eq_zero_iff z _).mp
            (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp w.2))⟩
          invFun := fun w => ⟨⟨w.1, w.2.1⟩, MonoidHom.mem_ker.mpr
            (congrArg Multiplicative.ofAdd ((Special.ell_eq_zero_iff z _).mpr w.2.2))⟩
          left_inv := fun w => rfl
          right_inv := fun w => rfl }
    have hrange : Nat.card ρ.range ≤ 2 := by
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [Nat.card_eq_fintype_card]
      rfl
    have h1 : Nat.card (hS.Wt t) = Nat.card ρ.ker * Nat.card ρ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]
    rw [C.card_Wt hS hx ht, hker] at h1
    nlinarith
  have hne : ∃ u ∈ W₁, u ∉ Z := by
    by_contra h
    push Not at h
    have : Nat.card W₁ ≤ Nat.card Z := Subgroup.card_le_of_le h
    rw [hS.card] at this
    omega
  have heq := C.eq_Wt_of_invariant hS hHS hx ht hZW₁ hW₁W hinv hne
  have : w ∈ W₁ := heq ▸ hw
  exact this.2

theorem Special.exists_conj_t (hS : Special S Z) {w : G} (hw : w ∈ hS.Wt t) :
    ∃ c ∈ Z, t * w * t⁻¹ = c * w :=
  ⟨t * w * t⁻¹ * w⁻¹, by
    have := Z.inv_mem hw.2
    rwa [Special.comm_inv] at this, by group⟩

theorem comm_mem_zpowers (hS : Special S Z)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w w' : G} (hw : w ∈ hS.Wt t)
    (hw' : w' ∈ hS.Wt t) : w * w' * w⁻¹ * w'⁻¹ ∈ zpowers z := by
  refine (hz _ (hS.comm_mem hw.1 hw'.1)).mp ?_
  obtain ⟨c, hc, hcw⟩ := hS.exists_conj_t hw
  obtain ⟨c', hc', hcw'⟩ := hS.exists_conj_t hw'
  have e : t * (w * w' * w⁻¹ * w'⁻¹) * t⁻¹ =
      (t * w * t⁻¹) * (t * w' * t⁻¹) * (t * w * t⁻¹)⁻¹ * (t * w' * t⁻¹)⁻¹ := by group
  rw [e, hcw, hcw']
  have e2 : c * w * (c' * w') * (c * w)⁻¹ * (c' * w')⁻¹ =
      (c * (w * (c' * w') * w⁻¹ * (c' * w')⁻¹) * c⁻¹) * (c * (c' * w') * c⁻¹ * (c' * w')⁻¹) := by
    group
  have hcw'S : c' * w' ∈ S := S.mul_mem (hS.le hc') hw'.1
  rw [e2, show c * (c' * w') * c⁻¹ * (c' * w')⁻¹ = 1 by
    rw [hS.comm_Z hc hcw'S]; group, mul_one]
  have e3 : w * (c' * w') * w⁻¹ * (c' * w')⁻¹ = w * (w' * c') * w⁻¹ * (w' * c')⁻¹ := by
    rw [hS.comm_Z hc' hw'.1]
  rw [e3, hS.comm_mul_Z hw.1 hw'.1 hc', hS.conj_Z (hS.comm_mem hw.1 hw'.1) (hS.le hc)]

theorem sq_mem_zpowers (hS : Special S Z)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w : G} (hw : w ∈ hS.Wt t) :
    w * w ∈ zpowers z := by
  refine (hz _ (hS.sq w hw.1)).mp ?_
  obtain ⟨c, hc, hcw⟩ := hS.exists_conj_t hw
  have e : t * (w * w) * t⁻¹ = (t * w * t⁻¹) * (t * w * t⁻¹) := by group
  rw [e, hcw]
  calc c * w * (c * w) = c * c * (w * w) := by
        rw [mul_assoc c w, ← mul_assoc w c, ← hS.comm_Z hc hw.1]; group
    _ = w * w := by rw [hS.elem c hc, one_mul]

end Zt

end Act

end Sec2

end CFSG.ComponentClassification.AS81
