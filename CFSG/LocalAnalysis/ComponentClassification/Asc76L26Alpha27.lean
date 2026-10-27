module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped Pointwise

variable {G : Type} [Group G]

theorem eq_of_mem_zpowers_four {t x : G} (ht : orderOf t = 4) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t ∨ x = t ^ 2 ∨ x = t⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h4' : ((orderOf t : ℕ) : ℤ) = 4 := by rw [ht]; rfl
  rw [← zpow_mod_orderOf, h4']
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  have ht4 : t ^ 4 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  interval_cases (k % 4)
  · left; simp
  · right; left; simp
  · right; right; left; rw [zpow_ofNat]
  · right; right; right
    rw [eq_inv_iff_mul_eq_one]
    calc t ^ (3 : ℤ) * t = t ^ 4 := by rw [zpow_ofNat]; group
      _ = 1 := ht4

theorem orderOf_sq_of_four {t : G} (ht : orderOf t = 4) : orderOf (t ^ 2) = 2 := by
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht]; norm_num), ht]

theorem eq_sq_of_orderOf_two {t x : G} (ht : orderOf t = 4) (hx : x ∈ zpowers t)
    (hx2 : orderOf x = 2) : x = t ^ 2 := by
  rcases eq_of_mem_zpowers_four ht hx with rfl | rfl | rfl | rfl
  · rw [orderOf_one] at hx2; omega
  · omega
  · rfl
  · rw [orderOf_inv] at hx2; omega

theorem eq_or_eq_inv_of_orderOf_four {t x : G} (ht : orderOf t = 4) (hx : x ∈ zpowers t)
    (hx4 : orderOf x = 4) : x = t ∨ x = t⁻¹ := by
  rcases eq_of_mem_zpowers_four ht hx with rfl | rfl | rfl | rfl
  · rw [orderOf_one] at hx4; omega
  · exact Or.inl rfl
  · rw [orderOf_sq_of_four ht] at hx4; omega
  · exact Or.inr rfl

section Cyclic4

variable {T : Subgroup G} (hc : IsCyclic T) (h4 : Nat.card T = 4)
include hc h4

theorem exists_gen_of_cyclic_four : ∃ t ∈ T, orderOf t = 4 ∧ zpowers t = T := by
  obtain ⟨⟨g, hgT⟩, hg⟩ := hc.exists_generator
  have hord : orderOf (⟨g, hgT⟩ : T) = 4 := by
    rw [← h4]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Subgroup.orderOf_mk] at hord
  refine ⟨g, hgT, hord, le_antisymm (zpowers_le.mpr hgT) fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

end Cyclic4

theorem exists_mul_of_mem_sup_centralizer {Y : Type} [Group Y] {T K : Subgroup Y} [K.Normal]
    {x : Y} (hx : x ∈ T ⊔ centralizer (K : Set Y)) :
    ∃ p ∈ T, ∃ c ∈ centralizer (K : Set Y), x = p * c := by
  have : x ∈ (T : Set Y) * (centralizer (K : Set Y) : Set Y) := by
    rw [← mul_normal]
    exact hx
  obtain ⟨p, hp, c, hc, rfl⟩ := this
  exact ⟨p, hp, c, hc, rfl⟩

theorem false_of_bender27 {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hK : fusionIsBenderGroup K) (P : Sylow 2 Y) (hKP : K ⊔ (P : Subgroup Y) = ⊤)
    {𝒯 : Set (Subgroup Y)} (hle : ∀ T ∈ 𝒯, T ≤ P)
    (hcyc : ∀ T ∈ 𝒯, IsCyclic T ∧ Nat.card T = 4)
    (hcomm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥)
    (hcl : fusionStronglyClosed (memberSet 𝒯) P) {a : Y} (haΓ : a ∈ memberSet 𝒯) (haK : a ∈ K)
    (ha2 : orderOf a = 2) : False := by
  set T := (P : Subgroup Y) ⊓ K with hTdef
  have hd := BenderExt.extData_of_benderData K (BenderExt.benderData_of_isBenderGroup hK) P hKP
  have hΓP : ∀ x ∈ memberSet 𝒯, x ∈ (P : Subgroup Y) := by
    rintro x ⟨-, T', hT', hx⟩
    exact hle T' hT' hx
  have hCP : ∀ {T₁ T₂ : Subgroup Y}, T₁ ∈ 𝒯 → T₂ ∈ 𝒯 → ∀ {x y : Y}, x ∈ T₁ → y ∈ T₂ →
      x * y ≠ y * x → T₁ = T₂ := fun hT₁ hT₂ x y hx hy hxy => by
    by_contra hne
    exact hxy (commute_of_commutator_eq_bot (hcomm _ hT₁ _ hT₂ hne) hx hy)
  have ha1 : a ≠ 1 := haΓ.1
  have haa : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have haT : a ∈ T := mem_inf.mpr ⟨hΓP a haΓ, haK⟩
  have haZ : a ∈ sylowCenter T := hd.omega_one a haT haa
  have hZΓ : ∀ z ∈ sylowCenter T, z ≠ 1 → z ∈ memberSet 𝒯 := by
    intro z hz hz1
    obtain ⟨n, -, -, hnz⟩ := hd.trans a haZ z hz ha1 hz1
    rw [← hnz]
    exact hcl a haΓ n (by rw [hnz]; exact (mem_inf.mp (sylowCenter_le T hz)).1)
  obtain ⟨-, T₁, hT₁, haT₁⟩ := haΓ
  obtain ⟨hT₁c, hT₁4⟩ := hcyc T₁ hT₁
  obtain ⟨t₁, ht₁T, ht₁4, ht₁gen⟩ := exists_gen_of_cyclic_four hT₁c hT₁4
  have hat : a = t₁ ^ 2 := eq_sq_of_orderOf_two ht₁4 (ht₁gen ▸ haT₁) ha2
  have ht₁1 : t₁ ≠ 1 := fun h => by rw [h, orderOf_one] at ht₁4; omega
  have ht₁Γ : t₁ ∈ memberSet 𝒯 := mem_memberSet hT₁ ht₁T ht₁1
  have ht₁P : t₁ ∈ (P : Subgroup Y) := hΓP t₁ ht₁Γ
  have ht₁Z : ∀ z ∈ sylowCenter T, t₁ * z = z * t₁ := by
    intro z hz
    by_contra hzt
    have hz1 : z ≠ 1 := fun h => hzt (by rw [h, mul_one, one_mul])
    obtain ⟨-, T', hT', hzT'⟩ := hZΓ z hz hz1
    have hT'eq : T' = T₁ := hCP hT' hT₁ hzT' ht₁T (fun h => hzt h.symm)
    have hz2 : orderOf z = 2 := orderOf_eq_prime (hd.sq_center z hz) hz1
    have hzt' := eq_sq_of_orderOf_two ht₁4 (ht₁gen ▸ hT'eq ▸ hzT') hz2
    exact hzt (by rw [hzt', ← pow_succ', ← pow_succ])
  have hord_conj : ∀ g : Y, orderOf (g⁻¹ * t₁ * g) = 4 := fun g => by
    rw [show g⁻¹ * t₁ * g = MulAut.conj g⁻¹ t₁ by simp,
      MulEquiv.orderOf_eq]
    exact ht₁4
  have ht₁N : ∀ x ∈ T, t₁ * x * t₁⁻¹ ∈ T := by
    intro x hx
    obtain ⟨hxP, hxK⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨P.mul_mem (P.mul_mem ht₁P hxP) (P.inv_mem ht₁P),
      (inferInstance : K.Normal).conj_mem x hxK t₁⟩
  by_cases hout : t₁ ∈ T ⊔ centralizer (K : Set Y)
  ·
    obtain ⟨p, hpT, c, hc, hpc⟩ := exists_mul_of_mem_sup_centralizer hout
    have hpK : p ∈ K := (mem_inf.mp hpT).2
    have hcpc : p * c = c * p := mem_centralizer_iff.mp hc p hpK
    have hsq : t₁ ^ 2 = p ^ 2 * c ^ 2 := by
      rw [hpc, sq, sq, sq]
      calc p * c * (p * c) = p * (c * p) * c := by group
        _ = p * (p * c) * c := by rw [← hcpc]
        _ = p * p * (c * c) := by group
    have hc2 : c ^ 2 = 1 := by
      have h1 : c ^ 2 = (p ^ 2)⁻¹ * a := by rw [hat, hsq]; group
      have hK' : c ^ 2 ∈ K := h1 ▸ K.mul_mem (K.inv_mem (K.pow_mem hpK 2)) haK
      have := mem_inf.mpr ⟨hK', pow_mem hc 2⟩
      rwa [hd.inf_centralizer, mem_bot] at this
    have hap : a = p ^ 2 := by rw [hat, hsq, hc2, mul_one]
    have hpZ : p ∉ sylowCenter T := fun hpZ => ha1 (by rw [hap]; exact hd.sq_center p hpZ)
    obtain ⟨n, hnK, hnN, hn⟩ := hd.cent p hpT hpZ
    have hp'T : n⁻¹ * p * n ∈ T := by
      have := (mem_normalizer_iff''.mp hnN p).mp hpT
      exact this
    have hcn : n⁻¹ * c * n = c := by
      have := mem_centralizer_iff.mp hc n hnK
      calc n⁻¹ * c * n = n⁻¹ * (c * n) := by group
        _ = n⁻¹ * (n * c) := by rw [this]
        _ = c := by group
    have hy : n⁻¹ * t₁ * n = (n⁻¹ * p * n) * c := by
      rw [hpc]
      calc n⁻¹ * (p * c) * n = (n⁻¹ * p * n) * (n⁻¹ * c * n) := by group
        _ = (n⁻¹ * p * n) * c := by rw [hcn]
    have hyP : n⁻¹ * t₁ * n ∈ (P : Subgroup Y) := by
      rw [hy]
      exact P.mul_mem (mem_inf.mp hp'T).1 (hd.centralizer_le hc)
    obtain ⟨-, T'', hT'', hyT''⟩ := hcl t₁ ht₁Γ n hyP
    have hpp : p * (n⁻¹ * p * n) = n⁻¹ * p * n * p := by
      have hcp' : (n⁻¹ * p * n) * c = c * (n⁻¹ * p * n) :=
        mem_centralizer_iff.mp hc _ (mem_inf.mp hp'T).2
      by_cases hTT : T'' = T₁
      · rcases eq_or_eq_inv_of_orderOf_four ht₁4 (ht₁gen ▸ hTT ▸ hyT'') (hord_conj n) with h | h
        · rw [hy, hpc] at h
          rw [mul_right_cancel h]
        · rw [hy, hpc] at h
          have h1 : p * (n⁻¹ * p * n) = (c * c)⁻¹ := by
            calc p * (n⁻¹ * p * n) = p * ((n⁻¹ * p * n) * c) * c⁻¹ := by group
              _ = p * (p * c)⁻¹ * c⁻¹ := by rw [h]
              _ = p * (c⁻¹ * p⁻¹) * c⁻¹ := by group
              _ = p * (p⁻¹ * c⁻¹) * c⁻¹ := by
                rw [show c⁻¹ * p⁻¹ = p⁻¹ * c⁻¹ by
                  rw [← mul_inv_rev, ← mul_inv_rev, hcpc]]
              _ = (c * c)⁻¹ := by group
          have hmem : p * (n⁻¹ * p * n) ∈ K ⊓ centralizer (K : Set Y) :=
            mem_inf.mpr ⟨K.mul_mem hpK (mem_inf.mp hp'T).2,
              h1 ▸ inv_mem (mul_mem hc hc)⟩
          rw [hd.inf_centralizer, mem_bot] at hmem
          have h2 : n⁻¹ * p * n = p⁻¹ := eq_inv_of_mul_eq_one_right hmem
          rw [h2, mul_inv_cancel, inv_mul_cancel]
      · have hyt := commute_of_commutator_eq_bot (hcomm T'' hT'' T₁ hT₁ hTT) hyT'' ht₁T
        rw [hy, hpc] at hyt
        have h1 : (n⁻¹ * p * n) * p * (c * c) = p * (n⁻¹ * p * n) * (c * c) := by
          calc (n⁻¹ * p * n) * p * (c * c) = ((n⁻¹ * p * n) * c) * (p * c) := by
                rw [mul_assoc (n⁻¹ * p * n) c, ← mul_assoc c p c, ← hcpc]; group
            _ = (p * c) * ((n⁻¹ * p * n) * c) := hyt
            _ = p * (n⁻¹ * p * n) * (c * c) := by
                rw [mul_assoc p c, ← mul_assoc c (n⁻¹ * p * n) c, ← hcp']; group
        exact (mul_right_cancel h1).symm
    exact hpZ (hn p hpT rfl hpp)
  · obtain ⟨-, hcent, s, hsT, hsm⟩ := hd.aut t₁ ht₁P ht₁Z hout
    have hcent' := hcent (by rw [← hat]; exact haZ)
    have hsP : s ∈ (P : Subgroup Y) := (mem_inf.mp hsT).1
    have hxP : s⁻¹ * t₁ * s ∈ (P : Subgroup Y) :=
      P.mul_mem (P.mul_mem (P.inv_mem hsP) ht₁P) hsP
    obtain ⟨-, T', hT', hxT'⟩ := hcl t₁ ht₁Γ s hxP
    have hm : s⁻¹ * (t₁ * s * t₁⁻¹) = s⁻¹ * t₁ * s * t₁⁻¹ := by group
    rw [hm] at hsm
    by_cases hTT : T' = T₁
    · rcases eq_or_eq_inv_of_orderOf_four ht₁4 (ht₁gen ▸ hTT ▸ hxT') (hord_conj s) with h | h
      · rw [h, mul_inv_cancel] at hsm
        exact hsm (one_mem _)
      · rw [h] at hsm
        apply hsm
        have : t₁⁻¹ * t₁⁻¹ = a⁻¹ := by rw [hat]; group
        rw [this]
        exact inv_mem haZ
    · have hxt := commute_of_commutator_eq_bot (hcomm T' hT' T₁ hT₁ hTT) hxT' ht₁T
      have hmT : s⁻¹ * t₁ * s * t₁⁻¹ ∈ T := by
        have : s⁻¹ * t₁ * s * t₁⁻¹ = s⁻¹ * (t₁ * s * t₁⁻¹) := by group
        rw [this]
        exact T.mul_mem (T.inv_mem hsT) (ht₁N s hsT)
      apply hsm
      apply hcent' _ hmT
      calc t₁ * (s⁻¹ * t₁ * s * t₁⁻¹) * t₁⁻¹ = (t₁ * (s⁻¹ * t₁ * s)) * t₁⁻¹ * t₁⁻¹ := by
            group
        _ = ((s⁻¹ * t₁ * s) * t₁) * t₁⁻¹ * t₁⁻¹ := by rw [← hxt]
        _ = s⁻¹ * t₁ * s * t₁⁻¹ := by group

end CFSG.ComponentClassification.Asc76.L26
