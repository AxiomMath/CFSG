module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchHKS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem SzC1.comm_mul_mul_eq {G : Type*} [Group G] {y z r s : G} (hrz : r * z = z * r)
    (hsy : s * y = y * s) (hrs : r * s = s * r) :
    (y * r) * (z * s) * (y * r)⁻¹ * (z * s)⁻¹ = y * z * y⁻¹ * z⁻¹ := by
  have h1 : r * (z * s) = (z * s) * r := by rw [← mul_assoc, hrz, mul_assoc, hrs, ← mul_assoc]
  have h2 : s * y⁻¹ = y⁻¹ * s := by
    calc s * y⁻¹ = y⁻¹ * (y * s) * y⁻¹ := by group
      _ = y⁻¹ * (s * y) * y⁻¹ := by rw [hsy]
      _ = y⁻¹ * s := by group
  calc (y * r) * (z * s) * (y * r)⁻¹ * (z * s)⁻¹ = y * (r * (z * s)) * r⁻¹ * y⁻¹ * (z * s)⁻¹ := by
        group
    _ = y * ((z * s) * r) * r⁻¹ * y⁻¹ * (z * s)⁻¹ := by rw [h1]
    _ = y * z * (s * y⁻¹) * s⁻¹ * z⁻¹ := by group
    _ = y * z * (y⁻¹ * s) * s⁻¹ * z⁻¹ := by rw [h2]
    _ = y * z * y⁻¹ * z⁻¹ := by group

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}
  {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}

section Translation

variable
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem conj_eq_of_translation (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G))
    (htr : ∀ c, h.famPerm hK hc hμ hlam n c = h.famPerm hK hc hμ hlam n 0 + c) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) : (n : G) * b * (n : G)⁻¹ = b := by
  have hK' := h.card_K hK hc
  have hcomm : ∀ y ∈ szT₁ L T, ∀ z ∈ szT₁ L T,
      (n : G) * (y * z * y⁻¹ * z⁻¹) * (n : G)⁻¹ = y * z * y⁻¹ * z⁻¹ := by
    intro y hy z hz
    obtain ⟨r, hr, hyr⟩ := h.conj_mem_mul_V_of_translation hK hc hμ hlam n htr hy
    obtain ⟨s, hs, hzs⟩ := h.conj_mem_mul_V_of_translation hK hc hμ hlam n htr hz
    calc (n : G) * (y * z * y⁻¹ * z⁻¹) * (n : G)⁻¹ =
          ((n : G) * y * (n : G)⁻¹) * ((n : G) * z * (n : G)⁻¹) *
            ((n : G) * y * (n : G)⁻¹)⁻¹ * ((n : G) * z * (n : G)⁻¹)⁻¹ := by group
      _ = (y * r) * (z * s) * (y * r)⁻¹ * (z * s)⁻¹ := by rw [hyr, hzs]
      _ = y * z * y⁻¹ * z⁻¹ := SzC1.comm_mul_mul_eq (h.V_comm hr hz).symm
            (h.V_comm hs hy).symm (h.comm r hr s hs)
  have hdec : ∀ g ∈ szT₁ L T ⊔ zpowers t, ∃ y ∈ szT₁ L T, ∃ s : G, (s = 1 ∨ s = t) ∧
      g = y * s := by
    intro g hg
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
      h.t_mem_normalizer_T₁ hg with h1 | h1
    · exact ⟨g, h1, 1, Or.inl rfl, (mul_one g).symm⟩
    · exact ⟨g * t, h1, t, Or.inr rfl, by rw [mul_assoc, h.t_mul_self, mul_one]⟩
  have hsT : ∀ s : G, (s = 1 ∨ s = t) → ∀ y ∈ szT₁ L T, s * y = y * s := by
    rintro s (rfl | rfl) y hy
    · group
    · exact (h.t_comm hy).symm
  have hss : ∀ s s' : G, (s = 1 ∨ s = t) → (s' = 1 ∨ s' = t) → s * s' = s' * s := by
    rintro s s' (rfl | rfl) (rfl | rfl) <;> group
  have hle : ⁅szT₁ L T ⊔ zpowers t, szT₁ L T ⊔ zpowers t⁆ ≤
      centralizer ({(n : G)} : Set G) := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨y₁, hy₁, s₁, hs₁, rfl⟩ := hdec g₁ hg₁
    obtain ⟨y₂, hy₂, s₂, hs₂, rfl⟩ := hdec g₂ hg₂
    rw [mem_centralizer_singleton_iff, commutatorElement_def,
      SzC1.comm_mul_mul_eq (hsT s₁ hs₁ y₂ hy₂) (hsT s₂ hs₂ y₁ hy₁) (hss s₁ s₂ hs₁ hs₂)]
    have e := hcomm y₁ hy₁ y₂ hy₂
    calc y₁ * y₂ * y₁⁻¹ * y₂⁻¹ * (n : G) =
          ((n : G) * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (n : G)⁻¹) * (n : G) := by rw [e]
      _ = (n : G) * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
  rw [hc.szA₁_eq_commutator h.ha hK' h.start.mem_centralizer_szT₁] at hb
  have e := mem_centralizer_singleton_iff.mp (hle hb)
  rw [← e, mul_inv_cancel_right]

theorem famPerm_zero_eq_zero_of_translation (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G))
    (htr : ∀ c, h.famPerm hK hc hμ hlam n c = h.famPerm hK hc hμ hlam n 0 + c) :
    h.famPerm hK hc hμ hlam n 0 = 0 := by
  have hK' := h.card_K hK hc
  set c₀ := h.famPerm hK hc hμ hlam n 0 with hc₀
  have hspec := h.famPerm_spec hK hc hμ hlam n 0
  rw [h.fam_zero hK hc hμ, ← hc₀] at hspec
  have hy₀ := SzC1.szSec_mem hc c₀
  have h1 : (1 : G) ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := one_mem _
  have hcentral : SzC1.szSec hc c₀ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy₀, mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨r, hr, hyr⟩ := h.conj_mem_mul_V_of_translation hK hc hμ hlam n htr hy
    have hmem : y * r ∈ SzC1.szFam U₁ t hc c₀ := by
      rw [← hspec, ← hyr]
      exact ⟨y, hy, rfl⟩
    have hmem' : y * r ∈ centralizer ({SzC1.szSec hc c₀ * 1 * t} : Set G) := by
      rw [mul_one]
      exact (mem_inf.mp hmem).2
    have hr2 := (h.mem_cent_iff hμ hy₀ h1 hy hr).mp hmem'
    have hy2 := h.conj_eq_of_translation hK hc hμ hlam n htr (hc.sq_mem_szA₁ h.ha hK' hy)
    have hry : r * y = y * r := (h.V_comm hr hy).symm
    have e : y ^ 2 * r ^ 2 = y ^ 2 := by
      calc y ^ 2 * r ^ 2 = (y * r) ^ 2 := by
            rw [sq, sq, sq]
            calc y * y * (r * r) = y * (y * r) * r := by group
              _ = y * (r * y) * r := by rw [hry]
              _ = y * r * (y * r) := by group
        _ = ((n : G) * y * (n : G)⁻¹) ^ 2 := by rw [hyr]
        _ = (n : G) * y ^ 2 * (n : G)⁻¹ := conj_pow
        _ = y ^ 2 := hy2
    have hr1 : r ^ 2 = 1 := by
      have := congrArg (fun z => (y ^ 2)⁻¹ * z) e
      simpa using this
    rw [hr1] at hr2
    have e1 : SzC1.szSec hc c₀ * y = y * SzC1.szSec hc c₀ := by
      calc SzC1.szSec hc c₀ * y =
            y * (y⁻¹ * SzC1.szSec hc c₀ * y * (SzC1.szSec hc c₀)⁻¹) * SzC1.szSec hc c₀ := by group
        _ = y * SzC1.szSec hc c₀ := by rw [← hr2, mul_one]
    exact e1.symm
  have hu := hc.u_eq_zero_of_mem_szA₁ h.ha hK' hcentral
  rwa [SzC1.szSec_u hc] at hu

end Translation

section HKS


theorem corner_of_nu_ne_zero (h : SzC1Stage G L f a t T d V U U₁ k)
    (hK : Fintype.card K = 2 ^ f) (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) :
    f = 3 ∧ Nat.card ((h.famPerm hK hc hμ hlam).range ⊓
        MulAction.stabilizer (Equiv.Perm K) (0 : K) : Subgroup (Equiv.Perm K)) = 21 ∧
      Nat.card (h.famPerm hK hc hμ hlam).range = 168 ∧
      IsSimpleGroup (h.famPerm hK hc hμ hlam).range := by
  have hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U := fun hU => h.false_of_isSylow hU
  have : IsSimpleGroup G := h.start.setting.1
  have hf2 : 2 ≤ f := by have := h.ha; rw [h.hfa]; omega
  have hY : normalizer (U : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : U.Normal := normalizer_eq_top_iff.mp htop
    rcases hnorm.eq_bot_or_eq_top with hbot | htop'
    · have hcard := h.card_U
      rw [hbot, Subgroup.card_bot] at hcard
      have : 0 < (2 ^ f) ^ (k + 3) := by positivity
      omega
    · exact hU ⟨h.isPGroup_U.toSylow (by rw [htop', Subgroup.index_top]; norm_num),
        rfl⟩
  have hcardK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨hodd, hdvd⟩ := h.famPerm_stabilizer hK hc hκ hμ hlam hν hU
  rcases odd_stabilizer_two_transitive_kProper_of_dvd h.start.setting.2.2.1 hY
    (h.famPerm hK hc hμ hlam) (h.famPerm hK hc hμ hlam).range le_rfl
    (h.famPerm_two_transitive hK hc hκ hμ hlam hν hU) (by omega) hcardK 0 hodd hdvd with
    ⟨A, hAN, hAnorm, -, -, hAcard, hreg⟩ | ⟨hf3, h21, h168, hsimple, -⟩
  · exfalso
    have hA2 : IsPGroup 2 A := IsPGroup.of_card hAcard
    have haff : ∀ x ∈ A, ∃ ℓ : K →+ K, ∀ c, x c = x 0 + ℓ c := by
      intro x hx
      obtain ⟨n, rfl⟩ := hAN hx
      exact h.famPerm_affine hK hc hμ hlam n
    set δn : normalizer (U : Set G) := ⟨d⁻¹, inv_mem h.d_mem_normalizer_U⟩
    have hδA : ∀ x ∈ A, (h.famPerm hK hc hμ hlam δn)⁻¹ * x * h.famPerm hK hc hμ hlam δn ∈ A := by
      intro x hx
      have hδN : (h.famPerm hK hc hμ hlam δn)⁻¹ ∈ (h.famPerm hK hc hμ hlam).range :=
        inv_mem ⟨δn, rfl⟩
      have := hAnorm.conj_mem ⟨x, hAN hx⟩ (mem_subgroupOf.mpr hx) ⟨_, hδN⟩
      rw [mem_subgroupOf] at this
      simpa using this
    have htrans := SzC1.translation_of_affine hK hf2 hκ hA2 haff
      (h.famPerm_d_inv hK hc hμ hlam) hδA
    obtain ⟨⟨x, hxA⟩, hx1, -⟩ := hreg 0 1
    obtain ⟨n, hn⟩ := hAN hxA
    have htr : ∀ c, h.famPerm hK hc hμ hlam n c = h.famPerm hK hc hμ hlam n 0 + c := by
      intro c
      rw [hn]
      exact htrans x hxA c
    have h0 := h.famPerm_zero_eq_zero_of_translation hK hc hμ hlam n htr
    rw [hn] at h0
    exact one_ne_zero (hx1.symm.trans h0)
  · exact ⟨hf3, h21, h168, hsimple⟩

theorem eq_three_of_nu_ne_zero (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) : f = 3 := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  exact (h.corner_of_nu_ne_zero hK hc hκ hμ hlam hν).1

end HKS

end SzC1Stage

@[expose] def SzEightCorner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (a : ℕ) (t : G) (T : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), SzC1Stage G L 3 a t T d V U U₁ k →
    U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) → U₁ ≤ centralizer (V : Set G) →
    (∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 ≠ 1) →
    ¬ (∃ S : Sylow 2 G, (S : Subgroup G) = U) → False

section Corner


theorem szC1NuExclusion_of_eightCorner (h8 : SzEightCorner) : SzC1NuExclusion := by
  intro G _ _ L f a t T d V U U₁ k h hμ hlam hν hU
  have hf3 := h.eq_three_of_nu_ne_zero hμ hlam hν
  subst hf3
  exact h8 G L a t T d V U U₁ k h hlam hμ hν hU

theorem SzC1Stage.nu_eq_zero_of_eightCorner (h8 : SzEightCorner) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G} {d : G} {V U U₁ : Subgroup G} {k : ℕ}
    (h : SzC1Stage G L f a t T d V U U₁ k) :
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) ∧ U₁ ≤ centralizer (V : Set G) ∧
      U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) ∧
      ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1 :=
  h.nu_eq_zero (szC1NuExclusion_of_eightCorner h8)

end Corner

end CFSG.SeitzReduction.RankOne
