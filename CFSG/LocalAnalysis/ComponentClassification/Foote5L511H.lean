module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511G

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_coreActionKernel_conjugate_iff' {J : Subgroup G} {g x : G} :
    x ∈ coreActionKernel (conjugate J g) ↔ g * x * g⁻¹ ∈ coreActionKernel J := by
  refine ⟨fun hx => ?_, mem_coreActionKernel_conjugate⟩
  have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ coreActionKernel (conjugate J g) := by
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]
  have h2 := mem_coreActionKernel_conjugate h1
  rwa [conjugate_conjugate_inv] at h2

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

theorem z_mul_self : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]

theorem card_centralizer_Q_le_two (hKF : Foote5FieldCentralizerC) (h𝕊 : FooteSimpleType 𝕊)
    {r : G} (hrS : r ∈ S) (hr2 : r * r = 1) (hrinn : actG L ε r ∉ innAut5 𝕊)
    (hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r) (hrz : r * z = z * r) {S₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁)
    (hS₁W : S₁ ≤ centralizer ((kleinFourOfCommutingInvolutions r z hr2 h.z_mul_self hrz :
      Subgroup G) : Set G))
    (hXS₁ : Q ⊓ centralizer ({r} : Set G) ≤ S₁) {n : G} (hnS₁ : n ∈ normalizer (S₁ : Set G))
    (hnz : n * z * n⁻¹ = r) (hnr : n * r * n⁻¹ = r * z) :
    Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  set W := kleinFourOfCommutingInvolutions r z hr2 hz2 hrz with hWdef
  have hrN := h.S_le hrS
  have hzS := h.zS_mem
  have hzN := h.S_le hzS
  have hz1 : actG L ε z = 1 := (h.actG_eq_one_iff_mem_Q ε hzS).mpr h.zQ
  have hWmem : ∀ w ∈ W, w = r * z ∨ w = r ∨ w = z ∨ w = 1 := fun w hw =>
    (mem_kleinFour_iff hr2 hz2 hrz).mp hw
  have hrW : r ∈ W := (mem_kleinFour_iff hr2 hz2 hrz).mpr (Or.inr (Or.inl rfl))
  have hzW : z ∈ W := (mem_kleinFour_iff hr2 hz2 hrz).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hWS : W ≤ S := fun w hw => by
    rcases hWmem w hw with rfl | rfl | rfl | rfl
    · exact mul_mem hrS hzS
    · exact hrS
    · exact hzS
    · exact one_mem _
  have hW : ∀ w ∈ W, actG L ε w = 1 ∨ actG L ε w = actG L ε r := fun w hw => by
    rcases hWmem w hw with rfl | rfl | rfl | rfl
    · right
      rw [actG_mul ε hrN hzN, hz1, mul_one]
    · exact Or.inr rfl
    · exact Or.inl hz1
    · exact Or.inl (actG_one ε)
  have hrL : r ∉ L := fun h1 => hrinn (by rw [actG_of_mem_self ε h1]; exact ⟨_, rfl⟩)
  have hS₁N : S₁ ≤ normalizer (L : Set G) := fun y hy => h.centralizer_le_normalizer
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hS₁W hy) z hzW).symm)
  have hFr : footeF L₀ r = conjugate L n⁻¹ := by
    have h1 := footeF_conj h.sec4.huniq z n⁻¹
    rwa [inv_inv, hnz, h.footeF_z] at h1
  have hrF : IsTwoComponentAt r (footeF L₀ r) := by
    have h1 := (h.pmax.conjugate n⁻¹).1
    rwa [inv_inv, hnz, ← hFr] at h1
  have hrF' : footeF L₀ r ∈ footeFamilyOf L₀ := by
    rw [hFr]
    exact conjugate_mem_footeFamilyOf h.memF n⁻¹
  set P := S₁ ⊓ coreActionKernel L with hPdef
  set P' := conjugate P n⁻¹ with hP'def
  have hnS₁' : ∀ y ∈ S₁, n⁻¹ * y * n ∈ S₁ := fun y hy => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hnS₁) y).mp hy
    rwa [inv_inv] at h1
  have hP'mem : ∀ x ∈ P', x ∈ S₁ ∧ x ∈ coreActionKernel (footeF L₀ r) := by
    intro x hx
    rw [hP'def, mem_conjugate_iff] at hx
    have hx' := mem_inf.mp hx
    refine ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp hnS₁ _).mp hx'.1
      rwa [show n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ = x by group] at h1
    · rw [hFr, mem_coreActionKernel_conjugate_iff']
      exact hx'.2
  have hTI : P ⊓ P' = ⊥ := by
    by_contra hne
    have hPn : S₁ ≤ normalizer (P : Set G) := le_normalizer_of_conj_mem fun s hs x hx =>
      mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hx).1) (inv_mem hs),
        (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L (hS₁N hs)) x).mp
          (mem_inf.mp hx).2⟩
    have hP'n : S₁ ≤ normalizer (P' : Set G) := le_normalizer_of_conj_mem fun s hs x hx => by
      rw [hP'def, mem_conjugate_iff] at hx ⊢
      have h1 := (mem_normalizer_iff.mp (hPn (hnS₁' s hs)) _).mp hx
      rwa [show n⁻¹ * s * n * (n⁻¹ * x * n⁻¹⁻¹) * (n⁻¹ * s * n)⁻¹ =
        n⁻¹ * (s * x * s⁻¹) * n⁻¹⁻¹ by group] at h1
    have hPP'n : S₁ ≤ normalizer ((P ⊓ P' : Subgroup G) : Set G) :=
      le_normalizer_of_conj_mem fun s hs x hx => mem_inf.mpr
        ⟨(mem_normalizer_iff.mp (hPn hs) x).mp (mem_inf.mp hx).1,
          (mem_normalizer_iff.mp (hP'n hs) x).mp (mem_inf.mp hx).2⟩
    obtain ⟨w, hwPP, hw2, hwZ⟩ := exists_involution_center hS₁
      (inf_le_left.trans inf_le_left) hPP'n hne
    have hwP := (mem_inf.mp hwPP).1
    have hwP' := (mem_inf.mp hwPP).2
    rw [hP'def, mem_conjugate_iff, inv_inv] at hwP'
    set w' := n⁻¹ * w * n with hw'def
    have hw'2 : orderOf w' = 2 := by
      have h1 : n⁻¹ * w * n = MulAut.conj n⁻¹ w := by rw [MulAut.conj_apply, inv_inv]
      rw [hw'def, h1, MulEquiv.orderOf_eq]
      exact hw2
    have hw'Z : ∀ s ∈ S₁, s * w' = w' * s := by
      intro s hs
      have h1 := hwZ _ ((mem_normalizer_iff.mp hnS₁ s).mp hs)
      calc s * w' = n⁻¹ * ((n * s * n⁻¹) * w) * n := by rw [hw'def]; group
        _ = n⁻¹ * (w * (n * s * n⁻¹)) * n := by rw [h1]
        _ = w' * s := by rw [hw'def]; group
    have hzS₁ : z ∈ S₁ := hXS₁ (mem_inf.mpr ⟨h.zQ, mem_centralizer_singleton_iff.mpr hrz.symm⟩)
    have h1 : z ∈ coreActionKernel (footeF L₀ w) :=
      (h.mem_coreActionKernel_footeF_iff (mem_inf.mp hwP).2 hw2 (hS₁N hzS₁)
        (mem_centralizer_singleton_iff.mpr (hwZ z hzS₁))).mpr (h.Q_le h.zQ)
    have hzn : n⁻¹ * z * n = r * z := by
      calc n⁻¹ * z * n = n⁻¹ * (n * (r * z) * n⁻¹) * n := by
            rw [show n * (r * z) * n⁻¹ = (n * r * n⁻¹) * (n * z * n⁻¹) by group, hnr, hnz,
              show r * z * r = r * (z * r) by group, ← hrz,
              show r * (r * z) = (r * r) * z by group, hr2, one_mul]
        _ = r * z := by group
    have hrzS₁ : r * z ∈ S₁ := by
      rw [← hzn]
      exact hnS₁' z hzS₁
    have h2 : r * z ∈ coreActionKernel (footeF L₀ w') := by
      have h3 : footeF L₀ w' = conjugate (footeF L₀ w) n := by
        rw [hw'def]
        exact footeF_conj h.sec4.huniq w n
      rw [h3, mem_coreActionKernel_conjugate_iff', ← hzn,
        show n * (n⁻¹ * z * n) * n⁻¹ = z by group]
      exact h1
    have hw'P : w' ∈ P := hwP'
    have h4 := (h.mem_coreActionKernel_footeF_iff (mem_inf.mp hw'P).2 hw'2 (hS₁N hrzS₁)
      (mem_centralizer_singleton_iff.mpr (hw'Z _ hrzS₁))).mp h2
    have h5 := (actG_eq_one_iff ε (hS₁N hrzS₁)).mpr h4
    rw [actG_mul ε hrN hzN, hz1, mul_one] at h5
    exact hrinn (by rw [h5]; exact one_mem _)
  have hrN' := hrN
  set β := actG L ε r with hβ
  have hβ2 : β * β = 1 := by rw [hβ, ← actG_mul ε hrN hrN, hr2, actG_one]
  have hβfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), β ρ = ρ := (h.actG_fix_iff ε hrS).mpr hrR
  obtain ⟨M, hMfix, -, -, hMaut⟩ := hKF 𝕊 h𝕊 β hβ2 hrinn ⟨h.Rbar ε, hβfix⟩
  have hact : ∀ p ∈ P', actG L ε p = 1 ∨ actG L ε p = β := by
    intro p hp
    obtain ⟨hpS₁, hpC⟩ := hP'mem p hp
    have hpN := hS₁N hpS₁
    refine hMaut _ fun m hm => ?_
    obtain ⟨k, hkL, hkW, rfl⟩ := h.exists_lift_of_fixed_W ε hWS hW (hMfix m hm)
    rw [actG_psi ε hpN]
    have hpW := hS₁W hpS₁
    have hkr : k ∈ normalizer (coreActionKernel (footeF L₀ r) : Set G) :=
      normalizer_le_normalizer_coreActionKernel _ (le_normalizer_of_mem_footeFamilyOf
        h.sec4.huniq hrF hrF' (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp hkW r hrW).symm))
    have hy : k⁻¹ * (p * k * p⁻¹) ∈ oddCoreIn L := by
      refine h.mem_oddCoreIn_of_mem_coreActionKernel_footeF ε hKF h𝕊 hrS hr2 hrinn hrR hWS hrW
        hW hrW hrL hrF hrF' ?_ ?_ ?_
      · exact mul_mem (inv_mem hkL)
          ((mem_normalizer_iff.mp hpN k).mp hkL)
      · exact mul_mem (inv_mem hkW) (mul_mem (mul_mem hpW hkW) (inv_mem hpW))
      · have h1 := (mem_normalizer_iff.mp (inv_mem hkr) p).mp hpC
        rw [inv_inv] at h1
        rw [show k⁻¹ * (p * k * p⁻¹) = (k⁻¹ * p * k) * p⁻¹ by group]
        exact mul_mem h1 (inv_mem hpC)
    exact ((psi_eq_iff ε ⟨k, hkL⟩ _).mpr hy).symm
  have hP'1 : ∀ p ∈ P', actG L ε p = 1 → p = 1 := by
    intro p hp hp1
    have h1 : p ∈ P ⊓ P' := mem_inf.mpr ⟨mem_inf.mpr ⟨(hP'mem p hp).1,
      (actG_eq_one_iff ε (hS₁N (hP'mem p hp).1)).mp hp1⟩, hp⟩
    rwa [hTI, mem_bot] at h1
  have hP'2 : Nat.card P' ≤ 2 := by
    by_cases hex : ∃ p₀ ∈ P', actG L ε p₀ = β
    · obtain ⟨p₀, hp₀, hp₀β⟩ := hex
      refine (SmallLocal.card_le_of_forall_mem_finset ({1, p₀} : Finset G) fun p hp => ?_).trans
        Finset.card_le_two
      rcases hact p hp with h1 | h1
      · rw [hP'1 p hp h1]
        exact Finset.mem_insert_self _ _
      · have h2 : p₀⁻¹ * p = 1 := hP'1 _ (mul_mem (inv_mem hp₀) hp) (by
          rw [actG_mul ε (inv_mem (hS₁N (hP'mem p₀ hp₀).1)) (hS₁N (hP'mem p hp).1),
            actG_inv ε (hS₁N (hP'mem p₀ hp₀).1), hp₀β, h1, inv_mul_cancel])
        rw [inv_mul_eq_one] at h2
        rw [← h2]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · push Not at hex
      refine (SmallLocal.card_le_of_forall_mem_finset ({1} : Finset G) fun p hp => ?_).trans
        (by simp)
      rcases hact p hp with h1 | h1
      · rw [hP'1 p hp h1]
        exact Finset.mem_singleton_self _
      · exact absurd h1 (hex p hp)
  have hXP : Q ⊓ centralizer ({r} : Set G) ≤ P := fun x hx =>
    mem_inf.mpr ⟨hXS₁ hx, h.Q_le (mem_inf.mp hx).1⟩
  calc Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ Nat.card P := card_le_of_le hXP
    _ = Nat.card P' := (card_conjugate_eq_card P n⁻¹).symm
    _ ≤ 2 := hP'2

end Sec5

end CFSG.ComponentClassification.Foote5
