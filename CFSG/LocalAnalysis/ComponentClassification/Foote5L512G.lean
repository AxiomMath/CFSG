module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsF
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511H
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512D

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

theorem mem_W₂_of_mem_kernel_L512 (hQd : DSDData ↥Q) {b : G} (hbQ : b ∈ Q) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hbz : b ≠ z) (hbzc : b * z = z * b) {W₂ P : Subgroup G}
    (hW₂ : ∀ w, w ∈ W₂ ↔ w = b * z ∨ w = b ∨ w = z ∨ w = 1) (hP2 : IsPGroup 2 P)
    (hW₂P : W₂ ≤ P) (hPW₂ : ∀ p ∈ P, ∀ w ∈ W₂, p * w = w * p) {d : G} (hdP : d ∈ P)
    (hdC : d ∈ coreActionKernel L) : d ∈ W₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  have hbW₂ : b ∈ W₂ := (hW₂ b).mpr (Or.inr (Or.inl rfl))
  have hzW₂ : z ∈ W₂ := (hW₂ z).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hD2 : IsPGroup 2 ↥(P ⊓ coreActionKernel L) := hP2.to_le inf_le_left
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf h.sylQ inf_le_right hD2
  have hbD : b ∈ P ⊓ coreActionKernel L := mem_inf.mpr ⟨hW₂P hbW₂, h.Q_le hbQ⟩
  have hzD : z ∈ P ⊓ coreActionKernel L := mem_inf.mpr ⟨hW₂P hzW₂, h.Q_le h.zQ⟩
  have hdD : d ∈ P ⊓ coreActionKernel L := mem_inf.mpr ⟨hdP, hdC⟩
  have hinj : ∀ u v : G, c⁻¹ * u * c = c⁻¹ * v * c → u = v := fun u v huv => by
    rwa [mul_left_inj, mul_right_inj] at huv
  have hsq : ∀ u : G, u * u = 1 → c⁻¹ * u * c * (c⁻¹ * u * c) = 1 := fun u hu => by
    rw [show c⁻¹ * u * c * (c⁻¹ * u * c) = c⁻¹ * (u * u) * c by group, hu]
    group
  have hne1 : ∀ u : G, u ≠ 1 → c⁻¹ * u * c ≠ 1 := fun u hu h1 => hu (by
    calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hcomm : ∀ u v : G, u * v = v * u →
      c⁻¹ * u * c * (c⁻¹ * v * c) = c⁻¹ * v * c * (c⁻¹ * u * c) := fun u v huv => by
    rw [show c⁻¹ * u * c * (c⁻¹ * v * c) = c⁻¹ * (u * v) * c by group, huv]
    group
  rcases mem_of_commute_four_of_dsd_L512 h.sylQ.isPGroup hQd (hc b hbD) (hc z hzD) (hsq b hb2)
    (hsq z hz2) (hne1 b hb1) (hne1 z hz1) (fun h1 => hbz (hinj _ _ h1)) (hcomm b z hbzc)
    (hc d hdD) (hcomm d b (hPW₂ d hdP b hbW₂)) (hcomm d z (hPW₂ d hdP z hzW₂))
    with h1 | h1 | h1 | h1
  · exact (hW₂ d).mpr (Or.inl (hinj _ _ (h1.trans (by group))))
  · exact (hW₂ d).mpr (Or.inr (Or.inl (hinj _ _ h1)))
  · exact (hW₂ d).mpr (Or.inr (Or.inr (Or.inl (hinj _ _ h1))))
  · exact (hW₂ d).mpr (Or.inr (Or.inr (Or.inr (hinj _ _ (h1.trans (by group))))))

include ε in
theorem exists_cyclic_mod_L512 (hL24 : Foote5Lemma24iiV) (h𝕊 : FooteSimpleType 𝕊)
    (hQd : DSDData ↥Q) {a b : G} (ha : a ∈ S ⊓ L) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hat : a ≠ t) (hbQ : b ∈ Q) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hbzc : b * z = z * b) {W₁ W₂ P : Subgroup G}
    (hW₁ : ∀ w, w ∈ W₁ ↔ w = a * t ∨ w = a ∨ w = t ∨ w = 1)
    (hW₂ : ∀ w, w ∈ W₂ ↔ w = b * z ∨ w = b ∨ w = z ∨ w = 1) (hP2 : IsPGroup 2 P)
    (hW₁P : W₁ ≤ P) (hW₂P : W₂ ≤ P) (hPW₁ : ∀ p ∈ P, ∀ w ∈ W₁, p * w = w * p)
    (hPW₂ : ∀ p ∈ P, ∀ w ∈ W₂, p * w = w * p) :
    ∃ p₀ ∈ P, ∀ q ∈ P, ∃ j : ℕ, ∃ w ∈ W₁ ⊔ W₂, q = p₀ ^ j * w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.t_mul_self
  have hatc : a * t = t * a := h.tZ a (mem_inf.mp ha).1
  have hzW₂ : z ∈ W₂ := (hW₂ z).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have haW₁ : a ∈ W₁ := (hW₁ a).mpr (Or.inr (Or.inl rfl))
  have htW₁ : t ∈ W₁ := (hW₁ t).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hPN : P ≤ normalizer (L : Set G) := fun p hp =>
    h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr (hPW₂ p hp z hzW₂))
  have haN : a ∈ normalizer (L : Set G) := le_normalizer (mem_inf.mp ha).2
  have htN : t ∈ normalizer (L : Set G) := le_normalizer h.tL
  have hR1 : ∀ r ∈ S ⊓ L, actG L ε r = 1 → r = 1 := fun r hr h1 => by
    have h2 := (h.actG_eq_one_iff_mem_Q ε (mem_inf.mp hr).1).mp h1
    have h3 : r ∈ Q ⊓ L := mem_inf.mpr ⟨h2, (mem_inf.mp hr).2⟩
    rwa [h.Q_inf_L, mem_bot] at h3
  have hα2 : actG L ε a * actG L ε a = 1 := by rw [← actG_mul ε haN haN, ha2, actG_one]
  have hβ2 : actG L ε t * actG L ε t = 1 := by rw [← actG_mul ε htN htN, ht2, actG_one]
  have hαβ : Commute (actG L ε a) (actG L ε t) := by
    change actG L ε a * actG L ε t = actG L ε t * actG L ε a
    rw [← actG_mul ε haN htN, ← actG_mul ε htN haN, hatc]
  have hα1 : actG L ε a ≠ 1 := fun h1 => ha1 (hR1 a ha h1)
  have hβ1 : actG L ε t ≠ 1 := fun h1 => h.t_ne_one (hR1 t h.tR h1)
  have hαβne : actG L ε a ≠ actG L ε t := fun h1 => hat (by
    have h2 : actG L ε (a * t⁻¹) = 1 := by
      rw [actG_mul ε haN (inv_mem htN), actG_inv ε htN]
      exact mul_inv_eq_one.mpr h1
    exact mul_inv_eq_one.mp (hR1 _ (mul_mem ha (inv_mem h.tR)) h2))
  set V := kleinFourOfCommutingInvolutions (actG L ε a) (actG L ε t) hα2 hβ2 hαβ with hVdef
  have hV4 : IsKleinFour V :=
    isKleinFour_kleinFourOfCommutingInvolutions _ _ hα2 hβ2 hα1 hβ1 hαβne hαβ
  have hVmem : ∀ v ∈ V, v = actG L ε a * actG L ε t ∨ v = actG L ε a ∨ v = actG L ε t ∨
      v = 1 := fun v hv => (mem_kleinFour_iff hα2 hβ2 hαβ).mp hv
  have hαinn : actG L ε a ∈ innAut5 𝕊 := by
    rw [actG_of_mem_self ε (mem_inf.mp ha).2]
    exact ⟨_, rfl⟩
  have hβinn : actG L ε t ∈ innAut5 𝕊 := by
    rw [actG_of_mem_self ε h.tL]
    exact ⟨_, rfl⟩
  have hVinn : V ≤ innAut5 𝕊 := fun v hv => by
    rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact mul_mem hαinn hβinn
    · exact hαinn
    · exact hβinn
    · exact one_mem _
  set X := actImage L ε P with hXdef
  have hX2 : IsPGroup 2 X := isPGroup_actImage ε hP2
  have hXC : X ≤ centralizer (V : Set (MulAut 𝕊)) := by
    intro ξ hξ
    obtain ⟨p, hp, rfl⟩ := (mem_actImage ε hPN).mp hξ
    have hpN := hPN hp
    have hca : actG L ε a * actG L ε p = actG L ε p * actG L ε a := by
      rw [← actG_mul ε haN hpN, ← actG_mul ε hpN haN, hPW₁ p hp a haW₁]
    have hct : actG L ε t * actG L ε p = actG L ε p * actG L ε t := by
      rw [← actG_mul ε htN hpN, ← actG_mul ε hpN htN, hPW₁ p hp t htW₁]
    rw [mem_centralizer_iff]
    intro v hv
    rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [mul_assoc, hct, ← mul_assoc, hca, mul_assoc]
    · exact hca
    · exact hct
    · rw [one_mul, mul_one]
  obtain ⟨Ps, hPs, hXPs⟩ := exists_isSylowOf_ge_of_le hXC hX2
  obtain ⟨f, hfV⟩ := hL24 𝕊 h𝕊 V hV4 hVinn Ps hPs
  have hXle : X ≤ zpowers f ⊔ V := hXPs.trans hfV.le
  have hfC : f ∈ centralizer (V : Set (MulAut 𝕊)) :=
    hPs.le (hfV ▸ mem_sup_left (mem_zpowers f))
  have hcommFV : ∀ φ ∈ zpowers f, ∀ v ∈ V, φ * v = v * φ := by
    intro φ hφ v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hφ
    exact (Commute.zpow_left (mem_centralizer_iff.mp hfC v hv).symm i).eq
  have hCcyc : IsCyclic ↥(X ⊓ zpowers f) := Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥(X ⊓ zpowers f))
  obtain ⟨p₀, hp₀P, hp₀γ⟩ := (mem_actImage ε hPN).mp (mem_inf.mp γ.2).1
  refine ⟨p₀, hp₀P, fun q hq => ?_⟩
  have hqN := hPN hq
  obtain ⟨φ, hφ, v, hv, hφv⟩ := exists_mul_of_mem_sup_commute hcommFV
    (hXle (actG_mem_actImage ε hPN hq))
  obtain ⟨w, hwW₁, hwv⟩ : ∃ w ∈ W₁, actG L ε w = v := by
    rcases hVmem v hv with h1 | h1 | h1 | h1
    · exact ⟨a * t, (hW₁ _).mpr (Or.inl rfl), by rw [actG_mul ε haN htN, h1]⟩
    · exact ⟨a, haW₁, h1.symm⟩
    · exact ⟨t, htW₁, h1.symm⟩
    · exact ⟨1, one_mem _, by rw [actG_one, h1]⟩
  have hwP := hW₁P hwW₁
  have hwN := hPN hwP
  have hφX : φ ∈ X := by
    have h1 : φ = actG L ε (q * w⁻¹) := by
      rw [actG_mul ε hqN (inv_mem hwN), actG_inv ε hwN, hφv, hwv]
      group
    rw [h1]
    exact actG_mem_actImage ε hPN (mul_mem hq (inv_mem hwP))
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hγ ⟨φ, mem_inf.mpr ⟨hφX, hφ⟩⟩)
  have hφi : actG L ε (p₀ ^ i) = φ := by
    rw [actG_zpow ε (hPN hp₀P), hp₀γ]
    exact congrArg Subtype.val hi
  have hp₀iN := hPN (zpow_mem hp₀P i)
  have hdP : (p₀ ^ i * w)⁻¹ * q ∈ P := mul_mem (inv_mem (mul_mem (zpow_mem hp₀P i) hwP)) hq
  have hdC : (p₀ ^ i * w)⁻¹ * q ∈ coreActionKernel L := by
    refine (actG_eq_one_iff ε (hPN hdP)).mp ?_
    rw [actG_mul ε (inv_mem (mul_mem hp₀iN hwN)) hqN, actG_inv ε (mul_mem hp₀iN hwN),
      actG_mul ε hp₀iN hwN, hφi, hwv, hφv, inv_mul_cancel]
  have hdW₂ := h.mem_W₂_of_mem_kernel_L512 hQd hbQ hb2 hb1 hbz hbzc hW₂ hP2 hW₂P hPW₂ hdP hdC
  obtain ⟨j, hj⟩ : ∃ j : ℕ, p₀ ^ j = p₀ ^ i := by
    have h1 := (isOfFinOrder_of_finite p₀).mem_powers_iff_mem_zpowers.mpr
      (mem_zpowers_iff.mpr ⟨i, rfl⟩)
    exact (Submonoid.mem_powers_iff _ _).mp h1
  refine ⟨j, w * ((p₀ ^ i * w)⁻¹ * q), mul_mem (mem_sup_left hwW₁) (mem_sup_right hdW₂), ?_⟩
  rw [hj]
  group

end Sec5

end CFSG.ComponentClassification.Foote5
