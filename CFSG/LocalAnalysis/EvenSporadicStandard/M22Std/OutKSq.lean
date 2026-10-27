module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KInvolutions

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

variable (h : OutOne L z F)

include h in
theorem sq_mem_F [Finite G] (hsq : ∀ g : G, g * g ≠ z) {k : G} (hk : k ∈ Ksub z F) :
    k * k ∈ F := by
  have hkk : k * k ∈ Ksub z F := Subgroup.mul_mem _ hk hk
  have hphi : phiv z (k * k) = 1 := by
    rw [h.phiv_mul hk hk]
    exact h.F_sq _ (h.phiv_mem hk)
  have hE := (h.phiv_eq_one_iff hkk).1 hphi
  obtain ⟨f, hf, b, hb, hfb⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) hE
  rcases h.mem_zpowers_cases hb with hb1 | hbz
  · rw [hfb, hb1, mul_one]
    exact hf
  · exfalso
    rw [hbz] at hfb
    have hconj : IsConj z (k * k) := by
      rw [hfb, ← h.z_comm f (h.F_le hf)]
      exact h.fused f hf
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine hsq (c⁻¹ * k * c) ?_
    calc c⁻¹ * k * c * (c⁻¹ * k * c) = c⁻¹ * (k * k) * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]
      _ = z := by group

include h in
theorem phiv_inv {k : G} (hk : k ∈ Ksub z F) : phiv z k⁻¹ = (phiv z k)⁻¹ := by
  have h1 := h.phiv_mul (Subgroup.inv_mem _ hk) hk
  rw [inv_mul_cancel] at h1
  have h0 : phiv z 1 = 1 := by
    unfold phiv
    simp [h.z_mul_self]
  rw [h0] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

include h in
theorem zk_eq {k : G} (hk : k ∈ Ksub z F) : z * k = k * z * phiv z k := by
  have hfF : phiv z k ∈ F := h.phiv_mem hk
  have hz : k * z * k⁻¹ = z * phiv z k := by
    unfold phiv
    rw [← mul_assoc, h.z_mul_self, one_mul]
  have hfk : phiv z k * k = k * phiv z k := (mem_Ksub.1 hk).2 _ hfF
  have h1 : k * z = z * phiv z k * k := mul_inv_eq_iff_eq_mul.1 hz
  calc z * k = z * k * (phiv z k * phiv z k) := by rw [h.F_sq _ hfF, mul_one]
    _ = z * (k * phiv z k) * phiv z k := by simp only [mul_assoc]
    _ = z * (phiv z k * k) * phiv z k := by rw [hfk]
    _ = (z * phiv z k * k) * phiv z k := by simp only [mul_assoc]
    _ = k * z * phiv z k := by rw [h1]

include h in
theorem sq_mul_F {k u : G} (hk : k ∈ Ksub z F) (hu : u ∈ F) : (k * u) * (k * u) = k * k := by
  have hkc : k * u = u * k := ((mem_Ksub.1 hk).2 u hu).symm
  calc k * u * (k * u) = k * (u * k) * u := by simp only [mul_assoc]
    _ = k * (k * u) * u := by rw [← hkc]
    _ = k * k * (u * u) := by simp only [mul_assoc]
    _ = k * k := by rw [h.F_sq u hu, mul_one]

include h in
theorem sq_mul_zF {k u : G} (hk : k ∈ Ksub z F) (hu : u ∈ F) :
    (k * (u * z)) * (k * (u * z)) = k * k * phiv z k := by
  have hfF : phiv z k ∈ F := h.phiv_mem hk
  have hkc : k * u = u * k := ((mem_Ksub.1 hk).2 u hu).symm
  have hzf : z * phiv z k = phiv z k * z := h.z_comm _ (h.F_le hfF)
  have hzu : z * u = u * z := h.z_comm u (h.F_le hu)
  have huf : u * phiv z k = phiv z k * u := h.F_comm u hu _ hfF
  have hcomb : u * z * phiv z k * u * z = phiv z k := by
    calc u * z * phiv z k * u * z = u * (z * phiv z k) * u * z := by simp only [mul_assoc]
      _ = u * (phiv z k * z) * u * z := by rw [hzf]
      _ = u * phiv z k * (z * u) * z := by simp only [mul_assoc]
      _ = u * phiv z k * (u * z) * z := by rw [hzu]
      _ = u * phiv z k * u * (z * z) := by simp only [mul_assoc]
      _ = u * phiv z k * u := by rw [h.z_mul_self, mul_one]
      _ = phiv z k * u * u := by rw [huf]
      _ = phiv z k := by rw [mul_assoc, h.F_sq u hu, mul_one]
  calc k * (u * z) * (k * (u * z)) = k * u * (z * k) * u * z := by simp only [mul_assoc]
    _ = k * u * (k * z * phiv z k) * u * z := by rw [h.zk_eq hk]
    _ = k * (u * k) * z * phiv z k * u * z := by simp only [mul_assoc]
    _ = k * (k * u) * z * phiv z k * u * z := by rw [← hkc]
    _ = (k * k) * (u * z * phiv z k * u * z) := by simp only [mul_assoc]
    _ = k * k * phiv z k := by rw [hcomb]

include h in
theorem sq_conj_cases {k k' : G} (hk : k ∈ Ksub z F) (hk' : k' ∈ Ksub z F)
    (hff : phiv z k' = phiv z k) : k' * k' = k * k ∨ k' * k' = k * k * phiv z k := by
  have hfF : phiv z k ∈ F := h.phiv_mem hk
  have he : k⁻¹ * k' ∈ Ksub z F := Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) hk'
  have hphi : phiv z (k⁻¹ * k') = 1 := by
    rw [h.phiv_mul (Subgroup.inv_mem _ hk) hk', h.phiv_inv hk, hff]
    exact inv_mul_cancel _
  have hE := (h.phiv_eq_one_iff he).1 hphi
  obtain ⟨u, hu, b, hb, hub⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) hE
  have hk'e : k' = k * (u * b) := by
    rw [← hub]
    group
  rcases h.mem_zpowers_cases hb with hb1 | hbz
  · left
    rw [hk'e, hb1, mul_one]
    exact h.sq_mul_F hk hu
  · right
    rw [hk'e, hbz]
    exact h.sq_mul_zF hk hu

include h in
theorem sq_mem_pair [Finite G] (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F) {k : G}
    (hk : k ∈ Ksub z F) (hf1 : phiv z k ≠ 1) : k * k = 1 ∨ k * k = phiv z k := by
  refine X.fixed _ (h.phiv_mem hk) hf1 _ (h.sq_mem_F hsq hk) ?_
  intro b hbL hbF hbf
  obtain ⟨hbk, hphi⟩ := h.conj_mem_Ksub hbL hbF hk
  have := h.sq_conj_cases hk hbk (hphi.trans hbf)
  have hsq' : (b * k * b⁻¹) * (b * k * b⁻¹) = b * (k * k) * b⁻¹ := by group
  rw [hsq'] at this
  exact this

include h in
theorem exists_involution [Finite G] (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ x ∈ Ksub z F, phiv z x = f ∧ x * x = 1 := by
  obtain ⟨κ, hκ⟩ := h.phiHomO_surjective htrans ⟨f, hf⟩
  have hkK : (κ : G) ∈ Ksub z F := κ.2
  have hkf : phiv z κ = f := congrArg Subtype.val hκ
  rcases h.sq_mem_pair hsq X hkK (hkf ▸ hf1) with h1 | h1
  · exact ⟨κ, hkK, hkf, h1⟩
  · have hzK : z ∈ Ksub z F := h.E_le_K (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    refine ⟨κ * z, Subgroup.mul_mem _ hkK hzK, ?_, ?_⟩
    · have hz1 : phiv z z = 1 := by
        unfold phiv
        simp [h.z_mul_self]
      rw [h.phiv_mul hkK hzK, hz1, mul_one, hkf]
    · have := h.sq_mul_zF hkK (Subgroup.one_mem F)
      simp only [one_mul] at this
      rw [this, h1, hkf]
      exact h.F_sq f hf

include h in
theorem involutions_eq {x : G} (hx : x ∈ Ksub z F) (hx2 : x * x = 1) (hf1 : phiv z x ≠ 1)
    {k : G} : (k ∈ Ksub z F ∧ phiv z k = phiv z x ∧ k * k = 1) ↔ ∃ u ∈ F, k = x * u := by
  constructor
  · rintro ⟨hk, hkx, hk2⟩
    have he : x⁻¹ * k ∈ Ksub z F := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hk
    have hphi : phiv z (x⁻¹ * k) = 1 := by
      rw [h.phiv_mul (Subgroup.inv_mem _ hx) hk, h.phiv_inv hx, hkx]
      exact inv_mul_cancel _
    obtain ⟨u, hu, b, hb, hub⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (h.zpowers_le_cent h.F_le) ((h.phiv_eq_one_iff he).1 hphi)
    have hke : k = x * (u * b) := by
      rw [← hub]
      group
    rcases h.mem_zpowers_cases hb with hb1 | hbz
    · exact ⟨u, hu, by rw [hke, hb1, mul_one]⟩
    · exfalso
      rw [hbz] at hke
      rw [hke, h.sq_mul_zF hx hu, hx2, one_mul] at hk2
      exact hf1 hk2
  · rintro ⟨u, hu, rfl⟩
    have huK : u ∈ Ksub z F := h.E_le_K (Subgroup.mem_sup_left hu)
    refine ⟨Subgroup.mul_mem _ hx huK, ?_, ?_⟩
    · have hu1 : phiv z u = 1 := (h.phiv_eq_one_iff huK).2 (Subgroup.mem_sup_left hu)
      rw [h.phiv_mul hx huK, hu1, mul_one]
    · rw [h.sq_mul_F hx hu, hx2]

end OutOne

end CFSG.EvenSporadicStandard.M22Std
