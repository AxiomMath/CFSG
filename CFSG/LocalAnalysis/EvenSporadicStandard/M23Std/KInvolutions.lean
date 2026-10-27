module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KSquares

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

structure FixedData (L : Subgroup G) (F : Subgroup G) : Prop where
  fixed : ∀ f ∈ F, f ≠ 1 → ∀ x ∈ F,
    (∀ b ∈ L, (∀ y, y ∈ F ↔ b * y * b⁻¹ ∈ F) → b * f * b⁻¹ = f →
      b * x * b⁻¹ = x ∨ b * x * b⁻¹ = x * f) → x = 1 ∨ x = f

omit [Finite G] in
theorem phiv_inv (h : OneClassData L z t) (D : NData L F) {k : G} (hk : k ∈ Ksub z F) :
    phiv z k⁻¹ = (phiv z k)⁻¹ := by
  have h1 := phiv_mul h D (Subgroup.inv_mem _ hk) hk
  rw [inv_mul_cancel] at h1
  have h0 : phiv z 1 = 1 := by
    unfold phiv
    simp [h.z_mul_self]
  rw [h0] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

omit [Finite G] in
theorem zk_eq (h : OneClassData L z t) (D : NData L F) {k : G} (hk : k ∈ Ksub z F) :
    z * k = k * z * phiv z k := by
  have hfF : phiv z k ∈ F := phiv_mem h D hk
  have hz : k * z * k⁻¹ = z * phiv z k := by
    unfold phiv
    rw [← mul_assoc, h.z_mul_self, one_mul]
  have hfk : phiv z k * k = k * phiv z k := (mem_Ksub.1 hk).2 _ hfF
  have h1 : k * z = z * phiv z k * k := mul_inv_eq_iff_eq_mul.1 hz
  calc z * k = z * k * (phiv z k * phiv z k) := by rw [D.F_sq _ hfF, mul_one]
    _ = z * (k * phiv z k) * phiv z k := by simp only [mul_assoc]
    _ = z * (phiv z k * k) * phiv z k := by rw [hfk]
    _ = (z * phiv z k * k) * phiv z k := by simp only [mul_assoc]
    _ = k * z * phiv z k := by rw [h1]

omit [Finite G] in
theorem sq_mul_F (D : NData L F) {k u : G} (hk : k ∈ Ksub z F)
    (hu : u ∈ F) : (k * u) * (k * u) = k * k := by
  have hkc : k * u = u * k := ((mem_Ksub.1 hk).2 u hu).symm
  calc k * u * (k * u) = k * (u * k) * u := by simp only [mul_assoc]
    _ = k * (k * u) * u := by rw [← hkc]
    _ = k * k * (u * u) := by simp only [mul_assoc]
    _ = k * k := by rw [D.F_sq u hu, mul_one]

omit [Finite G] in
theorem sq_mul_zF (h : OneClassData L z t) (D : NData L F) {k u : G} (hk : k ∈ Ksub z F)
    (hu : u ∈ F) : (k * (u * z)) * (k * (u * z)) = k * k * phiv z k := by
  have hfF : phiv z k ∈ F := phiv_mem h D hk
  have hkc : k * u = u * k := ((mem_Ksub.1 hk).2 u hu).symm
  have hzf : z * phiv z k = phiv z k * z := h.z_comm _ (D.F_le hfF)
  have hzu : z * u = u * z := h.z_comm u (D.F_le hu)
  have huf : u * phiv z k = phiv z k * u := D.F_comm u hu _ hfF
  have hcomb : u * z * phiv z k * u * z = phiv z k := by
    calc u * z * phiv z k * u * z = u * (z * phiv z k) * u * z := by simp only [mul_assoc]
      _ = u * (phiv z k * z) * u * z := by rw [hzf]
      _ = u * phiv z k * (z * u) * z := by simp only [mul_assoc]
      _ = u * phiv z k * (u * z) * z := by rw [hzu]
      _ = u * phiv z k * u * (z * z) := by simp only [mul_assoc]
      _ = u * phiv z k * u := by rw [h.z_mul_self, mul_one]
      _ = phiv z k * u * u := by rw [huf]
      _ = phiv z k := by rw [mul_assoc, D.F_sq u hu, mul_one]
  calc k * (u * z) * (k * (u * z)) = k * u * (z * k) * u * z := by simp only [mul_assoc]
    _ = k * u * (k * z * phiv z k) * u * z := by rw [zk_eq h D hk]
    _ = k * (u * k) * z * phiv z k * u * z := by simp only [mul_assoc]
    _ = k * (k * u) * z * phiv z k * u * z := by rw [← hkc]
    _ = (k * k) * (u * z * phiv z k * u * z) := by simp only [mul_assoc]
    _ = k * k * phiv z k := by rw [hcomb]

omit [Finite G] in
theorem sq_conj_cases (h : OneClassData L z t) (D : NData L F) {k k' : G} (hk : k ∈ Ksub z F)
    (hk' : k' ∈ Ksub z F) (hff : phiv z k' = phiv z k) :
    k' * k' = k * k ∨ k' * k' = k * k * phiv z k := by
  have hfF : phiv z k ∈ F := phiv_mem h D hk
  have he : k⁻¹ * k' ∈ Ksub z F := Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) hk'
  have hphi : phiv z (k⁻¹ * k') = 1 := by
    rw [phiv_mul h D (Subgroup.inv_mem _ hk) hk', phiv_inv h D hk, hff]
    exact inv_mul_cancel _
  have hE := (phiv_eq_one_iff h D he).1 hphi
  obtain ⟨u, hu, b, hb, hub⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) hE
  have hk'e : k' = k * (u * b) := by
    rw [← hub]
    group
  rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
  · left
    rw [hk'e, hb1, mul_one]
    exact sq_mul_F D hk hu
  · right
    rw [hk'e, hbz]
    exact sq_mul_zF h D hk hu

theorem sq_mem_pair (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    {k : G} (hk : k ∈ Ksub z F) (hf1 : phiv z k ≠ 1) :
    k * k = 1 ∨ k * k = phiv z k := by
  refine X.fixed _ (phiv_mem h D hk) hf1 _ (sq_mem_F h hZ D hk) ?_
  intro b hbL hbF hbf
  obtain ⟨hbk, hphi⟩ := conj_mem_Ksub h D hbL hbF hk
  have := sq_conj_cases h D hk hbk (hphi.trans hbf)
  have hsq : (b * k * b⁻¹) * (b * k * b⁻¹) = b * (k * k) * b⁻¹ := by group
  rw [hsq] at this
  exact this

theorem exists_involution (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ x ∈ Ksub z F, phiv z x = f ∧ x * x = 1 := by
  obtain ⟨κ, hκ⟩ := phiHom_surjective h hZ D htrans ⟨f, hf⟩
  have hkK : (κ : G) ∈ Ksub z F := κ.2
  have hkf : phiv z κ = f := congrArg Subtype.val hκ
  rcases sq_mem_pair h hZ D X hkK (hkf ▸ hf1) with h1 | h1
  · exact ⟨κ, hkK, hkf, h1⟩
  · have hzK : z ∈ Ksub z F := E_le_K h D (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    refine ⟨κ * z, Subgroup.mul_mem _ hkK hzK, ?_, ?_⟩
    · have hz1 : phiv z z = 1 := by
        unfold phiv
        simp [h.z_mul_self]
      rw [phiv_mul h D hkK hzK, hz1, mul_one, hkf]
    · have := sq_mul_zF h D hkK (Subgroup.one_mem F)
      simp only [one_mul] at this
      rw [this, h1, hkf]
      exact D.F_sq f hf

omit [Finite G] in
theorem involutions_eq (h : OneClassData L z t) (D : NData L F) {x : G} (hx : x ∈ Ksub z F)
    (hx2 : x * x = 1) (hf1 : phiv z x ≠ 1) {k : G} :
    (k ∈ Ksub z F ∧ phiv z k = phiv z x ∧ k * k = 1) ↔ ∃ u ∈ F, k = x * u := by
  constructor
  · rintro ⟨hk, hkx, hk2⟩
    have he : x⁻¹ * k ∈ Ksub z F := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hk
    have hphi : phiv z (x⁻¹ * k) = 1 := by
      rw [phiv_mul h D (Subgroup.inv_mem _ hx) hk, phiv_inv h D hx, hkx]
      exact inv_mul_cancel _
    obtain ⟨u, hu, b, hb, hub⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le_centralizer_of_le h D.F_le) ((phiv_eq_one_iff h D he).1 hphi)
    have hke : k = x * (u * b) := by
      rw [← hub]
      group
    rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
    · exact ⟨u, hu, by rw [hke, hb1, mul_one]⟩
    · exfalso
      rw [hbz] at hke
      rw [hke, sq_mul_zF h D hx hu, hx2, one_mul] at hk2
      exact hf1 hk2
  · rintro ⟨u, hu, rfl⟩
    have huK : u ∈ Ksub z F := E_le_K h D (Subgroup.mem_sup_left hu)
    refine ⟨Subgroup.mul_mem _ hx huK, ?_, ?_⟩
    · have hu1 : phiv z u = 1 := (phiv_eq_one_iff h D huK).2 (Subgroup.mem_sup_left hu)
      rw [phiv_mul h D hx huK, hu1, mul_one]
    · rw [sq_mul_F D hx hu, hx2]

end CFSG.EvenSporadicStandard.M23Std
