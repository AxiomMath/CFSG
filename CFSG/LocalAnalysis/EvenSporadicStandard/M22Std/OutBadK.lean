module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKStruct
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutL1

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

omit [Finite G] in
theorem F_mem_Ksub (h : OutOne L z F) {u : G} (hu : u ∈ F) :
    u ∈ Ksub z F :=
  E_le_K h (Subgroup.mem_sup_left hu)

omit [Finite G] in
theorem z_mem_Ksub (h : OutOne L z F) : z ∈ Ksub z F :=
  E_le_K h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

omit [Finite G] in
theorem phiv_mul_z (h : OutOne L z F) {x : G} (hx : x ∈ Ksub z F) :
    phiv z (x * z) = phiv z x := by
  rw [phiv_mul h hx (z_mem_Ksub h), phiv_z_self h, mul_one]

omit [Finite G] in
theorem sq_mul_z (h : OutOne L z F) {x : G} (hx : x ∈ Ksub z F) :
    (x * z) * (x * z) = x * x * phiv z x := by
  have := sq_mul_zF h hx (Subgroup.one_mem F)
  simpa only [one_mul] using this

omit [Finite G] in
theorem mul_z_mul_z (h : OutOne L z F) {x x' : G} (hx' : x' ∈ Ksub z F) :
    (x * z) * (x' * z) = x * x' * phiv z x' := by
  have hfF : phiv z x' ∈ F := phiv_mem h hx'
  have hzf : z * phiv z x' = phiv z x' * z := h.z_comm _ (h.F_le hfF)
  calc x * z * (x' * z) = x * (z * x') * z := by group
    _ = x * (x' * z * phiv z x') * z := by rw [zk_eq h hx']
    _ = x * x' * (z * phiv z x') * z := by group
    _ = x * x' * (phiv z x' * z) * z := by rw [hzf]
    _ = x * x' * phiv z x' * (z * z) := by group
    _ = x * x' * phiv z x' := by rw [h.z_mul_self, mul_one]

omit [Finite G] in
theorem mul_z_mul_z_self (h : OutOne L z F) {k : G} : k * z * z = k := by
  rw [mul_assoc, h.z_mul_self, mul_one]

theorem pair_sq (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) {x x' : G} (hx : x ∈ Ksub z F)
    (hx' : x' ∈ Ksub z F) (hx2 : x * x = 1) (hx'2 : x' * x' = 1) (hf : phiv z x ≠ 1)
    (hf' : phiv z x' ≠ 1) (hne : phiv z x ≠ phiv z x') :
    (x * x') * (x * x') = phiv z x * phiv z x' ∧ phiv z (x * x') ≠ 1 := by
  have hxx' : x * x' ∈ Ksub z F := Subgroup.mul_mem _ hx hx'
  have hphi : phiv z (x * x') = phiv z x * phiv z x' := phiv_mul h hx hx'
  have hne1 : phiv z x * phiv z x' ≠ 1 := by
    intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_eq_of_mul_eq_one_right (h.F_sq _ (phiv_mem h hx'))
  have hne1' : phiv z (x * x') ≠ 1 := by rw [hphi]; exact hne1
  refine ⟨?_, hne1'⟩
  rcases sq_mem_pair h hsq X hxx' hne1' with h1 | h1
  · exact absurd h1 (hbad x hx x' hx' hx2 hx'2 hf hf' hne)
  · rw [h1, hphi]

omit [Finite G] in
theorem lbad_sq (h : OutOne L z F) {k : G} (hk : k ∈ LbadSet z F) :
    k * k = phiv z k := by
  obtain ⟨-, hkF | ⟨-, hk2⟩⟩ := hk
  · rw [h.F_sq k hkF, phiv_eq_one_of_mem_F h hkF]
  · exact hk2

omit [Finite G] in
theorem lbad_mul_F (h : OutOne L z F) {u k : G} (hu : u ∈ F)
    (hk : k ∈ LbadSet z F) : u * k ∈ LbadSet z F := by
  obtain ⟨hkK, hkF | ⟨hk1, hk2⟩⟩ := hk
  · exact ⟨Subgroup.mul_mem _ (F_mem_Ksub h hu) hkK, Or.inl (Subgroup.mul_mem _ hu hkF)⟩
  · have huK := F_mem_Ksub h hu
    have hphi : phiv z (u * k) = phiv z k := by
      rw [phiv_mul h huK hkK, phiv_eq_one_of_mem_F h hu, one_mul]
    refine ⟨Subgroup.mul_mem _ huK hkK, Or.inr ⟨by rw [hphi]; exact hk1, ?_⟩⟩
    have huk : u * k = k * u := (mem_Ksub.1 hkK).2 u hu
    calc u * k * (u * k) = u * (k * u) * k := by simp only [mul_assoc]
      _ = u * (u * k) * k := by rw [← huk]
      _ = (u * u) * (k * k) := by simp only [mul_assoc]
      _ = phiv z (u * k) := by rw [h.F_sq u hu, one_mul, hk2, hphi]

omit [Finite G] in
theorem lbad_same (h : OutOne L z F) {k k' : G} (hk : k ∈ Ksub z F)
    (hk' : k' ∈ Ksub z F) (hk1 : phiv z k ≠ 1) (hk2 : k * k = phiv z k)
    (hk'2 : k' * k' = phiv z k') (hff : phiv z k' = phiv z k) : ∃ u ∈ F, k' = k * u := by
  have hzK := z_mem_Ksub h
  have hx : k * z ∈ Ksub z F := Subgroup.mul_mem _ hk hzK
  have hx' : k' * z ∈ Ksub z F := Subgroup.mul_mem _ hk' hzK
  have hx2 : (k * z) * (k * z) = 1 := by
    rw [sq_mul_z h hk, hk2]
    exact h.F_sq _ (phiv_mem h hk)
  have hx'2 : (k' * z) * (k' * z) = 1 := by
    rw [sq_mul_z h hk', hk'2]
    exact h.F_sq _ (phiv_mem h hk')
  have hφ : phiv z (k * z) ≠ 1 := by rw [phiv_mul_z h hk]; exact hk1
  obtain ⟨u, hu, hxu⟩ := (involutions_eq h hx hx2 hφ (k := k' * z)).1
    ⟨hx', by rw [phiv_mul_z h hk', phiv_mul_z h hk, hff], hx'2⟩
  refine ⟨u, hu, ?_⟩
  have hzu : z * u = u * z := h.z_comm u (h.F_le hu)
  calc k' = (k' * z) * z := (mul_z_mul_z_self h).symm
    _ = (k * z * u) * z := by rw [hxu]
    _ = k * (z * u) * z := by simp only [mul_assoc]
    _ = k * (u * z) * z := by rw [hzu]
    _ = k * u * (z * z) := by simp only [mul_assoc]
    _ = k * u := by rw [h.z_mul_self, mul_one]

theorem lbad_diff (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) {k k' : G} (hk : k ∈ Ksub z F)
    (hk' : k' ∈ Ksub z F) (hk1 : phiv z k ≠ 1) (hk2 : k * k = phiv z k)
    (hk'1 : phiv z k' ≠ 1) (hk'2 : k' * k' = phiv z k') (hne : phiv z k ≠ phiv z k') :
    (k * k' ∈ Ksub z F ∧ phiv z (k * k') ≠ 1 ∧ (k * k') * (k * k') = phiv z (k * k')) ∧
      k * k' = k' * k := by
  have hzK := z_mem_Ksub h
  have hx : k * z ∈ Ksub z F := Subgroup.mul_mem _ hk hzK
  have hx' : k' * z ∈ Ksub z F := Subgroup.mul_mem _ hk' hzK
  have hx2 : (k * z) * (k * z) = 1 := by
    rw [sq_mul_z h hk, hk2]
    exact h.F_sq _ (phiv_mem h hk)
  have hx'2 : (k' * z) * (k' * z) = 1 := by
    rw [sq_mul_z h hk', hk'2]
    exact h.F_sq _ (phiv_mem h hk')
  have hxφ : phiv z (k * z) = phiv z k := phiv_mul_z h hk
  have hx'φ : phiv z (k' * z) = phiv z k' := phiv_mul_z h hk'
  obtain ⟨hsq, hne1⟩ := pair_sq h hsq X hbad hx hx' hx2 hx'2 (by rw [hxφ]; exact hk1)
    (by rw [hx'φ]; exact hk'1) (by rw [hxφ, hx'φ]; exact hne)
  rw [hxφ, hx'φ] at hsq
  have hxx' : (k * z) * (k' * z) ∈ Ksub z F := Subgroup.mul_mem _ hx hx'
  have hfF := phiv_mem h hk
  have hf'F := phiv_mem h hk'
  have hkk' : k * k' = (k * z) * (k' * z) * phiv z k' := by
    calc k * k' = k * z * z * (k' * z * z) := by rw [mul_z_mul_z_self h, mul_z_mul_z_self h]
      _ = k * z * (k' * z) * phiv z (k' * z) := mul_z_mul_z h hx'
      _ = k * z * (k' * z) * phiv z k' := by rw [hx'φ]
  have hk'k : k' * k = (k' * z) * (k * z) * phiv z k := by
    calc k' * k = k' * z * z * (k * z * z) := by rw [mul_z_mul_z_self h, mul_z_mul_z_self h]
      _ = k' * z * (k * z) * phiv z (k * z) := mul_z_mul_z h hx
      _ = k' * z * (k * z) * phiv z k := by rw [hxφ]
  have hc2 : (phiv z k * phiv z k') * (phiv z k * phiv z k') = 1 := by
    calc phiv z k * phiv z k' * (phiv z k * phiv z k')
        = phiv z k * (phiv z k' * phiv z k) * phiv z k' := by simp only [mul_assoc]
      _ = phiv z k * (phiv z k * phiv z k') * phiv z k' := by rw [h.F_comm _ hf'F _ hfF]
      _ = (phiv z k * phiv z k) * (phiv z k' * phiv z k') := by simp only [mul_assoc]
      _ = 1 := by rw [h.F_sq _ hfF, h.F_sq _ hf'F, one_mul]
  have hw1 : ((k * z) * (k' * z)) * ((k * z) * (k' * z) * (phiv z k * phiv z k')) = 1 := by
    rw [← mul_assoc, hsq, hc2]
  have hrev : (k' * z) * (k * z) = ((k * z) * (k' * z)) * (phiv z k * phiv z k') := by
    have h1 : ((k * z) * (k' * z)) * ((k' * z) * (k * z)) = 1 := by
      calc (k * z) * (k' * z) * ((k' * z) * (k * z))
          = (k * z) * ((k' * z) * (k' * z)) * (k * z) := by simp only [mul_assoc]
        _ = 1 := by rw [hx'2, mul_one, hx2]
    have h2 := eq_inv_of_mul_eq_one_right h1
    have h3 := eq_inv_of_mul_eq_one_right hw1
    rw [h2, ← h3]
  have hcf : phiv z k * phiv z k' = phiv z k' * phiv z k := h.F_comm _ hfF _ hf'F
  have hcomm : k * k' = k' * k := by
    rw [hkk', hk'k, hrev]
    have h3 : phiv z k * phiv z k' * phiv z k = phiv z k' := by
      calc phiv z k * phiv z k' * phiv z k = phiv z k' * phiv z k * phiv z k := by rw [hcf]
        _ = phiv z k' * (phiv z k * phiv z k) := by simp only [mul_assoc]
        _ = phiv z k' := by rw [h.F_sq _ hfF, mul_one]
    rw [mul_assoc _ (phiv z k * phiv z k') (phiv z k), h3]
  refine ⟨⟨Subgroup.mul_mem _ hk hk', ?_, ?_⟩, hcomm⟩
  · have := hne1
    rw [phiv_mul h hx hx', hxφ, hx'φ] at this
    rw [phiv_mul h hk hk']
    exact this
  · have hphi : phiv z (k * k') = phiv z k * phiv z k' := phiv_mul h hk hk'
    rw [hphi, hkk', sq_mul_F h hxx' hf'F, hsq]

theorem lbad_mul (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) {k k' : G} (hk : k ∈ LbadSet z F)
    (hk' : k' ∈ LbadSet z F) : k * k' ∈ LbadSet z F := by
  by_cases hkF : k ∈ F
  · exact lbad_mul_F h hkF hk'
  by_cases hk'F : k' ∈ F
  · have hc : k * k' = k' * k := ((mem_Ksub.1 hk.1).2 k' hk'F).symm
    rw [hc]
    exact lbad_mul_F h hk'F hk
  obtain ⟨hkK, hk1, hk2⟩ : k ∈ Ksub z F ∧ phiv z k ≠ 1 ∧ k * k = phiv z k := by
    obtain ⟨hkK, hF | ⟨a, b⟩⟩ := hk
    · exact absurd hF hkF
    · exact ⟨hkK, a, b⟩
  obtain ⟨hk'K, hk'1, hk'2⟩ : k' ∈ Ksub z F ∧ phiv z k' ≠ 1 ∧ k' * k' = phiv z k' := by
    obtain ⟨hkK, hF | ⟨a, b⟩⟩ := hk'
    · exact absurd hF hk'F
    · exact ⟨hkK, a, b⟩
  by_cases hff : phiv z k = phiv z k'
  · obtain ⟨u, hu, hku⟩ := lbad_same h hkK hk'K hk1 hk2 hk'2 hff.symm
    refine ⟨Subgroup.mul_mem _ hkK hk'K, Or.inl ?_⟩
    rw [hku, ← mul_assoc, hk2]
    exact Subgroup.mul_mem _ (phiv_mem h hkK) hu
  · obtain ⟨⟨hmK, hm1, hm2⟩, -⟩ := lbad_diff h hsq X hbad hkK hk'K hk1 hk2 hk'1 hk'2 hff
    exact ⟨hmK, Or.inr ⟨hm1, hm2⟩⟩

theorem lbad_comm (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) {k k' : G} (hk : k ∈ LbadSet z F)
    (hk' : k' ∈ LbadSet z F) : k * k' = k' * k := by
  by_cases hkF : k ∈ F
  · exact (mem_Ksub.1 hk'.1).2 k hkF
  by_cases hk'F : k' ∈ F
  · exact ((mem_Ksub.1 hk.1).2 k' hk'F).symm
  obtain ⟨hkK, hk1, hk2⟩ : k ∈ Ksub z F ∧ phiv z k ≠ 1 ∧ k * k = phiv z k := by
    obtain ⟨hkK, hF | ⟨a, b⟩⟩ := hk
    · exact absurd hF hkF
    · exact ⟨hkK, a, b⟩
  obtain ⟨hk'K, hk'1, hk'2⟩ : k' ∈ Ksub z F ∧ phiv z k' ≠ 1 ∧ k' * k' = phiv z k' := by
    obtain ⟨hkK, hF | ⟨a, b⟩⟩ := hk'
    · exact absurd hF hk'F
    · exact ⟨hkK, a, b⟩
  by_cases hff : phiv z k = phiv z k'
  · obtain ⟨u, hu, hku⟩ := lbad_same h hkK hk'K hk1 hk2 hk'2 hff.symm
    have huk : u * k = k * u := (mem_Ksub.1 hkK).2 u hu
    rw [hku]
    calc k * (k * u) = k * (u * k) := by rw [huk]
      _ = k * u * k := by simp only [mul_assoc]
  · exact (lbad_diff h hsq X hbad hkK hk'K hk1 hk2 hk'1 hk'2 hff).2

omit [Finite G] in
theorem lbad_inv (h : OutOne L z F) {k : G} (hk : k ∈ LbadSet z F) :
    k⁻¹ ∈ LbadSet z F := by
  by_cases hkF : k ∈ F
  · exact ⟨Subgroup.inv_mem _ (F_mem_Ksub h hkF), Or.inl (Subgroup.inv_mem _ hkF)⟩
  · have hkK := hk.1
    have hk2 := lbad_sq h hk
    have hfF := phiv_mem h hkK
    have h1 : phiv z k * k * k = 1 := by
      calc phiv z k * k * k = phiv z k * (k * k) := by simp only [mul_assoc]
        _ = 1 := by rw [hk2]; exact h.F_sq _ hfF
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact lbad_mul_F h hfF hk

@[expose] def LbadSub (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) : Subgroup G where
  carrier := LbadSet z F
  mul_mem' := fun hk hk' => lbad_mul h hsq X hbad hk hk'
  one_mem' := lbad_one_mem
  inv_mem' := fun hk => lbad_inv h hk

theorem F_le_LbadSub (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) : F ≤ LbadSub h hsq X hbad :=
  fun _ hu => ⟨F_mem_Ksub h hu, Or.inl hu⟩

theorem exists_lbad_over (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ k ∈ LbadSet z F, phiv z k = f := by
  obtain ⟨x, hxK, hxf, hx2⟩ := exists_involution h hsq X htrans hf hf1
  refine ⟨x * z, ⟨Subgroup.mul_mem _ hxK (z_mem_Ksub h), Or.inr ⟨?_, ?_⟩⟩, ?_⟩
  · rw [phiv_mul_z h hxK, hxf]
    exact hf1
  · rw [sq_mul_z h hxK, hx2, one_mul, phiv_mul_z h hxK]
  · rw [phiv_mul_z h hxK, hxf]

theorem lbad_conj (h : OutOne L z F) {b k : G} (hbL : b ∈ L)
    (hbF : ∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) (hk : k ∈ LbadSet z F) : b * k * b⁻¹ ∈ LbadSet z F := by
  obtain ⟨hkK, hkF | ⟨hk1, hk2⟩⟩ := hk
  · exact ⟨(conj_mem_Ksub h hbL hbF hkK).1, Or.inl ((hbF k).1 hkF)⟩
  · obtain ⟨hbK, hphi⟩ := conj_mem_Ksub h hbL hbF hkK
    refine ⟨hbK, Or.inr ⟨?_, ?_⟩⟩
    · rw [hphi]
      intro h1
      apply hk1
      calc phiv z k = b⁻¹ * (b * phiv z k * b⁻¹) * b := by group
        _ = b⁻¹ * 1 * b := by rw [h1]
        _ = 1 := by group
    · calc b * k * b⁻¹ * (b * k * b⁻¹) = b * (k * k) * b⁻¹ := by group
        _ = b * phiv z k * b⁻¹ := by rw [hk2]
        _ = phiv z (b * k * b⁻¹) := hphi.symm

end OutOne

end CFSG.EvenSporadicStandard.M22Std
