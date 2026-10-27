module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8CentAut

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G}

private theorem mul_self_of_comm {M : Type} [Semigroup M] {x y : M} (hxy : x * y = y * x) :
    (x * y) * (x * y) = (x * x) * (y * y) :=
  Commute.mul_mul_mul_comm hxy.symm x y

theorem aut_A8_cent (h : F5Std a z) {b c t : G} (hb : IsConj a b) (hc : c ∈ orb2A a b)
    (ht : t ∈ InvIn (Gxy b c)) (htb : t ≠ b) (htc : t ≠ c) (htbc : t ≠ b * c) {η : G → G}
    (hη : IsIsoOn (Gxy b c) (Gxy b c) η) (hfix : ∀ x ∈ Gxyz b c t, η x = x) :
    (∀ x ∈ Gxy b c, η x = x) ∨ ∀ x ∈ Gxy b c, η x = t * x * t⁻¹ := by
  classical
  have hFb : F5Std b z := h.of_isConj hb (IsConj.refl z)
  have hcb : c ∈ orb2A b b := ⟨hb.symm.trans hc.1, hb.symm.trans hc.2⟩
  have hb2 : b * b = 1 := by
    have h2 : b ^ 2 = 1 := by
      simpa [h.orderOf_eq_two (Or.inl hb)] using pow_orderOf_eq_one b
    rwa [pow_two] at h2
  have hc2 : c * c = 1 := by
    have h2 : c ^ 2 = 1 := by
      simpa [h.orderOf_eq_two (Or.inl hc.1)] using pow_orderOf_eq_one c
    rwa [pow_two] at h2
  have hbc : b * c = c * b := h.mul_comm (Or.inl hb) (Or.inl hc.1) (Or.inl hc.2)
  have htX : t ∈ Gxy b c := ht.1
  have hbX : b ∈ Gxy b c := mem_Gxy.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hbc.symm⟩
  have hcX : c ∈ Gxy b c := mem_Gxy.mpr ⟨mem_Gx.mpr hbc, mem_Gx.mpr rfl⟩
  have hbcX : b * c ∈ Gxy b c := (Gxy b c).mul_mem hbX hcX
  have hb_comm : ∀ y ∈ Gxy b c, b * y = y * b := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).1
  have hc_comm : ∀ y ∈ Gxy b c, c * y = y * c := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).2
  have hbc_comm : ∀ y ∈ Gxy b c, (b * c) * y = y * (b * c) := by
    intro y hy
    rw [mul_assoc, hc_comm y hy, ← mul_assoc, hb_comm y hy, mul_assoc]
  have hcent : ∀ u : G, (u = 1 ∨ u = b ∨ u = c ∨ u = b * c) →
      ∀ y ∈ Gxy b c, u * y = y * u := by
    rintro u (rfl | rfl | rfl | rfl) y hy
    · rw [one_mul, mul_one]
    · exact hb_comm y hy
    · exact hc_comm y hy
    · exact hbc_comm y hy
  have hu2 : ∀ u : G, (u = 1 ∨ u = b ∨ u = c ∨ u = b * c) → u * u = 1 := by
    rintro u (rfl | rfl | rfl | rfl)
    · rw [one_mul]
    · exact hb2
    · exact hc2
    · rw [mul_self_of_comm hbc, hb2, hc2, mul_one]
  have hmem_u : ∀ u : G, (u = 1 ∨ u = b ∨ u = c ∨ u = b * c) → u ∈ Gxy b c := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact (Gxy b c).one_mem
    · exact hbX
    · exact hcX
    · exact hbcX
  have hfix_u : ∀ u : G, (u = 1 ∨ u = b ∨ u = c ∨ u = b * c) → η u = u := by
    intro u hu
    refine hfix u (mem_Gxyz.mpr ⟨?_, ?_, ?_⟩)
    · exact mem_Gx.mpr (hcent u hu b hbX).symm
    · exact mem_Gx.mpr (hcent u hu c hcX).symm
    · exact mem_Gx.mpr (hcent u hu t htX).symm
  have hdec := decomp_2A hFb hcb
  obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
    (hFb.loc.fusion3.self.shape_2A c hcb)
  have hdecomp : ∀ x ∈ Gxy b c, ∃ u : G, (u = 1 ∨ u = b ∨ u = c ∨ u = b * c) ∧
      ∃ n ∈ derivedOf (Gxy b c), x = u * n := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hdec x hx
    rcases hxn with h | h | h | h
    · exact ⟨1, Or.inl rfl, n, hn, by rw [h, one_mul]⟩
    · exact ⟨b, Or.inr (Or.inl rfl), n, hn, h⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inl rfl)), n, hn, h⟩
    · exact ⟨b * c, Or.inr (Or.inr (Or.inr rfl)), n, hn, h⟩
  obtain ⟨u, hu, n, hnA, htn⟩ := hdecomp t htX
  have hnX : n ∈ Gxy b c := derivedOf_le _ hnA
  have hn1 : n ≠ 1 := by
    intro hn
    have ht_eq : t = u := by rw [htn, hn, mul_one]
    rcases hu with rfl | rfl | rfl | rfl
    · have h2 := ht.2
      rw [ht_eq, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact htb ht_eq
    · exact htc ht_eq
    · exact htbc ht_eq
  have ht2 : t * t = 1 := by
    have h2 : t ^ 2 = 1 := by simpa [ht.2] using pow_orderOf_eq_one t
    rwa [pow_two] at h2
  have hnn : n * n = 1 := by
    have h' := ht2
    rw [htn, mul_self_of_comm (hcent u hu n hnX), hu2 u hu, one_mul] at h'
    exact h'
  set s8 : alternatingGroup (Fin 8) := e.symm ⟨n, hnA⟩ with hs8def
  have hs8 : ((e s8 : ↥(derivedOf (Gxy b c))) : G) = n := by
    rw [hs8def, MulEquiv.apply_symm_apply]
  have hs2 : s8 ^ 2 = 1 := by
    have hnn' : (⟨n, hnA⟩ : ↥(derivedOf (Gxy b c))) * ⟨n, hnA⟩ = 1 :=
      Subtype.ext hnn
    rw [pow_two, hs8def, ← map_mul, hnn', map_one]
  have hs1 : s8 ≠ 1 := by
    intro h1
    apply hn1
    have h2 : (⟨n, hnA⟩ : ↥(derivedOf (Gxy b c))) = 1 := by
      rw [← map_one e, ← h1, hs8def, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hfix' : ∀ g ∈ derivedOf (Gxy b c),
      g * ((e s8 : ↥(derivedOf (Gxy b c))) : G) =
        ((e s8 : ↥(derivedOf (Gxy b c))) : G) * g → η g = g := by
    intro g hg hcomm
    have hcomm' : g * n = n * g := by rwa [hs8] at hcomm
    refine hfix g (mem_Gxyz.mpr ⟨?_, ?_, ?_⟩)
    · exact (mem_Gxy.mp (derivedOf_le _ hg)).1
    · exact (mem_Gxy.mp (derivedOf_le _ hg)).2
    · refine mem_Gx.mpr ?_
      have hgX : g ∈ Gxy b c := derivedOf_le _ hg
      rw [htn, mul_assoc, ← hcomm', ← mul_assoc, hcent u hu g hgX, mul_assoc]
  have hcong : ∀ y ∈ Gxy b c, (u * n) * y * (u * n)⁻¹ = n * y * n⁻¹ := by
    intro y hy
    have hcomm_u : u * (n * y * n⁻¹) = (n * y * n⁻¹) * u :=
      hcent u hu (n * y * n⁻¹)
        ((Gxy b c).mul_mem ((Gxy b c).mul_mem hnX hy) ((Gxy b c).inv_mem hnX))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hu2 u hu)]
    rw [show (u * n) * y * (n⁻¹ * u) = u * (n * y * n⁻¹) * u by simp only [mul_assoc]]
    rw [hcomm_u, mul_assoc, hu2 u hu, mul_one]
  rcases aut_eq_id_or_conj_of_fix e hs2 hs1 hη.derived hfix' with hid | hconj
  · left
    intro x hx
    obtain ⟨u', hu', m, hmA, hxm⟩ := hdecomp x hx
    have hu'X : u' ∈ Gxy b c := hmem_u u' hu'
    have hmX : m ∈ Gxy b c := derivedOf_le _ hmA
    rw [hxm, hη.map_mul u' hu'X m hmX, hfix_u u' hu', hid m hmA]
  · right
    rw [hs8] at hconj
    intro x hx
    obtain ⟨u', hu', m, hmA, hxm⟩ := hdecomp x hx
    have hu'X : u' ∈ Gxy b c := hmem_u u' hu'
    have hmX : m ∈ Gxy b c := derivedOf_le _ hmA
    rw [hxm, hη.map_mul u' hu'X m hmX, hfix_u u' hu', hconj m hmA, htn,
      hcong (u' * m) ((Gxy b c).mul_mem hu'X hmX), ← mul_assoc n u' m,
      ← hcent u' hu' n hnX]
    simp only [mul_assoc]

theorem aut_A8_cent_iso (h : F5Std a z) {b c t : G} (hb : IsConj a b) (hc : c ∈ orb2A a b)
    (ht : t ∈ InvIn (Gxy b c)) (htb : t ≠ b) (htc : t ≠ c) (htbc : t ≠ b * c) {K' : Subgroup G'}
    {φ₁ φ₂ : G → G'} (h₁ : IsIsoOn (Gxy b c) K' φ₁) (h₂ : IsIsoOn (Gxy b c) K' φ₂)
    (hS : ∀ x ∈ Gxyz b c t, φ₁ x = φ₂ x) :
    (∀ x ∈ Gxy b c, φ₁ x = φ₂ x) ∨ ∀ x ∈ Gxy b c, φ₁ x = φ₂ (t * x * t⁻¹) :=
  iso_dichotomy_of_aut
    (fun x hx => by
      rw [Gxyz_eq_inf] at hx
      exact (Subgroup.mem_inf.mp hx).1)
    (fun _ hη hfix => aut_A8_cent h hb hc ht htb htc htbc hη hfix) h₁ h₂ hS

end CFSG.EvenSporadicStandard.HNRecog.Section4
