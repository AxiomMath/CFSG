module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCIrr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma sec9c_key {B M K : Subgroup G} {T : Set G} (hB : IsElemAb2 B 4)
    (hTM : ∀ x ∈ T, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hTK : ∀ x ∈ T, x ∈ K)
    (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B)
    (f : ↥M →* ↥B)
    (heq : ∀ x ∈ T, ∀ (m : ↥M) (hm : x * (m : G) * x⁻¹ ∈ M),
      ((f ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G) = x * ((f m : ↥B) : G) * x⁻¹)
    {m₀ : ↥M} (hm₀ : f m₀ ≠ 1) :
    ∃ c : ↥M, (c : G) ∈ K ∧ f c ≠ 1 := by
  have hb : ((f m₀ : ↥B) : G) ∈ B := (f m₀).2
  have hbne : ((f m₀ : ↥B) : G) ≠ 1 := by
    intro h
    exact hm₀ (Subtype.ext h)
  have hmoved : ∃ x ∈ T, x * ((f m₀ : ↥B) : G) * x⁻¹ ≠ ((f m₀ : ↥B) : G) := by
    by_contra h
    refine hbne (sec9c_fixed_eq_one hB hirr hb ?_)
    intro x hxT
    by_contra hxne
    exact h ⟨x, hxT, hxne⟩
  obtain ⟨x, hxT, hxne⟩ := hmoved
  let m₁ : ↥M := ⟨x * (m₀ : G)⁻¹ * x⁻¹,
    hTM x hxT ((m₀ : G)⁻¹) (M.inv_mem m₀.2)⟩
  let c : ↥M := m₀ * m₁
  have hcK : (c : G) ∈ K := by
    have h1 : (m₀ : G) * x * (m₀ : G)⁻¹ ∈ K := hMK (m₀ : G) m₀.2 x (hTK x hxT)
    have h2 : x⁻¹ ∈ K := K.inv_mem (hTK x hxT)
    have h3 : ((m₀ : G) * x * (m₀ : G)⁻¹) * x⁻¹ ∈ K := K.mul_mem h1 h2
    convert h3 using 1
    change (m₀ : G) * (x * (m₀ : G)⁻¹ * x⁻¹) = (m₀ : G) * x * (m₀ : G)⁻¹ * x⁻¹
    group
  have hfm₁ : ((f m₁ : ↥B) : G) = x * ((f m₀ : ↥B) : G)⁻¹ * x⁻¹ := by
    have harg : (⟨x * ((m₀⁻¹ : ↥M) : G) * x⁻¹,
        hTM x hxT ((m₀ : G)⁻¹) (M.inv_mem m₀.2)⟩ : ↥M) = m₁ := Subtype.ext rfl
    have h := heq x hxT (m₀⁻¹ : ↥M)
      (hTM x hxT ((m₀ : G)⁻¹) (M.inv_mem m₀.2))
    rw [harg] at h
    have hinv : ((f (m₀⁻¹) : ↥B) : G) = ((f m₀ : ↥B) : G)⁻¹ := by
      rw [map_inv]
      rfl
    rw [h, hinv]
  have hfc : f c ≠ 1 := by
    intro h1
    have h1G : ((f c : ↥B) : G) = 1 := by rw [h1]; rfl
    have hc : (f c : ↥B) = f m₀ * f m₁ := by
      change f (m₀ * m₁) = f m₀ * f m₁
      rw [map_mul]
    have hprod : ((f m₀ : ↥B) : G) * ((f m₁ : ↥B) : G) = 1 := by
      have hh := congrArg Subtype.val hc
      rw [h1G] at hh
      exact hh.symm
    rw [hfm₁] at hprod
    have hy : x * ((f m₀ : ↥B) : G)⁻¹ * x⁻¹ = ((f m₀ : ↥B) : G)⁻¹ :=
      mul_left_cancel (hprod.trans (mul_inv_cancel ((f m₀ : ↥B) : G)).symm)
    have hconj : x * ((f m₀ : ↥B) : G) * x⁻¹ = ((f m₀ : ↥B) : G) := by
      have := congrArg (fun z : G => z⁻¹) hy
      simp only [mul_inv_rev, inv_inv] at this
      simpa only [mul_assoc] using this
    exact hxne hconj
  exact ⟨c, hcK, hfc⟩

theorem sec9c_core {B M K : Subgroup G} {T : Set G} (hB : IsElemAb2 B 4) (hBM : B ≤ M)
    (hTB : ∀ x ∈ T, x ∈ normalizer (B : Set G))
    (hTM : ∀ x ∈ T, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hTK : ∀ x ∈ T, x ∈ K)
    (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B)
    (f₁ f₂ : ↥M →* ↥B) (hker : ∀ b : ↥M, (b : G) ∈ B → f₁ b = 1 ∧ f₂ b = 1)
    (hequiv : ∀ x ∈ T, ∀ (m : ↥M) (hm : x * (m : G) * x⁻¹ ∈ M),
      ((f₁ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G) = x * ((f₁ m : ↥B) : G) * x⁻¹ ∧
        ((f₂ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G) = x * ((f₂ m : ↥B) : G) * x⁻¹)
    (hne : ∃ m : ↥M, f₁ m ≠ 1 ∨ f₂ m ≠ 1) :
    2 ^ 8 ∣ Nat.card ↥(M ⊓ K) := by
  have hBK : B ≤ K := sec9c_B_le_K hB hBM hTB hTK hMK hirr
  have hBMK : B ≤ M ⊓ K := le_inf hBM hBK
  let φ : ↥(M ⊓ K) →* ↥B × ↥B :=
    (f₁.prod f₂).comp (Subgroup.inclusion inf_le_left)
  let V : Subgroup (↥B × ↥B) := φ.range
  obtain ⟨m₀, hm₀⟩ := hne
  have hV : V ≠ ⊥ := by
    obtain ⟨c, hcK, hfc⟩ : ∃ c : ↥M, (c : G) ∈ K ∧ (f₁ c ≠ 1 ∨ f₂ c ≠ 1) := by
      rcases hm₀ with h | h
      · obtain ⟨c, hcK, hfc⟩ :=
          sec9c_key hB hTM hTK hMK hirr f₁
            (fun x hx m hm => (hequiv x hx m hm).1) h
        exact ⟨c, hcK, Or.inl hfc⟩
      · obtain ⟨c, hcK, hfc⟩ :=
          sec9c_key hB hTM hTK hMK hirr f₂
            (fun x hx m hm => (hequiv x hx m hm).2) h
        exact ⟨c, hcK, Or.inr hfc⟩
    let c' : ↥(M ⊓ K) := ⟨c, c.2, hcK⟩
    have hφc : φ c' ≠ 1 := by
      intro h
      have hc1 : (φ c').1 = 1 := by rw [h]; rfl
      have hc2 : (φ c').2 = 1 := by rw [h]; rfl
      have hincl : Subgroup.inclusion inf_le_left c' = c := Subtype.ext rfl
      rcases hfc with h1 | h2
      · refine h1 ?_
        have hcoord : (φ c').1 = f₁ c := by
          change f₁ (Subgroup.inclusion inf_le_left c') = f₁ c
          rw [hincl]
        rw [hcoord] at hc1
        exact hc1
      · refine h2 ?_
        have hcoord : (φ c').2 = f₂ c := by
          change f₂ (Subgroup.inclusion inf_le_left c') = f₂ c
          rw [hincl]
        rw [hcoord] at hc2
        exact hc2
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨φ c', (MonoidHom.mem_range).mpr ⟨c', rfl⟩⟩, ?_⟩
    intro h
    exact hφc (congrArg Subtype.val h)
  have hinv : ∀ x ∈ T, ∀ w ∈ V, ∃ w' ∈ V,
      ((w'.1 : ↥B) : G) = x * ((w.1 : ↥B) : G) * x⁻¹ ∧
        ((w'.2 : ↥B) : G) = x * ((w.2 : ↥B) : G) * x⁻¹ := by
    intro x hxT w hw
    rw [MonoidHom.mem_range] at hw
    obtain ⟨c, rfl⟩ := hw
    let c' : ↥(M ⊓ K) := ⟨x * (c : G) * x⁻¹, hTM x hxT (c : G) c.2.1,
      K.mul_mem (K.mul_mem (hTK x hxT) c.2.2) (K.inv_mem (hTK x hxT))⟩
    refine ⟨φ c', (MonoidHom.mem_range).mpr ⟨c', rfl⟩, ?_, ?_⟩
    · change ((f₁ (Subgroup.inclusion inf_le_left c') : ↥B) : G)
        = x * ((f₁ (Subgroup.inclusion inf_le_left c) : ↥B) : G) * x⁻¹
      exact (hequiv x hxT (Subgroup.inclusion inf_le_left c) (c'.2.1)).1
    · change ((f₂ (Subgroup.inclusion inf_le_left c') : ↥B) : G)
        = x * ((f₂ (Subgroup.inclusion inf_le_left c) : ↥B) : G) * x⁻¹
      exact (hequiv x hxT (Subgroup.inclusion inf_le_left c) (c'.2.1)).2
  have h16V : 16 ∣ Nat.card V := sec9c_card_dvd hB hirr V hV hinv
  have hker_le : B.subgroupOf (M ⊓ K) ≤ φ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    have hbM : ((Subgroup.inclusion inf_le_left b : ↥M) : G) ∈ B := by
      rw [Subgroup.coe_inclusion]; exact hb
    have hkb := hker (Subgroup.inclusion inf_le_left b) hbM
    exact Prod.ext hkb.1 hkb.2
  have hcardB : Nat.card (B.subgroupOf (M ⊓ K)) = 16 := by
    have e := (Subgroup.subgroupOfEquivOfLe hBMK).toEquiv
    rw [Nat.card_congr e, hB.2]
    norm_num
  have h16ker : 16 ∣ Nat.card φ.ker := by
    rw [← hcardB]
    exact Subgroup.card_dvd_of_le hker_le
  have hcard : Nat.card ↥(M ⊓ K) = Nat.card V * Nat.card φ.ker := by
    rw [← card_ker_mul_card_range φ]
    exact Nat.mul_comm _ _
  rw [hcard]
  have hpow : 2 ^ 8 = 16 * 16 := by norm_num
  rw [hpow]
  exact Nat.mul_dvd_mul h16V h16ker

end CFSG.OddStandard.SmallF3.Omega
