module

public import CFSG.CGT.Timmesfeld75.Sec5Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def secA (T T₁ : Subgroup G) : Subgroup G :=
  ⨅ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g (normIn T T₁)

@[expose] def normD (T : Subgroup G) : Set G :=
  classD T ∩ (Subgroup.normalizer (T : Set G) : Set G)

theorem mem_secA {x : G} :
    x ∈ secA T T₁ ↔ ∀ g ∈ Subgroup.normalizer (T : Set G), x ∈ conjSubgroup g (normIn T T₁) := by
  simp only [secA, Subgroup.mem_iInf]

theorem secA_le_normIn : secA T T₁ ≤ normIn T T₁ := fun x hx => by
  have := mem_secA.1 hx 1 (Subgroup.one_mem _)
  rwa [conjSubgroup_one] at this

theorem secA_le_left : secA T T₁ ≤ T := secA_le_normIn.trans (normIn_le _ _)

theorem conjSubgroup_secA {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup h (secA T T₁) = secA T T₁ := by
  have key : ∀ h ∈ Subgroup.normalizer (T : Set G), ∀ x : G,
      x ∈ conjSubgroup h (secA T T₁) → x ∈ secA T T₁ := by
    intro h hh x hx
    rw [mem_conjSubgroup, mem_secA] at hx
    rw [mem_secA]
    intro g hg
    have h1 := hx (h⁻¹ * g) ((Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).inv_mem hh) hg)
    rw [mem_conjSubgroup] at h1 ⊢
    simpa [mul_assoc] using h1
  ext x
  constructor
  · exact key h hh x
  · intro hx
    have h1 := key h⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hh) (h⁻¹ * x * h) (by
      rw [mem_conjSubgroup]
      have e : h⁻¹⁻¹ * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [e]
      exact hx)
    rw [mem_conjSubgroup]
    exact h1

theorem normIn_ne_bot_of_conj [Finite G] (hT : IsWC T) {g : G} (hne : conjSubgroup g T ≠ T)
    (h : normIn (conjSubgroup g T) T ≠ ⊥) : normIn T (conjSubgroup g T) ≠ ⊥ := by
  have hwc : IsWC (conjSubgroup g T) := hT.conj g
  have hT' : conjSubgroup g⁻¹ (conjSubgroup g T) = T := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hne' : conjSubgroup g⁻¹ (conjSubgroup g T) ≠ conjSubgroup g T := by
    rw [hT']; exact fun h' => hne h'.symm
  have h' : normIn (conjSubgroup g T) (conjSubgroup g⁻¹ (conjSubgroup g T)) ≠ ⊥ := by
    rwa [hT']
  have c := Cfg.of_conj hwc hne' h'
  rw [hT'] at c
  exact c.symm.ne

section Five

variable [Finite G]

omit [Finite G] in
theorem not_mem_cfgM_of_not_mem_conj (hP : MaxPair T T₁) (hS : Sec3Global T) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {x : G} (hx : x ∈ T)
    (hxg : x ∉ conjSubgroup g (normIn T T₁)) : x ∉ cfgM T (conjSubgroup g T₁) := by
  intro hM
  have hs := hP.sec3_conj hS hg
  have h1 : x ∈ T ⊓ cfgM T (conjSubgroup g T₁) := ⟨hx, hM⟩
  rw [hs.cfg.inf_cfgM, normIn_conjSubgroup_of_mem_normalizer hg] at h1
  exact hxg h1

theorem exists_normalizer_conj_of_not_mem_conj (hP : MaxPair T T₁) (hS : Sec3Global T) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {x y : G} (hx : x ∈ T)
    (hxg : x ∉ conjSubgroup g (normIn T T₁)) (hy : y ∈ T)
    (hyg : y ∉ conjSubgroup g (normIn T T₁)) :
    ∃ z ∈ Subgroup.normalizer (T : Set G), z * x * z⁻¹ = y := by
  obtain ⟨z, -, hz, hzxy⟩ := (hP.sec3_conj hS hg).exists_mem_normalizer_conj hx
    (not_mem_cfgM_of_not_mem_conj hP hS hg hx hxg) hy (not_mem_cfgM_of_not_mem_conj hP hS hg hy hyg)
  exact ⟨z, hz, hzxy⟩

theorem secA_transitive (hP : MaxPair T T₁) (hS : Sec3Global T) {x y : G} (hx : x ∈ T)
    (hxA : x ∉ secA T T₁) (hy : y ∈ T) (hyA : y ∉ secA T T₁) :
    ∃ z ∈ Subgroup.normalizer (T : Set G), z * x * z⁻¹ = y := by
  have trans : ∀ {a b c : G}, (∃ z ∈ Subgroup.normalizer (T : Set G), z * a * z⁻¹ = b) →
      (∃ z ∈ Subgroup.normalizer (T : Set G), z * b * z⁻¹ = c) →
      ∃ z ∈ Subgroup.normalizer (T : Set G), z * a * z⁻¹ = c := by
    rintro a b c ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₂ * z₁, (Subgroup.normalizer (T : Set G)).mul_mem hz₂ hz₁, by group⟩
  have symm : ∀ {a b : G}, (∃ z ∈ Subgroup.normalizer (T : Set G), z * a * z⁻¹ = b) →
      ∃ z ∈ Subgroup.normalizer (T : Set G), z * b * z⁻¹ = a := by
    rintro a b ⟨z, hz, rfl⟩
    exact ⟨z⁻¹, (Subgroup.normalizer (T : Set G)).inv_mem hz, by group⟩
  obtain ⟨h, hh, hxh⟩ : ∃ h ∈ Subgroup.normalizer (T : Set G),
      x ∉ conjSubgroup h (normIn T T₁) := by
    by_contra hcon
    push Not at hcon
    exact hxA (mem_secA.2 hcon)
  obtain ⟨g, hg, hyg⟩ : ∃ g ∈ Subgroup.normalizer (T : Set G),
      y ∉ conjSubgroup g (normIn T T₁) := by
    by_contra hcon
    push Not at hcon
    exact hyA (mem_secA.2 hcon)
  have hxyT : x * y ∈ T := T.mul_mem hx hy
  by_cases hyh : y ∈ conjSubgroup h (normIn T T₁)
  ·
    have hxy : x * y ∉ conjSubgroup h (normIn T T₁) := by
      intro hxy
      apply hxh
      have := (conjSubgroup h (normIn T T₁)).mul_mem hxy
        ((conjSubgroup h (normIn T T₁)).inv_mem hyh)
      simpa using this
    have h1 := exists_normalizer_conj_of_not_mem_conj hP hS hh hx hxh hxyT hxy
    by_cases hxg : x ∈ conjSubgroup g (normIn T T₁)
    · have hyx : y * x ∉ conjSubgroup g (normIn T T₁) := by
        intro hyx
        apply hyg
        have := (conjSubgroup g (normIn T T₁)).mul_mem hyx
          ((conjSubgroup g (normIn T T₁)).inv_mem hxg)
        simpa using this
      have h2 := exists_normalizer_conj_of_not_mem_conj hP hS hg hy hyg (T.mul_mem hy hx) hyx
      have hcomm : y * x = x * y := (elemAbelian_mul_comm (hP.wc.1) hy hx)
      rw [hcomm] at h2
      exact trans h1 (symm h2)
    · exact exists_normalizer_conj_of_not_mem_conj hP hS hg hx hxg hy hyg
  · exact exists_normalizer_conj_of_not_mem_conj hP hS hh hx hxh hy hyh

omit [Finite G] in
theorem inf_centralizer_normD_le_secA (hP : MaxPair T T₁) (hS : Sec3Global T) :
    T ⊓ Subgroup.centralizer (normD T) ≤ secA T T₁ := by
  rintro x ⟨hxT, hxC⟩
  rw [mem_secA]
  intro g hg
  have hs := hP.sec3_conj hS hg
  have hc := hs.cfg.inf_centralizer_normIn
  rw [normIn_conjSubgroup_of_mem_normalizer hg T₁] at hc
  rw [← hc]
  refine ⟨hxT, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
  by_cases hb1 : b = 1
  · subst hb1
    simp
  · obtain ⟨hbT₁, hbN⟩ := mem_normIn.1 hb
    obtain ⟨x₀, hx₀⟩ := hP.conj
    have hbc : b ∈ conjSubgroup (g * x₀) T := by
      rw [← conjSubgroup_conjSubgroup, ← hx₀]
      exact hbT₁
    have hbD : b ∈ normD T := by
      refine ⟨⟨(g * x₀)⁻¹, (g * x₀)⁻¹ * b * (g * x₀)⁻¹⁻¹, ?_, ?_, ?_⟩, hbN⟩
      · simpa [mem_conjSubgroup] using hbc
      · intro h1
        apply hb1
        have : b = (g * x₀) * ((g * x₀)⁻¹ * b * (g * x₀)⁻¹⁻¹) * (g * x₀)⁻¹ := by group
        rw [this, h1]
        group
      · group
    exact Subgroup.mem_centralizer_iff.1 hxC b hbD

theorem secA_le_centralizer_normD (hP : MaxPair T T₁) (hS : Sec3Global T) :
    secA T T₁ ≤ Subgroup.centralizer (normD T) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
  obtain ⟨⟨k, t, htT, ht1, hak⟩, haN⟩ := ha
  have hxT : x ∈ T := secA_le_left hx
  by_cases haT : a ∈ T
  · exact elemAbelian_mul_comm hP.wc.1 haT hxT
  ·
    set T' := conjSubgroup k⁻¹ T with hT'
    have haT' : a ∈ T' := by
      rw [hT', mem_conjSubgroup, inv_inv, hak]
      have e : k * (k⁻¹ * t * k) * k⁻¹ = t := by group
      rw [e]
      exact htT
    have hne : T' ≠ T := fun h => haT (h ▸ haT')
    have ha1 : a ≠ 1 := fun h => haT (h ▸ T.one_mem)
    have hnT' : normIn T' T ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨a, mem_normIn.2 ⟨haT', haN⟩⟩, fun h => ?_⟩
      exact ha1 (congrArg Subtype.val h)
    have hnT : normIn T T' ≠ ⊥ := by
      have hT'' : conjSubgroup k⁻¹ T = T' := rfl
      exact normIn_ne_bot_of_conj hP.wc hne hnT'
    have hs : Sec3 T T' := hS k⁻¹ hne hnT
    have haM : a ∈ cfgM T T' := Cfg.normIn_le_cfgM_right T T' (mem_normIn.2 ⟨haT', haN⟩)
    have hxM : x ∈ cfgM T T' := by
      by_contra hxM
      have hsub : ∀ y ∈ T, y ∉ cfgM T T' → y ∈ secA T T₁ := by
        intro y hy hyM
        obtain ⟨z, -, hz, hzxy⟩ := hs.exists_mem_normalizer_conj hxT hxM hy hyM
        have : z * x * z⁻¹ ∈ conjSubgroup z (secA T T₁) := ⟨x, hx, rfl⟩
        rw [conjSubgroup_secA hz, hzxy] at this
        exact this
      obtain ⟨v, hvT, hvM⟩ := IsConcreteLE.not_le_iff_exists.1 hs.not_le_cfgM
      have hTA : T ≤ secA T T₁ := by
        intro u hu
        by_cases huM : u ∈ cfgM T T'
        · have huv : u * v ∉ cfgM T T' := fun h =>
            hvM (by simpa using (cfgM T T').mul_mem ((cfgM T T').inv_mem huM) h)
          have := (secA T T₁).mul_mem (hsub _ (T.mul_mem hu hvT) huv)
            ((secA T T₁).inv_mem (hsub v hvT hvM))
          simpa using this
        · exact hsub u hu huM
      have hs₁ := hP.sec3_conj hS (Subgroup.one_mem (Subgroup.normalizer (T : Set G)))
      rw [conjSubgroup_one] at hs₁
      exact hs₁.not_le_cfgM
        (hTA.trans (secA_le_normIn.trans (Cfg.normIn_le_cfgM_left T T₁)))
    exact elemAbelian_mul_comm hs.cfg.isElemAbelian_cfgM haM hxM

theorem secA_eq_centralizer_normD (hP : MaxPair T T₁) (hS : Sec3Global T) :
    secA T T₁ = T ⊓ Subgroup.centralizer (normD T) :=
  le_antisymm (le_inf secA_le_left (secA_le_centralizer_normD hP hS))
    (inf_centralizer_normD_le_secA hP hS)

end Five

end CFSG.CGT.Timmesfeld75
