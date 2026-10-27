module

public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

omit [Group G] in
theorem conjSubgroup_secA_eq_of_conjSubgroup_eq {G : Type} [Group G] {T T₁ : Subgroup G}
    {x₀ y₀ : G} (h : conjSubgroup x₀ T = conjSubgroup y₀ T) :
    conjSubgroup x₀ (secA T T₁) = conjSubgroup y₀ (secA T T₁) := by
  have hn : x₀⁻¹ * y₀ ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    calc conjSubgroup (x₀⁻¹ * y₀) T = conjSubgroup x₀⁻¹ (conjSubgroup y₀ T) := by
          rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup x₀⁻¹ (conjSubgroup x₀ T) := by rw [h]
      _ = T := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  calc conjSubgroup x₀ (secA T T₁) =
        conjSubgroup y₀ (conjSubgroup (y₀⁻¹ * x₀) (secA T T₁)) := by
        rw [conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup y₀ (secA T T₁) := by
        rw [conjSubgroup_secA (by simpa using (Subgroup.normalizer (T : Set G)).inv_mem hn)]

section Five

variable [Finite G]

theorem commutator_conj_secA_le_secA_of_mem_secR₁ (h1 : Sec4NoA) (h3 : Sec4Nine)
    (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hA4 : secA T T₁ ≠ normIn T T₁) {x₀ : G} (hx₀ : T₁ = conjSubgroup x₀ T) {x : G}
    (hx : x ∈ secR₁ T T₁) (hxx : x * x = 1) (hxD : x ∈ classD T) :
    ∀ a ∈ conjSubgroup x₀ (secA T T₁), ⁅a, x⁆ ∈ secA T T₁ := by
  have hP := hy.pair
  have hsec3 : Sec3 T T₁ := hP.sec3 hS
  have hcfg := hsec3.cfg
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := secR₁_le_normalizer hP hS hx
  have hx₀u : IsUIdx T T₁ x₀ := isUIdx_of_conj hP hS hx₀
  have hx₀ne : conjSubgroup x₀ T ≠ T := by rw [← hx₀]; exact hP.ne
  have hA₁L : conjSubgroup x₀ (secA T T₁) ≤ normIn T₁ T := by
    have := conjSubgroup_secA_le_normIn hP hS hx₀ne (by rw [← hx₀]; exact hcfg.ne₁)
    rwa [← hx₀] at this
  have hA₁R : conjSubgroup x₀ (secA T T₁) ≤ secR₁ T T₁ := by
    unfold secR₁
    exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) x₀ hx₀u
  have hE4 : ∀ a ∈ conjSubgroup x₀ (secA T T₁), ⁅a, x⁆ ∈ T := fun a ha =>
    commutator_secR₁_mem h1 h3 hy hS hI hA4 a (hA₁R ha) x hx
  by_cases hne : ∃ a ∈ conjSubgroup x₀ (secA T T₁), ⁅a, x⁆ ≠ 1
  swap
  · push Not at hne
    intro a ha
    rw [hne a ha]
    exact (secA T T₁).one_mem
  obtain ⟨t, htT, hxt⟩ := engine hy hS hI hA4 hx₀ hxN hxx hxD
    (conj_normIn_le_of_mem_secR₁ h1 h3 hy hS hI hA4 hx) hE4 hne
  have hu : ∀ y ∈ T ⊔ T₁, (x * t) * y * (x * t)⁻¹ ∈ T ⊔ T₁ := by
    intro y hy'
    have hM : y⁻¹ * ((x * t) * y * (x * t)⁻¹) ∈ T ⊔ T₁ := cfgM_le_sup T T₁ (hxt y hy')
    have := (T ⊔ T₁).mul_mem hy' hM
    rwa [mul_inv_cancel_left] at this
  have hxX : ∀ y ∈ T ⊔ T₁, x * y * x⁻¹ ∈ T ⊔ T₁ := by
    intro y hy'
    have htX : t ∈ T ⊔ T₁ := Subgroup.mem_sup_left htT
    have h2 : t⁻¹ * y * t ∈ T ⊔ T₁ :=
      (T ⊔ T₁).mul_mem ((T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem htX) hy') htX
    have h4 := hu _ h2
    have e : (x * t) * (t⁻¹ * y * t) * (x * t)⁻¹ = x * y * x⁻¹ := by group
    rwa [e] at h4
  have hIso : Sec3Iso T T₁ := by
    rw [hx₀]
    exact hI x₀ (by rw [← hx₀]; exact hP.ne) (by rw [← hx₀]; exact hcfg.ne)
  obtain ⟨hN, f, hf, hiso⟩ := hIso
  have := hN
  have hW := hsec3.conjSubgroup_sup_conj_eq hf hiso hx₀.symm secA_le_normIn
    (fun n hn => mem_normalizer_of_conjSubgroup_eq (conjSubgroup_secA hn))
  obtain ⟨y₀, hy₀X, hy₀⟩ := hsec3.conj
  have hA₁eq : conjSubgroup x₀ (secA T T₁) = conjSubgroup y₀ (secA T T₁) :=
    conjSubgroup_secA_eq_of_conjSubgroup_eq (by rw [← hx₀, hy₀])
  have hAW : secA T T₁ ≤ secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁) := le_sup_left
  have hA₁W : conjSubgroup x₀ (secA T T₁) ≤ secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁) :=
    le_sup_right
  have hxA₁ : ∀ a₁ ∈ conjSubgroup x₀ (secA T T₁),
      x * a₁ * x⁻¹ ∈ secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁) := by
    intro a₁ ha₁
    rw [hA₁eq] at ha₁
    have ha₁' : y₀⁻¹ * a₁ * y₀ ∈ secA T T₁ := mem_conjSubgroup.1 ha₁
    have hy₁ : x * y₀ * x⁻¹ ∈ T ⊔ T₁ := hxX y₀ hy₀X
    have ha' : x * (y₀⁻¹ * a₁ * y₀) * x⁻¹ ∈ secA T T₁ := by
      have := conj_mem_conjSubgroup x ha₁'
      rwa [conjSubgroup_secA hxN] at this
    have h4 := conj_mem_conjSubgroup (x * y₀ * x⁻¹) (hAW ha')
    rw [hW _ hy₁] at h4
    have e : (x * y₀ * x⁻¹) * (x * (y₀⁻¹ * a₁ * y₀) * x⁻¹) * (x * y₀ * x⁻¹)⁻¹ =
        x * a₁ * x⁻¹ := by group
    rwa [e] at h4
  intro a₁ ha₁
  have hc1 : ⁅a₁, x⁆ ∈ secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁) := by
    have h5 := (secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁)).mul_mem (hA₁W ha₁)
      ((secA T T₁ ⊔ conjSubgroup x₀ (secA T T₁)).inv_mem (hxA₁ a₁ ha₁))
    have e : a₁ * (x * a₁ * x⁻¹)⁻¹ = ⁅a₁, x⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h5
  have hc2 : ⁅a₁, x⁆ ∈ T := hE4 a₁ ha₁
  have hMab := hcfg.isElemAbelian_cfgM
  have hAM : secA T T₁ ≤ cfgM T T₁ := secA_le_normIn.trans (Cfg.normIn_le_cfgM_left T T₁)
  have hA₁M : conjSubgroup x₀ (secA T T₁) ≤ cfgM T T₁ :=
    hA₁L.trans (Cfg.normIn_le_cfgM_right T T₁)
  have hAn : secA T T₁ ≤ Subgroup.normalizer (conjSubgroup x₀ (secA T T₁) : Set G) :=
    le_normalizer_of_le_elemAbelian hMab hAM hA₁M
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (secA T T₁)
    (conjSubgroup x₀ (secA T T₁)) hAn
  have hc3 : ⁅a₁, x⁆ ∈ ((secA T T₁ : Set G) * (conjSubgroup x₀ (secA T T₁) : Set G)) := by
    rw [← hmul]
    exact hc1
  obtain ⟨a, ha, a', ha', hcaa⟩ := hc3
  have hcaa' : a * a' = ⁅a₁, x⁆ := hcaa
  have ha'T : a' ∈ T := by
    have : a' = a⁻¹ * ⁅a₁, x⁆ := by rw [← hcaa']; group
    rw [this]
    exact T.mul_mem (T.inv_mem (secA_le_left ha)) hc2
  have ha'T₁ : a' ∈ T₁ := normIn_le _ _ (hA₁L ha')
  have ha'1 : a' = 1 := by
    have h6 : a' ∈ T ⊓ T₁ := ⟨ha'T, ha'T₁⟩
    rwa [hcfg.inf, Subgroup.mem_bot] at h6
  rw [← hcaa', ha'1, mul_one]
  exact ha

theorem commutator_conj_secA_conj_secA_le (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) {g h : G}
    (hg : IsUIdx T T₁ g) (hh : IsUIdx T T₁ h) :
    ∀ a ∈ conjSubgroup h (secA T T₁), ∀ x ∈ conjSubgroup g (secA T T₁), ⁅a, x⁆ ∈ secA T T₁ := by
  intro a ha x hx
  have hP := hy.pair
  have : IsSimpleGroup G := hy.simple
  by_cases hx1 : x = 1
  · rw [hx1]
    simp [(secA T T₁).one_mem]
  have hy' : StepHyp T (conjSubgroup h T) := hh.stepHyp hy hS
  have hA4' : secA T (conjSubgroup h T) ≠ normIn T (conjSubgroup h T) :=
    secA_ne_normIn hTO hBW hy.nonab hy'.pair hS
  have hxR : x ∈ secR₁ T (conjSubgroup h T) := by
    rw [secR₁_eq_of_isUIdx hP hS hh]
    unfold secR₁
    exact (le_iSup₂ (f := fun (k : G) (_ : IsUIdx T T₁ k) => conjSubgroup k (secA T T₁)) g hg) hx
  have hxT : x ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left hx
  have hxx : x * x = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hP.wc.1 g) hxT
  have hxD : x ∈ classD T := mem_classD_of_mem_conjSubgroup hxT hx1
  have := commutator_conj_secA_le_secA_of_mem_secR₁ h1 h3 hy' hS hI hA4' (x₀ := h) rfl hxR hxx
    hxD a (by rw [secA_eq_of_isUIdx hP hS hh]; exact ha)
  rwa [secA_eq_of_isUIdx hP hS hh] at this

theorem commutator_secR₁_mem_secA (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) :
    ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁ := by
  rw [secR₁_eq_iSup_subtype]
  refine commutator_mem_of_forall_gen (T := secA T T₁) (fun i => ?_) (fun i j => ?_)
  · intro z hz
    exact mem_normalizer_of_conjSubgroup_eq
      (conjSubgroup_secA (i.2.conj_secA_le_normalizer hy.pair hS hz))
  · exact commutator_conj_secA_conj_secA_le h1 h3 hy hS hI hTO hBW j.2 i.2

theorem sec55 (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) :
    secR₁ T T₁ ≤ Subgroup.normalizer (T : Set G) ∧
      (∀ n ∈ Subgroup.normalizer (T : Set G), conjSubgroup n (secR₁ T T₁) = secR₁ T T₁) ∧
      IsPGroup 2 ↥(secR₁ T T₁) ∧ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁ := by
  have : IsSimpleGroup G := hy.simple
  have hA4 : secA T T₁ ≠ normIn T T₁ := secA_ne_normIn hTO hBW hy.nonab hy.pair hS
  exact ⟨secR₁_le_normalizer hy.pair hS, fun n hn => conjSubgroup_secR₁ hn,
    isPGroup_secR₁ h1 h3 hy hS hI hA4, commutator_secR₁_mem_secA h1 h3 hy hS hI hTO hBW⟩

end Five

end CFSG.CGT.Timmesfeld75
