module

public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.LU.Local.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Abstract

variable {Y C : Type} [Group Y] [Group C]

theorem image_isComponent (ρ : Y →* C) (hρ : Function.Surjective ρ) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) (hnt : ∃ a ∈ A, ρ a ≠ 1) : CFSG.IsComponent (A.map ρ) := by
  refine ⟨?_, hA.2.map hρ⟩
  let φ : ↥A →* ↥(A.map ρ) := (ρ.comp A.subtype).codRestrict (A.map ρ) (fun a => ⟨a, a.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨a, ha, ha1⟩ := hnt
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hA.1 hφ ⟨⟨a, ha⟩, ?_⟩
  intro h
  apply ha1
  exact congrArg Subtype.val h

theorem image_comps_two [Finite Y] (ρ : Y →* C) (hρ : Function.Surjective ρ) {A B : Subgroup Y}
    (hA : CFSG.IsComponent A) (hB : CFSG.IsComponent B) (hAB : A ≠ B) (hntA : ∃ a ∈ A, ρ a ≠ 1)
    (hntB : ∃ b ∈ B, ρ b ≠ 1) {L₁ L₂ : Subgroup C}
    (hcomps : {K : Subgroup C | CFSG.IsComponent K} = {L₁, L₂}) :
    (A.map ρ = L₁ ∧ B.map ρ = L₂) ∨ (A.map ρ = L₂ ∧ B.map ρ = L₁) := by
  have hcA := image_isComponent ρ hρ hA hntA
  have hcB := image_isComponent ρ hρ hB hntB
  have hmemA : A.map ρ ∈ ({L₁, L₂} : Set (Subgroup C)) := by rw [← hcomps]; exact hcA
  have hmemB : B.map ρ ∈ ({L₁, L₂} : Set (Subgroup C)) := by rw [← hcomps]; exact hcB
  have hne : A.map ρ ≠ B.map ρ := by
    intro h
    rcases CFSG.LocalCores.distinct_components_commute hA hB with h1 | h1
    · exact hAB h1
    · have h2 : ⁅A.map ρ, B.map ρ⁆ = ⊥ := by rw [← Subgroup.map_commutator, h1, Subgroup.map_bot]
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
      have hcomm : ∀ a b : ↥(A.map ρ), a * b = b * a := by
        intro a b
        have hb : (b : C) ∈ B.map ρ := h ▸ b.2
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle a.2) (b : C) hb).symm
      have : IsMulCommutative ↥(A.map ρ) := ⟨⟨hcomm⟩⟩
      have : Nontrivial ↥(A.map ρ) := CFSG.LocalCores.isQuasisimple_nontrivial hcA.1
      have : Group.IsPerfect ↥(A.map ρ) := hcA.1.1
      exact Group.IsPerfect.not_isMulCommutative ↥(A.map ρ) ‹_›
  rcases hmemA with h | h <;> rcases hmemB with h' | h'
  · exact absurd (h.trans h'.symm) hne
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact absurd (h.trans h'.symm) hne

theorem exists_conj_mem_sylow {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) (N : Subgroup Y)
    [N.Normal] {u : Y} (hu : u ∈ N) (hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1) :
    ∃ c ∈ N, c * u * c⁻¹ ∈ (P : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal P N
  obtain ⟨k, hk⟩ := hu2
  set g : ↥N := ⟨u, hu⟩ with hg
  have hgk : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hpg : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hgk)
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥N Q P'
  refine ⟨c, c.2, ?_⟩
  have hmem : ∀ x : ↥N, x ∈ (P' : Subgroup ↥N) ↔ c⁻¹ * x * c ∈ (Q : Subgroup ↥N) := by
    intro x
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hgQ : g ∈ (Q : Subgroup ↥N) := hQ (Subgroup.mem_zpowers g)
  have h1 : c * g * c⁻¹ ∈ (P' : Subgroup ↥N) := by
    rw [hmem]
    have : c⁻¹ * (c * g * c⁻¹) * c = g := by group
    rw [this]; exact hgQ
  rw [hP'] at h1
  exact Subgroup.mem_subgroupOf.1 h1

end Abstract

section Comps

variable {X : Type} [Group X]

theorem isCompIn_map_subtype (J : Subgroup X) {A K : Subgroup ↥J}
    (h : CFSG.GH74.GLS.IsCompIn A K) :
    CFSG.GH74.GLS.IsCompIn (A.map J.subtype) (K.map J.subtype) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let e : ↥A ≃* ↥(A.map J.subtype) := A.equivMapOfInjective J.subtype J.subtype_injective
  have hmap : (K.subgroupOf A).map e.toMonoidHom =
      (K.map J.subtype).subgroupOf (A.map J.subtype) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : ↥J), hx, rfl⟩
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_subgroupOf.1 hy
      obtain ⟨a, ha, hay⟩ := y.2
      have hka : k = a := J.subtype_injective (hky.trans hay.symm)
      refine ⟨⟨a, ha⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (hka ▸ hk)
      · apply Subtype.ext
        exact hay
  rw [← hmap]
  exact CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e h.2

theorem isCompIn_Y {J : Subgroup X} [J.Normal] {z' : X} (hzJ : z' ∈ J) {Y : Subgroup X}
    (hY : Subgroup.centralizer ({z'} : Set X) = Y) {K : Subgroup ↥J}
    (h : CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({(⟨z', hzJ⟩ : ↥J)} : Set ↥J)) K) :
    CFSG.GH74.GLS.IsCompIn Y (K.map J.subtype) := by
  have h1 := isCompIn_map_subtype J h
  have hcomm : ∀ a ∈ Subgroup.centralizer ({(⟨z', hzJ⟩ : ↥J)} : Set ↥J),
      (a : X) * z' = z' * (a : X) := by
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 ha)
  have hWY : (Subgroup.centralizer ({(⟨z', hzJ⟩ : ↥J)} : Set ↥J)).map J.subtype ≤ Y := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hY]
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha)
  refine CFSG.GH74.GLS.LU.Local.isCompIn_of_normal h1 hWY ?_
  rintro c hc _ ⟨a, ha, rfl⟩
  rw [← hY] at hc
  have hc' : c * z' = z' * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hc'' : c⁻¹ * z' = z' * c⁻¹ := by
    calc c⁻¹ * z' = c⁻¹ * (z' * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * z') * c⁻¹ := by rw [hc']
      _ = z' * c⁻¹ := by group
  refine ⟨MulAut.conjNormal c a, ?_, by simp⟩
  show MulAut.conjNormal c a ∈ Subgroup.centralizer ({(⟨z', hzJ⟩ : ↥J)} : Set ↥J)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, MulAut.conjNormal_apply]
  have hca : (a : X) * z' = z' * (a : X) := hcomm a ha
  calc c * (a : X) * c⁻¹ * z' = c * (a : X) * (c⁻¹ * z') := by group
    _ = c * (a : X) * (z' * c⁻¹) := by rw [hc'']
    _ = c * ((a : X) * z') * c⁻¹ := by group
    _ = c * (z' * (a : X)) * c⁻¹ := by rw [hca]
    _ = (c * z') * (a : X) * c⁻¹ := by group
    _ = (z' * c) * (a : X) * c⁻¹ := by rw [hc']
    _ = z' * (c * (a : X) * c⁻¹) := by group

end Comps

section YLevel

theorem map_conj_eq_of_sq {C : Type} [Group C] {Q : Subgroup C} {g : C} (hg : g * g = 1)
    (h : ∀ a ∈ Q, g * a * g⁻¹ ∈ Q) : Q.map (MulAut.conj g).toMonoidHom = Q := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact h a ha
  · intro hx
    refine ⟨g * x * g⁻¹, h x hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hinv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg]; group

variable {X C : Type} [Group X] [Finite X] [Group C]

theorem exists_conj_normalizing {J : Subgroup X} [J.Normal] {z' : X} (hzJ : z' ∈ J)
    {Y : Subgroup X} (hY : Subgroup.centralizer ({z'} : Set X) = Y) (ρ : ↥Y →* C)
    (hρ : Function.Surjective ρ) (hρz : ∀ hz : z' ∈ Y, ρ ⟨z', hz⟩ ≠ 1) {L₁ L₂ : Subgroup C}
    (hcomps : {K : Subgroup C | CFSG.IsComponent K} = {L₁, L₂}) {q : ℕ} {E₁ E₂ : Subgroup ↥J}
    (hLU : CFSG.GH74.GLS.LU.Local.LUComps ↥J q ⟨z', hzJ⟩ E₁ E₂) {u : X} (huY : u ∈ Y)
    (hu2 : u * u = 1) (hn₁ : ∀ x ∈ E₁, MulAut.conjNormal u x ∈ E₁)
    (hn₂ : ∀ x ∈ E₂, MulAut.conjNormal u x ∈ E₂) (T : Sylow 2 X) (hTY : (T : Subgroup X) ≤ Y) :
    ∃ y : ↥Y, (y : X) ∈ (T : Subgroup X) ∧ (∃ c : ↥Y, y = c * ⟨u, huY⟩ * c⁻¹) ∧
      compPerm C (ρ y) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z₀ : ↥J := ⟨z', hzJ⟩ with hz₀
  have hz'Y : z' ∈ Y := hY ▸ Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hc₁ := isCompIn_Y hzJ hY hLU.comp₁
  have hc₂ := isCompIn_Y hzJ hY hLU.comp₂
  set K₁ : Subgroup ↥Y := (E₁.map J.subtype).subgroupOf Y with hK₁
  set K₂ : Subgroup ↥Y := (E₂.map J.subtype).subgroupOf Y with hK₂
  have hne : K₁ ≠ K₂ := by
    intro h
    apply hLU.ne
    have h' := Subgroup.subgroupOf_inj.1 h
    rw [inf_eq_left.2 hc₁.1, inf_eq_left.2 hc₂.1] at h'
    exact Subgroup.map_injective J.subtype_injective h'
  have hz₀E : ∀ E : Subgroup ↥J, (Subgroup.center ↥E).map E.subtype = Subgroup.zpowers z₀ →
      z₀ ∈ E := by
    intro E hE
    have : z₀ ∈ (Subgroup.center ↥E).map E.subtype := hE ▸ Subgroup.mem_zpowers z₀
    obtain ⟨w, -, hw⟩ := Subgroup.mem_map.1 this
    exact hw ▸ w.2
  have hnt₁ : ∃ a ∈ K₁, ρ a ≠ 1 :=
    ⟨⟨z', hz'Y⟩, Subgroup.mem_subgroupOf.2 ⟨z₀, hz₀E E₁ hLU.cen₁, rfl⟩, hρz hz'Y⟩
  have hnt₂ : ∃ a ∈ K₂, ρ a ≠ 1 :=
    ⟨⟨z', hz'Y⟩, Subgroup.mem_subgroupOf.2 ⟨z₀, hz₀E E₂ hLU.cen₂, rfl⟩, hρz hz'Y⟩
  have hcomps2 := image_comps_two ρ hρ hc₁.2 hc₂.2 hne hnt₁ hnt₂ hcomps
  set u' : ↥Y := ⟨u, huY⟩ with hu'
  have hu'sq : u' * u' = 1 := Subtype.ext hu2
  have hρsq : ρ u' * ρ u' = 1 := by rw [← map_mul, hu'sq, map_one]
  have hnK : ∀ (E : Subgroup ↥J), (∀ x ∈ E, MulAut.conjNormal u x ∈ E) →
      ∀ a ∈ ((E.map J.subtype).subgroupOf Y).map ρ, ρ u' * a * (ρ u')⁻¹ ∈
        ((E.map J.subtype).subgroupOf Y).map ρ := by
    intro E hE a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    refine Subgroup.mem_map.2 ⟨u' * b * u'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    obtain ⟨w, hw, hwb⟩ := Subgroup.mem_subgroupOf.1 hb
    refine Subgroup.mem_subgroupOf.2 ⟨MulAut.conjNormal u w, hE w hw, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu']
    rw [← hwb]
    simp
  have hfix : compPerm C (ρ u') = 1 := by
    refine Equiv.ext fun ⟨K, hK⟩ => Subtype.ext ?_
    have hKmem : K ∈ ({L₁, L₂} : Set (Subgroup C)) := by rw [← hcomps]; exact hK
    change K.map (MulAut.conj (ρ u')).toMonoidHom = K
    refine map_conj_eq_of_sq hρsq ?_
    rcases hcomps2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hKmem with rfl | rfl
      · rw [← h1]; exact hnK E₁ hn₁
      · rw [← h2]; exact hnK E₂ hn₂
    · rcases hKmem with rfl | rfl
      · rw [← h2]; exact hnK E₂ hn₂
      · rw [← h1]; exact hnK E₁ hn₁
  set D : Subgroup ↥Y := (compPerm C).ker.comap ρ with hD
  have hDn : D.Normal := (MonoidHom.normal_ker (compPerm C)).comap ρ
  have hu'D : u' ∈ D := by
    rw [hD, Subgroup.mem_comap, MonoidHom.mem_ker]; exact hfix
  obtain ⟨c, hcD, hcmem⟩ := exists_conj_mem_sylow (T.subtype hTY) D hu'D
    ⟨1, by rw [pow_one, pow_two]; exact hu'sq⟩
  refine ⟨c * u' * c⁻¹, Subgroup.mem_subgroupOf.1 hcmem, ⟨c, rfl⟩, ?_⟩
  have : c * u' * c⁻¹ ∈ D := D.mul_mem (D.mul_mem hcD hu'D) (D.inv_mem hcD)
  rwa [hD, Subgroup.mem_comap, MonoidHom.mem_ker] at this

end YLevel

end CFSG.GH74.GLS.Stage2.Local.P34
