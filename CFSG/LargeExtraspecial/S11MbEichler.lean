module

public import CFSG.LargeExtraspecial.OrthoF2Radical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_zero_right)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem polar_sub_self_eq {l : V ≃ₗ[ZMod 2] V} (hl : l ∈ orthogonalGroup q) (x : V) :
    polar q (l x - x) x = q (l x - x) := by
  have hiso : q (l x) = q x := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hl x
  have h1 : polar q (l x - x) x = -q (l x - x) := by
    rw [polar, sub_add_cancel, hiso]
    ring
  rw [h1, zmod2_neg]

theorem polar_sub_comm {l : V ≃ₗ[ZMod 2] V} (hl : l ∈ orthogonalGroup q) (hll : l * l = 1)
    (x y : V) : polar q (l x - x) y = polar q (l y - y) x := by
  have h1 : polar q (l x) y = polar q x (l y) := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hl x (l y)
    rwa [← LinearEquiv.mul_apply, hll, LinearEquiv.coe_one, id] at this
  rw [polar_sub_left, polar_sub_left, h1, polar_comm q x (l y), polar_comm q x y]

theorem polar_sub_eq_zero_of_le {l : V ≃ₗ[ZMod 2] V} (hl : l ∈ orthogonalGroup q)
    (hll : l * l = 1) {H T : Submodule (ZMod 2) V} {x₁ x₂ : V} (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H)
    (hHT : H ≤ T ⊔ Submodule.span (ZMod 2) {x₁, x₂})
    (hsing : ∀ x ∈ H, q (l x - x) = 0)
    (hT : ∀ x ∈ T, ∀ x' ∈ H, polar q (l x - x) x' = 0)
    (h12 : polar q (l x₁ - x₁) x₂ = 0) :
    ∀ x ∈ H, ∀ x' ∈ H, polar q (l x - x) x' = 0 := by
  let Z : V → Submodule (ZMod 2) V := fun y =>
    LinearMap.ker ((q.polarBilin.flip y).comp ((l : V →ₗ[ZMod 2] V) - LinearMap.id))
  have hZ : ∀ x y, x ∈ Z y ↔ polar q (l x - x) y = 0 := fun x y => by
    simp only [Z, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.flip_apply, polarBilin_apply_apply]
    rfl
  have key : ∀ y, T ≤ Z y → x₁ ∈ Z y → x₂ ∈ Z y → H ≤ Z y := fun y hT' h1 h2 =>
    hHT.trans (sup_le hT' (Submodule.span_le.mpr (by
      rintro v (rfl | rfl)
      · exact h1
      · exact h2)))
  have hsymm : ∀ x y, polar q (l x - x) y = polar q (l y - y) x := polar_sub_comm hl hll
  have h11 : H ≤ Z x₁ := key _ (fun x hx => (hZ _ _).mpr (hT x hx _ hx₁))
    ((hZ _ _).mpr (by rw [polar_sub_self_eq hl]; exact hsing _ hx₁))
    ((hZ _ _).mpr (by rw [hsymm]; exact h12))
  have h22 : H ≤ Z x₂ := key _ (fun x hx => (hZ _ _).mpr (hT x hx _ hx₂))
    ((hZ _ _).mpr h12) ((hZ _ _).mpr (by rw [polar_sub_self_eq hl]; exact hsing _ hx₂))
  intro x hx x' hx'
  refine (hZ _ _).mp (key x' (fun v hv => (hZ _ _).mpr (hT v hv x' hx')) ?_ ?_ hx)
  · exact (hZ _ _).mpr (by rw [hsymm]; exact (hZ _ _).mp (h11 hx'))
  · exact (hZ _ _).mpr (by rw [hsymm]; exact (hZ _ _).mp (h22 hx'))

theorem finrank_sup_span_singleton [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    {x : V} (hx : x ∉ U) : finrank (ZMod 2) ↥(U ⊔ (ZMod 2) ∙ x) = finrank (ZMod 2) U + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ((ZMod 2) ∙ x)
  have h2 : U ⊓ (ZMod 2) ∙ x = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvU, hvx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvx
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul]
      exact Submodule.zero_mem _
    · rw [one_smul] at hvU
      exact absurd hvU hx
  have h3 : finrank (ZMod 2) ((ZMod 2) ∙ x) = 1 :=
    finrank_span_singleton fun h => hx (h ▸ U.zero_mem)
  rw [h2, finrank_bot] at h1
  omega

theorem exists_le_sup_span_pair [FiniteDimensional (ZMod 2) V] {H T : Submodule (ZMod 2) V}
    (hTH : T ≤ H) (hdim : finrank (ZMod 2) H ≤ finrank (ZMod 2) T + 2) :
    ∃ x₁ ∈ H, ∃ x₂ ∈ H, H ≤ T ⊔ Submodule.span (ZMod 2) {x₁, x₂} := by
  by_cases h1 : H ≤ T
  · exact ⟨0, H.zero_mem, 0, H.zero_mem, h1.trans le_sup_left⟩
  obtain ⟨x₁, hx₁H, hx₁T⟩ := IsConcreteLE.not_le_iff_exists.mp h1
  have hspan : ∀ y : V, Submodule.span (ZMod 2) {x₁, y} = (ZMod 2) ∙ x₁ ⊔ (ZMod 2) ∙ y :=
    fun y => by rw [Submodule.span_insert]
  by_cases h2 : H ≤ T ⊔ (ZMod 2) ∙ x₁
  · refine ⟨x₁, hx₁H, x₁, hx₁H, h2.trans ?_⟩
    rw [hspan, sup_idem]
  obtain ⟨x₂, hx₂H, hx₂T⟩ := IsConcreteLE.not_le_iff_exists.mp h2
  refine ⟨x₁, hx₁H, x₂, hx₂H, ?_⟩
  have e : T ⊔ Submodule.span (ZMod 2) {x₁, x₂} = (T ⊔ (ZMod 2) ∙ x₁) ⊔ (ZMod 2) ∙ x₂ := by
    rw [hspan, sup_assoc]
  have hle : T ⊔ Submodule.span (ZMod 2) {x₁, x₂} ≤ H := by
    rw [e]
    exact sup_le (sup_le hTH ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁H))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₂H)
  have hd : finrank (ZMod 2) H ≤ finrank (ZMod 2) ↥(T ⊔ Submodule.span (ZMod 2) {x₁, x₂}) := by
    rw [e, finrank_sup_span_singleton hx₂T, finrank_sup_span_singleton hx₁T]
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle hd).ge

theorem exists_le_sup_span_singleton [FiniteDimensional (ZMod 2) V]
    {H T : Submodule (ZMod 2) V} (hTH : T ≤ H)
    (hdim : finrank (ZMod 2) H ≤ finrank (ZMod 2) T + 1) :
    ∃ x ∈ H, H ≤ T ⊔ (ZMod 2) ∙ x := by
  by_cases h1 : H ≤ T
  · exact ⟨0, H.zero_mem, h1.trans le_sup_left⟩
  obtain ⟨x, hxH, hxT⟩ := IsConcreteLE.not_le_iff_exists.mp h1
  refine ⟨x, hxH, ?_⟩
  have hle : T ⊔ (ZMod 2) ∙ x ≤ H :=
    sup_le hTH ((Submodule.span_singleton_le_iff_mem _ _).mpr hxH)
  have hd : finrank (ZMod 2) H ≤ finrank (ZMod 2) ↥(T ⊔ (ZMod 2) ∙ x) := by
    rw [finrank_sup_span_singleton hxT]
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle hd).ge

theorem exists_mem_not_mem_finset {X : Type*} {A : Set X} (F : Finset X)
    (h : F.card < Nat.card A) : ∃ x ∈ A, x ∉ F := by
  by_contra hcon
  push Not at hcon
  have h1 : A ⊆ (F : Set X) := fun x hx => hcon x hx
  have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h2
  omega

theorem card_le_four_of_le_pointRadical [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {c : V} (hc0 : c ≠ 0) (hc : q c = 0)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : A ≤ pointRadical q c)
    (hA2 : ∀ l ∈ A, l ≠ 1 → ¬ IsTypeA q l 2) : Nat.card A ≤ 4 := by
  classical
  have hq1 : ∀ u, polar q c u = 0 → eichler q c u ∈ A → eichler q c u ≠ 1 → q u = 1 := by
    intro u hu hA' h1
    have hu' : u ∉ (ZMod 2) ∙ c := fun h => h1 ((eichler_eq_one_iff hq hc0 hc hu).mpr h)
    rcases zmod2_eq_zero_or_eq_one (q u) with h | h
    · exact absurd ((eichler_type_of_not_mem_span hq hc0 hc hu hu').2.1 h) (hA2 _ hA' h1)
    · exact h
  have hrep : ∀ l ∈ A, ∃ u, polar q c u = 0 ∧ l = eichler q c u := fun l hl =>
    (mem_pointRadical_iff hq hc0 hc).mp (hA hl)
  have hsq : ∀ u, polar q c u = 0 → eichler q c u * eichler q c u = 1 := fun u hu => by
    rw [eichler_mul hu hu, vec_add_self, eichler_zero_right]
  by_contra hcard
  push Not at hcard
  have hcA : Nat.card (A : Set (V ≃ₗ[ZMod 2] V)) = Nat.card A := rfl
  obtain ⟨l₁, hl₁, hl₁1⟩ := exists_mem_not_mem_finset (A := (A : Set (V ≃ₗ[ZMod 2] V)))
    ({1} : Finset (V ≃ₗ[ZMod 2] V)) (by rw [Finset.card_singleton, hcA]; omega)
  obtain ⟨l₂, hl₂, hl₂1⟩ := exists_mem_not_mem_finset (A := (A : Set (V ≃ₗ[ZMod 2] V)))
    ({1, l₁} : Finset (V ≃ₗ[ZMod 2] V))
    (lt_of_le_of_lt Finset.card_le_two (by rw [hcA]; omega))
  obtain ⟨l₃, hl₃, hl₃1⟩ := exists_mem_not_mem_finset (A := (A : Set (V ≃ₗ[ZMod 2] V)))
    ({1, l₁, l₂, l₁ * l₂} : Finset (V ≃ₗ[ZMod 2] V))
    (lt_of_le_of_lt Finset.card_le_four (by rw [hcA]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl₁1 hl₂1 hl₃1
  obtain ⟨u₁, hu₁, rfl⟩ := hrep l₁ hl₁
  obtain ⟨u₂, hu₂, rfl⟩ := hrep l₂ hl₂
  obtain ⟨u₃, hu₃, rfl⟩ := hrep l₃ hl₃
  have hp : ∀ u v, polar q c u = 0 → polar q c v = 0 → polar q c (u + v) = 0 :=
    fun u v hu hv => by rw [polar_add_right, hu, hv, add_zero]
  have hu₁₂ := hp _ _ hu₁ hu₂
  have hu₁₃ := hp _ _ hu₁ hu₃
  have hu₂₃ := hp _ _ hu₂ hu₃
  have hu₁₂₃ := hp _ _ hu₁₂ hu₃
  have hmul : ∀ u v, polar q c u = 0 → polar q c v = 0 → eichler q c u ∈ A →
      eichler q c v ∈ A → eichler q c (u + v) ∈ A := fun u v hu hv h1 h2 => by
    rw [← eichler_mul hu hv]
    exact mul_mem h1 h2
  have hne : ∀ u v w, polar q c u = 0 → polar q c v = 0 → eichler q c v ≠ eichler q c w →
      eichler q c u * eichler q c v = 1 → eichler q c u * eichler q c w = 1 → False :=
    fun u v w _ _ hvw h1 h2 => hvw (mul_left_cancel (h1.trans h2.symm))
  have n₁₂ : eichler q c (u₁ + u₂) ≠ 1 := fun h => hne u₁ u₂ u₁ hu₁ hu₂ hl₂1.2
    (by rw [eichler_mul hu₁ hu₂, h]) (hsq u₁ hu₁)
  have n₁₃ : eichler q c (u₁ + u₃) ≠ 1 := fun h => hne u₁ u₃ u₁ hu₁ hu₃ hl₃1.2.1
    (by rw [eichler_mul hu₁ hu₃, h]) (hsq u₁ hu₁)
  have n₂₃ : eichler q c (u₂ + u₃) ≠ 1 := fun h => hne u₂ u₃ u₂ hu₂ hu₃ hl₃1.2.2.1
    (by rw [eichler_mul hu₂ hu₃, h]) (hsq u₂ hu₂)
  have n₁₂₃ : eichler q c (u₁ + u₂ + u₃) ≠ 1 := fun h => hne (u₁ + u₂) u₃ (u₁ + u₂) hu₁₂ hu₃
    (by rw [← eichler_mul hu₁ hu₂]; exact hl₃1.2.2.2) (by rw [eichler_mul hu₁₂ hu₃, h])
    (hsq _ hu₁₂)
  have q₁ := hq1 u₁ hu₁ hl₁ hl₁1
  have q₂ := hq1 u₂ hu₂ hl₂ hl₂1.1
  have q₃ := hq1 u₃ hu₃ hl₃ hl₃1.1
  have q₁₃ := hq1 _ hu₁₃ (hmul _ _ hu₁ hu₃ hl₁ hl₃) n₁₃
  have q₂₃ := hq1 _ hu₂₃ (hmul _ _ hu₂ hu₃ hl₂ hl₃) n₂₃
  have q₁₂ := hq1 _ hu₁₂ (hmul _ _ hu₁ hu₂ hl₁ hl₂) n₁₂
  have q₁₂₃ := hq1 _ hu₁₂₃ (hmul _ _ hu₁₂ hu₃ (hmul _ _ hu₁ hu₂ hl₁ hl₂) hl₃) n₁₂₃
  have e : q (u₁ + u₂ + u₃) =
      q (u₁ + u₂) + q u₃ + ((q (u₁ + u₃) - q u₁ - q u₃) + (q (u₂ + u₃) - q u₂ - q u₃)) := by
    have h1 : polar q (u₁ + u₂) u₃ = polar q u₁ u₃ + polar q u₂ u₃ := polar_add_left _ _ _ _
    simp only [polar] at h1
    linear_combination h1
  rw [q₁₂₃, q₁₂, q₃, q₁₃, q₁, q₂₃, q₂] at e
  exact absurd e (by decide)

theorem card_le_eight [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {c : V} (hc0 : c ≠ 0) (hc : q c = 0) {P T : Submodule (ZMod 2) V}
    (hP : ∀ x ∈ P, q x = 0) (hPT : P ≤ T)
    (hT : T ≤ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ c))
    (hdim : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ c)) ≤
      finrank (ZMod 2) T + 2)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAO : A ≤ orthogonalGroup q)
    (hAinv : ∀ l ∈ A, l * l = 1) (hAc : ∀ l ∈ A, l c = c)
    (hAP : ∀ l ∈ A, ∀ x, polar q c x = 0 → l x - x ∈ P)
    (hAT : ∀ l ∈ A, ∀ x ∈ T, l x - x ∈ (ZMod 2) ∙ c)
    (hA2 : ∀ l ∈ A, l ≠ 1 → ¬ IsTypeA q l 2) : Nat.card A ≤ 8 := by
  set H := LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ c) with hH
  have hmemH : ∀ x, x ∈ H ↔ polar q c x = 0 := fun x => mem_orthogonal_span_singleton_iff
  obtain ⟨x₁, hx₁, x₂, hx₂, hle⟩ := exists_le_sup_span_pair hT hdim
  have hβT : ∀ l ∈ A, ∀ x ∈ T, ∀ x' ∈ H, polar q (l x - x) x' = 0 := by
    intro l hl x hx x' hx'
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hAT l hl x hx)
    rw [← ha, polar_smul_left, (hmemH x').mp hx', smul_zero]
  let φ : A →* Multiplicative (ZMod 2) :=
    { toFun := fun l => Multiplicative.ofAdd (polar q ((l : V ≃ₗ[ZMod 2] V) x₁ - x₁) x₂)
      map_one' := by simp
      map_mul' := fun l l' => by
        rw [← ofAdd_add]
        congr 1
        have hv : (l' : V ≃ₗ[ZMod 2] V) x₁ - x₁ ∈ T :=
          hPT (hAP l' l'.2 x₁ ((hmemH x₁).mp hx₁))
        have h0 := hβT l l.2 _ hv x₂ hx₂
        have e : ((l * l' : A) : V ≃ₗ[ZMod 2] V) x₁ - x₁ =
            ((l : V ≃ₗ[ZMod 2] V) x₁ - x₁) + ((l : V ≃ₗ[ZMod 2] V)
              ((l' : V ≃ₗ[ZMod 2] V) x₁ - x₁) - ((l' : V ≃ₗ[ZMod 2] V) x₁ - x₁)) +
              ((l' : V ≃ₗ[ZMod 2] V) x₁ - x₁) := by
          rw [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
          abel
        rw [e, polar_add_left, polar_add_left, h0, add_zero] }
  have hA₀ : φ.ker.map A.subtype ≤ pointRadical q c := by
    rintro _ ⟨l, hl, rfl⟩
    have hl0 : polar q ((l : V ≃ₗ[ZMod 2] V) x₁ - x₁) x₂ = 0 :=
      Multiplicative.ofAdd.injective (MonoidHom.mem_ker.mp hl)
    have hlO := hAO l.2
    have hvan := polar_sub_eq_zero_of_le hlO (hAinv l l.2) hx₁ hx₂ hle
      (fun x hx => hP _ (hAP l l.2 x ((hmemH x).mp hx))) (hβT l l.2) hl0
    refine mem_pointRadical.mpr ⟨hlO, hAc l l.2, fun x hx => ?_, fun v => ?_⟩
    · rw [← LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) ((ZMod 2) ∙ c)]
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x' hx' => ?_
      change q.polarBilin x' ((l : V ≃ₗ[ZMod 2] V) x - x) = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact hvan x ((hmemH x).mpr hx) x' hx'
    · have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hlO c v
      rw [hAc l l.2] at h1
      change polar q c ((l : V ≃ₗ[ZMod 2] V) v - v) = 0
      rw [polar_sub_right, h1, sub_self]
  have h4 := card_le_four_of_le_pointRadical hq hc0 hc hA₀ fun l hl hl1 =>
    hA2 l (Subgroup.map_subtype_le _ hl) hl1
  rw [Subgroup.card_map_of_injective A.subtype_injective] at h4
  have hidx := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hidx
  have hrange : Nat.card φ.range ≤ 2 := by
    calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [← hidx]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 4 * 2 := Nat.mul_le_mul h4 hrange
    _ = 8 := rfl

end CFSG.LargeExtraspecial.S11
