module

public import CFSG.CharacterTheory.Wreathed.BrauerWongLocal
public import CFSG.CharacterTheory.Wreathed.BrauerWongFocal
public import CFSG.CharacterTheory.Wreathed.BrauerWongModel

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

section Basic

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

@[expose] def modelOmega : Subgroup G :=
  (Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)}).map (wreathModelHom S e)

theorem mem_modelOmega_iff (hn : 1 ≤ n) (g : G) :
    g ∈ modelOmega S e ↔ g ∈ modelBase S e ∧ g ^ 2 = 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_closure_x_x2_iff n hn] at hw
    exact ⟨(mem_modelBase_iff S e w).mpr hw.1, by rw [← map_pow, hw.2, map_one]⟩
  · rintro ⟨⟨w, hw, rfl⟩, hsq⟩
    refine ⟨w, (mem_closure_x_x2_iff n hn w).mpr ⟨hw, ?_⟩, rfl⟩
    apply wreathModelHom_injective S e
    rw [map_pow, hsq, map_one]

theorem modelOmega_le_modelBase (hn : 1 ≤ n) : modelOmega S e ≤ modelBase S e :=
  fun g hg => ((mem_modelOmega_iff S e hn g).mp hg).1

theorem modelBase_commute (x y : G) (hx : x ∈ modelBase S e) (hy : y ∈ modelBase S e) :
    x * y = y * x := by
  have h := isMulCommutative_iff.mp (isMulCommutative_of_le_modelBase S e (le_refl _))
    ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem modelBase_le_centralizer_modelOmega (hn : 1 ≤ n) :
    modelBase S e ≤ Subgroup.centralizer (modelOmega S e : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact modelBase_commute S e d x (modelOmega_le_modelBase S e hn hd) hx

theorem normalizer_modelBase_le_normalizer_modelOmega (hn : 1 ≤ n) :
    Subgroup.normalizer (modelBase S e : Set G) ≤ Subgroup.normalizer (modelOmega S e : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro d
  rw [mem_modelOmega_iff S e hn, mem_modelOmega_iff S e hn, ← (Subgroup.mem_normalizer_iff.mp hk d)]
  constructor
  · rintro ⟨hd, hsq⟩
    exact ⟨hd, by rw [conj_pow, hsq]; group⟩
  · rintro ⟨hd, hsq⟩
    refine ⟨hd, ?_⟩
    rw [conj_pow] at hsq
    have := congrArg (fun y => k⁻¹ * y * k) hsq
    simpa [mul_assoc] using this

theorem mem_modelCenter_of_commute_outside (hn : 1 ≤ n) {u w : G} (hu : u ∈ modelBase S e)
    (hw : w ∈ (S : Subgroup G)) (hwB : w ∉ modelBase S e) (hc : u * w = w * u) :
    u ∈ modelCenter S e := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨w', rfl⟩ := exists_wreathModelHom_eq S e hw
  rw [mem_modelBase_iff] at hwB
  rw [mem_modelCenter_iff]
  obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective u'
  obtain ⟨⟨c, d, g⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w'
  change element _ a b f ∈ baseSubgroup _ at hu'
  change element _ c d g ∉ baseSubgroup _ at hwB
  change element _ a b f ∈ Original.Z _
  rw [element_mem_base] at hu' hwB
  subst hu'
  have hg : g = 1 := (swap_exponent_cases g).resolve_left hwB
  subst hg
  have hc' : Commute (element _ a b 0) (element (2 ^ n) c d 1) := by
    apply wreathModelHom_injective S e
    rw [map_mul, map_mul]
    exact hc
  rw [base_commutes_swap_iff] at hc'
  exact (mem_Z_iff _ hm _ _ _).mpr ⟨rfl, hc'⟩

theorem modelHom_x2_not_mem_modelCenter (hn : 1 ≤ n) :
    wreathModelHom S e (Original.x2 (2 ^ n)) ∉ modelCenter S e := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  rw [mem_modelCenter_iff, x2_eq_element, mem_Z_iff _ hm]
  exact fun h => half_ne_zero n hn h.2

theorem modelHom_z_not_mem_modelBase :
    wreathModelHom S e (Original.z (2 ^ n)) ∉ modelBase S e := by
  rw [mem_modelBase_iff, Original.z, element_mem_base]
  exact one_ne_zero

end Basic

variable [Finite G]

theorem modelBase_sylow_of_forall {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (C : Subgroup G) (hBC : modelBase S e ≤ C)
    (hC : ∀ k ∈ Subgroup.normalizer (modelBase S e : Set G), ∀ w ∈ (S : Subgroup G),
      w ∉ modelBase S e → k * w * k⁻¹ ∉ C) :
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = modelBase S e := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 ((modelBase S e).subgroupOf C) :=
    (S.isPGroup'.to_le (modelBase_le_sylow S e)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hBC).symm
  obtain ⟨P, hP⟩ := hBp.exists_le_sylow
  refine ⟨P, ?_⟩
  set P₀ : Subgroup G := (P : Subgroup C).map C.subtype
  have hBP₀ : modelBase S e ≤ P₀ := by
    intro x hx
    exact ⟨⟨x, hBC hx⟩, hP hx, rfl⟩
  have hP₀p : IsPGroup 2 P₀ := P.isPGroup'.map C.subtype
  have hP₀C : P₀ ≤ C := Subgroup.map_subtype_le _
  symm
  apply eq_of_normalizer_inf_le hP₀p hBP₀
  intro x ⟨hxN, hxP⟩
  by_contra hxB
  set N := Subgroup.normalizer (modelBase S e : Set G)
  have hMp : IsPGroup 2 ↥(N ⊓ P₀) := hP₀p.to_le inf_le_right
  obtain ⟨k, hkN, hk⟩ := exists_conj_mem_sylow_in (modelBaseNormalizerSylow S e)
    (inf_le_left : N ⊓ P₀ ≤ N) hMp
  have hwS : k⁻¹ * x * k ∈ (S : Subgroup G) := by
    have h := hk x ⟨hxN, hxP⟩
    rw [modelBaseNormalizerSylow_coe, Subgroup.subgroupOf_map_subtype] at h
    exact h.1
  have hwB : k⁻¹ * x * k ∉ modelBase S e := by
    intro h
    apply hxB
    have := (Subgroup.mem_normalizer_iff''.mp hkN x).mpr h
    exact this
  apply hC k hkN _ hwS hwB
  have : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
  rw [this]
  exact hP₀C hxP

theorem modelBase_sylow_centralizer_modelOmega {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ∃ P : Sylow 2 (Subgroup.centralizer (modelOmega S e : Set G)),
      (P : Subgroup _).map (Subgroup.centralizer (modelOmega S e : Set G)).subtype =
        modelBase S e := by
  apply modelBase_sylow_of_forall S e _ (modelBase_le_centralizer_modelOmega S e (by omega))
  intro k hk w hwS hwB hwC
  set j₁ := wreathModelHom S e (Original.x2 (2 ^ n))
  have hj₁ : j₁ ∈ modelOmega S e :=
    ⟨Original.x2 (2 ^ n), Subgroup.subset_closure (by simp), rfl⟩
  have hd : k * j₁ * k⁻¹ ∈ modelOmega S e :=
    (Subgroup.mem_normalizer_iff.mp
      (normalizer_modelBase_le_normalizer_modelOmega S e (by omega) hk) j₁).mp hj₁
  have hc := Subgroup.mem_centralizer_iff.mp hwC _ hd
  have hc' : j₁ * w = w * j₁ := by
    have h := congrArg (fun y => k⁻¹ * y * k) hc
    simpa [mul_assoc] using h
  have hj₁B : j₁ ∈ modelBase S e := modelOmega_le_modelBase S e (by omega) hj₁
  exact modelHom_x2_not_mem_modelCenter S e (by omega)
    (mem_modelCenter_of_commute_outside S e (by omega) hj₁B hwS hwB hc')

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hh d hd
    have hd' : g⁻¹ * d * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
    have := hh _ hd'
    calc
      d * (g * h * g⁻¹) = g * (g⁻¹ * d * g * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * d * g)) * g⁻¹ := by rw [this]
      _ = g * h * g⁻¹ * d := by group
  · intro hh d hd
    have hd' : g * d * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hg d).mp hd
    have := hh _ hd'
    calc
      d * h = g⁻¹ * ((g * d * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * d * g⁻¹)) * g := by rw [this]
      _ = h * d := by group

theorem normalizer_modelOmega_eq {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.normalizer (modelOmega S e : Set G) : Set G) =
      (Subgroup.centralizer (modelOmega S e : Set G) : Set G) *
        (Subgroup.normalizer (modelBase S e : Set G) : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨P, hP⟩ := modelBase_sylow_centralizer_modelOmega hn S e
    obtain ⟨c, hc, m, hm, rfl⟩ := exists_mem_mul_mem_normalizer P
      (normalizer_le_normalizer_centralizer _ hg)
    rw [hP] at hm
    exact ⟨c, hc, m, hm, rfl⟩
  · rintro _ ⟨c, hc, m, hm, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc)
      (normalizer_modelBase_le_normalizer_modelOmega S e (by omega) hm)

end CFSG.Wreathed.BrauerWong
