module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g3b_hat {Z Y : Type} [Group Z] [Group Y] (φ : Z →* Y) (a : Z ≃* Z)
    (ha : ∀ z, φ z = 1 → φ (a z) = 1) (hinv : ∀ z, a (a z) = z) (M : Subgroup Y)
    (hM : ∀ y, y ∈ M ↔ ∃ z, φ z = y) :
    ∃ b : ↥M ≃* ↥M, (∀ z, b ⟨φ z, (hM _).mpr ⟨z, rfl⟩⟩ = ⟨φ (a z), (hM _).mpr ⟨a z, rfl⟩⟩) ∧
      ∀ x, b (b x) = x := by
  let ρ : Z →* ↥M := φ.codRestrict M (fun z => (hM _).mpr ⟨z, rfl⟩)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨z, hz⟩ := (hM y).mp y.2
    exact ⟨z, Subtype.ext hz⟩
  have hker : ρ.ker ≤ (ρ.comp a.toMonoidHom).ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    have h1 : φ z = 1 := congrArg Subtype.val hz
    exact Subtype.ext (ha z h1)
  let b₀ : ↥M →* ↥M := (ρ.liftOfSurjective hρs) ⟨ρ.comp a.toMonoidHom, hker⟩
  have hb₀ : ∀ z, b₀ (ρ z) = ρ (a z) := fun z =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ρ.comp a.toMonoidHom, hker⟩ z
  have hbb : b₀.comp b₀ = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := hρs x
    simp only [MonoidHom.comp_apply, hb₀, hinv, MonoidHom.id_apply]
  refine ⟨MonoidHom.toMulEquiv b₀ b₀ hbb hbb, fun z => hb₀ z, fun x => ?_⟩
  have := congrArg (fun f => f x) hbb
  simpa using this

@[expose] def sec8t84g3b_M {Y : Type} [Group Y] (E F : Subgroup Y) : Subgroup Y :=
  twoRes (normalizer ((E ⊔ F : Subgroup Y) : Set Y))

@[expose] def Sec8T84G3BS4Concl (Y : Type) [Group Y] [Finite Y] (E F : Subgroup Y) : Prop :=
  E ⊔ F ≤ sec8t84g3b_M E F ∧
  (∀ y ∈ sec8t84g3b_M E F, (∃ k : ℕ, orderOf y = 3 ^ k) → y ≠ 1 →
      orderOf y = 3 ∧ ∀ u ∈ E ⊔ F, y * u = u * y → u = 1) ∧
  ∀ a : ↥(sec8t84g3b_M E F) ≃* ↥(sec8t84g3b_M E F),
    (∀ x, a (a x) = x) →
    Nat.card {x : ↥(sec8t84g3b_M E F) // (x : Y) ∈ E ⊔ F ∧ a x = x} = 4 →
    (∀ x : ↥(sec8t84g3b_M E F), (x : Y) ∈ E ⊔ F → a x = x → x * x = 1) →
      ∃ y : ↥(sec8t84g3b_M E F), orderOf y = 3 ∧ a y = y

theorem sec8t84g3b_one_side {G : Type} [Group G] {Y : Type} [Group Y] [Finite Y]
    {E F : Subgroup Y} (hS : Sec8T84G3BS4Concl Y E F) {Z O U : Subgroup G} {γ : G}
    (φ : ↥Z →* Y) (hγ2 : γ * γ = 1) (hγZ : ∀ z ∈ Z, γ * z * γ⁻¹ ∈ Z)
    (hγO : ∀ o ∈ O, γ * o * γ⁻¹ ∈ O) (hγU : ∀ u ∈ U, γ * u * γ⁻¹ ∈ U)
    (hker : ∀ z : ↥Z, φ z = 1 ↔ (z : G) ∈ O)
    (hrange : ∀ y, y ∈ sec8t84g3b_M E F ↔ ∃ z, φ z = y) (hUZ : U ≤ Z)
    (hOU : ∀ u ∈ U, u ∈ O → u = 1)
    (hUJ : ∀ z : ↥Z, (z : G) ∈ U → φ z ∈ E ⊔ F)
    (hJU : ∀ x ∈ E ⊔ F, ∃ z : ↥Z, (z : G) ∈ U ∧ φ z = x)
    (hC : Nat.card ↥(U ⊓ centralizer ({γ} : Set G)) = 4)
    (hCe : ∀ u ∈ U ⊓ centralizer ({γ} : Set G), u * u = 1) :
    ∃ z ∈ Z, z ∉ O ∧ z ^ 3 ∈ O ∧ γ * z * γ⁻¹ * z⁻¹ ∈ O ∧
      ∀ u ∈ U, z * u = u * z → u = 1 := by
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
  let α : ↥Z ≃* ↥Z :=
    { toFun := fun z => ⟨γ * z * γ⁻¹, hγZ z z.2⟩
      invFun := fun z => ⟨γ * z * γ⁻¹, hγZ z z.2⟩
      left_inv := fun z => Subtype.ext (by
        change γ * (γ * (z : G) * γ⁻¹) * γ⁻¹ = z
        calc γ * (γ * (z : G) * γ⁻¹) * γ⁻¹ = (γ * γ) * z * (γ⁻¹ * γ⁻¹) := by group
          _ = z := by rw [hγ2, ← mul_inv_rev, hγ2, inv_one]; simp)
      right_inv := fun z => Subtype.ext (by
        change γ * (γ * (z : G) * γ⁻¹) * γ⁻¹ = z
        calc γ * (γ * (z : G) * γ⁻¹) * γ⁻¹ = (γ * γ) * z * (γ⁻¹ * γ⁻¹) := by group
          _ = z := by rw [hγ2, ← mul_inv_rev, hγ2, inv_one]; simp)
      map_mul' := fun x y => Subtype.ext (by
        change γ * ((x : G) * y) * γ⁻¹ = γ * x * γ⁻¹ * (γ * y * γ⁻¹)
        group) }
  have hα : ∀ z : ↥Z, ((α z : ↥Z) : G) = γ * z * γ⁻¹ := fun z => rfl
  have hαα : ∀ z, α (α z) = z := fun z => α.left_inv z
  have ha : ∀ z : ↥Z, φ z = 1 → φ (α z) = 1 := by
    intro z hz
    exact (hker _).mpr (by rw [hα]; exact hγO _ ((hker z).mp hz))
  obtain ⟨b, hb, hbb⟩ := sec8t84g3b_hat φ α ha hαα (sec8t84g3b_M E F) hrange
  have hfix : ∀ z : ↥Z, (z : G) ∈ U → φ (α z) = φ z → (z : G) ∈ centralizer ({γ} : Set G) := by
    intro z hzU hφ
    have h1 : φ (α z * z⁻¹) = 1 := by rw [map_mul, map_inv, hφ, mul_inv_cancel]
    have h2 : ((α z * z⁻¹ : ↥Z) : G) ∈ O := (hker _).mp h1
    have h3 : ((α z * z⁻¹ : ↥Z) : G) ∈ U := by
      change γ * (z : G) * γ⁻¹ * (z : G)⁻¹ ∈ U
      exact U.mul_mem (hγU _ hzU) (U.inv_mem hzU)
    have h4 : γ * (z : G) * γ⁻¹ * (z : G)⁻¹ = 1 := hOU _ h3 h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)).symm
  have hfix' : ∀ z : ↥Z, (z : G) ∈ U → (z : G) ∈ centralizer ({γ} : Set G) → α z = z := by
    intro z _ hc
    refine Subtype.ext ?_
    rw [hα, ← Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hbx : ∀ (z : ↥Z) (hz : φ z ∈ sec8t84g3b_M E F), (z : G) ∈ U →
      (b ⟨φ z, hz⟩ = ⟨φ z, hz⟩ ↔ (z : G) ∈ centralizer ({γ} : Set G)) := by
    intro z hz hzU
    have h1 : b ⟨φ z, hz⟩ = ⟨φ (α z), (hrange _).mpr ⟨α z, rfl⟩⟩ := hb z
    rw [h1, Subtype.mk.injEq]
    exact ⟨fun h => hfix z hzU h, fun h => by rw [hfix' z hzU h]⟩
  have hmem : ∀ z : ↥Z, φ z ∈ sec8t84g3b_M E F := fun z => (hrange _).mpr ⟨z, rfl⟩
  have hcard : Nat.card {x : ↥(sec8t84g3b_M E F) // (x : Y) ∈ E ⊔ F ∧ b x = x} = 4 := by
    rw [← hC]
    symm
    refine Nat.card_eq_of_bijective
      (fun u : ↥(U ⊓ centralizer ({γ} : Set G)) =>
        (⟨⟨φ ⟨u, hUZ u.2.1⟩, hmem _⟩, hUJ _ u.2.1,
          (hbx ⟨u, hUZ u.2.1⟩ (hmem _) u.2.1).mpr u.2.2⟩ :
          {x : ↥(sec8t84g3b_M E F) // (x : Y) ∈ E ⊔ F ∧ b x = x})) ⟨?_, ?_⟩
    · intro u u' h
      have h1 : φ ⟨u, hUZ u.2.1⟩ = φ ⟨u', hUZ u'.2.1⟩ := by
        have := congrArg (fun x => ((x.1 : ↥(sec8t84g3b_M E F)) : Y)) h
        simpa using this
      have h2 : φ ((⟨u, hUZ u.2.1⟩ : ↥Z)⁻¹ * ⟨u', hUZ u'.2.1⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : (((u : G)⁻¹ * u' : G)) ∈ O := (hker _).mp h2
      have h4 : ((u : G)⁻¹ * u') ∈ U := U.mul_mem (U.inv_mem u.2.1) u'.2.1
      exact Subtype.ext (inv_mul_eq_one.mp (hOU _ h4 h3))
    · rintro ⟨⟨y, hy⟩, hyJ, hby⟩
      obtain ⟨z, hzU, hzy⟩ := hJU y hyJ
      have hyz : (⟨y, hy⟩ : ↥(sec8t84g3b_M E F)) = ⟨φ z, hmem z⟩ := Subtype.ext hzy.symm
      rw [hyz] at hby
      have hzC := (hbx z (hmem z) hzU).mp hby
      refine ⟨⟨(z : G), hzU, hzC⟩, ?_⟩
      refine Subtype.ext (Subtype.ext ?_)
      exact hzy
  have hexp : ∀ x : ↥(sec8t84g3b_M E F), (x : Y) ∈ E ⊔ F → b x = x → x * x = 1 := by
    rintro ⟨y, hy⟩ hyJ hby
    obtain ⟨z, hzU, hzy⟩ := hJU y hyJ
    have hyz : (⟨y, hy⟩ : ↥(sec8t84g3b_M E F)) = ⟨φ z, hmem z⟩ := Subtype.ext hzy.symm
    rw [hyz] at hby ⊢
    have hzC := (hbx z (hmem z) hzU).mp hby
    have hz2 : (z : G) * z = 1 := hCe _ ⟨hzU, hzC⟩
    refine Subtype.ext ?_
    change φ z * φ z = 1
    rw [← map_mul, show z * z = 1 from Subtype.ext hz2, map_one]
  obtain ⟨y, hy3, hby⟩ := hS.2.2 b hbb hcard hexp
  obtain ⟨z, hz⟩ := (hrange (y : Y)).mp y.2
  have hy3' : orderOf (y : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hy3
  have hyne : (y : Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy3'
    exact absurd hy3' (by norm_num)
  have hzO : (z : G) ∉ O := by
    intro h
    exact hyne (by rw [← hz]; exact (hker z).mpr h)
  have hz3 : (z : G) ^ 3 ∈ O := by
    have h1 : φ (z ^ 3) = 1 := by
      rw [map_pow, hz, ← hy3']
      exact pow_orderOf_eq_one _
    exact (hker _).mp h1
  have hzγ : γ * (z : G) * γ⁻¹ * (z : G)⁻¹ ∈ O := by
    have h1 : b ⟨φ z, hmem z⟩ = ⟨φ (α z), hmem (α z)⟩ := hb z
    have h2 : (⟨φ z, hmem z⟩ : ↥(sec8t84g3b_M E F)) = y := Subtype.ext hz
    rw [h2, hby] at h1
    have h3 : φ (α z) = φ z := ((congrArg Subtype.val h1).symm).trans hz.symm
    have h4 : φ (α z * z⁻¹) = 1 := by rw [map_mul, map_inv, h3, mul_inv_cancel]
    exact (hker _).mp h4
  refine ⟨z, z.2, hzO, hz3, hzγ, fun u hu hcomm => ?_⟩
  have hfp := (hS.2.1 (y : Y) y.2 ⟨1, by rw [pow_one]; exact hy3'⟩ hyne).2
  have huZ : u ∈ Z := hUZ hu
  have h1 : φ ⟨u, huZ⟩ = 1 := by
    refine hfp _ (hUJ _ hu) ?_
    rw [← hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  exact hOU u hu ((hker _).mp h1)

end CFSG.OddStandard.SmallF3.Omega
