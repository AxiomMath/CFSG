module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Model
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup HarrisEnd
open scoped Pointwise

theorem EndB.quaternion_pow_facts :
    (∀ q : QuaternionGroup 2, q ^ 4 = 1) ∧
      (∀ u v : QuaternionGroup 2, u ^ 2 = 1 → v ^ 2 = 1 → u = 1 ∨ v = 1 ∨ u = v) ∧
      ∀ y u : QuaternionGroup 2, y ^ 2 ≠ 1 → u * y = y * u →
        u = 1 ∨ u = y ∨ u = y ^ 2 ∨ u = y ^ 3 := by
  decide

theorem EndB.facts_of_embed_quaternion {G : Type*} [Group G] {Θ : Subgroup G}
    (φ : ↥Θ →* QuaternionGroup 2) (hφ : Function.Injective φ) :
    (∀ u ∈ Θ, u ^ 4 = 1) ∧
      (∀ u ∈ Θ, ∀ v ∈ Θ, u ^ 2 = 1 → v ^ 2 = 1 → u = 1 ∨ v = 1 ∨ u = v) ∧
      ∀ y ∈ Θ, y ^ 2 ≠ 1 → ∀ u ∈ Θ, u * y = y * u → ∃ k : ℕ, u = y ^ k := by
  obtain ⟨h4, h2, hc⟩ := EndB.quaternion_pow_facts
  have hinj : ∀ a b : ↥Θ, φ a = φ b → (a : G) = b := fun a b h =>
    congrArg Subtype.val (hφ h)
  have hsq : ∀ u (hu : u ∈ Θ), u ^ 2 = 1 → φ ⟨u, hu⟩ ^ 2 = 1 := fun u hu hu2 => by
    rw [← map_pow, show (⟨u, hu⟩ : ↥Θ) ^ 2 = 1 from Subtype.ext (by simpa using hu2), map_one]
  refine ⟨fun u hu => ?_, fun u hu v hv hu2 hv2 => ?_, fun y hy hy2 u hu huy => ?_⟩
  · have := hinj (⟨u, hu⟩ ^ 4) 1 (by rw [map_pow, h4, map_one])
    simpa using this
  · rcases h2 _ _ (hsq u hu hu2) (hsq v hv hv2) with h | h | h
    · left
      have := hinj ⟨u, hu⟩ 1 (by rw [h, map_one])
      simpa using this
    · right; left
      have := hinj ⟨v, hv⟩ 1 (by rw [h, map_one])
      simpa using this
    · right; right
      exact hinj ⟨u, hu⟩ ⟨v, hv⟩ h
  · have hy2' : φ ⟨y, hy⟩ ^ 2 ≠ 1 := by
      intro h
      apply hy2
      have := hinj (⟨y, hy⟩ ^ 2) 1 (by rw [map_pow, h, map_one])
      simpa using this
    have huy' : φ ⟨u, hu⟩ * φ ⟨y, hy⟩ = φ ⟨y, hy⟩ * φ ⟨u, hu⟩ := by
      rw [← map_mul, ← map_mul,
        show (⟨u, hu⟩ : ↥Θ) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨u, hu⟩ from Subtype.ext huy]
    rcases hc _ _ hy2' huy' with h | h | h | h
    · refine ⟨0, ?_⟩
      have := hinj ⟨u, hu⟩ 1 (by rw [h, map_one])
      simpa using this
    · refine ⟨1, ?_⟩
      have := hinj ⟨u, hu⟩ ⟨y, hy⟩ h
      simpa using this
    · refine ⟨2, ?_⟩
      have := hinj ⟨u, hu⟩ (⟨y, hy⟩ ^ 2) (by rw [h, map_pow])
      simpa using this
    · refine ⟨3, ?_⟩
      have := hinj ⟨u, hu⟩ (⟨y, hy⟩ ^ 3) (by rw [h, map_pow])
      simpa using this

theorem EndB.exists_embed_quaternion {d : Equiv.Perm (Fin 42)}
    (hd : d ∈ PSL3Four.R) {Θ : Subgroup (Equiv.Perm (Fin 42))}
    (hΘ : Θ ≤ centralizer {d * PSL3Four.r₄ * d⁻¹} ⊓ PSL3Four.S) (hΘ2 : IsPGroup 2 Θ) :
    ∃ φ : ↥Θ →* QuaternionGroup 2, Function.Injective φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θ' := Θ.map (MulAut.conj d⁻¹).toMonoidHom with hΘ'
  have hΘ'C : Θ' ≤ PSL3Four.C₄ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨huc, huS⟩ := mem_inf.mp (hΘ hu)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change d⁻¹ * u * d ∈ centralizer {PSL3Four.r₄} ⊓ PSL3Four.S
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have h1 := mem_centralizer_singleton_iff.mp huc
      calc d⁻¹ * u * d * PSL3Four.r₄ = d⁻¹ * (u * (d * PSL3Four.r₄ * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * PSL3Four.r₄ * d⁻¹) * u) * d := by rw [h1]
        _ = PSL3Four.r₄ * (d⁻¹ * u * d) := by group
    · have := PSL3Four.conj_mem_S (inv_mem hd) huS
      rwa [inv_inv] at this
  have hΘ''2 : IsPGroup 2 ↥(Θ'.subgroupOf PSL3Four.C₄) :=
    (hΘ2.map _).of_equiv (subgroupOfEquivOfLe hΘ'C).symm
  obtain ⟨P, hP⟩ := hΘ''2.exists_le_sylow
  obtain ⟨eQ⟩ := nonempty_quaternion_sylow_C₄ P
  let f₁ : ↥Θ ≃* ↥Θ' := Θ.equivMapOfInjective _ (MulAut.conj d⁻¹).injective
  let f₂ : ↥Θ' ≃* ↥(Θ'.subgroupOf PSL3Four.C₄) := (subgroupOfEquivOfLe hΘ'C).symm
  refine ⟨eQ.symm.toMonoidHom.comp ((Subgroup.inclusion hP).comp
    (f₂.toMonoidHom.comp f₁.toMonoidHom)), ?_⟩
  exact eQ.symm.injective.comp ((Subgroup.inclusion_injective hP).comp
    (f₂.injective.comp f₁.injective))

theorem EndB.dihedral_sixteen_facts :
    (∀ x : DihedralGroup (2 ^ 3), x ^ 8 = 1) ∧
      ∀ x : DihedralGroup (2 ^ 3), ∀ m : Fin 8, x ^ 2 ≠ 1 → (x ^ (m : ℕ)) ^ 2 = 1 →
        (x ^ (m : ℕ) = 1 ∨ x ^ (m : ℕ) = DihedralGroup.r 4) ∧ (m : ℕ) % 2 = 0 := by
  decide

theorem EndB.pow_eq_of_dihedral {G : Type*} [Group G] {D A : Subgroup G}
    (eD : ↥D ≃* DihedralGroup (2 ^ 3)) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) {y : G} (hy : y ∈ D ⊔ A) (hy2 : y ^ 2 ≠ 1)
    {k : ℕ} (hk1 : y ^ k ≠ 1) (hk2 : (y ^ k) ^ 2 = 1) :
    y ^ k = (eD.symm (DihedralGroup.r 4) : G) := by
  obtain ⟨h8, hfac⟩ := EndB.dihedral_sixteen_facts
  have hAn : A ≤ normalizer (D : Set G) := fun a ha => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    exact (hAD a ha y hy).symm
  have hy' : y ∈ ((D : Set G) * (A : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left D A hAn]
    exact hy
  obtain ⟨d, hd, a, ha, hya⟩ := hy'
  simp only at hya
  subst hya
  have hda : Commute d a := (hAD a ha d hd).symm
  have hdk : ∀ n : ℕ, (d * a) ^ n = d ^ n * a ^ n := fun n => hda.mul_pow n
  have ha2 := hA2 a ha
  set x := eD ⟨d, hd⟩ with hx
  have hpow : ∀ n : ℕ, ((eD.symm (x ^ n) : ↥D) : G) = d ^ n := fun n => by
    rw [map_pow, hx, MulEquiv.symm_apply_apply, Subgroup.coe_pow]
  have hxe : ∀ n : ℕ, x ^ n = 1 → d ^ n = 1 := fun n h => by
    rw [← hpow n, h, map_one, Subgroup.coe_one]
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    apply hy2
    rw [hdk, hxe 2 h, ha2, one_mul]
  have hkm : x ^ k = x ^ (k % 8) := by
    conv_lhs => rw [← Nat.mod_add_div k 8, pow_add, pow_mul, h8, one_pow, mul_one]
  have hxk2 : (x ^ (k % 8)) ^ 2 = 1 := by
    rw [← hkm]
    apply eD.symm.injective
    apply Subtype.ext
    rw [map_pow, map_pow, Subgroup.coe_pow, Subgroup.coe_pow, hx, MulEquiv.symm_apply_apply,
      map_one, Subgroup.coe_one]
    rw [← pow_mul, mul_comm k 2]
    rw [← pow_mul, hdk, mul_comm k 2, pow_mul a, ha2, one_pow, mul_one] at hk2
    exact hk2
  obtain ⟨hmem, hev⟩ := hfac x ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩ hx2 hxk2
  have hkev : a ^ k = 1 := by
    have : k % 2 = 0 := by
      have := Nat.mod_mod_of_dvd k (show 2 ∣ 8 by norm_num)
      simp only at hev
      omega
    obtain ⟨n, hn⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [hn, pow_mul, ha2, one_pow]
  rw [hdk, hkev, mul_one] at hk1 ⊢
  rcases hmem with h | h
  · exact absurd (hxe k (hkm.trans h)) hk1
  · rw [← hpow k, hkm, h]
