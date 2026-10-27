module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsSylow

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion

theorem eq_quarter_or_neg {m : ℕ} (hm : 0 < m) (h4m : 4 ∣ m) {α : ZMod m} (h4 : 4 * α = 0)
    (h2 : 2 * α ≠ 0) : α = ((m / 4 : ℕ) : ZMod m) ∨ α = -((m / 4 : ℕ) : ZMod m) := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨k, rfl⟩ := h4m
  rw [show 4 * k / 4 = k by omega]
  have hval : α = (α.val : ZMod (4 * k)) := (ZMod.natCast_zmod_val α).symm
  have hvlt : α.val < 4 * k := ZMod.val_lt α
  have h4' : 4 * k ∣ 4 * α.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [← hval]
    exact h4
  have h2' : ¬ 4 * k ∣ 2 * α.val := by
    intro hd
    apply h2
    rw [hval]
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at this
    exact this
  obtain ⟨j, hj⟩ : k ∣ α.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4'
  have hj4 : j < 4 := by
    by_contra h
    have : k * 4 ≤ k * j := Nat.mul_le_mul_left k (by omega)
    omega
  have hjodd : ¬ 2 ∣ j := by
    rintro ⟨i, rfl⟩
    apply h2'
    rw [hj]
    exact ⟨i, by ring⟩
  interval_cases j
  · exact absurd (dvd_zero 2) hjodd
  · left
    rw [hval, hj, mul_one]
  · exact absurd (dvd_refl 2) hjodd
  · right
    rw [hval, hj]
    have h0 : ((4 * k : ℕ) : ZMod (4 * k)) = 0 := ZMod.natCast_self _
    have h1 : ((k * 3 : ℕ) : ZMod (4 * k)) + (k : ZMod (4 * k)) = 0 := by
      rw [← h0]
      push_cast
      ring
    exact eq_neg_of_add_eq_zero_left h1

theorem exists_element {m : ℕ} (g : Wreath m) : ∃ a b e, g = element m a b e := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  exact ⟨a, b, e, rfl⟩

theorem element_eq_element_iff {m : ℕ} {a b a' b' : ZMod m} {e e' : ZMod 2} :
    element m a b e = element m a' b' e' ↔ a = a' ∧ b = b' ∧ e = e' := by
  constructor
  · intro h
    have h' := congrArg (coordinateEquiv m) h
    simp only [coordinateEquiv, Equiv.coe_fn_mk, element_left_zero, element_left_one,
      element_right, toAdd_ofAdd, Prod.mk.injEq] at h'
    exact h'
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem rightHom_element (m : ℕ) (a b : ZMod m) (e : ZMod 2) :
    RegularWreathProduct.rightHom (element m a b e) = Multiplicative.ofAdd e :=
  rfl

theorem quarter_mem_range {m : ℕ} (hm : 0 < m) (h4m : 4 ∣ m)
    (ψ : QuaternionGroup 2 →* Wreath m) (hψ : Function.Injective ψ) :
    element m ((m / 4 : ℕ) : ZMod m) (-((m / 4 : ℕ) : ZMod m)) 0 ∈ ψ.range := by
  set r : Wreath m →* Multiplicative (ZMod 2) := RegularWreathProduct.rightHom with hr
  have hcases : ∀ t : Multiplicative (ZMod 2), t = 1 ∨ t = Multiplicative.ofAdd 1 := by
    intro t
    rcases swap_exponent_cases (Multiplicative.toAdd t) with h | h
    · left
      exact congrArg Multiplicative.ofAdd h
    · right
      exact congrArg Multiplicative.ofAdd h
  have hbase : ∀ g h : Wreath m, r g = 1 → r h = 1 → g * h = h * g := by
    intro g h hg hh
    obtain ⟨a, b, e, rfl⟩ := exists_element g
    obtain ⟨c, d, e', rfl⟩ := exists_element h
    rw [rightHom_element] at hg hh
    have he : e = 0 := congrArg Multiplicative.toAdd hg
    have he' : e' = 0 := congrArg Multiplicative.toAdd hh
    subst he he'
    rw [element_base_mul, element_base_mul, add_comm a c, add_comm b d]
  have key : ∃ u v : QuaternionGroup 2, v * u * v⁻¹ = u⁻¹ ∧ u ^ 2 ≠ 1 ∧ u ^ 4 = 1 ∧
      r (ψ u) = 1 ∧ r (ψ v) ≠ 1 := by
    have h11 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    rcases hcases (r (ψ (QuaternionGroup.a 1))) with h1 | h1 <;>
      rcases hcases (r (ψ (QuaternionGroup.xa 0))) with h2 | h2
    · exfalso
      have h := hbase _ _ h1 h2
      rw [← map_mul, ← map_mul] at h
      exact absurd (hψ h) (by decide)
    · exact ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, by decide, by decide, by decide, h1,
        h2 ▸ h11⟩
    · exact ⟨QuaternionGroup.xa 0, QuaternionGroup.a 1, by decide, by decide, by decide, h2,
        h1 ▸ h11⟩
    · refine ⟨QuaternionGroup.a 1 * QuaternionGroup.xa 0, QuaternionGroup.a 1, by decide,
        by decide, by decide, ?_, h1 ▸ h11⟩
      rw [map_mul, map_mul, h1, h2]
      decide
  obtain ⟨u, v, hvu, hu2, hu4, hru, hrv⟩ := key
  obtain ⟨α, β, e₁, hu⟩ := exists_element (ψ u)
  obtain ⟨γ, δ, e₂, hv⟩ := exists_element (ψ v)
  rw [hu, rightHom_element] at hru
  rw [hv, rightHom_element] at hrv
  have he₁ : e₁ = 0 := congrArg Multiplicative.toAdd hru
  have he₂ : e₂ = 1 := by
    rcases swap_exponent_cases e₂ with h | h
    · exact absurd (by rw [h]; rfl) hrv
    · exact h
  subst he₁ he₂
  have hconj := congrArg ψ hvu
  rw [map_mul, map_mul, map_inv, map_inv, hu, hv, conjugate_base_by_swap,
    element_base_inv] at hconj
  have hβ : β = -α := (element_eq_element_iff.mp hconj).1
  have h4 : 4 * α = 0 := by
    have h := congrArg ψ hu4
    rw [map_pow, map_one, hu, element_base_pow, element_base_eq_one_iff] at h
    have h1 := h.1
    rwa [nsmul_eq_mul, Nat.cast_ofNat] at h1
  have h2 : 2 * α ≠ 0 := by
    intro h
    apply hu2
    apply hψ
    rw [map_pow, map_one, hu, element_base_pow, element_base_eq_one_iff, hβ]
    refine ⟨?_, ?_⟩
    · rw [nsmul_eq_mul]
      exact_mod_cast h
    · rw [nsmul_eq_mul, mul_neg]
      push_cast
      rw [h, neg_zero]
  rcases eq_quarter_or_neg hm h4m h4 h2 with hα | hα
  · exact ⟨u, by rw [hu, hβ, hα]⟩
  · refine ⟨u⁻¹, ?_⟩
    rw [map_inv, hu, hβ, hα, element_base_inv, neg_neg]

theorem quarter_mul_swap_ne (n : ℕ) (hn : 2 ≤ n) :
    element (2 ^ n) ((2 ^ n / 4 : ℕ) : ZMod (2 ^ n)) (-((2 ^ n / 4 : ℕ) : ZMod (2 ^ n))) 0 *
        Original.z (2 ^ n) ≠
      Original.z (2 ^ n) *
        element (2 ^ n) ((2 ^ n / 4 : ℕ) : ZMod (2 ^ n)) (-((2 ^ n / 4 : ℕ) : ZMod (2 ^ n))) 0 := by
  intro h
  rw [Original.z, element_base_mul, element_swap_mul] at h
  have h1 := (element_eq_element_iff.mp h).1
  simp only [add_zero, zero_add] at h1
  have h4 : 4 ∣ 2 ^ n := (Nat.pow_dvd_pow 2 hn : 2 ^ 2 ∣ 2 ^ n)
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have h2 : ((2 * (2 ^ n / 4) : ℕ) : ZMod (2 ^ n)) = 0 := by
    push_cast
    linear_combination h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hpos : 0 < 2 * (2 ^ n / 4) := by
    have : 4 ≤ 2 ^ n := Nat.le_of_dvd (by positivity) h4
    omega
  have hle := Nat.le_of_dvd hpos h2
  have : 2 * (2 ^ n / 4) < 2 ^ n := by omega
  omega

variable {G : Type} [Group G]

theorem wreath_quaternion_element (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∃ y ∈ ((wreathedSetting n S e p f).S : Subgroup G),
      y ∉ centerOf ((wreathedSetting n S e p f).S : Subgroup G) ∧
      ∀ X : Subgroup G, X ≤ (wreathedSetting n S e p f).S →
        ((wreathedSetting n S e p f).S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
          (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X := by
  set y₀ : Wreath (2 ^ n) :=
    element (2 ^ n) ((2 ^ n / 4 : ℕ) : ZMod (2 ^ n)) (-((2 ^ n / 4 : ℕ) : ZMod (2 ^ n))) 0
    with hy₀
  have hinj := wreathModelHom_injective S e
  have hS : (S : Subgroup G) = (wreathModelHom S e).range := (wreathModelHom_range S e).symm
  refine ⟨wreathModelHom S e y₀, (e.symm y₀).property, ?_, ?_⟩
  · rintro ⟨-, hc⟩
    have hz : wreathModelHom S e (Original.z (2 ^ n)) ∈ (S : Subgroup G) :=
      (e.symm _).property
    have h := Subgroup.mem_centralizer_iff.mp hc _ hz
    rw [← map_mul, ← map_mul] at h
    exact quarter_mul_swap_ne n hn (hinj h).symm
  · rintro X hXS - ⟨Q, hQX, ⟨eQ⟩⟩
    have hQS : Q ≤ (S : Subgroup G) := hQX.trans hXS
    have hQmap : (Q.comap (wreathModelHom S e)).map (wreathModelHom S e) = Q := by
      rw [Subgroup.map_comap_eq, ← hS, inf_eq_right.mpr hQS]
    have e₀ : QuaternionGroup 2 ≃* Q.comap (wreathModelHom S e) :=
      (((Subgroup.equivMapOfInjective _ _ hinj).trans
        (MulEquiv.subgroupCongr hQmap)).trans eQ).symm
    set ψ : QuaternionGroup 2 →* Wreath (2 ^ n) :=
      (Q.comap (wreathModelHom S e)).subtype.comp e₀.toMonoidHom with hψ
    have hψinj : Function.Injective ψ := Subtype.val_injective.comp e₀.injective
    have h4 : 4 ∣ 2 ^ n := (Nat.pow_dvd_pow 2 hn : 2 ^ 2 ∣ 2 ^ n)
    obtain ⟨q, hq⟩ := quarter_mem_range (by positivity) h4 ψ hψinj
    apply hQX
    have hmem : y₀ ∈ Q.comap (wreathModelHom S e) := by
      rw [hy₀, ← hq]
      exact (e₀ q).property
    exact hmem

theorem mem_oddCoreIn_of_odd [Finite G] {C P : Subgroup G} (hP : IsPGroup 2 P)
    (hC : oddCoreIn C ⊔ P = C) {c : G} (hc : c ∈ C) (hodd : Odd (orderOf c)) :
    c ∈ oddCoreIn C := by
  have hPC : P ≤ C := hC ▸ le_sup_right
  set K : Subgroup C := CFSG.oddCore C with hK
  have hKn : K.Normal := CFSG.oddCore_normal C
  set Q : Subgroup C := P.subgroupOf C with hQ
  have hsup : K ⊔ Q = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQ,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPC]
    exact hC
  have hmem : (⟨c, hc⟩ : C) ∈ K ⊔ Q := by rw [hsup]; trivial
  obtain ⟨k, hk, x, hx, hkx⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  set π := QuotientGroup.mk' K with hπ
  have hk1 : π k = 1 := by
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
    exact hk
  have hπx : π ⟨c, hc⟩ = π x := by
    rw [← hkx, map_mul, hk1, one_mul]
  obtain ⟨j, hj⟩ := (hP.to_le le_rfl) ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
  have hxj : x ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
  have h1 : (π ⟨c, hc⟩) ^ 2 ^ j = 1 := by rw [hπx, ← map_pow, hxj, map_one]
  have h2 : (π ⟨c, hc⟩) ^ orderOf c = 1 := by
    rw [← map_pow, show (⟨c, hc⟩ : C) ^ orderOf c = 1 from Subtype.ext (by simp), map_one]
  have hcop : Nat.Coprime (2 ^ j) (orderOf c) := (Nat.coprime_two_left.mpr hodd).pow_left j
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop.gcd_eq_one, pow_one, ← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk'] at h3
  exact ⟨⟨c, hc⟩, h3, rfl⟩

theorem wreath_C_odd_le_oddCore [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ c ∈ (wreathedSetting n S e p f).C, Odd (orderOf c) →
      c ∈ oddCoreIn (wreathedSetting n S e p f).C := by
  intro c hc hodd
  have hP : IsPGroup 2 (wreathedSetting n S e p f).F₀ :=
    S.isPGroup'.to_le ((inf_le_left : (wreathedSetting n S e p f).F₀ ≤ _).trans inf_le_left)
  exact mem_oddCoreIn_of_odd hP (TIFacts.wreathedSetting_C_eq n hn S e p f) hc hodd

theorem wreath_C_le_oddCore_sup_D [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).C ≤
      oddCoreIn (wreathedSetting n S e p f).C ⊔ (wreathedSetting n S e p f).D := by
  calc (wreathedSetting n S e p f).C =
      oddCoreIn (wreathedSetting n S e p f).C ⊔ (wreathedSetting n S e p f).F₀ :=
        (TIFacts.wreathedSetting_C_eq n hn S e p f).symm
    _ ≤ oddCoreIn (wreathedSetting n S e p f).C ⊔ (wreathedSetting n S e p f).D :=
        sup_le_sup_left inf_le_left _

end CFSG.Wreathed.OriginalAllPrime.IVFacts
