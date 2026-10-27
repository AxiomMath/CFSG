module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeProfile
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.Principal

variable {G : Type*} [Group G]

theorem exists_mulEquiv_sup_of_commute {H₁ H₂ : Subgroup G}
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) (hdisj : H₁ ⊓ H₂ = ⊥) :
    ∃ e : (H₁ × H₂) ≃* (H₁ ⊔ H₂ : Subgroup G), ∀ p, (e p : G) = p.1 * p.2 := by
  have hc : ∀ (x : H₁) (y : H₂), Commute (H₁.subtype x) (H₂.subtype y) :=
    fun x y => hcomm x x.2 y y.2
  have hf : Function.Injective (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H₁.subtype_injective, H₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hdisj
  have hrange : (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc).range = H₁ ⊔ H₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange), fun p => rfl⟩

theorem nonempty_closure_mulEquiv_dihedralGroup_three [Finite G] {ρ σ : G} (hρ : orderOf ρ = 3)
    (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ Subgroup.zpowers ρ) :
    Nonempty (Subgroup.closure {ρ, σ} ≃* DihedralGroup 3) := by
  set H := Subgroup.closure ({ρ, σ} : Set G)
  have hρH : ρ ∈ H := Subgroup.subset_closure (by simp)
  have hσH : σ ∈ H := Subgroup.subset_closure (by simp)
  have hgen : (⊤ : Subgroup H) = Subgroup.zpowers ⟨ρ, hρH⟩ ⊔ Subgroup.zpowers ⟨σ, hσH⟩ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, ← Subgroup.closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (D := H) ⟨ρ, hρH⟩ ⟨σ, hσH⟩
    hgen (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ (by
      have := (Subgroup.mem_zpowers_iff).mp hmem
      obtain ⟨k, hk⟩ := this
      exact (Subgroup.mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk, hρ] at h

theorem nonempty_perm_three_mulEquiv_dihedralGroup_three :
    Nonempty (Equiv.Perm (Fin 3) ≃* DihedralGroup 3) := by
  have hρ : orderOf (finRotate 3) = 3 := orderOf_eq_prime (by decide) (by decide)
  have hσ : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hgen : (⊤ : Subgroup (Equiv.Perm (Fin 3))) =
      Subgroup.zpowers (finRotate 3) ⊔ Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
    have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 1))
      (support_finRotate (n := 1)) 0
    exact h.symm
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (finRotate 3)
    (Equiv.swap (0 : Fin 3) 1) hgen (by decide) (by decide) (fun hmem => by
      have hdvd := orderOf_dvd_of_mem_zpowers hmem
      rw [hρ, hσ] at hdvd
      norm_num at hdvd)
  rwa [hρ] at h

theorem orderOf_eq_six_iff {x : G} : orderOf x = 6 ↔ x ^ 6 = 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1 := by
  constructor
  · intro h
    refine ⟨by rw [← h, pow_orderOf_eq_one], fun h2 => ?_, fun h3 => ?_⟩
    · have := orderOf_dvd_of_pow_eq_one h2
      rw [h] at this
      norm_num at this
    · have := orderOf_dvd_of_pow_eq_one h3
      rw [h] at this
      norm_num at this
  · rintro ⟨h6, h2, h3⟩
    have hdvd := orderOf_dvd_of_pow_eq_one h6
    have h1 : orderOf x ≠ 1 := fun h => h2 (by rw [orderOf_eq_one_iff.mp h, one_pow])
    have h2' : orderOf x ≠ 2 := fun h => h2 (by rw [← h, pow_orderOf_eq_one])
    have h3' : orderOf x ≠ 3 := fun h => h3 (by rw [← h, pow_orderOf_eq_one])
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf x <;> omega

theorem card_orderOf_eq_of_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂)
    (k : ℕ) : Nat.card {x : H₁ // orderOf x = k} = Nat.card {x : H₂ // orderOf x = k} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change orderOf x = k ↔ orderOf (e x) = k
    rw [MulEquiv.orderOf_eq])

theorem card_orderOf_eq_two_eq_fintype_card {H : Type*} [Group H] [Fintype H] [DecidableEq H] :
    Nat.card {x : H // orderOf x = 2} = Fintype.card {x : H // x ^ 2 = 1 ∧ x ≠ 1} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => orderOf_eq_prime_iff),
    Nat.card_eq_fintype_card]

theorem card_orderOf_eq_three_eq_fintype_card {H : Type*} [Group H] [Fintype H] [DecidableEq H] :
    Nat.card {x : H // orderOf x = 3} = Fintype.card {x : H // x ^ 3 = 1 ∧ x ≠ 1} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => orderOf_eq_prime_iff),
    Nat.card_eq_fintype_card]

theorem card_orderOf_eq_six_eq_fintype_card {H : Type*} [Group H] [Fintype H] [DecidableEq H] :
    Nat.card {x : H // orderOf x = 6} =
      Fintype.card {x : H // x ^ 6 = 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1} := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => orderOf_eq_six_iff),
    Nat.card_eq_fintype_card]

example : Nat.card {x : DihedralGroup 3 × DihedralGroup 3 // orderOf x = 3} = 8 := by
  rw [card_orderOf_eq_three_eq_fintype_card]; decide
example : Nat.card {x : DihedralGroup 3 × Multiplicative (ZMod 2) // orderOf x = 2} = 7 := by
  rw [card_orderOf_eq_two_eq_fintype_card]; decide
example : Nat.card {x : DihedralGroup 3 × Multiplicative (ZMod 2) // orderOf x = 6} = 2 := by
  rw [card_orderOf_eq_six_eq_fintype_card]; decide

theorem card_orderOf_two_dihedralGroup_three_prod :
    Nat.card {x : DihedralGroup 3 × DihedralGroup 3 // orderOf x = 2} = 15 := by
  rw [card_orderOf_eq_two_eq_fintype_card]; decide

theorem card_orderOf_three_dihedralGroup_three_prod :
    Nat.card {x : DihedralGroup 3 × DihedralGroup 3 // orderOf x = 3} = 8 := by
  rw [card_orderOf_eq_three_eq_fintype_card]; decide

theorem card_orderOf_six_dihedralGroup_three_prod :
    Nat.card {x : DihedralGroup 3 × DihedralGroup 3 // orderOf x = 6} = 12 := by
  rw [card_orderOf_eq_six_eq_fintype_card]; decide

theorem card_orderOf_two_dihedralGroup_three_prod_two :
    Nat.card {x : DihedralGroup 3 × Multiplicative (ZMod 2) // orderOf x = 2} = 7 := by
  rw [card_orderOf_eq_two_eq_fintype_card]; decide

theorem card_orderOf_three_dihedralGroup_three_prod_two :
    Nat.card {x : DihedralGroup 3 × Multiplicative (ZMod 2) // orderOf x = 3} = 2 := by
  rw [card_orderOf_eq_three_eq_fintype_card]; decide

theorem card_orderOf_six_dihedralGroup_three_prod_two :
    Nat.card {x : DihedralGroup 3 × Multiplicative (ZMod 2) // orderOf x = 6} = 2 := by
  rw [card_orderOf_eq_six_eq_fintype_card]; decide

theorem dihedralGroup_three_eq_one_of_forall_commute :
    ∀ x : DihedralGroup 3, (∀ y : DihedralGroup 3, x * y = y * x) → x = 1 := by decide

theorem dihedralGroup_three_centralizer_involution :
    ∀ s : DihedralGroup 3, s ≠ 1 → s ^ 2 = 1 → ∀ y : DihedralGroup 3, y * s = s * y →
      y = 1 ∨ y = s := by decide

theorem three_centralizer_produces_two_S3_local_subgroups [Finite G] (t : G) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer {t} ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (a : G) (haC : a ∈ Subgroup.centralizer {t}) (ha : orderOf a = 3)
    (hCa : Nat.card (Subgroup.centralizer {a}) = 54) (P : Subgroup G)
    (hPa : P ≤ Subgroup.centralizer {a}) (hP : Nat.card P = 27) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    (∀ Q : Subgroup G, Q ≤ Subgroup.centralizer {a} → Nat.card Q = 27 → Q = P) ∧
    ∃ b l : G, orderOf b = 2 ∧ Commute t b ∧ l ∈ P ∧ orderOf l = 3 ∧
      Nat.card (Subgroup.closure {a, l}) = 9 ∧ IsMulCommutative (Subgroup.closure {a, l}) ∧
      (∀ x ∈ Subgroup.closure {a, l}, x ^ 3 = 1) ∧
      t * a * t⁻¹ = a ∧ t * l * t⁻¹ = l⁻¹ ∧ b * a * b⁻¹ = a⁻¹ ∧ b * l * b⁻¹ = l ∧
      (∃ e : (Subgroup.closure {a, b} × Subgroup.closure {l, t}) ≃*
          (Subgroup.closure {a, l, t, b} : Subgroup G), ∀ x, (e x : G) = x.1 * x.2) ∧
      Nonempty (Subgroup.closure {a, b} ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Subgroup.closure {l, t} ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Subgroup.closure {a, l, t, b} ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      Nat.card (Subgroup.closure {a, l, t, b}) = 36 ∧
      Subgroup.closure {a, l, t, b} ⊓ Subgroup.centralizer {t} = Subgroup.closure {a, b, t} ∧
      Nonempty (Subgroup.closure {a, b, t} ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) ∧
      Nat.card (Subgroup.closure {a, b, t}) = 12 ∧
      Nat.card {x : Subgroup.closure {a, l, t, b} // orderOf x = 2} = 15 ∧
      Nat.card {x : Subgroup.closure {a, l, t, b} // orderOf x = 3} = 8 ∧
      Nat.card {x : Subgroup.closure {a, l, t, b} // orderOf x = 6} = 12 ∧
      Nat.card {x : Subgroup.closure {a, b, t} // orderOf x = 2} = 7 ∧
      Nat.card {x : Subgroup.closure {a, b, t} // orderOf x = 3} = 2 ∧
      Nat.card {x : Subgroup.closure {a, b, t} // orderOf x = 6} = 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hC
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  have hprof := CFSG.Semidihedral.Principal.GL2_three_element_profile_and_derived_subgroup
  dsimp only at hprof
  obtain ⟨hH48, hz2, -, hZH, -, -, -, -, -, -, -, -, -, -, -, -, hinvert⟩ := hprof
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hmemC : ∀ g : G, g ∈ C ↔ t * g = g * t := by
    intro g
    rw [hCdef, Subgroup.mem_centralizer_iff]
    simp
  have htC : t ∈ C := (hmemC t).mpr rfl
  have hCcard : Nat.card C = 48 := by rw [Nat.card_congr φ.toEquiv, hH48]
  have hCdvd : ∀ X : Subgroup G, X ≤ C → Nat.card X ∣ 48 := fun X hX => by
    rw [← hCcard]
    exact Subgroup.card_dvd_of_le hX
  have hφt : φ ⟨t, htC⟩ = -1 := by
    have hcent : φ ⟨t, htC⟩ ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨c, rfl⟩ := φ.surjective h
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact ((hmemC c).mp c.2).symm
    rw [hZH] at hcent
    obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hcent)
    rw [hz2, Finset.mem_range] at hk
    interval_cases k
    · exfalso
      rw [pow_zero] at hkt
      apply ht1
      have := congrArg Subtype.val (φ.injective (hkt.symm.trans (map_one φ).symm))
      exact this
    · rw [pow_one] at hkt
      exact hkt.symm
  obtain ⟨b', hb'2, hb'z, hb'a, -⟩ := hinvert (φ ⟨a, haC⟩) (by rw [MulEquiv.orderOf_eq,
    Subgroup.orderOf_mk, ha])
  set b₀ : G := ((φ.symm b' : C) : G) with hb₀
  have hb₀C : b₀ ∈ C := (φ.symm b').2
  have hb₀2 : orderOf b₀ = 2 := by
    rw [hb₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb'2]
  have hb₀a : b₀ * a * b₀⁻¹ = a⁻¹ := by
    have h := congrArg (fun g => ((φ.symm g : C) : G)) hb'a
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    exact h
  have hb₀t : b₀ ≠ t := by
    intro h
    apply hb'z
    have : φ.symm b' = ⟨t, htC⟩ := Subtype.ext h
    rw [← φ.apply_symm_apply b', this, hφt]
    exact Subgroup.mem_zpowers _
  have hb₀comm : t * b₀ = b₀ * t := (hmemC b₀).mp hb₀C
  have hb₀sq : b₀ * b₀ = 1 := by rw [← sq, ← hb₀2, pow_orderOf_eq_one]
  have htsq : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hat : t * a = a * t := (hmemC a).mp haC
  have hmemCa : ∀ g : G, g ∈ Subgroup.centralizer ({a} : Set G) ↔ a * g = g * a := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hCaN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have hidx : (P.subgroupOf (Subgroup.centralizer ({a} : Set G))).index = 2 := by
      have h := (P.subgroupOf (Subgroup.centralizer ({a} : Set G))).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPa).toEquiv, hP, hCa] at h
      omega
    have := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPa).mp this
  have hsyl : ∀ X : Subgroup G, X ≤ Subgroup.centralizer ({a} : Set G) → IsPGroup 3 X →
      X ≤ P := by
    intro X hX hX3
    have hXP : IsPGroup 3 (X ⊔ P : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hX3 hP3 (le_trans hX hCaN)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hXP
    have hdvd : Nat.card (X ⊔ P : Subgroup G) ∣ 54 := by
      rw [← hCa]
      exact Subgroup.card_dvd_of_le (sup_le hX hPa)
    have hle : 27 ≤ Nat.card (X ⊔ P : Subgroup G) := by
      rw [← hP]
      exact Subgroup.card_le_of_le le_sup_right
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 3 ^ 4 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      rw [← hk] at this
      have := Nat.dvd_trans this hdvd
      norm_num at this
    have hcard : Nat.card (X ⊔ P : Subgroup G) = 27 := by
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      rw [hk] at hle ⊢
      norm_num at this
      omega
    have heq : P = X ⊔ P := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcard, hP])
    rw [heq]
    exact le_sup_left
  have huniq : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer {a} → Nat.card Q = 27 → Q = P := by
    intro Q hQ hQ27
    have hle := hsyl Q hQ (IsPGroup.of_card (n := 3) (by rw [hQ27]; norm_num))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hQ27])
  have haP : a ∈ P := by
    have h := hsyl (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr ((hmemCa a).mpr rfl))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one]))
    exact h (Subgroup.mem_zpowers a)
  have hPcomm : ∀ x ∈ P, a * x = x * a := fun x hx => (hmemCa x).mp (hPa hx)
  have htN : t ∈ Subgroup.normalizer (P : Set G) := hCaN ((hmemCa t).mpr hat.symm)
  have hb₀N : b₀ ∈ Subgroup.normalizer (P : Set G) := by
    have hle : P.map (MulAut.conj b₀).toMonoidHom ≤ Subgroup.centralizer ({a} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hmemCa]
      have hxa : Commute a x := hPcomm x hx
      have hb₀a' : b₀ * a⁻¹ * b₀⁻¹ = a := by
        have := congrArg (·⁻¹) hb₀a
        simpa [mul_assoc] using this
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc a * (b₀ * x * b₀⁻¹) = (b₀ * a⁻¹ * b₀⁻¹) * (b₀ * x * b₀⁻¹) := by rw [hb₀a']
        _ = b₀ * (a⁻¹ * x) * b₀⁻¹ := by group
        _ = b₀ * (x * a⁻¹) * b₀⁻¹ := by rw [hxa.inv_left.eq]
        _ = (b₀ * x * b₀⁻¹) * (b₀ * a⁻¹ * b₀⁻¹) := by group
        _ = (b₀ * x * b₀⁻¹) * a := by rw [hb₀a']
    have heq := huniq _ hle (by rw [Subgroup.card_map_of_injective (MulAut.conj b₀).injective, hP])
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← heq]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', hhh⟩ := hh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
        mul_right_inj] at hhh
      rwa [← hhh]
  set Z := Subgroup.zpowers a with hZ
  have hZP : Z ≤ P := Subgroup.zpowers_le.mpr haP
  have hZcard : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, ha]
  have hZcomm : ∀ z ∈ Z, ∀ x ∈ P, z * x = x * z := by
    intro z hz x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (hPcomm x hx) k).eq
  have hF1 : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    let N := Z.subgroupOf P
    have hNnormal : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hcomm : (g : G) * n = n * g := (hZcomm n hn g g.2).symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
    have hNcard : Nat.card N = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZcard]
    have hQcard : Nat.card (P ⧸ N) = 3 ^ 2 := by
      have h := N.card_mul_index
      rw [hNcard, hP] at h
      change N.index = 3 ^ 2
      omega
    have hQcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
    intro x hx y hy
    have h := hQcomm.is_comm.comm (QuotientGroup.mk ⟨y⁻¹, P.inv_mem hy⟩ : P ⧸ N)
      (QuotientGroup.mk ⟨x⁻¹, P.inv_mem hx⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa [mul_assoc] using h
  have hZt : ∀ z ∈ Z, t * z * t⁻¹ = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hat, mul_inv_cancel_right]
  have hZ2 : ∀ z ∈ Z, z * z = 1 → z = 1 := by
    intro z hz h2
    have h3 : z ^ 3 = 1 := hexp z (hZP hz)
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have htt : ∀ z : G, t * (t * z * t⁻¹) * t⁻¹ = z := by
    intro z
    calc t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t * t)⁻¹ := by group
      _ = z := by rw [htsq]; group
  have hbb : ∀ z : G, b₀ * (b₀ * z * b₀⁻¹) * b₀⁻¹ = z := by
    intro z
    calc b₀ * (b₀ * z * b₀⁻¹) * b₀⁻¹ = (b₀ * b₀) * z * (b₀ * b₀)⁻¹ := by group
      _ = z := by rw [hb₀sq]; group
  have hbt : ∀ z : G, b₀ * (t * z * t⁻¹) * b₀⁻¹ = t * (b₀ * z * b₀⁻¹) * t⁻¹ := by
    intro z
    have h' : b₀ * t = t * b₀ := hb₀comm.symm
    calc b₀ * (t * z * t⁻¹) * b₀⁻¹ = (b₀ * t) * z * (b₀ * t)⁻¹ := by group
      _ = (t * b₀) * z * (t * b₀)⁻¹ := by rw [h']
      _ = t * (b₀ * z * b₀⁻¹) * t⁻¹ := by group
  have htP : ∀ z ∈ P, t * z * t⁻¹ ∈ P := fun z hz => (Subgroup.mem_normalizer_iff.mp htN z).mp hz
  have hb₀P : ∀ z ∈ P, b₀ * z * b₀⁻¹ ∈ P :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp hb₀N z).mp hz
  have hfix : ∀ y ∈ P, t * y * t⁻¹ * y⁻¹ ∈ Z → y ∈ Z := by
    intro y hy hc
    set c := t * y * t⁻¹ * y⁻¹ with hcdef
    have htyc : t * y * t⁻¹ = c * y := by rw [hcdef]; group
    have hcc : c * c = 1 := by
      have h : 1 * y = c * c * y := by
        calc 1 * y = t * (t * y * t⁻¹) * t⁻¹ := by rw [htt, one_mul]
          _ = t * (c * y) * t⁻¹ := by rw [htyc]
          _ = (t * c * t⁻¹) * (t * y * t⁻¹) := by group
          _ = c * (c * y) := by rw [hZt c hc, htyc]
          _ = c * c * y := by group
      exact (mul_right_cancel h).symm
    have hc1 := hZ2 c hc hcc
    have hty : t * y = y * t := by
      have h : t * y * t⁻¹ = y := by rw [htyc, hc1, one_mul]
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = y * t := by rw [h]
    by_contra hyZ
    have hX : Z ⊔ Subgroup.zpowers y ≤ C :=
      sup_le (Subgroup.zpowers_le.mpr haC) (Subgroup.zpowers_le.mpr ((hmemC y).mpr hty))
    have hXP : Z ⊔ Subgroup.zpowers y ≤ P := sup_le hZP (Subgroup.zpowers_le.mpr hy)
    have hd1 := hCdvd _ hX
    have hd2 : Nat.card (Z ⊔ Subgroup.zpowers y : Subgroup G) ∣ 27 :=
      hP ▸ Subgroup.card_dvd_of_le hXP
    have hd3 : Nat.card (Z ⊔ Subgroup.zpowers y : Subgroup G) ∣ 3 := by
      have := Nat.dvd_gcd hd1 hd2
      norm_num at this
      exact this
    have hle := Nat.le_of_dvd (by norm_num) hd3
    have heq : Z = Z ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hZcard]; exact hle)
    exact hyZ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  obtain ⟨x, hxP, hxZ⟩ : ∃ x ∈ P, x ∉ Z := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show P ≤ Z from fun x hx => h x hx)
    rw [hP, hZcard] at this
    omega
  have hxbP : b₀ * x * b₀⁻¹ ∈ P := hb₀P x hxP
  obtain ⟨y, hyP, hyZ, hyb⟩ : ∃ y ∈ P, y ∉ Z ∧
      (b₀ * y * b₀⁻¹ * y⁻¹ ∈ Z ∨ b₀ * y * b₀⁻¹ = y⁻¹) := by
    by_cases hp : x * (b₀ * x * b₀⁻¹) ∈ Z
    · by_cases hm : x * (b₀ * x * b₀⁻¹)⁻¹ ∈ Z
      · exfalso
        have hcomm := hF1 x⁻¹ (P.inv_mem hxP) _ hxbP
        have hx2 : x * x ∈ Z := by
          have h := Z.mul_mem (Z.mul_mem hp hm) (Z.inv_mem hcomm)
          have he : x * (b₀ * x * b₀⁻¹) * (x * (b₀ * x * b₀⁻¹)⁻¹) *
              (x⁻¹ * (b₀ * x * b₀⁻¹) * x⁻¹⁻¹ * (b₀ * x * b₀⁻¹)⁻¹)⁻¹ = x * x := by group
          rwa [he] at h
        have hx3 : x ^ 3 = 1 := hexp x hxP
        apply hxZ
        have h4 : x = (x * x) * (x * x) := by
          calc x = x ^ 3 * x := by rw [hx3, one_mul]
            _ = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [h4]
        exact Z.mul_mem hx2 hx2
      · refine ⟨x * (b₀ * x * b₀⁻¹)⁻¹, P.mul_mem hxP (P.inv_mem hxbP), hm, Or.inr ?_⟩
        have h := hbb x
        calc b₀ * (x * (b₀ * x * b₀⁻¹)⁻¹) * b₀⁻¹
            = (b₀ * x * b₀⁻¹) * (b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹)⁻¹ := by group
          _ = (b₀ * x * b₀⁻¹) * x⁻¹ := by rw [h]
          _ = (x * (b₀ * x * b₀⁻¹)⁻¹)⁻¹ := by group
    · refine ⟨x * (b₀ * x * b₀⁻¹), P.mul_mem hxP hxbP, hp, Or.inl ?_⟩
      have h := hbb x
      have hc := hF1 _ hxbP x hxP
      have he : b₀ * (x * (b₀ * x * b₀⁻¹)) * b₀⁻¹ * (x * (b₀ * x * b₀⁻¹))⁻¹ =
          (b₀ * x * b₀⁻¹) * x * (b₀ * x * b₀⁻¹)⁻¹ * x⁻¹ := by
        calc b₀ * (x * (b₀ * x * b₀⁻¹)) * b₀⁻¹ * (x * (b₀ * x * b₀⁻¹))⁻¹
            = (b₀ * x * b₀⁻¹) * (b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹) * (x * (b₀ * x * b₀⁻¹))⁻¹ := by
              group
          _ = (b₀ * x * b₀⁻¹) * x * (x * (b₀ * x * b₀⁻¹))⁻¹ := by rw [h]
          _ = (b₀ * x * b₀⁻¹) * x * (b₀ * x * b₀⁻¹)⁻¹ * x⁻¹ := by group
      rw [he]
      exact hc
  set l := y * (t * y * t⁻¹)⁻¹ with hl
  have hlP : l ∈ P := P.mul_mem hyP (P.inv_mem (htP y hyP))
  have htl : t * l * t⁻¹ = l⁻¹ := by
    rw [hl]
    calc t * (y * (t * y * t⁻¹)⁻¹) * t⁻¹ =
        (t * y * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹)⁻¹ := by group
      _ = (t * y * t⁻¹) * y⁻¹ := by rw [htt]
      _ = (y * (t * y * t⁻¹)⁻¹)⁻¹ := by group
  have hlZ : l ∉ Z := by
    intro h
    apply hyZ
    apply hfix y hyP
    have he : t * y * t⁻¹ * y⁻¹ = l⁻¹ := by rw [hl]; group
    rw [he]
    exact Z.inv_mem h
  have hbl : b₀ * l * b₀⁻¹ = l ∨ b₀ * l * b₀⁻¹ = l⁻¹ := by
    have hsplit : b₀ * l * b₀⁻¹ = (b₀ * y * b₀⁻¹) * (t * (b₀ * y * b₀⁻¹) * t⁻¹)⁻¹ := by
      calc b₀ * l * b₀⁻¹ = (b₀ * y * b₀⁻¹) * (b₀ * (t * y * t⁻¹) * b₀⁻¹)⁻¹ := by
            rw [hl]; group
        _ = (b₀ * y * b₀⁻¹) * (t * (b₀ * y * b₀⁻¹) * t⁻¹)⁻¹ := by rw [hbt]
    rcases hyb with hA | hB
    · left
      set c := b₀ * y * b₀⁻¹ * y⁻¹ with hcdef
      have hbyc : b₀ * y * b₀⁻¹ = c * y := by rw [hcdef]; group
      calc b₀ * l * b₀⁻¹ = (c * y) * (t * (c * y) * t⁻¹)⁻¹ := by rw [hsplit, hbyc]
        _ = (c * y) * ((t * c * t⁻¹) * (t * y * t⁻¹))⁻¹ := by group
        _ = (c * y) * (c * (t * y * t⁻¹))⁻¹ := by rw [hZt c hA]
        _ = c * l * c⁻¹ := by rw [hl]; group
        _ = l := by rw [hZcomm c hA l hlP]; group
    · right
      have hbl' : b₀ * l * b₀⁻¹ = y⁻¹ * (t * y * t⁻¹) := by
        rw [hsplit, hB]
        group
      set w := b₀ * l * b₀⁻¹ * l with hwdef
      have hwZ : w ∈ Z := by
        have h := hF1 y⁻¹ (P.inv_mem hyP) _ (htP y hyP)
        have he : w = y⁻¹ * (t * y * t⁻¹) * y⁻¹⁻¹ * (t * y * t⁻¹)⁻¹ := by
          rw [hwdef, hbl', hl]
          group
        rw [he]
        exact h
      have hwl : b₀ * l * b₀⁻¹ = w * l⁻¹ := by rw [hwdef]; group
      have htw : t * w * t⁻¹ = w⁻¹ := by
        have h1 : t * (b₀ * l * b₀⁻¹) * t⁻¹ = (b₀ * l * b₀⁻¹)⁻¹ := by
          rw [← hbt, htl]
          group
        calc t * w * t⁻¹ = (t * (b₀ * l * b₀⁻¹) * t⁻¹) * (t * l * t⁻¹) := by rw [hwdef]; group
          _ = (b₀ * l * b₀⁻¹)⁻¹ * l⁻¹ := by rw [h1, htl]
          _ = (l * (b₀ * l * b₀⁻¹))⁻¹ := by group
          _ = (l * (w * l⁻¹))⁻¹ := by rw [hwl]
          _ = (w * l * l⁻¹)⁻¹ := by rw [← mul_assoc, ← hZcomm w hwZ l hlP]
          _ = w⁻¹ := by group
      have hw1 : w = 1 := by
        have h := hZt w hwZ
        rw [htw] at h
        apply hZ2 w hwZ
        calc w * w = w * w⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel w
      rw [hwl, hw1, one_mul]
  obtain ⟨b, hb2, hbtc, hba, hblb⟩ : ∃ b : G, orderOf b = 2 ∧ Commute t b ∧
      b * a * b⁻¹ = a⁻¹ ∧ b * l * b⁻¹ = l := by
    rcases hbl with h | h
    · exact ⟨b₀, hb₀2, hb₀comm, hb₀a, h⟩
    · refine ⟨t * b₀, ?_, (Commute.refl t).mul_right hb₀comm, ?_, ?_⟩
      · apply orderOf_eq_prime
        · calc (t * b₀) ^ 2 = t * (b₀ * t) * b₀ := by rw [sq]; group
            _ = t * (t * b₀) * b₀ := by rw [← hb₀comm]
            _ = (t * t) * (b₀ * b₀) := by group
            _ = 1 := by rw [htsq, hb₀sq, one_mul]
        · intro h1
          apply hb₀t
          calc b₀ = t⁻¹ * (t * b₀) := by group
            _ = t := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right htsq]
      · calc t * b₀ * a * (t * b₀)⁻¹ = t * (b₀ * a * b₀⁻¹) * t⁻¹ := by group
          _ = t * a⁻¹ * t⁻¹ := by rw [hb₀a]
          _ = a⁻¹ := hZt a⁻¹ (Z.inv_mem (Subgroup.mem_zpowers a))
      · calc t * b₀ * l * (t * b₀)⁻¹ = t * (b₀ * l * b₀⁻¹) * t⁻¹ := by group
          _ = t * l⁻¹ * t⁻¹ := by rw [h]
          _ = (t * l * t⁻¹)⁻¹ := by group
          _ = l := by rw [htl, inv_inv]
  have hl3 : orderOf l = 3 := orderOf_eq_prime (hexp l hlP) (fun h => hlZ (h ▸ Z.one_mem))
  have hal : a * l = l * a := hPcomm l hlP
  have hta : t * a * t⁻¹ = a := hZt a (Subgroup.mem_zpowers a)
  have hbl' : b * l = l * b := by
    calc b * l = (b * l * b⁻¹) * b := by group
      _ = l * b := by rw [hblb]
  have hU : Subgroup.closure ({a, l} : Set G) = Z ⊔ Subgroup.zpowers l := by
    rw [hZ, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hZl : Z ⊓ Subgroup.zpowers l = ⊥ := by
    have hdvd : Nat.card (Z ⊓ Subgroup.zpowers l : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Z ⊓ Subgroup.zpowers l ≤ _)
      rwa [Nat.card_zpowers, hl3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers l = Subgroup.zpowers l :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hl3])
      exact hlZ (heq ▸ (Subgroup.mem_zpowers l) |>.1)
  obtain ⟨eU, -⟩ := exists_mulEquiv_sup_of_commute (H₁ := Z) (H₂ := Subgroup.zpowers l)
    (fun x hx y hy => hZcomm x hx y (Subgroup.zpowers_le.mpr hlP hy)) hZl
  have hUcard : Nat.card (Subgroup.closure ({a, l} : Set G)) = 9 := by
    rw [hU, ← Nat.card_congr eU.toEquiv, Nat.card_prod, hZcard, Nat.card_zpowers, hl3]
  have hUcomm : IsMulCommutative (Subgroup.closure ({a, l} : Set G)) := by
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [Commute.refl _, hal, hal.symm, Commute.refl _]
  have hUexp : ∀ x ∈ Subgroup.closure ({a, l} : Set G), x ^ 3 = 1 := by
    have hle : Subgroup.closure ({a, l} : Set G) ≤ P := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      exacts [haP, hlP]
    exact fun x hx => hexp x (hle hx)
  have hb2' : b ^ 2 = 1 := by rw [← hb2, pow_orderOf_eq_one]
  have ht2' : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hbnot : b ∉ Subgroup.zpowers a := fun h => by
    have := orderOf_dvd_of_mem_zpowers h
    rw [hb2, ha] at this
    norm_num at this
  have htnot : t ∉ Subgroup.zpowers l := fun h => by
    have := orderOf_dvd_of_mem_zpowers h
    rw [ht, hl3] at this
    norm_num at this
  obtain ⟨ψ₁⟩ := nonempty_closure_mulEquiv_dihedralGroup_three ha hb2' hba hbnot
  obtain ⟨ψ₂⟩ := nonempty_closure_mulEquiv_dihedralGroup_three hl3 ht2' htl htnot
  obtain ⟨θ⟩ := nonempty_perm_three_mulEquiv_dihedralGroup_three
  obtain ⟨A₁, hA₁⟩ : ∃ A : Subgroup G, A = Subgroup.closure ({a, b} : Set G) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : Subgroup G, A = Subgroup.closure ({l, t} : Set G) := ⟨_, rfl⟩
  rw [← hA₁] at ψ₁
  rw [← hA₂] at ψ₂
  have hcentA : ∀ (S : Set G) (g : G), (∀ h ∈ S, h * g = g * h) →
      ∀ h ∈ Subgroup.closure S, h * g = g * h := by
    intro S g hS h hh
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro k hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g' hg'
      rw [Set.mem_singleton_iff] at hg'
      subst hg'
      exact (hS k hk).symm
    have := Subgroup.mem_centralizer_iff.mp (hle hh) g rfl
    exact this.symm
  have hgen : ∀ g ∈ ({a, b} : Set G), ∀ h ∈ ({l, t} : Set G), h * g = g * h := by
    intro g hg h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
    · exact hal.symm
    · exact hat
    · exact hbl'.symm
    · exact hbtc.eq
  have hcomm12 : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y := by
    intro x hx y hy
    rw [hA₁] at hx
    rw [hA₂] at hy
    have hy' : ∀ g ∈ ({a, b} : Set G), g * y = y * g := fun g hg =>
      (hcentA ({l, t} : Set G) g (hgen g hg) y hy).symm
    exact hcentA ({a, b} : Set G) y hy' x hx
  have hψcent : ∀ x : A₁, (∀ y : A₁, x * y = y * x) → x = 1 := by
    intro x hx
    apply ψ₁.injective
    rw [map_one]
    apply dihedralGroup_three_eq_one_of_forall_commute
    intro d
    obtain ⟨y, rfl⟩ := ψ₁.surjective d
    rw [← map_mul, ← map_mul, hx y]
  have hdisj12 : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hψcent ⟨x, hx.1⟩ (fun y => Subtype.ext (hcomm12 y y.2 x hx.2).symm)
    exact congrArg Subtype.val h
  obtain ⟨eM, heM⟩ := exists_mulEquiv_sup_of_commute hcomm12 hdisj12
  have hMsup : Subgroup.closure ({a, l, t, b} : Set G) = A₁ ⊔ A₂ := by
    rw [hA₁, hA₂, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)
    · rintro ((h | h) | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  let e : (A₁ × A₂) ≃* (Subgroup.closure ({a, l, t, b} : Set G) : Subgroup G) :=
    eM.trans (MulEquiv.subgroupCongr hMsup.symm)
  have he : ∀ x, (e x : G) = x.1 * x.2 := fun x => heM x
  have hA₁card : Nat.card A₁ = 6 := by
    rw [Nat.card_congr ψ₁.toEquiv, DihedralGroup.nat_card]
  have hA₂card : Nat.card A₂ = 6 := by
    rw [Nat.card_congr ψ₂.toEquiv, DihedralGroup.nat_card]
  let eD : (Subgroup.closure ({a, l, t, b} : Set G) : Subgroup G) ≃*
      DihedralGroup 3 × DihedralGroup 3 := e.symm.trans (ψ₁.prodCongr ψ₂)
  have hMcard : Nat.card (Subgroup.closure ({a, l, t, b} : Set G)) = 36 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hA₁card, hA₂card]
  have hM2 : Nat.card {x : Subgroup.closure ({a, l, t, b} : Set G) // orderOf x = 2} = 15 := by
    rw [card_orderOf_eq_of_mulEquiv eD]
    exact card_orderOf_two_dihedralGroup_three_prod
  have hM3 : Nat.card {x : Subgroup.closure ({a, l, t, b} : Set G) // orderOf x = 3} = 8 := by
    rw [card_orderOf_eq_of_mulEquiv eD]
    exact card_orderOf_three_dihedralGroup_three_prod
  have hM6 : Nat.card {x : Subgroup.closure ({a, l, t, b} : Set G) // orderOf x = 6} = 12 := by
    rw [card_orderOf_eq_of_mulEquiv eD]
    exact card_orderOf_six_dihedralGroup_three_prod
  have htA₂ : t ∈ A₂ := hA₂ ▸ Subgroup.subset_closure (by simp)
  have hA₁t : ∀ x ∈ A₁, x * t = t * x := fun x hx => hcomm12 x hx t htA₂
  have hcommT : ∀ x ∈ A₁, ∀ y ∈ Subgroup.zpowers t, Commute x y := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_right (hA₁t x hx) k
  have hdisjT : A₁ ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hψcent ⟨x, hx.1⟩ (fun y => Subtype.ext (hcommT y y.2 x hx.2).symm)
    exact congrArg Subtype.val h
  obtain ⟨eT₀, heT₀⟩ := exists_mulEquiv_sup_of_commute hcommT hdisjT
  have hTsup : Subgroup.closure ({a, b, t} : Set G) = A₁ ⊔ Subgroup.zpowers t := by
    rw [hA₁, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    exact or_assoc.symm
  let eT : (A₁ × Subgroup.zpowers t) ≃* (Subgroup.closure ({a, b, t} : Set G) : Subgroup G) :=
    eT₀.trans (MulEquiv.subgroupCongr hTsup.symm)
  have htcard : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  let ζ : Subgroup.zpowers t ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq (by
    rw [htcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let eTD : (Subgroup.closure ({a, b, t} : Set G) : Subgroup G) ≃*
      DihedralGroup 3 × Multiplicative (ZMod 2) := eT.symm.trans (ψ₁.prodCongr ζ)
  have hTcard : Nat.card (Subgroup.closure ({a, b, t} : Set G)) = 12 := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, hA₁card, htcard]
  have hT2 : Nat.card {x : Subgroup.closure ({a, b, t} : Set G) // orderOf x = 2} = 7 := by
    rw [card_orderOf_eq_of_mulEquiv eTD]
    exact card_orderOf_two_dihedralGroup_three_prod_two
  have hT3 : Nat.card {x : Subgroup.closure ({a, b, t} : Set G) // orderOf x = 3} = 2 := by
    rw [card_orderOf_eq_of_mulEquiv eTD]
    exact card_orderOf_three_dihedralGroup_three_prod_two
  have hT6 : Nat.card {x : Subgroup.closure ({a, b, t} : Set G) // orderOf x = 6} = 2 := by
    rw [card_orderOf_eq_of_mulEquiv eTD]
    exact card_orderOf_six_dihedralGroup_three_prod_two
  have hA₁T : A₁ ≤ Subgroup.closure ({a, b, t} : Set G) := by
    rw [hA₁]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h
    exacts [Or.inl h, Or.inr (Or.inl h)]
  have htT : t ∈ Subgroup.closure ({a, b, t} : Set G) := Subgroup.subset_closure (by simp)
  have hMC : Subgroup.closure ({a, l, t, b} : Set G) ⊓ C =
      Subgroup.closure ({a, b, t} : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxM, hxC⟩
      have hxp : x = ((e.symm ⟨x, hxM⟩).1 : G) * (e.symm ⟨x, hxM⟩).2 := by
        have h := he (e.symm ⟨x, hxM⟩)
        rw [MulEquiv.apply_symm_apply] at h
        exact h
      set p := e.symm ⟨x, hxM⟩
      have hp2t : (p.2 : G) * t = t * p.2 := by
        have h1 : x * t = t * x := ((hmemC x).mp hxC).symm
        have h2 : (p.1 : G) * t = t * p.1 := hA₁t _ p.1.2
        rw [hxp] at h1
        calc (p.2 : G) * t = (p.1 : G)⁻¹ * ((p.1 : G) * p.2 * t) := by group
          _ = (p.1 : G)⁻¹ * (t * ((p.1 : G) * p.2)) := by rw [h1]
          _ = (p.1 : G)⁻¹ * ((t * p.1) * p.2) := by group
          _ = (p.1 : G)⁻¹ * ((p.1 * t) * p.2) := by rw [h2]
          _ = t * p.2 := by group
      have ht' : (⟨t, htA₂⟩ : A₂) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
      have hcases := dihedralGroup_three_centralizer_involution (ψ₂ ⟨t, htA₂⟩)
        (fun h => ht' (ψ₂.injective (h.trans (map_one ψ₂).symm)))
        (by rw [← map_pow]; rw [show (⟨t, htA₂⟩ : A₂) ^ 2 = 1 from Subtype.ext ht2', map_one])
        (ψ₂ p.2) (by rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hp2t)
      rcases hcases with h | h
      · have hp : p.2 = 1 := ψ₂.injective (h.trans (map_one ψ₂).symm)
        rw [hxp, hp, Subgroup.coe_one, mul_one]
        exact hA₁T p.1.2
      · have hp : p.2 = ⟨t, htA₂⟩ := ψ₂.injective h
        rw [hxp, hp]
        exact Subgroup.mul_mem _ (hA₁T p.1.2) htT
    · rw [Subgroup.closure_le]
      intro x hx
      have hxM : x ∈ Subgroup.closure ({a, l, t, b} : Set G) := by
        apply Subgroup.subset_closure
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
      refine ⟨hxM, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact haC
      · exact (hmemC _).mpr hbtc.eq
      · exact htC
  subst hA₁ hA₂
  exact ⟨huniq, b, l, hb2, hbtc, hlP, hl3, hUcard, hUcomm, hUexp, hta, htl, hba, hblb,
    ⟨e, he⟩, ⟨ψ₁.trans θ.symm⟩, ⟨ψ₂.trans θ.symm⟩, ⟨eD.trans (θ.symm.prodCongr θ.symm)⟩,
    hMcard, hMC, ⟨eT.symm.trans ((ψ₁.trans θ.symm).prodCongr ζ)⟩, hTcard, hM2, hM3, hM6, hT2,
    hT3, hT6⟩

end CFSG.Semidihedral.Principal
