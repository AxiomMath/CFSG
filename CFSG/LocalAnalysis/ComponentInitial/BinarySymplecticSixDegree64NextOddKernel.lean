module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextQuotient

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def symSix (u : Fin 6 → ZMod 2) : ↥(binarySymMatrices 3) :=
  ⟨!![u 0, u 3, u 4; u 3, u 1, u 5; u 4, u 5, u 2], by
    rw [mem_binarySymMatrices]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩

theorem symSix_add (u v : Fin 6 → ZMod 2) : symSix (u + v) = symSix u + symSix v :=
  Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)

theorem symSix_zero : symSix 0 = 0 :=
  Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)

theorem eq_zero_of_symSix_eq_zero {u : Fin 6 → ZMod 2} (h : symSix u = 0) : u = 0 := by
  have h' := fun i j => congrFun (congrFun (congrArg Subtype.val h) i) j
  funext k
  fin_cases k
  · exact h' 0 0
  · exact h' 1 1
  · exact h' 2 2
  · exact h' 0 1
  · exact h' 0 2
  · exact h' 1 2

theorem sum_single_six (u : Fin 6 → ZMod 2) :
    (Pi.single (0 : Fin 6) (u 0) : Fin 6 → ZMod 2) +
      (Pi.single (1 : Fin 6) (u 1) : Fin 6 → ZMod 2) +
      (Pi.single (2 : Fin 6) (u 2) : Fin 6 → ZMod 2) +
      (Pi.single (3 : Fin 6) (u 3) : Fin 6 → ZMod 2) +
      (Pi.single (4 : Fin 6) (u 4) : Fin 6 → ZMod 2) +
      (Pi.single (5 : Fin 6) (u 5) : Fin 6 → ZMod 2) = u := by
  funext k
  fin_cases k <;> simp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

include he hzC hz in
theorem degree64_next_jordan [Finite G] {D₂ C₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₂sq : ∀ c ∈ C₂, c ^ 2 = 1)
    (hνmul : ∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c')
    (hνk : ∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ 𝒜₂) (hνs : ∀ B : ↥(binarySymMatrices 3), ∃ c ∈ C₂, ν₂ c = B)
    (hC₂card : Nat.card C₂ = 4096) :
    ∃ Ψ : Multiplicative ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) ≃* C₂,
      (∀ u v, z * (Ψ (Multiplicative.ofAdd (u, v)) : G) * z⁻¹ =
        Ψ (Multiplicative.ofAdd (u, u + v))) ∧
      ∀ u v, (Ψ (Multiplicative.ofAdd (u, v)) : G) ∈ 𝒜₂ ↔ u = 0 := by
  classical
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hzN : z ∈ 𝒩₂ := le_normalizer hzR
  have hz1 : z * z = 1 := z_mul_self hz
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz1
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hC₂c : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x := fun x hx y hy =>
    comm_of_sq_eq_one hC₂sq hx hy
  have hτA : ∀ M : ↥(binarySymMatrices 3), tauHom φ he (Multiplicative.ofAdd M) ∈ 𝒜₂ :=
    fun M => (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hν1 : ν₂ 1 = 0 := by
    have h := hνmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact (add_eq_left.1 h.symm)
  have hzc : ∀ c ∈ C₂, z * c * z⁻¹ = c * tauHom φ he (Multiplicative.ofAdd (ν₂ c)) := by
    intro c hc
    rw [tauHom_nu he φ hzC hz hν₂z (hC₂D hc)]
    have h1 : z⁻¹ * c⁻¹ * z ∈ C₂ := by
      have h := hC₂n z⁻¹ (inv_mem hzN) c⁻¹ (inv_mem hc)
      rwa [inv_inv] at h
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hC₂sq c hc)
    calc z * c * z⁻¹ = z⁻¹ * c⁻¹ * z := by rw [hzinv, hcinv]
      _ = c * c * (z⁻¹ * c⁻¹ * z) := by rw [← sq, hC₂sq c hc, one_mul]
      _ = c * ((z⁻¹ * c⁻¹ * z) * c) := by rw [mul_assoc, hC₂c c hc _ h1]
      _ = c * (z⁻¹ * (c⁻¹ * z * c)) := by group
  choose cc hcc hccν using fun i : Fin 6 => hνs (symSix (Pi.single i 1))
  let _ : CommGroup C₂ :=
    { (inferInstance : Group C₂) with
      mul_comm := fun x y => Subtype.ext (hC₂c x x.2 y y.2) }
  set c : Fin 6 → C₂ := fun i => ⟨cc i, hcc i⟩ with hcdef
  have hc2 : ∀ i, c i ^ 2 = 1 := fun i => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hC₂sq _ (hcc i))
  let s : Multiplicative (Fin 6 → ZMod 2) →* C₂ :=
    { toFun := fun u => c 0 ^ (Multiplicative.toAdd u 0).val *
        c 1 ^ (Multiplicative.toAdd u 1).val *
        c 2 ^ (Multiplicative.toAdd u 2).val * c 3 ^ (Multiplicative.toAdd u 3).val *
        c 4 ^ (Multiplicative.toAdd u 4).val * c 5 ^ (Multiplicative.toAdd u 5).val
      map_one' := by
        simp only [toAdd_one, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
      map_mul' := fun u u' => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [pow_val_add_of_sq (hc2 0), pow_val_add_of_sq (hc2 1), pow_val_add_of_sq (hc2 2),
          pow_val_add_of_sq (hc2 3), pow_val_add_of_sq (hc2 4), pow_val_add_of_sq (hc2 5)]
        ac_rfl }
  have hs : ∀ u, (s u : G) = ((c 0 ^ (Multiplicative.toAdd u 0).val *
      c 1 ^ (Multiplicative.toAdd u 1).val * c 2 ^ (Multiplicative.toAdd u 2).val *
      c 3 ^ (Multiplicative.toAdd u 3).val * c 4 ^ (Multiplicative.toAdd u 4).val *
      c 5 ^ (Multiplicative.toAdd u 5).val : C₂) : G) := fun u => rfl
  let νH : C₂ →* Multiplicative ↥(binarySymMatrices 3) :=
    { toFun := fun x => Multiplicative.ofAdd (ν₂ x)
      map_one' := by
        change Multiplicative.ofAdd (ν₂ 1) = 1
        rw [hν1, ofAdd_zero]
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (ν₂ ((x : G) * y)) = _
        rw [hνmul _ x.2 _ y.2, ofAdd_add] }
  have hνpow : ∀ (i : Fin 6) (n : ZMod 2),
      νH (c i ^ n.val) = Multiplicative.ofAdd (symSix (Pi.single i n)) := by
    intro i n
    rcases zmod_two_eq_zero_or_eq_one n with rfl | rfl
    · rw [ZMod.val_zero, pow_zero, map_one, Pi.single_zero, symSix_zero, ofAdd_zero]
    · rw [ZMod.val_one, pow_one]
      exact congrArg Multiplicative.ofAdd (hccν i)
  have hνs' : ∀ u, ν₂ (s u : G) = symSix (Multiplicative.toAdd u) := by
    intro u
    have h : νH (s u) = Multiplicative.ofAdd (symSix (Multiplicative.toAdd u)) := by
      change νH (c 0 ^ (Multiplicative.toAdd u 0).val * c 1 ^ (Multiplicative.toAdd u 1).val *
        c 2 ^ (Multiplicative.toAdd u 2).val * c 3 ^ (Multiplicative.toAdd u 3).val *
        c 4 ^ (Multiplicative.toAdd u 4).val * c 5 ^ (Multiplicative.toAdd u 5).val) = _
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, hνpow, hνpow, hνpow, hνpow, hνpow, hνpow,
        ← ofAdd_add, ← ofAdd_add, ← ofAdd_add, ← ofAdd_add, ← ofAdd_add, ← symSix_add,
        ← symSix_add, ← symSix_add, ← symSix_add, ← symSix_add, sum_single_six]
    exact Multiplicative.ofAdd.injective h
  let t : Multiplicative (Fin 6 → ZMod 2) →* C₂ :=
    { toFun := fun v => ⟨tauHom φ he (Multiplicative.ofAdd (symSix (Multiplicative.toAdd v))),
        hA₂C₂ (hτA _)⟩
      map_one' := Subtype.ext (by
        change tauHom φ he (Multiplicative.ofAdd (symSix 0)) = 1
        rw [symSix_zero, ofAdd_zero, map_one])
      map_mul' := fun v v' => Subtype.ext (by
        change tauHom φ he (Multiplicative.ofAdd (symSix (Multiplicative.toAdd v +
          Multiplicative.toAdd v'))) = _
        rw [symSix_add, ofAdd_add, map_mul]
        rfl) }
  have ht : ∀ v, (t v : G) = tauHom φ he (Multiplicative.ofAdd (symSix (Multiplicative.toAdd v))) :=
    fun v => rfl
  let Ψ₀ : Multiplicative ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) →* C₂ :=
    { toFun := fun x => s (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
        t (Multiplicative.ofAdd (Multiplicative.toAdd x).2)
      map_one' := by
        simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, ofAdd_zero, map_one, mul_one]
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
        ac_rfl }
  have hΨ₀ : ∀ u v, (Ψ₀ (Multiplicative.ofAdd (u, v)) : G) =
      (s (Multiplicative.ofAdd u) : G) * (t (Multiplicative.ofAdd v) : G) := fun u v => rfl
  have hνΨ : ∀ u v, ν₂ (Ψ₀ (Multiplicative.ofAdd (u, v)) : G) = symSix u := by
    intro u v
    rw [hΨ₀, hνmul _ (s _).2 _ (t _).2, hνs', (hνk _ (t _).2).2 (by rw [ht]; exact hτA _),
      add_zero]
    rfl
  have hmemA : ∀ u v, (Ψ₀ (Multiplicative.ofAdd (u, v)) : G) ∈ 𝒜₂ ↔ u = 0 := by
    intro u v
    rw [← hνk _ (Ψ₀ _).2, hνΨ]
    exact ⟨eq_zero_of_symSix_eq_zero, fun h => by rw [h, symSix_zero]⟩
  have hinj : Function.Injective Ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨⟨u, v⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = x := ⟨Multiplicative.toAdd x, rfl⟩
    have hu : u = 0 := (hmemA u v).1 (by rw [hx]; exact one_mem _)
    subst hu
    have h1 : (t (Multiplicative.ofAdd v) : G) = 1 := by
      have h := congrArg Subtype.val hx
      rw [hΨ₀] at h
      have h0 : (s (Multiplicative.ofAdd (0 : Fin 6 → ZMod 2)) : G) = 1 := by
        rw [ofAdd_zero, map_one]
        rfl
      rw [h0, one_mul] at h
      exact h
    rw [ht, ← map_one (tauHom φ he), ← ofAdd_zero] at h1
    have h2 := Multiplicative.ofAdd.injective (tauHom_injective φ he h1)
    rw [toAdd_ofAdd] at h2
    have hv := eq_zero_of_symSix_eq_zero h2
    rw [hv]
    rfl
  have hbij : Function.Bijective Ψ₀ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hC₂card, show Nat.card (Multiplicative ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2))) =
      Nat.card ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) from rfl, Nat.card_prod, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    norm_num
  refine ⟨MulEquiv.ofBijective Ψ₀ hbij, fun u v => ?_, hmemA⟩
  change z * (Ψ₀ (Multiplicative.ofAdd (u, v)) : G) * z⁻¹ = Ψ₀ (Multiplicative.ofAdd (u, u + v))
  rw [hΨ₀, hΨ₀]
  have h1 := hzc _ (s (Multiplicative.ofAdd u)).2
  have h2 : z * (t (Multiplicative.ofAdd v) : G) * z⁻¹ = t (Multiplicative.ofAdd v) := by
    rw [mul_inv_eq_iff_eq_mul, hzL _ (hA₂L (by rw [ht]; exact hτA _))]
  rw [hνs', toAdd_ofAdd] at h1
  calc z * ((s (Multiplicative.ofAdd u) : G) * (t (Multiplicative.ofAdd v) : G)) * z⁻¹ =
      (z * (s (Multiplicative.ofAdd u) : G) * z⁻¹) *
        (z * (t (Multiplicative.ofAdd v) : G) * z⁻¹) := by group
    _ = (s (Multiplicative.ofAdd u) : G) * (tauHom φ he (Multiplicative.ofAdd (symSix u)) *
        (t (Multiplicative.ofAdd v) : G)) := by rw [h1, h2, mul_assoc]
    _ = (s (Multiplicative.ofAdd u) : G) * (t (Multiplicative.ofAdd (u + v)) : G) := by
      rw [ht, ht, toAdd_ofAdd, toAdd_ofAdd, symSix_add, ofAdd_add, map_mul]

include he hzC hinf hz in
theorem degree64_next_odd_kernel [Finite G] {D₂ C₂ X : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hX : X = normalizer (C₂ : Set G)) [(C₂.subgroupOf X).Normal]
    (hRc : centralizer (ℛ : Set G) = ℛ)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₂sq : ∀ c ∈ C₂, c ^ 2 = 1)
    (hνs : ∀ B : ↥(binarySymMatrices 3), ∃ c ∈ C₂, ν₂ c = B) (hC₂card : Nat.card C₂ = 4096) :
    let K := (CFSG.oddCore (centralizer (C₂ : Set G))).map (centralizer (C₂ : Set G)).subtype
    centralizer (C₂ : Set G) = C₂ ⊔ K ∧ C₂ ⊓ K = ⊥ ∧ Odd (Nat.card K) ∧
      (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
      (∀ k ∈ K, z * k * z⁻¹ = k⁻¹) ∧
      ∃ κ : X →* MulAut C₂, (∀ (x : X) (c : C₂), ((κ x c : C₂) : G) = x * c * (x : G)⁻¹) ∧
        κ.ker = (C₂ ⊔ K).subgroupOf X := by
  classical
  intro K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z * z = 1 := z_mul_self hz
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz1
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hzC₂ : z ∉ C₂ := z_not_mem_of_inf_eq φ hinf hz hC₂R
  have hC₂c : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x := fun x hx y hy =>
    comm_of_sq_eq_one hC₂sq hx hy
  have hCz : ∀ c ∈ C₂, c * z = z * c → c ∈ 𝒜₂ := fun c hc hcz => by
    have h : c ∈ C₂ ⊓ ℛ := by
      refine mem_inf.2 ⟨hc, ?_⟩
      rw [← hD₂H]
      exact mem_inf.2 ⟨hC₂D hc, mem_centralizer_singleton_iff.2 hcz⟩
    rw [hC₂R] at h
    exact h
  have hγC : ∀ c ∈ C₂, z⁻¹ * (c⁻¹ * z * c) ∈ 𝒜₂ := fun c hc => by
    rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D hc)]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hmemX : ∀ x : G, x ∈ X ↔ x ∈ normalizer (C₂ : Set G) := fun x => by rw [hX]
  have hzX : z ∈ X := (hmemX z).2 (mem_normalizer_of_conj_mem (hC₂n z (le_normalizer hzR)))
  have hC₂X : C₂ ≤ X := fun c hc => (hmemX c).2 (le_normalizer hc)
  have hCX : centralizer (C₂ : Set G) ≤ X := fun x hx =>
    (hmemX x).2 (centralizer_le_normalizer _ hx)
  have hE : ∀ x ∈ C₂.subgroupOf X, x ^ 2 = 1 := fun x hx => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hC₂sq _ (mem_subgroupOf.1 hx))
  have hz2' : (⟨z, hzX⟩ : X) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hz2)
  have hfix : (fun x => x⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * x * ⟨z, hzX⟩) '' ((C₂.subgroupOf X : Subgroup X) :
      Set X) = ((C₂.subgroupOf X ⊓ centralizer {(⟨z, hzX⟩ : X)} : Subgroup X) : Set X) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcC : (c : G) ∈ C₂ := mem_subgroupOf.1 hc
      have hγ := inv_mem (hγC _ hcC)
      have h1 : ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G) =
          (z⁻¹ * ((c : G)⁻¹ * z * c))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      refine mem_inf.2 ⟨mem_subgroupOf.2 ?_, mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
      · rw [h1]
        exact hA₂C₂ hγ
      · change ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G) * z =
          z * ((c⁻¹ * (⟨z, hzX⟩ : X)⁻¹ * c * ⟨z, hzX⟩ : X) : G)
        rw [h1]
        exact hzL _ (hA₂L hγ)
    · intro hx
      obtain ⟨hxE, hxz⟩ := mem_inf.1 hx
      have hxC : (x : G) ∈ C₂ := mem_subgroupOf.1 hxE
      have hxz' : (x : G) * z = z * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxz)
      have hxA := hCz _ hxC hxz'
      obtain ⟨M, hM⟩ := (mem_pullSub_iff φ he).1 hxA
      obtain ⟨c, hc, hcM⟩ := hνs (Multiplicative.toAdd M)
      have hγc : z⁻¹ * (c⁻¹ * z * c) = (x : G) := by
        rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D hc), hcM, ofAdd_toAdd, hM]
      refine ⟨⟨c, hC₂X hc⟩, mem_subgroupOf.2 hc, Subtype.ext ?_⟩
      have h1 : c⁻¹ * z⁻¹ * c * z = (z⁻¹ * (c⁻¹ * z * c))⁻¹ := by group
      change c⁻¹ * z⁻¹ * c * z = (x : G)
      rw [h1, hγc, inv_eq_of_mem_radA he φ hxA]
  have hmemCE : ∀ x : X, x ∈ centralizer ((C₂.subgroupOf X : Subgroup X) : Set X) ↔
      (x : G) ∈ centralizer (C₂ : Set G) := fun x => by
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h c hc
      exact congrArg Subtype.val (h ⟨c, hC₂X hc⟩ (mem_subgroupOf.2 hc))
    · intro h c hc
      exact Subtype.ext (h c (mem_subgroupOf.1 hc))
  have hCA : centralizer ((C₂.subgroupOf X : Subgroup X) : Set X) ⊓
      centralizer {(⟨z, hzX⟩ : X)} = C₂.subgroupOf X ⊓ centralizer {(⟨z, hzX⟩ : X)} := by
    refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ fun x hx =>
      (hmemCE x).2 (mem_centralizer_iff.2 fun c hc => hC₂c c hc _ (mem_subgroupOf.1 hx)))
    obtain ⟨hxC, hxz⟩ := mem_inf.1 hx
    have hxC' := (hmemCE x).1 hxC
    have hxz' : (x : G) * z = z * (x : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxz)
    have hxR : (x : G) ∈ ℛ := by
      rw [← hRc, mem_centralizer_iff]
      intro r hr
      refine mem_centralizer_singleton_iff.1 ((sup_le (fun a ha => ?_) ?_ :
        ℛ ≤ centralizer ({(x : G)} : Set G)) hr)
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxC' a (hA₂C₂ ha))
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.2 hxz'.symm
    obtain ⟨B, ε, hBε⟩ := (mem_radSub_iff φ he hzC hz).1 hxR
    rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
    · rw [zPow_zero, mul_one] at hBε
      refine mem_inf.2 ⟨mem_subgroupOf.2 ?_, hxz⟩
      rw [← hBε]
      exact hA₂C₂ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)
    · exfalso
      rw [zPow_one] at hBε
      have hτC := hA₂C₂ ((mem_pullSub_iff φ he).2 ⟨Multiplicative.ofAdd B, rfl⟩)
      have hzcen : ∀ c ∈ C₂, c * z = z * c := by
        intro c hc
        have h1 : z = (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * (x : G) := by
          rw [← hBε, inv_mul_cancel_left]
        have h2 : (x : G) * c = c * (x : G) := (mem_centralizer_iff.1 hxC' c hc).symm
        have h3 : (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * c =
            c * (tauHom φ he (Multiplicative.ofAdd B))⁻¹ := hC₂c _ (inv_mem hτC) c hc
        rw [h1]
        calc c * ((tauHom φ he (Multiplicative.ofAdd B))⁻¹ * (x : G)) =
            (c * (tauHom φ he (Multiplicative.ofAdd B))⁻¹) * (x : G) := by group
          _ = ((tauHom φ he (Multiplicative.ofAdd B))⁻¹ * c) * (x : G) := by rw [h3]
          _ = (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * ((x : G) * c) := by rw [mul_assoc, h2]
          _ = (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * (x : G) * c := by group
      have hle : C₂ ≤ 𝒜₂ := fun c hc => hCz c hc (hzcen c hc)
      have h64 := Subgroup.card_le_of_le hle
      rw [hC₂card, card_pullSub_radA he φ] at h64
      norm_num at h64
  obtain ⟨-, hlift⟩ :=
    EqualFixedImage.binary_involution_equal_fixed_image_centralizer_lifting hE hz2' hfix
  obtain ⟨hCcomm, hEK, -, hKmem, -, -, hKinv, -⟩ := hlift hCA
  have hcomm : ∀ x ∈ centralizer (C₂ : Set G), ∀ y ∈ centralizer (C₂ : Set G), x * y = y * x := by
    intro x hx y hy
    have h := hCcomm.is_comm.comm ⟨⟨x, hCX hx⟩, (hmemCE _).2 hx⟩ ⟨⟨y, hCX hy⟩, (hmemCE _).2 hy⟩
    exact congrArg (fun w : centralizer ((C₂.subgroupOf X : Subgroup X) : Set X) =>
      ((w : X) : G)) h
  have hCG : IsMulCommutative (centralizer (C₂ : Set G)) :=
    ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
  have hKeq : K = EqualFixedImage.centralizerOddCore C₂ := by
    change (CFSG.oddCore (centralizer (C₂ : Set G))).map (centralizer (C₂ : Set G)).subtype = _
    rw [CFSG.oddCore_eq_piCore]
    rfl
  have hK : ∀ x, x ∈ K ↔ x ∈ centralizer (C₂ : Set G) ∧ Odd (orderOf x) := fun x => by
    rw [hKeq]
    exact EqualFixedImage.mem_centralizerOddCore_iff hCG
  have hKC : K ≤ centralizer (C₂ : Set G) := fun x hx => ((hK x).1 hx).1
  have hsup : centralizer (C₂ : Set G) = C₂ ⊔ K := by
    refine le_antisymm (fun x hx => ?_) (sup_le (fun c hc => mem_centralizer_iff.2 fun d hd =>
      hC₂c d hd c hc) hKC)
    have hx' : (⟨x, hCX hx⟩ : X) ∈ C₂.subgroupOf X ⊔ EqualFixedImage.centralizerOddCore
        (C₂.subgroupOf X) := by
      rw [hEK]
      exact (hmemCE _).2 hx
    have h1 := Subgroup.mem_map_of_mem X.subtype hx'
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left hC₂X] at h1
    refine (sup_le_sup_left (fun y hy => ?_) C₂) h1
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨hkC, hkodd⟩ := (hKmem k).1 hk
    refine (hK _).2 ⟨(hmemCE k).1 hkC, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact hkodd
  have hbot : C₂ ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxK⟩ := mem_inf.1 hx
    have hodd := ((hK x).1 hxK).2
    rw [mem_bot, ← orderOf_eq_one_iff]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hC₂sq x hxC)) with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card K := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    have hodd := ((hK k).1 k.2).2
    rw [Subgroup.orderOf_coe, hk] at hodd
    exact absurd hodd (by decide)
  have hKn : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hkC, hkodd⟩ := (hK k).1 hk
    have hgN : g ∈ normalizer (C₂ : Set G) := (hmemX g).1 hg
    refine (hK _).2 ⟨mem_centralizer_iff.2 fun c hc => ?_, ?_⟩
    · have h1 : g⁻¹ * c * g ∈ C₂ := by
        have h := (mem_normalizer_iff.1 (inv_mem hgN) c).1 hc
        rwa [inv_inv] at h
      have h2 : (g⁻¹ * c * g) * k = k * (g⁻¹ * c * g) := mem_centralizer_iff.1 hkC _ h1
      calc c * (g * k * g⁻¹) = g * ((g⁻¹ * c * g) * k) * g⁻¹ := by group
        _ = g * (k * (g⁻¹ * c * g)) * g⁻¹ := by rw [h2]
        _ = g * k * g⁻¹ * c := by group
    · rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g k (g * k * g⁻¹) by
        rw [SemiconjBy]
        group)]
      exact hkodd
  have hzK : ∀ k ∈ K, z * k * z⁻¹ = k⁻¹ := by
    intro k hk
    obtain ⟨hkC, hkodd⟩ := (hK k).1 hk
    have hk' : (⟨k, hCX hkC⟩ : X) ∈ EqualFixedImage.centralizerOddCore (C₂.subgroupOf X) := by
      refine (hKmem _).2 ⟨(hmemCE _).2 hkC, ?_⟩
      rw [Subgroup.orderOf_mk]
      exact hkodd
    have h := congrArg Subtype.val (hKinv _ hk')
    change z⁻¹ * k * z = k⁻¹ at h
    rw [hzinv] at h
    rw [hzinv]
    exact h
  have hconj : ∀ (x : X) (c : C₂), (x : G) * c * (x : G)⁻¹ ∈ C₂ := fun x c =>
    (mem_normalizer_iff.1 ((hmemX x).1 x.2) c).1 c.2
  have hconj' : ∀ (x : X) (c : C₂), (x : G)⁻¹ * c * x ∈ C₂ := fun x c => by
    have h := (mem_normalizer_iff.1 (inv_mem ((hmemX x).1 x.2)) c).1 c.2
    rwa [inv_inv] at h
  let κ : X →* MulAut C₂ :=
    { toFun := fun x =>
        { toFun := fun c => ⟨(x : G) * c * (x : G)⁻¹, hconj x c⟩
          invFun := fun c => ⟨(x : G)⁻¹ * c * x, hconj' x c⟩
          left_inv := fun c => Subtype.ext (by
            change (x : G)⁻¹ * ((x : G) * c * (x : G)⁻¹) * x = c
            group)
          right_inv := fun c => Subtype.ext (by
            change (x : G) * ((x : G)⁻¹ * c * x) * (x : G)⁻¹ = c
            group)
          map_mul' := fun c d => Subtype.ext (by
            change (x : G) * ((c : G) * d) * (x : G)⁻¹ =
              (x : G) * c * (x : G)⁻¹ * ((x : G) * d * (x : G)⁻¹)
            group) }
      map_one' := MulEquiv.ext fun c => Subtype.ext (by
        change ((1 : X) : G) * c * ((1 : X) : G)⁻¹ = c
        simp)
      map_mul' := fun x y => MulEquiv.ext fun c => Subtype.ext (by
        change ((x * y : X) : G) * c * ((x * y : X) : G)⁻¹ =
          (x : G) * ((y : G) * c * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hκ : ∀ (x : X) (c : C₂), ((κ x c : C₂) : G) = x * c * (x : G)⁻¹ := fun x c => rfl
  have hker : κ.ker = (C₂ ⊔ K).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hsup, mem_centralizer_iff]
    constructor
    · intro h c hc
      have h1 := congrArg (fun φ' : MulAut C₂ => ((φ' ⟨c, hc⟩ : C₂) : G)) h
      change (x : G) * c * (x : G)⁻¹ = c at h1
      calc c * (x : G) = (x : G) * c * (x : G)⁻¹ * (x : G) := by rw [h1]
        _ = (x : G) * c := by group
    · intro h
      refine MulEquiv.ext fun c => Subtype.ext ?_
      change (x : G) * c * (x : G)⁻¹ = c
      rw [← h c c.2, mul_inv_cancel_right]
  exact ⟨hsup, hbot, hKodd, fun x hx y hy => hcomm x (hKC hx) y (hKC hy), hKn, hzK, κ, hκ, hker⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
