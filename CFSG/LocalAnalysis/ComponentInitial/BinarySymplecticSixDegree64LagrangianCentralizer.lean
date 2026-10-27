module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleElementary
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeCentralizerComplement

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

include hinf in
theorem sq_mem_radA_of_mem {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) {d : G} (hd : d ∈ D₂) : d ^ 2 ∈ 𝒜₂ := by
  have hd2 : d ^ 2 ∈ D₂ := pow_mem hd 2
  have hν : ν₂ (d ^ 2) = 0 := by
    rw [sq, nu_mul he φ hzC hinf hz hν₂z hpure hd hd, symThree_add_self]
  have hR : d ^ 2 ∈ ℛ := (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H hd2).1 hν
  obtain ⟨B, ε, hBε⟩ := (mem_radSub_iff φ he hzC hz).1 hR
  have h1 := hpure d hd B ε
  rw [← radHom_apply φ he hzC hz] at hBε
  have h2 : d⁻¹ * d ^ 2 * d = d ^ 2 := by group
  rw [hBε, h2] at h1
  have h3 := Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf (hBε.trans h1))
  have h4 : ε • ν₂ d = 0 := by
    have h5 := congrArg Prod.fst h3
    simp only at h5
    exact (add_eq_left.1 h5.symm)
  rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
  · rw [← hBε, radHom_tau]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  · rw [one_smul] at h4
    have hdR : d ∈ ℛ := (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H hd).1 h4
    obtain ⟨B', ε', rfl⟩ := (mem_radSub_iff φ he hzC hz).1 hdR
    rw [← radHom_apply φ he hzC hz, sq, ← map_mul, ← ofAdd_add, Prod.mk_add_mk,
      symThree_add_self, zmod_two_add_self_eq_zero, radHom_tau]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩

include hinf in
theorem degree64_lagrangian_centralizer [Finite G] {D₂ E₂ P : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hE₂D : E₂ ≤ D₂) (hE₂c : IsMulCommutative E₂) (hE₂sq : ∀ x ∈ E₂, x ^ 2 = 1)
    (hE₂R : E₂ ⊓ ℛ = 𝒜₂)
    (hE₂F : ∀ d ∈ D₂, symThreeDiag (ν₂ d : M₃) = 0 ↔
      d ∈ (zpowers z : Set G) * (E₂ : Set G))
    (hE₂levi : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ E₂,
      leviHom φ he g * x * (leviHom φ he g)⁻¹ ∈ E₂)
    (hPD : P ≤ D₂) (hPc : IsMulCommutative P) (hAP : 𝒜₂ ≤ P) (hPR : P ⊓ ℛ = 𝒜₂)
    (hPJ : ∀ B : ↥(binarySymMatrices 3),
      (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (B : M₃) i j = 0) ↔ ∃ p ∈ P, ν₂ p = B) :
    Nat.card (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) = 4096 ∧ Nat.card P = 512 ∧
      Nat.card E₂ = 512 ∧
      (D₂ : Set G) = (zpowers z : Set G) * ((D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) : Set G) ∧
      (D₂ ⊓ centralizer (E₂ : Set G)) ⊓ ℛ = 𝒜₂ ∧
      (∀ c : G, (c ∈ D₂ ⊓ centralizer (E₂ : Set G) ∧ symThreeDiag (ν₂ c : M₃) = 0) ↔ c ∈ E₂) ∧
      P ≤ D₂ ⊓ centralizer (E₂ : Set G) ∧
      (∀ B : ↥(binarySymMatrices 3), ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ν₂ c = B) ∧
      (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ν₂ c = 0 ↔ c ∈ 𝒜₂) ∧
      (∀ w : Fin 3 → ZMod 2, ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G),
        symThreeDiag (ν₂ c : M₃) = w) ∧
      ∃ ε : ZMod 2,
        (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ∀ d ∈ D₂ ⊓ centralizer (E₂ : Set G),
          c ^ 2 = tauHom φ he (Multiplicative.ofAdd
            (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)))) ∧
          c⁻¹ * d⁻¹ * c * d = tauHom φ he (Multiplicative.ofAdd
            (symThreeSquarePolar ε (symThreeDiag (ν₂ c : M₃)) (symThreeDiag (ν₂ d : M₃))))) ∧
        (ε = 0 → (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = 1) ∧
          ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ∀ d ∈ D₂ ⊓ centralizer (E₂ : Set G),
            c * d = d * c) ∧
        (ε = 1 → Monoid.exponent (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) = 4 ∧
          closure {x | ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = x} = 𝒜₂ ∧
          ⁅D₂ ⊓ centralizer (E₂ : Set G), D₂ ⊓ centralizer (E₂ : Set G)⁆ = altSub φ he ∧
          (center (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G)).map
            (D₂ ⊓ centralizer (E₂ : Set G)).subtype = E₂ ∧
          ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = 1 ↔ c ∈ E₂) := by
  classical
  have hzD : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  have hAD : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
  set zD : D₂ := ⟨z, hzD⟩ with hzD_def
  set A : Subgroup D₂ := Subgroup.subgroupOf 𝒜₂ D₂ with hA
  set R : Subgroup D₂ := Subgroup.subgroupOf ℛ D₂ with hR
  set E : Subgroup D₂ := E₂.subgroupOf D₂ with hE
  set P' : Subgroup D₂ := P.subgroupOf D₂ with hP'
  have hcomm₂ : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d := by
    intro d hd a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h := hpure d hd (Multiplicative.toAdd B) 0
    rw [zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h
    exact comm_of_inv_mul_mul_eq h
  have hAc : A ≤ center D₂ := fun x hx => mem_center_iff.2 fun y =>
    Subtype.ext (hcomm₂ y y.2 x (mem_subgroupOf.1 hx))
  let f : Multiplicative (binarySymMatrices 3) →* A :=
    { toFun := fun B => ⟨⟨tauHom φ he B, hAD ((mem_pullSub_iff φ he).2 ⟨B, rfl⟩)⟩,
        mem_subgroupOf.2 ((mem_pullSub_iff φ he).2 ⟨B, rfl⟩)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun B B' => Subtype.ext (Subtype.ext (map_mul _ B B')) }
  have hf : Function.Bijective f := by
    refine ⟨fun B B' h => tauHom_injective φ he (congrArg (fun x : A => ((x : D₂) : G)) h),
      fun x => ?_⟩
    obtain ⟨B, hB⟩ := (mem_pullSub_iff φ he).1 (mem_subgroupOf.1 x.2)
    exact ⟨B, Subtype.ext (Subtype.ext hB)⟩
  set a : A ≃* Multiplicative (binarySymMatrices 3) := (MulEquiv.ofBijective f hf).symm with ha
  have ha_symm : ∀ B, ((a.symm B : A) : G) = tauHom φ he B := fun B => by
    rw [ha, MulEquiv.symm_symm]
    rfl
  have hz2 : zD ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hz]
    exact pow_orderOf_eq_one z)
  have hzA : zD ∉ A := by
    intro h
    have h1 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨pullSub_le φ _ (mem_subgroupOf.1 h), mem_zpowers z⟩
    rw [hinf, mem_bot] at h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzpow : (zpowers z).subgroupOf D₂ = zpowers zD := by
    apply Subgroup.map_injective D₂.subtype_injective
    rw [subgroupOf_map_subtype, inf_of_le_left (zpowers_le.2 hzD), MonoidHom.map_zpowers]
    rfl
  have hRA : R = A ⊔ zpowers zD := by
    rw [hR, hA, ← hzpow, ← subgroupOf_sup hAD (zpowers_le.2 hzD)]
  have hsq : ∀ d : D₂, d ^ 2 ∈ A := fun d => by
    rw [hA, mem_subgroupOf, Subgroup.coe_pow]
    exact sq_mem_radA_of_mem he φ hzC hinf hz hν₂z hpure hD₂H d.2
  have hν : ∀ d : D₂, (a.symm (.ofAdd (ν₂ d)) : D₂) = zD⁻¹ * d⁻¹ * zD * d := fun d => by
    apply Subtype.ext
    rw [ha_symm, tauHom_nu he φ hzC hz hν₂z d.2]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzD_def]
    group
  have hνs : Function.Surjective (fun d : D₂ => ν₂ d) := fun C => by
    obtain ⟨d, hd, hdC⟩ := hν₂surj C
    exact ⟨⟨d, hd⟩, hdC⟩
  have hνk : ∀ d : D₂, ν₂ d = 0 ↔ d ∈ R := fun d => by
    rw [hR, mem_subgroupOf]
    exact nu_eq_zero_iff he φ hzC hz hν₂z hD₂H d.2
  have hρz : ∀ g : GL (Fin 3) (ZMod 2), leviAct he φ hzC hz hD₂n g zD = zD := fun g =>
    Subtype.ext (by
      rw [coe_leviAct, hzD_def, leviHom_mul_z φ he hzC g, mul_inv_cancel_right])
  have hρa : ∀ (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3),
      leviAct he φ hzC hz hD₂n g (a.symm (.ofAdd B) : D₂) =
        a.symm (.ofAdd (symThreeCongr g B)) := fun g B => Subtype.ext (by
    rw [coe_leviAct, ha_symm, ha_symm, leviHom_conj_tauHom'])
  have hEF : ∀ x ∈ E, (ν₂ x : M₃) ∈ binaryAltMatrices 3 := fun x hx => by
    rw [symThree_mem_alt_iff]
    have hxE : (x : G) ∈ E₂ := mem_subgroupOf.1 hx
    exact (hE₂F x x.2).2 ⟨1, one_mem _, x, hxE, one_mul _⟩
  have hEρ : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ E, leviAct he φ hzC hz hD₂n g x ∈ E :=
    fun g x hx => by
      rw [hE, mem_subgroupOf, coe_leviAct]
      exact hE₂levi g x (mem_subgroupOf.1 hx)
  have hEc : IsMulCommutative E := ⟨⟨fun x y => by
    have hx : ((x : D₂) : G) ∈ E₂ := mem_subgroupOf.1 x.2
    have hy : ((y : D₂) : G) ∈ E₂ := mem_subgroupOf.1 y.2
    have h := hE₂c.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((x : D₂) : G) * ((y : D₂) : G) = ((y : D₂) : G) * ((x : D₂) : G)
    exact congrArg (fun w : E₂ => (w : G)) h⟩⟩
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hE₂sq x (mem_subgroupOf.1 hx))
  have hER : E ⊓ R = A := by
    ext x
    rw [mem_inf, hE, hR, hA, mem_subgroupOf, mem_subgroupOf, mem_subgroupOf, ← hE₂R, mem_inf]
  have hFE : ∀ d : D₂, (ν₂ d : M₃) ∈ binaryAltMatrices 3 ↔
      d ∈ (zpowers zD : Set D₂) * (E : Set D₂) := fun d => by
    rw [symThree_mem_alt_iff, hE₂F d d.2]
    constructor
    · rintro ⟨t, ht, x, hx, hdx⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
      refine ⟨zD ^ n, ⟨n, rfl⟩, ⟨x, hE₂D hx⟩, mem_subgroupOf.2 hx, Subtype.ext ?_⟩
      change z ^ n * x = d
      exact hdx
    · rintro ⟨t, ht, x, hx, hdx⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
      refine ⟨z ^ n, ⟨n, rfl⟩, x, mem_subgroupOf.1 hx, ?_⟩
      have h := congrArg Subtype.val hdx
      change (zD ^ n : D₂).1 * x.1 = d.1 at h
      rw [Subgroup.coe_zpow] at h
      exact h
  have hPc' : IsMulCommutative P' := ⟨⟨fun x y => by
    have hx : ((x : D₂) : G) ∈ P := mem_subgroupOf.1 x.2
    have hy : ((y : D₂) : G) ∈ P := mem_subgroupOf.1 y.2
    have h := hPc.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((x : D₂) : G) * ((y : D₂) : G) = ((y : D₂) : G) * ((x : D₂) : G)
    exact congrArg (fun w : P => (w : G)) h⟩⟩
  have hAP' : A ≤ P' := fun x hx => mem_subgroupOf.2 (hAP (mem_subgroupOf.1 hx))
  have hPR' : P' ⊓ R = A := by
    ext x
    rw [mem_inf, hP', hR, hA, mem_subgroupOf, mem_subgroupOf, mem_subgroupOf, ← hPR, mem_inf]
  have hPJ' : ∀ B : binarySymMatrices 3,
      (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (B : M₃) i j = 0) ↔ ∃ p ∈ P', ν₂ p = B := fun B => by
    rw [hPJ B]
    constructor
    · rintro ⟨p, hp, hpB⟩
      exact ⟨⟨p, hPD hp⟩, mem_subgroupOf.2 hp, hpB⟩
    · rintro ⟨p, hp, hpB⟩
      exact ⟨p, mem_subgroupOf.1 hp, hpB⟩
  obtain ⟨-, -, -, hEcard, hPcard, hCcard, huniv, hCR, hCF, hPC, -, ⟨_, ψ, hψ⟩, -,
    ⟨_, ψ', hψ'⟩, -, ε, hεf, hε0, hε1⟩ :=
    binary_symmetric_three_centralizer_complement_and_square_map A hAc a zD hz2 hzA R hRA hsq
      (fun d => ν₂ d) hν hνs hνk (leviAct he φ hzC hz hD₂n) hρz hρa E hEF hEρ hE2 hER hFE P'
      hAP' hPR' hPJ' (centralizer (E : Set D₂)) rfl
  set C := centralizer (E : Set D₂) with hC
  have hCmap : C.map D₂.subtype = D₂ ⊓ centralizer (E₂ : Set G) := by
    ext x
    rw [mem_map_subtype_iff, mem_inf]
    constructor
    · rintro ⟨h, hxC⟩
      refine ⟨h, mem_centralizer_iff.2 fun y hy => ?_⟩
      have h1 := mem_centralizer_iff.1 hxC ⟨y, hE₂D hy⟩ (mem_subgroupOf.2 hy)
      exact congrArg Subtype.val h1
    · rintro ⟨h, hxC⟩
      refine ⟨h, mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
      exact mem_centralizer_iff.1 hxC y (mem_subgroupOf.1 hy)
  have hmemC : ∀ {x : G}, x ∈ D₂ ⊓ centralizer (E₂ : Set G) ↔ ∃ h : x ∈ D₂, (⟨x, h⟩ : D₂) ∈ C :=
    fun {x} => by rw [← hCmap, mem_map_subtype_iff]
  have hsqC : ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ∀ d ∈ D₂ ⊓ centralizer (E₂ : Set G),
      c ^ 2 = tauHom φ he (Multiplicative.ofAdd
        (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)))) ∧
      c⁻¹ * d⁻¹ * c * d = tauHom φ he (Multiplicative.ofAdd
        (symThreeSquarePolar ε (symThreeDiag (ν₂ c : M₃)) (symThreeDiag (ν₂ d : M₃)))) := by
    intro c hc d hd
    obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    obtain ⟨hdD, hdC⟩ := hmemC.1 hd
    obtain ⟨h1, h2⟩ := hεf _ hcC _ hdC
    refine ⟨?_, ?_⟩
    · have h := congrArg Subtype.val h1
      rw [Subgroup.coe_pow] at h
      rw [h, ha_symm]
    · have h := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [h, ha_symm]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun c => ?_, ?_, fun B => ?_, fun c hc => ?_, fun w => ?_, ε,
    hsqC, fun h0 => ?_, fun h1 => ?_⟩
  · rw [← hCmap, card_map_of_injective D₂.subtype_injective, hCcard]
  · rw [← Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv]
    exact hPcard
  · rw [← Nat.card_congr (subgroupOfEquivOfLe hE₂D).toEquiv]
    exact hEcard
  · ext x
    constructor
    · intro hx
      have h : (⟨x, hx⟩ : D₂) ∈ (Set.univ : Set D₂) := Set.mem_univ _
      rw [huniv] at h
      obtain ⟨t, ht, c, hc, htc⟩ := h
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
      refine ⟨z ^ n, ⟨n, rfl⟩, c, ?_, ?_⟩
      · rw [← hCmap]
        exact ⟨c, hc, rfl⟩
      · have h1 := congrArg Subtype.val htc
        change (zD ^ n : D₂).1 * c.1 = x at h1
        rw [Subgroup.coe_zpow] at h1
        exact h1
    · rintro ⟨t, ht, c, hc, rfl⟩
      exact mul_mem (zpowers_le.2 hzD ht) (mem_inf.1 hc).1
  · have h := congrArg (Subgroup.map D₂.subtype) hCR
    rw [Subgroup.map_inf_eq _ _ _ D₂.subtype_injective, hCmap, hR, hA, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hRD₂, inf_of_le_left hAD] at h
    exact h
  · constructor
    · rintro ⟨hc, hc0⟩
      obtain ⟨hcD, hcC⟩ := hmemC.1 hc
      have h := (hCF ⟨c, hcD⟩).1 ⟨hcC, (symThree_mem_alt_iff _).2 hc0⟩
      exact mem_subgroupOf.1 h
    · intro hc
      have hcD := hE₂D hc
      have h := (hCF ⟨c, hcD⟩).2 (mem_subgroupOf.2 hc)
      refine ⟨hmemC.2 ⟨hcD, h.1⟩, ?_⟩
      exact (symThree_mem_alt_iff _).1 h.2
  · intro p hp
    exact hmemC.2 ⟨hPD hp, hPC (mem_subgroupOf.2 hp)⟩
  · obtain ⟨q, hq⟩ := ψ.surjective (Multiplicative.ofAdd B)
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨c, hmemC.2 ⟨c.1.2, c.2⟩, ?_⟩
    rw [hψ] at hq
    exact Multiplicative.ofAdd.injective hq
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    constructor
    · intro h0
      have h := hψ ⟨⟨c, hcD⟩, hcC⟩
      change ψ _ = Multiplicative.ofAdd (ν₂ c) at h
      rw [h0, ofAdd_zero, ← map_one ψ] at h
      have h2 := ψ.injective h
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
      exact mem_subgroupOf.1 h2
    · intro hcA
      exact (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H hcD).2 (mem_sup_left hcA)
  · obtain ⟨q, hq⟩ := ψ'.surjective (Multiplicative.ofAdd w)
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨c, hmemC.2 ⟨c.1.2, c.2⟩, ?_⟩
    rw [hψ'] at hq
    exact Multiplicative.ofAdd.injective hq
  · obtain ⟨⟨_, hsq0⟩, -, -⟩ := hε0 h0
    refine ⟨fun c hc => ?_, fun c hc d hd => ?_⟩
    · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
      have h := congrArg Subtype.val (hsq0 _ hcC)
      rw [Subgroup.coe_pow] at h
      exact h
    · obtain ⟨⟨hcomm, -⟩, -, -⟩ := hε0 h0
      obtain ⟨hcD, hcC⟩ := hmemC.1 hc
      obtain ⟨hdD, hdC⟩ := hmemC.1 hd
      have h := congrArg (fun w : C => ((w : D₂) : G))
        (hcomm.is_comm.comm ⟨⟨c, hcD⟩, hcC⟩ ⟨⟨d, hdD⟩, hdC⟩)
      exact h
  · obtain ⟨hexp, hcl, hcomm, hcen, hinv⟩ := hε1 h1
    refine ⟨?_, ?_, ?_, ?_, fun c hc => ?_⟩
    · rw [← hexp]
      exact (Monoid.exponent_eq_of_mulEquiv
        ((C.equivMapOfInjective D₂.subtype D₂.subtype_injective).trans
          (MulEquiv.subgroupCongr hCmap))).symm
    · have h := congrArg (Subgroup.map D₂.subtype) hcl
      rw [MonoidHom.map_closure, hA, subgroupOf_map_subtype, inf_of_le_left hAD] at h
      rw [← h]
      congr 1
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨hcD, hcC⟩ := hmemC.1 hc
        exact ⟨⟨c, hcD⟩ ^ 2, ⟨⟨c, hcD⟩, hcC, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        exact ⟨c, hmemC.2 ⟨c.2, hc⟩, rfl⟩
    · rw [← hCmap, ← Subgroup.map_commutator]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨B, hB, rfl⟩ := (hcomm y).1 hy
        rw [Subgroup.coe_subtype, ha_symm]
        exact ⟨B, (symThree_mem_alt_iff B).1 hB, rfl⟩
      · rintro ⟨B, hB, rfl⟩
        refine ⟨a.symm (Multiplicative.ofAdd B), (hcomm _).2 ⟨B, (symThree_mem_alt_iff B).2 hB,
          rfl⟩, ?_⟩
        rw [Subgroup.coe_subtype, ha_symm]
    · rw [← hCmap, ← map_center_map_subtype, hcen, hE, subgroupOf_map_subtype,
        inf_of_le_left hE₂D]
    · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
      have h := hinv ⟨c, hcD⟩ hcC
      rw [mem_subgroupOf] at h
      rw [← h]
      constructor
      · intro h2
        exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h2)
      · intro h2
        have h3 := congrArg Subtype.val h2
        rw [Subgroup.coe_pow] at h3
        exact h3

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
