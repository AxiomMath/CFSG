module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveRadicalFixedLift

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup OddQuadraticFive

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
  {b : LinearMap.BilinForm (ZMod 2) E} {Q : QuadraticForm (ZMod 2) E}

theorem exists_fixed_lift_of_group [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b) {C I : Subgroup G}
    (hIc : ∀ i ∈ I, ∀ c ∈ C, i * c = c * i)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ I) (hsq : ∀ x ∈ C, x ^ 2 ∈ I)
    (ℓ : bilinIsometryGroup b →* G) (hℓC : ∀ s, ∀ c ∈ C, ℓ s * c * (ℓ s)⁻¹ ∈ C)
    (hℓI : ∀ s, ∀ i ∈ I, ℓ s * i * (ℓ s)⁻¹ ∈ I)
    (κ : E → G) (hκC : ∀ x, κ x ∈ C) (hκadd : ∀ x y, (κ (x + y))⁻¹ * (κ x * κ y) ∈ I)
    (hκinj : ∀ x, κ x ∈ I → x = 0)
    (hκσ : ∀ s x, (κ (sE s x))⁻¹ * (ℓ s * κ x * (ℓ s)⁻¹) ∈ I)
    (ρ : G → E × ZMod 2) (hρmul : ∀ x ∈ C, ∀ y ∈ C, ρ (x * y) = ρ x + ρ y)
    (hρsurj : ∀ v, ∃ c ∈ C, ρ c = v)
    (hρσ : ∀ s, ∀ c ∈ C, ρ (ℓ s * c * (ℓ s)⁻¹) =
      (sE s (ρ c).1, (ρ c).2 + Q (ρ c).1 + Q (sE s (ρ c).1)))
    (hρI : ∀ i ∈ I, ρ i = 0) (hρκ : ∀ x, ρ (κ x) = 0)
    (hρker : ∀ c ∈ C, ρ c = 0 → ∃ x, (κ x)⁻¹ * c ∈ I) :
    ∃ c ∈ C, ρ c = (0, 1) ∧ ∀ s, c⁻¹ * (ℓ s * c * (ℓ s)⁻¹) ∈ I := by
  classical
  set N : Subgroup C := I.subgroupOf C with hN
  have hmemN : ∀ x : C, x ∈ N ↔ (x : G) ∈ I := fun x => mem_subgroupOf
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hmemN] at hn ⊢
    have h : (n : G) * g = g * n := hIc n hn g g.2
    have h1 : ((g * n * g⁻¹ : C) : G) = n := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← h, mul_inv_cancel_right]
    rw [h1]
    exact hn⟩
  have hmk : ∀ x y : C, (x : C ⧸ N) = y ↔ (x : G)⁻¹ * y ∈ I := fun x y => by
    rw [QuotientGroup.eq, hmemN]
    exact Iff.rfl
  let _ : CommGroup (C ⧸ N) :=
    { (inferInstance : Group (C ⧸ N)) with
      mul_comm := fun p q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
        have h := hcomm _ (inv_mem y.2) _ (inv_mem x.2)
        rw [inv_inv, inv_inv] at h
        have h1 : ((x * y : C) : G)⁻¹ * ((y * x : C) : G) =
            (y : G)⁻¹ * (x : G)⁻¹ * y * x := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          group
        rw [h1]
        exact h }
  let _ : Module (ZMod 2) (Additive (C ⧸ N)) := AddCommGroup.zmodModule fun w => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    change Additive.ofMul (Additive.toMul w ^ 2) = Additive.ofMul 1
    refine congrArg Additive.ofMul ?_
    rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmemN, Subgroup.coe_pow]
    exact hsq x x.2
  let cj : bilinIsometryGroup b → C →* C := fun s =>
    { toFun := fun c => ⟨ℓ s * c * (ℓ s)⁻¹, hℓC s c c.2⟩
      map_one' := Subtype.ext (by
        change ℓ s * 1 * (ℓ s)⁻¹ = 1
        group)
      map_mul' := fun x y => Subtype.ext (by
        change ℓ s * (x * y) * (ℓ s)⁻¹ = ℓ s * x * (ℓ s)⁻¹ * (ℓ s * y * (ℓ s)⁻¹)
        group) }
  have hcj : ∀ s (c : C), ((cj s c : C) : G) = ℓ s * c * (ℓ s)⁻¹ := fun s c => rfl
  have hcjN : ∀ s, N ≤ N.comap (cj s) := fun s x hx => by
    rw [mem_comap, hmemN, hcj]
    exact hℓI s x ((hmemN x).1 hx)
  have hcj_one : ∀ c : C, cj 1 c = c := fun c => Subtype.ext (by
    rw [hcj, map_one]
    group)
  have hcj_mul : ∀ s t (c : C), cj (s * t) c = cj s (cj t c) := fun s t c => Subtype.ext (by
    rw [hcj, hcj, hcj, map_mul]
    group)
  let act : bilinIsometryGroup b → (C ⧸ N →* C ⧸ N) := fun s =>
    QuotientGroup.map N N (cj s) (hcjN s)
  let σ : Representation (ZMod 2) (bilinIsometryGroup b) (Additive (C ⧸ N)) :=
    { toFun := fun s => (MonoidHom.toAdditive (act s)).toZModLinearMap 2
      map_one' := by
        apply LinearMap.ext
        intro w
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
        change Additive.ofMul (act 1 (Additive.toMul w)) = w
        rw [← hx]
        change Additive.ofMul ((cj 1 x : C) : C ⧸ N) = w
        rw [hcj_one, hx]
        rfl
      map_mul' := fun s t => by
        apply LinearMap.ext
        intro w
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
        change Additive.ofMul (act (s * t) (Additive.toMul w)) =
          Additive.ofMul (act s (act t (Additive.toMul w)))
        rw [← hx]
        change Additive.ofMul ((cj (s * t) x : C) : C ⧸ N) =
          Additive.ofMul ((cj s (cj t x) : C) : C ⧸ N)
        rw [hcj_mul] }
  have hσ : ∀ s (c : C), σ s (Additive.ofMul (c : C ⧸ N)) =
      Additive.ofMul ((cj s c : C) : C ⧸ N) := fun s c => rfl
  have hκ0 : κ 0 ∈ I := by
    have h := hκadd 0 0
    rwa [add_zero, inv_mul_cancel_left] at h
  let ιA : E →+ Additive (C ⧸ N) :=
    { toFun := fun x => Additive.ofMul ((⟨κ x, hκC x⟩ : C) : C ⧸ N)
      map_zero' := congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).2 ((hmemN _).2 hκ0))
      map_add' := fun x y => congrArg Additive.ofMul (by
        change ((⟨κ (x + y), hκC _⟩ : C) : C ⧸ N) =
          ((⟨κ x, hκC x⟩ : C) : C ⧸ N) * ((⟨κ y, hκC y⟩ : C) : C ⧸ N)
        rw [← QuotientGroup.mk_mul, hmk]
        exact hκadd x y) }
  let ι : E →ₗ[ZMod 2] Additive (C ⧸ N) := ιA.toZModLinearMap 2
  have hι : ∀ x, ι x = Additive.ofMul ((⟨κ x, hκC x⟩ : C) : C ⧸ N) := fun x => rfl
  let ρC : C →* Multiplicative (E × ZMod 2) :=
    { toFun := fun c => Multiplicative.ofAdd (ρ c)
      map_one' := by
        change Multiplicative.ofAdd (ρ 1) = 1
        rw [hρI 1 (one_mem I)]
        rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (ρ (x * y)) = Multiplicative.ofAdd (ρ x) *
          Multiplicative.ofAdd (ρ y)
        rw [hρmul x x.2 y y.2, ofAdd_add] }
  have hρCN : N ≤ ρC.ker := fun n hn => by
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (ρ n) = 1
    rw [hρI n ((hmemN n).1 hn)]
    rfl
  let ρL : Additive (C ⧸ N) →ₗ[ZMod 2] E × ZMod 2 :=
    (MonoidHom.toAdditiveLeft (QuotientGroup.lift N ρC hρCN)).toZModLinearMap 2
  have hρL : ∀ c : C, ρL (Additive.ofMul (c : C ⧸ N)) = ρ c := fun c => rfl
  have hall : ∀ w : Additive (C ⧸ N), ∃ c : C, w = Additive.ofMul (c : C ⧸ N) := fun w => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    exact ⟨x, by rw [hx]; rfl⟩
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hι] at hx
    have h : ((⟨κ x, hκC x⟩ : C) : C ⧸ N) = 1 := congrArg Additive.toMul hx
    exact hκinj x ((hmemN _).1 ((QuotientGroup.eq_one_iff _).1 h))
  have hισ : ∀ (s : bilinIsometryGroup b) (x : E), ι (sE s x) = σ s (ι x) := by
    intro s x
    rw [hι, hι, hσ]
    exact congrArg Additive.ofMul ((hmk _ _).2 (hκσ s x))
  have hρLsurj : Function.Surjective ρL := fun v => by
    obtain ⟨c, hc, hcv⟩ := hρsurj v
    exact ⟨Additive.ofMul ((⟨c, hc⟩ : C) : C ⧸ N), by rw [hρL]; exact hcv⟩
  have hρLσ : ∀ (s : bilinIsometryGroup b) (y : Additive (C ⧸ N)),
      ρL (σ s y) = (sE s (ρL y).1, (ρL y).2 + Q (ρL y).1 + Q (sE s (ρL y).1)) := by
    intro s y
    obtain ⟨c, rfl⟩ := hall y
    rw [hσ, hρL, hρL, hcj]
    exact hρσ s c c.2
  have hker : LinearMap.ker ρL = LinearMap.range ι := by
    ext y
    obtain ⟨c, rfl⟩ := hall y
    rw [LinearMap.mem_ker, LinearMap.mem_range, hρL]
    constructor
    · intro hc
      obtain ⟨x, hx⟩ := hρker c c.2 hc
      exact ⟨x, by rw [hι]; exact congrArg Additive.ofMul ((hmk _ _).2 hx)⟩
    · rintro ⟨x, hx⟩
      rw [hι] at hx
      have h := congrArg ρL hx
      rw [hρL, hρL] at h
      rw [← h]
      exact hρκ x
  obtain ⟨ξ, hfix, hρξ⟩ := binary_odd_quadratic_five_by_natural_four_radical_fixed_lift hb hnd hQ
    σ ι hιinj hισ ρL hρLsurj hρLσ hker
  obtain ⟨c, rfl⟩ := hall ξ
  refine ⟨c, c.2, by rw [← hρL]; exact hρξ, fun s => ?_⟩
  have h := hfix s
  rw [hσ] at h
  have h1 : ((c : C) : C ⧸ N) = ((cj s c : C) : C ⧸ N) := (congrArg Additive.toMul h).symm
  rw [← hcj]
  exact (hmk _ _).1 h1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
