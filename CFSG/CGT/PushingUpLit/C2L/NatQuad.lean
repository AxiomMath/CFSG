module

public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.CGT.PushingUpLit.C2L

open scoped Matrix

private theorem nq_exists_four {n : ℕ} (hn : 2 ≤ n) :
    ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have h2 : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (GaloisField 2 n))) (n := 4) (by simpa using h2)
  exact ⟨t, ht⟩

private theorem nq_commute_of_perfect {G S : Type*} [Group G] [Group S] [Group.IsPerfect S]
    {X W : Subgroup G} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W) (φ : ↥X →* S) (hφs : Function.Surjective φ)
    {w : G} (hw : w ∈ W) (hker : ∀ x : ↥X, φ x = 1 → (x : G) * w = w * x)
    (hc : ∀ x ∈ X, w⁻¹ * (x * w * x⁻¹) ∈ W ⊓ Subgroup.centralizer (X : Set G)) :
    ∀ x ∈ X, x * w = w * x := by
  have hWc : IsMulCommutative ↥W :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hW a a.2 b b.2)
  let δ : ↥X →* ↥W :=
    { toFun := fun x => ⟨w⁻¹ * ((x : G) * w * (x : G)⁻¹),
        W.mul_mem (W.inv_mem hw) (hXW x x.2 w hw)⟩
      map_one' := Subtype.ext (by
        show w⁻¹ * ((1 : G) * w * (1 : G)⁻¹) = 1
        group)
      map_mul' := fun x y => Subtype.ext (by
        have hy : (x : G) * (w⁻¹ * ((y : G) * w * (y : G)⁻¹)) =
            w⁻¹ * ((y : G) * w * (y : G)⁻¹) * x :=
          Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hc y y.2)).2 x x.2
        have hy' : (x : G) * (w⁻¹ * ((y : G) * w * (y : G)⁻¹)) * (x : G)⁻¹ =
            w⁻¹ * ((y : G) * w * (y : G)⁻¹) := by
          rw [hy, mul_inv_cancel_right]
        show w⁻¹ * ((x : G) * y * w * ((x : G) * y)⁻¹) =
          w⁻¹ * ((x : G) * w * (x : G)⁻¹) * (w⁻¹ * ((y : G) * w * (y : G)⁻¹))
        calc w⁻¹ * ((x : G) * y * w * ((x : G) * y)⁻¹)
            = w⁻¹ * ((x : G) * w * (x : G)⁻¹) *
                ((x : G) * (w⁻¹ * ((y : G) * w * (y : G)⁻¹)) * (x : G)⁻¹) := by group
          _ = _ := by rw [hy']) }
  have hS : (commutator ↥X).map φ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hφs]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator ↥X ⊔ φ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hS, Subgroup.comap_top]
  have hle : commutator ↥X ⊔ φ.ker ≤ δ.ker := by
    refine sup_le (Abelianization.commutator_subset_ker δ) fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    apply Subtype.ext
    show w⁻¹ * ((x : G) * w * (x : G)⁻¹) = 1
    rw [hker x hx, mul_inv_cancel_right, inv_mul_cancel]
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥X) ∈ δ.ker := hle (by rw [hsup]; exact Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at h1
  have h2 : w⁻¹ * (x * w * x⁻¹) = 1 := congrArg Subtype.val h1
  have h3 : x * w * x⁻¹ = w := (inv_mul_eq_one.1 h2).symm
  calc x * w = x * w * x⁻¹ * x := by group
    _ = w * x := by rw [h3]

theorem isNatSL_of_quadratic {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    {X W A : Subgroup G}
    (φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφs : Function.Surjective φ)
    (hφk : φ.ker = (X ⊓ Subgroup.centralizer (W : Set G)).subgroupOf X)
    (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (_hAX : A ≤ X)
    (hA : (A.subgroupOf X).map φ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n))
    (hquad : ∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W,
      a' * (a * w * a⁻¹ * w⁻¹) = (a * w * a⁻¹ * w⁻¹) * a')
    {w₀ : G} (hw₀ : w₀ ∈ W)
    (hw₀fix : ∀ a ∈ A, a * w₀ * a⁻¹ * w₀⁻¹ ∈ W ⊓ Subgroup.centralizer (X : Set G))
    (hw₀Z : w₀ ∉ W ⊓ Subgroup.centralizer (X : Set G))
    (hcard : Nat.card W = 2 ^ (2 * n) * Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G))) :
    CFSG.CGT.PushingUpLit.BHS.IsNatSL X W n := by
  classical
  set K := GaloisField 2 n
  set Z : Subgroup G := W ⊓ Subgroup.centralizer (X : Set G)
  have hWc : IsMulCommutative ↥W :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hW a a.2 b b.2)
  set N : Subgroup ↥W := Z.subgroupOf W
  have hmemN : ∀ w : ↥W, w ∈ N ↔ (w : G) ∈ Z := fun w => Subgroup.mem_subgroupOf
  have hQc : IsMulCommutative (↥W ⧸ N) := IsMulCommutative.of_comm fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm' a b]
  let _ : CommGroup (↥W ⧸ N) := IsMulCommutative.instCommGroup
  have hsurjV : ∀ v : Additive (↥W ⧸ N), ∃ w : ↥W,
      Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) = v := by
    intro v
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨w, by rw [hw, ofMul_toMul]⟩
  let cW : ↥X → ↥W →* ↥W := fun x =>
    { toFun := fun w => ⟨(x : G) * w * (x : G)⁻¹, hXW x x.2 w w.2⟩
      map_one' := Subtype.ext (by
        show (x : G) * 1 * (x : G)⁻¹ = 1
        group)
      map_mul' := fun a b => Subtype.ext (by
        show (x : G) * ((a : G) * b) * (x : G)⁻¹ =
          (x : G) * a * (x : G)⁻¹ * ((x : G) * b * (x : G)⁻¹)
        group) }
  have hcW : ∀ (x : ↥X) (w : ↥W), ((cW x w : ↥W) : G) = (x : G) * w * (x : G)⁻¹ :=
    fun _ _ => rfl
  have hcN : ∀ x : ↥X, N ≤ N.comap (cW x) := by
    intro x w hw
    rw [Subgroup.mem_comap, hmemN, hcW]
    have hw' := (hmemN w).1 hw
    have hxw : (x : G) * w = w * x :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw').2 x x.2
    rw [hxw, mul_inv_cancel_right]
    exact hw'
  let ρ₀ : ↥X →* AddMonoid.End (Additive (↥W ⧸ N)) :=
    { toFun := fun x => MonoidHom.toAdditive (QuotientGroup.map N N (cW x) (hcN x))
      map_one' := by
        refine AddMonoidHom.ext fun v => ?_
        obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
        show Additive.ofMul (QuotientGroup.mk (cW 1 w) : ↥W ⧸ N) =
          Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N)
        rw [show cW 1 w = w from Subtype.ext (by simp [hcW])]
      map_mul' := fun x y => by
        refine AddMonoidHom.ext fun v => ?_
        obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
        show Additive.ofMul (QuotientGroup.mk (cW (x * y) w) : ↥W ⧸ N) =
          Additive.ofMul (QuotientGroup.mk (cW x (cW y w)) : ↥W ⧸ N)
        rw [show cW (x * y) w = cW x (cW y w) from Subtype.ext (by
          simp only [hcW, Subgroup.coe_mul]
          group)] }
  have hker₀ : φ.ker ≤ ρ₀.ker := by
    intro k hk
    have hk' : (k : G) ∈ Subgroup.centralizer (W : Set G) := by
      rw [hφk] at hk
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2
    rw [MonoidHom.mem_ker]
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    show Additive.ofMul (QuotientGroup.mk (cW k w) : ↥W ⧸ N) =
      Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N)
    rw [show cW k w = w from Subtype.ext (by
      rw [hcW, ← Subgroup.mem_centralizer_iff.1 hk' w w.2, mul_inv_cancel_right])]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K →* AddMonoid.End (Additive (↥W ⧸ N)) :=
    (QuotientGroup.lift φ.ker ρ₀ hker₀).comp e.symm.toMonoidHom
  have hρ : ∀ x : ↥X, ρ (φ x) = ρ₀ x := by
    intro x
    have h1 : e.symm (φ x) = (x : ↥X ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift φ.ker ρ₀ hker₀ (e.symm (φ x)) = ρ₀ x
    rw [h1]
    rfl
  let _ : DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Additive (↥W ⧸ N)) :=
    DistribMulAction.compHom _ ρ
  have hsmul : ∀ (x : ↥X) (w : ↥W), φ x • Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) =
      Additive.ofMul (QuotientGroup.mk (cW x w) : ↥W ⧸ N) := by
    intro x w
    show ρ (φ x) (Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N)) = _
    rw [hρ]
    rfl
  have hupper : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K, ∃ x : ↥X, (x : G) ∈ A ∧ φ x = a := by
    intro a ha
    rw [← hA] at ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl
      (Or.inr (nq_exists_four hn))
  have hfix : ∀ v : Additive (↥W ⧸ N),
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g • v = v) → v = 0 := by
    intro v hv
    obtain ⟨w, rfl⟩ := hsurjV v
    have hc : ∀ x ∈ X, (w : G)⁻¹ * (x * w * x⁻¹) ∈ W ⊓ Subgroup.centralizer (X : Set G) := by
      intro x hx
      have h1 := hv (φ ⟨x, hx⟩)
      rw [hsmul] at h1
      have h2 : (QuotientGroup.mk (cW ⟨x, hx⟩ w) : ↥W ⧸ N) = QuotientGroup.mk w :=
        Additive.ofMul.injective h1
      exact (hmemN _).1 (QuotientGroup.eq.1 h2.symm)
    have hker : ∀ x : ↥X, φ x = 1 → (x : G) * w = w * x := by
      intro x hx
      have hx' : x ∈ φ.ker := hx
      rw [hφk] at hx'
      exact (Subgroup.mem_centralizer_iff.1
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx')).2 w w.2).symm
    have hcomm := nq_commute_of_perfect hW hXW φ hφs w.2 hker hc
    have hwZ : (w : G) ∈ Z := Subgroup.mem_inf.2 ⟨w.2, Subgroup.mem_centralizer_iff.2 hcomm⟩
    have h3 : (QuotientGroup.mk w : ↥W ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff w).2 ((hmemN w).2 hwZ)
    rw [h3, ofMul_one]
  have hquad' : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
      ∀ a' ∈ CFSG.Timmesfeld.upperUnipotent K, ∀ v : Additive (↥W ⧸ N),
        a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨x, hx, rfl⟩ := hupper a ha
    obtain ⟨x', hx', rfl⟩ := hupper a' ha'
    obtain ⟨w, rfl⟩ := hsurjV v
    rw [hsmul x w, ← ofMul_div, ← QuotientGroup.mk_div, hsmul x' (cW x w / w)]
    have key : cW x' (cW x w / w) = cW x w / w := by
      apply Subtype.ext
      simp only [hcW, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      rw [hquad x hx x' hx' w w.2, mul_inv_cancel_right]
    rw [key]
  have hfixA : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
      a • Additive.ofMul (QuotientGroup.mk ⟨w₀, hw₀⟩ : ↥W ⧸ N) =
        Additive.ofMul (QuotientGroup.mk ⟨w₀, hw₀⟩ : ↥W ⧸ N) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hupper a ha
    rw [hsmul]
    congr 1
    rw [QuotientGroup.eq_iff_div_mem, hmemN, Subgroup.coe_div, hcW, div_eq_mul_inv]
    exact hw₀fix x hx
  have hw0 : Additive.ofMul (QuotientGroup.mk ⟨w₀, hw₀⟩ : ↥W ⧸ N) ≠ 0 := by
    intro h0
    have h1 : (QuotientGroup.mk ⟨w₀, hw₀⟩ : ↥W ⧸ N) = 1 :=
      Additive.ofMul.injective (h0.trans ofMul_one.symm)
    exact hw₀Z ((hmemN _).1 ((QuotientGroup.eq_one_iff _).1 h1))
  obtain ⟨θ, hθinj, -, -, hθ⟩ :=
    CFSG.Timmesfeld.ARS.exists_natural_of_quadratic hfix hquad' hfixA hw0
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hNZ : Nat.card ↥N = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ≤ W)).toEquiv
  have hVcard : Nat.card (Additive (↥W ⧸ N)) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNZ, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right hZpos h1).symm
  have hKcard : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  have hFcard : Nat.card (Fin 2 → K) = 2 ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_fin, hKcard, ← pow_mul, mul_comm]
  have hθbij : Function.Bijective θ := hθinj.bijective_of_nat_card_le (hVcard.trans hFcard.symm).le
  let θe : (Fin 2 → K) ≃+ Additive (↥W ⧸ N) := AddEquiv.ofBijective θ hθbij
  let ψ : ↥W →* Multiplicative (Fin 2 → K) :=
    (AddMonoidHom.toMultiplicativeRight θe.symm.toAddMonoidHom).comp (QuotientGroup.mk' N)
  have hψ : ∀ w : ↥W, Multiplicative.toAdd (ψ w) =
      θe.symm (Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N)) := fun _ => rfl
  have hθψ : ∀ w : ↥W, θ (Multiplicative.toAdd (ψ w)) =
      Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) := fun _ => θe.apply_symm_apply _
  refine ⟨φ, ψ, hφs, hφk, ?_, ?_, ?_⟩
  ·
    intro u
    obtain ⟨w, hw⟩ := hsurjV (θ (Multiplicative.toAdd u))
    refine ⟨w, Multiplicative.toAdd.injective ?_⟩
    rw [hψ, hw]
    exact θe.symm_apply_apply _
  ·
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : θe.symm (Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N)) = 0 := by
        rw [← hψ, h, toAdd_one]
      have h2 : Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) = 0 :=
        θe.symm.injective (h1.trans (map_zero θe.symm).symm)
      have h3 : (QuotientGroup.mk w : ↥W ⧸ N) = 1 :=
        Additive.ofMul.injective (h2.trans ofMul_one.symm)
      exact (hmemN w).1 ((QuotientGroup.eq_one_iff w).1 h3)
    · intro h
      have h3 : (QuotientGroup.mk w : ↥W ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff w).2 ((hmemN w).2 h)
      apply Multiplicative.toAdd.injective
      rw [hψ, h3, ofMul_one, map_zero, toAdd_one]
  ·
    intro x w hw'
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hψ ⟨_, hw'⟩]
    apply θe.injective
    rw [θe.apply_symm_apply]
    show _ = θ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (ψ w))
    rw [hθ (φ x), hθψ, hsmul]
    rfl

end CFSG.CGT.PushingUpLit.C2L
