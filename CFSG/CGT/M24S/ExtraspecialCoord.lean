module

public import CFSG.CGT.M24S.GL4
public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.M24S

open CFSG.CGT.Timmesfeld75 Matrix GL4
open scoped MatrixGroups

variable {G : Type} [Group G]

structure NatCoord (T H : Subgroup G) (z : G) where
  le : T ≤ H
  ρ : H →* SL(4, ZMod 2)
  ψ : T ≃* Multiplicative (Fin 4 → ZMod 2)
  ker_iff : ∀ h : H, ρ h = 1 ↔ (h : G) ∈ T
  surj : Function.Surjective ρ
  compat : ∀ (h : H) (t : T) (hm : (h : G) * t * (h : G)⁻¹ ∈ T),
    Multiplicative.toAdd (ψ ⟨_, hm⟩) =
      (ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (ψ t)
  mem : z ∈ T
  ψ_z : Multiplicative.toAdd (ψ ⟨z, mem⟩) = e0

namespace NatCoord

variable {T H : Subgroup G} {z : G} (c : NatCoord T H z)

open Classical in
noncomputable def mat (x : G) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  if hx : x ∈ H then (c.ρ ⟨x, hx⟩ : Matrix (Fin 4) (Fin 4) (ZMod 2)) else 1

open Classical in
noncomputable def vec (x : G) : Fin 4 → ZMod 2 :=
  if hx : x ∈ T then Multiplicative.toAdd (c.ψ ⟨x, hx⟩) else 0

theorem mat_of_mem {x : G} (hx : x ∈ H) :
    c.mat x = (c.ρ ⟨x, hx⟩ : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  dite_eq_left hx

theorem vec_of_mem {x : G} (hx : x ∈ T) : c.vec x = Multiplicative.toAdd (c.ψ ⟨x, hx⟩) :=
  dite_eq_left hx

theorem mat_mul {x y : G} (hx : x ∈ H) (hy : y ∈ H) : c.mat (x * y) = c.mat x * c.mat y := by
  rw [c.mat_of_mem hx, c.mat_of_mem hy, c.mat_of_mem (H.mul_mem hx hy)]
  have : (⟨x * y, H.mul_mem hx hy⟩ : H) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]
  rfl

theorem mat_one : c.mat 1 = 1 := by
  rw [c.mat_of_mem H.one_mem]
  have : (⟨1, H.one_mem⟩ : H) = 1 := rfl
  rw [this, map_one]
  rfl

theorem mat_inv_mul {x : G} (hx : x ∈ H) : c.mat x⁻¹ * c.mat x = 1 := by
  rw [← c.mat_mul (H.inv_mem hx) hx, inv_mul_cancel, c.mat_one]

theorem mat_mul_inv {x : G} (hx : x ∈ H) : c.mat x * c.mat x⁻¹ = 1 := by
  rw [← c.mat_mul hx (H.inv_mem hx), mul_inv_cancel, c.mat_one]

theorem mat_eq_one_iff {x : G} (hx : x ∈ H) : c.mat x = 1 ↔ x ∈ T := by
  rw [c.mat_of_mem hx]
  refine ⟨fun h => (c.ker_iff ⟨x, hx⟩).1 (Subtype.ext h), fun h => ?_⟩
  rw [(c.ker_iff ⟨x, hx⟩).2 h]
  rfl

theorem exists_mat_eq (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det = 1) :
    ∃ x ∈ H, c.mat x = g := by
  obtain ⟨⟨x, hx⟩, hxg⟩ := c.surj ⟨g, hg⟩
  exact ⟨x, hx, by rw [c.mat_of_mem hx, hxg]⟩

theorem vec_mul {x y : G} (hx : x ∈ T) (hy : y ∈ T) : c.vec (x * y) = c.vec x + c.vec y := by
  rw [c.vec_of_mem hx, c.vec_of_mem hy, c.vec_of_mem (T.mul_mem hx hy)]
  have : (⟨x * y, T.mul_mem hx hy⟩ : T) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem vec_one : c.vec 1 = 0 := by
  rw [c.vec_of_mem T.one_mem]
  have : (⟨1, T.one_mem⟩ : T) = 1 := rfl
  rw [this, map_one, toAdd_one]

theorem eq_of_vec_eq {x y : G} (hx : x ∈ T) (hy : y ∈ T) (h : c.vec x = c.vec y) : x = y := by
  rw [c.vec_of_mem hx, c.vec_of_mem hy] at h
  exact congrArg Subtype.val (c.ψ.injective (Multiplicative.toAdd.injective h))

theorem exists_vec_eq (w : Fin 4 → ZMod 2) : ∃ t ∈ T, c.vec t = w := by
  refine ⟨(c.ψ.symm (Multiplicative.ofAdd w) : G), (c.ψ.symm _).2, ?_⟩
  rw [c.vec_of_mem (c.ψ.symm _).2, Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem vec_z : c.vec z = e0 := by
  rw [c.vec_of_mem c.mem, c.ψ_z]

include c in
theorem conj_mem {x t : G} (hx : x ∈ H) (ht : t ∈ T) : x * t * x⁻¹ ∈ T := by
  have hm : x * t * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx (c.le ht)) (H.inv_mem hx)
  rw [← c.mat_eq_one_iff hm, c.mat_mul (H.mul_mem hx (c.le ht)) (H.inv_mem hx),
    c.mat_mul hx (c.le ht), (c.mat_eq_one_iff (c.le ht)).2 ht, mul_one, c.mat_mul_inv hx]

theorem vec_conj {x t : G} (hx : x ∈ H) (ht : t ∈ T) :
    c.vec (x * t * x⁻¹) = c.mat x *ᵥ c.vec t := by
  rw [c.vec_of_mem (c.conj_mem hx ht), c.mat_of_mem hx, c.vec_of_mem ht]
  exact c.compat ⟨x, hx⟩ ⟨t, ht⟩ (c.conj_mem hx ht)

theorem mem_centralizer_iff {x : G} (hx : x ∈ H) :
    x ∈ Subgroup.centralizer ({z} : Set G) ↔ c.mat x *ᵥ e0 = e0 := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← c.vec_z, ← c.vec_conj hx c.mem]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    have h1 := c.eq_of_vec_eq (c.conj_mem hx c.mem) c.mem h
    calc x * z = x * z * x⁻¹ * x := by rw [inv_mul_cancel_right]
      _ = z * x := by rw [h1]

end NatCoord

theorem nonempty_natCoord {T H : Subgroup G} (hTH : T ≤ H) (hN : NaturalSL T H 4 1) {z : G}
    (hz : z ∈ T) (hz1 : z ≠ 1) : Nonempty (NatCoord T H z) := by
  classical
  obtain ⟨_, e, φ, hcompat⟩ := hN
  let κ : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let μ : SL(4, GaloisField 2 1) →* SL(4, ZMod 2) := SpecialLinearGroup.map κ.toRingHom
  let μ' : SL(4, ZMod 2) →* SL(4, GaloisField 2 1) := SpecialLinearGroup.map κ.symm.toRingHom
  have hμμ' : ∀ g, μ (μ' g) = g := fun g => by
    ext i j
    simp [μ, μ']
  have hμ'μ : ∀ g, μ' (μ g) = g := fun g => by
    ext i j
    simp [μ, μ']
  let ρ₀ : H →* SL(4, ZMod 2) := μ.comp (e.toMonoidHom.comp (QuotientGroup.mk' _))
  have hρ₀ : ∀ h, ρ₀ h = μ (e (QuotientGroup.mk h)) := fun h => rfl
  let ψ₀ : T ≃* Multiplicative (Fin 4 → ZMod 2) :=
    φ.trans (AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => κ.toAddEquiv))
  have hψ₀ : ∀ t, Multiplicative.toAdd (ψ₀ t) = fun i => κ (Multiplicative.toAdd (φ t) i) :=
    fun t => rfl
  have hcompat₀ : ∀ (h : H) (t : T) (hm : (h : G) * t * (h : G)⁻¹ ∈ T),
      Multiplicative.toAdd (ψ₀ ⟨_, hm⟩) =
        (ρ₀ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (ψ₀ t) := by
    intro h t hm
    ext i
    rw [hψ₀, hψ₀, hcompat h t hm, toAdd_ofAdd]
    exact RingHom.map_mulVec κ.toRingHom _ _ i
  have hv : Multiplicative.toAdd (ψ₀ ⟨z, hz⟩) ≠ 0 := by
    intro h0
    apply hz1
    have h1 : ψ₀ ⟨z, hz⟩ = 1 := toAdd_eq_zero.1 h0
    exact congrArg Subtype.val (ψ₀.injective (h1.trans (map_one ψ₀).symm))
  obtain ⟨A, hAA, hAv⟩ := exists_mulVec_eq_e0 hv
  have hdet : A.det = 1 := zmod_two_eq_one_of_mul_self _ (by rw [← det_mul, hAA, det_one])
  let A' : SL(4, ZMod 2) := ⟨A, hdet⟩
  have hinv : ((A'⁻¹ : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * A = 1 :=
    congrArg (fun g : SL(4, ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) (inv_mul_cancel A')
  let σ : (Fin 4 → ZMod 2) ≃+ (Fin 4 → ZMod 2) :=
    { toFun := fun w => A *ᵥ w
      invFun := fun w => A *ᵥ w
      left_inv := fun w => by simp only [mulVec_mulVec, hAA, one_mulVec]
      right_inv := fun w => by simp only [mulVec_mulVec, hAA, one_mulVec]
      map_add' := fun w w' => mulVec_add A w w' }
  refine ⟨{ le := hTH
            ρ := (MulAut.conj A').toMonoidHom.comp ρ₀
            ψ := ψ₀.trans (AddEquiv.toMultiplicative σ)
            ker_iff := fun h => ?_
            surj := fun g => ?_
            compat := fun h t hm => ?_
            mem := hz
            ψ_z := ?_ }⟩
  · show MulAut.conj A' (ρ₀ h) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hρ₀]
    constructor
    · intro h1
      have h2 : e (QuotientGroup.mk h) = 1 := by
        have h3 := congrArg μ' h1
        rwa [hμ'μ, map_one] at h3
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
      exact Subgroup.mem_subgroupOf.1 h2
    · intro h1
      have h3 : (QuotientGroup.mk h : H ⧸ T.subgroupOf H) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)
      rw [h3, map_one, map_one]
  · obtain ⟨q, hq⟩ := e.surjective (μ' ((MulAut.conj A').symm g))
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨h, ?_⟩
    show MulAut.conj A' (ρ₀ h) = g
    rw [hρ₀, hq, hμμ', MulEquiv.apply_symm_apply]
  · show A *ᵥ (Multiplicative.toAdd (ψ₀ ⟨_, hm⟩)) =
      (A * (ρ₀ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) * ((A'⁻¹ : SL(4, ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ (A *ᵥ Multiplicative.toAdd (ψ₀ t))
    rw [hcompat₀ h t hm, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc _ _ A, hinv,
      Matrix.mul_one]
  · exact hAv

end CFSG.CGT.M24S
