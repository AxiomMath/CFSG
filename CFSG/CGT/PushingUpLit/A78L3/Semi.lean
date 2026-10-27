module

public import CFSG.CGT.PushingUpLit.A78L3.Nat
public import CFSG.CGT.PushingUpLit.BHS.SL2Normalizer

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.QuasithinUnique.Setup.Offender (IsSemilinearWith)
open CFSG.QuasithinUnique.Setup.Campbell (slPerm)
open Matrix

theorem conj_mem_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {x h : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) (hh : h ∈ H) : x * h * x⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 hx h).1 hh

namespace NatCoord

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F] (D : NatCoord G L V F)

@[expose] noncomputable def sec (w : Fin 2 → F) : G := (D.κ_surj w).choose

theorem sec_mem (w : Fin 2 → F) : D.sec w ∈ V := (D.κ_surj w).choose_spec.1

theorem κ_sec (w : Fin 2 → F) : D.κ (D.sec w) = w := (D.κ_surj w).choose_spec.2

theorem sec_κ {v : G} (hv : v ∈ V) : D.sec (D.κ v) = v :=
  D.κ_inj _ (D.sec_mem _) v hv (D.κ_sec _)

include D in
theorem le_normalizer : L ≤ Subgroup.normalizer (V : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => D.norm l hl v hv, fun hv => ?_⟩
  have := D.norm l⁻¹ (inv_mem hl) _ hv
  simpa [mul_assoc] using this

@[expose] noncomputable def act (x : G) (w : Fin 2 → F) : Fin 2 → F := D.κ (x * D.sec w * x⁻¹)

variable {D}

theorem act_κ {x v : G} (hv : v ∈ V) : D.act x (D.κ v) = D.κ (x * v * x⁻¹) := by
  rw [act, D.sec_κ hv]

theorem act_add {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (w w' : Fin 2 → F) :
    D.act x (w + w') = D.act x w + D.act x w' := by
  have hs : w + w' = D.κ (D.sec w * D.sec w') := by
    rw [D.κ_mul _ (D.sec_mem w) _ (D.sec_mem w'), D.κ_sec, D.κ_sec]
  have e : x * (D.sec w * D.sec w') * x⁻¹ = (x * D.sec w * x⁻¹) * (x * D.sec w' * x⁻¹) := by
    group
  rw [hs, act_κ (mul_mem (D.sec_mem w) (D.sec_mem w')), e,
    D.κ_mul _ (conj_mem_of_mem_normalizer hx (D.sec_mem w)) _
      (conj_mem_of_mem_normalizer hx (D.sec_mem w'))]
  rfl

theorem act_mul {x y : G} (hy : y ∈ Subgroup.normalizer (V : Set G)) (w : Fin 2 → F) :
    D.act (x * y) w = D.act x (D.act y w) := by
  conv_lhs => rw [← D.κ_sec w]
  conv_rhs => rw [← D.κ_sec w]
  rw [act_κ (D.sec_mem w), act_κ (D.sec_mem w),
    act_κ (conj_mem_of_mem_normalizer hy (D.sec_mem w))]
  congr 1
  group

theorem act_one (w : Fin 2 → F) : D.act 1 w = w := by
  rw [act, one_mul, inv_one, mul_one, D.κ_sec]

theorem act_of_mem_L {l : G} (hl : l ∈ L) (w : Fin 2 → F) :
    D.act l w = (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w := by
  rw [act, D.conj l hl _ (D.sec_mem w), D.κ_sec]

theorem act_inv_act {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (w : Fin 2 → F) :
    D.act x⁻¹ (D.act x w) = w := by
  rw [← act_mul hx, inv_mul_cancel, act_one]

theorem act_act_inv {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (w : Fin 2 → F) :
    D.act x (D.act x⁻¹ w) = w := by
  rw [← act_mul (inv_mem hx), mul_inv_cancel, act_one]

variable (D) in
@[expose] noncomputable def actPerm (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    Equiv.Perm (Fin 2 → F) where
  toFun := D.act x
  invFun := D.act x⁻¹
  left_inv w := act_inv_act hx w
  right_inv w := act_act_inv hx w

theorem act_twist {x l : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hl : l ∈ L) (w : Fin 2 → F) :
    D.act x ((D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w) =
      (D.ρ (x * l * x⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ D.act x w := by
  have hxl : x * l * x⁻¹ ∈ L := conj_mem_of_mem_normalizer hxL hl
  rw [← act_of_mem_L hl, ← act_of_mem_L hxl, ← act_mul (D.le_normalizer hl),
    ← act_mul hxV]
  congr 1
  group

theorem exists_semilinear [Finite F] {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    ∃ σ : F ≃+* F, IsSemilinearWith (D.actPerm x hxV) σ := by
  refine BHS.exists_isSemilinearWith_of_normalizes (D.actPerm x hxV)
    (fun w w' => act_add hxV w w') fun g => ?_
  obtain ⟨l, hl, rfl⟩ := D.ρ_surj g
  have hxl : x⁻¹ * l * x⁻¹⁻¹ ∈ L := conj_mem_of_mem_normalizer (inv_mem hxL) hl
  refine ⟨D.ρ (x⁻¹ * l * x⁻¹⁻¹), Equiv.ext fun w => ?_⟩
  show D.act x⁻¹ ((D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.act x w) =
    (D.ρ (x⁻¹ * l * x⁻¹⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ w
  rw [act_twist (inv_mem hxL) (inv_mem hxV) hl, act_inv_act hxV]

theorem act_of_mem_centralizer {x : G} (hx : x ∈ Subgroup.centralizer (V : Set G))
    (w : Fin 2 → F) : D.act x w = w := by
  rw [act]
  have h1 := Subgroup.mem_centralizer_iff.1 hx _ (D.sec_mem w)
  rw [show x * D.sec w * x⁻¹ = D.sec w by rw [← h1]; group, D.κ_sec]

theorem mem_centralizer_of_act {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (h : ∀ w, D.act x w = w) : x ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := h (D.κ v)
  rw [act_κ hv] at h1
  have h2 := D.κ_inj _ (conj_mem_of_mem_normalizer hx hv) v hv h1
  calc v * x = x * v * x⁻¹ * x := by rw [h2]
    _ = x * v := by group

end NatCoord

end CFSG.CGT.PushingUpLit.A78L3
