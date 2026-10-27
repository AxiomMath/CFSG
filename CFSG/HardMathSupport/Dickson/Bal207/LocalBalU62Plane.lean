module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Base

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

@[expose] def planeVec (i j n : Fin 6) (α β : Kˣ) : Fin 6 → Kˣ :=
  Pi.mulSingle i α * Pi.mulSingle j β * Pi.mulSingle n (α * β)⁻¹

theorem prod_planeVec (i j n : Fin 6) (α β : Kˣ) : ∏ l, planeVec i j n α β l = 1 := by
  simp only [planeVec, Pi.mul_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

theorem planeVec_mul (i j n : Fin 6) (α β α' β' : Kˣ) :
    planeVec i j n (α * α') (β * β') = planeVec i j n α β * planeVec i j n α' β' := by
  unfold planeVec
  simp only [mul_inv, Pi.mulSingle_mul]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem planeVec_one (i j n : Fin 6) : planeVec i j n (1 : Kˣ) 1 = 1 := by
  unfold planeVec
  simp

theorem planeVec_i {i j n : Fin 6} (hij : i ≠ j) (hin : i ≠ n) (α β : Kˣ) :
    planeVec i j n α β i = α := by
  simp [planeVec, Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_of_ne hin]

theorem planeVec_j {i j n : Fin 6} (hij : i ≠ j) (hjn : j ≠ n) (α β : Kˣ) :
    planeVec i j n α β j = β := by
  simp [planeVec, Pi.mulSingle_eq_of_ne hij.symm, Pi.mulSingle_eq_of_ne hjn]

theorem planeVec_other {i j n l : Fin 6} (hi : l ≠ i) (hj : l ≠ j) (hn : l ≠ n) (α β : Kˣ) :
    planeVec i j n α β l = 1 := by
  simp [planeVec, Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hn]

theorem exists_fourth (i j n : Fin 6) : ∃ l : Fin 6, l ≠ i ∧ l ≠ j ∧ l ≠ n := by
  revert i j n
  decide

section Plane

variable (h : UnitaryFieldData 2 1 K)

@[expose] noncomputable def planeHom (i j n : Fin 6) : Kˣ × Kˣ →* primeFormP h (idGram K 6) where
  toFun p := diagP h (planeVec i j n p.1 p.2) (prod_planeVec i j n p.1 p.2)
  map_one' := by
    have := diagP_one h (K := K)
    simp only [Prod.fst_one, Prod.snd_one]
    rw [← this]
    congr 1
    exact planeVec_one i j n
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [diagP_mul]
    congr 1
    exact planeVec_mul i j n _ _ _ _

theorem planeHom_apply (i j n : Fin 6) (α β : Kˣ) :
    planeHom h i j n (α, β) = diagP h (planeVec i j n α β) (prod_planeVec i j n α β) :=
  rfl

@[expose] noncomputable def plane (i j n : Fin 6) : Subgroup (primeFormP h (idGram K 6)) :=
  (planeHom h i j n).range

theorem planeHom_injective {i j n : Fin 6} (hij : i ≠ j) (hin : i ≠ n) (hjn : j ≠ n) :
    Function.Injective (planeHom h i j n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨α, β⟩ hp
  rw [MonoidHom.mem_ker, planeHom_apply, diagP_eq_one_iff] at hp
  obtain ⟨c, hc⟩ := hp
  obtain ⟨l, hli, hlj, hln⟩ := exists_fourth i j n
  have hc1 : c = 1 := by
    have := hc l
    rw [planeVec_other hli hlj hln] at this
    exact this.symm
  have hα : α = 1 := by
    have := hc i
    rwa [planeVec_i hij hin, hc1] at this
  have hβ : β = 1 := by
    have := hc j
    rwa [planeVec_j hij hjn, hc1] at this
  rw [hα, hβ]
  exact Subgroup.one_mem _

theorem card_plane {i j n : Fin 6} (hij : i ≠ j) (hin : i ≠ n) (hjn : j ≠ n) :
    Nat.card (plane h i j n) = 3 ^ 2 := by
  haveI := h.finite
  have e := Nat.card_congr (MonoidHom.ofInjective (planeHom_injective h hij hin hjn)).toEquiv
  rw [plane, ← e, Nat.card_prod, u62lb_card_units h]
  norm_num

theorem plane_pow_three (i j n : Fin 6) (m : plane h i j n) : m ^ 3 = 1 := by
  obtain ⟨m, p, rfl⟩ := m
  apply Subtype.ext
  change (planeHom h i j n p) ^ 3 = 1
  rw [← map_pow]
  have : p ^ 3 = 1 :=
    Prod.ext (by simpa using u62lb_units_pow_three h p.1)
      (by simpa using u62lb_units_pow_three h p.2)
  rw [this, map_one]

theorem mem_plane_iff (i j n : Fin 6) (m : primeFormP h (idGram K 6)) :
    m ∈ plane h i j n ↔ ∃ α β : Kˣ,
      m = diagP h (planeVec i j n α β) (prod_planeVec i j n α β) := by
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    exact ⟨α, β, rfl⟩
  · rintro ⟨α, β, rfl⟩
    exact ⟨(α, β), rfl⟩

theorem diagP_comm (μ ν : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) (hν : ∏ i, ν i = 1) :
    diagP h μ hμ * diagP h ν hν = diagP h ν hν * diagP h μ hμ := by
  rw [diagP_mul, diagP_mul]
  congr 1
  exact mul_comm μ ν

theorem u62lb_finite : Finite (primeFormP h (idGram K 6)) := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      Units.val_injective
  infer_instance

@[expose] def TorusInv (N : Subgroup (primeFormP h (idGram K 6))) : Prop :=
  ∀ (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1), ∀ x ∈ N, diagP h μ hμ * x * (diagP h μ hμ)⁻¹ ∈ N

@[expose] def NoCommutingPlane (N : Subgroup (primeFormP h (idGram K 6))) : Prop :=
  ∃ i j n : Fin 6, i ≠ j ∧ i ≠ n ∧ j ≠ n ∧ ∀ m ∈ plane h i j n, m ≠ 1 →
    ¬ N ≤ Subgroup.centralizer ({m} : Set (primeFormP h (idGram K 6)))

end Plane

end CFSG.HardMathSupport.Dickson.Bal207

end
