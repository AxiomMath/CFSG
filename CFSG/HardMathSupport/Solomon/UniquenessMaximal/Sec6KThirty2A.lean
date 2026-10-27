module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KThirty2ACore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
public import CFSG.Open.StatedAPI

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open

theorem det_eq_one_of_mem_statedSL {F : Type} [Field F] {g : GL (Fin 3) F}
    (hg : g ∈ StatedSL 3 F) : (g : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem det_eq_one_of_mem_statedSU {F : Type} [Field F] {q : ℕ} {g : GL (Fin 3) F}
    (hg : g ∈ StatedSU 3 q F) : (g : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hg

@[expose] noncomputable def projHom {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F)) :
    StatedProj H →* Matrix.ProjGenLinGroup (Fin 3) F :=
  QuotientGroup.lift _ ((Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _).comp H.subtype) (by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ha)

theorem projHom_mk {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F)) (a : H) :
    projHom H (QuotientGroup.mk a) = Matrix.ProjGenLinGroup.mk (a : GL (Fin 3) F) := rfl

theorem projHom_injective {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F)) :
    Function.Injective (projHom H) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [projHom_mk, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at ha
    exact (QuotientGroup.eq_one_iff a).2 ha

theorem exists_cube_root_of_card_mod_three {F : Type} [Field F] [Finite F]
    (h : Nat.card F % 3 = 1) : ∃ τ : F, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨x, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val this
  · intro h1
    have : x = 1 := Units.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem isLThreeEps_data {Y : Type} [Group Y] (h : IsLThreeEps Y) :
    ∃ (F : Type) (_ : Field F) (H : Subgroup (GL (Fin 3) F)) (τ : F), τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) ∧ Nonempty (Y ≃* StatedProj H) := by
  rcases h with ⟨F, _, _, hF, θ⟩ | ⟨F, _, _, q, hF, hq, θ⟩
  · obtain ⟨τ, hτ, hτ1⟩ := exists_cube_root_of_card_mod_three hF
    exact ⟨F, inferInstance, StatedSL 3 F, τ, hτ, hτ1, fun g hg => det_eq_one_of_mem_statedSL hg, θ⟩
  · have hF' : Nat.card F % 3 = 1 := by
      rw [hF, Nat.pow_mod, hq]
    obtain ⟨τ, hτ, hτ1⟩ := exists_cube_root_of_card_mod_three hF'
    exact ⟨F, inferInstance, StatedSU 3 q F, τ, hτ, hτ1, fun g hg => det_eq_one_of_mem_statedSU hg,
      θ⟩

theorem rank_le_nine_of_isLThreeEps (K : Type) [Group K] [Finite K]
    (h : IsLThreeEps (K ⧸ GLAPPrimeCore 3 K)) :
    ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  intro E hE
  obtain ⟨F, _, H, τ, hτ, hτ1, hdet, ⟨θ⟩⟩ := isLThreeEps_data h
  let ρ : E →* Matrix.ProjGenLinGroup (Fin 3) F :=
    ((projHom H).comp θ.toMonoidHom).comp
      ((QuotientGroup.mk' (GLAPPrimeCore 3 K)).comp E.subtype)
  have hker : ∀ x : E, QuotientGroup.mk' (GLAPPrimeCore 3 K) (x : K) = 1 → x = 1 := by
    intro x hx
    by_contra hx1
    have hxO : (x : K) ∈ GLAPPrimeCore 3 K := (QuotientGroup.eq_one_iff _).1 hx
    have h3 : x ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    have ho : orderOf x = 3 := orderOf_eq_prime h3 hx1
    have ho' : orderOf (x : K) = 3 := by rw [Subgroup.orderOf_coe, ho]
    have hdvd : 3 ∣ Nat.card (GLAPPrimeCore 3 K) := by
      have := orderOf_dvd_natCard (⟨(x : K), hxO⟩ : GLAPPrimeCore 3 K)
      rwa [Subgroup.orderOf_mk, ho'] at this
    have hcop := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
      Nat.prime_three K
    exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) hdvd) (by norm_num)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hker
    have h1 := projHom_injective H
    have h2 : θ ((QuotientGroup.mk' (GLAPPrimeCore 3 K)) (x : K)) = 1 :=
      h1 (by rw [map_one]; exact hx)
    exact θ.injective (by rw [h2, map_one])
  refine K32A.card_le_nine hρ hτ hτ1 (fun x y => ?_) (fun x => Subtype.ext (hE.2 x x.2)) fun x => ?_
  · exact hE.1.is_comm.comm x y
  · obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk' (GLAPPrimeCore 3 K) (x : K)))
    refine ⟨(a : GL (Fin 3) F), hdet _ a.2, ?_⟩
    show _ = projHom H
      (θ (QuotientGroup.mk' (GLAPPrimeCore 3 K) (x : K)))
    rw [← ha]
    rfl

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
