module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UThompson
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UZ2
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8C

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

@[expose] def Dsub (z : G) (ιd : Perm (Fin 10) →* G) : Subgroup G :=
  closure ({z, gElt ιd} : Set G)

@[expose] noncomputable def Qsub (ι : Perm (Fin 10) →* G)
    (P : Subgroup (Perm (Fin 8))) : Subgroup G :=
  P.map (ι.comp liftS8)

theorem injective_comp_liftS8 (F : UFrame z ι ιd) : Function.Injective (ι.comp liftS8) := by
  intro a b h
  exact liftS8_injective (F.cent.inj h)

theorem comm_Dsub_Qsub (F : UFrame z ι ιd) (P : Subgroup (Perm (Fin 8))) :
    ∀ d ∈ Dsub z ιd, ∀ q ∈ Qsub ι P, d * q = q * d := by
  intro d hd q hq
  rw [Qsub] at hq
  obtain ⟨p, _hp, rfl⟩ := Subgroup.mem_map.mp hq
  exact F.comm_D_sigma hd p

theorem Dsub_inf_Qsub (F : UFrame z ι ιd) (P : Subgroup (Perm (Fin 8))) :
    Dsub z ιd ⊓ Qsub ι P = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  obtain ⟨hd, hqQ⟩ := Subgroup.mem_inf.mp hq
  rw [Qsub] at hqQ
  obtain ⟨p, _hp, hpq⟩ := Subgroup.mem_map.mp hqQ
  exact F.eq_one_of_mem_D_of_eq_sigma hd hpq.symm

theorem card_Dsub (F : UFrame z ι ιd) : Nat.card (Dsub z ιd) = 8 := by
  simpa only [Dsub] using F.d8.card

theorem isPGroup_Dsub (F : UFrame z ι ιd) : IsPGroup 2 (Dsub z ιd) := by
  refine IsPGroup.of_card (n := 3) ?_
  rw [card_Dsub F]
  norm_num

theorem card_Qsub (F : UFrame z ι ιd) (P : Subgroup (Perm (Fin 8))) :
    Nat.card (Qsub ι P) = Nat.card P := by
  simpa only [Qsub] using Subgroup.card_map_of_injective (injective_comp_liftS8 F)

theorem isPGroup_Qsub (F : UFrame z ι ιd) {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P) :
    IsPGroup 2 (Qsub ι P) := by
  change IsPGroup 2 (P.map (ι.comp liftS8))
  exact hP.map (ι.comp liftS8)

theorem card_Tstar (F : UFrame z ι ιd) {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P)
    (hc : Nat.card P = 2 ^ 7) : Nat.card (Dsub z ιd ⊔ Qsub ι P : Subgroup G) = 2 ^ 10 := by
  rw [card_sup_of_commute (comm_Dsub_Qsub F P) (Dsub_inf_Qsub F P),
    card_Dsub F, card_Qsub F P, hc]
  norm_num

theorem normalizer_Tstar_le (F : UFrame z ι ιd) {P : Subgroup (Perm (Fin 8))}
    (h01 : swap 0 1 ∈ P) (h23 : swap 2 3 ∈ P) (h45 : swap 4 5 ∈ P) (h67 : swap 6 7 ∈ P)
    (hZ : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄') :
    normalizer ((Dsub z ιd ⊔ Qsub ι P : Subgroup G) : Set G) ≤
      centralizer ({z * ι τ₀} : Set G) := by
  have hT : ∀ t ∈ (Dsub z ιd ⊔ Qsub ι P : Subgroup G),
      ∃ d ∈ Dsub z ιd, ∃ q ∈ Qsub ι P, t = d * q :=
    fun t ht => (mem_sup_iff_of_commute (comm_Dsub_Qsub F P)).mp ht
  have ha : z ∈ Dsub z ιd := by simpa only [Dsub] using D8Rel.z_mem z (gElt ιd)
  have hb : gElt ιd ∈ Dsub z ιd := by simpa only [Dsub] using D8Rel.g_mem z (gElt ιd)
  have hab : ⁅z, gElt ιd⁆ = z * ι τ₀ := (F.d8).commutator_z_g
  have hx : z * ι τ₀ ≠ 1 := (F.d8).x_ne
  have hD2 : ∀ d₁ ∈ Dsub z ιd, ∀ d₂ ∈ Dsub z ιd,
      ⁅d₁, d₂⁆ = 1 ∨ ⁅d₁, d₂⁆ = z * ι τ₀ :=
    fun d₁ h₁ d₂ h₂ => (F.d8).commutator_mem h₁ h₂
  have hxD : ∀ d ∈ Dsub z ιd, d * (z * ι τ₀) = (z * ι τ₀) * d :=
    fun d hd => (F.d8).x_comm hd
  have hQ := hQ_of_sylow h01 h23 h45 h67 hZ (ι.comp liftS8) (injective_comp_liftS8 F)
  exact normalizer_le_centralizer le_sup_left le_sup_right hT (comm_Dsub_Qsub F P)
    ha hb hab hx hD2 hxD hQ

@[expose] noncomputable def signMap (φ : Perm (Fin 8) →* G) (hφ : Function.Injective φ)
    (P : Subgroup (Perm (Fin 8))) : P.map φ →* ℤˣ :=
  (sign.comp P.subtype).comp ((P.equivMapOfInjective φ hφ).symm : P.map φ ≃* P).toMonoidHom

theorem signMap_apply (φ : Perm (Fin 8) →* G) (hφ : Function.Injective φ)
    (P : Subgroup (Perm (Fin 8))) {p : Perm (Fin 8)} (hp : p ∈ P) :
    signMap φ hφ P ⟨φ p, Subgroup.mem_map_of_mem φ hp⟩ = sign p := by
  have h1 : P.equivMapOfInjective φ hφ ⟨p, hp⟩ =
      ⟨φ p, Subgroup.mem_map_of_mem φ hp⟩ := Subtype.ext rfl
  have h2 : (P.equivMapOfInjective φ hφ).symm ⟨φ p, Subgroup.mem_map_of_mem φ hp⟩ =
      ⟨p, hp⟩ := by
    rw [← h1, MulEquiv.symm_apply_apply]
  simp only [signMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2, Subgroup.coe_subtype]

end CFSG.OddStandard.AltStdSec.SwapPartner
