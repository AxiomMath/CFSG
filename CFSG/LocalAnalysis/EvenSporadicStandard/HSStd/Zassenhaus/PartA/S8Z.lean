module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Fields2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Fields

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section ZLe

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' →
    K' = K ∨ K' = cj (tG hb a.toPA6.toPA5) K)
  (hne : cj (tG hb a.toPA6.toPA5) K ≠ K)

include hb a hK horb hne

theorem sw_hcomm : ∀ x ∈ K, ∀ y ∈ cj (tG hb a.toPA6.toPA5) K, x * y = y * x := fun x hx y hy =>
  (Subgroup.mem_centralizer_iff.1
    (le_centralizer_of_ne hK (isComponent_cj _ hK) hne.symm hx) y hy).symm

theorem sw_central_cent (k : ↥K) (hk : k ∈ center ↥K) :
    ((k : ↥(Cen a.ub)) : G) ∈
      centralizer ((GorensteinWalter.componentLayerOf (Cen a.ub) : Subgroup G) : Set G) := by
  obtain ⟨-, -, hZ, -⟩ := sw_struct hb a hK horb hne
  have hkcj : (k : ↥(Cen a.ub)) ∈ cj (tG hb a.toPA6.toPA5) K := (hZ k hk).2
  have hkc : ∀ x ∈ K, (k : ↥(Cen a.ub)) * x = x * k := fun x hx =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hk ⟨x, hx⟩)).symm
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro h hh
  rw [componentLayerOf_eq, layer_eq_of_orbit hb a.toPA6.toPA5 hK horb] at hh
  obtain ⟨y, hy, rfl⟩ := hh
  have := centralizes_sup_of_mem (sw_hcomm hb a hK horb hne) k.2 hkcj hkc y hy
  exact (congrArg Subtype.val this).symm

theorem sw_central_mem_F (k : ↥K) (hk : k ∈ center ↥K) :
    ((k : ↥(Cen a.ub)) : G) ∈ Open.pCoreOf 2 (Cen a.ub) :=
  a.CPE ⟨(k : ↥(Cen a.ub)).2, sw_central_cent hb a hK horb hne k hk⟩

theorem sw_Z_le :
    (center ↥(K.map (Cen a.ub).subtype)).map (K.map (Cen a.ub).subtype).subtype ≤
      zpowers a.ub := by
  obtain ⟨-, ⟨eqv⟩, hZ, -⟩ := sw_struct hb a hK horb hne
  obtain ⟨eJ⟩ := s8_J_equiv a.Abar a.eAbar
  let a5 := a.toPA6.toPA5
  let eA : ↥K ⧸ center ↥K ≃* alternatingGroup (Fin 6) :=
    eqv.trans ((JG_equiv hb a5).trans eJ)
  let π : ↥K →* alternatingGroup (Fin 6) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (center ↥K))
  have hπs : Function.Surjective π := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = center ↥K := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have h2 : IsPGroup 2 ↥π.ker := by
    intro x
    have hxc : ((x : ↥K)) ∈ center ↥K := hπker.le x.2
    obtain ⟨n, hn⟩ := pCoreOf_pow _ (sw_central_mem_F hb a hK horb hne (x : ↥K) hxc)
    refine ⟨n, ?_⟩
    exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using hn)))
  have hdvd := card_ker_dvd_two_of_a6 hK.1.1 hπs hπker.le h2
  have hsq : ∀ k : ↥K, k ∈ center ↥K → k * k = 1 := by
    intro k hk
    have hk' : k ∈ π.ker := hπker.ge hk
    have h3 : orderOf (⟨k, hk'⟩ : ↥π.ker) ∣ 2 := (_root_.orderOf_dvd_natCard _).trans hdvd
    have h4 : (⟨k, hk'⟩ : ↥π.ker) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
    have := congrArg (fun x : ↥π.ker => (x : ↥K)) h4
    simpa [pow_two] using this
  rintro g ⟨c, hcc, rfl⟩
  obtain ⟨k0, hk0, hk0c⟩ := c.2
  have hk0c' : ((k0 : ↥(Cen a.ub)) : G) = (c : G) := hk0c
  set k : ↥K := ⟨k0, hk0⟩ with hkdef
  have hkcen : k ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Subgroup.mem_center_iff.1 hcc ⟨((y : ↥K) : ↥(Cen a.ub)).val, ⟨y, y.2, rfl⟩⟩
    have h2 : ((y : ↥K) : ↥(Cen a.ub)).val * (c : G) = (c : G) * ((y : ↥K) : ↥(Cen a.ub)).val :=
      congrArg Subtype.val h1
    apply Subtype.ext; apply Subtype.ext
    show ((y : ↥K) : ↥(Cen a.ub)).val * k0.val = k0.val * ((y : ↥K) : ↥(Cen a.ub)).val
    rw [hk0c']; exact h2
  obtain ⟨htk, hkcj⟩ := hZ k hkcen
  have hgg : ((k : ↥(Cen a.ub)) : G) * ((k : ↥(Cen a.ub)) : G) = 1 :=
    congrArg (fun x : ↥K => ((x : ↥(Cen a.ub)) : G)) (hsq k hkcen)
  have hgt : ((k : ↥(Cen a.ub)) : G) * t = t * ((k : ↥(Cen a.ub)) : G) := by
    have h1 := congrArg Subtype.val htk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 : ((k : ↥(Cen a.ub)) : G)⁻¹ = ((k : ↥(Cen a.ub)) : G) :=
      inv_eq_of_mul_eq_one_right hgg
    rw [h2] at h1
    have h3 : t * ((k : ↥(Cen a.ub)) : G) = ((k : ↥(Cen a.ub)) : G) * t := by
      calc t * ((k : ↥(Cen a.ub)) : G) = (t * ((k : ↥(Cen a.ub)) : G) * t⁻¹) * t := by group
        _ = _ := by rw [show t * ((k : ↥(Cen a.ub)) : G) * t⁻¹ = _ from h1]
    exact h3.symm
  have hcent := sw_central_cent hb a hK horb hne k hkcen
  have hgJ : ∀ j ∈ derivedIn a.Abar, ((k : ↥(Cen a.ub)) : G) * j = j * ((k : ↥(Cen a.ub)) : G) := by
    intro j hj
    have hjE : j ∈ GorensteinWalter.componentLayerOf (Cen a.ub) := a.E₁_le (a.J_E₁ hj)
    exact (Subgroup.mem_centralizer_iff.1 hcent j hjE).symm
  have hV := PA5.cent_t_J hb a5 hgt hgJ
  rw [mem_Vsub_iff hb.t_mul_t (PA5.ub_sq a5) (PA5.t_ub a5 hb)] at hV
  have hcomm_x : ∀ x ∈ K, ((x : ↥(Cen a.ub)) : G) * ((k : ↥(Cen a.ub)) : G) =
      ((k : ↥(Cen a.ub)) : G) * ((x : ↥(Cen a.ub)) : G) := fun x hx =>
    congrArg Subtype.val (congrArg Subtype.val (Subgroup.mem_center_iff.1 hkcen ⟨x, hx⟩))
  have hnot : ¬ ∀ x ∈ K, (x : G) * t = t * (x : G) := by
    intro h
    apply hne
    exact cj_eq_of_commute (tG_mul_tG hb a5) (fun x hx => Subtype.ext (h x hx).symm)
  have hcg : (c : G) = ((k : ↥(Cen a.ub)) : G) := hk0c'.symm
  show (c : G) ∈ zpowers a.ub
  rw [hcg]
  rcases hV with h | h | h | h
  · rw [h]; exact one_mem _
  · exfalso
    apply hnot
    intro x hx
    have := hcomm_x x hx
    rw [h] at this
    exact this
  · rw [h]; exact mem_zpowers _
  · exfalso
    apply hnot
    intro x hx
    have h1 := hcomm_x x hx
    rw [h] at h1
    have hxub : (x : G) * a.ub = a.ub * (x : G) := mem_Cen.1 x.2
    have : ((x : G) * t) * a.ub = (t * (x : G)) * a.ub := by
      calc ((x : G) * t) * a.ub = (x : G) * (t * a.ub) := by rw [mul_assoc]
        _ = (t * a.ub) * (x : G) := h1
        _ = t * (a.ub * (x : G)) := by rw [mul_assoc]
        _ = t * ((x : G) * a.ub) := by rw [hxub]
        _ = (t * (x : G)) * a.ub := by rw [mul_assoc]
    exact mul_right_cancel this

end ZLe

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
