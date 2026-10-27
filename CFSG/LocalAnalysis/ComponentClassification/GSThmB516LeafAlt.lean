module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafAltS
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSp4C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafLin

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Pump516

theorem cf516AltRow : CF516AltRow := by
  intro S _ _ n hn ⟨θ⟩ hs hna _ σ P hP p f hp hp2 hf hPm t htP ht2 J hJC hJ hJm _ _ JB hJBJP
    _ hJBs
  have : IsSimpleGroup S := hs
  have hX4 := l4u4_card_lower hp2 hPm
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  by_cases hn6 : n = 6
  ·
    subst hn6
    have hS : Nat.card S = 360 := by
      rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      rfl
    have hXP : Nat.card (P ⧸ pPrimeCore 2 P) ≤ Nat.card S :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans
        (Subgroup.card_le_card_group P)
    have hlow : 729 * 8 * 26 * 80 ≤
        (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) := by
      have h6 : 3 ^ 6 ≤ (p ^ f) ^ 6 := Nat.pow_le_pow_left hq3 6
      have h2 : 3 ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
      have h3 : 3 ^ 3 ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
      have h4 : 3 ^ 4 ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by simpa using h6) (by omega))
        (by omega)) (by omega)
    omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have hσ1 := hP.ne_one
  obtain ⟨hP', -⟩ := hP.map θ
  obtain ⟨τ, hτ⟩ := hbij.2 (MulAut.congr θ σ)
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => hP.1 y
  have hττ : τ * τ = 1 := by
    apply hbij.1
    rw [map_mul, hτ, ← map_mul, hσ2, map_one, map_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hσ1
    apply (MulAut.congr θ).injective
    rw [← hτ, map_one, map_one]
  rw [← hτ] at hP'
  obtain ⟨-, hPa, -⟩ := alt_fixed_component_structure hττ hτ1 hP'.2.1 hP'.2.2.1
  have hZ := center_eq_bot_of_nonabelian hna
  have hct := orderOf_conj_eq_two hZ ht2
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hJα : J ≤ fixedSubgroup (MulAut.conj t) := by
    rw [fixedSubgroup_conj]
    exact hJC
  have hJα' : IsPComponent 2 (J.subgroupOf (fixedSubgroup (MulAut.conj t))) := by
    rw [fixedSubgroup_conj]
    exact hJ
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht2
      omega
    apply ht1
    refine mem_bot.mp (hZ ▸ mem_center_iff.mpr fun g => ?_)
    have hg : g ∈ centralizer ({t} : Set S) := hJC (hJt ▸ mem_top g)
    exact (mem_centralizer_singleton_iff.mp hg)
  have hJPF : ProperFixedComponent (MulAut.conj t) J :=
    ⟨fun y => by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [htt]; group, hJα, hJα', hJtop⟩
  obtain ⟨hJ', -⟩ := hJPF.map θ
  set u : Perm (Fin n) := ((θ t : alternatingGroup (Fin n)) : Perm (Fin n)) with hudef
  have hcu : MulAut.congr θ (MulAut.conj t) = MulAut.conjNormal u := by
    rw [congr_conj]
    exact MulEquiv.ext fun x => Subtype.ext rfl
  have huu : u * u = 1 := by
    rw [hudef, ← Subgroup.coe_mul, ← map_mul, htt, map_one]
    rfl
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : θ t = 1 := Subtype.ext h
    rw [← map_one θ] at h1
    have := θ.injective h1
    rw [this, orderOf_one] at ht2
    omega
  rw [hcu] at hJ'
  obtain ⟨hJs, -, hJb⟩ := alt_fixed_component_structure huu hu1 hJ'.2.1 hJ'.2.2.1
  have hJs' : IsSimpleGroup J :=
    (J.equivMapOfInjective θ.toMonoidHom θ.injective).isSimpleGroup
  have hJnt : Nontrivial (J ⧸ pPrimeCore 2 J) :=
    (Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) hJm).toNontrivial
  have hO : oddCoreIn J = ⊥ := by
    unfold oddCoreIn
    rw [pPrimeCore_eq_bot_of_simple hJnt, Subgroup.map_bot]
  have hJP : J ≤ P := by
    rw [hO, sup_bot_eq] at hJBs
    exact hJBs.trans (hJBJP.trans inf_le_right)
  apply hτ1
  refine Equiv.ext fun a => ?_
  rw [Perm.one_apply]
  by_contra ha
  have htP' : θ t ∈ P.map θ.toMonoidHom := mem_map_of_mem _ htP
  have hua : u a = a := hPa _ htP' a ha
  obtain ⟨x, hx, hxa⟩ := hJb a hua
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  exact hxa (hPa _ (mem_map_of_mem _ (hJP hy)) a ha)

end CFSG.ComponentClassification.GSThmB
