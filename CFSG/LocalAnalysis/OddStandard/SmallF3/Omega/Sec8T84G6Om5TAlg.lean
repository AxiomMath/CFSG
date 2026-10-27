module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Om5TGeo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCComp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec8t84g6t_not_five_dvd (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {z : ProjOrth Q}
    (hz : z ∈ omegaProj hQ) (hzz : z * z = 1) (hz1 : z ≠ 1) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set (ProjOrth Q))) := by
  rcases natCard_centralizer_involution_five hQ hdim hσ hzz hz1 with
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
  · rw [h]; omega
  · rw [h]; omega
  · exfalso
    rcases (hasType_mem_omegaProj_iff_five hQ hdim ht (Or.inr rfl)).mp hz with h | h
    · exact absurd h.2 (by decide)
    · exact absurd h.1 (by decide)
  · exfalso
    rcases (hasType_mem_omegaProj_iff_five hQ hdim ht (Or.inl rfl)).mp hz with h | h
    · exact absurd h.1 (by decide)
    · exact absurd h.2 (by decide)

private theorem sec8t84g6t_type_of_five_dvd (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {y : ProjOrth Q}
    (hyy : y * y = 1) (hy1 : y ≠ 1)
    (h5 : 5 ∣ Nat.card (Subgroup.centralizer ({y} : Set (ProjOrth Q)))) : HasType y 4 (-1) := by
  rcases natCard_centralizer_involution_five hQ hdim hσ hyy hy1 with
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | ⟨-, h⟩
  · rw [h] at h5; omega
  · rw [h] at h5; omega
  · exact ht
  · rw [h] at h5; omega

private theorem sec8t84g6t_even_orderOf {H : Type*} [Group H] (ε : H →* (ZMod 3)ˣ) {h : H}
    (hε : ε h = -1) : Even (orderOf h) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h1 : ε h ^ orderOf h = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hε, hodd.neg_one_pow] at h1
  exact absurd h1 (by decide)

theorem sec8t84g6t_core (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hσ : quadSign Q = 1) (hsimple : IsSimpleGroup ↥(omegaProj hQ)) {y : ProjOrth Q}
    (hyy : y * y = 1) {B : Subgroup (ProjOrth Q)}
    (hB : IsComponentIn B (omegaProj hQ ⊓ Subgroup.centralizer ({y} : Set (ProjOrth Q))))
    (hL : IsL29 B) :
    ∃ u ∈ omegaProj hQ ⊓ Subgroup.centralizer ({y} : Set (ProjOrth Q)), u * u = 1 ∧
      ∀ a ∈ B, ∀ c ∈ Subgroup.centralizer (B : Set (ProjOrth Q)), u ≠ a * c := by
  haveI : Finite (ProjOrth Q) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_projOrth_five hQ hdim]; norm_num)
  obtain ⟨m, hm, hBcard⟩ := sec63PC_card_of_isL29 hL
  have h5 : 5 ∣ Nat.card B := by
    rw [hBcard]
    exact Dvd.dvd.mul_right (by norm_num) m
  by_cases hy1 : y = 1
  · exfalso
    subst hy1
    have hD : omegaProj hQ ⊓ Subgroup.centralizer ({1} : Set (ProjOrth Q)) = omegaProj hQ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    rw [hD] at hB
    have hBeq : B = omegaProj hQ :=
      sec63PC_component_eq (H := omegaProj hQ) (L := omegaProj hQ) le_rfl
        (fun h _ x hx => (omegaProj_normal hQ).conj_mem x hx h) ⟨0, by simp⟩ hsimple hB
    rw [hBeq, natCard_omegaProj_five hQ hdim] at hBcard
    obtain ⟨k, rfl⟩ := hm
    omega
  · have hBD : B ≤ omegaProj hQ ⊓ Subgroup.centralizer ({y} : Set (ProjOrth Q)) := hB.1
    have hBC : B ≤ Subgroup.centralizer ({y} : Set (ProjOrth Q)) := hBD.trans inf_le_right
    have h5C : 5 ∣ Nat.card (Subgroup.centralizer ({y} : Set (ProjOrth Q))) :=
      h5.trans (Subgroup.card_dvd_of_le hBC)
    have hy4 : HasType y 4 (-1) := sec8t84g6t_type_of_five_dvd hQ hdim hσ hyy hy1 h5C
    obtain ⟨ε, u, hu, huu, huΩ, hεu⟩ := sec8t84g6t_outer hQ hdim hy4
    have huD : u ∈ omegaProj hQ ⊓ Subgroup.centralizer ({y} : Set (ProjOrth Q)) :=
      Subgroup.mem_inf.mpr ⟨huΩ, hu⟩
    refine ⟨u, huD, huu, ?_⟩
    intro a ha c hc hac
    haveI : Group.IsPerfect ↥B := hB.isQuasisimple.1
    have hεa : ε ⟨a, hBC ha⟩ = 1 := by
      let ψ : ↥B →* (ZMod 3)ˣ := ε.comp (Subgroup.inclusion hBC)
      haveI : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
      haveI : Subsingleton ↥ψ.range := inferInstance
      have h1 : (⟨ψ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩ : ↥ψ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h1
    have hcD : c ∈ omegaProj hQ ⊓ Subgroup.centralizer ({y} : Set (ProjOrth Q)) := by
      have hcu : c = a⁻¹ * u := by rw [hac]; group
      rw [hcu]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBD ha)) huD
    have hcC : c ∈ Subgroup.centralizer ({y} : Set (ProjOrth Q)) := (Subgroup.mem_inf.mp hcD).2
    have hεc : ε ⟨c, hcC⟩ = -1 := by
      have h1 : (⟨u, hu⟩ : ↥(Subgroup.centralizer ({y} : Set (ProjOrth Q)))) =
          ⟨a, hBC ha⟩ * ⟨c, hcC⟩ := Subtype.ext hac
      rw [h1, map_mul, hεa, one_mul] at hεu
      exact hεu
    have heven : Even (orderOf c) := by
      have h1 : orderOf (⟨c, hcC⟩ : ↥(Subgroup.centralizer ({y} : Set (ProjOrth Q)))) =
          orderOf c := Subgroup.orderOf_mk _ _
      rw [← h1]
      exact sec8t84g6t_even_orderOf ε hεc
    have hn : orderOf c ≠ 0 := (orderOf_pos c).ne'
    have hzord : orderOf (c ^ (orderOf c / 2)) = 2 :=
      orderOf_pow_orderOf_div hn (even_iff_two_dvd.mp heven)
    have hzz : c ^ (orderOf c / 2) * c ^ (orderOf c / 2) = 1 := by
      have h := pow_orderOf_eq_one (c ^ (orderOf c / 2))
      rw [hzord, pow_two] at h
      exact h
    have hz1 : c ^ (orderOf c / 2) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzord
      omega
    have hzΩ : c ^ (orderOf c / 2) ∈ omegaProj hQ :=
      Subgroup.pow_mem _ (Subgroup.mem_inf.mp hcD).1 _
    have hzB : c ^ (orderOf c / 2) ∈ Subgroup.centralizer (B : Set (ProjOrth Q)) :=
      Subgroup.pow_mem _ hc _
    have hBz : B ≤ Subgroup.centralizer ({c ^ (orderOf c / 2)} : Set (ProjOrth Q)) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzB b hb
    exact sec8t84g6t_not_five_dvd hQ hdim hσ hzΩ hzz hz1 (h5.trans (Subgroup.card_dvd_of_le hBz))

end CFSG.OddStandard.SmallF3.Omega
