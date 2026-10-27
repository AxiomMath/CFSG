module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockBase
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Lift

section Cext

theorem no_odd_ker {P : Type} [Group P] (hP : commutator P = ⊤)
    {π : P →* ↥(alternatingGroup (Fin 5))} (hπs : Function.Surjective π)
    (hπk : π.ker ≤ Subgroup.center P) (hodd : Odd (Nat.card ↥π.ker)) : π.ker = ⊥ := by
  have h := CFSG.ComponentClassification.RankTwoAlt.card_ker_dvd_two_five hP hπs hπk
  exact Subgroup.eq_bot_of_card_eq _
    (CFSG.ComponentClassification.RankTwoAlt.eq_one_of_dvd_two_of_odd h hodd)

theorem a5_no_odd_cext_aux {G : Type} [Group G] [Finite G]
    (hG : commutator G = ⊤) (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hodd : Odd (Nat.card ↥Z))
    (hq : Nonempty ((G ⧸ Z) ≃* ↥(alternatingGroup (Fin 5)))) : Z = ⊥ := by
  obtain ⟨e⟩ := hq
  let π : G →* ↥(alternatingGroup (Fin 5)) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : π.ker = Z := by
    ext x
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have := no_odd_ker hG hπs (hker ▸ hZ) (hker ▸ hodd)
  rwa [hker] at this

end Cext

section Lift

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem a5_lift_aux (h : Setup28 W K S)
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7)))
    {B : Subgroup ↥(alternatingGroup (Fin 7))}
    (hB : Nonempty (↥B ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ Ik : Subgroup X, Ik ≤ K ∧ (∀ k : ↥K, (k : X) ∈ Ik → piOf e k ∈ B) ∧
      (∀ b ∈ B, ∃ k : ↥K, (k : X) ∈ Ik ∧ piOf e k = b) ∧
      ∀ k : ↥K, (k : X) ∈ Ik → piOf e k = 1 → (k : X) ∈ W := by
  obtain ⟨θ⟩ := hB
  let π' : ↥(bar W K) →* ↥(alternatingGroup (Fin 7)) := A5Base.piBar e
  have hπs : Function.Surjective π' := A5Base.piBar_surjective e
  have hπker : ∀ a, π' a = 1 ↔ a ∈ Subgroup.center ↥(bar W K) := A5Base.piBar_eq_one_iff e
  let Bt : Subgroup ↥(bar W K) := B.comap π'
  let Ih : Subgroup ↥(bar W K) := ⁅Bt, Bt⁆
  haveI : Group.IsPerfect ↥(alternatingGroup (Fin 5)) := ⟨A5Base.commutator_alt5⟩
  have hBperf : ⁅B, B⁆ = B := by
    haveI : Group.IsPerfect ↥B :=
      Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hmapBt : Bt.map π' = B := Subgroup.map_comap_eq_self_of_surjective hπs B
  have hmapIh : Ih.map π' = B := by
    show (⁅Bt, Bt⁆).map π' = B
    rw [Subgroup.map_commutator, hmapBt, hBperf]
  have hIhBt : Ih ≤ Bt := Subgroup.commutator_le_self _
  have hdec : ∀ b ∈ Bt, ∃ i ∈ Ih, ∃ z ∈ Subgroup.center ↥(bar W K), b = i * z := by
    intro b hb
    have h1 : π' b ∈ Ih.map π' := by rw [hmapIh]; exact hb
    obtain ⟨i, hi, hib⟩ := Subgroup.mem_map.1 h1
    refine ⟨i, hi, i⁻¹ * b, (hπker _).1 ?_, by group⟩
    rw [map_mul, map_inv, hib, inv_mul_cancel]
  have hIhperf : ⁅Ih, Ih⁆ = Ih := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    refine Subgroup.commutator_le.2 fun b₁ hb₁ b₂ hb₂ => ?_
    obtain ⟨i₁, hi₁, z₁, hz₁, rfl⟩ := hdec b₁ hb₁
    obtain ⟨i₂, hi₂, z₂, hz₂, rfl⟩ := hdec b₂ hb₂
    rw [CFSG.ComponentClassification.RankTwoAlt.commutatorElement_mul_central hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator hi₁ hi₂
  haveI : Group.IsPerfect ↥Ih := Subgroup.isPerfect_iff.mpr hIhperf
  have hIhB : ∀ i : ↥Ih, π' i ∈ B := fun i => hIhBt i.2
  let ρ : ↥Ih →* ↥B := (π'.comp Ih.subtype).codRestrict B hIhB
  let pH : ↥Ih →* ↥(alternatingGroup (Fin 5)) := θ.toMonoidHom.comp ρ
  have hpHs : Function.Surjective pH := by
    intro a
    have hb : (θ.symm a : ↥(alternatingGroup (Fin 7))) ∈ Ih.map π' := by
      rw [hmapIh]; exact (θ.symm a).2
    obtain ⟨i, hi, hib⟩ := Subgroup.mem_map.1 hb
    refine ⟨⟨i, hi⟩, ?_⟩
    have : ρ ⟨i, hi⟩ = θ.symm a := Subtype.ext hib
    simp [pH, this]
  have hpHker : ∀ x : ↥Ih, pH x = 1 → π' x = 1 := by
    intro x hx
    have h1 : ρ x = 1 := by simpa [pH] using hx
    have h2 : (ρ x : ↥(alternatingGroup (Fin 7))) = π' x := rfl
    rw [← h2, h1]
    rfl
  have hkercenter : pH.ker ≤ Subgroup.center ↥Ih := by
    intro x hx
    have h1 : (x : ↥(bar W K)) ∈ Subgroup.center ↥(bar W K) := (hπker _).1 (hpHker x hx)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h1) g)
  have hkerodd : Odd (Nat.card ↥pH.ker) := by
    let j : ↥pH.ker →* ↥(Subgroup.center ↥(bar W K)) :=
      ((Ih.subtype).comp pH.ker.subtype).codRestrict _ fun x =>
        (hπker _).1 (hpHker x.1 x.2)
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(Subgroup.center ↥(bar W K)) => (z : ↥(bar W K))) hxy))
    exact Odd.of_dvd_nat (BlocksChief.centre_odd_aux h) (Subgroup.card_dvd_of_injective j hj)
  have hker : pH.ker = ⊥ :=
    no_odd_ker (Group.isPerfect_def.mp inferInstance) hpHs hkercenter hkerodd
  let Ik : Subgroup X := (Ih.comap (toBar W K)).map K.subtype
  have hmem : ∀ k : ↥K, (k : X) ∈ Ik ↔ toBar W K k ∈ Ih := by
    intro k
    constructor
    · rintro ⟨y, hy, hyk⟩
      have : y = k := Subtype.ext hyk
      subst this
      exact hy
    · intro hk
      exact ⟨k, hk, rfl⟩
  refine ⟨Ik, Subgroup.map_subtype_le _, fun k hk => ?_, fun b hb => ?_, fun k hk hk1 => ?_⟩
  · exact hIhBt ((hmem k).1 hk)
  · have hb' : b ∈ Ih.map π' := by rw [hmapIh]; exact hb
    obtain ⟨i, hi, hib⟩ := Subgroup.mem_map.1 hb'
    obtain ⟨k, rfl⟩ := BlocksChief.toBar_surjective W K i
    exact ⟨k, (hmem k).2 hi, hib⟩
  · have hk' : toBar W K k ∈ Ih := (hmem k).1 hk
    have h1 : π' (toBar W K k) = 1 := hk1
    have h2 : (⟨toBar W K k, hk'⟩ : ↥Ih) ∈ pH.ker := by
      rw [MonoidHom.mem_ker]
      have : ρ ⟨toBar W K k, hk'⟩ = 1 := Subtype.ext h1
      simp [pH, this]
    rw [hker, Subgroup.mem_bot] at h2
    exact (BlocksChief.toBar_eq_one_iff k).1 (congrArg Subtype.val h2)

end Lift

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Lift
