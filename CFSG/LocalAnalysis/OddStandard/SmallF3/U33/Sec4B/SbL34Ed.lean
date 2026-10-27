module

public import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {Λ : Type*} [Group Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

structure Crit (ι : Λ →* (E ≃ₗ[ZMod 2] E)) (P W : Subgroup Λ) (r s : Λ) : Prop where
  inj : Function.Injective ι
  dim : Module.finrank (ZMod 2) E = 6
  r_cube : r ^ 3 = 1
  r_ne : r ≠ 1
  s_sq : s * s = 1
  s_conj : s * r * s⁻¹ = r⁻¹
  normal : P.Normal
  card_index : Nat.card Λ = 6 * Nat.card P
  fpf : ∀ x ∈ P, r * x * r⁻¹ = x → x = 1
  W_pgroup : IsPGroup 2 W
  W_index : ¬ 2 ∣ W.index
  s_mem : s ∈ W
  cent : Nat.card ↥(Subgroup.centralizer ({s} : Set Λ) ⊓ W) = 4

theorem isNilpotent_of_fpf (P : Subgroup Λ) [P.Normal] (r : Λ) (hr3 : r ^ 3 = 1)
    (hfix : ∀ x ∈ P, r * x * r⁻¹ = x → x = 1) : Group.IsNilpotent ↥P := by
  by_cases hsub : Subsingleton ↥P
  · haveI := hsub
    infer_instance
  ·
    let α : MulAut ↥P := MulAut.conjNormal r
    have hα3 : α ^ 3 = 1 := by
      change MulAut.conjNormal r ^ 3 = 1
      rw [← map_pow, hr3, map_one]
    have hαne : α ≠ 1 := by
      intro h
      apply hsub
      have hfix1 : ∀ a : ↥P, a = 1 := by
        intro a
        have ha : α a = a := by rw [h]; rfl
        have hcoe : r * (a : Λ) * r⁻¹ = (a : Λ) := by
          have := congrArg (fun y : ↥P => (y : Λ)) ha
          simpa [α, MulAut.conjNormal_apply] using this
        exact Subtype.ext (by simpa using hfix (a : Λ) a.2 hcoe)
      exact ⟨fun a b => (hfix1 a).trans (hfix1 b).symm⟩
    have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hαne
    have hαfix : ∀ g : ↥P, α g = g → g = 1 := by
      intro g hg
      have hcoe : r * (g : Λ) * r⁻¹ = (g : Λ) := by
        have := congrArg (fun y : ↥P => (y : Λ)) hg
        simpa [α, MulAut.conjNormal_apply] using this
      exact Subtype.ext (by simpa using hfix (g : Λ) g.2 hcoe)
    exact CFSG.StronglyEmbedded.prime_order_fixed_point_free_automorphism_nilpotent
      α Nat.prime_three hαord hαfix

theorem exists_normal_sylow (P : Subgroup Λ) [P.Normal] (hnil : Group.IsNilpotent ↥P) (p : ℕ)
    [Fact p.Prime] :
    ∃ R : Subgroup Λ, R ≤ P ∧ R.Normal ∧ IsPGroup p R ∧ ¬ p ∣ R.relIndex P := by
  haveI : Group.IsNilpotent ↥P := hnil
  let S : Sylow p ↥P := Classical.arbitrary _
  let R : Subgroup Λ := (S : Subgroup ↥P).map P.subtype
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  have hRpg : IsPGroup p R := S.isPGroup'.map P.subtype
  have hSchar : (S : Subgroup ↥P).Characteristic :=
    Sylow.characteristic_of_normal S inferInstance
  have hRnorm : R.Normal := by
    haveI : (S : Subgroup ↥P).Characteristic := hSchar
    exact ConjAct.normal_of_characteristic_of_normal
  refine ⟨R, hRP, hRnorm, hRpg, ?_⟩
  have hRsub : R.subgroupOf P = S := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRP]
  have hrel : R.relIndex P = (S : Subgroup ↥P).index := by
    rw [show R.relIndex P = (R.subgroupOf P).index from rfl, hRsub]
  rw [hrel]
  exact Sylow.not_dvd_index S

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
