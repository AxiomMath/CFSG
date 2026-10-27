module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem map_conj_eq_of_alt5_comp {G : Type} [Group G] [Finite G] {x t : G} {J J₁ : Subgroup G}
    (hxt : x * t = t * x) (ht2 : t * t = 1)
    (hJc : IsCompIn J (centralizer ({x} : Set G))) (hJ₁c : IsCompIn J₁ (centralizer ({x} : Set G)))
    (hne : J₁ ≠ J) (hJA : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (hJ₁A : Nonempty (J₁ ≃* alternatingGroup (Fin 5)))
    (hJt : ∀ j ∈ J, t * j = j * t)
    (hG0 : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      ⁅R, R⁆ = R → R ≤ J) :
    J₁.map (MulAut.conj t).toMonoidHom = J₁ := by
  set J₂ : Subgroup G := J₁.map (MulAut.conj t).toMonoidHom with hJ₂def
  by_contra hn
  have htX : t ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxt.symm
  have hJ₂c : IsCompIn J₂ (centralizer ({x} : Set G)) := by
    rw [hJ₂def]
    exact hJ₁c.map_conj htX
  have hconj2 : ∀ y : G, MulAut.conj t (MulAut.conj t y) = y := by
    intro y
    show t * (t * y * t⁻¹) * t⁻¹ = y
    rw [inv_eq_of_mul_eq_one_right ht2]
    rw [show t * (t * y * t) * t = (t * t) * y * (t * t) by group, ht2,
      one_mul, mul_one]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom
      = MonoidHom.id G := by
    ext y
    simpa using hconj2 y
  have hJ₂map : J₂.map (MulAut.conj t).toMonoidHom = J₁ := by
    rw [hJ₂def, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hJmap : J.map (MulAut.conj t).toMonoidHom = J := by
    refine le_antisymm ?_ ?_
    · rintro a ⟨j, hj, rfl⟩
      show t * j * t⁻¹ ∈ J
      rw [hJt j hj, mul_assoc, mul_inv_cancel, mul_one]
      exact hj
    · intro j hj
      refine ⟨MulAut.conj t j, ?_, ?_⟩
      · show t * j * t⁻¹ ∈ J
        rw [hJt j hj, mul_assoc, mul_inv_cancel, mul_one]
        exact hj
      · simpa using hconj2 j
  have hJ₂neJ : J₂ ≠ J := by
    intro hEq
    apply hn
    rw [← hJ₂map, hEq, hJmap]
  have hcomm₁₂ : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a :=
    hJ₁c.commute_of_ne hJ₂c (Ne.symm hn)
  have hcomm₁J : ∀ a ∈ J₁, ∀ b ∈ J, a * b = b * a := hJ₁c.commute_of_ne hJc hne
  have hcomm₂J : ∀ a ∈ J₂, ∀ b ∈ J, a * b = b * a := hJ₂c.commute_of_ne hJc hJ₂neJ
  let f : ↥J₁ →* G :=
    MonoidHom.mk' (fun j => (j : G) * MulAut.conj t (j : G)) (by
      intro a b
      have hb : MulAut.conj t (a : G) ∈ J₂ := by
        rw [hJ₂def]
        exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom a.2
      have hcomm : (b : G) * MulAut.conj t (a : G)
          = MulAut.conj t (a : G) * (b : G) :=
        hcomm₁₂ (b : G) b.2 (MulAut.conj t (a : G)) hb
      simp only [Subgroup.coe_mul]
      rw [map_mul]
      calc ((a : G) * (b : G)) *
            (MulAut.conj t (a : G) * MulAut.conj t (b : G))
          = (a : G) * ((b : G) * (MulAut.conj t (a : G) *
              MulAut.conj t (b : G))) := by group
        _ = (a : G) * (((b : G) * MulAut.conj t (a : G)) *
              MulAut.conj t (b : G)) := by group
        _ = (a : G) * ((MulAut.conj t (a : G) * (b : G)) *
              MulAut.conj t (b : G)) := by rw [hcomm]
        _ = ((a : G) * MulAut.conj t (a : G)) *
              ((b : G) * MulAut.conj t (b : G)) := by group)
  let R : Subgroup G := f.range
  have hRle : R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) := by
    apply le_inf
    · rintro r ⟨j, rfl⟩
      change (j : G) * MulAut.conj t (j : G) ∈ centralizer ({x} : Set G)
      have hjX : (j : G) ∈ centralizer ({x} : Set G) := hJ₁c.le j.2
      have hcJ₂ : MulAut.conj t (j : G) ∈ J₂ := by
        rw [hJ₂def]
        exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom j.2
      have hcX : MulAut.conj t (j : G) ∈ centralizer ({x} : Set G) := hJ₂c.le hcJ₂
      exact mul_mem hjX hcX
    · rintro r ⟨j, rfl⟩
      change (j : G) * MulAut.conj t (j : G) ∈ centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcJ₂ : MulAut.conj t (j : G) ∈ J₂ := by
        rw [hJ₂def]
        exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom j.2
      have hcomm : MulAut.conj t (j : G) * (j : G)
          = (j : G) * MulAut.conj t (j : G) :=
        (hcomm₁₂ (j : G) j.2 (MulAut.conj t (j : G)) hcJ₂).symm
      have hfix : MulAut.conj t ((j : G) * MulAut.conj t (j : G))
          = (j : G) * MulAut.conj t (j : G) := by
        rw [map_mul, hconj2 (j : G)]
        exact hcomm
      have h2 := congrArg (fun y => y * t) hfix
      simpa [mul_assoc] using h2.symm
  have hRR : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥J₁ := hJ₁c.isQuasisimple.1
    have hperf : Group.IsPerfect ↥R := Group.IsPerfect.range f
    letI : Group.IsPerfect ↥R := hperf
    exact Subgroup.commutator_eq_self
  have hRJ : R ≤ J := hG0 R hRle hRR
  have hRcent : R ≤ centralizer (J : Set G) := by
    rintro r ⟨j, rfl⟩
    change (j : G) * MulAut.conj t (j : G) ∈ centralizer (J : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcJ₂ : MulAut.conj t (j : G) ∈ J₂ := by
      rw [hJ₂def]
      exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom j.2
    have hcomm₁ : h * (j : G) = (j : G) * h := (hcomm₁J (j : G) j.2 h hh).symm
    have hcomm₂ : h * MulAut.conj t (j : G) = MulAut.conj t (j : G) * h :=
      (hcomm₂J (MulAut.conj t (j : G)) hcJ₂ h hh).symm
    rw [← mul_assoc, hcomm₁, mul_assoc, hcomm₂, mul_assoc]
  have hRbot : R = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    have hrJ : r ∈ J := hRJ hr
    have hrc : r ∈ centralizer (J : Set G) := hRcent hr
    have hcomm : ∀ h' ∈ J, r * h' = h' * r := by
      intro h' hh'
      exact ((Subgroup.mem_centralizer_iff.mp hrc) h' hh').symm
    exact alt5_subgroup_center hJA.some hrJ hcomm
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro j hj
    have hj1 : f j = 1 := MonoidHom.mem_ker.mp hj
    change (j : G) * MulAut.conj t (j : G) = 1 at hj1
    have hcJ₂ : MulAut.conj t (j : G) ∈ J₂ := by
      rw [hJ₂def]
      exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom j.2
    have hjb : (j : G) = (MulAut.conj t (j : G))⁻¹ := eq_inv_of_mul_eq_one_left hj1
    have hjJ₂ : (j : G) ∈ J₂ := by
      rw [hjb]
      exact J₂.inv_mem hcJ₂
    have hcommj : ∀ j' ∈ J₁, (j : G) * j' = j' * (j : G) := by
      intro j' hj'
      exact (hcomm₁₂ j' hj' (j : G) hjJ₂).symm
    refine Subtype.ext ?_
    simpa using alt5_subgroup_center hJ₁A.some j.2 hcommj
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hJ₁bot : J₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro j hj
    have hjR : f ⟨j, hj⟩ ∈ R := MonoidHom.mem_range.mpr ⟨⟨j, hj⟩, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at hjR
    have h1 : (⟨j, hj⟩ : ↥J₁) = 1 := by
      apply hfinj
      rw [map_one]
      exact hjR
    exact congrArg Subtype.val h1
  have hcard60 : Nat.card ↥J₁ = 60 := alt5_card hJ₁A.some
  have hcard1 : Nat.card ↥J₁ = 1 := by
    rw [hJ₁bot]
    exact Subgroup.card_bot
  omega

end CFSG.EvenSporadicStandard.M12Std.PropA
