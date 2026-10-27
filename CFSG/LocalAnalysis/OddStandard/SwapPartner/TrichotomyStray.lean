module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomySetup
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

namespace SwapShape

variable {X : Type*} [Group X] {t : X} {Sg V : Subgroup X}

private theorem wt_conj_comm_of_comm {a j : X} (ht : Commute a t) (hj : Commute a j) :
    Commute a ((MulAut.conj t) j) := by
  rw [MulAut.conj_apply]
  exact (ht.mul_right hj).mul_right ht.inv_right

theorem map_conj_eq_of_stray [Finite X] (h : SwapShape t Sg V) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (hJA : ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥) :
    J.map (MulAut.conj t).toMonoidHom = J := by
  by_contra hne
  have hJt : CFSG.IsComponent (J.map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hJ
  have hcomm : ⁅J, J.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hJ hJt with heq | hc
    · exact absurd heq.symm hne
    · exact hc
  have hJ_le_cJt : J ≤ centralizer (J.map (MulAut.conj t).toMonoidHom : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hJcentA : J ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact hJA
  have ht2 : t * t = 1 := by simpa [pow_two] using h.sq_eq_one
  have hconj2mul : (MulAut.conj t) * (MulAut.conj t) = 1 := by
    rw [← map_mul (MulAut.conj) t t, ht2, map_one]
  have hconj2 : ∀ x : X, (MulAut.conj t) ((MulAut.conj t) x) = x := by
    intro x
    rw [← MulAut.mul_apply, hconj2mul, MulAut.one_apply]
  let φ : J →* X :=
    { toFun := fun j => (j : X) * (MulAut.conj t) (j : X)
      map_one' := by simp
      map_mul' := by
        intro a b
        have hcb : (MulAut.conj t) (a : X) * (b : X) =
            (b : X) * (MulAut.conj t) (a : X) :=
          Subgroup.mem_centralizer_iff.mp (hJ_le_cJt b.2) _
            (Subgroup.mem_map_of_mem _ a.2)
        show (a : X) * (b : X) * (MulAut.conj t) ((a : X) * (b : X)) =
            ((a : X) * (MulAut.conj t) (a : X)) *
              ((b : X) * (MulAut.conj t) (b : X))
        calc (a : X) * (b : X) * (MulAut.conj t) ((a : X) * (b : X))
            = (a : X) * (b : X) *
                ((MulAut.conj t) (a : X) * (MulAut.conj t) (b : X)) := by
              rw [map_mul]
          _ = (a : X) * ((b : X) *
                ((MulAut.conj t) (a : X) * (MulAut.conj t) (b : X))) := by
              rw [mul_assoc]
          _ = (a : X) * (((b : X) * (MulAut.conj t) (a : X)) *
                (MulAut.conj t) (b : X)) := by
              rw [mul_assoc]
          _ = (a : X) * (((MulAut.conj t) (a : X) * (b : X)) *
                (MulAut.conj t) (b : X)) := by
              rw [← hcb]
          _ = (a : X) * ((MulAut.conj t) (a : X) *
                ((b : X) * (MulAut.conj t) (b : X))) := by
              rw [mul_assoc]
          _ = (a : X) * (MulAut.conj t) (a : X) *
                ((b : X) * (MulAut.conj t) (b : X)) := by
              rw [mul_assoc] }
  have hφperf : Group.IsPerfect φ.range := by
    haveI : Group.IsPerfect J := hJ.1.1
    exact Group.IsPerfect.range φ
  have hRC : φ.range ≤ centralizer ({t} : Set X) := by
    intro x hx
    obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconjφ : (MulAut.conj t) (φ j) = φ j := by
      show (MulAut.conj t) ((j : X) * (MulAut.conj t) (j : X)) =
          (j : X) * (MulAut.conj t) (j : X)
      rw [map_mul, hconj2]
      exact Subgroup.mem_centralizer_iff.mp (hJ_le_cJt j.2) _
        (Subgroup.mem_map_of_mem _ j.2)
    have hconjφ' : t * φ j * t⁻¹ = φ j := by
      simpa only [MulAut.conj_apply] using hconjφ
    have hcomm_t : t * φ j = φ j * t := (mul_inv_eq_iff_eq_mul).mp hconjφ'
    exact hcomm_t.symm
  have hRA : φ.range ≤ (⁅Sg, Sg⁆ : Subgroup X) :=
    calc φ.range = ⁅φ.range, φ.range⁆ := (Subgroup.isPerfect_iff.mp hφperf).symm
      _ ≤ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ :=
          Subgroup.commutator_mono hRC hRC
      _ = ⁅Sg, Sg⁆ := h.commutator_centralizer_eq
  have hcomm_a_t : ∀ a ∈ (⁅Sg, Sg⁆ : Subgroup X), Commute a t := fun a ha =>
    (commute_iff_eq a t).mpr (Subgroup.mem_centralizer_singleton_iff.mp
      (h.commutator_sg_le_centralizer ha))
  have hRcentA : φ.range ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    intro x hx
    obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hja : a * (j : X) = (j : X) * a :=
      Subgroup.mem_centralizer_iff.mp (hJcentA j.2) a ha
    have hca : a * (MulAut.conj t) (j : X) = (MulAut.conj t) (j : X) * a :=
      (wt_conj_comm_of_comm (hcomm_a_t a ha) ((commute_iff_eq a (j : X)).mpr hja)).eq
    calc a * ((j : X) * (MulAut.conj t) (j : X))
        = (a * (j : X)) * (MulAut.conj t) (j : X) := (mul_assoc a (j : X) _).symm
      _ = ((j : X) * a) * (MulAut.conj t) (j : X) := by rw [hja]
      _ = (j : X) * (a * (MulAut.conj t) (j : X)) := mul_assoc (j : X) a _
      _ = (j : X) * ((MulAut.conj t) (j : X) * a) := by rw [hca]
      _ = ((j : X) * (MulAut.conj t) (j : X)) * a := (mul_assoc (j : X) _ a).symm
  have hRbot : φ.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    have hrA : r ∈ (⁅Sg, Sg⁆ : Subgroup X) := hRA hr
    have hrc : r ∈ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := hRcentA hr
    have hcent : (⟨r, hrA⟩ : (⁅Sg, Sg⁆ : Subgroup X)) ∈
        center (⁅Sg, Sg⁆ : Subgroup X) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : X) * r = r * (y : X)
      exact Subgroup.mem_centralizer_iff.mp hrc (y : X) y.2
    rw [h.center_abar_eq_bot, Subgroup.mem_bot] at hcent
    exact Subtype.ext_iff.mp hcent
  have hφbot : ∀ j : J, φ j = 1 := by
    intro j
    have hj : φ j ∈ φ.range := MonoidHom.mem_range.mpr ⟨j, rfl⟩
    rw [hRbot] at hj
    exact Subgroup.mem_bot.mp hj
  have hJt_le_J : J.map (MulAut.conj t).toMonoidHom ≤ J := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : (j : X) * (MulAut.conj t) (j : X) = 1 := hφbot ⟨j, hj⟩
    have h2 : (MulAut.conj t).toMonoidHom j = (j : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact J.inv_mem hj
  have hcard : Nat.card (J.map (MulAut.conj t).toMonoidHom) = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  exact hne (Subgroup.eq_of_le_of_card_ge hJt_le_J (by rw [hcard]))

theorem inf_centralizer_le_of_stray (h : SwapShape t Sg V) {J : Subgroup X}
    (hJA : ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥) : J ⊓ centralizer ({t} : Set X) ≤ V := by
  have hJcent : J ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact hJA
  calc J ⊓ centralizer ({t} : Set X)
      ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) ⊓ centralizer ({t} : Set X) :=
        le_inf (inf_le_left.trans hJcent) inf_le_right
    _ = V := h.centralizer_abar_inf_centralizer

theorem mem_of_stray_of_four_le [Finite X] (h : SwapShape t Sg V) {J : Subgroup X}
    (hJA : ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥)
    (h4 : 4 ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set X))) : t ∈ J := by
  have hMle : J ⊓ centralizer ({t} : Set X) ≤ V := inf_centralizer_le_of_stray h hJA
  have hcard : Nat.card V ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set X)) := by
    rw [h.card_v]
    exact h4
  have hMV : J ⊓ centralizer ({t} : Set X) = V :=
    Subgroup.eq_of_le_of_card_ge hMle hcard
  have htM : t ∈ J ⊓ centralizer ({t} : Set X) := by
    rw [hMV]
    exact h.mem_v
  exact (Subgroup.mem_inf.mp htM).1

end SwapShape

end CFSG.OddStandard.AltStdSec.SwapPartner
