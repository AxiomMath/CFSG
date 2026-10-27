module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBTheta
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBJ2Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.External
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

structure JLayer (hs : Setting46e t L p f S w z V i j)
    (π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P) : Prop where
  h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)
  h47 : ∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')
  quasi : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  out : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
    innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  surj : Function.Surjective π
  ker : π.ker = center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  center_le : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≤ 2

namespace JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem isPerfect (hJ : JLayer hs π) :
    Group.IsPerfect ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  hJ.quasi.1

@[expose] def theta (hJ : JLayer hs π) :
    MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) →* MulAut P :=
  haveI := hJ.isPerfect
  Classical.choose (exists_theta π hJ.surj hJ.ker)

theorem theta_spec (hJ : JLayer hs π) :
    (∀ (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
        (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))),
        (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = g * l * g⁻¹ →
          hJ.theta g (π l) = π l') ∧
      ∀ g, hJ.theta g = 1 ↔
        g ∈ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  haveI := hJ.isPerfect
  Classical.choose_spec (exists_theta π hJ.surj hJ.ker)

theorem theta_apply (hJ : JLayer hs π) (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (h : (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = g * l * g⁻¹) :
    hJ.theta g (π l) = π l' :=
  hJ.theta_spec.1 g l l' h

theorem theta_eq_one_iff (hJ : JLayer hs π) (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    hJ.theta g = 1 ↔ g ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [hJ.theta_spec.2, hs.centralizer_layer_eq hJ.h412]

theorem theta_conj (hJ : JLayer hs π) (l : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    hJ.theta l = MulAut.conj (π l) :=
  EndB.theta_conj hJ.surj hJ.theta_spec.1 l

theorem theta_mem_inner_iff (hJ : JLayer hs π) (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    hJ.theta g ∈ innAut P ↔ g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [EndB.theta_mem_inner_iff hJ.surj hJ.theta_spec.1 hJ.theta_spec.2,
    hs.centralizer_layer_eq hJ.h412]

theorem alpha_not_mem (hJ : JLayer hs π) : hJ.theta (hs.setup.tBar i j) ∉ innAut P := by
  rw [hJ.theta_mem_inner_iff]
  intro h
  apply hJ.out
  rw [← hs.centralizer_layer_eq hJ.h412] at h
  have hc : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ n ∈ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), k * n = n * k :=
    fun k hk n hn => mem_centralizer_iff.mp hn k hk
  obtain ⟨k, hk, n, hn, hkn⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc h
  refine conjOn_mem_innAut_iff.mpr ⟨k, hk, ?_⟩
  rw [hkn, show k * n * k⁻¹ = n by rw [hc k hk n hn]; group]
  exact hn

theorem orderOf_alpha (hJ : JLayer hs π) : orderOf (hJ.theta (hs.setup.tBar i j)) = 2 := by
  refine orderOf_eq_prime (by rw [← map_pow, hs.tBar_sq, map_one]) fun h => hJ.alpha_not_mem ?_
  rw [h]
  exact one_mem _

theorem mem_sup_or (hJ : JLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∨
      g * (hs.setup.tBar i j)⁻¹ ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have h := mem_sup_or_mul_mem_sup hJ.surj hJ.theta_spec.1 hJ.theta_spec.2 index_innAut_P
    hJ.alpha_not_mem g
  rwa [hs.centralizer_layer_eq hJ.h412] at h

theorem odd_mem_sup
    (hJ : JLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg : Odd (orderOf g)) :
    g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have h := EndB.odd_mem_sup hJ.surj hJ.theta_spec.1 hJ.theta_spec.2 index_innAut_P hg
  rwa [hs.centralizer_layer_eq hJ.h412] at h

theorem odd_mem_layer
    (hJ : JLayer hs π) {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg : Odd (orderOf g)) :
    g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  refine mem_of_odd_of_mem_sup pCore_isPGroup (fun k hk n hn => ?_) (hJ.odd_mem_sup hg) hg
  rw [← hs.centralizer_layer_eq hJ.h412] at hn
  exact mem_centralizer_iff.mp hn k hk

end JLayer

end EndB

end CFSG.ComponentClassification.HarrisLit
