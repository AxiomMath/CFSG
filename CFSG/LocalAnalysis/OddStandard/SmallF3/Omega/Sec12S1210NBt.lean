module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem sec12N_beta_one (V : Subgroup G) {n : ↥(normalizer (V : Set G))}
    (h : (n : G) ∈ centralizer (V : Set G)) : sec12J_beta V n = 1 := by
  apply Subtype.ext
  refine MulEquiv.ext fun v => ?_
  apply Subtype.ext
  have h1 := sec12J_beta_apply V n v
  have hcm : (v : G) * (n : G) = (n : G) * (v : G) := Subgroup.mem_centralizer_iff.mp h v v.2
  change (((sec12J_beta V n : ↥(secNb V)) : MulAut ↥V) v : G) = (v : G)
  rw [h1, ← hcm, mul_inv_cancel_right]

theorem sec12N_cent_card {V : Subgroup G} {t : G} (htN : t ∈ secN V)
    (hcent : Nat.card ↥(secNb V ⊓ Subgroup.centralizer ({betaOf V t} : Set (MulAut ↥V))) = 120) :
    Nat.card (Subgroup.centralizer ({sec12J_beta V ⟨t, htN⟩} : Set ↥(secNb V))) = 120 := by
  have htN' : t ∈ normalizer (V : Set G) := htN
  have hbt : ((sec12J_beta V ⟨t, htN'⟩ : ↥(secNb V)) : MulAut ↥V) = betaOf V t := by
    unfold betaOf
    rw [dif_pos htN']
    rfl
  have hmemiff : ∀ x : ↥(secNb V),
      x ∈ Subgroup.centralizer ({sec12J_beta V ⟨t, htN'⟩} : Set ↥(secNb V)) ↔
        (x : MulAut ↥V) ∈ Subgroup.centralizer ({betaOf V t} : Set (MulAut ↥V)) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h2 := congrArg Subtype.val h
      rw [← hbt]
      exact h2
    · intro h
      apply Subtype.ext
      change (sec12J_beta V ⟨t, htN'⟩ : MulAut ↥V) * x = x * (sec12J_beta V ⟨t, htN'⟩ : MulAut ↥V)
      rw [hbt]
      exact h
  rw [← hcent]
  exact Nat.card_congr
    { toFun := fun x => ⟨(x : ↥(secNb V)).1, (x : ↥(secNb V)).2, (hmemiff x).mp x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, (hmemiff ⟨x.1, x.2.1⟩).mpr x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CFSG.OddStandard.SmallF3.Omega
