module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerLayer

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Points

theorem two_ne_zero_te6 (hp2 : p ≠ 2) : (2 : GaloisField p (2 * f)) ≠ 0 :=
  two_ne_zero_of_charP_ne_two (K := GaloisField p (2 * f)) (p := p) hp2

variable (p f) in
@[expose] noncomputable def te6Node :
    Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1)) :=
  LcU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num))

variable (p f) in
@[expose] noncomputable def te6Plane :
    Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1)) :=
  LcU (GaloisField p (2 * f)) p f (nodePair 5 2 (by norm_num))

theorem isLongRootSU2_te6Node (hp2 : p ≠ 2) :
    IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 5 + 1) (te6Node p f)
      (te6Inv p f) :=
  isLongRootSU2_LcU (two_ne_zero_te6 hp2) _ _

theorem isLongRootSU2_te6Plane (hp2 : p ≠ 2) :
    IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 5 + 1) (te6Plane p f)
      (zEltU (GaloisField p (2 * f)) p f (nodePair 5 2 (by norm_num))) :=
  isLongRootSU2_LcU (two_ne_zero_te6 hp2) _ _

theorem te6Node_le_centralizer :
    te6Node p f ≤ Subgroup.centralizer ({te6Inv p f} : Set _) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hx' := (mem_longRootGroupSU.mp hx).1
  exact suMat_injective (σ := unitaryInvolution (GaloisField p (2 * f)) p f)
    (by rw [suMat_mul, suMat_mul]; exact hx'.symm)

theorem te6Plane_le_centralizer (hp2 : p ≠ 2) :
    te6Plane p f ≤ Subgroup.centralizer ({te6Inv p f} : Set _) := by
  have hd : Disjoint (nodePair 5 0 (by norm_num)).1 (nodePair 5 2 (by norm_num)).1 := by
    simp only [nodePair, natPair]
    decide
  have hc := commutes_LcU_of_disjoint (K := GaloisField p (2 * f)) (p := p) (f := f)
    (two_ne_zero_te6 hp2) hd
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hc _ (isLongRootSU2_te6Node hp2).mem x hx

@[expose] noncomputable def te6NodePoint (hp2 : p ≠ 2) : TE6Layer p f :=
  some ⟨te6Node p f, ⟨_, isLongRootSU2_te6Node hp2⟩, te6Node_le_centralizer⟩

@[expose] noncomputable def te6PlanePoint (hp2 : p ≠ 2) : TE6Layer p f :=
  some ⟨te6Plane p f, ⟨_, isLongRootSU2_te6Plane hp2⟩, te6Plane_le_centralizer hp2⟩

theorem te6Plane_ne_te6Node (hp2 : p ≠ 2) (hf : 1 ≤ f) : te6Plane p f ≠ te6Node p f := by
  intro h
  have := LcU_injective (card_galoisField_two_mul p f hf) hp2 (by norm_num : 2 ≤ 5 + 1) h
  have h2 := (nodePair_eq_iff (m := 5) (by norm_num : 2 < 5) (by norm_num : 0 < 5)).mp this
  omega

theorem te6PlanePoint_ne_te6NodePoint (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    te6PlanePoint (p := p) (f := f) hp2 ≠ te6NodePoint hp2 := by
  intro h
  exact te6Plane_ne_te6Node hp2 hf (congrArg Subtype.val (Option.some.inj h))

end Points

section Shape

theorem TE6Layer.rel_node (hp2 : p ≠ 2) (hf : 1 ≤ f) (x : TE6Layer p f)
    (hx : x ≠ te6NodePoint hp2) : TE6Layer.rel x (te6NodePoint hp2) := by
  rcases x with _ | ⟨P, hP, hPc⟩
  · exact trivial
  · obtain ⟨iP, hiP⟩ := hP
    have hK := card_galoisField_two_mul p f hf
    have h2 := two_ne_zero_te6 (p := p) (f := f) hp2
    have hnode := isLongRootSU2_te6Node (p := p) (f := f) hp2
    have hne : P ≠ te6Node p f := fun h => hx (by subst h; rfl)
    have hc : Commute iP (te6Inv p f) :=
      (Subgroup.mem_centralizer_iff.mp (hPc hiP.mem) (te6Inv p f) rfl).symm
    have hne' : iP ≠ te6Inv p f := by
      intro h
      rw [h] at hiP
      exact hne ((hiP.eq_longRootGroupSU h2).trans (hnode.eq_longRootGroupSU h2).symm)
    rcases lemma_6_5_su hK hp2 (by norm_num : 3 ≤ 5 + 1) hiP hnode hc hne' with
      ⟨hcomm, -⟩ | ⟨hnot, -⟩
    · exact hcomm
    · exact absurd (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hPc hy) (te6Inv p f) rfl).symm) hnot

theorem TE6Layer.rel_none_left (x : TE6Layer p f) (hx : x ≠ none) : TE6Layer.rel none x := by
  rcases x with _ | R
  · exact absurd rfl hx
  · exact trivial

theorem TE6Layer.rel_none_right (x : TE6Layer p f) (hx : x ≠ none) : TE6Layer.rel x none := by
  rcases x with _ | R
  · exact absurd rfl hx
  · exact trivial

theorem te6NodePoint_ne_none (hp2 : p ≠ 2) : te6NodePoint (p := p) (f := f) hp2 ≠ none :=
  Option.some_ne_none _

theorem te6PlanePoint_ne_none (hp2 : p ≠ 2) : te6PlanePoint (p := p) (f := f) hp2 ≠ none :=
  Option.some_ne_none _

end Shape

end CFSG.ClassicalInvolution.RouteD.NonClassical
