module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.GH74.Generic.S3.V1InnerUni

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.GH74.KGroups.L3Eps (InvData invData_of_equiv tInv tInv_mul_self tInv_ne_one
  exists_projectiveSL_equiv)
open CFSG.LocalAnalysis.ComponentInitial (ordProj_two_le_of_dvd ordProj_two_eq_one_of_odd)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped MatrixGroups

namespace GHInv

theorem hOut_of_ordProj_le_two {L : Type} [Group L] [Finite L]
    (h : ordProj[2] (Nat.card (Outer L)) ≤ 2) :
    ∀ E : Subgroup (Outer L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
  intro E hE
  have hfin : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  have : Finite (Outer L) := inferInstanceAs (Finite (MulAut L ⧸ inner L))
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one' E hE
  have hne : Nat.card (Outer L) ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ d ∣ Nat.card (Outer L) := by
    rw [← hd]
    exact Subgroup.card_subgroup_dvd_card E
  have h1 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hne).1 hdvd
  have hpos : 0 < ordProj[2] (Nat.card (Outer L)) := Nat.ordProj_pos _ _
  have h2 : 2 ^ d ≤ 2 := (Nat.le_of_dvd hpos h1).trans h
  rw [hd]
  simpa using h2

theorem ordProj_two_le_two_of_dvd {m f d : ℕ} (hf : Odd f) (hd : Odd d) (h : m ∣ 2 * f * d) :
    ordProj[2] m ≤ 2 := by
  have hf0 : f ≠ 0 := by rintro rfl; exact absurd hf (by decide)
  have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
  have hne : 2 * f * d ≠ 0 := by positivity
  refine (ordProj_two_le_of_dvd hne h).trans (le_of_eq ?_)
  rw [Nat.ordProj_mul 2 (by positivity) hd0, Nat.ordProj_mul 2 two_ne_zero hf0,
    ordProj_two_eq_one_of_odd hf, ordProj_two_eq_one_of_odd hd,
    Nat.Prime.factorization_self Nat.prime_two]
  simp

end GHInv

theorem exists_invData_lin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f)
    {K : Type} [Group K] [Finite K] (hX : StatedClassicalModel K .PSL 3 p f) :
    ∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, InvData (p ^ f) K x S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := Generic.S3.two_ne_zero_of_odd_card hodd
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  intro x hx2 hx1
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := Generic.S3.singleInv_projectiveSL h2 (e x) tInv hex2 hex1 tInv_mul_self
    (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' x = tInv := by
    show MulAut.conj g (e x) = tInv
    rw [MulAut.conj_apply]
    exact hg
  exact ⟨_, invData_of_equiv hp hF hf h2 (by omega) e' he'⟩

theorem comp_mem_lin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f)
    {X : Type} [Group X] [Finite X] (hX : StatedClassicalModel X .PSL 3 p f) :
    ∀ y : X, y * y = 1 → y ≠ 1 → ∀ B : Subgroup X,
      IsCompIn (Subgroup.centralizer ({y} : Set X)) B → y ∈ B := by
  intro y hy2 hy1 B hB
  obtain ⟨S, hInv⟩ := exists_invData_lin hp hp2 h5 hf hX y hy2 hy1
  exact GHInv.mem_of_isCompIn_of_normal_quasisimple hInv.quasisimple hInv.mem hInv.le_centralizer
    hInv.conj_mem hInv.commutator_mem hB

theorem comp_mem_uni {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {X : Type} [Group X] [Finite X] (hX : StatedClassicalModel X .PSU 3 p f) :
    ∀ y : X, y * y = 1 → y ≠ 1 → ∀ B : Subgroup X,
      IsCompIn (Subgroup.centralizer ({y} : Set X)) B → y ∈ B := by
  intro y hy2 hy1 B hB
  obtain ⟨S, hInv⟩ := ((Generic.S3.libData_uni hp hp2 h5) X hX).1 y hy2 hy1
  exact GHInv.mem_of_isCompIn_of_normal_quasisimple hInv.quasisimple hInv.mem hInv.le_centralizer
    hInv.conj_mem hInv.commutator_mem hB

theorem ivk73_l3_odd {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f) :
    Ivk73Empty (fun X _ => LieModel X .PSL 3 p f) := by
  intro N _ _ L K Q h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hg : Odd (Nat.gcd 3 (p ^ f - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  refine h.false_of_comp_mem (GHInv.hOut_of_ordProj_le_two
    (GHInv.ordProj_two_le_two_of_dvd hf hg (CFSG.GH74.KGroups.L3Eps.lin_outer_dvd hst)))
    (comp_mem_lin hp hp2 h5 hf hst)

end CFSG.GH74.GLS.IVK
