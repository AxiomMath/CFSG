module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F

@[expose] def I144Cat : TauCeti.CFSGIndex → Prop :=
  fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i

@[expose] def I144Inner (K : Type) [Group K] (α : MulAut K) : Prop :=
  GLAMarking K (fun _ _ _ I _ θ => ∃ φ ∈ I, GLAInduces θ (fun x y => α x = y) φ)

@[expose] def I144InnFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (α : MulAut K) (J : Subgroup K),
    CFSG.Open.IsQuasisimple K → α ^ 3 = 1 → GLAPComponent 3 (fixSubgroup α) J →
      catalogIs (PSimple 3 J) I144Cat → I144Inner K α → GLAMarking K (fun lab _ _ _ _ _ => lab.n = 1)

@[expose] def I144OutFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (α : MulAut K) (J : Subgroup K),
    CFSG.Open.IsQuasisimple K → IsChevSimple 2 (K ⧸ Subgroup.center K) → α ^ 3 = 1 →
      GLAPComponent 3 (fixSubgroup α) J → catalogIs (PSimple 3 J) I144Cat → ¬ I144Inner K α →
      GLAMarking K (fun lab _ _ I F θ => GLAPrimeField 3 lab I F (GLAInduces θ fun x y => α x = y))

variable {G : Type} [Group G] [Finite G]

theorem centralizer_inv_eq (a : G) :
    Subgroup.centralizer ({a⁻¹} : Set G) = Subgroup.centralizer ({a} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem i144One_of_facts (hIn : I144InnFact) (hOut : I144OutFact) : I144oneAt G := by
  intro b' a Kstar K hab ha3 hKc hqK hchev hNa hKa hcat _
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨eP⟩ := S9.nonempty_pSimple_equiv hp3 hKc hqK
  have hchevZ : IsChevSimple 2 (↥Kstar ⧸ Subgroup.center ↥Kstar) :=
    isChevSimple_two_of_equiv' eP.symm hchev
  have hyN : a⁻¹ ∈ Subgroup.normalizer (Kstar : Set G) := Subgroup.inv_mem _ hNa
  have hKc' : GLAPComponent 3 (Kstar ⊓ Subgroup.centralizer ({a⁻¹} : Set G)) K := by
    rw [centralizer_inv_eq]
    exact hKa
  obtain ⟨hKK, hfix⟩ := glaPComponent_fixSubgroup_conjAut' hp3 Kstar hyN hKc'
  have hα3 : (conjAut' Kstar a⁻¹ hyN) ^ 3 = 1 :=
    conjAut'_pow Kstar hyN (by rw [inv_pow, ha3, inv_one])
  have hcat' : catalogIs (PSimple 3 (K.subgroupOf Kstar)) I144Cat := by
    obtain ⟨e⟩ := pSimple_subgroupOf_equiv (p := 3) (hKa.1.trans inf_le_left)
    exact (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 hcat
  have key : ∀ x y : ↥Kstar, conjAut' Kstar a⁻¹ hyN x = y ↔ (y : G) = a⁻¹ * (x : G) * a := by
    intro x y
    rw [← Subtype.coe_inj, coe_conjAut', inv_inv]
    exact eq_comm
  have hrel : (fun (j j' : ↥Kstar) => (j' : G) = a⁻¹ * (j : G) * a) =
      (fun x y => conjAut' Kstar a⁻¹ hyN x = y) := by
    funext x y
    exact propext (key x y).symm
  by_cases hI : I144Inner ↥Kstar (conjAut' Kstar a⁻¹ hyN)
  · exact Or.inl (hIn ↥Kstar (conjAut' Kstar a⁻¹ hyN) (K.subgroupOf Kstar) hqK hα3 hfix hcat' hI)
  · refine Or.inr ?_
    have h := hOut ↥Kstar (conjAut' Kstar a⁻¹ hyN) (K.subgroupOf Kstar) hqK hchevZ hα3 hfix hcat' hI
    rw [hrel]
    exact h

end CFSG.LocalAnalysis.GLTheoremA.K144
