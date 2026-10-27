module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Torus
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Squares

variable {K : Type} [Field K]

theorem exists_sq_of_pow_odd {u : Kˣ} {n : ℕ} (hn : Odd n) (hu : u ^ n = 1) :
    ∃ b : Kˣ, u = b ^ 2 := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨u ^ (m + 1), ?_⟩
  rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by ring, pow_succ, hu, one_mul]

theorem tupAct_mem (μ : Subgroup Kˣ) (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    {a : Fin Tag.D4.rank → Kˣ} (ha : ∀ j, a j ∈ μ) (j : Fin Tag.D4.rank) : tupAct M a j ∈ μ :=
  Subgroup.prod_mem _ fun k _ => Subgroup.zpow_mem _ (ha k) _

end Squares

section D4

variable {K : Type} [Field K]

theorem rootDiagUnit_mem_of_sq {a : Fin Tag.D4.rank → Kˣ} (ha : ∀ j, ∃ b : Kˣ, a j = b ^ 2) :
    rootDiagUnit Tag.D4 a ∈ adjointGroup Tag.D4 K := by
  choose b hb using ha
  have h := rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) b
  have e : (fun j : Fin 4 => b j ^ 2) = a := funext fun j => (hb j).symm
  rwa [e] at h

@[expose] def torusSub (μ : Subgroup Kˣ) : Subgroup ↥(adjointGroup Tag.D4 K) where
  carrier := {g | ∃ a : Fin Tag.D4.rank → Kˣ, (∀ j, a j ∈ μ) ∧
    (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a}
  mul_mem' := by
    rintro g h ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩
    exact ⟨a * b, fun j => μ.mul_mem (ha j) (hb j), by
      rw [Subgroup.coe_mul, hga, hhb, rootDiagUnit_mul]⟩
  one_mem' := ⟨1, fun _ => μ.one_mem, by rw [Subgroup.coe_one, rootDiagUnit_one]⟩
  inv_mem' := by
    rintro g ⟨a, ha, hga⟩
    exact ⟨a⁻¹, fun j => μ.inv_mem (ha j), by rw [Subgroup.coe_inv, hga, rootDiagUnit_inv]⟩

theorem card_torusSub [Finite K] (μ : Subgroup Kˣ) (hμ : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2) :
    Nat.card (torusSub (K := K) μ) = Nat.card μ ^ 4 := by
  let f : (Fin Tag.D4.rank → μ) → torusSub (K := K) μ := fun a =>
    ⟨⟨rootDiagUnit Tag.D4 (fun j => (a j : Kˣ)),
      rootDiagUnit_mem_of_sq (fun j => hμ _ (a j).2)⟩, ⟨_, fun j => (a j).2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun g : torusSub (K := K) μ => ((g : ↥(adjointGroup Tag.D4 K)) :
      ModGL Tag.D4 K)) hab
    have h' := rootDiagUnit_injective_D4 h
    funext j
    exact Subtype.ext (congrFun h' j)
  have hsurj : Function.Surjective f := by
    rintro ⟨g, a, ha, hga⟩
    refine ⟨fun j => ⟨a j, ha j⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact hga.symm
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_fun]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem d4Graph_one_torusSub {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} (hga : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) :
    ((d4Graph K 1 g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct permM a) := by
  rw [coe_d4Graph, pow_one, hga, diagramMap_conj_rootDiagUnit_tupAct]

theorem rootDiagUnit_commute (a b : Fin Tag.D4.rank → Kˣ) :
    rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 b =
      rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 a := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem commute_of_diag {g h : ↥(adjointGroup Tag.D4 K)} {a b : Fin Tag.D4.rank → Kˣ}
    (hg : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a)
    (hh : (h : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 b) : g * h = h * g :=
  Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hg, hh, rootDiagUnit_commute])

theorem coe_torusElement (i : Fin Tag.D4.rank) (t : Kˣ) :
    ((torusElement Tag.D4 K i t : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (fun j => t ^ Tag.D4.cartan i j) :=
  torusElt_eq_rootDiagUnit i t

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
