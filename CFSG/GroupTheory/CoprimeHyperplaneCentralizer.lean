module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_hyperplane_not_le_centralizer_inf_centralizer {r : ℕ} [Fact r.Prime]
    {E Q : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian r E) (hEcard : r ^ 2 ≤ Nat.card E)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hrQ : ¬ r ∣ Nat.card Q)
    (hfaith : ¬ E ≤ Subgroup.centralizer (Q : Set G)) :
    ∃ Y : Subgroup G, Y ≤ E ∧ Nat.card Y * r = Nat.card E ∧
      ¬ E ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  classical
  haveI : Nontrivial E := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
    nlinarith
  haveI : IsElementaryAbelian r E :=
    { is_comm := hE.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hE.2 x x.2) }
  letI : Subgroup.Normalizes E Q := ⟨hEQ⟩
  have hgen : ⨆ (B : Subgroup E) (_ : B.index = r), fixedPointSubgroup B Q = ⊤ :=
    CFSG.SolvableHall.coprime_hyperplane_generation (p := r) (A := E) (H := Q) hrQ
  by_contra hcon
  push_neg at hcon
  have hQ : Q ≤ Subgroup.centralizer (E : Set G) := by
    have hle : (⨆ (B : Subgroup E) (_ : B.index = r), fixedPointSubgroup B Q) ≤
        (Subgroup.centralizer (E : Set G)).comap Q.subtype := by
      refine iSup_le fun B => iSup_le fun hB => ?_
      intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro e he
      set Y : Subgroup G := B.map E.subtype
      have hYE : Y ≤ E := Subgroup.map_subtype_le B
      have hYcard : Nat.card Y * r = Nat.card E := by
        change Nat.card (B.map E.subtype) * r = Nat.card E
        rw [Subgroup.card_map_of_injective E.subtype_injective, ← hB]
        exact B.card_mul_index
      have hxY : (x : G) ∈ Subgroup.centralizer (Y : Set G) := by
        change (x : G) ∈ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        rintro y ⟨b, hb, rfl⟩
        have hb' := congrArg Subtype.val (hx ⟨b, hb⟩)
        change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hb'
        calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
          _ = (x : G) * (b : G) := by rw [hb']
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (hcon Y hYE hYcard he) (x : G) ⟨x.2, hxY⟩
      exact hcomm.symm
    rw [hgen] at hle
    intro q hq
    exact Subgroup.mem_comap.mp (hle (Subgroup.mem_top (⟨q, hq⟩ : Q)))
  exact hfaith fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hQ hq) e he).symm

end CFSG.GroupTheory
